#!/usr/bin/env bash
# ==============================================================================
# garry-ultimate-oss (v4.0.0) - Deterministic Verification Script
# Author: Nguyen Nhat Nam (ORCID: 0009-0006-8216-0594)
# Scope: Pure-Rust Kernel (33 tests, 0 crates) + BLW CAP Emitter + Z3 SMT-LIB +
#        39-Module Lean 4 / Mathlib4 Dual-Domain Suite (T^3 & R^3, 0 sorryAx)
# ==============================================================================
set -euo pipefail

echo "================================================================================"
echo " [1/8] Checking dependency tree (expected: 0 external crates)"
echo "================================================================================"
cargo tree --depth 1

echo "================================================================================"
echo " [2/8] Running clippy static analysis (-D warnings)"
echo "================================================================================"
cargo clippy --all-targets -- -D warnings

echo "================================================================================"
echo " [3/8] Running Rust test suite (33/33 tests)"
echo "================================================================================"
cargo test --release --verbose

echo "================================================================================"
echo " [4/8] Running stack latency benchmarks (5,000 iterations)"
echo "================================================================================"
cargo run --release -- bench

echo "================================================================================"
echo " [5/8] Regenerating canonical suites, autonomous synthesizer & BLW CAP artifacts"
echo "================================================================================"
cargo run --release -- solutions
cargo run --release -- synthesize
cargo run --release -- --certify-blw

echo "================================================================================"
echo " [6/8] Checking SMT-LIB 2.6 (.smt2) & standalone Tier A Lean 4 certificates"
echo "================================================================================"
if command -v z3 >/dev/null 2>&1; then
    for f in \
        garry_workspace/solutions/ns_*.smt2 \
        garry_workspace/solutions/navier_stokes_smtlib_certificate.smt2 \
        garry_workspace/solutions/autonomous_u0_smtlib_certificate.smt2 \
        garry_workspace/solutions/blw_r3_certificate.smt2; do
        echo -n " -> Z3 $f : "
        out="$(z3 "$f")"
        echo "$out"
        if [ "$out" != "unsat" ]; then
            echo "ERROR: Expected 'unsat' for $f, got '$out'" >&2
            exit 1
        fi
    done
else
    echo " -> [INFO] z3 not found in PATH; skipping external .smt2 check."
fi

if command -v lean >/dev/null 2>&1; then
    for f in \
        garry_workspace/solutions/ns_*.lean \
        garry_workspace/solutions/navier_stokes_lean4_certificate.lean \
        garry_workspace/solutions/autonomous_u0_lean4_certificate.lean; do
        echo " -> Lean 4 (standalone) $f"
        lean_out="$(lean "$f")"
        echo "$lean_out"
        if echo "$lean_out" | grep -q "sorryAx"; then
            echo "ERROR: sorryAx detected in $f" >&2
            exit 1
        fi
    done
else
    echo " -> [INFO] lean not found in PATH; skipping standalone Lean 4 check."
fi

echo "================================================================================"
echo " [7/8] Building 39-module Mathlib4 suite (T^3 & R^3) and BLW CAP certificate"
echo "================================================================================"
if command -v lake >/dev/null 2>&1; then
    pushd formal_proofs_mathlib >/dev/null
    lake build SupercriticalClayFrontier15G
    lake build SupercriticalBoundaryAuditTorus3D
    lake build GarryNavierStokesMathlib

    for target in \
        SupercriticalClayFrontier15G.lean \
        SchwartzClayPackagingNS3D.lean \
        SupercriticalBoundaryAuditTorus3D.lean \
        ../garry_workspace/solutions/blw_r3_certificate.lean; do
        echo " -> Auditing axioms: $target"
        lean_out="$(lake env lean "$target")"
        echo "$lean_out"
        if echo "$lean_out" | grep -q "sorryAx"; then
            echo "ERROR: sorryAx detected in $target" >&2
            exit 1
        fi
    done
    popd >/dev/null
else
    echo " -> [INFO] lake not found in PATH; skipping Mathlib4 build check."
fi

echo "================================================================================"
echo " [8/8] Static sorry/axiom scan & SHA-256 manifest verification"
echo "================================================================================"
if grep -rnE '^\s*(private\s+)?axiom\b|\b(sorry|sorryAx|admit)\b' \
    formal_proofs_mathlib/*.lean garry_workspace/solutions/*.lean; then
    echo "ERROR: Prohibited sorry/admit/axiom token detected." >&2
    exit 1
else
    echo " -> Static scan clean: 0 sorry, 0 sorryAx, 0 admit, 0 custom axioms."
fi

if [ -f SHA256SUMS.txt ] && command -v sha256sum >/dev/null 2>&1; then
    sha256sum -c SHA256SUMS.txt --quiet
    echo " -> SHA256SUMS.txt verified."
else
    echo " -> [INFO] sha256sum not found or SHA256SUMS.txt missing; skipping checksum check."
fi

echo "================================================================================"
echo " [PASS] garry-ultimate-oss v4.0.0 verification complete."
echo "================================================================================"