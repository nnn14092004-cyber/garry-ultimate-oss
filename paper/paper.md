---
title: 'garry-ultimate-oss: A Pure-Rust O(1) Interval SMT Verifier and Dual-Domain Lean 4 / Mathlib4 Formalization of the 3D Incompressible Navier-Stokes Equations on T^3 and R^3'
tags:
  - Rust
  - formal verification
  - Navier-Stokes
  - partial differential equations
  - interval arithmetic
  - SMT solver
  - Lean 4
  - Mathlib4
  - computer-assisted proof
authors:
  - name: Nguyen Nhat Nam
    orcid: 0009-0006-8216-0594
    affiliation: "1, 2"
affiliations:
  - name: Independent Formal Verification Researcher, Nha Trang, Vietnam
    index: 1
  - name: Nha Trang University, Khanh Hoa, Vietnam
    index: 2
date: 24 November 2026
bibliography: paper.bib
---

# Summary

`garry-ultimate-oss` (v4.0.0) is a dual-engine formal verification suite for the three-dimensional incompressible Navier-Stokes equations on the periodic torus $\mathbb{T}^3 = (\mathbb{R}/\mathbb{Z})^3$ and whole space $\mathbb{R}^3$ [@nguyen2026garryult; @nguyen2026whitepaper]. It combines:

1. A zero-dependency pure-Rust verification kernel (`src/`, 15 modules, 33/33 unit and adversarial falsification tests passing in 0.01 s) implementing a stack-bounded symbolic PDE deductor, a 128-bit outward-rounded rational interval SMT prover, an autonomous 3D solenoidal initial-mode synthesizer (`synthesize`), and a static-stack Betchov-Loomis-Whitney (BLW) three-phase waterfall witness verifier (`--certify-blw`) that emits `.txt`, `.smt2`, and `.lean` certificates [@de2008z3].
2. A Lean 4 / Mathlib4 formalization (`formal_proofs_mathlib/`, 39 modules, 50,216 lines, 403 `#print axioms`-audited declarations, `0 sorryAx`, `0` custom axioms) paired with 60 unique audited declarations in `garry_workspace/solutions/` [@moura2021lean]. Every audited theorem depends exclusively on the standard Lean 4 core axioms `[propext, Classical.choice, Quot.sound]`.

# Statement of need

Conventional numerical fluid dynamics solvers integrate three-dimensional velocity and vorticity fields over finite meshes in IEEE-754 floating-point arithmetic. Because spectral truncation remainders, aliasing errors, and rounding drift are not formally enclosed, numerical simulations cannot certify analytical regularity criteria or rule out finite-time singularities [@fefferman2006existence; @beale1984remarks; @caffarelli1982partial]. Conversely, existing theorem-proving libraries rarely connect infinite-dimensional 3D Sobolev and Fourier PDE theory, sharp counter-obstructions, and deterministic computer-assisted witness checking within a single reproducible repository.

Researchers investigating conditional regularity criteria, invariant enstrophy basins, or computer-assisted blow-up exclusion need tooling that enforces strict separation between unconditional theorems and conditional hypotheses inside a trusted proof kernel. `garry-ultimate-oss` addresses this gap by linking a zero-dependency Rust 128-bit witness verifier directly to a dual-domain Lean 4 / Mathlib4 Navier-Stokes library on $\mathbb{T}^3$ and $\mathbb{R}^3$.

# State of the field

Computational fluid dynamics packages such as OpenFOAM, Dedalus, and Nek5000 provide high-resolution numerical approximations of 3D incompressible turbulence but do not emit machine-checked proofs. In the computer-assisted proof community, rigorous ODE/PDE enclosure libraries such as CAPD and RadiiPolynomial.jl validate finite-dimensional or spectral fixed points using interval arithmetic, typically targeting specific equilibria or periodic orbits without an embedded proof assistant kernel. In interactive theorem proving, Mathlib4 (Lean 4) and Isabelle/HOL provide foundational measure theory, Fourier analysis, and functional analysis, yet neither ships an end-to-end 3D Navier-Stokes regularity tower spanning both $\mathbb{T}^3$ and $\mathbb{R}^3$. `garry-ultimate-oss` bridges these efforts by combining a self-contained Rust interval/SMT witness checker with a 39-module Mathlib4 formalization that checks emitted `.lean` certificates directly against the formalized PDE theorems.

# Software design

`garry-ultimate-oss` is organized into two coupled verification layers:

1. **Pure-Rust Verification Kernel (`src/`):** Compiles with zero external crates (`[dependencies]` empty) and zero `if`/`else` branches across all 15 source modules (all control flow uses exhaustive `match`). Core data structures--including the 128-node symbolic AST arena (`SymbolicArena`), 16-variable/32-constraint interval SMT table (`DeterministicSmtProver`), 16-node execution DAG (`PlanGraph`), 256-node domain hypergraph (`AxiomHyperGraphL2`), 8-register stack ISA (`StackOmniverseCpu`), 128-bit BLW witness checker (`BlwWaterfallWitnessStack<16>`, 223.98 ns mean verification latency), and the `[u8; 32768]` output buffer in `src/blw_emitter.rs`--operate strictly on the stack. Heap `String` allocation is restricted to legacy CLI report formatting. Exact integer constants from Lean 4 (`46,656`, `23,328`, `186,624`, `8/19,683` on $\mathbb{R}^3$; `169/8`, `4/13`, `217,088` on $\mathbb{T}^3$) are synchronized in `src/omniverse_constants.rs`. Given a micro-scaled ($10^6$) trajectory grid $(t_k, Z_k, E_k)$, `--certify-blw` verifies $4 z_k^2 \Delta t_k \le 23\,328\,\nu_{\mathrm{micro}}^3$ and $E(t_N)Z(t_N) \cdot 10^{12} < 46\,656\,\nu_{\mathrm{micro}}^4$ in overflow-checked `i128` arithmetic and writes `blw_r3_certificate.smt2` (`unsat` under Z3) and `blw_r3_certificate.lean` (verified against `SupercriticalClayFrontier15G` with `0 sorryAx`).
2. **Dual-Domain Lean 4 / Mathlib4 Library (`formal_proofs_mathlib/`):** Structured into 39 modules covering vector calculus, Leray energy laws [@leray1934mouvement], Fourier-Parseval-Sobolev-Agmon theory, constructive Picard-Duhamel local existence on $\mathbb{T}^3$ and $\mathbb{R}^3$, Serrin $L^2$ global uniqueness [@prodi1959teorema; @serrin1962interior], all-order mixed spacetime smoothness (`SpacetimeSmoothnessNS3D`), strain-pressure geometry and Betchov's identity [@betchov1956inequality], Constantin-Fefferman and $\lambda_2^+$ depletion criteria [@constantin1993direction; @neustupa2001vorticity; @miller2020strain], and the Betchov-Loomis-Whitney $46\,656\,\nu^4$ invariant basin [@loomis1949inequality]. Inside `SupercriticalClayFrontier15G.lean` and `SchwartzClayPackagingNS3D.lean`, Tier I isolates unconditional theorems (including three-phase CAP closure for certified supercritical trajectories), while Tier II isolates the remaining open arbitrary-data Clay Millennium Problem to a single geometric hypothesis, `BiaxialSheetSelfRegulationLemmaR3`.

# Research impact statement

`garry-ultimate-oss` establishes a reusable, machine-checked baseline for formalizing 3D incompressible fluid dynamics and auditing supercritical regularity arguments. Its 39-module Lean 4 / Mathlib4 codebase provides verified building blocks--including whole-space $\mathbb{R}^3$ integration by parts, homogeneous 3D Agmon and Loomis-Whitney inequalities, Serrin $L^2$ uniqueness, constructive frequency-space Picard-Duhamel existence, and exact red-team separatrix ODE obstructions (`variational_EZ_separatrix_red_team_obstruction`)--that prevent circular energy-to-enstrophy reasoning in future proof attempts. By archiving versioned software releases and preprints on Zenodo with persistent DOIs and Software Heritage SWHIDs, and providing an automated multi-OS audit script (`verify_all.sh`), the repository enables mathematicians and formal-methods researchers to independently verify and extend both the Tier I computer-assisted closure pipeline and the Tier II geometric depletion frontier.

# AI usage disclosure

All mathematical formulations, the two-tier verification boundary, the Rust kernel design, and the Lean 4 module architecture were directed and independently verified by the author through `cargo test --release`, `z3`, and `lake build SupercriticalClayFrontier15G` (`0 sorryAx`). Large language models were used strictly for English copy-editing, Markdown/LaTeX formatting, and interactive Lean 4 tactic drafting; every generated proof script and Rust module was audited and mechanically verified by the compiler and Lean 4 kernel prior to inclusion.

# Acknowledgements

The author thanks the Lean 4 and Mathlib4 communities for maintaining the foundational analysis and measure theory libraries used in `formal_proofs_mathlib/`.

# References