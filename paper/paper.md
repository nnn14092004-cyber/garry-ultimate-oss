---
title: 'GARRYULT: A Bare-Metal O(1) Rust Symbolic/SMT Kernel and Two-Tier Lean 4 / Mathlib4 Formalization of the 3D Incompressible Navier-Stokes Equations on T^3'
tags:
  - Rust
  - formal verification
  - Navier-Stokes
  - partial differential equations
  - interval arithmetic
  - SMT solver
  - Lean 4
  - Mathlib4
  - Z3
authors:
  - name: Nhật Nam Nguyễn
    orcid: 0009-0006-8216-0594
    affiliation: "1, 2"
affiliations:
  - name: Independent Formal Verification Researcher, Nha Trang, Vietnam
    index: 1
  - name: Nha Trang University, Khanh Hoa, Vietnam
    index: 2
date: 20 November 2026
bibliography: paper.bib
---

# Summary

`garry-ultimate-oss` (`GARRYULT` v4.0.0) is a dual-engine, machine-checkable formal verification framework for the three-dimensional incompressible Navier–Stokes equations [@nguyen2026garryult; @nguyen2026whitepaper]. It combines: (1) a deterministic, zero-dependency (`#![no_std]` core), $O(1)$ stack-bounded pure-Rust kernel implementing a 5-lemma symbolic PDE deduction tree (`SymbolicPdeProofTree`), an autonomous zero-catalog 3D solenoidal initial-data synthesizer (`synthesize`), a Lagrangian parcel trajectory enclosure, and outward-rounded 128-bit rational interval arithmetic (`RationalInterval128`, verified by 30/30 unit and adversarial falsification tests in 0.01 s); and (2) an end-to-end **Lean 4 / Mathlib4** formalization comprising **234 unique `#print axioms`-audited theorems** across **19 Mathlib4 modules (6,230 Lake build jobs)** and **6 unique standalone integer suites** (`ns_1`–`ns_5` plus `autonomous_u0`) with **`0 sorryAx`** and **`0` custom axioms** [@de2008z3; @moura2021lean].

# Statement of Need

Traditional computational fluid dynamics (CFD) and numerical PDE solvers evaluate velocity and vorticity fields over finite meshes using IEEE-754 floating-point arithmetic [@fefferman2006existence]. When investigating regularity criteria or potential finite-time singularities [@beale1984remarks; @caffarelli1982partial], rounding drift, unverified Galerkin spectral truncation remainders, and opaque numerical assumptions prevent simulations from serving as rigorous mathematical proofs. Conversely, existing formal proof libraries rarely bridge infinite-dimensional 3D Sobolev/Fourier PDE theory all the way to pointwise smooth classical solutions in a single, auditable repository.

`GARRYULT` v4.0.0 addresses both gaps by pairing a zero-heap, zero-crate Rust symbolic/SMT verifier with an 8-milestone **Lean 4 / Mathlib4** PDE formalization on the periodic 3D torus $\mathbb{T}^3 = (\mathbb{R}/\mathbb{Z})^3$ that explicitly separates unconditional PDE theorems from conditional supercritical closure criteria inside the proof assistant's trusted kernel.

# Architecture and Formal Verification Methodology

`garry-ultimate-oss` v4.0.0 operates across two tightly coupled verification stacks:

1. **Pure-Rust $O(1)$ Symbolic PDE, Autonomous Synthesizer & 128-Bit Interval SMT Kernel (`src/`):**
   - *Outward-Rounded 128-Bit Interval Arithmetic (`RationalInterval128`):* Lifts continuous Reynolds numbers, vortex stretching rates ($S_{\text{stretch}}$), Galerkin spectral tail remainders ($R_{\text{tail}}$), and viscous dissipation bounds ($D_{\text{visc}}$) into $10^6$-scaled 128-bit integer intervals with mandatory outward safety rounding.
   - *5-Lemma Symbolic PDE Tree & Autonomous 3D Mode Synthesizer (`synthesize`):* Verifies $\nabla \cdot \mathbf{u} = 0$, $\nabla \times \nabla p \equiv \mathbf{0}$, Constantin–Fefferman depletion [@constantin1993direction], Bernstein–Poincaré coercivity, and Lagrangian trajectory decay (`ns_1`–`ns_5`, $\dot{Z}_{\text{upper}} \in [-517.854144, -294.106363]$), while `synthesize` accepts raw $(k, a, \nu, L_0)$ 3D velocity modes without catalog presets, rejects compressible modes ($\nabla \cdot u_0 \ne 0$) fail-closed, and emits verified `.txt`, `.smt2`, and 3-theorem `.lean` certificates (canonical seal `0x2F3FECC4`, $\dot{Z}_{\text{upper}} = -693.996029$, `UNSAT`).
   - *Fail-Closed Adversarial Falsification Gate (`30/30` Tests):* Perturbing any single physical bound by one micro-unit ($10^{-6}$), omitting L2 axiom registration, breaking hypergraph causal links, or supplying compressible initial data immediately triggers a deterministic `Fail-Closed` rejection.

2. **8-Milestone Lean 4 / Mathlib4 True 3D Navier–Stokes Formalization on $\mathbb{T}^3$ (`formal_proofs_mathlib/`):**
   - *Tier B (`GarryNavierStokesMathlib.lean`, 24 theorems):* Real-field ($\mathbb{R}$) formalization of the symbolic PDE lemmas, $\sqrt{Z}/\sqrt{Z}$ and $\nu/\nu$ cancellations, Kolmogorov core floor, intrinsic polynomial-square quartic Young $(4/5, 4)$ absorption, Bony paraproduct triad cancellation, Galerkin UV tail bridge, and the `v4` autonomous synthesizer.
   - *Tier C — Milestones 1–6 (109 theorems across 13 modules):* Real 3D Fréchet vector calculus, exact 3D vorticity equation, periodic integration by parts, continuous-time Leray kinetic energy and enstrophy laws, sharp 3D Wirtinger–Poincaré exponential decay ($E(t) \le E_0 e^{-8\pi^2\nu t}$), spectral Biot–Savart and orthogonal Leray projection, global $L^2$ Calderón–Zygmund pressure bounds, Parseval–Plancherel identities, Sobolev $H^2(\mathbb{T}^3) \hookrightarrow L^\infty(\mathbb{T}^3)$, Agmon's 3D inequality, weighted $H^2$ convolution algebra, Duhamel $1/4$-contraction, and Picard–Banach local existence and uniqueness for arbitrary $u_0 \in H^2_{\mathrm{div}}(\mathbb{T}^3)$.
   - *Tier C — Milestones 7–8 (43 theorems across 5 modules):* Differential Grönwall, true 3D BKM continuation, classical $C^3$ and mild $H^2$ global uniqueness, unconditional global existence on $[0, \infty)$ for small mean-zero data ($217088 \Vert{}u_0\Vert{}_{H^2}^2 \le \pi^2 \nu^2$), a **Finite-Time Basin Entry ("Waterfall-to-River") transfer law** (`finite_time_basin_entry_global_ns3d_torus3D`), unconditional Wiener-$\ell^1 \to H^2$ tame continuation, instantaneous parabolic bootstrapping $H^2 \to H^m(\mathbb{T}^3)$ for all $m \in \mathbb{N}$, exact $H^\infty(\mathbb{T}^3) \hookrightarrow C^\infty(\mathbb{T}^3)$ synthesis for both velocity $U(t, \cdot)$ and Calderón–Zygmund pressure $P(t, \cdot)$, exact pointwise physical-space PDE verification (`mild_solution_physical_ns3d_torus3D`), and the unified Two-Tier Grand Master Theorem (`garry_millennium_master_theorem_torus3D`).

# Two-Tier Mathematical Boundary and Anti-Circularity Audit

To ensure complete transparency during peer review, `SupercriticalBoundaryAuditTorus3D.lean` and `SmoothClassicalSynthesisTorus3D.lean` formally enforce a strict separation between unconditional and conditional results inside Lean 4:

1. **Unconditional Tier I on $\mathbb{T}^3$ (Zero Extra Premises):** Local $C^\infty$ classical solutions for arbitrary $u_0 \in H^2_{\mathrm{div}}(\mathbb{T}^3)$; global $C^\infty$ classical solutions on $(0, \infty)$ for small data, compatible viscosity, or finite-time basin entry; global uniqueness; true 3D BKM and Wiener-$\ell^1$ tame continuation; and formal proofs of the supercritical $Z^3$ Young wall (`supercritical_young_absorption_wall_torus3D`) and the 3D supercritical energy scaling barrier (`ns3d_supercritical_energy_barrier`).
2. **Conditional Tier II on $\mathbb{T}^3$ (Non-Vacuous Garry Closure Criteria):** `GarryConditionalClosureHypotheses`, $\sqrt{Z}$-cancellation with Kolmogorov core floor, and quartic Young / Bony triad hypotheses are explicitly isolated as theorem premises, constructively proven non-vacuous (`garry_closure_hypotheses_nonvacuous`), bridged directly to true 3D Lebesgue integrals, and proved to imply global $C^\infty(\mathbb{T}^3)$ physical-space solutions on $(0, \infty)$.
3. **Explicit Scope Honesty:** An unconditional global regularity proof for arbitrary large initial data at arbitrarily small $\nu > 0$ without Tier II closure premises remains open (the Clay Millennium Problem) and is never concealed behind any `sorryAx` or custom axiom.

# Acknowledgements and AI Usage Disclosure

All mathematical formulations, the two-tier Navier–Stokes formalization architecture, the `#![no_std]` pure-Rust kernel, and the 128-bit interval SMT and 19-module Lean 4 / Mathlib4 verification pipelines were conceived, designed, implemented, and verified by the author. AI assistance was used strictly for academic English editing, Markdown/LaTeX typesetting, and interactive Lean 4 tactic engineering under the author's independent kernel verification (`lake build SmoothClassicalSynthesisTorus3D`).

# References