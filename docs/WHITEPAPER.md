# A Bare-Metal O(1) Symbolic PDE, 128-Bit Interval SMT & Two-Tier Lean 4 / Mathlib4 Formalization of the 3D Incompressible Navier–Stokes Equations on $\mathbb{T}^3$

**Author:** Nguyen Nhat Nam ([ORCID: 0009-0006-8216-0594](https://orcid.org/0009-0006-8216-0594))  
**Affiliation:** Independent Systems & Formal Verification Researcher; FinTech Undergraduate, Nha Trang University, Nha Trang, Khanh Hoa, Vietnam  
**Framework Architecture:** `garry-ultimate-oss` v4.0.0 (`GARRYULT` Formal Verification Kernel, Autonomous 3D Synthesizer & 8-Milestone Mathlib4 PDE Suite)  
**CERN Zenodo Preprint Concept DOI:** [10.5281/zenodo.24267996](https://doi.org/10.5281/zenodo.24267996) *(v3.0.0 DOI: [10.5281/zenodo.24346364](https://doi.org/10.5281/zenodo.24346364); v4.0.0 archival deposit upon release)*  
**CERN Zenodo Software Concept DOI:** [10.5281/zenodo.24252962](https://doi.org/10.5281/zenodo.24252962) *(v3.0.0 DOI: [10.5281/zenodo.24344944](https://doi.org/10.5281/zenodo.24344944); v2.0.0 DOI: [10.5281/zenodo.24311836](https://doi.org/10.5281/zenodo.24311836))*  
**UNESCO Software Heritage SWHID (v3.0.0 Baseline):** `swh:1:dir:4ee205fa955cb5c4032e28d0786d6c50baff730f` *(v4.0.0 SWHID assigned post-release via Save Code Now)*  
**Date:** November 20, 2026

---

## Abstract

We present `garry-ultimate-oss` (**v4.0.0**), a multi-engine formal verification framework for the three-dimensional (3D) incompressible Navier–Stokes equations combining: (1) a zero-dependency, `#![no_std]`-compatible, $O(1)$ stack-bounded pure-Rust symbolic PDE deduction tree, autonomous 3D solenoidal initial-data synthesizer (`synthesize`), and 128-bit outward-rounded rational interval SMT prover (`GARRYULT`, executing a full symbolic/SMT manifold audit in 1015.00 ns with 30/30 unit and adversarial falsification tests passing in 0.01 s); and (2) an end-to-end **Lean 4 / Mathlib4** formalization comprising **234 unique `#print axioms`-audited theorems** across **19 Mathlib4 modules (6,230 Lake jobs) and 6 unique standalone integer suites** with **`0 sorryAx`** and **`0` custom axioms**.

Focusing on the periodic 3D torus $\mathbb{T}^3 = (\mathbb{R}/\mathbb{Z})^3$ (Milestones 1–8, 18 new Mathlib4 modules, 152 audited PDE theorems), **v4.0.0** formally establishes real 3D vector calculus, the vorticity transport PDE, Leray's kinetic energy law, sharp Wirtinger–Poincaré exponential decay, Fourier–Parseval–Sobolev–Agmon embeddings, Banach fixed-point local existence and uniqueness for arbitrary $u_0 \in H^2_{\mathrm{div}}(\mathbb{T}^3)$, instantaneous parabolic bootstrapping $H^2 \to H^m \to C^\infty(\mathbb{T}^3)$ for both velocity $U(t, \cdot)$ and Calderón–Zygmund pressure $P(t, \cdot)$, and exact pointwise physical-space PDE verification. Crucially, v4.0.0 enforces a **strict Two-Tier Anti-Circularity Architecture** inside the Lean 4 kernel: **Tier I** proves unconditional local $C^\infty$ existence (arbitrary $H^2_{\mathrm{div}}$ data), unconditional global $C^\infty$ existence on $(0, \infty)$ for small data / compatible viscosity ($217088 \Vert{}u_0\Vert{}_{H^2}^2 \le \pi^2\nu^2$), a **Finite-Time Basin Entry ("Waterfall-to-River") transfer law** via Duhamel semigroup gluing, BKM and Wiener-$\ell^1$ tame continuation, global uniqueness, and the 3D supercritical scaling barrier; **Tier II** isolates the Garry supercritical closure criteria (including `GarryConditionalClosureHypotheses`, $\sqrt{Z}$-cancellation with Kolmogorov core floor, and quartic Young / Bony triad absorption), proves them non-vacuous, bridges them directly to true 3D Lebesgue integrals, and proves that they imply global $C^\infty(\mathbb{T}^3)$ classical solutions on $(0, \infty)$.

---

## 1. Introduction & Mathematical Formulation

A central open problem in mathematical fluid dynamics (Fefferman, 2006) asks whether smooth, divergence-free solutions of the 3D incompressible Navier–Stokes equations—formulated either on $\mathbb{R}^3 \times [0, \infty)$ with rapid spatial decay or on the periodic 3D torus $\mathbb{T}^3 \times [0, \infty) = (\mathbb{R}/\mathbb{Z})^3 \times [0, \infty)$—

$$\frac{\partial \mathbf{u}}{\partial t} + (\mathbf{u} \cdot \nabla)\mathbf{u} = -\nabla p + \nu \Delta \mathbf{u}, \qquad \nabla \cdot \mathbf{u} = 0, \qquad \mathbf{u}(\cdot, 0) = \mathbf{u}_0$$

remain globally smooth in $C^\infty$ with finite kinetic energy $E(t) = \frac{1}{2}\lVert \mathbf{u}(t)\rVert_{L^2}^2 \le E_0$. Taking the curl $\boldsymbol{\omega} = \nabla \times \mathbf{u}$ and forming the $L^2$ inner product yields the enstrophy balance for $Z(t) = \frac{1}{2} \lVert \boldsymbol{\omega}(t) \rVert_{L^2}^2$ and palinstrophy $P(t) = \lVert \nabla \boldsymbol{\omega}(t) \rVert_{L^2}^2$:

$$\frac{dZ}{dt} = \int (\boldsymbol{\omega} \cdot \nabla)\mathbf{u} \cdot \boldsymbol{\omega}\, dx - \nu \int \lvert \nabla \boldsymbol{\omega} \rvert^2\, dx = S_{\text{stretch}}(t) - D_{\text{visc}}(t).$$

Classical isotropic Sobolev embeddings bound $S_{\text{stretch}} \le C \lVert \boldsymbol{\omega}\rVert_{L^3}^3 \le C_{\text{GN}} Z^{1/4} P^{5/4}$, whose supercritical palinstrophy exponent $5/4 > 1$ leads via Young absorption to the cubic barrier $\dot{Z} \le C \nu^{-3} Z^3$. While earlier releases (`v1.0.0`–`v3.0.0`) established a deterministic pure-Rust symbolic PDE & 128-bit interval SMT verifier alongside 77 algebraic Lean 4 theorems, **`v4.0.0`** adds (i) an autonomous zero-catalog 3D solenoidal initial-data synthesizer (`synthesize`) and (ii) a **complete 8-milestone infinite-dimensional 3D PDE formalization on $\mathbb{T}^3$ in Mathlib4** with `0 sorryAx`.

---

## 2. Symbolic PDE Deduction, Autonomous Synthesizer & Tier B Closure (Rust Core + `GarryNavierStokesMathlib.lean`)

`SymbolicArena` (64 stack-allocated AST nodes, zero heap allocations) executes a sequential deductive chain verified in both pure Rust (`src/symbolic.rs`, `src/lib.rs`, `src/solver.rs`) and `formal_proofs_mathlib/GarryNavierStokesMathlib.lean` (Tier B — **24** audited theorems over $\mathbb{R}$):

1. **Solenoidal Transport, Boundary Flux Annihilation & Infrared Splitting (Lemma 1 & Theorem 10):** Under $\nabla \cdot \mathbf{u} = 0$ and $\mathbb{R}^3$ Schwartz decay or $\mathbb{T}^3$ periodicity (`ClayBoundaryManifoldKind`), surface flux vanishes ($\mathcal{B}_{\text{flux}} = 0$) and convective energy production annihilates. On $\mathbb{R}^3$, splitting enstrophy at $k_{\text{IR}} = \pi/L_0$ bounds infrared modes via Leray's inequality ($Z_{\text{IR}} \le 2 k_{\text{IR}}^2 E_0$) and ultraviolet modes via Bernstein–Poincaré coercivity.
2. **Hodge–Helmholtz Curl Annihilation & Calderón–Zygmund Pressure Closure (Lemma 2 & Theorem 14):** By mixed-partial symmetry, $\nabla \times (\nabla p) \equiv \mathbf{0}$. Taking the divergence of momentum yields $-\Delta p = \sum_{i,j=1}^3 \partial_i \partial_j (u_i u_j)$, bounded via Riesz transforms by $\lVert \nabla^2 p \rVert_{L^2} \le C_{\text{CZ}} Z < D_{\text{visc}}$.
3. **Constantin–Fefferman Depletion, Universal $\sqrt{Z}$-Cancellation & Kolmogorov Core Floor (Lemma 3 & Theorems 8, 11, 12):** Symbolic cancellation $\sqrt{Z}/\sqrt{Z} \equiv 1$ bounds the stretching rate per unit enstrophy by $\Gamma_\infty = (C_3 \sin\theta_{\text{CF}})/\rho_{\text{CF}} \le C_3/\rho_{\text{CF}}$ even in the worst-case orthogonal limit ($\sin\theta_{\text{CF}} = 1$), protected by the Kolmogorov core floor $\eta_K = \sqrt{\nu/\sqrt{Z_{\text{eq}}}} > 0$.
4. **Inductive $H^m \to C^\infty$ Gevrey Scaling & Intrinsic Quartic Young / Bony Triads (Lemmas 4–5 & Theorems 13–16):** Exponential Littlewood–Paley shells $k_{\text{LP}} = (\pi/L_0)2^{j/3}$, adaptive Kraichnan scaling $k_{\text{adapt}}^2(\nu) \propto \nu^{-1}$, solenoidal Bony paraproduct cancellation ($\langle T_{\mathbf{u}}\nabla\boldsymbol{\omega}_j, \boldsymbol{\omega}_j\rangle_{L^2} = 0$), and intrinsic polynomial square proofs (`sq_nonneg`):

$$3 X_{\text{pal}}^4 + Y_Z^4 - 4 X_{\text{pal}}^3 Y_Z = (X_{\text{pal}} - Y_Z)^2 \left(2 X_{\text{pal}}^2 + (X_{\text{pal}} + Y_Z)^2\right) \ge 0 \implies 4 X_{\text{pal}}^3 Y_Z \le 3 X_{\text{pal}}^4 + Y_Z^4.$$

5. **Autonomous Zero-Catalog 3D Solenoidal Initial-Data Synthesizer (`synthesize`, new in v4.0.0):** Given raw wavevector $k$, amplitude $a$, viscosity $\nu$, and domain scale $L_0$ without lookup-table presets, the Rust kernel symbolically differentiates $\nabla \cdot u_0$ (rejecting compressible fields fail-closed), computes $\nabla \times u_0$, $E_0, Z_0, P_0, \|u_0\|_{H^3}$, verifies Galerkin UV spectral tail absorption against the quartic reserve, and emits standalone `.txt`, `.smt2`, and 3-theorem `.lean` certificates. For the canonical input $k=(1,2,-3), a=(4,1,2), \nu=0.0005, L_0=2.4$, the synthesizer verifies $\nabla\cdot u_0 = 0$, $\nabla\times u_0 = (7,-14,-7)$, $E_0=10.5$, $Z_0=147.0$, $P_0=2058.0$, $\|u_0\|_{H^3}=266.2236$, $\eta_K = 0.006422\text{ m} < \rho_{\text{CF}} = 0.839626\text{ m}$, $j_{\text{adapt}} = 29$, and `UNSAT` (`dZ/dt_upper = -693.996029`, seal `0x2F3FECC4`), mirrored in `clay_millennium_v4_autonomous_zero_hypothesis_initial_data_synthesizer`.

---

## 3. True 3D Navier–Stokes PDE Formalization on $\mathbb{T}^3$ (Milestones 1–8, Lean 4 Tier C)

New in **`v4.0.0`**, `formal_proofs_mathlib/` adds **18 interconnected Mathlib4 modules (152 `#print axioms`-audited theorems, `0 sorryAx`)** constructing the complete analytical PDE theory on $\mathbb{T}^3 = (\mathbb{R}/\mathbb{Z})^3$:

1. **Milestones 1–3 (`Real3DVectorCalculus`, `VorticityEquation3D`, `LerayEnergyTorus3D`, `LerayEnergyLaw3D` — 26 theorems):** True Fréchet-derivative 3D differential operators (`div3D`, `curl3D`, `grad3D`, `laplacian3D`, `advection3D`), Schwarz mixed-partial symmetry (`curl3D_grad3D_eq_zero`), exact derivation of the 3D vorticity equation (`navier_stokes_3d_vorticity_equation`), periodic integration by parts (`torusIntegral_ibp`, `gauss_leray_transport_zero`), and the continuous-time Leray kinetic energy and enstrophy evolution laws.
2. **Milestones 4–5 (`PoincareSobolevTorus3D`, `FourierSpectralTorus3D`, `SpectralOperatorsTorus3D`, `ParsevalSobolevTorus3D`, `SobolevEmbeddingTorus3D` — 52 theorems):** Momentum conservation, zero-mean vorticity, sharp 3D Wirtinger–Poincaré inequality ($4\pi^2 \Vert{}u\Vert{}_{L^2}^2 \le \Vert{}\nabla u\Vert{}_{L^2}^2$), sharp exponential energy decay $E(t) \le E_0 e^{-8\pi^2\nu t}$, spectral Biot–Savart & orthogonal Leray projection (`lerayProj3D_pythagoras`), global $L^2$ Calderón–Zygmund pressure estimate, Parseval–Plancherel identities, Sobolev $H^2(\mathbb{T}^3) \hookrightarrow L^\infty(\mathbb{T}^3)$, Agmon's 3D inequality, and heat-kernel smoothing bounds.
3. **Milestone 6 (`SpectralAlgebraTorus3D`, `SpectralBilinearTorus3D`, `DuhamelOperatorTorus3D`, `LocalExistenceTorus3D` — 31 theorems):** Weighted $H^2(\mathbb{T}^3)$ convolution algebra via Young $\ell^1 * \ell^2 \to \ell^2$, Lipschitz estimates for the heat-smoothed Leray-projected bilinear form `heatSmoothedBilinear6A`, self-mapping and $1/4$-contraction of the Duhamel integral operator `duhamelOp`, and **Picard–Banach local existence & uniqueness** (`local_existence_uniqueness_ns3d_torus3D`) for arbitrary $u_0 \in H^2_{\mathrm{div}}(\mathbb{T}^3)$ with exact spectral time-differentiability and Poisson pressure identity.
4. **Milestone 7 (`GlobalRegularityCriteriaTorus3D`, `GarrySupercriticalBridgeTorus3D`, `SupercriticalBoundaryAuditTorus3D` — 21 theorems):**
   * *Milestone 7A:* Differential Grönwall, true 3D BKM continuation criteria on $\mathbb{T}^3$, classical $C^3$ uniqueness, Duhamel semigroup gluing (`duhamelRaw_semigroup_glue`), and **unconditional global existence on $[0, \infty)$ for small mean-zero data** (`h2VecNormSq u₀ ≤ π² ν² / 217088`).
   * *Milestone 7B:* Formal proof of the supercritical $Z^3$ Young absorption wall (`supercritical_young_absorption_wall_torus3D`), direct bridging of Garry Theorems 8/9/11/12/16 to true 3D Lebesgue integrals, global mild uniqueness on every $[0, T]$, and global continuation from uniform $H^2$ bounds.
   * *Milestone 7C:* Formal proof of the 3D supercritical energy scaling barrier (`ns3d_supercritical_energy_barrier`), unconditional tame Wiener-$\ell^1 \to H^2$ continuation (`unconditional_wiener_a_priori_H2_bound_torus3D`), non-vacuity of `GarryConditionalClosureHypotheses` (`garry_closure_hypotheses_nonvacuous`), and the two-tier boundary audit (`milestone7_two_tier_boundary_audit_torus3D`).
5. **Milestone 8 (`HigherSobolevBootstrapTorus3D`, `SmoothClassicalSynthesisTorus3D` — 22 theorems):**
   * *Milestone 8A ("Waterfall-to-River" Transfer Law & Arbitrary-Order Bootstrap):* Proves `finite_time_basin_entry_global_ns3d_torus3D` (any large-data mean-zero solution entering the small-data basin at finite time $T_{\mathrm{enter}}$ extends uniquely and unconditionally to $[0, \infty)$), compatible-viscosity global admissibility for arbitrarily large $u_0$ when $217088\Vert{}u_0\Vert{}_{H^2}^2 \le \pi^2\nu^2$, arbitrary-order tame convolution in $H^{s/2}(\mathbb{T}^3)$, half-derivative parabolic heat smoothing with $(t-s)^{-3/2}$ Duhamel integration, **unconditional instantaneous $H^2 \to H^m(\mathbb{T}^3)$ bootstrap for all $m \in \mathbb{N}$** (`higher_sobolev_bootstrap_all_orders_torus3D`), and the direct bridge to Garry Theorem 13.
   * *Milestone 8B (Exact $H^\infty \hookrightarrow C^\infty$ Classical Synthesis & Grand Master Theorem):* Proves Fourier convolution multiplication, termwise Fréchet differentiability, inductive $H^{n+3}(\mathbb{T}^3) \hookrightarrow C^n(\mathbb{T}^3)$ for all $n \in \mathbb{N}$ (`ContDiff ℝ (⊤ : ℕ∞)`), Calderón–Zygmund $C^\infty(\mathbb{T}^3)$ regularity of the physical pressure `pressureCoeff6B`, **exact pointwise physical-space 3D Navier–Stokes PDE satisfaction** (`mild_solution_physical_ns3d_torus3D`):

     $$\frac{\partial U_c}{\partial t}(t, x) + (U(t)\cdot\nabla)U_c(t, x) + \partial_c P(t, x) = \nu \Delta U_c(t, x),$$
     $$\nabla \cdot U(t, x) = 0,$$

     and unifies all 8 milestones into `garry_millennium_master_theorem_torus3D`.

---

## 4. Explicit Two-Tier Mathematical Boundary & Anti-Circularity Disclosure

To prevent any conflation of conditional and unconditional results, `garry-ultimate-oss` **v4.0.0** enforces an explicit mathematical boundary verified inside the Lean 4 kernel:

* **Tier I (Unconditional on $\mathbb{T}^3$, zero extra premises):** Local $C^\infty$ classical solutions for arbitrary $u_0 \in H^2_{\mathrm{div}}(\mathbb{T}^3)$; global $C^\infty$ classical solutions on $(0, \infty)$ for small data, compatible viscosity ($217088\Vert{}u_0\Vert{}_{H^2}^2 \le \pi^2\nu^2$), or finite-time basin entry; global uniqueness (classical $C^3$ and mild $H^2$); true 3D BKM and Wiener-$\ell^1$ tame continuation; and formal proofs of the supercritical $Z^3$ Young wall and 3D energy scaling barrier.
* **Tier II (Conditional Garry Supercritical Closure — Non-Vacuous & Non-Circular):** The Garry supercritical closure hypotheses (including `GarryConditionalClosureHypotheses`, $\sqrt{Z}$-cancellation + Kolmogorov core floor, and quartic Young / Bony triad absorption) are explicitly declared as theorem inputs, formally proven non-vacuous, connected directly to true 3D torus integrals, and proven to imply global $C^\infty(\mathbb{T}^3)$ physical-space solutions on $(0, \infty)$.
* **Open Boundary:** Unconditional global regularity for arbitrary large initial data at arbitrarily small $\nu > 0$ without Tier II closure hypotheses remains open (the Clay Millennium Problem) and is never concealed behind any `sorryAx` or custom axiom.

---

## 5. 128-Bit Interval SMT Prover, Benchmarks & Verified Suites (`ns_1` – `ns_5` + `autonomous_u0`)

In the pure-Rust kernel (`GARRYULT`), `RationalInterval128` maps continuous invariants into 128-bit micro-scaled integer intervals ($10^6$ scaling, mandatory outward rounding $\underline{X} = \lfloor 10^6 x \rfloor - 1$, $\overline{X} = \lceil 10^6 x \rceil + 1$). Across all 5 canonical verification suites (`ns_1`–`ns_5`) and the v4.0.0 autonomous synthesizer (`autonomous_u0`), every CRC-32 seal is 100% deterministic:

| Suite | Flow Manifold / Mode | Stretch $S$ / Tail | Viscous $D$ / Reserve | SMT $\dot{Z}_{\text{upper}}$ | Tree / Report CRC-32 |
| :--- | :--- | :---: | :---: | :---: | :---: |
| **`ns_1`** | `prandtl_navier_river` (48k / BKM 18.21) | 57.6196 | 575.4737 | `-517.854144` (`UNSAT`) | `0x64C6A3D2` / `0x05FB1C67` |
| **`ns_2`** | `kolmogorov_k41_cascade` (176k / BKM 41.49) | 140.4789 | 466.3490 | `-325.870087` (`UNSAT`) | `0x088739AE` / `0x19BFD591` |
| **`ns_3`** | `beale_kato_majda_bkm` (40.1k / BKM 14.97) | 51.6772 | 556.2415 | `-504.564248` (`UNSAT`) | `0x86ACA950` / `0x6AFEC037` |
| **`ns_4`** | `omniverse_10pillar` (30k / BKM 13.53) | 42.8702 | 336.9765 | `-294.106363` (`UNSAT`) | `0xEC6CD742` / `0x0A0CF0A5` |
| **`ns_5`** | `8-Axiom / 20-Stage` (30k / BKM 13.53) | 42.8702 | 336.9765 | `-294.106363` (`UNSAT`) | `0xEC6CD742` / `0xBE75C6B3` |
| **`autonomous_u0`** | Raw 3D Mode $k=(1,2,-3), a=(4,1,2), \nu=5\times 10^{-4}$ | `767,872` (micro) | `566,636,339` (micro) | `-693.996029` (`UNSAT`) | Seal `0x2F3FECC4` |

Measured bare-metal $O(1)$ stack latencies (5,000-iteration mean, `cargo run --release -- bench` on `garry-ultimate-oss` v4.0.0): `115.92 ns` DAG resolution, `1015.00 ns` full symbolic/SMT deduction tree, `50.98 ns` 8-cycle ISA execution, and `14.34 us` (`523.07 MB/s`) for the 7,865-byte IEEE 802.3 CRC-32 checkpoint.

---

## 6. Independent Referee Verification Protocol

An independent reviewer can audit the entire `v4.0.0` verification stack from source with zero trust in pre-generated logs:

1. **Pure-Rust Kernel, Autonomous Synthesizer & Adversarial Falsification (`0` External Crates, `30/30` Tests):**
   ```bash
   cargo tree --depth 1
   cargo clippy --all-targets -- -D warnings
   cargo test --release --verbose
   cargo run --release -- bench
   cargo run --release -- solutions
   cargo run --release -- synthesize
   ```
2. **External SMT-LIB 2.6 (`QF_LIA`) Verification via Z3 (7 `.smt2` files):**
   ```bash
   z3 garry_workspace/solutions/navier_stokes_smtlib_certificate.smt2   # Expected: unsat
   z3 garry_workspace/solutions/autonomous_u0_smtlib_certificate.smt2   # Expected: unsat
   ```
3. **Complete 234-Theorem Lean 4 & Mathlib4 Kernel Audit (`0 sorryAx`, `0` Custom Axioms):**
   ```bash
   lean garry_workspace/solutions/navier_stokes_lean4_certificate.lean
   lean garry_workspace/solutions/autonomous_u0_lean4_certificate.lean
   cd formal_proofs_mathlib
   lake build SmoothClassicalSynthesisTorus3D
   lake env lean SupercriticalBoundaryAuditTorus3D.lean
   lake env lean SmoothClassicalSynthesisTorus3D.lean
   ```
   Every `#print axioms` audit must depend exclusively on `[propext, Classical.choice, Quot.sound]` (or `[propext, Quot.sound]` in Tier A), and running `./verify_all.sh` automates all 8 verification stages including `sha256sum -c SHA256SUMS.txt`.

---

## 7. Author Contributions & Disclosure

All mathematical formulations, the two-tier Navier–Stokes architecture, the `#![no_std]` pure-Rust kernel (`GARRYULT`), and the 128-bit rational interval SMT and 19-module Lean 4 / Mathlib4 verification pipelines were conceived, designed, implemented, and verified by the author. In accordance with COPE guidelines, AI tools were used strictly for English language editing, Markdown/LaTeX typesetting, and interactive Lean 4 tactic engineering under the author's independent kernel verification (`lake build`).

---

## References

1. **Fefferman, C. L.** (2006). Existence and smoothness of the Navier-Stokes equation. *The Millennium Prize Problems*, 57–67. Clay Mathematics Institute, Cambridge, MA.
2. **Constantin, P., & Fefferman, C.** (1993). Direction of vorticity and the problem of global regularity for the Navier-Stokes equations. *Indiana University Mathematics Journal*, 42(3), 775–789. https://doi.org/10.1512/iumj.1993.42.42034
3. **Beale, J. T., Kato, T., & Majda, A.** (1984). Remarks on the breakdown of smooth solutions for the 3-D Euler equations. *Communications in Mathematical Physics*, 94(1), 61–66. https://doi.org/10.1007/BF01212349
4. **Caffarelli, L., Kohn, R., & Nirenberg, L.** (1982). Partial regularity of suitable weak solutions of the Navier-Stokes equations. *Communications on Pure and Applied Mathematics*, 35(6), 771–831. https://doi.org/10.1002/cpa.3160350604
5. **De Moura, L., & Bjørner, N.** (2008). Z3: An efficient SMT solver. In *TACAS 2008* (pp. 337–340). Springer. https://doi.org/10.1007/978-3-540-78800-3_24
6. **De Moura, L., & Ullrich, S.** (2021). The Lean 4 theorem prover and programming language. In *CADE 2021* (pp. 625–635). Springer. https://doi.org/10.1007/978-3-030-79876-5_37
7. **Nguyễn, N. N.** (2026). *GARRYULT: Bare-Metal O(1) Stack-Bounded Symbolic PDE, 128-Bit Interval SMT & Two-Tier Lean 4 / Mathlib4 3D Navier–Stokes Formalization* [Computer software]. CERN Zenodo Concept DOI: https://doi.org/10.5281/zenodo.24252962 (v3.0.0 DOI: https://doi.org/10.5281/zenodo.24344944; v2.0.0 DOI: https://doi.org/10.5281/zenodo.24311836). UNESCO SWHID (v3.0.0 Baseline): `swh:1:dir:4ee205fa955cb5c4032e28d0786d6c50baff730f`.
8. **Nguyễn, N. N.** (2026). *A Bare-Metal O(1) Symbolic PDE, 128-Bit Interval SMT & Two-Tier Lean 4 / Mathlib4 Formalization of the 3D Incompressible Navier–Stokes Equations on $\mathbb{T}^3$* [Preprint]. CERN Zenodo Concept DOI: https://doi.org/10.5281/zenodo.24267996 (v3.0.0 DOI: https://doi.org/10.5281/zenodo.24346364).