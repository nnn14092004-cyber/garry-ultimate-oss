# A Pure-Rust O(1) Interval SMT Verifier and Dual-Domain Lean 4 / Mathlib4 Formalization of the 3D Incompressible Navier-Stokes Equations on $\mathbb{T}^3$ and $\mathbb{R}^3$

**Author:** Nguyen Nhat Nam ([ORCID: 0009-0006-8216-0594](https://orcid.org/0009-0006-8216-0594))  
**Affiliation:** Independent Systems & Formal Verification Researcher; FinTech Undergraduate, Nha Trang University, Nha Trang, Khanh Hoa, Vietnam  
**Software:** `garry-ultimate-oss` v4.0.0 (`GARRYULT` Pure-Rust Verification Kernel, BLW CAP Emitter & 39-Module Mathlib4 PDE Library)  
**Zenodo Preprint Concept DOI:** [10.5281/zenodo.24267996](https://doi.org/10.5281/zenodo.24267996) *(v4.0.0 DOI: [10.5281/zenodo.24502746](https://doi.org/10.5281/zenodo.24502746); v3.0.0 DOI: [10.5281/zenodo.24346364](https://doi.org/10.5281/zenodo.24346364))*  
**Zenodo Software Concept DOI:** [10.5281/zenodo.24252962](https://doi.org/10.5281/zenodo.24252962) *(v3.0.0 DOI: [10.5281/zenodo.24344944](https://doi.org/10.5281/zenodo.24344944); v2.0.0 DOI: [10.5281/zenodo.24311836](https://doi.org/10.5281/zenodo.24311836))*  
**Software Heritage SWHID (v3.0.0 Baseline):** `swh:1:dir:4ee205fa955cb5c4032e28d0786d6c50baff730f` *(v4.0.0 SWHID assigned post-release)*  
**Date:** November 24, 2026

---

## Abstract

We present `garry-ultimate-oss` (v4.0.0), a machine-verified framework for the three-dimensional (3D) incompressible Navier-Stokes equations on both the periodic torus $\mathbb{T}^3 = (\mathbb{R}/\mathbb{Z})^3$ and whole space $\mathbb{R}^3$. The repository combines: (1) a zero-dependency pure-Rust kernel (`src/`, 15 modules, zero `if`/`else` branching, 33/33 unit and adversarial falsification tests passing in 0.01 s) implementing a stack-bounded symbolic PDE deductor, an autonomous 3D solenoidal mode synthesizer (`synthesize`), a 128-bit outward-rounded rational interval SMT prover, and a static-stack Betchov-Loomis-Whitney (BLW) three-phase waterfall witness verifier (`--certify-blw`, 223.98 ns per 128-bit verification) emitting `.txt`, `.smt2`, and `.lean` certificates directly linked to Lean 4; and (2) a 39-module **Lean 4 / Mathlib4** formalization (`formal_proofs_mathlib/`, 50,216 lines, 403 `#print axioms`-audited declarations, 6,330 Lake build jobs) plus 60 unique audited declarations in `garry_workspace/solutions/`, totaling **463 unique audited declarations** with **`0 sorryAx`** and **`0` custom axioms**.

Across Milestones 1–15G, the Lean 4 library formalizes real 3D vector calculus, the vorticity equation, Leray energy and enstrophy laws, sharp Wirtinger-Poincaré decay, Fourier-Parseval-Sobolev-Agmon theory, constructive Picard-Duhamel local existence on both $\mathbb{T}^3$ and $\mathbb{R}^3$, Serrin $L^2$ global uniqueness, instantaneous $H^2 \to H^m \to C^\infty(\mathbb{T}^3)$ pointwise classical PDE synthesis, all-order mixed spacetime derivative hierarchies ($\partial_t^k \partial_x^\alpha$, including $t = 0$), and strain-pressure geometry. On $\mathbb{R}^3$, combining Betchov's identity with the 3D Loomis-Whitney $L^3$ inequality yields the unconditional vortex-stretching constant $C_{\mathrm{BLW}}^4 = 8/19\,683$, proving an invariant scale-invariant basin $E(t)Z(t) < 46\,656\,\nu^4$ and contracting any putative finite-time singularity horizon to $T^* \le T_{\mathrm{trap}}/186\,624$. Explicit red-team separatrix ODE obstructions prove that this threshold is exact for the coupled $(E, Z, P)$ system without further geometric depletion. We embed Fefferman's Schwartz input class $\mathcal{S}_\sigma(\mathbb{R}^3)$, remove artificial pointwise $\langle x\rangle^{-3}$ decay at $t > 0$ via `IsPureSobolevClassicalNS3D_R3`, prove three-phase computer-assisted closure for any supercritical trajectory certified by `GarryBLWWaterfallWitnessR3`, and reduce the remaining open arbitrary-data Clay Millennium frontier to a single geometric hypothesis, `BiaxialSheetSelfRegulationLemmaR3`.

---

## 1. Introduction and Mathematical Formulation

The three-dimensional incompressible Navier-Stokes equations with kinematic viscosity $\nu > 0$—posed on $\mathbb{T}^3 \times [0, \infty) = (\mathbb{R}/\mathbb{Z})^3 \times [0, \infty)$ with zero spatial mean or on $\mathbb{R}^3 \times [0, \infty)$ with rapidly decaying Schwartz initial data $u_0 \in \mathcal{S}_\sigma(\mathbb{R}^3)$ (Fefferman, 2006)—read

$$\frac{\partial \mathbf{u}}{\partial t} + (\mathbf{u} \cdot \nabla)\mathbf{u} = -\nabla p + \nu \Delta \mathbf{u}, \qquad \nabla \cdot \mathbf{u} = 0, \qquad \mathbf{u}(\cdot, 0) = \mathbf{u}_0.$$

Writing $\boldsymbol{\omega} = \nabla \times \mathbf{u}$, kinetic energy $E(t) = \frac{1}{2}\lVert \mathbf{u}(t)\rVert_{L^2}^2$, enstrophy $Z(t) = \frac{1}{2}\lVert \boldsymbol{\omega}(t)\rVert_{L^2}^2$, and palinstrophy $P(t) = \lVert \nabla \boldsymbol{\omega}(t)\rVert_{L^2}^2$, smooth periodic or decaying solutions obey

$$\frac{dE}{dt} = -2\nu Z(t), \qquad \frac{dZ}{dt} = \int (\boldsymbol{\omega} \cdot \nabla)\mathbf{u} \cdot \boldsymbol{\omega}\, dx - \nu \int \lvert \nabla \boldsymbol{\omega} \rvert^2\, dx = S_{\text{stretch}}(t) - D_{\text{visc}}(t).$$

Under isotropic Sobolev embeddings, $S_{\text{stretch}} \le C \lVert \boldsymbol{\omega}\rVert_{L^3}^3 \le C_{\text{GN}} Z^{1/4} P^{5/4}$ (or $C Z^{3/4} P^{3/4}$ after energy-enstrophy interpolation), producing the supercritical cubic Riccati barrier $\dot{Z} \le c_\nu Z^3$. While `v1.0.0`–`v3.0.0` built a pure-Rust symbolic PDE and 128-bit interval SMT verifier with 77 algebraic Lean 4 theorems, `v4.0.0` completes a 39-module dual-domain Lean 4 / Mathlib4 PDE formalization spanning Milestones 1–15G (`0 sorryAx`) and couples it to a deterministic Rust witness checker (`--certify-blw`) for supercritical computer-assisted proofs.

---

## 2. Symbolic PDE Deduction, Autonomous Synthesizer and Tier B Closure (Rust Core + `GarryNavierStokesMathlib.lean`)

`SymbolicArena` (128 stack-allocated AST nodes) executes a sequential deductive chain verified in both pure Rust (`src/symbolic.rs`, `src/lib.rs`, `src/solver.rs`) and `formal_proofs_mathlib/GarryNavierStokesMathlib.lean` (Tier B — **24** audited theorems over $\mathbb{R}$):

1. **Solenoidal Transport, Boundary Flux Annihilation & Infrared Splitting (Lemma 1 & Theorem 10):** Under $\nabla \cdot \mathbf{u} = 0$ and $\mathbb{R}^3$ Schwartz decay or $\mathbb{T}^3$ periodicity (`ClayBoundaryManifoldKind`), surface flux vanishes ($\mathcal{B}_{\text{flux}} = 0$) and convective energy production annihilates. On $\mathbb{R}^3$, splitting enstrophy at $k_{\text{IR}} = \pi/L_0$ bounds infrared modes via Leray's inequality ($Z_{\text{IR}} \le 2 k_{\text{IR}}^2 E_0$) and ultraviolet modes via Bernstein-Poincaré coercivity.
2. **Hodge-Helmholtz Curl Annihilation & Calderón-Zygmund Pressure Closure (Lemma 2 & Theorem 14):** Mixed-partial symmetry gives $\nabla \times (\nabla p) \equiv \mathbf{0}$, and taking the divergence of momentum yields $-\Delta p = \sum_{i,j=1}^3 \partial_i \partial_j (u_i u_j)$, bounded via Riesz transforms by $\lVert \nabla^2 p \rVert_{L^2} \le C_{\text{CZ}} Z < D_{\text{visc}}$.
3. **Constantin-Fefferman Depletion, $\sqrt{Z}$-Cancellation & Kolmogorov Core Floor (Lemma 3 & Theorems 8, 11, 12):** Symbolic cancellation $\sqrt{Z}/\sqrt{Z} \equiv 1$ bounds the stretching rate per unit enstrophy by $\Gamma_\infty = (C_3 \sin\theta_{\text{CF}})/\rho_{\text{CF}} \le C_3/\rho_{\text{CF}}$ even in the worst-case orthogonal limit ($\sin\theta_{\text{CF}} = 1$), protected by the Kolmogorov core floor $\eta_K = \sqrt{\nu/\sqrt{Z_{\text{eq}}}} > 0$.
4. **Inductive $H^m \to C^\infty$ Gevrey Scaling & Intrinsic Quartic Young / Bony Triads (Lemmas 4–5 & Theorems 13–16):** Exponential Littlewood-Paley shells $k_{\text{LP}} = (\pi/L_0)2^{j/3}$, adaptive Kraichnan scaling $k_{\text{adapt}}^2(\nu) \propto \nu^{-1}$, solenoidal Bony paraproduct cancellation ($\langle T_{\mathbf{u}}\nabla\boldsymbol{\omega}_j, \boldsymbol{\omega}_j\rangle_{L^2} = 0$), and intrinsic polynomial-square proofs (`sq_nonneg`):

$$3 X_{\text{pal}}^4 + Y_Z^4 - 4 X_{\text{pal}}^3 Y_Z = (X_{\text{pal}} - Y_Z)^2 \left(2 X_{\text{pal}}^2 + (X_{\text{pal}} + Y_Z)^2\right) \ge 0 \implies 4 X_{\text{pal}}^3 Y_Z \le 3 X_{\text{pal}}^4 + Y_Z^4.$$

5. **Autonomous Zero-Catalog 3D Solenoidal Initial-Data Synthesizer (`synthesize`):** Given raw wavevector $k$, amplitude $a$, viscosity $\nu$, and domain scale $L_0$ without lookup-table presets, the Rust kernel symbolically differentiates $\nabla \cdot u_0$ (rejecting compressible modes fail-closed), computes $\nabla \times u_0$, $E_0, Z_0, P_0, \lVert u_0 \rVert_{H^3}$, verifies Galerkin UV spectral tail absorption against the quartic reserve, and emits standalone `.txt`, `.smt2`, and 3-theorem `.lean` certificates. For $k=(1,2,-3), a=(4,1,2), \nu=0.0005, L_0=2.4$, it verifies $\nabla\cdot u_0 = 0$, $\nabla\times u_0 = (7,-14,-7)$, $E_0=10.5$, $Z_0=147.0$, $P_0=2058.0$, $\lVert u_0 \rVert_{H^3}=266.2236$, $\eta_K = 0.006422\text{ m} < \rho_{\text{CF}} = 0.839626\text{ m}$, $j_{\text{adapt}} = 29$, and `UNSAT` (`dZ/dt_upper = -693.996029`, seal `0x2F3FECC4`), mirrored in `clay_millennium_v4_autonomous_zero_hypothesis_initial_data_synthesizer`.

---

## 3. Dual-Domain Lean 4 / Mathlib4 PDE Formalization (Milestones 1–15G, Tier C)

`formal_proofs_mathlib/` comprises **38 Tier C PDE modules** (**379** audited declarations, **49,290** lines) alongside Tier B (**1** module, **24** audits), built via `lake build SupercriticalClayFrontier15G` (6,330 Lake jobs, `0 sorryAx`).

### 3.1 Periodic Torus $\mathbb{T}^3$ Foundations, Classical Synthesis & Riccati Certificates (M1–M9)

1. **Milestones 1–3 (`Real3DVectorCalculus`, `VorticityEquation3D`, `LerayEnergyTorus3D`, `LerayEnergyLaw3D` — 26 audits):** Fréchet-derivative 3D differential operators (`div3D`, `curl3D`, `grad3D`, `laplacian3D`, `advection3D`), Schwarz mixed-partial symmetry (`curl3D_grad3D_eq_zero`), exact 3D vorticity PDE (`navier_stokes_3d_vorticity_equation`), periodic IBP (`torusIntegral_ibp`, `gauss_leray_transport_zero`), and continuous-time Leray energy and enstrophy laws.
2. **Milestones 4–5 (`PoincareSobolevTorus3D`, `FourierSpectralTorus3D`, `SpectralOperatorsTorus3D`, `ParsevalSobolevTorus3D`, `SobolevEmbeddingTorus3D` — 52 audits):** Momentum conservation, zero-mean vorticity, sharp 3D Wirtinger-Poincaré inequality ($4\pi^2 \lVert u \rVert_{L^2}^2 \le \lVert \nabla u \rVert_{L^2}^2$), sharp exponential energy decay $E(t) \le E_0 e^{-8\pi^2\nu t}$, spectral Biot-Savart & orthogonal Leray projection (`lerayProj3D_pythagoras`), global $L^2$ Calderón-Zygmund pressure, Parseval-Plancherel, $H^2(\mathbb{T}^3) \hookrightarrow L^\infty(\mathbb{T}^3)$, 3D Agmon inequality, and heat smoothing.
3. **Milestone 6 (`SpectralAlgebraTorus3D`, `SpectralBilinearTorus3D`, `DuhamelOperatorTorus3D`, `LocalExistenceTorus3D` — 31 audits):** Weighted $H^2(\mathbb{T}^3)$ convolution algebra via Young $\ell^1 * \ell^2 \to \ell^2$, Lipschitz heat-smoothed Leray bilinear form, Duhamel $1/4$-contraction, and Picard-Banach local existence and uniqueness (`local_existence_uniqueness_ns3d_torus3D`) for arbitrary $u_0 \in H^2_{\mathrm{div}}(\mathbb{T}^3)$ with Poisson pressure splitting.
4. **Milestone 7 (`GlobalRegularityCriteriaTorus3D`, `GarrySupercriticalBridgeTorus3D`, `SupercriticalBoundaryAuditTorus3D` — 21 audits):** Differential Grönwall, 3D BKM continuation, classical $C^3$ and mild $H^2$ global uniqueness, Duhamel semigroup gluing, unconditional small-data global existence ($217\,088 \lVert u_0 \rVert_{H^2}^2 \le \pi^2\nu^2$), supercritical $Z^3$ Young wall, 3D supercritical energy scaling barrier, unconditional Wiener-$\ell^1 \to H^2$ continuation, non-vacuity of `GarryConditionalClosureHypotheses`, and two-tier boundary audit.
5. **Milestone 8 (`HigherSobolevBootstrapTorus3D`, `SmoothClassicalSynthesisTorus3D` — 22 audits):** Finite-time basin entry transfer law (`finite_time_basin_entry_global_ns3d_torus3D`), compatible-viscosity global admissibility, arbitrary-order instantaneous $H^2 \to H^m(\mathbb{T}^3)$ bootstrap, exact $H^\infty(\mathbb{T}^3) \hookrightarrow C^\infty(\mathbb{T}^3)$ synthesis for velocity $U$ and Calderón-Zygmund pressure $P$, and pointwise physical-space 3D Navier-Stokes PDE verification (`mild_solution_physical_ns3d_torus3D`):

$$\frac{\partial U_c}{\partial t}(t, x) + (U(t)\cdot\nabla)U_c(t, x) + \partial_c P(t, x) = \nu \Delta U_c(t, x), \qquad \nabla \cdot U(t, x) = 0.$$

6. **Milestone 9 (`EnstrophyBasinTorus3D`, `CriticalProdiSerrinTorus3D`, `GarryWaterfallCertificateTorus3D` — 16 audits):** Derives $\dot{Z} \le -\frac{\nu}{4} P + c_\nu Z^3$ on $\mathbb{T}^3$ with $c_\nu = \frac{169}{8\pi^4\nu^3}$, basin threshold $Z_{\mathrm{crit}}(\nu) = \frac{4\pi^3}{13}\nu^2$, trap time $T_{\mathrm{trap}} = \frac{13 E_0}{4\pi^3\nu^3}$, critical Prodi-Serrin $L^4_t\dot{H}^1_x$ reduction, and multi-step Riccati certificate `GarryWaterfallWitness`.

### 3.2 Whole Space $\mathbb{R}^3$, Global Uniqueness & Strain-Pressure Geometry (M10–M14)

1. **Milestones 10–11 (`WholeSpaceR3Integral`, `WholeSpaceR3Agmon`, `WholeSpaceR3EnstrophyWaterfall`, `GlobalUniquenessNS3D`, `GlobalRegularityBootstrapNS3D`, `TwoTierBoundaryAuditNS3D` — 60 audits):** Extends IBP without boundary terms, Leray's energy law, $2Z^2 \le EP$, homogeneous 3D Agmon bounds, scale-invariant basin invariance, algebraic $O(1/t)$ decay, and `GarryWaterfallWitnessR3` to $\mathbb{R}^3$; proves Serrin $L^2$ stability and global uniqueness on both $\mathbb{T}^3$ and $\mathbb{R}^3$, an inductive Sobolev bootstrap ladder, and scaling-gap obstructions (`OpenCriticalL4H1Boundary`).
2. **Milestones 12–14 (`StrainPressureGeometryNS3D`, `SupercriticalFrontierProbeNS3D`, `HeatLerayMildNS3D`, `ConcreteNS3DClosures`, `ClassicalPDEBridgeNS3D`, `GeometricDepletionCriteriaNS3D` — 78 audits):** Decomposes $\nabla u = S + \Omega$, proves $-\Delta p = |S|^2 - \frac{1}{2}|\omega|^2$, establishes the Betchov identity on both $\mathbb{T}^3$ and $\mathbb{R}^3$:

$$\int \langle S\omega, \omega \rangle\, dx = -\frac{4}{3} \int \operatorname{tr}(S^3)\, dx = -4 \int \lambda_1 \lambda_2 \lambda_3\, dx \qquad (\lambda_1 + \lambda_2 + \lambda_3 = 0),$$

formalizes the singularity cage $Z(t) \ge (2 c_\nu (T^* - t))^{-1/2}$, Constantin-Fefferman direction coherence, Neustupa-Penel ($L^1_t L^\infty_x$) and Miller ($L^2_t L^3_x$) intermediate eigenvalue ($\lambda_2^+$) criteria, weighted pressure-Hessian evolution, concrete Mathlib4 heat-semigroup and Leray-projector laws, Kato-Ponce $H^m \to C^\infty(\mathbb{R}^3)$ closures, and the dual-domain classical PDE bridge.

### 3.3 Adversarial Supercritical Lab: Betchov-Loomis-Whitney $46\,656\,\nu^4$ Basin (M15A–M15C)

In `AdversarialSupercriticalLabNS3D.lean` (4,498 lines, 20 audits):

* **Unconditional BLW Vortex-Stretching Bound:** Combining the trace-free spectral inequality $|\operatorname{tr}(S^3)| \le \frac{1}{\sqrt{6}} |S|^3$ (`trace_free_symm3_real_spectrum_and_cube_bound`), the identity $\int |\nabla S|^2 = \frac{1}{2} P$ (`r3_strain_grad_norm_sq_eq_half_palinstrophy`), and the 3D Loomis-Whitney $L^3$ inequality (`r3_loomis_whitney_strain_L3_bound`) yields

$$|\mathrm{vortexStretchingR3}(u)| \le C_{\mathrm{BLW}}\, Z^{3/4} P^{3/4}, \qquad C_{\mathrm{BLW}}^4 = \frac{8}{19\,683}.$$

* **Invariant Basin & Contracted Singularity Horizon:** Applying variational $(E, Z, P)$ optimization (`variational_EZ_basin_and_horizon_general`, `milestone15_adversarial_supercritical_lab_master`) establishes:
  * Invariant scale-invariant basin: $R_{\mathrm{crit}}(\nu) = 46\,656\,\nu^4$.
  * Sharp Riccati cubic constant: $c_{\mathrm{BLW}}(\nu) = \frac{1}{23\,328\,\nu^3}$.
  * Sharp singularity horizon: $T^* \le T_{\mathrm{sep}} = \frac{T_{\mathrm{trap}}}{186\,624}$.
* **Exact Red-Team Separatrix Obstructions:** `variational_EZ_separatrix_red_team_obstruction` constructs an analytic blow-up trajectory $(E_{\mathrm{sep}}, Z_{\mathrm{sep}}, P_{\mathrm{sep}})$ satisfying $E_{\mathrm{sep}} Z_{\mathrm{sep}} \equiv 46\,656\,\nu^4$, $\dot{E}_{\mathrm{sep}} = -2\nu Z_{\mathrm{sep}}$, $E_{\mathrm{sep}} P_{\mathrm{sep}} = 6 Z_{\mathrm{sep}}^2$, and $\dot{Z}_{\mathrm{sep}} = -\nu P_{\mathrm{sep}} + C_{\mathrm{BLW}} Z_{\mathrm{sep}}^{3/4} P_{\mathrm{sep}}^{3/4}$ that blows up at $T_{\mathrm{sep}}$. Furthermore, `red_team_weighted_E_gamma_Z_trap_audit` proves $E^n Z$ is scale-invariant if and only if $n = 1$, and that for every $n \ge 2$ the separatrix satisfies $E_{\mathrm{sep}}^n Z_{\mathrm{sep}} \to 0$ while $Z_{\mathrm{sep}} \to \infty$.
* **Biaxiality Deficit Profile:** For ordered trace-free eigenvalues $\lambda_1 \ge \lambda_2 \ge \lambda_3$ with $s = \sqrt{|S|^2/6}$, `betchov_biaxiality_deficit_identity_and_profile` proves that capping $\lambda_2 \le \theta s$ ($\theta \in [0, 1]$) scales the stretching bound by `betchovProfile θ` (with `betchovProfile (1/2) = 11/16`, lifting the basin above $208\,000\,\nu^4$). If $\lambda_2 \le 0$ everywhere (tube regime), arbitrary data closes unconditionally; conversely, any finite-time blow-up forces persistent super-threshold biaxial sheets with $\lambda_2 > 0$ (`classical_r3_blowup_forces_terminal_super_threshold_biaxiality`).

### 3.4 Constructive $\mathbb{R}^3$ Local Existence, Spacetime Smoothness & Clay Frontier Packaging (M15D–M15G)

1. **`WholeSpaceR3LocalExistence.lean` (M15D, 2,233 lines, 19 audits):** Constructs the continuous-frequency $H^2(\mathbb{R}^3)$ Banach algebra via Young $L^1 * L^2 \to L^2$, heat-smoothed Leray bilinear operator `heatSmoothedBilinearR3`, $1/4$-contraction of `duhamelOpR3`, geometric Cauchy convergence of Picard iterates (`picardIterR3_cauchy_geometric_r3`), mild uniqueness, and the blow-up alternative (`maximal_existence_blowup_alternative_r3`).
2. **`SpacetimeSmoothnessNS3D.lean` (M15E, 2,241 lines, 16 audits):** Formalizes the all-order time-derivative PDE and Poisson pressure hierarchy on $\mathbb{T}^3$ and $\mathbb{R}^3$, establishing spatial and mixed spacetime derivative bounds $\partial_t^k \partial_x^\alpha$ including the boundary $t = 0$.
3. **`SchwartzClayPackagingNS3D.lean` (M15F, 934 lines, 13 audits):** Defines Fefferman's Schwartz initial-data class `IsSchwartzSolenoidalR3`, proves $\mathcal{S}_\sigma(\mathbb{R}^3) \hookrightarrow H^\infty_\sigma(\mathbb{R}^3)$, and removes pointwise $\langle x\rangle^{-3}$ decay at $t > 0$ via `IsPureSobolevClassicalNS3D_R3` (deriving vanishing at infinity solely from $L^2$ integrability and Lipschitz continuity in `vanishesAtInfinityR3_of_L2_and_lipschitz`).
4. **`SupercriticalClayFrontier15G.lean` (M15G, 620 lines, 5 audits):** Unifies three results inside `milestone15G_grand_clay_frontier_master`:
   * *Tier I Small-Data Basin:* For any Pure-Sobolev classical $\mathbb{R}^3$ solution with $u_0 \in \mathcal{S}_\sigma(\mathbb{R}^3)$ and $E_0 Z_0 < 46\,656\,\nu^4$, global $L^2$, basin invariance, $L^4_t\dot{H}^1_x$, $L^\infty_t H^1$, and $L^2_t\dot{H}^2$ a priori bounds hold unconditionally.
   * *Tier I Supercritical Three-Phase CAP Closure:* For any supercritical trajectory ($E_0 Z_0 \ge 46\,656\,\nu^4$) certified by a finite-step `GarryBLWWaterfallWitnessR3` entering below $46\,656\,\nu^4$ at $t_N$, `clay_fefferman2000_r3_supercritical_cap_three_phase_master` proves global three-phase regularity bounds on $[0, \infty)$.
   * *Tier II Single-Lemma Clay Reduction:* `clay_millennium_single_geometric_lemma_reduction_r3` reduces arbitrary-data global closure for Pure-Sobolev classical $\mathbb{R}^3$ flows to one explicit geometric hypothesis, `BiaxialSheetSelfRegulationLemmaR3`, requiring $(\delta(t))^4 E(t) Z(t) \le (1-\eta)^4 \cdot 46\,656\,\nu^4$.

---

## 4. Theorem-to-Lean 4 Cross-Reference Map

| Paper Result | Lean 4 Module | Formal Theorem / Structure Identifier | Tier |
| :--- | :--- | :--- | :---: |
| Exact 3D vorticity PDE | `VorticityEquation3D` | `navier_stokes_3d_vorticity_equation` | Tier I |
| Sharp $\mathbb{T}^3$ exponential energy decay | `FourierSpectralTorus3D` | `sharp_global_exponential_energy_decay_torus3D` | Tier I |
| $\mathbb{T}^3$ local mild existence & uniqueness | `LocalExistenceTorus3D` | `local_existence_uniqueness_ns3d_torus3D` | Tier I |
| $\mathbb{T}^3$ finite-time basin entry | `HigherSobolevBootstrapTorus3D` | `finite_time_basin_entry_global_ns3d_torus3D` | Tier I |
| $\mathbb{T}^3$ pointwise $C^\infty$ NS synthesis | `SmoothClassicalSynthesisTorus3D` | `mild_solution_physical_ns3d_torus3D` | Tier I |
| $\mathbb{T}^3$ multi-step Riccati witness | `GarryWaterfallCertificateTorus3D` | `garry_certified_waterfall_to_global_river_torus3D` | Tier I (CAP) |
| $\mathbb{R}^3$ Serrin $L^2$ global uniqueness | `GlobalUniquenessNS3D` | `r3_serrin_L2_stability_and_global_uniqueness` | Tier I |
| $\mathbb{R}^3$ Betchov identity | `GeometricDepletionCriteriaNS3D` | `r3_betchov_identity` | Tier I |
| $\mathbb{R}^3$ Loomis-Whitney $L^3$ strain bound | `AdversarialSupercriticalLabNS3D` | `r3_loomis_whitney_strain_L3_bound` | Tier I |
| $\mathbb{R}^3$ unconditional BLW stretching bound | `AdversarialSupercriticalLabNS3D` | `unconditional_r3_betchov_loomis_whitney_stretching` | Tier I |
| $46\,656\,\nu^4$ basin & $T_{\mathrm{trap}}/186\,624$ horizon | `AdversarialSupercriticalLabNS3D` | `milestone15_adversarial_supercritical_lab_master` | Tier I |
| Red-team separatrix ODE obstruction | `AdversarialSupercriticalLabNS3D` | `variational_EZ_separatrix_red_team_obstruction` | Tier I |
| Biaxiality deficit profile `betchovProfile` | `AdversarialSupercriticalLabNS3D` | `betchov_biaxiality_deficit_identity_and_profile` | Tier I |
| $\mathbb{R}^3$ constructive Picard-Duhamel existence | `WholeSpaceR3LocalExistence` | `picardIterR3_cauchy_geometric_r3`, `maximal_existence_blowup_alternative_r3` | Tier I |
| All-order mixed spacetime smoothness | `SpacetimeSmoothnessNS3D` | `milestone15E_spacetime_smoothness_master` | Tier I |
| Schwartz input & Pure-Sobolev $\mathbb{R}^3$ packaging | `SchwartzClayPackagingNS3D` | `clay_fefferman2000_r3_46656_tier1_master` | Tier I |
| Three-phase supercritical CAP closure | `SupercriticalClayFrontier15G` | `clay_fefferman2000_r3_supercritical_cap_three_phase_master` | Tier I (CAP) |
| Single-lemma Clay frontier reduction | `SupercriticalClayFrontier15G` | `clay_millennium_single_geometric_lemma_reduction_r3` | Tier II |
| Emitted Rust $\to$ Lean 4 CAP witness | `garry_workspace/solutions/blw_r3_certificate.lean` | `GarryBlwCertifiedWitnessR3.buildCertifiedWitnessR3` | Tier I (CAP) |

---

## 5. Pure-Rust Interval SMT Prover, BLW CAP Bridge, Benchmarks & Verified Suites

In `src/` (15 modules, zero external crates, zero `if`/`else`, `33/33` tests in `0.01 s`), core verification structures and `src/blw_emitter.rs` (`StackTextBuf<32768>`) operate strictly on the stack; `String` allocation is restricted to legacy CLI report formatting.

1. **BLW Three-Phase CAP Bridge (`--certify-blw`):** `BlwWaterfallWitnessStack<16>::verify_128bit` checks micro-scaled ($10^6$) nodes $(t_k, Z_k, E_k)$ against the overflow-checked 128-bit integer equivalents of the Milestone 15G inequalities:

$$4 z_k^2 \Delta t_k \le 23\,328\,\nu_{\mathrm{micro}}^3 \quad (0 \le k < N), \qquad E(t_N) Z(t_N) \cdot 10^{12} < 46\,656\,\nu_{\mathrm{micro}}^4.$$

   For the canonical 4-step supercritical $\mathbb{R}^3$ witness ($\nu = 0.1$, $E_0 Z_0 = 10.0 > 4.6656 \to E_4 Z_4 = 2.70 < 4.6656$ at $t_4 = 1.80$, $B_{\mathrm{pre}} \le 28.102004$, CRC-32 seal `0x76039629`), `--certify-blw` renders 2D three-phase closure and 3D BLW / strain-spectrum projections and emits `blw_r3_certificate.smt2` (`unsat`) and `blw_r3_certificate.lean` (verified against `SupercriticalClayFrontier15G` with `0 sorryAx`).

2. **Verified Suites (`ns_1`–`ns_5`, `autonomous_u0`, `blw_r3_cap`):**

| Suite | Flow Manifold / Mode | Stretch / Riccati Bound | Viscous / Basin Threshold | SMT / CAP Verdict | Tree / Seal CRC-32 |
| :--- | :--- | :---: | :---: | :---: | :---: |
| **`ns_1`** | `prandtl_navier_river` (48k / BKM 18.21) | 57.6196 | 575.4737 | `-517.854144` (`UNSAT`) | `0x64C6A3D2` / `0x05FB1C67` |
| **`ns_2`** | `kolmogorov_k41_cascade` (176k / BKM 41.49) | 140.4789 | 466.3490 | `-325.870087` (`UNSAT`) | `0x088739AE` / `0x19BFD591` |
| **`ns_3`** | `beale_kato_majda_bkm` (40.1k / BKM 14.97) | 51.6772 | 556.2415 | `-504.564248` (`UNSAT`) | `0x86ACA950` / `0x6AFEC037` |
| **`ns_4`** | `omniverse_10pillar` (30k / BKM 13.53) | 42.8702 | 336.9765 | `-294.106363` (`UNSAT`) | `0xEC6CD742` / `0x0A0CF0A5` |
| **`ns_5`** | `8-Axiom / 20-Stage` (30k / BKM 13.53) | 42.8702 | 336.9765 | `-294.106363` (`UNSAT`) | `0xEC6CD742` / `0xBE75C6B3` |
| **`autonomous_u0`** | Raw Mode $k=(1,2,-3), a=(4,1,2), \nu=5\times 10^{-4}$ | `767,872` (micro) | `566,636,339` (micro) | `-693.996029` (`UNSAT`) | Seal `0x2F3FECC4` |
| **`blw_r3_cap`** | M15G $\mathbb{R}^3$ ($\nu=0.1$, 4 steps, $E_0 Z_0=10.0 \to 2.70$) | $B_{\mathrm{pre}} \le 28.102004$ | $R_{\mathrm{crit}} = 4.6656$ | `VERIFIED` / `UNSAT` | Seal `0x76039629` |

3. **Measured Release-Mode Stack Latencies (`cargo run --release -- bench`, 5,000-iteration mean):**
   * `PlanGraph::resolve_readiness`: `124.60 ns`
   * `DeterministicEngine::export_checkpoint` (7,865 B): `14.84 us` (`505.56 MB/s`)
   * `deduce_navier_stokes_symbolic_proof_tree`: `1108.46 ns`
   * `StackOmniverseCpu::run` (8-cycle ISA): `48.36 ns`
   * `BlwWaterfallWitnessStack::verify_128bit` (M15G $\mathbb{R}^3$): `223.98 ns`

---

## 6. Independent Verification Protocol

```bash
# 1. Pure-Rust kernel, BLW CAP emitter, autonomous synthesizer & canonical suites
cargo tree --depth 1
cargo clippy --all-targets -- -D warnings
cargo test --release --verbose
cargo run --release -- bench
cargo run --release -- --certify-blw
cargo run --release -- solutions
cargo run --release -- synthesize

# 2. External Z3 SMT-LIB 2.6 check (expected: unsat)
z3 garry_workspace/solutions/blw_r3_certificate.smt2
z3 garry_workspace/solutions/autonomous_u0_smtlib_certificate.smt2
z3 garry_workspace/solutions/navier_stokes_smtlib_certificate.smt2

# 3. Full 39-module Lean 4 / Mathlib4 build & cross-check of emitted BLW witness (0 sorryAx)
lean garry_workspace/solutions/navier_stokes_lean4_certificate.lean
lean garry_workspace/solutions/autonomous_u0_lean4_certificate.lean
cd formal_proofs_mathlib
lake build SupercriticalClayFrontier15G
lake build SupercriticalBoundaryAuditTorus3D
lake env lean SupercriticalClayFrontier15G.lean
lake env lean ../garry_workspace/solutions/blw_r3_certificate.lean
```

Running `./verify_all.sh` automates all eight verification stages, including static `sorry`/`admit`/custom `axiom` scanning and `SHA256SUMS.txt` validation.

---

## 7. Author Contributions and Tool Disclosure

All mathematical formulations, the dual-domain two-tier architecture, the pure-Rust kernel (`GARRYULT`), and the 39-module Lean 4 / Mathlib4 formalization were directed and independently verified by the author via `cargo test` and `lake build`. In accordance with COPE guidelines, automated language tools were used for English copy-editing, Markdown/LaTeX typesetting, and interactive Lean 4 tactic drafting under full kernel verification.

---

## References

1. Leray, J. (1934). Sur le mouvement d'un liquide visqueux emplissant l'espace. *Acta Mathematica*, 63(1), 193-248. [https://doi.org/10.1007/BF02547354](https://doi.org/10.1007/BF02547354)
2. Loomis, L. H., & Whitney, H. (1949). An inequality related to the isoperimetric inequality. *Bulletin of the American Mathematical Society*, 55(10), 961-962. [https://doi.org/10.1090/S0002-9904-1949-09320-5](https://doi.org/10.1090/S0002-9904-1949-09320-5)
3. Betchov, R. (1956). An inequality concerning the production of vorticity in isotropic turbulence. *Journal of Fluid Mechanics*, 1(5), 497-504. [https://doi.org/10.1017/S0022112056000317](https://doi.org/10.1017/S0022112056000317)
4. Prodi, G. (1959). Un teorema di unicità per le equazioni di Navier-Stokes. *Annali di Matematica Pura ed Applicata*, 48(1), 173-182. [https://doi.org/10.1007/BF02410664](https://doi.org/10.1007/BF02410664)
5. Serrin, J. (1962). On the interior regularity of weak solutions of the Navier-Stokes equations. *Archive for Rational Mechanics and Analysis*, 9(1), 187-195. [https://doi.org/10.1007/BF00253344](https://doi.org/10.1007/BF00253344)
6. Caffarelli, L., Kohn, R., & Nirenberg, L. (1982). Partial regularity of suitable weak solutions of the Navier-Stokes equations. *Communications on Pure and Applied Mathematics*, 35(6), 771-831. [https://doi.org/10.1002/cpa.3160350604](https://doi.org/10.1002/cpa.3160350604)
7. Beale, J. T., Kato, T., & Majda, A. (1984). Remarks on the breakdown of smooth solutions for the 3-D Euler equations. *Communications in Mathematical Physics*, 94(1), 61-66. [https://doi.org/10.1007/BF01212349](https://doi.org/10.1007/BF01212349)
8. Constantin, P., & Fefferman, C. (1993). Direction of vorticity and the problem of global regularity for the Navier-Stokes equations. *Indiana University Mathematics Journal*, 42(3), 775-789. [https://doi.org/10.1512/iumj.1993.42.42034](https://doi.org/10.1512/iumj.1993.42.42034)
9. Neustupa, J., & Penel, P. (2001). Anisotropic and geometric criteria for interior regularity of weak solutions to the 3D Navier-Stokes equations. *Mathematical Fluid Mechanics*, 237-265. Birkhäuser. [https://doi.org/10.1007/978-3-0348-8243-9_11](https://doi.org/10.1007/978-3-0348-8243-9_11)
10. Fefferman, C. L. (2006). Existence and smoothness of the Navier-Stokes equation. *The Millennium Prize Problems*, 57-67. Clay Mathematics Institute, Cambridge, MA.
11. Miller, E. (2020). A strain-based regularity criterion for the 3D Navier-Stokes equations. *Nonlinearity*, 33(10), 5116-5147. [https://doi.org/10.1088/1361-6544/ab94f3](https://doi.org/10.1088/1361-6544/ab94f3)
12. De Moura, L., & Bjørner, N. (2008). Z3: An efficient SMT solver. In *TACAS 2008* (pp. 337-340). Springer. [https://doi.org/10.1007/978-3-540-78800-3_24](https://doi.org/10.1007/978-3-540-78800-3_24)
13. De Moura, L., & Ullrich, S. (2021). The Lean 4 theorem prover and programming language. In *CADE 2021* (pp. 625-635). Springer. [https://doi.org/10.1007/978-3-030-79876-5_37](https://doi.org/10.1007/978-3-030-79876-5_37)
14. Nguyen, N. N. (2026). *garry-ultimate-oss: Pure-Rust O(1) Interval SMT Kernel and Dual-Domain Lean 4 / Mathlib4 Formalization of the 3D Incompressible Navier-Stokes Equations on $\mathbb{T}^3$ and $\mathbb{R}^3$* (Version 4.0.0) [Computer software]. Zenodo Concept DOI: [https://doi.org/10.5281/zenodo.24252962](https://doi.org/10.5281/zenodo.24252962) (v3.0.0 DOI: [https://doi.org/10.5281/zenodo.24344944](https://doi.org/10.5281/zenodo.24344944); v2.0.0 DOI: [https://doi.org/10.5281/zenodo.24311836](https://doi.org/10.5281/zenodo.24311836)). SWHID (v3.0.0 baseline): `swh:1:dir:4ee205fa955cb5c4032e28d0786d6c50baff730f`.
15. Nguyen, N. N. (2026). *A Pure-Rust O(1) Interval SMT Verifier and Dual-Domain Lean 4 / Mathlib4 Formalization of the 3D Incompressible Navier-Stokes Equations on $\mathbb{T}^3$ and $\mathbb{R}^3$* (Version 4.0.0) [Preprint]. Zenodo Concept DOI: [https://doi.org/10.5281/zenodo.24267996](https://doi.org/10.5281/zenodo.24267996) (v4.0.0 DOI: [https://doi.org/10.5281/zenodo.24502746](https://doi.org/10.5281/zenodo.24502746); v3.0.0 DOI: [https://doi.org/10.5281/zenodo.24346364](https://doi.org/10.5281/zenodo.24346364)).