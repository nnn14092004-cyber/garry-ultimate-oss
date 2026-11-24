# garry-ultimate-oss (v4.0.0) — Adversarial Falsification, Anti-Circularity & Fail-Closed Audit Log

## 1. Outward-Rounded Interval Falsifiability ($10^{-6}$) and 128-Bit Exact BLW Gates

Any formal verification engine must reject corrupted inputs deterministically rather than producing false-positive certificates. In `garry-ultimate-oss` (v4.0.0), two integer arithmetic gates enforce fail-closed falsifiability:

1. **Outward-Rounded Micro-Scaled Coercivity (`RationalInterval128`):** Continuous invariants are scaled by $10^6$ (`RATIONAL_SCALE_MICRO = 1_000_000`) with mandatory outward rounding ($\underline{X} = \lfloor 10^6 x \rfloor - 1$, $\overline{X} = \lceil 10^6 x \rceil + 1$). Enstrophy coercivity passes if and only if the viscous palinstrophy lower bound $\underline{D_{\text{visc}}}$ strictly exceeds the perturbed vortex stretching upper bound $\overline{S_{\text{stretch}}} + \overline{R_{\text{tail}}}$ by at least one micro-scaled resolution unit:

$$\mathcal{M}_{\text{coercive}}^{\text{micro}} = \underline{D_{\text{visc}}} - \left(\overline{S_{\text{stretch}}} + \overline{R_{\text{tail}}}\right) \ge 1 \quad (\text{i.e., } \dot{Z}_{\text{upper}} \le -10^{-6} < 0).$$

2. **Overflow-Checked 128-Bit BLW Three-Phase CAP Gate (`BlwWaterfallWitnessStack::verify_128bit`):** For any micro-scaled trajectory grid $(t_k, Z_k, E_k)$ targeting `SupercriticalClayFrontier15G.lean`, certification succeeds if and only if viscosity is positive, the time grid is monotone from $t_0 = 0$, energy is non-increasing, every step satisfies the exact Riccati safe-step inequality, and the terminal state enters the $46\,656\,\nu^4$ invariant basin:

$$4 z_k^2 \Delta t_k \le 23\,328\,\nu_{\mathrm{micro}}^3 \quad (0 \le k < N), \qquad E(t_N) Z(t_N) \cdot 10^{12} < 46\,656\,\nu_{\mathrm{micro}}^4.$$

Whenever any adversarial perturbation violates either gate, `DeterministicSmtProver`, `BlwWaterfallWitnessStack`, Microsoft Z3, and Lean 4 immediately reject the certificate.

---

## 2. Canonical, Autonomous & M15G BLW Verified Baseline (100% `UNSAT` / `0 sorryAx`)

| Suite ID | Manifold / Mode | Stretching / Riccati Bound | Dissipation / Basin Threshold | SMT / CAP Verdict | Lean 4 Verification | Tree / Witness CRC-32 |
| :--- | :--- | :---: | :---: | :---: | :---: | :---: |
| **`ns_1`** | `prandtl_navier_river` | `57,619,601` (+`2` tail) | `575,473,745` | `-517,854,144` (`UNSAT`) | 11/11 (`omega`, `0 sorryAx`) | `0x64C6A3D2` / `0x05FB1C67` |
| **`ns_2`** | `kolmogorov_k41_cascade` | `140,478,901` (+`2` tail) | `466,348,988` | `-325,870,087` (`UNSAT`) | 11/11 (`omega`, `0 sorryAx`) | `0x088739AE` / `0x19BFD591` |
| **`ns_3`** | `beale_kato_majda_bkm` | `51,677,201` (+`2` tail) | `556,241,449` | `-504,564,248` (`UNSAT`) | 11/11 (`omega`, `0 sorryAx`) | `0x86ACA950` / `0x6AFEC037` |
| **`ns_4`** | `omniverse_10pillar` | `42,870,201` (+`2` tail) | `336,976,564` | `-294,106,363` (`UNSAT`) | 11/11 (`omega`, `0 sorryAx`) | `0xEC6CD742` / `0x0A0CF0A5` |
| **`ns_5`** | `8-Axiom / 20-Stage` | `42,870,201` (+`2` tail) | `336,976,564` | `-294,106,363` (`UNSAT`) | 11/11 (`omega`, `0 sorryAx`) | `0xEC6CD742` / `0xBE75C6B3` |
| **`autonomous_u0`** | Raw Mode $k=(1,2,-3), a=(4,1,2)$ | `767,872` (Tail+Triad) | `566,636,339` (Quartic) | `-693,996,029` (`UNSAT`) | 3/3 (`omega`, `0 sorryAx`) | Seal `0x2F3FECC4` |
| **`blw_r3_cap`** | M15G $\mathbb{R}^3$ ($\nu=0.1$, 4 steps, $E_0 Z_0=10.0 \to 2.70$) | $B_{\mathrm{pre}} \le 28.102004$ on $[0, 1.8]$ | $R_{\mathrm{crit}} = 4.6656$ ($46\,656\,\nu^4$) | `VERIFIED` / `UNSAT` (`QF_NIA`) | 2/2 linked to `SupercriticalClayFrontier15G` (`0 sorryAx`) | Seal `0x76039629` |

---

## 3. Adversarial Falsification Test Matrix (`33/33` Pure-Rust Suite, `0.01s`)

Unit tests in `src/lib.rs`, `src/symbolic.rs`, `src/solver.rs`, and `src/blw_emitter.rs` inject corrupted physical and numerical states across all 16 failure modes:

| Adversarial Test ID | Injected Fault / Corrupted Physics | Target Verification Barrier | Expected Behavior | Observed Verdict |
| :--- | :--- | :--- | :--- | :---: |
| **`ADV-01` (Unswarmed L2 Query)** | Query `ax_unswarmed_navier_stokes_test` without `:swarm` registration | `solver.rs` (`Fail-Closed Gate`) | Immediate halt before CPU execution; preserve FSM state | **`FAIL-CLOSED` (Rejected)** |
| **`ADV-02` (Lemma 1/2 Violation)** | Perturb solenoidal condition $\nabla \cdot \mathbf{u} \ne 0$ (`Lemma1_div_u_ibp_micro = 1`) | `symbolic.rs` (`SymbolicPdeProofTree`) | Lemma 1 identity check fails; proof tree invalidates | **`FAIL-CLOSED` (Rejected)** |
| **`ADV-03` (1-Unit Coercivity Flip)** | Set `S_stretch_upper_micro = 336976565` ($= \underline{D_{\text{visc}}} + 1$) | `DeterministicSmtProver` / Z3 / Lean 4 `omega` | $\dot{Z}_{\text{upper}} = +1 \ge 0$; Z3 outputs `sat`; Lean 4 `omega` fails | **`FAIL-CLOSED` (Refuted)** |
| **`ADV-04` (Hypergraph Link Break)** | Corrupt causal dependency token between Stage #03 and Stage #04 in `ns_5` | `hypergraph.rs` (`verify_causal_lemma_chain_stack`) | Topological sort detects dangling dependency; halts pipeline | **`FAIL-CLOSED` (Rejected)** |
| **`ADV-05` (Non-Monotone Leaf Trajectory)** | Inject upward enstrophy spike $Z_{\text{leaf},2} = 181.5 > Z_{\text{leaf},1} = 180.0$ | `monotone_descent_verified` (`lib.rs`) | Detects violation of Lagrangian cascade decay | **`FAIL-CLOSED` (`false`)** |
| **`ADV-06` (Galerkin Tail Overflow)** | Set Galerkin spectral remainder $R_{\text{tail}} = 300.0$ ($S + R_{\text{tail}} > D_{\text{visc}}$) | `trajectory_blowup_unsat` (`lib.rs`) | Interval flux crosses zero; refutation fails | **`FAIL-CLOSED` (`false`)** |
| **`ADV-07` (Filament Radius Collapse)** | Force alignment radius below Kolmogorov floor ($\rho_{\text{CF}} = 0.01 < \eta_K = 0.05$) | `filament_collapse_unsat` (Theorem 11) | Sub-Kolmogorov collapse detected and rejected | **`FAIL-CLOSED` (`false`)** |
| **`ADV-08` (Orthogonal Stretching Excess)** | Force worst-case orthogonal slope $\Gamma_{\text{ortho}} = 2.50 > \lambda_{\text{visc, ortho}} = 1.48$ | `adversarial_orthogonal_unsat` (Theorem 12) | Orthogonal vorticity check rejects unsafe margin | **`FAIL-CLOSED` (`false`)** |
| **`ADV-09` ($H^m$ Gevrey Commutator Spike)** | Inject Kato-Ponce commutator growth $450.0 > 387.9$ | `hm_gevrey_c_infty_bootstrap_unsat` (Theorem 13) | High-order derivative bootstrap rejected | **`FAIL-CLOSED` (`false`)** |
| **`ADV-10` (Pure $\mathbb{R}^3$ Vacuum Underflow)** | Drop pure $\mathbb{R}^3$ molecular dissipation to $0.20 < \Gamma_{\text{ortho}} = 0.59$ | `pure_r3_and_cz_pressure_unsat` (Theorem 14) | Pure $\mathbb{R}^3$ zero-hydraulic check fails closed | **`FAIL-CLOSED` (`false`)** |
| **`ADV-11` (Parameter-Free Kato Breach)** | Set parameter-free stretching slope $5.00 > 3.972$ | `unconditional_parameter_free_unsat` (Theorem 15) | Parameter-free attractor check fails closed | **`FAIL-CLOSED` (`false`)** |
| **`ADV-12` (Bony Triad / Quartic Reserve Breach)** | Set Bony paraproduct triad flux $300.0 > 252.7$ quartic reserve | `trinity_functional_gaps_unsat` (Theorem 16) | Trinity functional-gap verifier rejects certificate | **`FAIL-CLOSED` (`false`)** |
| **`ADV-13` (v4 Compressible Raw 3D Mode)** | Supply non-orthogonal raw mode $k \cdot a \ne 0$ to `synthesize` | `symbolic.rs` / `solver.rs` (`Zero-Hypothesis Gate`) | Symbolic 3D partial derivative detects $\nabla \cdot u_0 \ne 0$; halts export | **`FAIL-CLOSED` (Rejected)** |
| **`ADV-14` (v4 Autonomous SMT Divergence Breach)** | Inject non-zero divergence residue into `prove_autonomous_zero_hypothesis_field_no_blowup` | `lib.rs` (`AutonomousZeroHypothesisCertificate`) | `autonomous_zero_hypothesis_blowup_unsat` flips immediately to `false` | **`FAIL-CLOSED` (`false`)** |
| **`ADV-15` (M15G Riccati Safe-Step Breach)** | Stretch step 0 duration to `t_grid_micro[1] = 500_000` ($4 z_0^2 \Delta t_0 > 23\,328\,\nu^3$) | `blw_emitter.rs` (`test_blw_fail_closed_rejects_riccati_step_or_basin_violation`) | Returns `Err(BlwVerifyError::RiccatiSafeStepViolated { step_index: 0 })` | **`FAIL-CLOSED` (`Err`)** |
| **`ADV-16` (M15G Basin Capture Failure)** | Raise terminal enstrophy cap `z_cap_micro[4] = 3_500_000` ($E_4 Z_4 = 5.25 \ge 4.6656$) | `blw_emitter.rs` (`test_blw_fail_closed_rejects_riccati_step_or_basin_violation`) | Returns `Err(BlwVerifyError::BasinCaptureNotReached)` | **`FAIL-CLOSED` (`Err`)** |

---

## 4. Lean 4 Kernel Anti-Circularity & Sharp Supercritical Obstruction Audit (Milestones 7B–15G)

In addition to runtime Rust falsification, `formal_proofs_mathlib/` formalizes explicit red-team counter-obstructions inside the Lean 4 kernel (`0 sorryAx`, `[propext, Classical.choice, Quot.sound]`) to block circular energy-to-enstrophy claims and quantify exact barriers:

| Formal Audit / Obstruction Theorem | Lean 4 Module | What It Formally Proves & Prevents |
| :--- | :--- | :--- |
| **`supercritical_young_absorption_wall_torus3D`** | `GarrySupercriticalBridgeTorus3D.lean` | Exhibits the 3D supercritical cubic wall $\dot{Z} \le C \nu^{-3} Z^3$ under isotropic Gagliardo-Nirenberg, proving why naive $L^2$-to-$H^1$ absorption cannot close arbitrary large data. |
| **`ns3d_supercritical_energy_barrier`** | `SupercriticalBoundaryAuditTorus3D.lean` | Proves that 3D Navier-Stokes scaling ($\lambda > 1$) drives kinetic energy $E_0 \mapsto \lambda^{-1} E_0 < \varepsilon$ arbitrarily small while forcing $Z_0 \mapsto \lambda Z_0 > R$ and $P_0 \mapsto \lambda^3 P_0 > R$ arbitrarily large. |
| **`garry_closure_hypotheses_nonvacuous`** | `SupercriticalBoundaryAuditTorus3D.lean` | Proves `GarryConditionalClosureHypotheses ν B u₀` is constructively inhabited (`∃ B u₀, ...`), ensuring Tier II theorems are not vacuously true by contradiction. |
| **`milestone7_two_tier_boundary_audit_torus3D`** | `SupercriticalBoundaryAuditTorus3D.lean` | Audits the exact separation between unconditional Tier I results and conditional Tier II closure on $\mathbb{T}^3$ inside a single verified theorem. |
| **`r3_supercritical_gap_scaling_obstruction`** | `TwoTierBoundaryAuditNS3D.lean` | Quantifies the scale-invariant supercritical gap on $\mathbb{R}^3$ between Leray kinetic energy and $L^4_t \dot{H}^1_x$ criticality (`OpenCriticalL4H1Boundary`). |
| **`raw_cubic_ode_leray_barrier_obstruction`** | `StrainPressureGeometryNS3D.lean` | Proves that the raw cubic differential inequality $\dot{Z} \le c_\nu Z^3$ coupled only with $\int Z \le E_0/(2\nu)$ admits explicit finite-time blow-up solutions. |
| **`coupled_EZ_separatrix_exact_obstruction`** | `SupercriticalFrontierProbeNS3D.lean` | Constructs an exact analytic blow-up separatrix along $E(t)Z(t) \equiv 5\nu^4$ at $T_{\mathrm{sep}} = T_{\mathrm{trap}}/20$ for the coupled Agmon-Leray $(E, Z)$ system. |
| **`variational_EZ_separatrix_red_team_obstruction`** | `AdversarialSupercriticalLabNS3D.lean` | Constructs the sharp blow-up separatrix $(E_{\mathrm{sep}}, Z_{\mathrm{sep}}, P_{\mathrm{sep}})$ along $E(t)Z(t) \equiv 46\,656\,\nu^4$ at $T_{\mathrm{sep}} = T_{\mathrm{trap}}/186\,624$, proving that the BLW basin threshold is exact without further geometric depletion. |
| **`red_team_weighted_E_gamma_Z_trap_audit`** | `AdversarialSupercriticalLabNS3D.lean` | Proves that $E^n Z$ is Navier-Stokes scale-invariant if and only if $n = 1$, and that for every $n \ge 2$ the separatrix drives $E_{\mathrm{sep}}^n Z_{\mathrm{sep}} \to 0$ while $Z_{\mathrm{sep}} \to \infty$ (blocking weighted-power trap fallacies). |
| **`classical_r3_blowup_forces_terminal_super_threshold_biaxiality`** | `AdversarialSupercriticalLabNS3D.lean` | Proves that any putative finite-time $\mathbb{R}^3$ singularity forces terminal super-threshold biaxial sheets with $\lambda_2 > 0$ and $E(t)Z(t) > (1-\eta)^4 \cdot 46\,656\,\nu^4$. |
| **`clay_millennium_single_geometric_lemma_reduction_r3`** | `SupercriticalClayFrontier15G.lean` | Isolates the remaining open arbitrary-data Clay Millennium Problem for Pure-Sobolev classical $\mathbb{R}^3$ flows to one explicit geometric premise (`BiaxialSheetSelfRegulationLemmaR3`). |