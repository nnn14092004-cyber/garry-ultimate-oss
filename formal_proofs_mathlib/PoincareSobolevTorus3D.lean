import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import LerayEnergyLaw3D

/-!
# GARRYULT v4.0.0 — Milestone 4 (Part 1): Enstrophy–Gradient Identity, Global `L¹_t H¹_x`
# Bound, Momentum Conservation, 3D Periodic Poincaré Inequality (Analytical Lemma 4) &
# Exponential Kinetic Energy Decay on `𝕋³` (`0 sorryAx`)
-/

namespace GarryPoincareSobolev3D

open MeasureTheory Filter Topology GarryReal3DCalculus GarryVorticity3D
  GarryLerayTorus3D GarryLerayEnergyLaw3D

private lemma two_add_one_eq_three''' {α : Type*} [AddMonoidWithOne α] :
    (2 : α) + 1 = 3 := by
  rw [← Nat.cast_ofNat (n := 2), ← Nat.cast_one, ← Nat.cast_add]
  exact Nat.cast_ofNat

private lemma contDiff_two_of_three' {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {f : E → F} (hf : ContDiff ℝ 3 f) :
    ContDiff ℝ 2 f :=
  hf.of_le (by rw [← two_add_one_eq_three''']; exact le_self_add)

private lemma contDiff_one_of_two' {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {f : E → F} (hf : ContDiff ℝ 2 f) :
    ContDiff ℝ 1 f :=
  hf.of_le (by rw [← one_add_one_eq_two]; exact le_self_add)

-- ============================================================================
-- SECTION 1: BRIDGE 1 — ENSTROPHY–GRADIENT IDENTITY & GLOBAL L¹_t H¹_x BOUND
-- ============================================================================

/-- Cross-partial integration by parts on `𝕋³`:
    `∫_{𝕋³} (∂_i f)(∂_j g) = ∫_{𝕋³} (∂_j f)(∂_i g)` for `C²` periodic `f, g`. -/
theorem torusIntegral_cross_partial_comm
    {f g : R3 → ℝ} (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g)
    (hpf : IsPeriodic3D f) (hpg : IsPeriodic3D g) (i j : Fin 3) :
    torusIntegral (fun x => partialDerivScalar f x i * partialDerivScalar g x j) =
      torusIntegral (fun x => partialDerivScalar f x j * partialDerivScalar g x i) := by
  have hf1 : ContDiff ℝ 1 f := contDiff_one_of_two' hf
  have hg1 : ContDiff ℝ 1 g := contDiff_one_of_two' hg
  have hgj : ContDiff ℝ 1 (fun y => partialDerivScalar g y j) := contDiff_one_partialDerivScalar hg j
  have hgi : ContDiff ℝ 1 (fun y => partialDerivScalar g y i) := contDiff_one_partialDerivScalar hg i
  have hpgj : IsPeriodic3D (fun y => partialDerivScalar g y j) :=
    IsPeriodic3D.partialDeriv hpg (hg1.differentiable (by simp)) j
  have hpgi : IsPeriodic3D (fun y => partialDerivScalar g y i) :=
    IsPeriodic3D.partialDeriv hpg (hg1.differentiable (by simp)) i
  have hibp_i := torusIntegral_ibp hf1 hgj hpf hpgj i
  have hibp_j := torusIntegral_ibp hf1 hgi hpf hpgi j
  have hsymm : ∀ x : R3,
      f x * partialDerivScalar (fun y => partialDerivScalar g y j) x i =
      f x * partialDerivScalar (fun y => partialDerivScalar g y i) x j := fun x => by
    rw [partial_partial_eq_sndPartial g x hg.contDiffAt i j,
        partial_partial_eq_sndPartial g x hg.contDiffAt j i,
        sndPartial_symm_of_contDiffAt g x hg.contDiffAt i j]
  have heq_mid := torusIntegral_congr hsymm
  linarith

/-- Pointwise 3D vector identity linking `|∇ × u|² + (∇ · u)²` to `|∇u|²` and cross-partial terms. -/
theorem curlNormSq_add_divSq_pointwise (u : R3 → R3) (x : R3) :
    dot3D (curl3D u x) (curl3D u x) + (div3D u x) ^ 2 =
      gradNormSq3D u x +
      2 * ((partialDerivScalar (fun y => u y 0) x 0 * partialDerivScalar (fun y => u y 1) x 1 -
            partialDerivScalar (fun y => u y 0) x 1 * partialDerivScalar (fun y => u y 1) x 0) +
           (partialDerivScalar (fun y => u y 1) x 1 * partialDerivScalar (fun y => u y 2) x 2 -
            partialDerivScalar (fun y => u y 1) x 2 * partialDerivScalar (fun y => u y 2) x 1) +
           (partialDerivScalar (fun y => u y 2) x 2 * partialDerivScalar (fun y => u y 0) x 0 -
            partialDerivScalar (fun y => u y 2) x 0 * partialDerivScalar (fun y => u y 0) x 2)) := by
  unfold dot3D curl3D vec3 div3D gradNormSq3D
  dsimp only
  ring

/-- **Exact 3D Curl–Div–Gradient Identity on `𝕋³`:**
    `∫_{𝕋³} |∇ × u|² dx + ∫_{𝕋³} (∇ · u)² dx = ∫_{𝕋³} |∇u|² dx` for any `C²` periodic `u`. -/
theorem torusIntegral_curlNormSq_add_divSq
    {u : R3 → R3} (hu : ContDiff ℝ 2 u) (hpu : IsPeriodic3D u) :
    torusIntegral (fun x => dot3D (curl3D u x) (curl3D u x)) +
      torusIntegral (fun x => (div3D u x) ^ 2) =
      torusIntegral (gradNormSq3D u) := by
  have hu0 : ContDiff ℝ 2 (fun y => u y 0) := contDiff_pi.mp hu 0
  have hu1 : ContDiff ℝ 2 (fun y => u y 1) := contDiff_pi.mp hu 1
  have hu2 : ContDiff ℝ 2 (fun y => u y 2) := contDiff_pi.mp hu 2
  have hu1_0 : ContDiff ℝ 1 (fun y => u y 0) := contDiff_one_of_two' hu0
  have hu1_1 : ContDiff ℝ 1 (fun y => u y 1) := contDiff_one_of_two' hu1
  have hu1_2 : ContDiff ℝ 1 (fun y => u y 2) := contDiff_one_of_two' hu2
  have hpu0 : IsPeriodic3D (fun y => u y 0) := fun x i => congrArg (fun v => v 0) (hpu x i)
  have hpu1 : IsPeriodic3D (fun y => u y 1) := fun x i => congrArg (fun v => v 1) (hpu x i)
  have hpu2 : IsPeriodic3D (fun y => u y 2) := fun x i => congrArg (fun v => v 2) (hpu x i)
  have hdiff01 : torusIntegral (fun x =>
      partialDerivScalar (fun y => u y 0) x 0 * partialDerivScalar (fun y => u y 1) x 1 -
      partialDerivScalar (fun y => u y 0) x 1 * partialDerivScalar (fun y => u y 1) x 0) = 0 := by
    have hcA : Continuous (fun x => partialDerivScalar (fun y => u y 0) x 0 *
        partialDerivScalar (fun y => u y 1) x 1) :=
      (continuous_partialDerivScalar_of_contDiff hu1_0 0).mul
      (continuous_partialDerivScalar_of_contDiff hu1_1 1)
    have hcB : Continuous (fun x => partialDerivScalar (fun y => u y 0) x 1 *
        partialDerivScalar (fun y => u y 1) x 0) :=
      (continuous_partialDerivScalar_of_contDiff hu1_0 1).mul
      (continuous_partialDerivScalar_of_contDiff hu1_1 0)
    rw [torusIntegral_sub hcA hcB, torusIntegral_cross_partial_comm hu0 hu1 hpu0 hpu1 0 1, sub_self]
  have hdiff12 : torusIntegral (fun x =>
      partialDerivScalar (fun y => u y 1) x 1 * partialDerivScalar (fun y => u y 2) x 2 -
      partialDerivScalar (fun y => u y 1) x 2 * partialDerivScalar (fun y => u y 2) x 1) = 0 := by
    have hcA : Continuous (fun x => partialDerivScalar (fun y => u y 1) x 1 *
        partialDerivScalar (fun y => u y 2) x 2) :=
      (continuous_partialDerivScalar_of_contDiff hu1_1 1).mul
      (continuous_partialDerivScalar_of_contDiff hu1_2 2)
    have hcB : Continuous (fun x => partialDerivScalar (fun y => u y 1) x 2 *
        partialDerivScalar (fun y => u y 2) x 1) :=
      (continuous_partialDerivScalar_of_contDiff hu1_1 2).mul
      (continuous_partialDerivScalar_of_contDiff hu1_2 1)
    rw [torusIntegral_sub hcA hcB, torusIntegral_cross_partial_comm hu1 hu2 hpu1 hpu2 1 2, sub_self]
  have hdiff20 : torusIntegral (fun x =>
      partialDerivScalar (fun y => u y 2) x 2 * partialDerivScalar (fun y => u y 0) x 0 -
      partialDerivScalar (fun y => u y 2) x 0 * partialDerivScalar (fun y => u y 0) x 2) = 0 := by
    have hcA : Continuous (fun x => partialDerivScalar (fun y => u y 2) x 2 *
        partialDerivScalar (fun y => u y 0) x 0) :=
      (continuous_partialDerivScalar_of_contDiff hu1_2 2).mul
      (continuous_partialDerivScalar_of_contDiff hu1_0 0)
    have hcB : Continuous (fun x => partialDerivScalar (fun y => u y 2) x 0 *
        partialDerivScalar (fun y => u y 0) x 2) :=
      (continuous_partialDerivScalar_of_contDiff hu1_2 0).mul
      (continuous_partialDerivScalar_of_contDiff hu1_0 2)
    rw [torusIntegral_sub hcA hcB, torusIntegral_cross_partial_comm hu2 hu0 hpu2 hpu0 2 0, sub_self]
  have hc_curl : Continuous (fun x => dot3D (curl3D u x) (curl3D u x)) := by
    have hw : Continuous (curl3D u) := by
      refine continuous_pi fun c => ?_
      match c with
      | ⟨0, _⟩ => exact (continuous_partialDerivScalar_of_contDiff hu1_2 1).sub
                        (continuous_partialDerivScalar_of_contDiff hu1_1 2)
      | ⟨1, _⟩ => exact (continuous_partialDerivScalar_of_contDiff hu1_0 2).sub
                        (continuous_partialDerivScalar_of_contDiff hu1_2 0)
      | ⟨2, _⟩ => exact (continuous_partialDerivScalar_of_contDiff hu1_1 0).sub
                        (continuous_partialDerivScalar_of_contDiff hu1_0 1)
    exact continuous_dot3D hw hw
  have hc_div : Continuous (fun x => (div3D u x) ^ 2) := by
    have hd : Continuous (div3D u) := by
      unfold div3D
      exact ((continuous_partialDerivScalar_of_contDiff hu1_0 0).add
             (continuous_partialDerivScalar_of_contDiff hu1_1 1)).add
            (continuous_partialDerivScalar_of_contDiff hu1_2 2)
    exact hd.pow 2
  have hc_grad : Continuous (gradNormSq3D u) := continuous_gradNormSq3D (contDiff_one_of_two' hu)
  have hc_d01 : Continuous (fun x =>
      partialDerivScalar (fun y => u y 0) x 0 * partialDerivScalar (fun y => u y 1) x 1 -
      partialDerivScalar (fun y => u y 0) x 1 * partialDerivScalar (fun y => u y 1) x 0) :=
    ((continuous_partialDerivScalar_of_contDiff hu1_0 0).mul
     (continuous_partialDerivScalar_of_contDiff hu1_1 1)).sub
    ((continuous_partialDerivScalar_of_contDiff hu1_0 1).mul
     (continuous_partialDerivScalar_of_contDiff hu1_1 0))
  have hc_d12 : Continuous (fun x =>
      partialDerivScalar (fun y => u y 1) x 1 * partialDerivScalar (fun y => u y 2) x 2 -
      partialDerivScalar (fun y => u y 1) x 2 * partialDerivScalar (fun y => u y 2) x 1) :=
    ((continuous_partialDerivScalar_of_contDiff hu1_1 1).mul
     (continuous_partialDerivScalar_of_contDiff hu1_2 2)).sub
    ((continuous_partialDerivScalar_of_contDiff hu1_1 2).mul
     (continuous_partialDerivScalar_of_contDiff hu1_2 1))
  have hc_d20 : Continuous (fun x =>
      partialDerivScalar (fun y => u y 2) x 2 * partialDerivScalar (fun y => u y 0) x 0 -
      partialDerivScalar (fun y => u y 2) x 0 * partialDerivScalar (fun y => u y 0) x 2) :=
    ((continuous_partialDerivScalar_of_contDiff hu1_2 2).mul
     (continuous_partialDerivScalar_of_contDiff hu1_0 0)).sub
    ((continuous_partialDerivScalar_of_contDiff hu1_2 0).mul
     (continuous_partialDerivScalar_of_contDiff hu1_0 2))
  have hc_sum3 : Continuous (fun x =>
      (partialDerivScalar (fun y => u y 0) x 0 * partialDerivScalar (fun y => u y 1) x 1 -
       partialDerivScalar (fun y => u y 0) x 1 * partialDerivScalar (fun y => u y 1) x 0) +
      (partialDerivScalar (fun y => u y 1) x 1 * partialDerivScalar (fun y => u y 2) x 2 -
       partialDerivScalar (fun y => u y 1) x 2 * partialDerivScalar (fun y => u y 2) x 1) +
      (partialDerivScalar (fun y => u y 2) x 2 * partialDerivScalar (fun y => u y 0) x 0 -
       partialDerivScalar (fun y => u y 2) x 0 * partialDerivScalar (fun y => u y 0) x 2)) :=
    (hc_d01.add hc_d12).add hc_d20
  have hc_2sum : Continuous (fun x => 2 *
      ((partialDerivScalar (fun y => u y 0) x 0 * partialDerivScalar (fun y => u y 1) x 1 -
        partialDerivScalar (fun y => u y 0) x 1 * partialDerivScalar (fun y => u y 1) x 0) +
       (partialDerivScalar (fun y => u y 1) x 1 * partialDerivScalar (fun y => u y 2) x 2 -
        partialDerivScalar (fun y => u y 1) x 2 * partialDerivScalar (fun y => u y 2) x 1) +
       (partialDerivScalar (fun y => u y 2) x 2 * partialDerivScalar (fun y => u y 0) x 0 -
        partialDerivScalar (fun y => u y 2) x 0 * partialDerivScalar (fun y => u y 0) x 2))) :=
    continuous_const.mul hc_sum3
  have heq := torusIntegral_congr (curlNormSq_add_divSq_pointwise u)
  rw [torusIntegral_add hc_curl hc_div, torusIntegral_add hc_grad hc_2sum,
      torusIntegral_const_mul 2 hc_sum3, torusIntegral_add3 hc_d01 hc_d12 hc_d20,
      hdiff01, hdiff12, hdiff20] at heq
  linarith

/-- **Bridge 1 (Solenoidal Enstrophy–Gradient Identity on `𝕋³`):**
    Whenever `div(u) = 0`, `∫_{𝕋³} |∇ × u|² dx = ∫_{𝕋³} |∇u|² dx`. -/
theorem enstrophy_eq_half_gradNormSq
    {u : R3 → R3} (hu : ContDiff ℝ 2 u) (hpu : IsPeriodic3D u)
    (hdiv : ∀ x : R3, div3D u x = 0) :
    torusIntegral (fun x => dot3D (curl3D u x) (curl3D u x)) =
      torusIntegral (gradNormSq3D u) := by
  have h := torusIntegral_curlNormSq_add_divSq hu hpu
  have hdiv_zero : torusIntegral (fun x => (div3D u x) ^ 2) = 0 := by
    have hpt : ∀ x : R3, (div3D u x) ^ 2 = 0 := fun x => by rw [hdiv x]; ring
    rw [torusIntegral_congr hpt]
    unfold torusIntegral
    simp
  linarith

/-- **Global Unconditional `L¹_t H¹_x` Enstrophy Time-Integral Bound on `𝕋³`:**
    For EVERY periodic classical 3D Navier-Stokes solution `(u, p)` and EVERY `T ≥ 0`:
      `E(T) + 2ν ∫_0^T Z(s) ds = E(0)`  and  `∫_0^T Z(s) ds ≤ E(0) / (2ν)` (`0 sorryAx`). -/
theorem global_enstrophy_time_integral_bound
    {u : ℝ → R3 → R3} {p : ℝ → R3 → ℝ} {ν : ℝ}
    (hns : IsPeriodicClassicalNS3D_C3 u p ν) {T : ℝ} (hT : 0 ≤ T) :
    kineticEnergy u T + 2 * ν * (∫ s in (0 : ℝ)..T, enstrophy u s) = kineticEnergy u 0 ∧
    (∫ s in (0 : ℝ)..T, enstrophy u s) ≤ kineticEnergy u 0 / (2 * ν) := by
  have hbal := global_leray_energy_balance_and_bound hns hT
  have h_eq_integrand : ∀ s ∈ Set.uIoc (0 : ℝ) T,
      torusIntegral (gradNormSq3D (u s)) = 2 * enstrophy u s := by
    intro s hs
    rw [Set.uIoc_of_le hT] at hs
    have hs_ge : s ≥ 0 := le_of_lt hs.1
    have hge := enstrophy_eq_half_gradNormSq
      (contDiff_two_of_three' (hns.h_u_c3_global s hs_ge))
      (hns.h_u_periodic s hs_ge)
      (hns.h_incompressible s hs_ge)
    unfold enstrophy
    linarith
  have h_int_eq : (∫ s in (0 : ℝ)..T, torusIntegral (gradNormSq3D (u s))) =
      2 * (∫ s in (0 : ℝ)..T, enstrophy u s) := by
    rw [intervalIntegral.integral_congr_ae (Eventually.of_forall h_eq_integrand),
        intervalIntegral.integral_const_mul 2 (enstrophy u)]
  have h_bal_Z : kineticEnergy u T + 2 * ν * (∫ s in (0 : ℝ)..T, enstrophy u s) =
      kineticEnergy u 0 := by
    rw [h_int_eq] at hbal
    linarith [hbal.1]
  have h2nu_pos : 0 < 2 * ν := by linarith [hns.h_nu_pos]
  have h_bound_Z : (∫ s in (0 : ℝ)..T, enstrophy u s) ≤ kineticEnergy u 0 / (2 * ν) := by
    rw [le_div_iff₀ h2nu_pos]
    linarith [h_bal_Z, hbal.2.1]
  exact ⟨h_bal_Z, h_bound_Z⟩

-- ============================================================================
-- SECTION 2: BRIDGE 2 — ZERO-MEAN VORTICITY & MOMENTUM CONSERVATION ON `𝕋³`
-- ============================================================================

/-- **Bridge 2 (Unconditional Zero Mean of Vorticity on `𝕋³`):**
    For any `C¹` periodic velocity field `u`, every component of `ω = ∇ × u` has zero
    spatial mean: `∫_{𝕋³} (∇ × u)_c dx = 0`. -/
theorem vorticity_mean_zero
    {u : R3 → R3} (hu : ContDiff ℝ 1 u) (hpu : IsPeriodic3D u) (comp : Fin 3) :
    torusIntegral (fun x => curl3D u x comp) = 0 := by
  have hu0 : ContDiff ℝ 1 (fun y => u y 0) := contDiff_pi.mp hu 0
  have hu1 : ContDiff ℝ 1 (fun y => u y 1) := contDiff_pi.mp hu 1
  have hu2 : ContDiff ℝ 1 (fun y => u y 2) := contDiff_pi.mp hu 2
  have hpu0 : IsPeriodic3D (fun y => u y 0) := fun x i => congrArg (fun v => v 0) (hpu x i)
  have hpu1 : IsPeriodic3D (fun y => u y 1) := fun x i => congrArg (fun v => v 1) (hpu x i)
  have hpu2 : IsPeriodic3D (fun y => u y 2) := fun x i => congrArg (fun v => v 2) (hpu x i)
  match comp with
  | ⟨0, _⟩ =>
    change torusIntegral (fun x => partialDerivScalar (fun y => u y 2) x 1 -
      partialDerivScalar (fun y => u y 1) x 2) = 0
    rw [torusIntegral_sub (continuous_partialDerivScalar_of_contDiff hu2 1)
          (continuous_partialDerivScalar_of_contDiff hu1 2),
        torusIntegral_partialDeriv_eq_zero hu2 hpu2 1,
        torusIntegral_partialDeriv_eq_zero hu1 hpu1 2, sub_self]
  | ⟨1, _⟩ =>
    change torusIntegral (fun x => partialDerivScalar (fun y => u y 0) x 2 -
      partialDerivScalar (fun y => u y 2) x 0) = 0
    rw [torusIntegral_sub (continuous_partialDerivScalar_of_contDiff hu0 2)
          (continuous_partialDerivScalar_of_contDiff hu2 0),
        torusIntegral_partialDeriv_eq_zero hu0 hpu0 2,
        torusIntegral_partialDeriv_eq_zero hu2 hpu2 0, sub_self]
  | ⟨2, _⟩ =>
    change torusIntegral (fun x => partialDerivScalar (fun y => u y 1) x 0 -
      partialDerivScalar (fun y => u y 0) x 1) = 0
    rw [torusIntegral_sub (continuous_partialDerivScalar_of_contDiff hu1 0)
          (continuous_partialDerivScalar_of_contDiff hu0 1),
        torusIntegral_partialDeriv_eq_zero hu1 hpu1 0,
        torusIntegral_partialDeriv_eq_zero hu0 hpu0 1, sub_self]

/-- **Total Linear Momentum Conservation on `𝕋³`:**
    For every periodic classical 3D Navier-Stokes solution `(u, p)`, the spatial mean
    `∫_{𝕋³} u(t, x)_c dx` is strictly constant in time (`M_c(T) = M_c(0)` for all `T ≥ 0`). -/
theorem momentum_conservation_torus3D
    {u : ℝ → R3 → R3} {p : ℝ → R3 → ℝ} {ν : ℝ}
    (hns : IsPeriodicClassicalNS3D_C3 u p ν) {T : ℝ} (hT : 0 ≤ T) (comp : Fin 3) :
    torusIntegral (fun x => u T x comp) = torusIntegral (fun x => u 0 x comp) := by
  have hu_cont : Continuous (fun q : ℝ × R3 => u q.1 q.2) :=
    (contDiff_iff_contDiffAt.mpr hns.h_u_c2_spacetime).continuous
  have hF_cont : Continuous (fun q : ℝ × R3 => u q.1 q.2 comp) :=
    (continuous_apply comp).comp hu_cont
  have hF'_cont : Continuous (fun q : ℝ × R3 => deriv (fun s => u s q.2 comp) q.1) := by
    have hFc : ∀ q : ℝ × R3, ContDiffAt ℝ 2 (fun r : ℝ × R3 => u r.1 r.2 comp) q :=
      fun q => contDiffAt_pi.mp (hns.h_u_c2_spacetime q) comp
    have hfun : (fun q : ℝ × R3 => deriv (fun s => u s q.2 comp) q.1) =
        (fun q : ℝ × R3 => fderiv ℝ (fun r : ℝ × R3 => u r.1 r.2 comp) q ((1 : ℝ), (0 : R3))) := by
      funext q
      exact timeDeriv_eq_fderiv_prod (fun r => u r.1 r.2 comp) hFc q.1 q.2
    rw [hfun]
    have hcd : ContDiff ℝ 2 (fun r : ℝ × R3 => u r.1 r.2 comp) :=
      contDiff_iff_contDiffAt.mpr hFc
    have hcd1 : ContDiff ℝ 1 (fderiv ℝ (fun r : ℝ × R3 => u r.1 r.2 comp)) :=
      hcd.fderiv_right (by simp [one_add_one_eq_two])
    exact (ContinuousLinearMap.apply ℝ ℝ ((1 : ℝ), (0 : R3))).continuous.comp hcd1.continuous
  have h_deriv_zero : ∀ t : ℝ, 0 ≤ t →
      HasDerivAt (fun s => torusIntegral (fun x => u s x comp)) 0 t := by
    intro t ht
    have h_diff_pt : ∀ (s : ℝ) (x : R3),
        HasDerivAt (fun r => u r x comp) (deriv (fun r => u r x comp) s) s := by
      intro s x
      have hFc : ∀ q : ℝ × R3, ContDiffAt ℝ 2 (fun r : ℝ × R3 => u r.1 r.2 comp) q :=
        fun q => contDiffAt_pi.mp (hns.h_u_c2_spacetime q) comp
      have h1 : ContDiffAt ℝ 1 (fun r : ℝ × R3 => u r.1 r.2 comp) (s, x) :=
        (hFc (s, x)).of_le (by rw [← one_add_one_eq_two]; exact le_self_add)
      have hdiff : DifferentiableAt ℝ (fun r : ℝ × R3 => u r.1 r.2 comp) (s, x) :=
        h1.differentiableAt (by simp)
      have hembed : HasDerivAt (fun r : ℝ => (r, x)) ((1 : ℝ), (0 : R3)) s :=
        (hasDerivAt_id s).prodMk (hasDerivAt_const s x)
      have hd := hdiff.hasFDerivAt.comp_hasDerivAt s hembed
      rw [← timeDeriv_eq_fderiv_prod (fun r => u r.1 r.2 comp) hFc s x] at hd
      exact hd
    have h_leib := hasDerivAt_torusIntegral_of_continuous
      (F := fun s x => u s x comp)
      (F' := fun s x => deriv (fun r => u r x comp) s)
      hF_cont hF'_cont h_diff_pt t
    have hu2 : ContDiff ℝ 2 (u t) := contDiff_two_of_three' (hns.h_u_c3_global t ht)
    have hu1 : ContDiff ℝ 1 (u t) := contDiff_one_of_two' hu2
    have hp1 : ContDiff ℝ 1 (p t) := contDiff_one_of_two' (hns.h_p_c2_global t ht)
    have hpu : IsPeriodic3D (u t) := hns.h_u_periodic t ht
    have hpp : IsPeriodic3D (p t) := hns.h_p_periodic t ht
    have huc2 : ContDiff ℝ 2 (fun y => u t y comp) := contDiff_pi.mp hu2 comp
    have huc1 : ContDiff ℝ 1 (fun y => u t y comp) := contDiff_one_of_two' huc2
    have hpuc : IsPeriodic3D (fun y => u t y comp) := fun x i => congrArg (fun v => v comp) (hpu x i)
    -- 1. ∫ Δu_comp = 0
    have h_lap_zero : torusIntegral (fun x => laplacian3D (u t) x comp) = 0 := by
      have haxis : ∀ i : Fin 3, torusIntegral (fun x => sndPartial (fun y => u t y comp) x i i) = 0 := by
        intro i
        have hgi : ContDiff ℝ 1 (fun y => partialDerivScalar (fun z => u t z comp) y i) :=
          contDiff_one_partialDerivScalar huc2 i
        have hpgi : IsPeriodic3D (fun y => partialDerivScalar (fun z => u t z comp) y i) :=
          IsPeriodic3D.partialDeriv hpuc (huc1.differentiable (by simp)) i
        have hpt : ∀ x : R3, sndPartial (fun y => u t y comp) x i i =
            partialDerivScalar (fun y => partialDerivScalar (fun z => u t z comp) y i) x i :=
          fun x => (partial_partial_eq_sndPartial (fun y => u t y comp) x huc2.contDiffAt i i).symm
        rw [torusIntegral_congr hpt]
        exact torusIntegral_partialDeriv_eq_zero hgi hpgi i
      have hc0 := continuous_sndPartial_of_contDiff huc2 0 0
      have hc1 := continuous_sndPartial_of_contDiff huc2 1 1
      have hc2 := continuous_sndPartial_of_contDiff huc2 2 2
      unfold laplacian3D laplacianScalar
      rw [torusIntegral_add3 hc0 hc1 hc2, haxis 0, haxis 1, haxis 2]
      ring
    -- 2. ∫ ∂_comp p = 0
    have h_gp_zero : torusIntegral (fun x => grad3D (p t) x comp) = 0 :=
      torusIntegral_partialDeriv_eq_zero hp1 hpp comp
    -- 3. ∫ (u·∇)u_comp = ∫ div(u_comp * u) = 0
    have h_adv_zero : torusIntegral (fun x => advection3D (u t) x comp) = 0 := by
      let F : R3 → R3 := fun y i => u t y i * u t y comp
      have hF_c1 : ContDiff ℝ 1 F := contDiff_pi.mpr fun i => (contDiff_pi.mp hu1 i).mul huc1
      have hF_per : IsPeriodic3D F := by
        intro x i; funext j
        change u t (x + basisVec i) j * u t (x + basisVec i) comp = u t x j * u t x comp
        rw [hpu x i]
      have hpt : ∀ x : R3, advection3D (u t) x comp = div3D F x := by
        intro x
        have hdu : ∀ i : Fin 3, DifferentiableAt ℝ (fun y => u t y i) x :=
          fun i => (contDiff_pi.mp hu1 i).differentiable (by simp) x
        have hduc : DifferentiableAt ℝ (fun y => u t y comp) x := huc1.differentiable (by simp) x
        have hdiv_eq : div3D F x = advection3D (u t) x comp + div3D (u t) x * u t x comp := by
          unfold div3D advection3D
          change partialDerivScalar (fun y => u t y 0 * u t y comp) x 0 +
                 partialDerivScalar (fun y => u t y 1 * u t y comp) x 1 +
                 partialDerivScalar (fun y => u t y 2 * u t y comp) x 2 = _
          rw [partialDerivScalar_mul (hdu 0) hduc 0,
              partialDerivScalar_mul (hdu 1) hduc 1,
              partialDerivScalar_mul (hdu 2) hduc 2]
          ring
        rw [hdiv_eq, hns.h_incompressible t ht x, zero_mul, add_zero]
      rw [torusIntegral_congr hpt]
      exact torusIntegral_div3D_eq_zero hF_c1 hF_per
    -- Combine via momentum PDE
    have hpt_mom : ∀ x : R3, deriv (fun r => u r x comp) t =
        ν * laplacian3D (u t) x comp - advection3D (u t) x comp - grad3D (p t) x comp := by
      intro x
      linarith [hns.h_momentum t ht x comp]
    have hc_lap : Continuous (fun x => laplacian3D (u t) x comp) :=
      (continuous_apply comp).comp (continuous_laplacian3D hu2)
    have hc_nu_lap : Continuous (fun x => ν * laplacian3D (u t) x comp) := continuous_const.mul hc_lap
    have hc_adv : Continuous (fun x => advection3D (u t) x comp) :=
      (continuous_apply comp).comp (continuous_advection3D hu1)
    have hc_sub1 : Continuous (fun x => ν * laplacian3D (u t) x comp - advection3D (u t) x comp) :=
      hc_nu_lap.sub hc_adv
    have hc_gp : Continuous (fun x => grad3D (p t) x comp) :=
      (continuous_apply comp).comp (continuous_grad3D hp1)
    have h_int_zero : torusIntegral (fun x => deriv (fun r => u r x comp) t) = 0 := by
      rw [torusIntegral_congr hpt_mom,
          torusIntegral_sub hc_sub1 hc_gp,
          torusIntegral_sub hc_nu_lap hc_adv,
          torusIntegral_const_mul ν hc_lap,
          h_lap_zero, h_adv_zero, h_gp_zero]
      ring
    rw [h_int_zero] at h_leib
    exact h_leib
  have h_ftc := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (a := (0 : ℝ)) (b := T)
    (f := fun s => torusIntegral (fun x => u s x comp))
    (f' := fun _ => (0 : ℝ))
    (fun s hs => by
      rw [Set.uIcc_of_le hT] at hs
      exact h_deriv_zero s hs.1)
    (continuous_const.intervalIntegrable 0 T)
  simp only [intervalIntegral.integral_zero] at h_ftc
  linarith

-- ============================================================================
-- SECTION 3: 1D PERIODIC POINCARÉ INEQUALITY (`8 ∫₀¹ g² ≤ ∫₀¹ (g')²`)
-- ============================================================================

/-- Elementary Cauchy–Schwarz inequality on `[a, b]`: `(∫_a^b f)² ≤ (b - a) ∫_a^b f²`. -/
theorem intervalIntegral_sq_le_mul_integral_sq
    {f : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b) (hf : Continuous f) :
    (∫ t in a..b, f t) ^ 2 ≤ (b - a) * (∫ t in a..b, (f t) ^ 2) := by
  rcases eq_or_lt_of_le hab with rfl | hlt
  · simp
  · let A : ℝ := ∫ t in a..b, f t
    let B : ℝ := ∫ t in a..b, (f t) ^ 2
    let L : ℝ := b - a
    have hL : 0 < L := by dsimp only [L]; linarith
    let r : ℝ := A / L
    have h_nn : 0 ≤ ∫ t in a..b, (r - f t) ^ 2 :=
      intervalIntegral.integral_nonneg hab fun t _ => sq_nonneg _
    have h_exp : ∀ t : ℝ, (r - f t) ^ 2 = (r ^ 2 - 2 * r * f t) + (f t) ^ 2 := fun t => by ring
    have hc1 : Continuous (fun _ : ℝ => r ^ 2) := continuous_const
    have hc2 : Continuous (fun t : ℝ => 2 * r * f t) := continuous_const.mul hf
    have hc3 : Continuous (fun t : ℝ => (f t) ^ 2) := hf.pow 2
    have hc12 : Continuous (fun t : ℝ => r ^ 2 - 2 * r * f t) := hc1.sub hc2
    have h_calc : (∫ t in a..b, (r - f t) ^ 2) = r ^ 2 * L - 2 * r * A + B := by
      have hcongr : (∫ t in a..b, (r - f t) ^ 2) =
          ∫ t in a..b, ((r ^ 2 - 2 * r * f t) + (f t) ^ 2) := by
        congr 1; funext t; exact h_exp t
      rw [hcongr,
          intervalIntegral.integral_add (hc12.intervalIntegrable a b) (hc3.intervalIntegrable a b),
          intervalIntegral.integral_sub (hc1.intervalIntegrable a b) (hc2.intervalIntegrable a b),
          intervalIntegral.integral_const,
          intervalIntegral.integral_const_mul (2 * r) f]
      simp only [smul_eq_mul]
      dsimp only [A, B, L]
      ring
    have hrL : r * L = A := div_mul_cancel₀ A (ne_of_gt hL)
    have h_quad : 0 ≤ r ^ 2 * L - 2 * r * A + B := by linarith
    have h_mul : 0 ≤ (r ^ 2 * L - 2 * r * A + B) * L := mul_nonneg h_quad (le_of_lt hL)
    have h_alg : (r ^ 2 * L - 2 * r * A + B) * L = L * B - A ^ 2 := by
      calc (r ^ 2 * L - 2 * r * A + B) * L
          = (r * L) ^ 2 - 2 * (r * L) * A + L * B := by ring
        _ = A ^ 2 - 2 * A * A + L * B := by rw [hrL]
        _ = L * B - A ^ 2 := by ring
    dsimp only [A, B, L] at h_mul h_alg
    linarith

/-- Translation invariance of unit-interval integrals of 1-periodic continuous functions. -/
theorem periodic_shift_integral
    {φ : ℝ → ℝ} (hφ : Continuous φ) (hper : ∀ s : ℝ, φ (s + 1) = φ s) (x₀ : ℝ) :
    (∫ t in (0 : ℝ)..1, φ (x₀ + t)) = ∫ t in (0 : ℝ)..1, φ t := by
  have hcomm : (∫ t in (0 : ℝ)..1, φ (x₀ + t)) = ∫ t in (0 : ℝ)..1, φ (t + x₀) := by
    congr 1; funext t; rw [add_comm]
  rw [hcomm, intervalIntegral.integral_comp_add_right φ x₀, zero_add]
  have hsplit : (∫ t in x₀..1, φ t) + (∫ t in (1 : ℝ)..(1 + x₀), φ t) =
      ∫ t in x₀..(1 + x₀), φ t :=
    intervalIntegral.integral_add_adjacent_intervals
      (hφ.intervalIntegrable _ _) (hφ.intervalIntegrable _ _)
  have hshift : (∫ t in (1 : ℝ)..(1 + x₀), φ t) = ∫ t in (0 : ℝ)..x₀, φ t := by
    have hcomp := intervalIntegral.integral_comp_add_right (a := (0 : ℝ)) (b := x₀) φ (1 : ℝ)
    have hper_eq : (fun t => φ (t + 1)) = φ := funext hper
    rw [hper_eq, zero_add, add_comm x₀ 1] at hcomp
    exact hcomp.symm
  have hjoin : (∫ t in (0 : ℝ)..x₀, φ t) + (∫ t in x₀..1, φ t) = ∫ t in (0 : ℝ)..1, φ t :=
    intervalIntegral.integral_add_adjacent_intervals
      (hφ.intervalIntegrable _ _) (hφ.intervalIntegrable _ _)
  linarith

private theorem integral_id_zero_half : ∫ t in (0 : ℝ)..(1 / 2 : ℝ), t = 1 / 8 := by
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (a := (0 : ℝ)) (b := (1 / 2 : ℝ))
    (f := fun t : ℝ => t ^ 2 / 2) (f' := fun t : ℝ => t)
    (fun s _ => by
      have hd := (hasDerivAt_pow 2 s).div_const 2
      convert hd using 1; ring)
    (continuous_id.intervalIntegrable 0 (1 / 2))
  norm_num at h
  exact h

private theorem integral_one_sub_half_one : ∫ t in (1 / 2 : ℝ)..(1 : ℝ), (1 - t) = 1 / 8 := by
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (a := (1 / 2 : ℝ)) (b := (1 : ℝ))
    (f := fun t : ℝ => t - t ^ 2 / 2) (f' := fun t : ℝ => 1 - t)
    (fun s _ => by
      have hid : HasDerivAt (fun t : ℝ => t) 1 s := hasDerivAt_id s
      have hsq : HasDerivAt (fun t : ℝ => t ^ 2 / 2) (↑2 * s ^ (2 - 1) / 2) s :=
        (hasDerivAt_pow 2 s).div_const 2
      have hsub : HasDerivAt (fun t : ℝ => t - t ^ 2 / 2) (1 - ↑2 * s ^ (2 - 1) / 2) s :=
        hid.sub hsq
      have heq : (1 : ℝ) - ↑2 * s ^ (2 - 1) / 2 = 1 - s := by norm_num
      rwa [heq] at hsub)
    ((continuous_const.sub continuous_id).intervalIntegrable (1 / 2) 1)
  norm_num at h
  exact h

/-- **1D Periodic Poincaré Inequality:** For any `C¹` 1-periodic mean-zero function `g : ℝ → ℝ`,
    `8 ∫₀¹ g(s)² ds ≤ ∫₀¹ g'(s)² ds` (`0 sorryAx`). -/
theorem poincare_1d_periodic
    {g g' : ℝ → ℝ}
    (hg_cont : Continuous g) (hg'_cont : Continuous g')
    (hg_deriv : ∀ s : ℝ, HasDerivAt g (g' s) s)
    (hg_per : ∀ s : ℝ, g (s + 1) = g s)
    (hg'_per : ∀ s : ℝ, g' (s + 1) = g' s)
    (hg_mean : ∫ s in (0 : ℝ)..1, g s = 0) :
    8 * (∫ s in (0 : ℝ)..1, (g s) ^ 2) ≤ ∫ s in (0 : ℝ)..1, (g' s) ^ 2 := by
  -- Step 1: Mean zero + continuity implies existence of a root `x₀` with `g x₀ = 0`.
  obtain ⟨a, _, ha_min⟩ :=
    (isCompact_Icc (a := (0 : ℝ)) (b := 1)).exists_isMinOn ⟨(0 : ℝ), ⟨le_rfl, by norm_num⟩⟩ hg_cont.continuousOn
  have hga_le : g a ≤ 0 := by
    have hca : Continuous (fun _ : ℝ => g a) := continuous_const
    have hle := intervalIntegral.integral_mono_on (μ := volume) (by norm_num : (0 : ℝ) ≤ 1)
      (hca.intervalIntegrable (μ := volume) 0 1) (hg_cont.intervalIntegrable (μ := volume) 0 1)
      (fun s hs => ha_min hs)
    simp [hg_mean] at hle
    exact hle
  obtain ⟨b, _, hb_max⟩ :=
    (isCompact_Icc (a := (0 : ℝ)) (b := 1)).exists_isMaxOn ⟨(0 : ℝ), ⟨le_rfl, by norm_num⟩⟩ hg_cont.continuousOn
  have hgb_ge : 0 ≤ g b := by
    have hcb : Continuous (fun _ : ℝ => g b) := continuous_const
    have hle := intervalIntegral.integral_mono_on (μ := volume) (by norm_num : (0 : ℝ) ≤ 1)
      (hg_cont.intervalIntegrable (μ := volume) 0 1) (hcb.intervalIntegrable (μ := volume) 0 1)
      (fun s hs => hb_max hs)
    simp [hg_mean] at hle
    exact hle
  have hx0_exists : ∃ x₀ : ℝ, g x₀ = 0 := by
    rcases le_total a b with hab | hba
    · obtain ⟨x₀, _, hx₀⟩ :=
        intermediate_value_Icc hab hg_cont.continuousOn (show (0 : ℝ) ∈ Set.Icc (g a) (g b) from ⟨hga_le, hgb_ge⟩)
      exact ⟨x₀, hx₀⟩
    · obtain ⟨x₀, _, hx₀⟩ :=
        intermediate_value_Icc' hba hg_cont.continuousOn (show (0 : ℝ) ∈ Set.Icc (g a) (g b) from ⟨hga_le, hgb_ge⟩)
      exact ⟨x₀, hx₀⟩
  obtain ⟨x₀, hx0_eq⟩ := hx0_exists
  -- Step 2: Shift to `h(t) = g(x₀ + t)` satisfying `h(0) = h(1) = 0`.
  let h : ℝ → ℝ := fun t => g (x₀ + t)
  let h' : ℝ → ℝ := fun t => g' (x₀ + t)
  have hh_cont : Continuous h := hg_cont.comp (continuous_const.add continuous_id)
  have hh'_cont : Continuous h' := hg'_cont.comp (continuous_const.add continuous_id)
  have hh0 : h 0 = 0 := by dsimp only [h]; rw [add_zero]; exact hx0_eq
  have hh1 : h 1 = 0 := by dsimp only [h]; rw [hg_per x₀]; exact hx0_eq
  have hh_deriv : ∀ t : ℝ, HasDerivAt h (h' t) t := fun t => by
    have htr : HasDerivAt (fun s : ℝ => x₀ + s) 1 t := by
      have h1 : HasDerivAt (fun s : ℝ => x₀ + s) (0 + 1) t :=
        (hasDerivAt_const t x₀).add (hasDerivAt_id t)
      rwa [zero_add] at h1
    have hc : HasDerivAt (fun s : ℝ => g (x₀ + s)) (g' (x₀ + t) * 1) t :=
      (hg_deriv (x₀ + t)).comp t htr
    rwa [mul_one] at hc
  -- Step 3: Left half `[0, 1/2]`
  have h_left_pt : ∀ t ∈ Set.Icc (0 : ℝ) (1 / 2 : ℝ),
      (h t) ^ 2 ≤ t * (∫ u in (0 : ℝ)..(1 / 2 : ℝ), (h' u) ^ 2) := by
    intro t ht
    have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt
      (a := (0 : ℝ)) (b := t) (f := h) (f' := h')
      (fun s _ => hh_deriv s) (hh'_cont.intervalIntegrable 0 t)
    rw [hh0, sub_zero] at hftc
    have hcs := intervalIntegral_sq_le_mul_integral_sq ht.1 hh'_cont
    rw [hftc, sub_zero] at hcs
    have hsplit : (∫ u in (0 : ℝ)..t, (h' u) ^ 2) + (∫ u in t..(1 / 2 : ℝ), (h' u) ^ 2) =
        ∫ u in (0 : ℝ)..(1 / 2 : ℝ), (h' u) ^ 2 :=
      intervalIntegral.integral_add_adjacent_intervals
        ((hh'_cont.pow 2).intervalIntegrable _ _) ((hh'_cont.pow 2).intervalIntegrable _ _)
    have hrem : 0 ≤ ∫ u in t..(1 / 2 : ℝ), (h' u) ^ 2 :=
      intervalIntegral.integral_nonneg ht.2 fun _ _ => sq_nonneg _
    have hmono : (∫ u in (0 : ℝ)..t, (h' u) ^ 2) ≤ ∫ u in (0 : ℝ)..(1 / 2 : ℝ), (h' u) ^ 2 := by
      linarith
    have hmul := mul_le_mul_of_nonneg_left hmono ht.1
    linarith
  have h_left : 8 * (∫ t in (0 : ℝ)..(1 / 2 : ℝ), (h t) ^ 2) ≤
      ∫ u in (0 : ℝ)..(1 / 2 : ℝ), (h' u) ^ 2 := by
    have hcl : Continuous (fun t => (h t) ^ 2) := hh_cont.pow 2
    have hcr : Continuous (fun t => t * (∫ u in (0 : ℝ)..(1 / 2 : ℝ), (h' u) ^ 2)) :=
      continuous_id.mul continuous_const
    have hmono := intervalIntegral.integral_mono_on (μ := volume) (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (hcl.intervalIntegrable (μ := volume) 0 (1 / 2))
      (hcr.intervalIntegrable (μ := volume) 0 (1 / 2))
      h_left_pt
    rw [intervalIntegral.integral_mul_const, integral_id_zero_half] at hmono
    linarith
  -- Step 4: Right half `[1/2, 1]`
  have h_right_pt : ∀ t ∈ Set.Icc (1 / 2 : ℝ) (1 : ℝ),
      (h t) ^ 2 ≤ (1 - t) * (∫ u in (1 / 2 : ℝ)..(1 : ℝ), (h' u) ^ 2) := by
    intro t ht
    have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt
      (a := t) (b := (1 : ℝ)) (f := h) (f' := h')
      (fun s _ => hh_deriv s) (hh'_cont.intervalIntegrable t 1)
    rw [hh1, zero_sub] at hftc
    have hcs := intervalIntegral_sq_le_mul_integral_sq ht.2 hh'_cont
    rw [hftc, neg_sq] at hcs
    have hsplit : (∫ u in (1 / 2 : ℝ)..t, (h' u) ^ 2) + (∫ u in t..(1 : ℝ), (h' u) ^ 2) =
        ∫ u in (1 / 2 : ℝ)..(1 : ℝ), (h' u) ^ 2 :=
      intervalIntegral.integral_add_adjacent_intervals
        ((hh'_cont.pow 2).intervalIntegrable _ _) ((hh'_cont.pow 2).intervalIntegrable _ _)
    have hrem : 0 ≤ ∫ u in (1 / 2 : ℝ)..t, (h' u) ^ 2 :=
      intervalIntegral.integral_nonneg ht.1 fun _ _ => sq_nonneg _
    have hmono : (∫ u in t..(1 : ℝ), (h' u) ^ 2) ≤ ∫ u in (1 / 2 : ℝ)..(1 : ℝ), (h' u) ^ 2 := by
      linarith
    have hmul := mul_le_mul_of_nonneg_left hmono (by linarith [ht.2] : 0 ≤ 1 - t)
    linarith
  have h_right : 8 * (∫ t in (1 / 2 : ℝ)..(1 : ℝ), (h t) ^ 2) ≤
      ∫ u in (1 / 2 : ℝ)..(1 : ℝ), (h' u) ^ 2 := by
    have hcl : Continuous (fun t => (h t) ^ 2) := hh_cont.pow 2
    have hcr : Continuous (fun t => (1 - t) * (∫ u in (1 / 2 : ℝ)..(1 : ℝ), (h' u) ^ 2)) :=
      (continuous_const.sub continuous_id).mul continuous_const
    have hmono := intervalIntegral.integral_mono_on (μ := volume) (by norm_num : (1 / 2 : ℝ) ≤ 1)
      (hcl.intervalIntegrable (μ := volume) (1 / 2) 1)
      (hcr.intervalIntegrable (μ := volume) (1 / 2) 1)
      h_right_pt
    rw [intervalIntegral.integral_mul_const, integral_one_sub_half_one] at hmono
    linarith
  -- Step 5: Combine both halves and shift back via periodicity
  have h_sum_h : (∫ t in (0 : ℝ)..(1 / 2 : ℝ), (h t) ^ 2) +
      (∫ t in (1 / 2 : ℝ)..(1 : ℝ), (h t) ^ 2) = ∫ t in (0 : ℝ)..1, (h t) ^ 2 :=
    intervalIntegral.integral_add_adjacent_intervals
      ((hh_cont.pow 2).intervalIntegrable _ _) ((hh_cont.pow 2).intervalIntegrable _ _)
  have h_sum_h' : (∫ u in (0 : ℝ)..(1 / 2 : ℝ), (h' u) ^ 2) +
      (∫ u in (1 / 2 : ℝ)..(1 : ℝ), (h' u) ^ 2) = ∫ u in (0 : ℝ)..1, (h' u) ^ 2 :=
    intervalIntegral.integral_add_adjacent_intervals
      ((hh'_cont.pow 2).intervalIntegrable _ _) ((hh'_cont.pow 2).intervalIntegrable _ _)
  have hg_sq_cont : Continuous (fun s => (g s) ^ 2) := hg_cont.pow 2
  have hg'_sq_cont : Continuous (fun s => (g' s) ^ 2) := hg'_cont.pow 2
  have h_shift_g : (∫ t in (0 : ℝ)..1, (h t) ^ 2) = ∫ s in (0 : ℝ)..1, (g s) ^ 2 :=
    periodic_shift_integral hg_sq_cont (fun s => by rw [hg_per s]) x₀
  have h_shift_g' : (∫ u in (0 : ℝ)..1, (h' u) ^ 2) = ∫ s in (0 : ℝ)..1, (g' s) ^ 2 :=
    periodic_shift_integral hg'_sq_cont (fun s => by rw [hg'_per s]) x₀
  linarith

-- ============================================================================
-- SECTION 4: 1D/2D LEIBNIZ HELPERS & 3D TORUS POINCARÉ INEQUALITY
-- ============================================================================

private noncomputable abbrev uMeas1 : Measure ℝ := volume.restrict (Set.Icc (0 : ℝ) 1)
private noncomputable abbrev uMeas2 : Measure (ℝ × ℝ) := uMeas1.prod uMeas1
private noncomputable abbrev uSquare : Set (ℝ × ℝ) := Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1

private theorem isFiniteMeasure_uMeas1 : IsFiniteMeasure uMeas1 :=
  ⟨by rw [Measure.restrict_apply_univ]; exact isCompact_Icc.measure_lt_top⟩

private theorem uMeas2_eq_restrict : uMeas2 = (volume : Measure (ℝ × ℝ)).restrict uSquare := by
  unfold uMeas2 uMeas1 uSquare
  rw [Measure.prod_restrict]
  rfl

private theorem isFiniteMeasure_uMeas2 : IsFiniteMeasure uMeas2 :=
  ⟨by rw [uMeas2_eq_restrict, Measure.restrict_apply_univ]; exact (isCompact_Icc.prod isCompact_Icc).measure_lt_top⟩

private theorem int1_eq_uMeas1 (h : ℝ → ℝ) : ∫ t in (0 : ℝ)..1, h t = ∫ t, h t ∂uMeas1 := by
  rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1),
      ← MeasureTheory.integral_Icc_eq_integral_Ioc]

private theorem int2_eq_uMeas2 {g : ℝ → ℝ → ℝ} (hg : Continuous (fun p : ℝ × ℝ => g p.1 p.2)) :
    (∫ y in (0 : ℝ)..1, ∫ z in (0 : ℝ)..1, g y z) = ∫ p : ℝ × ℝ, g p.1 p.2 ∂uMeas2 := by
  simp_rw [int1_eq_uMeas1]
  have hint : Integrable (fun p : ℝ × ℝ => g p.1 p.2) uMeas2 := by
    rw [uMeas2_eq_restrict]
    exact hg.continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)
  exact (MeasureTheory.integral_prod (fun p : ℝ × ℝ => g p.1 p.2) hint).symm

private theorem continuous_int1_of_joint {G : ℝ → ℝ → ℝ}
    (hG : Continuous (fun p : ℝ × ℝ => G p.1 p.2)) :
    Continuous (fun t => ∫ z in (0 : ℝ)..1, G t z) := by
  have : IsFiniteMeasure uMeas1 := isFiniteMeasure_uMeas1
  have h_eq : (fun t => ∫ z in (0 : ℝ)..1, G t z) = (fun t => ∫ z, G t z ∂uMeas1) := by
    funext t; exact int1_eq_uMeas1 (G t)
  rw [h_eq]
  refine continuous_iff_continuousAt.mpr fun t₀ => ?_
  let s : Set ℝ := Set.Icc (t₀ - 1) (t₀ + 1)
  have hs : s ∈ 𝓝 t₀ := Icc_mem_nhds (by linarith) (by linarith)
  obtain ⟨C, hC⟩ := (isCompact_Icc.prod isCompact_Icc).exists_bound_of_continuousOn hG.continuousOn
    (s := s ×ˢ Set.Icc (0 : ℝ) 1)
  have h_meas : ∀ᶠ t in 𝓝 t₀, AEStronglyMeasurable (fun z => G t z) uMeas1 :=
    Eventually.of_forall fun t => (hG.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
  have h_bound : ∀ᶠ t in 𝓝 t₀, ∀ᵐ z ∂uMeas1, ‖G t z‖ ≤ C := by
    filter_upwards [hs] with t ht
    filter_upwards [ae_restrict_mem measurableSet_Icc] with z hz
    exact hC (t, z) ⟨ht, hz⟩
  have h_cont : ∀ᵐ z ∂uMeas1, ContinuousAt (fun t => G t z) t₀ :=
    Eventually.of_forall fun z => (hG.comp (continuous_id.prodMk continuous_const)).continuousAt
  exact continuousAt_of_dominated h_meas h_bound (integrable_const C) h_cont

private theorem continuous_int2_of_joint {G : ℝ → ℝ → ℝ → ℝ}
    (hG : Continuous (fun q : ℝ × (ℝ × ℝ) => G q.1 q.2.1 q.2.2)) :
    Continuous (fun x => ∫ y in (0 : ℝ)..1, ∫ z in (0 : ℝ)..1, G x y z) := by
  have h1 : Continuous (fun p : ℝ × ℝ => ∫ z in (0 : ℝ)..1, G p.1 p.2 z) := by
    have : IsFiniteMeasure uMeas1 := isFiniteMeasure_uMeas1
    have h_eq : (fun p : ℝ × ℝ => ∫ z in (0 : ℝ)..1, G p.1 p.2 z) =
        (fun p : ℝ × ℝ => ∫ z, G p.1 p.2 z ∂uMeas1) := by
      funext p; exact int1_eq_uMeas1 (G p.1 p.2)
    rw [h_eq]
    refine continuous_iff_continuousAt.mpr fun p₀ => ?_
    let s : Set (ℝ × ℝ) := Set.Icc (p₀.1 - 1) (p₀.1 + 1) ×ˢ Set.Icc (p₀.2 - 1) (p₀.2 + 1)
    have hs : s ∈ 𝓝 p₀ := prod_mem_nhds (Icc_mem_nhds (by linarith) (by linarith))
      (Icc_mem_nhds (by linarith) (by linarith))
    have hG' : Continuous (fun r : (ℝ × ℝ) × ℝ => G r.1.1 r.1.2 r.2) :=
      hG.comp ((continuous_fst.comp continuous_fst).prodMk
        ((continuous_snd.comp continuous_fst).prodMk continuous_snd))
    obtain ⟨C, hC⟩ := ((isCompact_Icc.prod isCompact_Icc).prod isCompact_Icc).exists_bound_of_continuousOn
      hG'.continuousOn (s := s ×ˢ Set.Icc (0 : ℝ) 1)
    have h_meas : ∀ᶠ p in 𝓝 p₀, AEStronglyMeasurable (fun z => G p.1 p.2 z) uMeas1 :=
      Eventually.of_forall fun p =>
        (hG'.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
    have h_bound : ∀ᶠ p in 𝓝 p₀, ∀ᵐ z ∂uMeas1, ‖G p.1 p.2 z‖ ≤ C := by
      filter_upwards [hs] with p hp
      filter_upwards [ae_restrict_mem measurableSet_Icc] with z hz
      exact hC (p, z) ⟨hp, hz⟩
    have h_cont : ∀ᵐ z ∂uMeas1, ContinuousAt (fun p : ℝ × ℝ => G p.1 p.2 z) p₀ :=
      Eventually.of_forall fun z => (hG'.comp (continuous_id.prodMk continuous_const)).continuousAt
    exact continuousAt_of_dominated h_meas h_bound (integrable_const C) h_cont
  exact continuous_int1_of_joint h1

private theorem hasDerivAt_int1_unit {F F' : ℝ → ℝ → ℝ}
    (hF : Continuous (fun p : ℝ × ℝ => F p.1 p.2))
    (hF' : Continuous (fun p : ℝ × ℝ => F' p.1 p.2))
    (hdiff : ∀ t z : ℝ, HasDerivAt (fun s => F s z) (F' t z) t) (t₀ : ℝ) :
    HasDerivAt (fun t => ∫ z in (0 : ℝ)..1, F t z) (∫ z in (0 : ℝ)..1, F' t₀ z) t₀ := by
  have : IsFiniteMeasure uMeas1 := isFiniteMeasure_uMeas1
  have h_eq : (fun t => ∫ z in (0 : ℝ)..1, F t z) = (fun t => ∫ z, F t z ∂uMeas1) := by
    funext t; exact int1_eq_uMeas1 (F t)
  rw [h_eq, int1_eq_uMeas1 (F' t₀)]
  let s : Set ℝ := Set.Icc (t₀ - 1) (t₀ + 1)
  have hs : s ∈ 𝓝 t₀ := Icc_mem_nhds (by linarith) (by linarith)
  obtain ⟨C, hC⟩ := (isCompact_Icc.prod isCompact_Icc).exists_bound_of_continuousOn hF'.continuousOn
    (s := s ×ˢ Set.Icc (0 : ℝ) 1)
  have h_meas : ∀ᶠ t in 𝓝 t₀, AEStronglyMeasurable (fun z => F t z) uMeas1 :=
    Eventually.of_forall fun t => (hF.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
  have h_int : Integrable (fun z => F t₀ z) uMeas1 :=
    (hF.comp (continuous_const.prodMk continuous_id)).continuousOn.integrableOn_compact isCompact_Icc
  have h_meas' : AEStronglyMeasurable (fun z => F' t₀ z) uMeas1 :=
    (hF'.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
  have h_bound : ∀ᵐ z ∂uMeas1, ∀ t ∈ s, ‖F' t z‖ ≤ C := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with z hz t ht
    exact hC (t, z) ⟨ht, hz⟩
  have h_diff_ae : ∀ᵐ z ∂uMeas1, ∀ t ∈ s, HasDerivAt (fun r => F r z) (F' t z) t :=
    Eventually.of_forall fun z t _ => hdiff t z
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le hs h_meas h_int h_meas'
    h_bound (integrable_const C) h_diff_ae).2

private theorem hasDerivAt_int2_unit {F F' : ℝ → ℝ → ℝ → ℝ}
    (hF : Continuous (fun q : ℝ × (ℝ × ℝ) => F q.1 q.2.1 q.2.2))
    (hF' : Continuous (fun q : ℝ × (ℝ × ℝ) => F' q.1 q.2.1 q.2.2))
    (hdiff : ∀ x y z : ℝ, HasDerivAt (fun s => F s y z) (F' x y z) x) (x₀ : ℝ) :
    HasDerivAt (fun x => ∫ y in (0 : ℝ)..1, ∫ z in (0 : ℝ)..1, F x y z)
      (∫ y in (0 : ℝ)..1, ∫ z in (0 : ℝ)..1, F' x₀ y z) x₀ := by
  have : IsFiniteMeasure uMeas2 := isFiniteMeasure_uMeas2
  have hF_slice : ∀ x : ℝ, Continuous (fun p : ℝ × ℝ => F x p.1 p.2) :=
    fun x => hF.comp (continuous_const.prodMk continuous_id)
  have hF'_slice : Continuous (fun p : ℝ × ℝ => F' x₀ p.1 p.2) :=
    hF'.comp (continuous_const.prodMk continuous_id)
  have h_eq : (fun x => ∫ y in (0 : ℝ)..1, ∫ z in (0 : ℝ)..1, F x y z) =
      (fun x => ∫ p : ℝ × ℝ, F x p.1 p.2 ∂uMeas2) := by
    funext x; exact int2_eq_uMeas2 (hF_slice x)
  rw [h_eq, int2_eq_uMeas2 hF'_slice]
  let s : Set ℝ := Set.Icc (x₀ - 1) (x₀ + 1)
  have hs : s ∈ 𝓝 x₀ := Icc_mem_nhds (by linarith) (by linarith)
  obtain ⟨C, hC⟩ := (isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc)).exists_bound_of_continuousOn
    hF'.continuousOn (s := s ×ˢ uSquare)
  have h_meas : ∀ᶠ x in 𝓝 x₀, AEStronglyMeasurable (fun p : ℝ × ℝ => F x p.1 p.2) uMeas2 :=
    Eventually.of_forall fun x => (hF_slice x).aestronglyMeasurable
  have h_int : Integrable (fun p : ℝ × ℝ => F x₀ p.1 p.2) uMeas2 := by
    rw [uMeas2_eq_restrict]
    exact (hF_slice x₀).continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)
  have h_meas' : AEStronglyMeasurable (fun p : ℝ × ℝ => F' x₀ p.1 p.2) uMeas2 :=
    hF'_slice.aestronglyMeasurable
  have h_bound : ∀ᵐ p ∂uMeas2, ∀ x ∈ s, ‖F' x p.1 p.2‖ ≤ C := by
    rw [uMeas2_eq_restrict]
    filter_upwards [ae_restrict_mem (measurableSet_Icc.prod measurableSet_Icc)] with p hp x hx
    exact hC (x, p) ⟨hx, hp⟩
  have h_diff_ae : ∀ᵐ p ∂uMeas2, ∀ x ∈ s, HasDerivAt (fun r => F r p.1 p.2) (F' x p.1 p.2) x :=
    Eventually.of_forall fun p x _ => hdiff x p.1 p.2
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le hs h_meas h_int h_meas'
    h_bound (integrable_const C) h_diff_ae).2

private theorem variance_identity_unit {φ : ℝ → ℝ} (hφ : Continuous φ) :
    (∫ s in (0 : ℝ)..1, (φ s) ^ 2) =
      (∫ s in (0 : ℝ)..1, (φ s - ∫ u in (0 : ℝ)..1, φ u) ^ 2) +
      (∫ u in (0 : ℝ)..1, φ u) ^ 2 := by
  let m : ℝ := ∫ u in (0 : ℝ)..1, φ u
  have h_exp : (∫ s in (0 : ℝ)..1, (φ s - m) ^ 2) =
      ∫ s in (0 : ℝ)..1, (((φ s) ^ 2 - 2 * m * φ s) + m ^ 2) := by
    congr 1; funext s; ring
  have hc1 : Continuous (fun s => (φ s) ^ 2) := hφ.pow 2
  have hc2 : Continuous (fun s => 2 * m * φ s) := continuous_const.mul hφ
  have hc3 : Continuous (fun _ : ℝ => m ^ 2) := continuous_const
  have hc12 : Continuous (fun s : ℝ => (φ s) ^ 2 - 2 * m * φ s) := hc1.sub hc2
  rw [h_exp,
      intervalIntegral.integral_add (hc12.intervalIntegrable 0 1) (hc3.intervalIntegrable 0 1),
      intervalIntegral.integral_sub (hc1.intervalIntegrable 0 1) (hc2.intervalIntegrable 0 1),
      intervalIntegral.integral_const_mul (2 * m) φ,
      intervalIntegral.integral_const]
  simp only [sub_zero, one_smul]
  dsimp only [m]
  ring

private theorem continuous_vec3_xyz :
    Continuous (fun q : ℝ × (ℝ × ℝ) => vec3 q.1 q.2.1 q.2.2) := by
  refine continuous_pi fun i => ?_
  match i with
  | ⟨0, _⟩ => exact continuous_fst
  | ⟨1, _⟩ => exact continuous_fst.comp continuous_snd
  | ⟨2, _⟩ => exact continuous_snd.comp continuous_snd

private theorem vec3_add_basis0 (x y z : ℝ) : vec3 (x + 1) y z = vec3 x y z + basisVec 0 := by
  funext i; match i with | ⟨0, _⟩ => simp [vec3, basisVec] | ⟨1, _⟩ => simp [vec3, basisVec] | ⟨2, _⟩ => simp [vec3, basisVec]

private theorem vec3_add_basis1 (x y z : ℝ) : vec3 x (y + 1) z = vec3 x y z + basisVec 1 := by
  funext i; match i with | ⟨0, _⟩ => simp [vec3, basisVec] | ⟨1, _⟩ => simp [vec3, basisVec] | ⟨2, _⟩ => simp [vec3, basisVec]

private theorem vec3_add_basis2 (x y z : ℝ) : vec3 x y (z + 1) = vec3 x y z + basisVec 2 := by
  funext i; match i with | ⟨0, _⟩ => simp [vec3, basisVec] | ⟨1, _⟩ => simp [vec3, basisVec] | ⟨2, _⟩ => simp [vec3, basisVec]

private theorem hasDerivAt_vec3_0 (y z t : ℝ) : HasDerivAt (fun s => vec3 s y z) (basisVec 0) t := by
  refine hasDerivAt_pi.mpr fun k => ?_
  match k with
  | ⟨0, _⟩ => change HasDerivAt (fun s : ℝ => s) 1 t; exact hasDerivAt_id t
  | ⟨1, _⟩ => change HasDerivAt (fun _ : ℝ => y) 0 t; exact hasDerivAt_const t y
  | ⟨2, _⟩ => change HasDerivAt (fun _ : ℝ => z) 0 t; exact hasDerivAt_const t z

private theorem hasDerivAt_vec3_1 (x z t : ℝ) : HasDerivAt (fun s => vec3 x s z) (basisVec 1) t := by
  refine hasDerivAt_pi.mpr fun k => ?_
  match k with
  | ⟨0, _⟩ => change HasDerivAt (fun _ : ℝ => x) 0 t; exact hasDerivAt_const t x
  | ⟨1, _⟩ => change HasDerivAt (fun s : ℝ => s) 1 t; exact hasDerivAt_id t
  | ⟨2, _⟩ => change HasDerivAt (fun _ : ℝ => z) 0 t; exact hasDerivAt_const t z

private theorem hasDerivAt_vec3_2 (x y t : ℝ) : HasDerivAt (fun s => vec3 x y s) (basisVec 2) t := by
  refine hasDerivAt_pi.mpr fun k => ?_
  match k with
  | ⟨0, _⟩ => change HasDerivAt (fun _ : ℝ => x) 0 t; exact hasDerivAt_const t x
  | ⟨1, _⟩ => change HasDerivAt (fun _ : ℝ => y) 0 t; exact hasDerivAt_const t y
  | ⟨2, _⟩ => change HasDerivAt (fun s : ℝ => s) 1 t; exact hasDerivAt_id t

/-- **3D Periodic Poincaré Inequality on `𝕋³` (Scalar):**
    For any `C¹` periodic scalar field `f : ℝ³ → ℝ` with zero spatial mean (`∫_{𝕋³} f = 0`):
      `8 ∫_{𝕋³} f(x)² dx ≤ ∫_{𝕋³} |∇f(x)|² dx` (`0 sorryAx`). -/
private theorem poincare_3d_step_z
    {f : R3 → ℝ} (hf : ContDiff ℝ 1 f) (hpf : IsPeriodic3D f) (x y : ℝ) :
    8 * (∫ z in (0 : ℝ)..1, (f (vec3 x y z) - ∫ u in (0 : ℝ)..1, f (vec3 x y u)) ^ 2) ≤
      ∫ z in (0 : ℝ)..1, (partialDerivScalar f (vec3 x y z) 2) ^ 2 := by
  have hdiff : Differentiable ℝ f := hf.differentiable (by simp)
  have hc_p2 := continuous_partialDerivScalar_of_contDiff hf 2
  have hp_p2 : IsPeriodic3D (fun p => partialDerivScalar f p 2) := IsPeriodic3D.partialDeriv hpf hdiff 2
  have hcz : Continuous (fun z => f (vec3 x y z)) :=
    hf.continuous.comp (continuous_pi fun k => match k with
      | ⟨0, _⟩ => continuous_const | ⟨1, _⟩ => continuous_const | ⟨2, _⟩ => continuous_id)
  have hcz_sub : Continuous (fun z => f (vec3 x y z) - ∫ u in (0 : ℝ)..1, f (vec3 x y u)) :=
    hcz.sub continuous_const
  have hcz' : Continuous (fun z => partialDerivScalar f (vec3 x y z) 2) :=
    hc_p2.comp (continuous_pi fun k => match k with
      | ⟨0, _⟩ => continuous_const | ⟨1, _⟩ => continuous_const | ⟨2, _⟩ => continuous_id)
  have hmean_z : ∫ z in (0 : ℝ)..1, (f (vec3 x y z) - ∫ u in (0 : ℝ)..1, f (vec3 x y u)) = 0 := by
    rw [intervalIntegral.integral_sub (hcz.intervalIntegrable 0 1)
          (continuous_const.intervalIntegrable 0 1),
        intervalIntegral.integral_const]
    simp only [sub_zero, one_smul]
    ring
  exact poincare_1d_periodic hcz_sub hcz'
    (fun z => by
      have hd : HasDerivAt (fun s => f (vec3 x y s)) (partialDerivScalar f (vec3 x y z) 2) z :=
        (hdiff (vec3 x y z)).hasFDerivAt.comp_hasDerivAt z (hasDerivAt_vec3_2 x y z)
      exact hd.sub_const (∫ u in (0 : ℝ)..1, f (vec3 x y u)))
    (fun z => by rw [vec3_add_basis2, hpf (vec3 x y z) 2])
    (fun z => by rw [vec3_add_basis2]; exact hp_p2 (vec3 x y z) 2)
    hmean_z

private theorem unitIntegral_sq_le_integral_sq {φ : ℝ → ℝ} (hφ : Continuous φ) :
    (∫ t in (0 : ℝ)..1, φ t) ^ 2 ≤ ∫ t in (0 : ℝ)..1, (φ t) ^ 2 := by
  have h := intervalIntegral_sq_le_mul_integral_sq (by norm_num : (0 : ℝ) ≤ 1) hφ
  linarith

private theorem continuous_vec3_yz' (x : ℝ) :
    Continuous (fun p : ℝ × ℝ => vec3 x p.1 p.2) :=
  continuous_pi fun k => match k with
    | ⟨0, _⟩ => continuous_const | ⟨1, _⟩ => continuous_fst | ⟨2, _⟩ => continuous_snd

private theorem continuous_vec3_z' (x y : ℝ) :
    Continuous (fun z : ℝ => vec3 x y z) :=
  continuous_pi fun k => match k with
    | ⟨0, _⟩ => continuous_const | ⟨1, _⟩ => continuous_const | ⟨2, _⟩ => continuous_id

private theorem poincare_3d_step_y
    {f : R3 → ℝ} (hf : ContDiff ℝ 1 f) (hpf : IsPeriodic3D f) (x : ℝ) :
    8 * (∫ y in (0 : ℝ)..1,
        ((∫ z in (0 : ℝ)..1, f (vec3 x y z)) -
         ∫ v in (0 : ℝ)..1, ∫ z in (0 : ℝ)..1, f (vec3 x v z)) ^ 2) ≤
      ∫ y in (0 : ℝ)..1, ∫ z in (0 : ℝ)..1, (partialDerivScalar f (vec3 x y z) 1) ^ 2 := by
  have hdiff : Differentiable ℝ f := hf.differentiable (by simp)
  have hc_p1 := continuous_partialDerivScalar_of_contDiff hf 1
  have hp_p1 : IsPeriodic3D (fun p => partialDerivScalar f p 1) := IsPeriodic3D.partialDeriv hpf hdiff 1
  let f1x : ℝ → ℝ := fun y => ∫ z in (0 : ℝ)..1, f (vec3 x y z)
  let df1 : ℝ → ℝ := fun y => ∫ z in (0 : ℝ)..1, partialDerivScalar f (vec3 x y z) 1
  have hF_cont : Continuous (fun p : ℝ × ℝ => f (vec3 x p.1 p.2)) :=
    hf.continuous.comp (continuous_vec3_yz' x)
  have hF'_cont : Continuous (fun p : ℝ × ℝ => partialDerivScalar f (vec3 x p.1 p.2) 1) :=
    hc_p1.comp (continuous_vec3_yz' x)
  have hF'_sq : Continuous (fun p : ℝ × ℝ => (partialDerivScalar f (vec3 x p.1 p.2) 1) ^ 2) :=
    hF'_cont.pow 2
  have hf1_cont : Continuous f1x :=
    continuous_int1_of_joint (G := fun y z => f (vec3 x y z)) hF_cont
  have hf1_sub : Continuous (fun y => f1x y - ∫ v in (0 : ℝ)..1, f1x v) :=
    hf1_cont.sub continuous_const
  have hdf1_cont : Continuous df1 :=
    continuous_int1_of_joint (G := fun y z => partialDerivScalar f (vec3 x y z) 1) hF'_cont
  have hf1_deriv : ∀ y : ℝ, HasDerivAt f1x (df1 y) y := fun y =>
    hasDerivAt_int1_unit
      (F := fun s z => f (vec3 x s z))
      (F' := fun s z => partialDerivScalar f (vec3 x s z) 1)
      hF_cont hF'_cont
      (fun s z => (hdiff (vec3 x s z)).hasFDerivAt.comp_hasDerivAt s (hasDerivAt_vec3_1 x z s)) y
  have hmean_y : ∫ y in (0 : ℝ)..1, (f1x y - ∫ v in (0 : ℝ)..1, f1x v) = 0 := by
    rw [intervalIntegral.integral_sub (hf1_cont.intervalIntegrable 0 1)
          (continuous_const.intervalIntegrable 0 1),
        intervalIntegral.integral_const]
    simp only [sub_zero, one_smul]
    ring
  have hpoin_y : 8 * (∫ y in (0 : ℝ)..1, (f1x y - ∫ v in (0 : ℝ)..1, f1x v) ^ 2) ≤
      ∫ y in (0 : ℝ)..1, (df1 y) ^ 2 :=
    poincare_1d_periodic hf1_sub hdf1_cont
      (fun y => (hf1_deriv y).sub_const (∫ v in (0 : ℝ)..1, f1x v))
      (fun y => by
        dsimp only [f1x]
        have heq : (fun z => f (vec3 x (y + 1) z)) = (fun z => f (vec3 x y z)) := by
          funext z; rw [vec3_add_basis1, hpf (vec3 x y z) 1]
        rw [heq])
      (fun y => by
        dsimp only [df1]
        have heq : (fun z => partialDerivScalar f (vec3 x (y + 1) z) 1) =
            (fun z => partialDerivScalar f (vec3 x y z) 1) := by
          funext z; rw [vec3_add_basis1]; exact hp_p1 (vec3 x y z) 1
        rw [heq])
      hmean_y
  have hc_lhs_y : Continuous (fun y => (df1 y) ^ 2) := hdf1_cont.pow 2
  have hc_rhs_y : Continuous (fun y => ∫ z in (0 : ℝ)..1, (partialDerivScalar f (vec3 x y z) 1) ^ 2) :=
    continuous_int1_of_joint (G := fun y z => (partialDerivScalar f (vec3 x y z) 1) ^ 2) hF'_sq
  have hcs_y : (∫ y in (0 : ℝ)..1, (df1 y) ^ 2) ≤
      ∫ y in (0 : ℝ)..1, ∫ z in (0 : ℝ)..1, (partialDerivScalar f (vec3 x y z) 1) ^ 2 :=
    intervalIntegral.integral_mono_on (by norm_num : (0 : ℝ) ≤ 1)
      (hc_lhs_y.intervalIntegrable 0 1) (hc_rhs_y.intervalIntegrable 0 1) fun y _ => by
        have hcz : Continuous (fun z => partialDerivScalar f (vec3 x y z) 1) :=
          hc_p1.comp (continuous_vec3_z' x y)
        exact unitIntegral_sq_le_integral_sq hcz
  exact le_trans hpoin_y hcs_y

private theorem poincare_3d_step_x
    {f : R3 → ℝ} (hf : ContDiff ℝ 1 f) (hpf : IsPeriodic3D f)
    (hmean : torusIntegral f = 0) :
    8 * (∫ x in (0 : ℝ)..1, (∫ y in (0 : ℝ)..1, ∫ z in (0 : ℝ)..1, f (vec3 x y z)) ^ 2) ≤
      torusIntegral (fun p => (partialDerivScalar f p 0) ^ 2) := by
  have hdiff : Differentiable ℝ f := hf.differentiable (by simp)
  have hc_p0 := continuous_partialDerivScalar_of_contDiff hf 0
  have hp_p0 : IsPeriodic3D (fun p => partialDerivScalar f p 0) := IsPeriodic3D.partialDeriv hpf hdiff 0
  let f2 : ℝ → ℝ := fun x => ∫ y in (0 : ℝ)..1, ∫ z in (0 : ℝ)..1, f (vec3 x y z)
  let df2 : ℝ → ℝ := fun x =>
    ∫ y in (0 : ℝ)..1, ∫ z in (0 : ℝ)..1, partialDerivScalar f (vec3 x y z) 0
  have hF_all : Continuous (fun q : ℝ × (ℝ × ℝ) => f (vec3 q.1 q.2.1 q.2.2)) :=
    hf.continuous.comp continuous_vec3_xyz
  have hF'_cont : Continuous (fun q : ℝ × (ℝ × ℝ) => partialDerivScalar f (vec3 q.1 q.2.1 q.2.2) 0) :=
    hc_p0.comp continuous_vec3_xyz
  have hF'_sq : Continuous (fun q : ℝ × (ℝ × ℝ) => (partialDerivScalar f (vec3 q.1 q.2.1 q.2.2) 0) ^ 2) :=
    hF'_cont.pow 2
  have hf2_cont : Continuous f2 :=
    continuous_int2_of_joint (G := fun x y z => f (vec3 x y z)) hF_all
  have hdf2_cont : Continuous df2 :=
    continuous_int2_of_joint (G := fun x y z => partialDerivScalar f (vec3 x y z) 0) hF'_cont
  have hf2_deriv : ∀ x : ℝ, HasDerivAt f2 (df2 x) x := fun x =>
    hasDerivAt_int2_unit
      (F := fun s y z => f (vec3 s y z))
      (F' := fun s y z => partialDerivScalar f (vec3 s y z) 0)
      hF_all hF'_cont
      (fun s y z => (hdiff (vec3 s y z)).hasFDerivAt.comp_hasDerivAt s (hasDerivAt_vec3_0 y z s)) x
  have hpoin_x : 8 * (∫ x in (0 : ℝ)..1, (f2 x) ^ 2) ≤ ∫ x in (0 : ℝ)..1, (df2 x) ^ 2 :=
    poincare_1d_periodic hf2_cont hdf2_cont hf2_deriv
      (fun x => by
        dsimp only [f2]
        have heq : ∀ y z : ℝ, f (vec3 (x + 1) y z) = f (vec3 x y z) := fun y z => by
          rw [vec3_add_basis0, hpf (vec3 x y z) 0]
        simp_rw [heq])
      (fun x => by
        dsimp only [df2]
        have heq : ∀ y z : ℝ, partialDerivScalar f (vec3 (x + 1) y z) 0 =
            partialDerivScalar f (vec3 x y z) 0 := fun y z => by
          rw [vec3_add_basis0]; exact hp_p0 (vec3 x y z) 0
        simp_rw [heq])
      hmean
  have hc_lhs_x : Continuous (fun x => (df2 x) ^ 2) := hdf2_cont.pow 2
  have hc_rhs_x : Continuous (fun x =>
      ∫ y in (0 : ℝ)..1, ∫ z in (0 : ℝ)..1, (partialDerivScalar f (vec3 x y z) 0) ^ 2) :=
    continuous_int2_of_joint (G := fun x y z => (partialDerivScalar f (vec3 x y z) 0) ^ 2) hF'_sq
  have hcs_x : (∫ x in (0 : ℝ)..1, (df2 x) ^ 2) ≤
      torusIntegral (fun p => (partialDerivScalar f p 0) ^ 2) := by
    unfold torusIntegral
    refine intervalIntegral.integral_mono_on (by norm_num : (0 : ℝ) ≤ 1)
      (hc_lhs_x.intervalIntegrable 0 1) (hc_rhs_x.intervalIntegrable 0 1) fun x _ => ?_
    have hFx' : Continuous (fun p : ℝ × ℝ => partialDerivScalar f (vec3 x p.1 p.2) 0) :=
      hc_p0.comp (continuous_vec3_yz' x)
    have hcy : Continuous (fun y => ∫ z in (0 : ℝ)..1, partialDerivScalar f (vec3 x y z) 0) :=
      continuous_int1_of_joint (G := fun y z => partialDerivScalar f (vec3 x y z) 0) hFx'
    have hcs1 := unitIntegral_sq_le_integral_sq hcy
    have hcy_sq : Continuous (fun y => (∫ z in (0 : ℝ)..1, partialDerivScalar f (vec3 x y z) 0) ^ 2) :=
      hcy.pow 2
    have hcz_sq_int : Continuous (fun y => ∫ z in (0 : ℝ)..1, (partialDerivScalar f (vec3 x y z) 0) ^ 2) :=
      continuous_int1_of_joint (G := fun y z => (partialDerivScalar f (vec3 x y z) 0) ^ 2) (hFx'.pow 2)
    have hcs2 : (∫ y in (0 : ℝ)..1, (∫ z in (0 : ℝ)..1, partialDerivScalar f (vec3 x y z) 0) ^ 2) ≤
        ∫ y in (0 : ℝ)..1, ∫ z in (0 : ℝ)..1, (partialDerivScalar f (vec3 x y z) 0) ^ 2 :=
      intervalIntegral.integral_mono_on (by norm_num : (0 : ℝ) ≤ 1)
        (hcy_sq.intervalIntegrable 0 1) (hcz_sq_int.intervalIntegrable 0 1) fun y _ => by
          have hcz : Continuous (fun z => partialDerivScalar f (vec3 x y z) 0) :=
            hc_p0.comp (continuous_vec3_z' x y)
          exact unitIntegral_sq_le_integral_sq hcz
    exact le_trans hcs1 hcs2
  exact le_trans hpoin_x hcs_x

theorem poincare_3d_torus
    {f : R3 → ℝ} (hf : ContDiff ℝ 1 f) (hpf : IsPeriodic3D f)
    (hmean : torusIntegral f = 0) :
    8 * torusIntegral (fun x => (f x) ^ 2) ≤
      torusIntegral (fun x =>
        (partialDerivScalar f x 0) ^ 2 +
        (partialDerivScalar f x 1) ^ 2 +
        (partialDerivScalar f x 2) ^ 2) := by
  have hc_p0 := continuous_partialDerivScalar_of_contDiff hf 0
  have hc_p1 := continuous_partialDerivScalar_of_contDiff hf 1
  have hc_p2 := continuous_partialDerivScalar_of_contDiff hf 2
  let f1 : ℝ → ℝ → ℝ := fun x y => ∫ z in (0 : ℝ)..1, f (vec3 x y z)
  let f2 : ℝ → ℝ := fun x => ∫ y in (0 : ℝ)..1, f1 x y
  have hF_all : Continuous (fun q : ℝ × (ℝ × ℝ) => f (vec3 q.1 q.2.1 q.2.2)) :=
    hf.continuous.comp continuous_vec3_xyz
  have hF_sq : Continuous (fun q : ℝ × (ℝ × ℝ) => (f (vec3 q.1 q.2.1 q.2.2)) ^ 2) := hF_all.pow 2
  have hF_p1_sq : Continuous (fun q : ℝ × (ℝ × ℝ) => (partialDerivScalar f (vec3 q.1 q.2.1 q.2.2) 1) ^ 2) :=
    (hc_p1.comp continuous_vec3_xyz).pow 2
  have hF_p2_sq : Continuous (fun q : ℝ × (ℝ × ℝ) => (partialDerivScalar f (vec3 q.1 q.2.1 q.2.2) 2) ^ 2) :=
    (hc_p2.comp continuous_vec3_xyz).pow 2
  have hf2_cont : Continuous f2 :=
    continuous_int2_of_joint (G := fun x y z => f (vec3 x y z)) hF_all
  have h_xy_bound : ∀ x : ℝ,
      8 * (∫ y in (0 : ℝ)..1, ∫ z in (0 : ℝ)..1, (f (vec3 x y z)) ^ 2) ≤
        (∫ y in (0 : ℝ)..1, ∫ z in (0 : ℝ)..1, (partialDerivScalar f (vec3 x y z) 2) ^ 2) +
        (∫ y in (0 : ℝ)..1, ∫ z in (0 : ℝ)..1, (partialDerivScalar f (vec3 x y z) 1) ^ 2) +
        8 * (f2 x) ^ 2 := by
    intro x
    have hFx : Continuous (fun p : ℝ × ℝ => f (vec3 x p.1 p.2)) :=
      hf.continuous.comp (continuous_vec3_yz' x)
    have hFx_sq : Continuous (fun p : ℝ × ℝ => (f (vec3 x p.1 p.2)) ^ 2) := hFx.pow 2
    have hFp2x_sq : Continuous (fun p : ℝ × ℝ => (partialDerivScalar f (vec3 x p.1 p.2) 2) ^ 2) :=
      (hc_p2.comp (continuous_vec3_yz' x)).pow 2
    have hf1_cont : Continuous (fun y => f1 x y) :=
      continuous_int1_of_joint (G := fun y z => f (vec3 x y z)) hFx
    have h_step_z : ∀ y : ℝ,
        8 * (∫ z in (0 : ℝ)..1, (f (vec3 x y z)) ^ 2) ≤
          (∫ z in (0 : ℝ)..1, (partialDerivScalar f (vec3 x y z) 2) ^ 2) + 8 * (f1 x y) ^ 2 := fun y => by
      have hcz : Continuous (fun z => f (vec3 x y z)) := hf.continuous.comp (continuous_vec3_z' x y)
      have h_var_z := variance_identity_unit hcz
      dsimp only [f1]
      linarith [h_var_z, poincare_3d_step_z hf hpf x y]
    have hc_lhs : Continuous (fun y => 8 * ∫ z in (0 : ℝ)..1, (f (vec3 x y z)) ^ 2) :=
      continuous_const.mul (continuous_int1_of_joint (G := fun y z => (f (vec3 x y z)) ^ 2) hFx_sq)
    have hc_rhs1 : Continuous (fun y => ∫ z in (0 : ℝ)..1, (partialDerivScalar f (vec3 x y z) 2) ^ 2) :=
      continuous_int1_of_joint (G := fun y z => (partialDerivScalar f (vec3 x y z) 2) ^ 2) hFp2x_sq
    have hc_rhs2 : Continuous (fun y => 8 * (f1 x y) ^ 2) := continuous_const.mul (hf1_cont.pow 2)
    have hc_rhs12 : Continuous (fun y =>
        (∫ z in (0 : ℝ)..1, (partialDerivScalar f (vec3 x y z) 2) ^ 2) + 8 * (f1 x y) ^ 2) :=
      hc_rhs1.add hc_rhs2
    have h_int_y := intervalIntegral.integral_mono_on (μ := volume) (by norm_num : (0 : ℝ) ≤ 1)
      (hc_lhs.intervalIntegrable (μ := volume) 0 1) (hc_rhs12.intervalIntegrable (μ := volume) 0 1)
      (fun y _ => h_step_z y)
    rw [intervalIntegral.integral_const_mul 8,
        intervalIntegral.integral_add (hc_rhs1.intervalIntegrable (μ := volume) 0 1) (hc_rhs2.intervalIntegrable (μ := volume) 0 1),
        intervalIntegral.integral_const_mul 8] at h_int_y
    have h_var_y := variance_identity_unit hf1_cont
    dsimp only [f2, f1] at h_int_y h_var_y ⊢
    linarith [h_int_y, h_var_y, poincare_3d_step_y hf hpf x]
  have hc_x_lhs : Continuous (fun x => 8 * ∫ y in (0 : ℝ)..1, ∫ z in (0 : ℝ)..1, (f (vec3 x y z)) ^ 2) :=
    continuous_const.mul (continuous_int2_of_joint (G := fun x y z => (f (vec3 x y z)) ^ 2) hF_sq)
  have hc_x_p2 : Continuous (fun x => ∫ y in (0 : ℝ)..1, ∫ z in (0 : ℝ)..1, (partialDerivScalar f (vec3 x y z) 2) ^ 2) :=
    continuous_int2_of_joint (G := fun x y z => (partialDerivScalar f (vec3 x y z) 2) ^ 2) hF_p2_sq
  have hc_x_p1 : Continuous (fun x => ∫ y in (0 : ℝ)..1, ∫ z in (0 : ℝ)..1, (partialDerivScalar f (vec3 x y z) 1) ^ 2) :=
    continuous_int2_of_joint (G := fun x y z => (partialDerivScalar f (vec3 x y z) 1) ^ 2) hF_p1_sq
  have hc_x_f2 : Continuous (fun x => 8 * (f2 x) ^ 2) := continuous_const.mul (hf2_cont.pow 2)
  have hc_x_p21 : Continuous (fun x =>
      (∫ y in (0 : ℝ)..1, ∫ z in (0 : ℝ)..1, (partialDerivScalar f (vec3 x y z) 2) ^ 2) +
      (∫ y in (0 : ℝ)..1, ∫ z in (0 : ℝ)..1, (partialDerivScalar f (vec3 x y z) 1) ^ 2)) :=
    hc_x_p2.add hc_x_p1
  have hc_x_all : Continuous (fun x =>
      (∫ y in (0 : ℝ)..1, ∫ z in (0 : ℝ)..1, (partialDerivScalar f (vec3 x y z) 2) ^ 2) +
      (∫ y in (0 : ℝ)..1, ∫ z in (0 : ℝ)..1, (partialDerivScalar f (vec3 x y z) 1) ^ 2) +
      8 * (f2 x) ^ 2) :=
    hc_x_p21.add hc_x_f2
  have h_final_x := intervalIntegral.integral_mono_on (μ := volume) (by norm_num : (0 : ℝ) ≤ 1)
    (hc_x_lhs.intervalIntegrable (μ := volume) 0 1) (hc_x_all.intervalIntegrable (μ := volume) 0 1)
    (fun x _ => h_xy_bound x)
  rw [intervalIntegral.integral_const_mul 8,
      intervalIntegral.integral_add (hc_x_p21.intervalIntegrable (μ := volume) 0 1) (hc_x_f2.intervalIntegrable (μ := volume) 0 1),
      intervalIntegral.integral_add (hc_x_p2.intervalIntegrable (μ := volume) 0 1) (hc_x_p1.intervalIntegrable (μ := volume) 0 1),
      intervalIntegral.integral_const_mul 8] at h_final_x
  have hc_p0_sq : Continuous (fun x => (partialDerivScalar f x 0) ^ 2) := hc_p0.pow 2
  have hc_p1_sq : Continuous (fun x => (partialDerivScalar f x 1) ^ 2) := hc_p1.pow 2
  have hc_p2_sq : Continuous (fun x => (partialDerivScalar f x 2) ^ 2) := hc_p2.pow 2
  have h_x := poincare_3d_step_x hf hpf hmean
  rw [torusIntegral_add3 hc_p0_sq hc_p1_sq hc_p2_sq]
  unfold torusIntegral at h_x ⊢
  dsimp only [f2, f1] at h_final_x
  linarith [h_final_x, h_x]

/-- **3D Vector Poincaré Inequality on `𝕋³`:**
    For any `C¹` periodic vector field `w` whose components each have zero spatial mean:
      `8 ∫_{𝕋³} |w(x)|² dx ≤ ∫_{𝕋³} |∇w(x)|² dx`. -/
theorem poincare_3d_torus_vec
    {w : R3 → R3} (hw : ContDiff ℝ 1 w) (hpw : IsPeriodic3D w)
    (hmean : ∀ comp : Fin 3, torusIntegral (fun x => w x comp) = 0) :
    8 * torusIntegral (fun x => dot3D (w x) (w x)) ≤ torusIntegral (gradNormSq3D w) := by
  have hw0 : ContDiff ℝ 1 (fun y => w y 0) := contDiff_pi.mp hw 0
  have hw1 : ContDiff ℝ 1 (fun y => w y 1) := contDiff_pi.mp hw 1
  have hw2 : ContDiff ℝ 1 (fun y => w y 2) := contDiff_pi.mp hw 2
  have hpw0 : IsPeriodic3D (fun y => w y 0) := fun x i => congrArg (fun v => v 0) (hpw x i)
  have hpw1 : IsPeriodic3D (fun y => w y 1) := fun x i => congrArg (fun v => v 1) (hpw x i)
  have hpw2 : IsPeriodic3D (fun y => w y 2) := fun x i => congrArg (fun v => v 2) (hpw x i)
  have hp0 := poincare_3d_torus hw0 hpw0 (hmean 0)
  have hp1 := poincare_3d_torus hw1 hpw1 (hmean 1)
  have hp2 := poincare_3d_torus hw2 hpw2 (hmean 2)
  have hdot : torusIntegral (fun x => dot3D (w x) (w x)) =
      torusIntegral (fun x => (w x 0) ^ 2) +
      torusIntegral (fun x => (w x 1) ^ 2) +
      torusIntegral (fun x => (w x 2) ^ 2) := by
    have hpt : ∀ x : R3, dot3D (w x) (w x) = (w x 0) ^ 2 + (w x 1) ^ 2 + (w x 2) ^ 2 := fun x => by
      unfold dot3D; ring
    have hcw0 : Continuous (fun x => (w x 0) ^ 2) := hw0.continuous.pow 2
    have hcw1 : Continuous (fun x => (w x 1) ^ 2) := hw1.continuous.pow 2
    have hcw2 : Continuous (fun x => (w x 2) ^ 2) := hw2.continuous.pow 2
    rw [torusIntegral_congr hpt, torusIntegral_add3 hcw0 hcw1 hcw2]
  have hq : ∀ (f : R3 → ℝ), ContDiff ℝ 1 f → Continuous (fun x =>
      (partialDerivScalar f x 0) ^ 2 + (partialDerivScalar f x 1) ^ 2 + (partialDerivScalar f x 2) ^ 2) :=
    fun f hf =>
      (((continuous_partialDerivScalar_of_contDiff hf 0).pow 2).add
       ((continuous_partialDerivScalar_of_contDiff hf 1).pow 2)).add
      ((continuous_partialDerivScalar_of_contDiff hf 2).pow 2)
  have hgrad : torusIntegral (gradNormSq3D w) =
      torusIntegral (fun x => (partialDerivScalar (fun y => w y 0) x 0) ^ 2 +
        (partialDerivScalar (fun y => w y 0) x 1) ^ 2 + (partialDerivScalar (fun y => w y 0) x 2) ^ 2) +
      torusIntegral (fun x => (partialDerivScalar (fun y => w y 1) x 0) ^ 2 +
        (partialDerivScalar (fun y => w y 1) x 1) ^ 2 + (partialDerivScalar (fun y => w y 1) x 2) ^ 2) +
      torusIntegral (fun x => (partialDerivScalar (fun y => w y 2) x 0) ^ 2 +
        (partialDerivScalar (fun y => w y 2) x 1) ^ 2 + (partialDerivScalar (fun y => w y 2) x 2) ^ 2) := by
    have hpt : ∀ x : R3, gradNormSq3D w x =
        ((partialDerivScalar (fun y => w y 0) x 0) ^ 2 +
         (partialDerivScalar (fun y => w y 0) x 1) ^ 2 + (partialDerivScalar (fun y => w y 0) x 2) ^ 2) +
        ((partialDerivScalar (fun y => w y 1) x 0) ^ 2 +
         (partialDerivScalar (fun y => w y 1) x 1) ^ 2 + (partialDerivScalar (fun y => w y 1) x 2) ^ 2) +
        ((partialDerivScalar (fun y => w y 2) x 0) ^ 2 +
         (partialDerivScalar (fun y => w y 2) x 1) ^ 2 + (partialDerivScalar (fun y => w y 2) x 2) ^ 2) :=
      fun x => by unfold gradNormSq3D; ring
    rw [torusIntegral_congr hpt, torusIntegral_add3 (hq _ hw0) (hq _ hw1) (hq _ hw2)]
  rw [hdot, hgrad]
  linarith

-- ============================================================================
-- SECTION 5: ANALYTICAL LEMMA 4 (BERNSTEIN–POINCARÉ) & EXPONENTIAL DECAY
-- ============================================================================

/-- **ANALYTICAL LEMMA 4 (Unconditional Bernstein–Poincaré Spectral Coercivity for Vorticity on `𝕋³`):**
    Proved directly from `IsPeriodicClassicalNS3D_C3` with ZERO external spectral assumptions:
    For every `t ≥ 0`, palinstrophy `P(t) = ∫_{𝕋³} |∇ω|² dx` coercively dominates enstrophy `Z(t)`:
      `16 * Z(t) ≤ P(t)`  and  `16 * ν * Z(t) ≤ ν * P(t)` (`0 sorryAx`). -/
theorem analytical_lemma4_bernstein_poincare_vorticity
    {u : ℝ → R3 → R3} {p : ℝ → R3 → ℝ} {ν : ℝ}
    (hns : IsPeriodicClassicalNS3D_C3 u p ν) {t : ℝ} (ht : t ≥ 0) :
    16 * enstrophy u t ≤ palinstrophy3D (u t) ∧
    ν * (16 * enstrophy u t) ≤ ν * palinstrophy3D (u t) := by
  have hu3 : ContDiff ℝ 3 (u t) := hns.h_u_c3_global t ht
  have hu1 : ContDiff ℝ 1 (u t) := contDiff_one_of_two' (contDiff_two_of_three' hu3)
  have hw1 : ContDiff ℝ 1 (curl3D (u t)) := contDiff_one_of_two' (contDiff_two_curl3D hu3)
  have hpu : IsPeriodic3D (u t) := hns.h_u_periodic t ht
  have hpw : IsPeriodic3D (curl3D (u t)) := hpu.curl3D (hu1.differentiable (by simp))
  have hmean : ∀ comp : Fin 3, torusIntegral (fun x => curl3D (u t) x comp) = 0 :=
    fun comp => vorticity_mean_zero hu1 hpu comp
  have hpoin := poincare_3d_torus_vec hw1 hpw hmean
  have h16 : 16 * enstrophy u t ≤ palinstrophy3D (u t) := by
    unfold enstrophy palinstrophy3D
    linarith
  have h_l4 := GarryNavierStokesMathlib.lemma4_bernstein_poincare_spectral_coercivity
    ν (palinstrophy3D (u t)) 16 (enstrophy u t) (ν * palinstrophy3D (u t))
    (le_of_lt hns.h_nu_pos) h16 rfl
  exact ⟨h16, h_l4⟩

/-- **Global Unconditional Exponential Kinetic Energy Decay on `𝕋³`:**
    For EVERY periodic classical 3D Navier-Stokes solution `(u, p)` with zero initial mean
    velocity (`∫_{𝕋³} u(0, x) dx = 0`), kinetic energy decays exponentially for all `T ≥ 0`:
      `E(T) ≤ E(0) * Real.exp (-16 * ν * T)` (`0 sorryAx`). -/
theorem global_exponential_energy_decay_torus3D
    {u : ℝ → R3 → R3} {p : ℝ → R3 → ℝ} {ν : ℝ}
    (hns : IsPeriodicClassicalNS3D_C3 u p ν)
    (hmean0 : ∀ comp : Fin 3, torusIntegral (fun x => u 0 x comp) = 0)
    {T : ℝ} (hT : 0 ≤ T) :
    kineticEnergy u T ≤ kineticEnergy u 0 * Real.exp (-16 * ν * T) := by
  let h : ℝ → ℝ := fun s => Real.exp (16 * ν * s) * kineticEnergy u s
  let h' : ℝ → ℝ := fun s =>
    Real.exp (16 * ν * s) * (16 * ν * kineticEnergy u s - ν * torusIntegral (gradNormSq3D (u s)))
  have h_deriv : ∀ s : ℝ, 0 ≤ s → HasDerivAt h (h' s) s := by
    intro s hs
    have hexp : HasDerivAt (fun r : ℝ => Real.exp (16 * ν * r)) (Real.exp (16 * ν * s) * (16 * ν)) s := by
      have hlin : HasDerivAt (fun r : ℝ => 16 * ν * r) (16 * ν) s := by
        have h1 : HasDerivAt (fun r : ℝ => 16 * ν * r) (16 * ν * 1) s :=
          (hasDerivAt_id s).const_mul (16 * ν)
        rwa [mul_one] at h1
      exact (Real.hasDerivAt_exp (16 * ν * s)).comp s hlin
    have hE := (hasDerivAt_kineticEnergy_leray hns hs).1
    have hprod := hexp.mul hE
    have heq_d : Real.exp (16 * ν * s) * (16 * ν) * kineticEnergy u s +
        Real.exp (16 * ν * s) * (-ν * torusIntegral (gradNormSq3D (u s))) = h' s := by
      dsimp only [h']; ring
    rw [heq_d] at hprod
    exact hprod
  have h_nonpos : ∀ s : ℝ, 0 ≤ s → h' s ≤ 0 := by
    intro s hs
    have hmeans : ∀ comp : Fin 3, torusIntegral (fun x => u s x comp) = 0 := fun comp => by
      rw [momentum_conservation_torus3D hns hs comp, hmean0 comp]
    have hu1 : ContDiff ℝ 1 (u s) := contDiff_one_of_two' (contDiff_two_of_three' (hns.h_u_c3_global s hs))
    have hpoin := poincare_3d_torus_vec hu1 (hns.h_u_periodic s hs) hmeans
    have h16E : 16 * kineticEnergy u s ≤ torusIntegral (gradNormSq3D (u s)) := by
      unfold kineticEnergy; linarith
    have hbr : 16 * ν * kineticEnergy u s - ν * torusIntegral (gradNormSq3D (u s)) ≤ 0 := by
      nlinarith [hns.h_nu_pos, h16E]
    exact mul_nonpos_of_nonneg_of_nonpos (le_of_lt (Real.exp_pos _)) hbr
  have hu_cont : Continuous (fun q : ℝ × R3 => u q.1 q.2) :=
    (contDiff_iff_contDiffAt.mpr hns.h_u_c2_spacetime).continuous
  have hu0 : Continuous (fun q : ℝ × R3 => u q.1 q.2 0) := (continuous_apply 0).comp hu_cont
  have hu1 : Continuous (fun q : ℝ × R3 => u q.1 q.2 1) := (continuous_apply 1).comp hu_cont
  have hu2 : Continuous (fun q : ℝ × R3 => u q.1 q.2 2) := (continuous_apply 2).comp hu_cont
  have h_joint_E : Continuous (fun q : ℝ × R3 => dot3D (u q.1 q.2) (u q.1 q.2)) := by
    unfold dot3D
    exact ((hu0.mul hu0).add (hu1.mul hu1)).add (hu2.mul hu2)
  have h_intE_cont : Continuous (fun s => torusIntegral (fun x => dot3D (u s x) (u s x))) :=
    continuous_torusIntegral_of_joint_continuous (G := fun s x => dot3D (u s x) (u s x)) h_joint_E
  have hE_cont : Continuous (kineticEnergy u) := by
    unfold kineticEnergy
    exact continuous_const.mul h_intE_cont
  have h_joint_grad : Continuous (fun q : ℝ × R3 => gradNormSq3D (u q.1) q.2) := by
    have hc_sp : ∀ c i : Fin 3, Continuous (fun q : ℝ × R3 =>
        partialDerivScalar (fun y => u q.1 y c) q.2 i) := by
      intro c i
      have hFc : ∀ q : ℝ × R3, ContDiffAt ℝ 2 (fun r : ℝ × R3 => u r.1 r.2 c) q :=
        fun q => contDiffAt_pi.mp (hns.h_u_c2_spacetime q) c
      have hfun : (fun q : ℝ × R3 => partialDerivScalar (fun y => u q.1 y c) q.2 i) =
          (fun q : ℝ × R3 => fderiv ℝ (fun r : ℝ × R3 => u r.1 r.2 c) q ((0 : ℝ), basisVec i)) := by
        funext q; exact spacePartial_eq_fderiv_prod (fun r => u r.1 r.2 c) hFc q.1 q.2 i
      rw [hfun]
      have hcd1 : ContDiff ℝ 1 (fderiv ℝ (fun r : ℝ × R3 => u r.1 r.2 c)) :=
        (contDiff_iff_contDiffAt.mpr hFc).fderiv_right (by simp [one_add_one_eq_two])
      exact (ContinuousLinearMap.apply ℝ ℝ ((0 : ℝ), basisVec i)).continuous.comp hcd1.continuous
    unfold gradNormSq3D
    exact (((((((((hc_sp 0 0).pow 2).add ((hc_sp 0 1).pow 2)).add ((hc_sp 0 2).pow 2)).add
      ((hc_sp 1 0).pow 2)).add ((hc_sp 1 1).pow 2)).add ((hc_sp 1 2).pow 2)).add
      ((hc_sp 2 0).pow 2)).add ((hc_sp 2 1).pow 2)).add ((hc_sp 2 2).pow 2)
  have h_grad_cont : Continuous (fun s => torusIntegral (gradNormSq3D (u s))) :=
    continuous_torusIntegral_of_joint_continuous (G := fun s x => gradNormSq3D (u s) x) h_joint_grad
  have hc_exp : Continuous (fun s : ℝ => Real.exp (16 * ν * s)) :=
    Real.continuous_exp.comp (continuous_const.mul continuous_id)
  have hc_br : Continuous (fun s : ℝ =>
      16 * ν * kineticEnergy u s - ν * torusIntegral (gradNormSq3D (u s))) :=
    (continuous_const.mul hE_cont).sub (continuous_const.mul h_grad_cont)
  have hh'_cont : Continuous h' := hc_exp.mul hc_br
  have h_ftc := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (a := (0 : ℝ)) (b := T) (f := h) (f' := h')
    (fun s hs => by rw [Set.uIcc_of_le hT] at hs; exact h_deriv s hs.1)
    (hh'_cont.intervalIntegrable 0 T)
  have h_int_nonpos : (∫ s in (0 : ℝ)..T, h' s) ≤ 0 := by
    have hnn : 0 ≤ ∫ s in (0 : ℝ)..T, (-h' s) :=
      intervalIntegral.integral_nonneg hT fun s hs => by linarith [h_nonpos s hs.1]
    rw [intervalIntegral.integral_neg] at hnn
    linarith
  have hhT_le : h T ≤ h 0 := by linarith
  have h0_eq : h 0 = kineticEnergy u 0 := by dsimp only [h]; simp
  rw [h0_eq] at hhT_le
  have hexp_pos : 0 < Real.exp (-16 * ν * T) := Real.exp_pos _
  have hmul := mul_le_mul_of_nonneg_right hhT_le (le_of_lt hexp_pos)
  have hcancel : h T * Real.exp (-16 * ν * T) = kineticEnergy u T := by
    dsimp only [h]
    have hz : 16 * ν * T + -16 * ν * T = 0 := by ring
    calc Real.exp (16 * ν * T) * kineticEnergy u T * Real.exp (-16 * ν * T)
        = (Real.exp (16 * ν * T) * Real.exp (-16 * ν * T)) * kineticEnergy u T := by ring
      _ = Real.exp (16 * ν * T + -16 * ν * T) * kineticEnergy u T := by rw [← Real.exp_add]
      _ = Real.exp 0 * kineticEnergy u T := by rw [hz]
      _ = kineticEnergy u T := by simp
  linarith

-- ============================================================================
-- SECTION 6: AXIOM AUDIT TRAIL (0 sorryAx)
-- ============================================================================

#print axioms torusIntegral_curlNormSq_add_divSq
#print axioms enstrophy_eq_half_gradNormSq
#print axioms global_enstrophy_time_integral_bound
#print axioms vorticity_mean_zero
#print axioms momentum_conservation_torus3D
#print axioms poincare_1d_periodic
#print axioms poincare_3d_torus
#print axioms poincare_3d_torus_vec
#print axioms analytical_lemma4_bernstein_poincare_vorticity
#print axioms global_exponential_energy_decay_torus3D

end GarryPoincareSobolev3D