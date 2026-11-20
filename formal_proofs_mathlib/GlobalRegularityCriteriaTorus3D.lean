import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import LocalExistenceTorus3D

/-!
# GARRYULT v4.0.0 — Milestone 7A: Unconditional Global Regularity Criteria on `𝕋³`
# 1. Differential Grönwall Inequality on `[0, T]`
# 2. True 3D Beale–Kato–Majda (BKM) / Velocity-Gradient Enstrophy Continuation Bound
# 3. Unconditional Classical Uniqueness (`u(0) = v(0) ⇒ u ≡ v`) for `IsPeriodicClassicalNS3D_C3`
# 4. Duhamel Semigroup Gluing & Unconditional Global Existence on `[0, ∞)` for Small
#    Mean-Zero `H²(𝕋³)` Initial Data (`‖u₀‖²_{H²} ≤ π² ν² / 217088`, `0 sorryAx`)
-/

namespace GarryGlobalRegularity3D

open MeasureTheory Filter Topology GarryReal3DCalculus GarryVorticity3D
  GarryLerayTorus3D GarryLerayEnergyLaw3D GarryPoincareSobolev3D
  GarryFourierSpectral3D GarrySpectralOperators3D GarryParsevalSobolev3D
  GarrySobolevEmbedding3D GarrySpectralAlgebra3D GarrySpectralBilinear3D
  GarryDuhamelOperator3D GarryLocalExistence3D

-- ============================================================================
-- SECTION 1: DIFFERENTIAL GRÖNWALL & TORUS INTEGRAL MONOTONICITY ON `[0, 1]³`
-- ============================================================================

private theorem le_of_hasDerivAt_nonpos_Icc {h h' : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hderiv : ∀ t ∈ Set.Icc a b, HasDerivAt h (h' t) t)
    (hnonpos : ∀ t ∈ Set.Ioo a b, h' t ≤ 0) :
    h b ≤ h a := by
  rcases eq_or_lt_of_le hab with rfl | hlt
  · exact le_rfl
  · have hcont : ContinuousOn h (Set.Icc a b) :=
      fun t ht => (hderiv t ht).continuousAt.continuousWithinAt
    obtain ⟨c, hc, hslope⟩ := exists_hasDerivAt_eq_slope h h' hlt hcont
      (fun t ht => hderiv t ⟨le_of_lt ht.1, le_of_lt ht.2⟩)
    have hba : 0 < b - a := sub_pos.mpr hlt
    have hle : (h b - h a) / (b - a) ≤ 0 := by rw [← hslope]; exact hnonpos c hc
    have hsub : h b - h a ≤ 0 * (b - a) := (div_le_iff₀ hba).mp hle
    linarith

/-- **THEOREM 1 OF MILESTONE 7A (Differential Grönwall Inequality on `[0, T]`):**
    If `E'(t) ≤ α(t) E(t)` on `(0, T)` with continuous `α`, then
    `E(T) ≤ E(0) * exp(∫_0^T α(s) ds)` (`0 sorryAx`). -/
theorem gronwall_exp_integral_bound {E E' α : ℝ → ℝ} {T : ℝ} (hT : 0 ≤ T)
    (hα_cont : Continuous α)
    (hderiv : ∀ t ∈ Set.Icc (0 : ℝ) T, HasDerivAt E (E' t) t)
    (h_ineq : ∀ t ∈ Set.Ioo (0 : ℝ) T, E' t ≤ α t * E t) :
    E T ≤ E 0 * Real.exp (∫ s in (0 : ℝ)..T, α s) := by
  let A : ℝ → ℝ := fun t => ∫ s in (0 : ℝ)..t, α s
  let h : ℝ → ℝ := fun t => Real.exp (-A t) * E t
  let h' : ℝ → ℝ := fun t => Real.exp (-A t) * (E' t - α t * E t)
  have hA_deriv : ∀ t : ℝ, HasDerivAt A (α t) t := fun t =>
    intervalIntegral.integral_hasDerivAt_right
      (hα_cont.intervalIntegrable (μ := volume) 0 t)
      (hα_cont.stronglyMeasurable.stronglyMeasurableAtFilter)
      hα_cont.continuousAt
  have hh_deriv : ∀ t ∈ Set.Icc (0 : ℝ) T, HasDerivAt h (h' t) t := by
    intro t ht
    have hnegA : HasDerivAt (fun r => -A r) (-α t) t := (hA_deriv t).neg
    have hexp : HasDerivAt (fun r => Real.exp (-A r)) (Real.exp (-A t) * (-α t)) t :=
      hnegA.exp
    have hprod := hexp.mul (hderiv t ht)
    have hval : Real.exp (-A t) * (-α t) * E t + Real.exp (-A t) * E' t = h' t := by
      dsimp only [h']; ring
    rwa [hval] at hprod
  have hh_nonpos : ∀ t ∈ Set.Ioo (0 : ℝ) T, h' t ≤ 0 := fun t ht =>
    mul_nonpos_of_nonneg_of_nonpos (le_of_lt (Real.exp_pos _)) (by linarith [h_ineq t ht])
  have hle := le_of_hasDerivAt_nonpos_Icc hT hh_deriv hh_nonpos
  have h0 : h 0 = E 0 := by dsimp only [h, A]; simp
  rw [h0] at hle
  have hexp_pos : 0 < Real.exp (A T) := Real.exp_pos _
  have hmul := mul_le_mul_of_nonneg_right hle (le_of_lt hexp_pos)
  have hcancel : h T * Real.exp (A T) = E T := by
    dsimp only [h]
    calc Real.exp (-A T) * E T * Real.exp (A T)
        = (Real.exp (-A T) * Real.exp (A T)) * E T := by ring
      _ = Real.exp (-A T + A T) * E T := by rw [← Real.exp_add]
      _ = E T := by simp
  rw [hcancel] at hmul
  exact hmul

private noncomputable abbrev unitCube7 : Set (ℝ × (ℝ × ℝ)) :=
  Set.Icc (0 : ℝ) 1 ×ˢ (Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1)

private noncomputable abbrev unitMeas7 : Measure ℝ := volume.restrict (Set.Icc (0 : ℝ) 1)

private noncomputable abbrev unitMeas3_7 : Measure (ℝ × (ℝ × ℝ)) :=
  unitMeas7.prod (unitMeas7.prod unitMeas7)

private theorem unitMeas3_7_eq :
    unitMeas3_7 = (volume : Measure (ℝ × (ℝ × ℝ))).restrict unitCube7 := by
  unfold unitMeas3_7 unitMeas7 unitCube7
  rw [Measure.prod_restrict, Measure.prod_restrict]
  rfl

private theorem continuous_vec3_triple7 :
    Continuous (fun q : ℝ × (ℝ × ℝ) => vec3 q.1 q.2.1 q.2.2) :=
  continuous_pi fun i => match i with
    | ⟨0, _⟩ => continuous_fst
    | ⟨1, _⟩ => continuous_fst.comp continuous_snd
    | ⟨2, _⟩ => continuous_snd.comp continuous_snd

private theorem torusIntegral_eq_unitMeas3_7 {g : R3 → ℝ} (hg : Continuous g) :
    torusIntegral g = ∫ q : ℝ × (ℝ × ℝ), g (vec3 q.1 q.2.1 q.2.2) ∂unitMeas3_7 := by
  have hint1 : ∀ φ : ℝ → ℝ, ∫ t in (0 : ℝ)..1, φ t = ∫ t, φ t ∂unitMeas7 := fun φ => by
    rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1),
        ← MeasureTheory.integral_Icc_eq_integral_Ioc]
  unfold torusIntegral
  simp_rw [hint1]
  have h2 : ∀ x : ℝ, (∫ y, (∫ z, g (vec3 x y z) ∂unitMeas7) ∂unitMeas7) =
      ∫ p : ℝ × ℝ, g (vec3 x p.1 p.2) ∂(unitMeas7.prod unitMeas7) := by
    intro x
    have hprod : unitMeas7.prod unitMeas7 =
        (volume : Measure (ℝ × ℝ)).restrict (Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1) := by
      unfold unitMeas7; rw [Measure.prod_restrict]; rfl
    have hc : Continuous (fun p : ℝ × ℝ => g (vec3 x p.1 p.2)) :=
      hg.comp (continuous_pi fun i => match i with
        | ⟨0, _⟩ => continuous_const | ⟨1, _⟩ => continuous_fst | ⟨2, _⟩ => continuous_snd)
    have hint : Integrable (fun p : ℝ × ℝ => g (vec3 x p.1 p.2)) (unitMeas7.prod unitMeas7) := by
      rw [hprod]; exact hc.continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)
    exact (MeasureTheory.integral_prod (fun p : ℝ × ℝ => g (vec3 x p.1 p.2)) hint).symm
  simp_rw [h2]
  have hint3 : Integrable (fun q : ℝ × (ℝ × ℝ) => g (vec3 q.1 q.2.1 q.2.2)) unitMeas3_7 := by
    rw [unitMeas3_7_eq]
    exact (hg.comp continuous_vec3_triple7).continuousOn.integrableOn_compact
      (isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc))
  exact (MeasureTheory.integral_prod (fun q : ℝ × (ℝ × ℝ) => g (vec3 q.1 q.2.1 q.2.2)) hint3).symm

private theorem torusIntegral_le_on_cube {f g : R3 → ℝ} (hf : Continuous f) (hg : Continuous g)
    (hle : ∀ x ∈ Set.Icc (0 : ℝ) 1, ∀ y ∈ Set.Icc (0 : ℝ) 1, ∀ z ∈ Set.Icc (0 : ℝ) 1,
      f (vec3 x y z) ≤ g (vec3 x y z)) :
    torusIntegral f ≤ torusIntegral g := by
  rw [torusIntegral_eq_unitMeas3_7 hf, torusIntegral_eq_unitMeas3_7 hg]
  have hintf : Integrable (fun q : ℝ × (ℝ × ℝ) => f (vec3 q.1 q.2.1 q.2.2)) unitMeas3_7 := by
    rw [unitMeas3_7_eq]
    exact (hf.comp continuous_vec3_triple7).continuousOn.integrableOn_compact
      (isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc))
  have hintg : Integrable (fun q : ℝ × (ℝ × ℝ) => g (vec3 q.1 q.2.1 q.2.2)) unitMeas3_7 := by
    rw [unitMeas3_7_eq]
    exact (hg.comp continuous_vec3_triple7).continuousOn.integrableOn_compact
      (isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc))
  refine MeasureTheory.integral_mono_ae hintf hintg ?_
  rw [unitMeas3_7_eq]
  filter_upwards [ae_restrict_mem (measurableSet_Icc.prod (measurableSet_Icc.prod measurableSet_Icc))] with q hq
  exact hle q.1 hq.1 q.2.1 hq.2.1 q.2.2 hq.2.2

-- ============================================================================
-- SECTION 2: TRUE 3D BKM / VELOCITY-GRADIENT ENSTROPHY CONTINUATION ON `𝕋³`
-- ============================================================================

private lemma cs3_sq (a0 a1 a2 w0 w1 w2 : ℝ) :
    (w0 * a0 + w1 * a1 + w2 * a2) ^ 2 ≤ (a0 ^ 2 + a1 ^ 2 + a2 ^ 2) * (w0 ^ 2 + w1 ^ 2 + w2 ^ 2) := by
  nlinarith [sq_nonneg (a0 * w1 - a1 * w0), sq_nonneg (a0 * w2 - a2 * w0), sq_nonneg (a1 * w2 - a2 * w1)]

private lemma stretching_pointwise_cs (a00 a01 a02 a10 a11 a12 a20 a21 a22 w0 w1 w2 : ℝ) :
    ((w0 * a00 + w1 * a01 + w2 * a02) * w0 +
     (w0 * a10 + w1 * a11 + w2 * a12) * w1 +
     (w0 * a20 + w1 * a21 + w2 * a22) * w2) ^ 2 ≤
    (a00 ^ 2 + a01 ^ 2 + a02 ^ 2 + a10 ^ 2 + a11 ^ 2 + a12 ^ 2 + a20 ^ 2 + a21 ^ 2 + a22 ^ 2) *
    (w0 ^ 2 + w1 ^ 2 + w2 ^ 2) ^ 2 := by
  let b0 := w0 * a00 + w1 * a01 + w2 * a02
  let b1 := w0 * a10 + w1 * a11 + w2 * a12
  let b2 := w0 * a20 + w1 * a21 + w2 * a22
  have hb0 : b0 ^ 2 ≤ (a00 ^ 2 + a01 ^ 2 + a02 ^ 2) * (w0 ^ 2 + w1 ^ 2 + w2 ^ 2) :=
    cs3_sq a00 a01 a02 w0 w1 w2
  have hb1 : b1 ^ 2 ≤ (a10 ^ 2 + a11 ^ 2 + a12 ^ 2) * (w0 ^ 2 + w1 ^ 2 + w2 ^ 2) :=
    cs3_sq a10 a11 a12 w0 w1 w2
  have hb2 : b2 ^ 2 ≤ (a20 ^ 2 + a21 ^ 2 + a22 ^ 2) * (w0 ^ 2 + w1 ^ 2 + w2 ^ 2) :=
    cs3_sq a20 a21 a22 w0 w1 w2
  have hout : (b0 * w0 + b1 * w1 + b2 * w2) ^ 2 ≤
      (b0 ^ 2 + b1 ^ 2 + b2 ^ 2) * (w0 ^ 2 + w1 ^ 2 + w2 ^ 2) := by
    have h := cs3_sq b0 b1 b2 w0 w1 w2
    have hcomm : w0 * b0 + w1 * b1 + w2 * b2 = b0 * w0 + b1 * w1 + b2 * w2 := by ring
    rwa [hcomm] at h
  have hsum : b0 ^ 2 + b1 ^ 2 + b2 ^ 2 ≤
      (a00 ^ 2 + a01 ^ 2 + a02 ^ 2 + a10 ^ 2 + a11 ^ 2 + a12 ^ 2 + a20 ^ 2 + a21 ^ 2 + a22 ^ 2) *
      (w0 ^ 2 + w1 ^ 2 + w2 ^ 2) := by linarith
  have hw_nn : 0 ≤ w0 ^ 2 + w1 ^ 2 + w2 ^ 2 := by positivity
  have hmul := mul_le_mul_of_nonneg_right hsum hw_nn
  have heq : (a00 ^ 2 + a01 ^ 2 + a02 ^ 2 + a10 ^ 2 + a11 ^ 2 + a12 ^ 2 + a20 ^ 2 + a21 ^ 2 + a22 ^ 2) *
      (w0 ^ 2 + w1 ^ 2 + w2 ^ 2) * (w0 ^ 2 + w1 ^ 2 + w2 ^ 2) =
      (a00 ^ 2 + a01 ^ 2 + a02 ^ 2 + a10 ^ 2 + a11 ^ 2 + a12 ^ 2 + a20 ^ 2 + a21 ^ 2 + a22 ^ 2) *
      (w0 ^ 2 + w1 ^ 2 + w2 ^ 2) ^ 2 := by ring
  linarith

private lemma abs_directional_dot_le_of_grad_le {w v : R3 → R3} {x : R3} {G : ℝ}
    (hG : 0 ≤ G) (hgrad : gradNormSq3D v x ≤ G ^ 2) :
    |dot3D (fun c =>
      w x 0 * partialDerivScalar (fun y => v y c) x 0 +
      w x 1 * partialDerivScalar (fun y => v y c) x 1 +
      w x 2 * partialDerivScalar (fun y => v y c) x 2) (w x)| ≤
    G * dot3D (w x) (w x) := by
  have hcs := stretching_pointwise_cs
    (partialDerivScalar (fun y => v y 0) x 0) (partialDerivScalar (fun y => v y 0) x 1)
    (partialDerivScalar (fun y => v y 0) x 2) (partialDerivScalar (fun y => v y 1) x 0)
    (partialDerivScalar (fun y => v y 1) x 1) (partialDerivScalar (fun y => v y 1) x 2)
    (partialDerivScalar (fun y => v y 2) x 0) (partialDerivScalar (fun y => v y 2) x 1)
    (partialDerivScalar (fun y => v y 2) x 2) (w x 0) (w x 1) (w x 2)
  have hdot_w : dot3D (w x) (w x) = (w x 0) ^ 2 + (w x 1) ^ 2 + (w x 2) ^ 2 := by
    unfold dot3D; ring
  have hgrad_eq : gradNormSq3D v x =
      partialDerivScalar (fun y => v y 0) x 0 ^ 2 + partialDerivScalar (fun y => v y 0) x 1 ^ 2 +
      partialDerivScalar (fun y => v y 0) x 2 ^ 2 + partialDerivScalar (fun y => v y 1) x 0 ^ 2 +
      partialDerivScalar (fun y => v y 1) x 1 ^ 2 + partialDerivScalar (fun y => v y 1) x 2 ^ 2 +
      partialDerivScalar (fun y => v y 2) x 0 ^ 2 + partialDerivScalar (fun y => v y 2) x 1 ^ 2 +
      partialDerivScalar (fun y => v y 2) x 2 ^ 2 := by
    unfold gradNormSq3D; ring
  rw [← hgrad_eq, ← hdot_w] at hcs
  have hdot_lhs : dot3D (fun c =>
      w x 0 * partialDerivScalar (fun y => v y c) x 0 +
      w x 1 * partialDerivScalar (fun y => v y c) x 1 +
      w x 2 * partialDerivScalar (fun y => v y c) x 2) (w x) =
      (w x 0 * partialDerivScalar (fun y => v y 0) x 0 +
       w x 1 * partialDerivScalar (fun y => v y 0) x 1 +
       w x 2 * partialDerivScalar (fun y => v y 0) x 2) * w x 0 +
      (w x 0 * partialDerivScalar (fun y => v y 1) x 0 +
       w x 1 * partialDerivScalar (fun y => v y 1) x 1 +
       w x 2 * partialDerivScalar (fun y => v y 1) x 2) * w x 1 +
      (w x 0 * partialDerivScalar (fun y => v y 2) x 0 +
       w x 1 * partialDerivScalar (fun y => v y 2) x 1 +
       w x 2 * partialDerivScalar (fun y => v y 2) x 2) * w x 2 := by
    unfold dot3D; ring
  rw [hdot_lhs]
  have hsq_le : ((w x 0 * partialDerivScalar (fun y => v y 0) x 0 +
       w x 1 * partialDerivScalar (fun y => v y 0) x 1 +
       w x 2 * partialDerivScalar (fun y => v y 0) x 2) * w x 0 +
      (w x 0 * partialDerivScalar (fun y => v y 1) x 0 +
       w x 1 * partialDerivScalar (fun y => v y 1) x 1 +
       w x 2 * partialDerivScalar (fun y => v y 1) x 2) * w x 1 +
      (w x 0 * partialDerivScalar (fun y => v y 2) x 0 +
       w x 1 * partialDerivScalar (fun y => v y 2) x 1 +
       w x 2 * partialDerivScalar (fun y => v y 2) x 2) * w x 2) ^ 2 ≤
      (G * dot3D (w x) (w x)) ^ 2 := by
    have hmul := mul_le_mul_of_nonneg_right hgrad (sq_nonneg (dot3D (w x) (w x)))
    have hpow : G ^ 2 * dot3D (w x) (w x) ^ 2 = (G * dot3D (w x) (w x)) ^ 2 := by ring
    linarith
  have hrhs_nn : 0 ≤ G * dot3D (w x) (w x) := mul_nonneg hG (dot3D_self_nonneg _)
  rw [← sq_abs] at hsq_le
  nlinarith [abs_nonneg ((w x 0 * partialDerivScalar (fun y => v y 0) x 0 +
       w x 1 * partialDerivScalar (fun y => v y 0) x 1 +
       w x 2 * partialDerivScalar (fun y => v y 0) x 2) * w x 0 +
      (w x 0 * partialDerivScalar (fun y => v y 1) x 0 +
       w x 1 * partialDerivScalar (fun y => v y 1) x 1 +
       w x 2 * partialDerivScalar (fun y => v y 1) x 2) * w x 1 +
      (w x 0 * partialDerivScalar (fun y => v y 2) x 0 +
       w x 1 * partialDerivScalar (fun y => v y 2) x 1 +
       w x 2 * partialDerivScalar (fun y => v y 2) x 2) * w x 2)]

private lemma two_add_one_eq_three7 {α : Type*} [AddMonoidWithOne α] : (2 : α) + 1 = 3 := by
  rw [← Nat.cast_ofNat (n := 2), ← Nat.cast_one, ← Nat.cast_add]; exact Nat.cast_ofNat

private lemma contDiff_two_of_three7 {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {f : E → F} (hf : ContDiff ℝ 3 f) :
    ContDiff ℝ 2 f :=
  hf.of_le (by rw [← two_add_one_eq_three7]; exact le_self_add)

private lemma contDiff_one_of_three7 {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {f : E → F} (hf : ContDiff ℝ 3 f) :
    ContDiff ℝ 1 f :=
  (contDiff_two_of_three7 hf).of_le (by rw [← one_add_one_eq_two]; exact le_self_add)

/-- **THEOREM 2 OF MILESTONE 7A (True 3D BKM / Velocity-Gradient Enstrophy Continuation Bound on `𝕋³`):**
    For every periodic classical 3D Navier–Stokes solution `(u, p)` on `[0, T]`, if a continuous
    nonnegative envelope `G(t)` bounds `|∇u(t, x)| ≤ G(t)` on `[0, 1]³`, then enstrophy satisfies
    the exact viscous-damped Grönwall bound:
      `Z(T) ≤ Z(0) * exp(∫_0^T (2 G(s) - 16 ν) ds)` (`0 sorryAx`). -/
theorem bkm_gradient_enstrophy_continuation_torus3D
    {u : ℝ → R3 → R3} {p : ℝ → R3 → ℝ} {ν : ℝ}
    (hns : IsPeriodicClassicalNS3D_C3 u p ν) {T : ℝ} (hT : 0 ≤ T)
    {G : ℝ → ℝ} (hG_cont : Continuous G) (hG_nn : ∀ s ∈ Set.Icc (0 : ℝ) T, 0 ≤ G s)
    (hG_bound : ∀ s ∈ Set.Icc (0 : ℝ) T,
      ∀ x ∈ Set.Icc (0 : ℝ) 1, ∀ y ∈ Set.Icc (0 : ℝ) 1, ∀ z ∈ Set.Icc (0 : ℝ) 1,
        gradNormSq3D (u s) (vec3 x y z) ≤ (G s) ^ 2) :
    enstrophy u T ≤ enstrophy u 0 * Real.exp (∫ s in (0 : ℝ)..T, (2 * G s - 16 * ν)) := by
  refine gronwall_exp_integral_bound hT
    ((continuous_const.mul hG_cont).sub continuous_const)
    (fun s hs => (hasDerivAt_enstrophy_evolution_3D hns hs.1).1) fun s hs => ?_
  have hs_icc : s ∈ Set.Icc (0 : ℝ) T := ⟨le_of_lt hs.1, le_of_lt hs.2⟩
  have hu3 : ContDiff ℝ 3 (u s) := hns.h_u_c3_global s hs_icc.1
  have hu1 : ContDiff ℝ 1 (u s) := contDiff_one_of_three7 hu3
  have hw_cont : Continuous (curl3D (u s)) := (contDiff_two_curl3D hu3).continuous
  have hstr_cont : Continuous (fun x =>
      dot3D (directionalAdvection3D (curl3D (u s)) (u s) x) (curl3D (u s) x)) := by
    have hdir : Continuous (directionalAdvection3D (curl3D (u s)) (u s)) := by
      refine continuous_pi fun c => ?_
      unfold directionalAdvection3D
      exact ((((continuous_apply 0).comp hw_cont).mul
              (continuous_partialDerivScalar_of_contDiff (contDiff_pi.mp hu1 c) 0)).add
            (((continuous_apply 1).comp hw_cont).mul
              (continuous_partialDerivScalar_of_contDiff (contDiff_pi.mp hu1 c) 1))).add
            (((continuous_apply 2).comp hw_cont).mul
              (continuous_partialDerivScalar_of_contDiff (contDiff_pi.mp hu1 c) 2))
    exact continuous_dot3D hdir hw_cont
  have hstr_le : vortexStretching3D (u s) ≤ 2 * G s * enstrophy u s := by
    have hle_int : torusIntegral (fun x =>
          dot3D (directionalAdvection3D (curl3D (u s)) (u s) x) (curl3D (u s) x)) ≤
        torusIntegral (fun x => G s * dot3D (curl3D (u s) x) (curl3D (u s) x)) :=
      torusIntegral_le_on_cube hstr_cont (continuous_const.mul (continuous_dot3D hw_cont hw_cont))
        fun x hx y hy z hz => by
          have habs := abs_directional_dot_le_of_grad_le (w := curl3D (u s)) (v := u s)
            (hG_nn s hs_icc) (hG_bound s hs_icc x hx y hy z hz)
          exact le_trans (le_abs_self _) habs
    have hconst : torusIntegral (fun x => G s * dot3D (curl3D (u s) x) (curl3D (u s) x)) =
        G s * torusIntegral (fun x => dot3D (curl3D (u s) x) (curl3D (u s) x)) :=
      torusIntegral_const_mul (G s) (continuous_dot3D hw_cont hw_cont)
    unfold vortexStretching3D enstrophy
    linarith
  have hpoin := (analytical_lemma4_bernstein_poincare_vorticity hns hs_icc.1).2
  linarith

/-- **THEOREM 3 OF MILESTONE 7A (Abstract BKM Vorticity Envelope Continuation Bound on `𝕋³`):**
    Whenever the true 3D stretching integral obeys `S_stretch(s) ≤ C_bkm * Ω(s) * Z(s)` for a
    continuous vorticity envelope `Ω(s)` on `[0, T]`, enstrophy satisfies
      `Z(T) ≤ Z(0) * exp(∫_0^T (C_bkm * Ω(s) - 16 ν) ds)` (`0 sorryAx`). -/
theorem bkm_vorticity_envelope_continuation_torus3D
    {u : ℝ → R3 → R3} {p : ℝ → R3 → ℝ} {ν C_bkm : ℝ}
    (hns : IsPeriodicClassicalNS3D_C3 u p ν) {T : ℝ} (hT : 0 ≤ T)
    {Ω : ℝ → ℝ} (hΩ_cont : Continuous Ω)
    (h_bkm_stretch : ∀ s ∈ Set.Icc (0 : ℝ) T, vortexStretching3D (u s) ≤ C_bkm * Ω s * enstrophy u s) :
    enstrophy u T ≤ enstrophy u 0 * Real.exp (∫ s in (0 : ℝ)..T, (C_bkm * Ω s - 16 * ν)) := by
  refine gronwall_exp_integral_bound hT
    ((continuous_const.mul hΩ_cont).sub continuous_const)
    (fun s hs => (hasDerivAt_enstrophy_evolution_3D hns hs.1).1) fun s hs => ?_
  have hs_icc : s ∈ Set.Icc (0 : ℝ) T := ⟨le_of_lt hs.1, le_of_lt hs.2⟩
  have hpoin := (analytical_lemma4_bernstein_poincare_vorticity hns hs_icc.1).2
  linarith [h_bkm_stretch s hs_icc]

-- ============================================================================
-- SECTION 3: UNCONDITIONAL CLASSICAL 3D NAVIER–STOKES UNIQUENESS ON `𝕋³`
-- ============================================================================

private theorem partialDerivScalar_sub_7a {f g : R3 → ℝ} {x : R3}
    (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) (i : Fin 3) :
    partialDerivScalar (fun y => f y - g y) x i =
      partialDerivScalar f x i - partialDerivScalar g x i := by
  unfold partialDerivScalar
  have hsub : HasFDerivAt (fun y => f y - g y) (fderiv ℝ f x - fderiv ℝ g x) x :=
    hf.hasFDerivAt.sub hg.hasFDerivAt
  rw [hsub.fderiv]; simp

private theorem sndPartial_sub_7a {f g : R3 → ℝ} (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g)
    (x : R3) (i j : Fin 3) :
    sndPartial (fun y => f y - g y) x i j = sndPartial f x i j - sndPartial g x i j := by
  have hfg : ContDiff ℝ 2 (fun y => f y - g y) := hf.sub hg
  have hf1 : ContDiff ℝ 1 f := hf.of_le (by rw [← one_add_one_eq_two]; exact le_self_add)
  have hg1 : ContDiff ℝ 1 g := hg.of_le (by rw [← one_add_one_eq_two]; exact le_self_add)
  rw [← partial_partial_eq_sndPartial (fun y => f y - g y) x hfg.contDiffAt i j,
      ← partial_partial_eq_sndPartial f x hf.contDiffAt i j,
      ← partial_partial_eq_sndPartial g x hg.contDiffAt i j]
  have hfun : (fun y => partialDerivScalar (fun z => f z - g z) y j) =
      (fun y => partialDerivScalar f y j - partialDerivScalar g y j) :=
    funext fun y => partialDerivScalar_sub_7a
      (hf1.differentiable (by simp) y) (hg1.differentiable (by simp) y) j
  rw [hfun]
  exact partialDerivScalar_sub_7a
    ((contDiff_one_partialDerivScalar hf j).differentiable (by simp) x)
    ((contDiff_one_partialDerivScalar hg j).differentiable (by simp) x) i

private theorem torusIntegral_laplacian_dot_self_7a {w : R3 → R3}
    (hw : ContDiff ℝ 2 w) (hpw : IsPeriodic3D w) :
    torusIntegral (fun x => dot3D (laplacian3D w x) (w x)) =
      -torusIntegral (gradNormSq3D w) := by
  have hw1 : ContDiff ℝ 1 w := hw.of_le (by rw [← one_add_one_eq_two]; exact le_self_add)
  have hcomp_axis : ∀ (c i : Fin 3),
      torusIntegral (fun x => sndPartial (fun y => w y c) x i i * w x c) =
        -torusIntegral (fun x => (partialDerivScalar (fun y => w y c) x i) ^ 2) := by
    intro c i
    have hwc2 : ContDiff ℝ 2 (fun y => w y c) := contDiff_pi.mp hw c
    have hwc1 : ContDiff ℝ 1 (fun y => w y c) := contDiff_pi.mp hw1 c
    have hpwc : IsPeriodic3D (fun y => w y c) := fun x j => congrArg (fun v => v c) (hpw x j)
    have hgi : ContDiff ℝ 1 (fun y => partialDerivScalar (fun z => w z c) y i) :=
      contDiff_one_partialDerivScalar hwc2 i
    have hpgi : IsPeriodic3D (fun y => partialDerivScalar (fun z => w z c) y i) :=
      IsPeriodic3D.partialDeriv hpwc (hwc1.differentiable (by simp)) i
    have hpt : ∀ x : R3, sndPartial (fun y => w y c) x i i * w x c =
        w x c * partialDerivScalar (fun y => partialDerivScalar (fun z => w z c) y i) x i :=
      fun x => by
        rw [← partial_partial_eq_sndPartial (fun y => w y c) x hwc2.contDiffAt i i, mul_comm]
    have hibp := torusIntegral_ibp hwc1 hgi hpwc hpgi i
    have hpt2 : ∀ x : R3,
        partialDerivScalar (fun y => w y c) x i * partialDerivScalar (fun z => w z c) x i =
        (partialDerivScalar (fun y => w y c) x i) ^ 2 := fun x => by ring
    rw [torusIntegral_congr hpt, hibp, torusIntegral_congr hpt2]
  have hcomp : ∀ c : Fin 3,
      torusIntegral (fun x => laplacianScalar (fun y => w y c) x * w x c) =
        -(torusIntegral (fun x => (partialDerivScalar (fun y => w y c) x 0) ^ 2) +
          torusIntegral (fun x => (partialDerivScalar (fun y => w y c) x 1) ^ 2) +
          torusIntegral (fun x => (partialDerivScalar (fun y => w y c) x 2) ^ 2)) := by
    intro c
    have hwc2 : ContDiff ℝ 2 (fun y => w y c) := contDiff_pi.mp hw c
    have hsnd : ∀ i : Fin 3, Continuous (fun x => sndPartial (fun y => w y c) x i i * w x c) :=
      fun i => (continuous_sndPartial_of_contDiff hwc2 i i).mul hwc2.continuous
    have hpt : ∀ x : R3, laplacianScalar (fun y => w y c) x * w x c =
        sndPartial (fun y => w y c) x 0 0 * w x c +
        sndPartial (fun y => w y c) x 1 1 * w x c +
        sndPartial (fun y => w y c) x 2 2 * w x c := fun x => by unfold laplacianScalar; ring
    rw [torusIntegral_congr hpt, torusIntegral_add3 (hsnd 0) (hsnd 1) (hsnd 2),
        hcomp_axis c 0, hcomp_axis c 1, hcomp_axis c 2]
    ring
  have hc_lap : ∀ c : Fin 3, Continuous (fun x => laplacianScalar (fun y => w y c) x * w x c) :=
    fun c => ((continuous_apply c).comp (continuous_laplacian3D hw)).mul ((continuous_apply c).comp hw.continuous)
  have hpt_dot : ∀ x : R3, dot3D (laplacian3D w x) (w x) =
      laplacianScalar (fun y => w y 0) x * w x 0 +
      laplacianScalar (fun y => w y 1) x * w x 1 +
      laplacianScalar (fun y => w y 2) x * w x 2 := fun x => by unfold dot3D laplacian3D; rfl
  have hp : ∀ c i : Fin 3, Continuous (fun x => (partialDerivScalar (fun y => w y c) x i) ^ 2) :=
    fun c i => (continuous_partialDerivScalar_of_contDiff (contDiff_pi.mp hw1 c) i).pow 2
  have hq : ∀ c : Fin 3, Continuous (fun x =>
      (partialDerivScalar (fun y => w y c) x 0) ^ 2 +
      (partialDerivScalar (fun y => w y c) x 1) ^ 2 +
      (partialDerivScalar (fun y => w y c) x 2) ^ 2) :=
    fun c => ((hp c 0).add (hp c 1)).add (hp c 2)
  have hgrad_split : torusIntegral (gradNormSq3D w) =
      (torusIntegral (fun x => (partialDerivScalar (fun y => w y 0) x 0) ^ 2) +
       torusIntegral (fun x => (partialDerivScalar (fun y => w y 0) x 1) ^ 2) +
       torusIntegral (fun x => (partialDerivScalar (fun y => w y 0) x 2) ^ 2)) +
      (torusIntegral (fun x => (partialDerivScalar (fun y => w y 1) x 0) ^ 2) +
       torusIntegral (fun x => (partialDerivScalar (fun y => w y 1) x 1) ^ 2) +
       torusIntegral (fun x => (partialDerivScalar (fun y => w y 1) x 2) ^ 2)) +
      (torusIntegral (fun x => (partialDerivScalar (fun y => w y 2) x 0) ^ 2) +
       torusIntegral (fun x => (partialDerivScalar (fun y => w y 2) x 1) ^ 2) +
       torusIntegral (fun x => (partialDerivScalar (fun y => w y 2) x 2) ^ 2)) := by
    have hpt : ∀ x : R3, gradNormSq3D w x =
        ((partialDerivScalar (fun y => w y 0) x 0) ^ 2 +
         (partialDerivScalar (fun y => w y 0) x 1) ^ 2 +
         (partialDerivScalar (fun y => w y 0) x 2) ^ 2) +
        ((partialDerivScalar (fun y => w y 1) x 0) ^ 2 +
         (partialDerivScalar (fun y => w y 1) x 1) ^ 2 +
         (partialDerivScalar (fun y => w y 1) x 2) ^ 2) +
        ((partialDerivScalar (fun y => w y 2) x 0) ^ 2 +
         (partialDerivScalar (fun y => w y 2) x 1) ^ 2 +
         (partialDerivScalar (fun y => w y 2) x 2) ^ 2) := fun x => by unfold gradNormSq3D; ring
    rw [torusIntegral_congr hpt, torusIntegral_add3 (hq 0) (hq 1) (hq 2),
        torusIntegral_add3 (hp 0 0) (hp 0 1) (hp 0 2),
        torusIntegral_add3 (hp 1 0) (hp 1 1) (hp 1 2),
        torusIntegral_add3 (hp 2 0) (hp 2 1) (hp 2 2)]
  rw [torusIntegral_congr hpt_dot, torusIntegral_add3 (hc_lap 0) (hc_lap 1) (hc_lap 2),
      hcomp 0, hcomp 1, hcomp 2, hgrad_split]
  ring

private theorem torusIntegral_grad_dot_solenoidal_zero_7a {r : R3 → ℝ} {w : R3 → R3}
    (hr : ContDiff ℝ 1 r) (hw : ContDiff ℝ 1 w) (hpr : IsPeriodic3D r) (hpw : IsPeriodic3D w)
    (hdiv : ∀ x : R3, div3D w x = 0) :
    torusIntegral (fun x => dot3D (grad3D r x) (w x)) = 0 := by
  have hc : ∀ c : Fin 3, Continuous (fun x => partialDerivScalar r x c * w x c) := fun c =>
    (continuous_partialDerivScalar_of_contDiff hr c).mul ((continuous_apply c).comp hw.continuous)
  have hpt : ∀ x : R3, dot3D (grad3D r x) (w x) =
      partialDerivScalar r x 0 * w x 0 +
      partialDerivScalar r x 1 * w x 1 +
      partialDerivScalar r x 2 * w x 2 := fun x => by unfold dot3D grad3D; rfl
  have hpwc : ∀ c : Fin 3, IsPeriodic3D (fun y => w y c) :=
    fun c x j => congrArg (fun v => v c) (hpw x j)
  have hibp0 := torusIntegral_ibp hr (contDiff_pi.mp hw 0) hpr (hpwc 0) 0
  have hibp1 := torusIntegral_ibp hr (contDiff_pi.mp hw 1) hpr (hpwc 1) 1
  have hibp2 := torusIntegral_ibp hr (contDiff_pi.mp hw 2) hpr (hpwc 2) 2
  have hrc : ∀ c : Fin 3, Continuous (fun x => r x * partialDerivScalar (fun y => w y c) x c) :=
    fun c => hr.continuous.mul (continuous_partialDerivScalar_of_contDiff (contDiff_pi.mp hw c) c)
  have hsum : torusIntegral (fun x => r x * partialDerivScalar (fun y => w y 0) x 0) +
      torusIntegral (fun x => r x * partialDerivScalar (fun y => w y 1) x 1) +
      torusIntegral (fun x => r x * partialDerivScalar (fun y => w y 2) x 2) = 0 := by
    rw [← torusIntegral_add3 (hrc 0) (hrc 1) (hrc 2)]
    have hz : ∀ x : R3,
        r x * partialDerivScalar (fun y => w y 0) x 0 +
        r x * partialDerivScalar (fun y => w y 1) x 1 +
        r x * partialDerivScalar (fun y => w y 2) x 2 = 0 := fun x => by
      have hfac : r x * partialDerivScalar (fun y => w y 0) x 0 +
          r x * partialDerivScalar (fun y => w y 1) x 1 +
          r x * partialDerivScalar (fun y => w y 2) x 2 = r x * div3D w x := by unfold div3D; ring
      rw [hfac, hdiv x, mul_zero]
    rw [torusIntegral_congr hz]; unfold torusIntegral; simp
  rw [torusIntegral_congr hpt, torusIntegral_add3 (hc 0) (hc 1) (hc 2)]
  linarith

private theorem torusIntegral_transport_diff_zero_7a {u w : R3 → R3}
    (hu : ContDiff ℝ 1 u) (hw : ContDiff ℝ 1 w) (hpu : IsPeriodic3D u) (hpw : IsPeriodic3D w)
    (hdiv : ∀ x : R3, div3D u x = 0) :
    torusIntegral (fun x => dot3D (fun c =>
      u x 0 * partialDerivScalar (fun y => w y c) x 0 +
      u x 1 * partialDerivScalar (fun y => w y c) x 1 +
      u x 2 * partialDerivScalar (fun y => w y c) x 2) (w x)) = 0 := by
  let q : R3 → ℝ := fun y => (1 / 2 : ℝ) * dot3D (w y) (w y)
  have hq_c1 : ContDiff ℝ 1 q := by
    unfold q dot3D
    exact contDiff_const.mul
      ((((contDiff_pi.mp hw 0).mul (contDiff_pi.mp hw 0)).add
        ((contDiff_pi.mp hw 1).mul (contDiff_pi.mp hw 1))).add
       ((contDiff_pi.mp hw 2).mul (contDiff_pi.mp hw 2)))
  let F : R3 → R3 := fun y i => u y i * q y
  have hF_c1 : ContDiff ℝ 1 F := contDiff_pi.mpr fun i => (contDiff_pi.mp hu i).mul hq_c1
  have hF_per : IsPeriodic3D F := fun x j => by
    funext i; dsimp only [F, q]; rw [hpu x j, hpw x j]
  have hpt : ∀ x : R3, dot3D (fun c =>
      u x 0 * partialDerivScalar (fun y => w y c) x 0 +
      u x 1 * partialDerivScalar (fun y => w y c) x 1 +
      u x 2 * partialDerivScalar (fun y => w y c) x 2) (w x) = div3D F x := by
    intro x
    have hdu : ∀ i : Fin 3, DifferentiableAt ℝ (fun y => u y i) x :=
      fun i => (contDiff_pi.mp hu i).differentiable (by simp) x
    have hdw : ∀ c : Fin 3, DifferentiableAt ℝ (fun y => w y c) x :=
      fun c => (contDiff_pi.mp hw c).differentiable (by simp) x
    have hdq : DifferentiableAt ℝ q x := hq_c1.differentiable (by simp) x
    have hq_deriv : ∀ i : Fin 3, partialDerivScalar q x i =
        w x 0 * partialDerivScalar (fun y => w y 0) x i +
        w x 1 * partialDerivScalar (fun y => w y 1) x i +
        w x 2 * partialDerivScalar (fun y => w y 2) x i := by
      intro i
      unfold partialDerivScalar
      have h0 : HasFDerivAt (fun y => w y 0 * w y 0)
          (w x 0 • fderiv ℝ (fun y => w y 0) x + w x 0 • fderiv ℝ (fun y => w y 0) x) x :=
        (hdw 0).hasFDerivAt.mul (hdw 0).hasFDerivAt
      have h1 : HasFDerivAt (fun y => w y 1 * w y 1)
          (w x 1 • fderiv ℝ (fun y => w y 1) x + w x 1 • fderiv ℝ (fun y => w y 1) x) x :=
        (hdw 1).hasFDerivAt.mul (hdw 1).hasFDerivAt
      have h2 : HasFDerivAt (fun y => w y 2 * w y 2)
          (w x 2 • fderiv ℝ (fun y => w y 2) x + w x 2 • fderiv ℝ (fun y => w y 2) x) x :=
        (hdw 2).hasFDerivAt.mul (hdw 2).hasFDerivAt
      have hsum : HasFDerivAt q
          ((1 / 2 : ℝ) •
            ((w x 0 • fderiv ℝ (fun y => w y 0) x + w x 0 • fderiv ℝ (fun y => w y 0) x) +
             (w x 1 • fderiv ℝ (fun y => w y 1) x + w x 1 • fderiv ℝ (fun y => w y 1) x) +
             (w x 2 • fderiv ℝ (fun y => w y 2) x + w x 2 • fderiv ℝ (fun y => w y 2) x))) x :=
        ((h0.add h1).add h2).const_mul (1 / 2 : ℝ)
      rw [hsum.fderiv]
      simp [smul_eq_mul]
      ring
    have hdivF : div3D F x =
        div3D u x * q x +
        (u x 0 * partialDerivScalar q x 0 + u x 1 * partialDerivScalar q x 1 +
         u x 2 * partialDerivScalar q x 2) := by
      unfold div3D
      change partialDerivScalar (fun y => u y 0 * q y) x 0 +
             partialDerivScalar (fun y => u y 1 * q y) x 1 +
             partialDerivScalar (fun y => u y 2 * q y) x 2 = _
      rw [partialDerivScalar_mul (hdu 0) hdq 0,
          partialDerivScalar_mul (hdu 1) hdq 1,
          partialDerivScalar_mul (hdu 2) hdq 2]
      ring
    rw [hdivF, hdiv x, zero_mul, zero_add, hq_deriv 0, hq_deriv 1, hq_deriv 2]
    unfold dot3D; ring
  rw [torusIntegral_congr hpt]
  exact torusIntegral_div3D_eq_zero hF_c1 hF_per

private theorem diff_energy_hasDerivAt_7a
    {u v : ℝ → R3 → R3} {p q : ℝ → R3 → ℝ} {ν : ℝ}
    (hu : IsPeriodicClassicalNS3D_C3 u p ν) (hv : IsPeriodicClassicalNS3D_C3 v q ν) (t : ℝ) :
    HasDerivAt (fun s => (1 / 2 : ℝ) * torusIntegral (fun y =>
        dot3D (fun c => u s y c - v s y c) (fun c => u s y c - v s y c)))
      (torusIntegral (fun y =>
        dot3D (fun c => deriv (fun s => u s y c - v s y c) t) (fun c => u t y c - v t y c))) t := by
  let w : ℝ → R3 → R3 := fun s y c => u s y c - v s y c
  have hw_st : ∀ z : ℝ × R3, ContDiffAt ℝ 2 (fun s : ℝ × R3 => w s.1 s.2) z :=
    fun z => (hu.h_u_c2_spacetime z).sub (hv.h_u_c2_spacetime z)
  have hw_cont : Continuous (fun z : ℝ × R3 => w z.1 z.2) :=
    (contDiff_iff_contDiffAt.mpr hw_st).continuous
  have hwt_cont : ∀ c : Fin 3, Continuous (fun z : ℝ × R3 => deriv (fun s => w s z.2 c) z.1) := by
    intro c
    have hFc : ∀ z : ℝ × R3, ContDiffAt ℝ 2 (fun s : ℝ × R3 => w s.1 s.2 c) z :=
      fun z => contDiffAt_pi.mp (hw_st z) c
    have hfun : (fun z : ℝ × R3 => deriv (fun s => w s z.2 c) z.1) =
        (fun z : ℝ × R3 => fderiv ℝ (fun s : ℝ × R3 => w s.1 s.2 c) z ((1 : ℝ), (0 : R3))) :=
      funext fun z => timeDeriv_eq_fderiv_prod (fun s => w s.1 s.2 c) hFc z.1 z.2
    rw [hfun]
    have hcd1 : ContDiff ℝ 1 (fderiv ℝ (fun s : ℝ × R3 => w s.1 s.2 c)) :=
      (contDiff_iff_contDiffAt.mpr hFc).fderiv_right (by simp [one_add_one_eq_two])
    exact (ContinuousLinearMap.apply ℝ ℝ ((1 : ℝ), (0 : R3))).continuous.comp hcd1.continuous
  have hderiv_w : ∀ (s : ℝ) (y : R3) (c : Fin 3),
      HasDerivAt (fun r => w r y c) (deriv (fun r => w r y c) s) s := by
    intro s y c
    have hFc : ∀ z : ℝ × R3, ContDiffAt ℝ 2 (fun r : ℝ × R3 => w r.1 r.2 c) z :=
      fun z => contDiffAt_pi.mp (hw_st z) c
    have h1 : ContDiffAt ℝ 1 (fun r : ℝ × R3 => w r.1 r.2 c) (s, y) :=
      (hFc (s, y)).of_le (by rw [← one_add_one_eq_two]; exact le_self_add)
    have hd := (h1.differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt s
      ((hasDerivAt_id s).prodMk (hasDerivAt_const s y))
    rwa [← timeDeriv_eq_fderiv_prod (fun r => w r.1 r.2 c) hFc s y] at hd
  have hw0 : Continuous (fun z : ℝ × R3 => w z.1 z.2 0) := (continuous_apply 0).comp hw_cont
  have hw1 : Continuous (fun z : ℝ × R3 => w z.1 z.2 1) := (continuous_apply 1).comp hw_cont
  have hw2 : Continuous (fun z : ℝ × R3 => w z.1 z.2 2) := (continuous_apply 2).comp hw_cont
  have hF : Continuous (fun z : ℝ × R3 => (1 / 2 : ℝ) * dot3D (w z.1 z.2) (w z.1 z.2)) := by
    unfold dot3D; exact continuous_const.mul (((hw0.mul hw0).add (hw1.mul hw1)).add (hw2.mul hw2))
  have hF' : Continuous (fun z : ℝ × R3 => dot3D (fun c => deriv (fun s => w s z.2 c) z.1) (w z.1 z.2)) := by
    unfold dot3D; exact (((hwt_cont 0).mul hw0).add ((hwt_cont 1).mul hw1)).add ((hwt_cont 2).mul hw2)
  have hleib := hasDerivAt_torusIntegral_of_continuous hF hF'
    (fun s y => hasDerivAt_half_dot3D_self
      (w := fun r => w r y) (w' := fun c => deriv (fun r => w r y c) s)
      (hderiv_w s y 0) (hderiv_w s y 1) (hderiv_w s y 2)) t
  have hE_eq : (fun s => (1 / 2 : ℝ) * torusIntegral (fun y => dot3D (w s y) (w s y))) =
      (fun s => torusIntegral (fun y => (1 / 2 : ℝ) * dot3D (w s y) (w s y))) := by
    funext s
    have hcs : Continuous (w s) := hw_cont.comp (continuous_const.prodMk continuous_id)
    exact (torusIntegral_const_mul (1 / 2 : ℝ) (continuous_dot3D hcs hcs)).symm
  rwa [← hE_eq] at hleib

private theorem diff_energy_deriv_le_7a
    {u v : ℝ → R3 → R3} {p q : ℝ → R3 → ℝ} {ν G t : ℝ}
    (hu : IsPeriodicClassicalNS3D_C3 u p ν) (hv : IsPeriodicClassicalNS3D_C3 v q ν)
    (ht : 0 ≤ t) (hG : 0 ≤ G)
    (hgrad_bd : ∀ a ∈ Set.Icc (0 : ℝ) 1, ∀ b ∈ Set.Icc (0 : ℝ) 1, ∀ d ∈ Set.Icc (0 : ℝ) 1,
      gradNormSq3D (v t) (vec3 a b d) ≤ G ^ 2) :
    torusIntegral (fun y =>
        dot3D (fun c => deriv (fun s => u s y c - v s y c) t) (fun c => u t y c - v t y c)) ≤
      (2 * G) * ((1 / 2 : ℝ) * torusIntegral (fun y =>
        dot3D (fun c => u t y c - v t y c) (fun c => u t y c - v t y c))) := by
  let wt : R3 → R3 := fun y c => u t y c - v t y c
  let rt : R3 → ℝ := fun y => p t y - q t y
  have hu2 : ContDiff ℝ 2 (u t) := contDiff_two_of_three7 (hu.h_u_c3_global t ht)
  have hv2 : ContDiff ℝ 2 (v t) := contDiff_two_of_three7 (hv.h_u_c3_global t ht)
  have hu1 : ContDiff ℝ 1 (u t) := contDiff_one_of_three7 (hu.h_u_c3_global t ht)
  have hv1 : ContDiff ℝ 1 (v t) := contDiff_one_of_three7 (hv.h_u_c3_global t ht)
  have hw2 : ContDiff ℝ 2 wt := hu2.sub hv2
  have hw1 : ContDiff ℝ 1 wt := hw2.of_le (by rw [← one_add_one_eq_two]; exact le_self_add)
  have hr1 : ContDiff ℝ 1 rt :=
    ((hu.h_p_c2_global t ht).sub (hv.h_p_c2_global t ht)).of_le
      (by rw [← one_add_one_eq_two]; exact le_self_add)
  have hpw : IsPeriodic3D wt := fun y i => by
    funext c; dsimp only [wt]; rw [hu.h_u_periodic t ht y i, hv.h_u_periodic t ht y i]
  have hpr : IsPeriodic3D rt := fun y i => by
    dsimp only [rt]; rw [hu.h_p_periodic t ht y i, hv.h_p_periodic t ht y i]
  have hdiv_w : ∀ y : R3, div3D wt y = 0 := by
    intro y; unfold div3D
    rw [partialDerivScalar_sub_7a ((contDiff_pi.mp hu1 0).differentiable (by simp) y)
          ((contDiff_pi.mp hv1 0).differentiable (by simp) y) 0,
        partialDerivScalar_sub_7a ((contDiff_pi.mp hu1 1).differentiable (by simp) y)
          ((contDiff_pi.mp hv1 1).differentiable (by simp) y) 1,
        partialDerivScalar_sub_7a ((contDiff_pi.mp hu1 2).differentiable (by simp) y)
          ((contDiff_pi.mp hv1 2).differentiable (by simp) y) 2]
    have hdu := hu.h_incompressible t ht y
    have hdv := hv.h_incompressible t ht y
    unfold div3D at hdu hdv; linarith
  have hpt_diff : ∀ y : R3, dot3D (fun c => deriv (fun s => u s y c - v s y c) t) (wt y) =
      ν * dot3D (laplacian3D wt y) (wt y) -
      dot3D (fun c =>
        u t y 0 * partialDerivScalar (fun z => wt z c) y 0 +
        u t y 1 * partialDerivScalar (fun z => wt z c) y 1 +
        u t y 2 * partialDerivScalar (fun z => wt z c) y 2) (wt y) -
      dot3D (fun c =>
        wt y 0 * partialDerivScalar (fun z => v t z c) y 0 +
        wt y 1 * partialDerivScalar (fun z => v t z c) y 1 +
        wt y 2 * partialDerivScalar (fun z => v t z c) y 2) (wt y) -
      dot3D (grad3D rt y) (wt y) := by
    intro y
    have hcomp : ∀ c : Fin 3, deriv (fun s => u s y c - v s y c) t =
        ν * laplacian3D wt y c -
        (u t y 0 * partialDerivScalar (fun z => wt z c) y 0 +
         u t y 1 * partialDerivScalar (fun z => wt z c) y 1 +
         u t y 2 * partialDerivScalar (fun z => wt z c) y 2) -
        (wt y 0 * partialDerivScalar (fun z => v t z c) y 0 +
         wt y 1 * partialDerivScalar (fun z => v t z c) y 1 +
         wt y 2 * partialDerivScalar (fun z => v t z c) y 2) -
        grad3D rt y c := by
      intro c
      have hdu_t : HasDerivAt (fun s => u s y c) (deriv (fun s => u s y c) t) t := by
        have hFc : ∀ z : ℝ × R3, ContDiffAt ℝ 2 (fun s : ℝ × R3 => u s.1 s.2 c) z :=
          fun z => contDiffAt_pi.mp (hu.h_u_c2_spacetime z) c
        have h1 : ContDiffAt ℝ 1 (fun s : ℝ × R3 => u s.1 s.2 c) (t, y) :=
          (hFc (t, y)).of_le (by rw [← one_add_one_eq_two]; exact le_self_add)
        have hd := (h1.differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt t
          ((hasDerivAt_id t).prodMk (hasDerivAt_const t y))
        rwa [← timeDeriv_eq_fderiv_prod (fun s => u s.1 s.2 c) hFc t y] at hd
      have hdv_t : HasDerivAt (fun s => v s y c) (deriv (fun s => v s y c) t) t := by
        have hFc : ∀ z : ℝ × R3, ContDiffAt ℝ 2 (fun s : ℝ × R3 => v s.1 s.2 c) z :=
          fun z => contDiffAt_pi.mp (hv.h_u_c2_spacetime z) c
        have h1 : ContDiffAt ℝ 1 (fun s : ℝ × R3 => v s.1 s.2 c) (t, y) :=
          (hFc (t, y)).of_le (by rw [← one_add_one_eq_two]; exact le_self_add)
        have hd := (h1.differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt t
          ((hasDerivAt_id t).prodMk (hasDerivAt_const t y))
        rwa [← timeDeriv_eq_fderiv_prod (fun s => v s.1 s.2 c) hFc t y] at hd
      have hdw_t : deriv (fun s => u s y c - v s y c) t =
          deriv (fun s => u s y c) t - deriv (fun s => v s y c) t :=
        (hdu_t.sub hdv_t).deriv
      have hlap_eq : laplacian3D wt y c = laplacian3D (u t) y c - laplacian3D (v t) y c := by
        unfold laplacian3D laplacianScalar
        rw [sndPartial_sub_7a (contDiff_pi.mp hu2 c) (contDiff_pi.mp hv2 c) y 0 0,
            sndPartial_sub_7a (contDiff_pi.mp hu2 c) (contDiff_pi.mp hv2 c) y 1 1,
            sndPartial_sub_7a (contDiff_pi.mp hu2 c) (contDiff_pi.mp hv2 c) y 2 2]
        ring
      have hp1 : ContDiff ℝ 1 (p t) :=
        (hu.h_p_c2_global t ht).of_le (by rw [← one_add_one_eq_two]; exact le_self_add)
      have hq1 : ContDiff ℝ 1 (q t) :=
        (hv.h_p_c2_global t ht).of_le (by rw [← one_add_one_eq_two]; exact le_self_add)
      have hgp_eq : grad3D rt y c = grad3D (p t) y c - grad3D (q t) y c := by
        unfold grad3D
        exact partialDerivScalar_sub_7a (hp1.differentiable (by simp) y) (hq1.differentiable (by simp) y) c
      have hadv_eq : advection3D (u t) y c - advection3D (v t) y c =
          (u t y 0 * partialDerivScalar (fun z => wt z c) y 0 +
           u t y 1 * partialDerivScalar (fun z => wt z c) y 1 +
           u t y 2 * partialDerivScalar (fun z => wt z c) y 2) +
          (wt y 0 * partialDerivScalar (fun z => v t z c) y 0 +
           wt y 1 * partialDerivScalar (fun z => v t z c) y 1 +
           wt y 2 * partialDerivScalar (fun z => v t z c) y 2) := by
        unfold advection3D
        rw [partialDerivScalar_sub_7a ((contDiff_pi.mp hu1 c).differentiable (by simp) y)
              ((contDiff_pi.mp hv1 c).differentiable (by simp) y) 0,
            partialDerivScalar_sub_7a ((contDiff_pi.mp hu1 c).differentiable (by simp) y)
              ((contDiff_pi.mp hv1 c).differentiable (by simp) y) 1,
            partialDerivScalar_sub_7a ((contDiff_pi.mp hu1 c).differentiable (by simp) y)
              ((contDiff_pi.mp hv1 c).differentiable (by simp) y) 2]
        dsimp only [wt]; ring
      have hmu := hu.h_momentum t ht y c
      have hmv := hv.h_momentum t ht y c
      have hlin : deriv (fun s => u s y c) t - deriv (fun s => v s y c) t =
          ν * (laplacian3D (u t) y c - laplacian3D (v t) y c) -
          (advection3D (u t) y c - advection3D (v t) y c) -
          (grad3D (p t) y c - grad3D (q t) y c) := by linarith
      rw [hdw_t, hlin, ← hlap_eq, ← hgp_eq, hadv_eq]
      ring
    unfold dot3D; dsimp only
    rw [hcomp 0, hcomp 1, hcomp 2]
    ring
  have hc_lap : Continuous (fun y => dot3D (laplacian3D wt y) (wt y)) :=
    continuous_dot3D (continuous_laplacian3D hw2) hw2.continuous
  have hc_tr1 : Continuous (fun y => dot3D (fun c =>
      u t y 0 * partialDerivScalar (fun z => wt z c) y 0 +
      u t y 1 * partialDerivScalar (fun z => wt z c) y 1 +
      u t y 2 * partialDerivScalar (fun z => wt z c) y 2) (wt y)) := by
    refine continuous_dot3D (continuous_pi fun c => ?_) hw2.continuous
    exact ((((continuous_apply 0).comp hu1.continuous).mul
            (continuous_partialDerivScalar_of_contDiff (contDiff_pi.mp hw1 c) 0)).add
          (((continuous_apply 1).comp hu1.continuous).mul
            (continuous_partialDerivScalar_of_contDiff (contDiff_pi.mp hw1 c) 1))).add
          (((continuous_apply 2).comp hu1.continuous).mul
            (continuous_partialDerivScalar_of_contDiff (contDiff_pi.mp hw1 c) 2))
  have hc_tr2 : Continuous (fun y => dot3D (fun c =>
      wt y 0 * partialDerivScalar (fun z => v t z c) y 0 +
      wt y 1 * partialDerivScalar (fun z => v t z c) y 1 +
      wt y 2 * partialDerivScalar (fun z => v t z c) y 2) (wt y)) := by
    refine continuous_dot3D (continuous_pi fun c => ?_) hw2.continuous
    exact ((((continuous_apply 0).comp hw1.continuous).mul
            (continuous_partialDerivScalar_of_contDiff (contDiff_pi.mp hv1 c) 0)).add
          (((continuous_apply 1).comp hw1.continuous).mul
            (continuous_partialDerivScalar_of_contDiff (contDiff_pi.mp hv1 c) 1))).add
          (((continuous_apply 2).comp hw1.continuous).mul
            (continuous_partialDerivScalar_of_contDiff (contDiff_pi.mp hv1 c) 2))
  have hc_gp : Continuous (fun y => dot3D (grad3D rt y) (wt y)) :=
    continuous_dot3D (continuous_grad3D hr1) hw2.continuous
  have hc_nu_lap : Continuous (fun y => ν * dot3D (laplacian3D wt y) (wt y)) :=
    continuous_const.mul hc_lap
  have hc_s1 : Continuous (fun y => ν * dot3D (laplacian3D wt y) (wt y) -
      dot3D (fun c =>
        u t y 0 * partialDerivScalar (fun z => wt z c) y 0 +
        u t y 1 * partialDerivScalar (fun z => wt z c) y 1 +
        u t y 2 * partialDerivScalar (fun z => wt z c) y 2) (wt y)) := hc_nu_lap.sub hc_tr1
  have hc_s2 : Continuous (fun y => ν * dot3D (laplacian3D wt y) (wt y) -
      dot3D (fun c =>
        u t y 0 * partialDerivScalar (fun z => wt z c) y 0 +
        u t y 1 * partialDerivScalar (fun z => wt z c) y 1 +
        u t y 2 * partialDerivScalar (fun z => wt z c) y 2) (wt y) -
      dot3D (fun c =>
        wt y 0 * partialDerivScalar (fun z => v t z c) y 0 +
        wt y 1 * partialDerivScalar (fun z => v t z c) y 1 +
        wt y 2 * partialDerivScalar (fun z => v t z c) y 2) (wt y)) := hc_s1.sub hc_tr2
  rw [torusIntegral_congr hpt_diff,
      torusIntegral_sub hc_s2 hc_gp,
      torusIntegral_sub hc_s1 hc_tr2,
      torusIntegral_sub hc_nu_lap hc_tr1,
      torusIntegral_const_mul ν hc_lap,
      torusIntegral_laplacian_dot_self_7a hw2 hpw,
      torusIntegral_transport_diff_zero_7a hu1 hw1 (hu.h_u_periodic t ht) hpw
        (hu.h_incompressible t ht),
      torusIntegral_grad_dot_solenoidal_zero_7a hr1 hw1 hpr hpw hdiv_w]
  have hdiss_nn : 0 ≤ torusIntegral (gradNormSq3D wt) :=
    torusIntegral_nonneg (continuous_gradNormSq3D hw1) (gradNormSq3D_nonneg wt)
  have htr2_le : -torusIntegral (fun y => dot3D (fun c =>
        wt y 0 * partialDerivScalar (fun z => v t z c) y 0 +
        wt y 1 * partialDerivScalar (fun z => v t z c) y 1 +
        wt y 2 * partialDerivScalar (fun z => v t z c) y 2) (wt y)) ≤
      torusIntegral (fun y => G * dot3D (wt y) (wt y)) := by
    have hneg_eq : -torusIntegral (fun y => dot3D (fun c =>
          wt y 0 * partialDerivScalar (fun z => v t z c) y 0 +
          wt y 1 * partialDerivScalar (fun z => v t z c) y 1 +
          wt y 2 * partialDerivScalar (fun z => v t z c) y 2) (wt y)) =
        torusIntegral (fun y => -dot3D (fun c =>
          wt y 0 * partialDerivScalar (fun z => v t z c) y 0 +
          wt y 1 * partialDerivScalar (fun z => v t z c) y 1 +
          wt y 2 * partialDerivScalar (fun z => v t z c) y 2) (wt y)) := by
      have h := torusIntegral_const_mul (-1 : ℝ) hc_tr2
      have hpt1 : (fun y => (-1 : ℝ) * dot3D (fun c =>
            wt y 0 * partialDerivScalar (fun z => v t z c) y 0 +
            wt y 1 * partialDerivScalar (fun z => v t z c) y 1 +
            wt y 2 * partialDerivScalar (fun z => v t z c) y 2) (wt y)) =
          (fun y => -dot3D (fun c =>
            wt y 0 * partialDerivScalar (fun z => v t z c) y 0 +
            wt y 1 * partialDerivScalar (fun z => v t z c) y 1 +
            wt y 2 * partialDerivScalar (fun z => v t z c) y 2) (wt y)) :=
        funext fun _ => by ring
      rw [hpt1] at h; linarith
    rw [hneg_eq]
    exact torusIntegral_le_on_cube hc_tr2.neg
      (continuous_const.mul (continuous_dot3D hw2.continuous hw2.continuous))
      fun a ha b hb d hd => by
        have habs := abs_directional_dot_le_of_grad_le (w := wt) (v := v t) hG (hgrad_bd a ha b hb d hd)
        linarith [(abs_le.mp habs).1]
  rw [torusIntegral_const_mul G (continuous_dot3D hw2.continuous hw2.continuous)] at htr2_le
  nlinarith [hu.h_nu_pos, hdiss_nn, htr2_le]

/-- **THEOREM 4 OF MILESTONE 7A (Unconditional Classical 3D Navier–Stokes Uniqueness on `𝕋³`):**
    Any two periodic classical `C³` 3D Navier–Stokes solutions `(u, p)` and `(v, q)` with the same
    initial velocity `u(0) = v(0)` coincide identically for all `T ≥ 0` and `x ∈ ℝ³` (`0 sorryAx`). -/
private theorem continuous_joint_spacePartial_7a
    {v : ℝ → R3 → R3}
    (hv_st : ∀ z : ℝ × R3, ContDiffAt ℝ 2 (fun s : ℝ × R3 => v s.1 s.2) z)
    (c i : Fin 3) :
    Continuous (fun z : ℝ × R3 => partialDerivScalar (fun y => v z.1 y c) z.2 i) := by
  have hFc : ∀ z : ℝ × R3, ContDiffAt ℝ 2 (fun s : ℝ × R3 => v s.1 s.2 c) z :=
    fun z => contDiffAt_pi.mp (hv_st z) c
  have hfun : (fun z : ℝ × R3 => partialDerivScalar (fun y => v z.1 y c) z.2 i) =
      (fun z : ℝ × R3 => fderiv ℝ (fun s : ℝ × R3 => v s.1 s.2 c) z ((0 : ℝ), basisVec i)) :=
    funext fun z => spacePartial_eq_fderiv_prod (fun s => v s.1 s.2 c) hFc z.1 z.2 i
  rw [hfun]
  have hcd1 : ContDiff ℝ 1 (fderiv ℝ (fun s : ℝ × R3 => v s.1 s.2 c)) :=
    (contDiff_iff_contDiffAt.mpr hFc).fderiv_right (by simp [one_add_one_eq_two])
  exact (ContinuousLinearMap.apply ℝ ℝ ((0 : ℝ), basisVec i)).continuous.comp hcd1.continuous

private theorem exists_bound_on_Icc_unitCube7 {F : ℝ → R3 → ℝ}
    (hF : Continuous (fun z : ℝ × R3 => F z.1 z.2)) (T : ℝ) :
    ∃ C : ℝ, ∀ s ∈ Set.Icc (0 : ℝ) T,
      ∀ a ∈ Set.Icc (0 : ℝ) 1, ∀ b ∈ Set.Icc (0 : ℝ) 1, ∀ d ∈ Set.Icc (0 : ℝ) 1,
        F s (vec3 a b d) ≤ C := by
  have hK : IsCompact (Set.Icc (0 : ℝ) T ×ˢ unitCube7) :=
    isCompact_Icc.prod (isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc))
  have hF_prod : Continuous (fun z : ℝ × (ℝ × (ℝ × ℝ)) => F z.1 (vec3 z.2.1 z.2.2.1 z.2.2.2)) :=
    hF.comp (continuous_fst.prodMk (continuous_vec3_triple7.comp continuous_snd))
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hF_prod.continuousOn
  refine ⟨C, fun s hs a ha b hb d hd => ?_⟩
  have hbnd := hC (s, (a, (b, d))) ⟨hs, ⟨ha, ⟨hb, hd⟩⟩⟩
  rw [Real.norm_eq_abs] at hbnd
  exact le_trans (le_abs_self _) hbnd

private theorem exists_gradNormSq_bound_on_cube_7a
    {v : ℝ → R3 → R3} {q : ℝ → R3 → ℝ} {ν : ℝ}
    (hv : IsPeriodicClassicalNS3D_C3 v q ν) (T : ℝ) :
    ∃ G : ℝ, 0 ≤ G ∧ ∀ s ∈ Set.Icc (0 : ℝ) T,
      ∀ a ∈ Set.Icc (0 : ℝ) 1, ∀ b ∈ Set.Icc (0 : ℝ) 1, ∀ d ∈ Set.Icc (0 : ℝ) 1,
        gradNormSq3D (v s) (vec3 a b d) ≤ G ^ 2 := by
  have hterm : ∀ c i : Fin 3, ∃ C : ℝ, ∀ s ∈ Set.Icc (0 : ℝ) T,
      ∀ a ∈ Set.Icc (0 : ℝ) 1, ∀ b ∈ Set.Icc (0 : ℝ) 1, ∀ d ∈ Set.Icc (0 : ℝ) 1,
        (partialDerivScalar (fun y => v s y c) (vec3 a b d) i) ^ 2 ≤ C := fun c i =>
    exists_bound_on_Icc_unitCube7
      (F := fun s y => (partialDerivScalar (fun x => v s x c) y i) ^ 2)
      ((continuous_joint_spacePartial_7a hv.h_u_c2_spacetime c i).pow 2) T
  obtain ⟨C00, h00⟩ := hterm 0 0
  obtain ⟨C01, h01⟩ := hterm 0 1
  obtain ⟨C02, h02⟩ := hterm 0 2
  obtain ⟨C10, h10⟩ := hterm 1 0
  obtain ⟨C11, h11⟩ := hterm 1 1
  obtain ⟨C12, h12⟩ := hterm 1 2
  obtain ⟨C20, h20⟩ := hterm 2 0
  obtain ⟨C21, h21⟩ := hterm 2 1
  obtain ⟨C22, h22⟩ := hterm 2 2
  let Ctot : ℝ := C00 + C01 + C02 + C10 + C11 + C12 + C20 + C21 + C22
  refine ⟨Real.sqrt (max Ctot 0), Real.sqrt_nonneg _, fun s hs a ha b hb d hd => ?_⟩
  have hmax : C00 + C01 + C02 + C10 + C11 + C12 + C20 + C21 + C22 ≤ Real.sqrt (max Ctot 0) ^ 2 := by
    rw [Real.sq_sqrt (le_max_right Ctot 0)]
    exact le_max_left Ctot 0
  unfold gradNormSq3D
  linarith [h00 s hs a ha b hb d hd, h01 s hs a ha b hb d hd, h02 s hs a ha b hb d hd,
            h10 s hs a ha b hb d hd, h11 s hs a ha b hb d hd, h12 s hs a ha b hb d hd,
            h20 s hs a ha b hb d hd, h21 s hs a ha b hb d hd, h22 s hs a ha b hb d hd,
            hmax]

theorem classical_ns3d_uniqueness_torus3D
    {u v : ℝ → R3 → R3} {p q : ℝ → R3 → ℝ} {ν : ℝ}
    (hu : IsPeriodicClassicalNS3D_C3 u p ν) (hv : IsPeriodicClassicalNS3D_C3 v q ν)
    (hinit : u 0 = v 0) {T : ℝ} (hT : 0 ≤ T) (x : R3) :
    u T x = v T x := by
  obtain ⟨G, hG_nn, hgrad_bd⟩ := exists_gradNormSq_bound_on_cube_7a hv T
  have hgron := gronwall_exp_integral_bound hT (continuous_const (y := 2 * G))
    (fun t _ => diff_energy_hasDerivAt_7a hu hv t)
    (fun t ht => diff_energy_deriv_le_7a hu hv (le_of_lt ht.1) hG_nn
      (hgrad_bd t ⟨le_of_lt ht.1, le_of_lt ht.2⟩))
  have hE0 : (1 / 2 : ℝ) * torusIntegral (fun y =>
      dot3D (fun c => u 0 y c - v 0 y c) (fun c => u 0 y c - v 0 y c)) = 0 := by
    have h0 : ∀ y : R3, dot3D (fun c => u 0 y c - v 0 y c) (fun c => u 0 y c - v 0 y c) = 0 := by
      intro y; rw [hinit]; unfold dot3D; ring
    rw [torusIntegral_congr h0]; unfold torusIntegral; simp
  rw [hE0, zero_mul] at hgron
  let wT : R3 → R3 := fun y c => u T y c - v T y c
  have hwT_cont : Continuous wT :=
    ((hu.h_u_c3_global T hT).sub (hv.h_u_c3_global T hT)).continuous
  have hwT_per : IsPeriodic3D wT := fun y i => by
    funext c; dsimp only [wT]; rw [hu.h_u_periodic T hT y i, hv.h_u_periodic T hT y i]
  have hET_nn : 0 ≤ torusIntegral (fun y => dot3D (wT y) (wT y)) :=
    torusIntegral_nonneg (continuous_dot3D hwT_cont hwT_cont) (fun y => dot3D_self_nonneg _)
  have hET_zero : torusIntegral (fun y => dot3D (wT y) (wT y)) = 0 := by
    dsimp only [wT] at hET_nn ⊢; linarith
  have hcomp_zero : ∀ c : Fin 3, torusIntegral (fun y => (wT y c) ^ 2) = 0 := by
    have hc : ∀ c : Fin 3, Continuous (fun y => (wT y c) ^ 2) := fun c =>
      ((continuous_apply c).comp hwT_cont).pow 2
    have hpt : ∀ y : R3, dot3D (wT y) (wT y) = (wT y 0) ^ 2 + (wT y 1) ^ 2 + (wT y 2) ^ 2 :=
      fun y => by unfold dot3D; ring
    have hsplit : torusIntegral (fun y => dot3D (wT y) (wT y)) =
        torusIntegral (fun y => (wT y 0) ^ 2) +
        torusIntegral (fun y => (wT y 1) ^ 2) +
        torusIntegral (fun y => (wT y 2) ^ 2) := by
      rw [torusIntegral_congr hpt, torusIntegral_add3 (hc 0) (hc 1) (hc 2)]
    have hnn : ∀ c : Fin 3, 0 ≤ torusIntegral (fun y => (wT y c) ^ 2) := fun c =>
      torusIntegral_nonneg (hc c) (fun _ => sq_nonneg _)
    intro c
    fin_cases c
    · change torusIntegral (fun y => (wT y 0) ^ 2) = 0; linarith [hsplit, hET_zero, hnn 0, hnn 1, hnn 2]
    · change torusIntegral (fun y => (wT y 1) ^ 2) = 0; linarith [hsplit, hET_zero, hnn 0, hnn 1, hnn 2]
    · change torusIntegral (fun y => (wT y 2) ^ 2) = 0; linarith [hsplit, hET_zero, hnn 0, hnn 1, hnn 2]
  funext c
  have hwc0 := eq_zero_of_torusIntegral_sq_eq_zero ((continuous_apply c).comp hwT_cont)
    (fun y i => congrArg (fun z => z c) (hwT_per y i)) (hcomp_zero c) x
  exact sub_eq_zero.mp hwc0

-- ============================================================================
-- SECTION 4: DUHAMEL SEMIGROUP GLUING & UNCONDITIONAL GLOBAL EXISTENCE ON `[0, ∞)`
--            FOR SMALL MEAN-ZERO `H²(𝕋³)` INITIAL DATA
-- ============================================================================

private theorem one_le_kNormSq_of_ne_zero {k : Fin 3 → ℤ} (hk : k ≠ 0) :
    (1 : ℝ) ≤ kNormSq k := by
  have hex : k 0 ≠ 0 ∨ k 1 ≠ 0 ∨ k 2 ≠ 0 := by
    by_contra h; push Not at h; apply hk; funext i; fin_cases i <;> tauto
  have h1 : ∀ n : ℤ, n ≠ 0 → (1 : ℝ) ≤ (n : ℝ) ^ 2 := fun n hn => by
    have ha : (1 : ℤ) ≤ |n| := Int.one_le_abs hn
    have har : (1 : ℝ) ≤ |(n : ℝ)| := by exact_mod_cast ha
    rw [← sq_abs]; nlinarith
  unfold kNormSq
  rcases hex with h0 | h1' | h2
  · linarith [h1 (k 0) h0, sq_nonneg (k 1 : ℝ), sq_nonneg (k 2 : ℝ)]
  · linarith [h1 (k 1) h1', sq_nonneg (k 0 : ℝ), sq_nonneg (k 2 : ℝ)]
  · linarith [h1 (k 2) h2, sq_nonneg (k 0 : ℝ), sq_nonneg (k 1 : ℝ)]

private theorem exp_neg_eight_le_quarter :
    Real.exp (-8 : ℝ) ≤ 1 / 4 := by
  have hexp : (4 : ℝ) ≤ Real.exp 8 := by linarith [Real.add_one_le_exp (8 : ℝ)]
  rw [Real.exp_neg]
  have hinv := inv_anti₀ (by norm_num : (0 : ℝ) < 4) hexp
  norm_num at hinv ⊢
  exact hinv

private theorem heatStep_meanZero_decay {ν : ℝ} (hν : 0 < ν) {u₀ : VecSeq3D}
    (hu₀ : InH2Vec u₀) (hzero : ∀ c : Fin 3, u₀ 0 c = 0) :
    InH2Vec (fun k c => (heatMultiplier3D ν (1 / (Real.pi ^ 2 * ν)) k : ℂ) * u₀ k c) ∧
    h2VecNormSq (fun k c => (heatMultiplier3D ν (1 / (Real.pi ^ 2 * ν)) k : ℂ) * u₀ k c) ≤
      (1 / 4 : ℝ) * h2VecNormSq u₀ := by
  have hpiν : Real.pi ^ 2 * ν ≠ 0 := by positivity
  have hcomp : ∀ c : Fin 3,
      InH2Seq (fun k => (heatMultiplier3D ν (1 / (Real.pi ^ 2 * ν)) k : ℂ) * u₀ k c) ∧
      h2NormSq (fun k => (heatMultiplier3D ν (1 / (Real.pi ^ 2 * ν)) k : ℂ) * u₀ k c) ≤
        (1 / 4 : ℝ) * h2NormSq (fun k => u₀ k c) := by
    intro c
    have hle : ∀ k : Fin 3 → ℤ,
        h2Weight k * ‖(heatMultiplier3D ν (1 / (Real.pi ^ 2 * ν)) k : ℂ) * u₀ k c‖ ^ 2 ≤
          (1 / 4 : ℝ) * (h2Weight k * ‖u₀ k c‖ ^ 2) := by
      intro k
      by_cases hk : k = 0
      · subst hk; simp [hzero c]
      · have hk1 : (1 : ℝ) ≤ kNormSq k := one_le_kNormSq_of_ne_zero hk
        have hsq : (heatMultiplier3D ν (1 / (Real.pi ^ 2 * ν)) k) ^ 2 =
            Real.exp (-8 * kNormSq k) := by
          unfold heatMultiplier3D
          rw [← Real.exp_nat_mul]
          congr 1
          calc (2 : ℕ) * (-4 * Real.pi ^ 2 * ν * kNormSq k * (1 / (Real.pi ^ 2 * ν)))
              = -8 * kNormSq k * ((Real.pi ^ 2 * ν) * (Real.pi ^ 2 * ν)⁻¹) := by push_cast; ring
            _ = -8 * kNormSq k * 1 := by rw [mul_inv_cancel₀ hpiν]
            _ = -8 * kNormSq k := mul_one _
        have hexp_le : Real.exp (-8 * kNormSq k) ≤ 1 / 4 :=
          le_trans (Real.exp_le_exp.mpr (by linarith)) exp_neg_eight_le_quarter
        rw [norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs, hsq]
        have hnn : 0 ≤ h2Weight k * ‖u₀ k c‖ ^ 2 := mul_nonneg (le_of_lt (h2Weight_pos k)) (sq_nonneg _)
        nlinarith
    have hsum := Summable.of_nonneg_of_le
      (fun k => mul_nonneg (le_of_lt (h2Weight_pos k)) (sq_nonneg _)) hle ((hu₀ c).mul_left (1 / 4 : ℝ))
    exact ⟨hsum, hasSum_le hle hsum.hasSum ((hu₀ c).hasSum.mul_left (1 / 4 : ℝ))⟩
  refine ⟨fun c => (hcomp c).1, ?_⟩
  unfold h2VecNormSq
  linarith [(hcomp 0).2, (hcomp 1).2, (hcomp 2).2]

private theorem small_data_step_return_to_ball {ν : ℝ} (hν : 0 < ν) {u₀ : VecSeq3D}
    (hu₀ : InH2Vec u₀) (hsol₀ : IsSolenoidal u₀) (hsym₀ : IsRealSymm u₀)
    (hzero : ∀ c : Fin 3, u₀ 0 c = 0)
    (hsmall₀ : h2VecNormSq u₀ ≤ Real.pi ^ 2 * ν ^ 2 / 217088) :
    let T₀ : ℝ := 1 / (Real.pi ^ 2 * ν)
    let M : ℝ := Real.pi ^ 2 * ν ^ 2 / 54272
    let u := picardLimit ν T₀ u₀
    IsAdmissibleCurve M u ∧
    h2VecNormSq (u T₀) ≤ Real.pi ^ 2 * ν ^ 2 / 217088 ∧
    IsSolenoidal (u T₀) ∧
    IsRealSymm (u T₀) ∧
    (∀ c : Fin 3, u T₀ 0 c = 0) := by
  intro T₀ M u
  have hpiν : Real.pi ^ 2 * ν ≠ 0 := by positivity
  have hT₀_pos : 0 < T₀ := by dsimp only [T₀]; positivity
  have hT₀_nn : 0 ≤ T₀ := le_of_lt hT₀_pos
  have hM_nn : 0 ≤ M := by dsimp only [M]; positivity
  have hR : 4 * h2VecNormSq u₀ ≤ M := by dsimp only [M]; linarith
  have hsmall : 54272 * T₀ * M ≤ ν := by
    have heq : 54272 * T₀ * M = ν := by
      dsimp only [T₀, M]
      calc 54272 * (1 / (Real.pi ^ 2 * ν)) * (Real.pi ^ 2 * ν ^ 2 / 54272)
          = (Real.pi ^ 2 * ν)⁻¹ * (Real.pi ^ 2 * ν) * ν := by ring
        _ = 1 * ν := by rw [inv_mul_cancel₀ hpiν]
        _ = ν := one_mul ν
    linarith
  have hadm := (picardLimit_admissible_and_rate hν hT₀_nn hM_nn hu₀ hR hsmall).1
  have hfix := picardLimit_fixedPoint_and_structure hν hT₀_nn hM_nn hu₀ hsol₀ hsym₀ hR hsmall
  have hlin := heatStep_meanZero_decay hν hu₀ hzero
  have hG_cont : ∀ (k : Fin 3 → ℤ) (c : Fin 3),
      Continuous (fun s : ℝ => heatSmoothedBilinear6A ν (T₀ - s) (u s) (u s) k c) := fun k c => by
    unfold heatSmoothedBilinear6A
    exact (Complex.continuous_ofReal.comp
      ((Real.continuous_exp.comp (continuous_const.mul continuous_id)).comp
        (continuous_const.sub continuous_id))).mul
      (continuous_nsBilinear6A_of_admissible hadm hadm k c)
  have hint := integral_h2_bound_of_inv_sqrt_decay hT₀_nn (K := 848 * M ^ 2 / ν) (by positivity)
    (G := fun s => heatSmoothedBilinear6A ν (T₀ - s) (u s) (u s)) hG_cont fun s hs => by
      have hts : 0 < T₀ - s := sub_pos.mpr hs.2
      have hbd := heatSmoothedBilinear6A_inH2_and_bound hν hts (hadm.h_inH2 s) (hadm.h_inH2 s)
      refine ⟨hbd.1, ?_⟩
      have h1 : h2VecNormSq (u s) * h2VecNormSq (u s) ≤ M ^ 2 := by
        nlinarith [h2VecNormSq_nonneg (u s), hadm.h_bound s]
      have h2 : (848 / (ν * (T₀ - s))) * h2VecNormSq (u s) * h2VecNormSq (u s) ≤
          (848 / (ν * (T₀ - s))) * M ^ 2 := by
        rw [mul_assoc]; exact mul_le_mul_of_nonneg_left h1 (by positivity)
      have h3 : (848 / (ν * (T₀ - s))) * M ^ 2 = (848 * M ^ 2 / ν) / (T₀ - s) := by
        have hν_ne : ν ≠ 0 := ne_of_gt hν
        have hts_ne : T₀ - s ≠ 0 := ne_of_gt hts
        field_simp [hν_ne, hts_ne]
      linarith [hbd.2]
  have hadd := inH2Vec_add hlin.1 hint.1
  have huT_eq : u T₀ = (fun k c => (heatMultiplier3D ν T₀ k : ℂ) * u₀ k c +
      ∫ s in (0 : ℝ)..T₀, heatSmoothedBilinear6A ν (T₀ - s) (u s) (u s) k c) :=
    hfix.2.1 T₀ ⟨hT₀_nn, le_rfl⟩
  have hbd_T₀ : h2VecNormSq (u T₀) ≤ Real.pi ^ 2 * ν ^ 2 / 217088 := by
    rw [huT_eq]
    have hcalc : 2 * (4 * T₀ * (848 * M ^ 2 / ν)) = Real.pi ^ 2 * ν ^ 2 / 434176 := by
      dsimp only [T₀, M]
      have hν_ne : ν ≠ 0 := ne_of_gt hν
      calc 2 * (4 * (1 / (Real.pi ^ 2 * ν)) * (848 * (Real.pi ^ 2 * ν ^ 2 / 54272) ^ 2 / ν))
          = ((Real.pi ^ 2 * ν)⁻¹ * (Real.pi ^ 2 * ν)) * (ν⁻¹ * ν) * (Real.pi ^ 2 * ν ^ 2 / 434176) := by ring
        _ = 1 * 1 * (Real.pi ^ 2 * ν ^ 2 / 434176) := by rw [inv_mul_cancel₀ hpiν, inv_mul_cancel₀ hν_ne]
        _ = Real.pi ^ 2 * ν ^ 2 / 434176 := by ring
    linarith [hadd.2, hlin.2, hint.2, hcalc]
  have hst := hfix.2.2.2 T₀
  refine ⟨hadm, hbd_T₀, hst.1, hst.2.1, fun c => ?_⟩
  dsimp only [u]; rw [hst.2.2 c, hzero c]

/-- **THEOREM 5 OF MILESTONE 7A (Duhamel Semigroup Gluing Lemma):**
    If an admissible curve `u` solves `duhamelRaw` from `0` to `T₁` and solves `duhamelRaw`
    restarted at `u(T₁)` on `[0, s]`, then `u(T₁ + s) = duhamelRaw ν u₀ u (T₁ + s)` (`0 sorryAx`). -/
theorem duhamelRaw_semigroup_glue {ν M T₁ s : ℝ} (u₀ : VecSeq3D)
    {u : ℝ → VecSeq3D} (hu : IsAdmissibleCurve M u)
    (h1 : u T₁ = duhamelRaw ν u₀ u T₁)
    (h2 : u (T₁ + s) = duhamelRaw ν (u T₁) (fun r => u (T₁ + r)) s) :
    u (T₁ + s) = duhamelRaw ν u₀ u (T₁ + s) := by
  funext k c
  rw [congrFun (congrFun h2 k) c]
  unfold duhamelRaw
  rw [congrFun (congrFun h1 k) c]
  unfold duhamelRaw
  have hlin : (heatMultiplier3D ν s k : ℂ) * ((heatMultiplier3D ν T₁ k : ℂ) * u₀ k c) =
      (heatMultiplier3D ν (T₁ + s) k : ℂ) * u₀ k c := by
    rw [← mul_assoc, ← Complex.ofReal_mul, ← heatMultiplier3D_add, add_comm s T₁]
  have hint1 : (heatMultiplier3D ν s k : ℂ) *
      (∫ r in (0 : ℝ)..T₁, heatSmoothedBilinear6A ν (T₁ - r) (u r) (u r) k c) =
      ∫ r in (0 : ℝ)..T₁, heatSmoothedBilinear6A ν (T₁ + s - r) (u r) (u r) k c := by
    rw [← intervalIntegral.integral_const_mul]
    congr 1; funext r
    unfold heatSmoothedBilinear6A
    rw [← mul_assoc, ← Complex.ofReal_mul, ← heatMultiplier3D_add]
    have harg : s + (T₁ - r) = T₁ + s - r := by ring
    rw [harg]
  have hint2 : (∫ r in (0 : ℝ)..s, heatSmoothedBilinear6A ν (s - r) (u (T₁ + r)) (u (T₁ + r)) k c) =
      ∫ r in T₁..(T₁ + s), heatSmoothedBilinear6A ν (T₁ + s - r) (u r) (u r) k c := by
    have hcomp := intervalIntegral.integral_comp_add_left
      (f := fun y => heatSmoothedBilinear6A ν (T₁ + s - y) (u y) (u y) k c) (a := (0 : ℝ)) (b := s) T₁
    rw [add_zero] at hcomp
    have hfun : (fun x => heatSmoothedBilinear6A ν (T₁ + s - (T₁ + x)) (u (T₁ + x)) (u (T₁ + x)) k c) =
        (fun x => heatSmoothedBilinear6A ν (s - x) (u (T₁ + x)) (u (T₁ + x)) k c) := by
      funext x
      have hsub : T₁ + s - (T₁ + x) = s - x := by ring
      rw [hsub]
    rw [hfun] at hcomp
    exact hcomp
  have hc_int : Continuous (fun r => heatSmoothedBilinear6A ν (T₁ + s - r) (u r) (u r) k c) := by
    unfold heatSmoothedBilinear6A
    exact (Complex.continuous_ofReal.comp
      ((Real.continuous_exp.comp (continuous_const.mul continuous_id)).comp
        (continuous_const.sub continuous_id))).mul
      (continuous_nsBilinear6A_of_admissible hu hu k c)
  rw [mul_add, hlin, hint1, hint2, add_assoc,
      intervalIntegral.integral_add_adjacent_intervals
        (hc_int.intervalIntegrable (μ := volume) 0 T₁)
        (hc_int.intervalIntegrable (μ := volume) T₁ (T₁ + s))]

/-- Recursive state sequence `u(n / (π² ν))` generated by iterating the small-data `H²` map. -/
noncomputable def smallDataState (ν : ℝ) (u₀ : VecSeq3D) : ℕ → VecSeq3D
  | 0 => u₀
  | n + 1 => picardLimit ν (1 / (Real.pi ^ 2 * ν)) (smallDataState ν u₀ n) (1 / (Real.pi ^ 2 * ν))

/-- Global stitched solution curve on `[0, ∞)` extended constantly for `t ≤ 0`. -/
noncomputable def smallDataGlobal (ν : ℝ) (u₀ : VecSeq3D) (t : ℝ) : VecSeq3D :=
  if t ≤ 0 then u₀
  else
    picardLimit ν (1 / (Real.pi ^ 2 * ν))
      (smallDataState ν u₀ (Nat.floor (t * (Real.pi ^ 2 * ν))))
      (t - (Nat.floor (t * (Real.pi ^ 2 * ν)) : ℝ) * (1 / (Real.pi ^ 2 * ν)))

private theorem smallDataState_invariant {ν : ℝ} (hν : 0 < ν) {u₀ : VecSeq3D}
    (hu₀ : InH2Vec u₀) (hsol₀ : IsSolenoidal u₀) (hsym₀ : IsRealSymm u₀)
    (hzero : ∀ c : Fin 3, u₀ 0 c = 0)
    (hsmall₀ : h2VecNormSq u₀ ≤ Real.pi ^ 2 * ν ^ 2 / 217088) (n : ℕ) :
    InH2Vec (smallDataState ν u₀ n) ∧
    h2VecNormSq (smallDataState ν u₀ n) ≤ Real.pi ^ 2 * ν ^ 2 / 217088 ∧
    IsSolenoidal (smallDataState ν u₀ n) ∧
    IsRealSymm (smallDataState ν u₀ n) ∧
    (∀ c : Fin 3, smallDataState ν u₀ n 0 c = 0) := by
  induction n with
  | zero => exact ⟨hu₀, hsmall₀, hsol₀, hsym₀, hzero⟩
  | succ m ih =>
    have hstep := small_data_step_return_to_ball hν ih.1 ih.2.2.1 ih.2.2.2.1 ih.2.2.2.2 ih.2.1
    exact ⟨hstep.1.h_inH2 _, hstep.2.1, hstep.2.2.1, hstep.2.2.2.1, hstep.2.2.2.2⟩

private theorem smallDataGlobal_slab_eq {ν : ℝ} (hν : 0 < ν) {u₀ : VecSeq3D}
    (hu₀ : InH2Vec u₀) (hsol₀ : IsSolenoidal u₀) (hsym₀ : IsRealSymm u₀)
    (hzero : ∀ c : Fin 3, u₀ 0 c = 0)
    (hsmall₀ : h2VecNormSq u₀ ≤ Real.pi ^ 2 * ν ^ 2 / 217088)
    (n : ℕ) {s : ℝ} (hs : s ∈ Set.Icc (0 : ℝ) (1 / (Real.pi ^ 2 * ν))) :
    smallDataGlobal ν u₀ ((n : ℝ) * (1 / (Real.pi ^ 2 * ν)) + s) =
      picardLimit ν (1 / (Real.pi ^ 2 * ν)) (smallDataState ν u₀ n) s := by
  have hpiν_pos : 0 < Real.pi ^ 2 * ν := by positivity
  have hpiν : Real.pi ^ 2 * ν ≠ 0 := ne_of_gt hpiν_pos
  have hT₀_pos : 0 < 1 / (Real.pi ^ 2 * ν) := by positivity
  have hM_nn : 0 ≤ Real.pi ^ 2 * ν ^ 2 / 54272 := by positivity
  have hsm : 54272 * (1 / (Real.pi ^ 2 * ν)) * (Real.pi ^ 2 * ν ^ 2 / 54272) ≤ ν := by
    have heq : 54272 * (1 / (Real.pi ^ 2 * ν)) * (Real.pi ^ 2 * ν ^ 2 / 54272) = ν := by
      calc 54272 * (1 / (Real.pi ^ 2 * ν)) * (Real.pi ^ 2 * ν ^ 2 / 54272)
          = (Real.pi ^ 2 * ν)⁻¹ * (Real.pi ^ 2 * ν) * ν := by ring
        _ = 1 * ν := by rw [inv_mul_cancel₀ hpiν]
        _ = ν := one_mul ν
    linarith
  have hst_n := smallDataState_invariant hν hu₀ hsol₀ hsym₀ hzero hsmall₀ n
  have hfix_n := picardLimit_fixedPoint_and_structure hν (le_of_lt hT₀_pos) hM_nn
    hst_n.1 hst_n.2.2.1 hst_n.2.2.2.1 (by linarith [hst_n.2.1]) hsm
  rcases eq_or_lt_of_le hs.2 with rfl | hs_lt
  · have ht_pos : 0 < (n : ℝ) * (1 / (Real.pi ^ 2 * ν)) + 1 / (Real.pi ^ 2 * ν) := by positivity
    have hprod : ((n : ℝ) * (1 / (Real.pi ^ 2 * ν)) + 1 / (Real.pi ^ 2 * ν)) * (Real.pi ^ 2 * ν) =
        ((n + 1 : ℕ) : ℝ) := by
      rw [add_mul, mul_assoc, one_div_mul_cancel hpiν, mul_one]; push_cast; ring
    have hfl : Nat.floor (((n : ℝ) * (1 / (Real.pi ^ 2 * ν)) + 1 / (Real.pi ^ 2 * ν)) * (Real.pi ^ 2 * ν)) =
        n + 1 := by rw [hprod, Nat.floor_natCast]
    have hsub : (n : ℝ) * (1 / (Real.pi ^ 2 * ν)) + 1 / (Real.pi ^ 2 * ν) -
        ((n + 1 : ℕ) : ℝ) * (1 / (Real.pi ^ 2 * ν)) = 0 := by push_cast; ring
    unfold smallDataGlobal
    simp only [not_le.mpr ht_pos, ↓reduceIte, hfl, hsub]
    have hst_n1 := smallDataState_invariant hν hu₀ hsol₀ hsym₀ hzero hsmall₀ (n + 1)
    have hfix_n1 := picardLimit_fixedPoint_and_structure hν (le_of_lt hT₀_pos) hM_nn
      hst_n1.1 hst_n1.2.2.1 hst_n1.2.2.2.1 (by linarith [hst_n1.2.1]) hsm
    rw [hfix_n1.2.2.1]; rfl
  · by_cases ht0 : (n : ℝ) * (1 / (Real.pi ^ 2 * ν)) + s ≤ 0
    · have hn0 : n = 0 := by
        by_contra hne
        have hn1 : (1 : ℝ) ≤ (n : ℝ) := Nat.one_le_cast.mpr (Nat.pos_of_ne_zero hne)
        have : 0 < (n : ℝ) * (1 / (Real.pi ^ 2 * ν)) := mul_pos (by linarith) hT₀_pos
        linarith [hs.1]
      subst hn0
      have hs0 : s = 0 := by simp at ht0; linarith [hs.1]
      subst hs0
      unfold smallDataGlobal
      simp only [Nat.cast_zero, zero_mul, add_zero, le_refl, ↓reduceIte]
      exact hfix_n.2.2.1.symm
    · push Not at ht0
      have hs0 : 0 ≤ s := hs.1
      have hprod : ((n : ℝ) * (1 / (Real.pi ^ 2 * ν)) + s) * (Real.pi ^ 2 * ν) =
          (n : ℝ) + s * (Real.pi ^ 2 * ν) := by
        rw [add_mul, mul_assoc, one_div_mul_cancel hpiν, mul_one]
      have hfl : Nat.floor (((n : ℝ) * (1 / (Real.pi ^ 2 * ν)) + s) * (Real.pi ^ 2 * ν)) = n := by
        rw [hprod, Nat.floor_eq_iff (by positivity)]
        have hs_lt1 : s * (Real.pi ^ 2 * ν) < 1 := by
          have := mul_lt_mul_of_pos_right hs_lt hpiν_pos
          rwa [one_div_mul_cancel hpiν] at this
        exact ⟨by linarith [mul_nonneg hs0 (le_of_lt hpiν_pos)], by linarith⟩
      have hsub : (n : ℝ) * (1 / (Real.pi ^ 2 * ν)) + s - (n : ℝ) * (1 / (Real.pi ^ 2 * ν)) = s := by ring
      unfold smallDataGlobal
      simp only [not_le.mpr ht0, ↓reduceIte, hfl, hsub]

private theorem smallDataGlobal_continuous {ν : ℝ} (hν : 0 < ν) {u₀ : VecSeq3D}
    (hu₀ : InH2Vec u₀) (hsol₀ : IsSolenoidal u₀) (hsym₀ : IsRealSymm u₀)
    (hzero : ∀ c : Fin 3, u₀ 0 c = 0)
    (hsmall₀ : h2VecNormSq u₀ ≤ Real.pi ^ 2 * ν ^ 2 / 217088)
    (k : Fin 3 → ℤ) (c : Fin 3) :
    Continuous (fun t : ℝ => smallDataGlobal ν u₀ t k c) := by
  let T₀ : ℝ := 1 / (Real.pi ^ 2 * ν)
  let M : ℝ := Real.pi ^ 2 * ν ^ 2 / 54272
  have hpiν_pos : 0 < Real.pi ^ 2 * ν := by positivity
  have hpiν : Real.pi ^ 2 * ν ≠ 0 := ne_of_gt hpiν_pos
  have hT₀_pos : 0 < T₀ := by dsimp only [T₀]; positivity
  have hT₀_nn : 0 ≤ T₀ := le_of_lt hT₀_pos
  have hM_nn : 0 ≤ M := by dsimp only [M]; positivity
  have hsm : 54272 * T₀ * M ≤ ν := by
    have heq : 54272 * T₀ * M = ν := by
      dsimp only [T₀, M]
      calc 54272 * (1 / (Real.pi ^ 2 * ν)) * (Real.pi ^ 2 * ν ^ 2 / 54272)
          = (Real.pi ^ 2 * ν)⁻¹ * (Real.pi ^ 2 * ν) * ν := by ring
        _ = 1 * ν := by rw [inv_mul_cancel₀ hpiν]
        _ = ν := one_mul ν
    linarith
  have hslab_cont : ∀ n : ℕ, Continuous (fun s : ℝ => picardLimit ν T₀ (smallDataState ν u₀ n) s k c) := by
    intro n
    have hst := smallDataState_invariant hν hu₀ hsol₀ hsym₀ hzero hsmall₀ n
    exact (picardLimit_admissible_and_rate hν hT₀_nn hM_nn hst.1 (by dsimp only [M]; linarith [hst.2.1]) hsm).1.h_cont k c
  have h0_eq : picardLimit ν T₀ u₀ 0 = u₀ :=
    (picardLimit_fixedPoint_and_structure hν hT₀_nn hM_nn hu₀ hsol₀ hsym₀ (by dsimp only [M]; linarith) hsm).2.2.1
  refine continuous_iff_continuousAt.mpr fun t₀ => ?_
  by_cases ht_neg : t₀ < 0
  · refine (continuousAt_const (y := u₀ k c)).congr ?_
    filter_upwards [Iio_mem_nhds ht_neg] with t ht
    have ht_le : t ≤ 0 := le_of_lt (Set.mem_Iio.mp ht)
    unfold smallDataGlobal; simp only [ht_le, ↓reduceIte]
  · push Not at ht_neg
    rcases eq_or_lt_of_le ht_neg with rfl | ht_pos
    · have hcont0 : ContinuousAt (fun t : ℝ => picardLimit ν T₀ u₀ (max 0 t) k c) 0 :=
        ((hslab_cont 0).comp (continuous_const.max continuous_id)).continuousAt
      refine hcont0.congr ?_
      filter_upwards [Ioo_mem_nhds (by norm_num : (-1 : ℝ) < 0) hT₀_pos] with t ht
      rcases le_or_gt t 0 with hle | hgt
      · rw [max_eq_left hle]
        unfold smallDataGlobal; simp only [hle, ↓reduceIte]
        exact congrArg (fun w => w k c) h0_eq
      · rw [max_eq_right (le_of_lt hgt)]
        have heq := smallDataGlobal_slab_eq hν hu₀ hsol₀ hsym₀ hzero hsmall₀ 0 ⟨le_of_lt hgt, le_of_lt ht.2⟩
        simp only [Nat.cast_zero, zero_mul, zero_add] at heq
        exact congrArg (fun w => w k c) heq.symm
    · let n : ℕ := Nat.floor (t₀ * (Real.pi ^ 2 * ν))
      have hnt_le : (n : ℝ) * T₀ ≤ t₀ := by
        have hfl := Nat.floor_le (by positivity : 0 ≤ t₀ * (Real.pi ^ 2 * ν))
        have h1 := mul_le_mul_of_nonneg_right hfl hT₀_nn
        dsimp only [T₀] at h1 ⊢
        rw [mul_assoc, mul_one_div_cancel hpiν, mul_one] at h1
        exact h1
      have hnt_lt : t₀ < ((n + 1 : ℕ) : ℝ) * T₀ := by
        have hfl := Nat.lt_floor_add_one (t₀ * (Real.pi ^ 2 * ν))
        have h1 := mul_lt_mul_of_pos_right hfl hT₀_pos
        dsimp only [T₀] at h1 ⊢
        rw [mul_assoc, mul_one_div_cancel hpiν, mul_one] at h1
        push_cast; linarith
      rcases eq_or_lt_of_le hnt_le with heq_bd | hnt_strict
      · have hn_pos : 1 ≤ n := by
          by_contra h0
          have hn0 : n = 0 := by omega
          rw [hn0] at heq_bd; simp at heq_bd; linarith
        let m : ℕ := n - 1
        have hmn : m + 1 = n := by omega
        have ht0_eq : t₀ = (m : ℝ) * T₀ + T₀ := by
          rw [← heq_bd, ← hmn]; push_cast; ring
        refine Metric.continuousAt_iff.mpr fun ε hε => ?_
        have hcm : ContinuousAt (fun r : ℝ => picardLimit ν T₀ (smallDataState ν u₀ m) (r - (m : ℝ) * T₀) k c) t₀ :=
          ((hslab_cont m).comp (continuous_id.sub continuous_const)).continuousAt
        have hcn : ContinuousAt (fun r : ℝ => picardLimit ν T₀ (smallDataState ν u₀ n) (r - (n : ℝ) * T₀) k c) t₀ :=
          ((hslab_cont n).comp (continuous_id.sub continuous_const)).continuousAt
        obtain ⟨δ₁, hδ₁_pos, hδ₁⟩ := Metric.continuousAt_iff.mp hcm ε hε
        obtain ⟨δ₂, hδ₂_pos, hδ₂⟩ := Metric.continuousAt_iff.mp hcn ε hε
        let δ : ℝ := min (min δ₁ δ₂) (T₀ / 2)
        have hδ_pos : 0 < δ := lt_min (lt_min hδ₁_pos hδ₂_pos) (by positivity)
        refine ⟨δ, hδ_pos, fun {t} ht => ?_⟩
        have hd1 : dist t t₀ < δ₁ := lt_of_lt_of_le ht (le_trans (min_le_left _ _) (min_le_left _ _))
        have hd2 : dist t t₀ < δ₂ := lt_of_lt_of_le ht (le_trans (min_le_left _ _) (min_le_right _ _))
        have hdT : |t - t₀| < T₀ / 2 := by rw [← Real.dist_eq]; exact lt_of_lt_of_le ht (min_le_right _ _)
        have htab : t₀ - T₀ / 2 < t ∧ t < t₀ + T₀ / 2 :=
          abs_lt.mp hdT |> fun ⟨h1, h2⟩ => ⟨by linarith, by linarith⟩
        rcases le_or_gt t t₀ with hle | hgt
        · have hs_mem : t - (m : ℝ) * T₀ ∈ Set.Icc (0 : ℝ) T₀ :=
            ⟨by linarith [ht0_eq, htab.1], by linarith [ht0_eq]⟩
          have h1 := congrArg (fun w => w k c)
            (smallDataGlobal_slab_eq hν hu₀ hsol₀ hsym₀ hzero hsmall₀ m hs_mem)
          have h2 := congrArg (fun w => w k c)
            (smallDataGlobal_slab_eq hν hu₀ hsol₀ hsym₀ hzero hsmall₀ m ⟨hT₀_nn, le_rfl⟩)
          have hsum_t : (m : ℝ) * (1 / (Real.pi ^ 2 * ν)) + (t - (m : ℝ) * T₀) = t := by
            dsimp only [T₀]; ring
          have ht0_eq' : (m : ℝ) * (1 / (Real.pi ^ 2 * ν)) + 1 / (Real.pi ^ 2 * ν) = t₀ := by
            dsimp only [T₀] at ht0_eq; exact ht0_eq.symm
          have hsum_t0 : t₀ - (m : ℝ) * T₀ = T₀ := by linarith [ht0_eq]
          rw [hsum_t] at h1; rw [ht0_eq'] at h2
          have hdist : dist (picardLimit ν T₀ (smallDataState ν u₀ m) (t - (m : ℝ) * T₀) k c)
              (picardLimit ν T₀ (smallDataState ν u₀ m) (t₀ - (m : ℝ) * T₀) k c) < ε := hδ₁ hd1
          rw [hsum_t0] at hdist
          rw [h1, h2]; exact hdist
        · have hs_mem : t - (n : ℝ) * T₀ ∈ Set.Icc (0 : ℝ) T₀ :=
            ⟨by linarith [heq_bd], by linarith [heq_bd, htab.2]⟩
          have h1 := congrArg (fun w => w k c)
            (smallDataGlobal_slab_eq hν hu₀ hsol₀ hsym₀ hzero hsmall₀ n hs_mem)
          have h2 := congrArg (fun w => w k c)
            (smallDataGlobal_slab_eq hν hu₀ hsol₀ hsym₀ hzero hsmall₀ n ⟨le_rfl, hT₀_nn⟩)
          have hsum_t : (n : ℝ) * (1 / (Real.pi ^ 2 * ν)) + (t - (n : ℝ) * T₀) = t := by
            dsimp only [T₀]; ring
          have ht0_eq' : (n : ℝ) * (1 / (Real.pi ^ 2 * ν)) + 0 = t₀ := by
            dsimp only [T₀] at heq_bd; linarith
          have hsum_t0 : t₀ - (n : ℝ) * T₀ = 0 := by linarith [heq_bd]
          rw [hsum_t] at h1; rw [ht0_eq'] at h2
          have hdist : dist (picardLimit ν T₀ (smallDataState ν u₀ n) (t - (n : ℝ) * T₀) k c)
              (picardLimit ν T₀ (smallDataState ν u₀ n) (t₀ - (n : ℝ) * T₀) k c) < ε := hδ₂ hd2
          rw [hsum_t0] at hdist
          rw [h1, h2]; exact hdist
      · have hcn : ContinuousAt (fun r : ℝ => picardLimit ν T₀ (smallDataState ν u₀ n) (r - (n : ℝ) * T₀) k c) t₀ :=
          ((hslab_cont n).comp (continuous_id.sub continuous_const)).continuousAt
        refine hcn.congr ?_
        filter_upwards [Ioo_mem_nhds hnt_strict hnt_lt] with t ht
        have hs_mem : t - (n : ℝ) * T₀ ∈ Set.Icc (0 : ℝ) T₀ := by
          have hsucc : ((n + 1 : ℕ) : ℝ) * T₀ = (n : ℝ) * T₀ + T₀ := by push_cast; ring
          exact ⟨by linarith [ht.1], by linarith [ht.2, hsucc]⟩
        have h1 := smallDataGlobal_slab_eq hν hu₀ hsol₀ hsym₀ hzero hsmall₀ n hs_mem
        have hsum_t : (n : ℝ) * T₀ + (t - (n : ℝ) * T₀) = t := by ring
        rw [hsum_t] at h1
        exact congrArg (fun w => w k c) h1.symm

private theorem smallDataGlobal_admissible_and_struct {ν : ℝ} (hν : 0 < ν) {u₀ : VecSeq3D}
    (hu₀ : InH2Vec u₀) (hsol₀ : IsSolenoidal u₀) (hsym₀ : IsRealSymm u₀)
    (hzero : ∀ c : Fin 3, u₀ 0 c = 0)
    (hsmall₀ : h2VecNormSq u₀ ≤ Real.pi ^ 2 * ν ^ 2 / 217088) :
    IsAdmissibleCurve (Real.pi ^ 2 * ν ^ 2 / 54272) (smallDataGlobal ν u₀) ∧
    (∀ t : ℝ, IsSolenoidal (smallDataGlobal ν u₀ t) ∧
              IsRealSymm (smallDataGlobal ν u₀ t) ∧
              (∀ c : Fin 3, smallDataGlobal ν u₀ t 0 c = 0)) := by
  let T₀ : ℝ := 1 / (Real.pi ^ 2 * ν)
  let M : ℝ := Real.pi ^ 2 * ν ^ 2 / 54272
  have hpiν : Real.pi ^ 2 * ν ≠ 0 := by positivity
  have hT₀_nn : 0 ≤ T₀ := by dsimp only [T₀]; positivity
  have hM_nn : 0 ≤ M := by dsimp only [M]; positivity
  have hsm : 54272 * T₀ * M ≤ ν := by
    have heq : 54272 * T₀ * M = ν := by
      dsimp only [T₀, M]
      calc 54272 * (1 / (Real.pi ^ 2 * ν)) * (Real.pi ^ 2 * ν ^ 2 / 54272)
          = (Real.pi ^ 2 * ν)⁻¹ * (Real.pi ^ 2 * ν) * ν := by ring
        _ = 1 * ν := by rw [inv_mul_cancel₀ hpiν]
        _ = ν := one_mul ν
    linarith
  have hslab_adm : ∀ n : ℕ, IsAdmissibleCurve M (picardLimit ν T₀ (smallDataState ν u₀ n)) := by
    intro n
    have hst := smallDataState_invariant hν hu₀ hsol₀ hsym₀ hzero hsmall₀ n
    exact (picardLimit_admissible_and_rate hν hT₀_nn hM_nn hst.1 (by dsimp only [M]; linarith [hst.2.1]) hsm).1
  have hslab_st : ∀ (n : ℕ) (s : ℝ),
      IsSolenoidal (picardLimit ν T₀ (smallDataState ν u₀ n) s) ∧
      IsRealSymm (picardLimit ν T₀ (smallDataState ν u₀ n) s) ∧
      (∀ c : Fin 3, picardLimit ν T₀ (smallDataState ν u₀ n) s 0 c = 0) := by
    intro n s
    have hst := smallDataState_invariant hν hu₀ hsol₀ hsym₀ hzero hsmall₀ n
    have hfix := picardLimit_fixedPoint_and_structure hν hT₀_nn hM_nn
      hst.1 hst.2.2.1 hst.2.2.2.1 (by dsimp only [M]; linarith [hst.2.1]) hsm
    exact ⟨(hfix.2.2.2 s).1, (hfix.2.2.2 s).2.1, fun c => by rw [(hfix.2.2.2 s).2.2 c, hst.2.2.2.2 c]⟩
  refine ⟨⟨fun t => ?_, fun t => ?_, smallDataGlobal_continuous hν hu₀ hsol₀ hsym₀ hzero hsmall₀⟩, fun t => ?_⟩
  · unfold smallDataGlobal; split_ifs
    · exact hu₀
    · exact (hslab_adm _).h_inH2 _
  · unfold smallDataGlobal; split_ifs
    · have hpos : 0 ≤ Real.pi ^ 2 * ν ^ 2 := by positivity
      linarith [hsmall₀, hpos]
    · exact (hslab_adm _).h_bound _
  · unfold smallDataGlobal; split_ifs
    · exact ⟨hsol₀, hsym₀, hzero⟩
    · exact hslab_st _ _

private theorem smallDataGlobal_duhamel_all {ν : ℝ} (hν : 0 < ν) {u₀ : VecSeq3D}
    (hu₀ : InH2Vec u₀) (hsol₀ : IsSolenoidal u₀) (hsym₀ : IsRealSymm u₀)
    (hzero : ∀ c : Fin 3, u₀ 0 c = 0)
    (hsmall₀ : h2VecNormSq u₀ ≤ Real.pi ^ 2 * ν ^ 2 / 217088) :
    ∀ t : ℝ, 0 ≤ t → smallDataGlobal ν u₀ t = duhamelRaw ν u₀ (smallDataGlobal ν u₀) t := by
  let T₀ : ℝ := 1 / (Real.pi ^ 2 * ν)
  let M : ℝ := Real.pi ^ 2 * ν ^ 2 / 54272
  have hpiν_pos : 0 < Real.pi ^ 2 * ν := by positivity
  have hpiν : Real.pi ^ 2 * ν ≠ 0 := ne_of_gt hpiν_pos
  have hT₀_pos : 0 < T₀ := by dsimp only [T₀]; positivity
  have hT₀_nn : 0 ≤ T₀ := le_of_lt hT₀_pos
  have hM_nn : 0 ≤ M := by dsimp only [M]; positivity
  have hsm : 54272 * T₀ * M ≤ ν := by
    have heq : 54272 * T₀ * M = ν := by
      dsimp only [T₀, M]
      calc 54272 * (1 / (Real.pi ^ 2 * ν)) * (Real.pi ^ 2 * ν ^ 2 / 54272)
          = (Real.pi ^ 2 * ν)⁻¹ * (Real.pi ^ 2 * ν) * ν := by ring
        _ = 1 * ν := by rw [inv_mul_cancel₀ hpiν]
        _ = ν := one_mul ν
    linarith
  have hu_adm := (smallDataGlobal_admissible_and_struct hν hu₀ hsol₀ hsym₀ hzero hsmall₀).1
  have hslab_fix : ∀ n : ℕ,
      (∀ s ∈ Set.Icc (0 : ℝ) T₀,
        picardLimit ν T₀ (smallDataState ν u₀ n) s =
          duhamelRaw ν (smallDataState ν u₀ n) (picardLimit ν T₀ (smallDataState ν u₀ n)) s) ∧
      picardLimit ν T₀ (smallDataState ν u₀ n) 0 = smallDataState ν u₀ n := by
    intro n
    have hst := smallDataState_invariant hν hu₀ hsol₀ hsym₀ hzero hsmall₀ n
    have hfix := picardLimit_fixedPoint_and_structure hν hT₀_nn hM_nn
      hst.1 hst.2.2.1 hst.2.2.2.1 (by dsimp only [M]; linarith [hst.2.1]) hsm
    exact ⟨hfix.2.1, hfix.2.2.1⟩
  have hslab : ∀ (n : ℕ) (s : ℝ), s ∈ Set.Icc (0 : ℝ) T₀ →
      smallDataGlobal ν u₀ ((n : ℝ) * T₀ + s) =
        duhamelRaw ν u₀ (smallDataGlobal ν u₀) ((n : ℝ) * T₀ + s) := by
    intro n
    induction n with
    | zero =>
      intro s hs
      have h0 := smallDataGlobal_slab_eq hν hu₀ hsol₀ hsym₀ hzero hsmall₀ 0 hs
      simp only [Nat.cast_zero, zero_mul, zero_add] at h0 ⊢
      rw [h0, (hslab_fix 0).1 s hs]
      funext k c; unfold duhamelRaw
      have hint : (∫ r in (0 : ℝ)..s,
            heatSmoothedBilinear6A ν (s - r) (picardLimit ν T₀ u₀ r) (picardLimit ν T₀ u₀ r) k c) =
          ∫ r in (0 : ℝ)..s,
            heatSmoothedBilinear6A ν (s - r) (smallDataGlobal ν u₀ r) (smallDataGlobal ν u₀ r) k c := by
        refine intervalIntegral.integral_congr fun r hr => ?_
        rw [Set.uIcc_of_le hs.1] at hr
        have hru := smallDataGlobal_slab_eq hν hu₀ hsol₀ hsym₀ hzero hsmall₀ 0 ⟨hr.1, le_trans hr.2 hs.2⟩
        simp only [Nat.cast_zero, zero_mul, zero_add] at hru
        change heatSmoothedBilinear6A ν (s - r) (picardLimit ν (1 / (Real.pi ^ 2 * ν)) (smallDataState ν u₀ 0) r)
            (picardLimit ν (1 / (Real.pi ^ 2 * ν)) (smallDataState ν u₀ 0) r) k c = _
        rw [← hru]
      exact congrArg ((heatMultiplier3D ν s k : ℂ) * u₀ k c + ·) hint
    | succ m ih =>
      intro s hs
      have hm_end : smallDataGlobal ν u₀ (((m + 1 : ℕ) : ℝ) * T₀) =
          duhamelRaw ν u₀ (smallDataGlobal ν u₀) (((m + 1 : ℕ) : ℝ) * T₀) := by
        have hstep := ih T₀ ⟨hT₀_nn, le_rfl⟩
        have hcast : ((m + 1 : ℕ) : ℝ) * T₀ = (m : ℝ) * T₀ + T₀ := by push_cast; ring
        rwa [hcast]
      have hloc : smallDataGlobal ν u₀ (((m + 1 : ℕ) : ℝ) * T₀ + s) =
          duhamelRaw ν (smallDataGlobal ν u₀ (((m + 1 : ℕ) : ℝ) * T₀))
            (fun r => smallDataGlobal ν u₀ (((m + 1 : ℕ) : ℝ) * T₀ + r)) s := by
        have h1 := smallDataGlobal_slab_eq hν hu₀ hsol₀ hsym₀ hzero hsmall₀ (m + 1) hs
        have h2 := smallDataGlobal_slab_eq hν hu₀ hsol₀ hsym₀ hzero hsmall₀ (m + 1) ⟨le_rfl, hT₀_nn⟩
        rw [add_zero] at h2
        have hst_eq : smallDataGlobal ν u₀ (((m + 1 : ℕ) : ℝ) * T₀) = smallDataState ν u₀ (m + 1) := by
          rw [h2, (hslab_fix (m + 1)).2]
        rw [h1, (hslab_fix (m + 1)).1 s hs, hst_eq]
        funext k c; unfold duhamelRaw
        have hint : (∫ r in (0 : ℝ)..s,
              heatSmoothedBilinear6A ν (s - r) (picardLimit ν T₀ (smallDataState ν u₀ (m + 1)) r)
                (picardLimit ν T₀ (smallDataState ν u₀ (m + 1)) r) k c) =
            ∫ r in (0 : ℝ)..s,
              heatSmoothedBilinear6A ν (s - r)
                (smallDataGlobal ν u₀ (((m + 1 : ℕ) : ℝ) * T₀ + r))
                (smallDataGlobal ν u₀ (((m + 1 : ℕ) : ℝ) * T₀ + r)) k c := by
          refine intervalIntegral.integral_congr fun r hr => ?_
          rw [Set.uIcc_of_le hs.1] at hr
          have hru := smallDataGlobal_slab_eq hν hu₀ hsol₀ hsym₀ hzero hsmall₀ (m + 1) ⟨hr.1, le_trans hr.2 hs.2⟩
          rw [← hru]
        exact congrArg ((heatMultiplier3D ν s k : ℂ) * smallDataState ν u₀ (m + 1) k c + ·) hint
      exact duhamelRaw_semigroup_glue u₀ hu_adm hm_end hloc
  intro t ht
  let n : ℕ := Nat.floor (t * (Real.pi ^ 2 * ν))
  have hs_mem : t - (n : ℝ) * T₀ ∈ Set.Icc (0 : ℝ) T₀ := by
    have hfl1 := Nat.floor_le (by positivity : 0 ≤ t * (Real.pi ^ 2 * ν))
    have hfl2 := Nat.lt_floor_add_one (t * (Real.pi ^ 2 * ν))
    have h1 := mul_le_mul_of_nonneg_right hfl1 hT₀_nn
    have h2 := mul_lt_mul_of_pos_right hfl2 hT₀_pos
    dsimp only [T₀] at h1 h2 ⊢
    rw [mul_assoc, mul_one_div_cancel hpiν, mul_one] at h1 h2
    exact ⟨by linarith, by linarith⟩
  have h := hslab n (t - (n : ℝ) * T₀) hs_mem
  have hsum : (n : ℝ) * T₀ + (t - (n : ℝ) * T₀) = t := by ring
  rwa [hsum] at h

/-- **MAIN THEOREM 6 OF MILESTONE 7A (Unconditional Global Existence & Regularity on `[0, ∞)`
    for Small Mean-Zero `H²(𝕋³)` Initial Data, `0 sorryAx`):**
    For EVERY viscosity `ν > 0` and EVERY real, solenoidal, mean-zero initial velocity `u₀ ∈ H²(𝕋³)`
    with `‖u₀‖²_{H²} ≤ π² ν² / 217088`, there EXISTS a global admissible curve `u : ℝ → VecSeq3D`
    with `M = π² ν² / 54272` satisfying for ALL `t ≥ 0`:
    1. `u(0) = u₀`, `‖u(t)‖²_{H²} ≤ M`, `IsSolenoidal (u t)`, `IsRealSymm (u t)`, mean `0`;
    2. Single unbroken global Duhamel equation `u(t) = duhamelRaw ν u₀ u t` for ALL `t ≥ 0`;
    3. Mode-wise 3D Navier–Stokes momentum ODE with Poisson pressure for ALL `t > 0`;
    4. Global continuous `ℤ³`-periodic physical velocity `U(t, x) = synthVec3D (u t) x`
       with `|U(t, x)|² ≤ 53 M` for ALL `t ≥ 0, x ∈ ℝ³`. -/
theorem global_existence_small_data_ns3d_torus3D
    {ν : ℝ} (hν : 0 < ν) {u₀ : VecSeq3D}
    (hu₀ : InH2Vec u₀) (hsol₀ : IsSolenoidal u₀) (hsym₀ : IsRealSymm u₀)
    (hzero : ∀ c : Fin 3, u₀ 0 c = 0)
    (hsmall₀ : h2VecNormSq u₀ ≤ Real.pi ^ 2 * ν ^ 2 / 217088) :
    let M : ℝ := Real.pi ^ 2 * ν ^ 2 / 54272
    ∃ u : ℝ → VecSeq3D,
      IsAdmissibleCurve M u ∧
      u 0 = u₀ ∧
      (∀ t : ℝ, 0 ≤ t → u t = duhamelRaw ν u₀ u t) ∧
      (∀ t : ℝ, 0 < t → ∀ (k : Fin 3 → ℤ) (c : Fin 3),
        HasDerivAt (fun s : ℝ => u s k c)
          ((-4 * (Real.pi : ℂ) ^ 2 * (ν : ℂ) * ((kNormSq k : ℝ) : ℂ)) * u t k c -
            nsFlux6A (u t) (u t) k c -
            2 * (Real.pi : ℂ) * Complex.I * (k c : ℂ) * pressureCoeff6B (u t) k) t) ∧
      (∀ t : ℝ, IsSolenoidal (u t) ∧ IsRealSymm (u t) ∧ (∀ c : Fin 3, u t 0 c = 0)) ∧
      (∀ t : ℝ, Continuous (synthVec3D (u t)) ∧ IsPeriodic3D (synthVec3D (u t)) ∧
        (∀ x : R3, dot3D (synthVec3D (u t) x) (synthVec3D (u t) x) ≤ 53 * M)) := by
  intro M
  have hpair := smallDataGlobal_admissible_and_struct hν hu₀ hsol₀ hsym₀ hzero hsmall₀
  have hduh := smallDataGlobal_duhamel_all hν hu₀ hsol₀ hsym₀ hzero hsmall₀
  refine ⟨smallDataGlobal ν u₀, hpair.1, ?_, hduh, ?_, hpair.2, ?_⟩
  · unfold smallDataGlobal; simp
  · intro t ht k c
    exact mild_solution_hasDerivAt_spectral_ns3d (T := t + 1) u₀ hpair.1
      (fun s hs => hduh s hs.1) ⟨ht, by linarith⟩ k c
  · intro t
    have hsyn := synthVec3D_continuous_periodic_and_Linf (hpair.1.h_inH2 t)
    refine ⟨hsyn.1, hsyn.2.1, fun x => ?_⟩
    have hbd : h2VecNormSq (smallDataGlobal ν u₀ t) ≤ M := hpair.1.h_bound t
    linarith [hsyn.2.2 x, hbd]

-- ============================================================================
-- SECTION 5: AXIOM AUDIT TRAIL — MILESTONE 7A (0 sorryAx)
-- ============================================================================

#print axioms gronwall_exp_integral_bound
#print axioms bkm_gradient_enstrophy_continuation_torus3D
#print axioms bkm_vorticity_envelope_continuation_torus3D
#print axioms classical_ns3d_uniqueness_torus3D
#print axioms duhamelRaw_semigroup_glue
#print axioms global_existence_small_data_ns3d_torus3D

end GarryGlobalRegularity3D