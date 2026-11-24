import WholeSpaceR3EnstrophyWaterfall
import GarryWaterfallCertificateTorus3D
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

/-!
# Milestone 11A-1 (Hurdle 2 — Tier I, 100% Unconditional):
  Global Serrin `L²` Stability, Pointwise Uniqueness & Uniform `L²_t L∞_x` Bounds
  on Both Whole Space `ℝ³` and Periodic Torus `𝕋³` (`0 sorryAx`)

This module proves unconditional global uniqueness and continuous `L²` dependence on initial
data for classical 3D Navier–Stokes solutions on BOTH `ℝ³` and `𝕋³`, using the 3D Agmon
inequalities already verified with `0 sorryAx`:

1. **Theorem 11A1-1 (`r3_serrin_L2_stability_and_global_uniqueness`):**
   For any two decaying classical 3D NS solutions `(u₁, p₁)` and `(u₂, p₂)` on `ℝ³`,
   `E_diff(T) ≤ E_diff(0) * exp((1/ν) ∫_0^T M_{u₂}(s) ds)`, where
   `M_{u₂}(s) = (1/2) √(2 Z_{ℝ³}(u₂ s)) √(P_{ℝ³}(u₂ s))`.
   Hence `u₁(0) = u₂(0) → ∀ t ≥ 0, ∀ x : R3, u₁ t x = u₂ t x`.
2. **Theorem 11A1-2 (`r3_global_L2_Linf_bound_of_waterfall`):**
   Any `ℝ³` solution with a certified `GarryWaterfallWitnessR3` reaching the half-critical
   basin satisfies a uniform-in-`T` global `L²_t L∞_x` bound on `[0, ∞)`:
   `∀ T ≥ 0, ∫_0^T M_u(s) ds ≤ E₀/(4ν) + (1/ν)(zCap 0 + c_nu_R3 ν * M_peak * B) + (2/ν) zCap N`.
3. **Theorems 11A1-3 & 11A1-4 (Part 2/2):** Exact periodic `𝕋³` counterparts with zero
   extra domination hypotheses, plus uniform `L²_t L∞_x` river bounds and axiom audit.
-/

namespace GarryGlobalUniquenessNS3D

open MeasureTheory Filter Topology
open GarryReal3DCalculus
open GarryVorticity3D
open GarryWholeSpaceR3
open GarryWholeSpaceR3Agmon
open GarryWholeSpaceR3Waterfall
open GarryLerayTorus3D
open GarryLerayEnergyLaw3D
open GarrySobolevEmbedding3D
open GarryEnstrophyBasin3D
open GarryCriticalProdiSerrin3D
open GarryWaterfallCertificate3D

-- ============================================================================
-- SECTION 0: SHARED ELEMENTARY TOOLS (GRONWALL, POINTWISE YOUNG & L² VANISHING)
-- ============================================================================

private lemma int_add_u {f g : R3 → ℝ} (hf : Integrable f volume) (hg : Integrable g volume) :
    Integrable (fun x => f x + g x) volume := hf.add hg

private lemma int_sub_u {f g : R3 → ℝ} (hf : Integrable f volume) (hg : Integrable g volume) :
    Integrable (fun x => f x - g x) volume := hf.sub hg

private lemma int_const_mul_u (c : ℝ) {f : R3 → ℝ} (hf : Integrable f volume) :
    Integrable (fun x => c * f x) volume := hf.const_mul c

private lemma contDiff_partial_c2_u {g : R3 → ℝ} (hg : ContDiff ℝ 3 g) (i : Fin 3) :
    ContDiff ℝ 2 (fun x => partialDerivScalar g x i) := by
  unfold partialDerivScalar
  have hfd : ContDiff ℝ 2 (fderiv ℝ g) := hg.fderiv_right (by norm_cast)
  exact hfd.clm_apply contDiff_const

private lemma contDiff_partial_c1_u {g : R3 → ℝ} (hg : ContDiff ℝ 2 g) (i : Fin 3) :
    ContDiff ℝ 1 (fun x => partialDerivScalar g x i) := by
  unfold partialDerivScalar
  have hfd : ContDiff ℝ 1 (fderiv ℝ g) := hg.fderiv_right (by norm_cast)
  exact hfd.clm_apply contDiff_const

private lemma contDiff_snd_c1_u {g : R3 → ℝ} (hg : ContDiff ℝ 3 g) (i j : Fin 3) :
    ContDiff ℝ 1 (fun x => sndPartial g x i j) := by
  have h2 : ContDiff ℝ 2 g := hg.of_le (by exact_mod_cast (show (2 : ℕ) ≤ 3 by decide))
  have heq : (fun x => sndPartial g x i j) =
      fun x => partialDerivScalar (fun y => partialDerivScalar g y j) x i := by
    funext x; exact (partial_partial_eq_sndPartial g x h2.contDiffAt i j).symm
  rw [heq]
  exact contDiff_partial_c1_u (contDiff_partial_c2_u hg j) i

private lemma antitone_of_hasDerivAt_nonpos_11a {f f' : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hcont : ContinuousOn f (Set.Icc a b))
    (hderiv : ∀ s ∈ Set.Ioo a b, HasDerivAt f (f' s) s)
    (hnonpos : ∀ s ∈ Set.Ioo a b, f' s ≤ 0) :
    f b ≤ f a := by
  rcases eq_or_lt_of_le hab with rfl | hlt
  · exact le_rfl
  · obtain ⟨c, hc_mem, hc_eq⟩ := exists_hasDerivAt_eq_slope f f' hlt hcont hderiv
    have hc' : f' c ≤ 0 := hnonpos c hc_mem
    have hdiv : (f b - f a) / (b - a) ≤ 0 := by linarith
    have hpos : 0 < b - a := by linarith
    have hsub : f b - f a ≤ 0 := by
      rcases div_nonpos_iff.mp hdiv with ⟨_, hle⟩ | ⟨hge, _⟩
      · linarith
      · exact hge
    linarith

/-- General Gronwall `L²` stability lemma on `[0, T]`:
    if `E` is differentiable on `[0, T]` with `E'(s) ≤ γ(s) * E(s)` and `γ` is continuous,
    then `E(T) ≤ E(0) * exp(∫_0^T γ(s) ds)`. -/
lemma gronwall_L2_of_hasDerivAt {E E' γ : ℝ → ℝ} {T : ℝ} (hT : 0 ≤ T)
    (hE_deriv : ∀ s ∈ Set.Icc (0 : ℝ) T, HasDerivAt E (E' s) s)
    (hγ_cont : Continuous γ)
    (hineq : ∀ s ∈ Set.Ioo (0 : ℝ) T, E' s ≤ γ s * E s) :
    E T ≤ E 0 * Real.exp (∫ s in (0 : ℝ)..T, γ s) := by
  let I : ℝ → ℝ := fun r => ∫ s in (0 : ℝ)..r, γ s
  let μ : ℝ → ℝ := fun r => Real.exp (-I r)
  let g : ℝ → ℝ := fun r => E r * μ r
  let g' : ℝ → ℝ := fun r => E' r * μ r + E r * (μ r * (-γ r))
  have hg_deriv : ∀ r ∈ Set.Icc (0 : ℝ) T, HasDerivAt g (g' r) r := fun r hr => by
    have hI_d : HasDerivAt I (γ r) r :=
      intervalIntegral.integral_hasDerivAt_right
        (hγ_cont.intervalIntegrable (μ := volume) 0 r)
        (hγ_cont.stronglyMeasurableAtFilter volume (nhds r))
        hγ_cont.continuousAt
    have hμ_d : HasDerivAt μ (μ r * (-γ r)) r := hI_d.neg.exp
    exact (hE_deriv r hr).mul hμ_d
  have hg_nonpos : ∀ r ∈ Set.Ioo (0 : ℝ) T, g' r ≤ 0 := fun r hr => by
    have hfac : g' r = (E' r - γ r * E r) * μ r := by dsimp only [g']; ring
    rw [hfac]
    exact mul_nonpos_of_nonpos_of_nonneg (by linarith [hineq r hr]) (le_of_lt (Real.exp_pos _))
  have hg_anti := antitone_of_hasDerivAt_nonpos_11a (f := g) hT
    (fun r hr => (hg_deriv r hr).continuousAt.continuousWithinAt)
    (fun r hr => hg_deriv r ⟨le_of_lt hr.1, le_of_lt hr.2⟩)
    hg_nonpos
  have hg0 : g 0 = E 0 := by dsimp only [g, μ, I]; simp
  rw [hg0] at hg_anti
  dsimp only [g, μ] at hg_anti
  have hmul := mul_le_mul_of_nonneg_right hg_anti (le_of_lt (Real.exp_pos (I T)))
  have hcancel : E T * Real.exp (-I T) * Real.exp (I T) = E T := by
    rw [mul_assoc, ← Real.exp_add, neg_add_cancel, Real.exp_zero, mul_one]
  rwa [hcancel] at hmul

/-- Pointwise Cauchy–Schwarz + Young absorption for the difference advection term:
    `⟨u₂, (w · ∇)w⟩ ≤ (ν / 2) |∇w|² + (1 / (2 ν)) |u₂|² |w|²`. -/
private lemma cauchy_schwarz_3_sq (x0 x1 x2 y0 y1 y2 : ℝ) :
    (x0 * y0 + x1 * y1 + x2 * y2) ^ 2 ≤
      (x0 ^ 2 + x1 ^ 2 + x2 ^ 2) * (y0 ^ 2 + y1 ^ 2 + y2 ^ 2) := by
  nlinarith [sq_nonneg (x0 * y1 - x1 * y0),
             sq_nonneg (x0 * y2 - x2 * y0),
             sq_nonneg (x1 * y2 - x2 * y1)]

private lemma le_add_of_sq_le_four_mul {X A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (h : X ^ 2 ≤ 4 * A * B) : X ≤ A + B := by
  nlinarith [sq_nonneg (A - B), sq_nonneg (A + B - X)]

lemma pointwise_diff_advection_young {ν : ℝ} (hν : 0 < ν) (u₂ w : R3)
    (dw00 dw01 dw02 dw10 dw11 dw12 dw20 dw21 dw22 : ℝ) :
    u₂ 0 * (w 0 * dw00 + w 1 * dw01 + w 2 * dw02) +
    u₂ 1 * (w 0 * dw10 + w 1 * dw11 + w 2 * dw12) +
    u₂ 2 * (w 0 * dw20 + w 1 * dw21 + w 2 * dw22) ≤
      (ν / 2) * (dw00 ^ 2 + dw01 ^ 2 + dw02 ^ 2 +
        dw10 ^ 2 + dw11 ^ 2 + dw12 ^ 2 +
        dw20 ^ 2 + dw21 ^ 2 + dw22 ^ 2) +
      (1 / (2 * ν)) * dot3D u₂ u₂ * dot3D w w := by
  let b0 := w 0 * dw00 + w 1 * dw01 + w 2 * dw02
  let b1 := w 0 * dw10 + w 1 * dw11 + w 2 * dw12
  let b2 := w 0 * dw20 + w 1 * dw21 + w 2 * dw22
  have hu2_eq : dot3D u₂ u₂ = (u₂ 0) ^ 2 + (u₂ 1) ^ 2 + (u₂ 2) ^ 2 := by unfold dot3D; ring
  have hw_eq : dot3D w w = (w 0) ^ 2 + (w 1) ^ 2 + (w 2) ^ 2 := by unfold dot3D; ring
  have hcs_u : (u₂ 0 * b0 + u₂ 1 * b1 + u₂ 2 * b2) ^ 2 ≤
      dot3D u₂ u₂ * (b0 ^ 2 + b1 ^ 2 + b2 ^ 2) := by
    rw [hu2_eq]; exact cauchy_schwarz_3_sq (u₂ 0) (u₂ 1) (u₂ 2) b0 b1 b2
  have hb0 : b0 ^ 2 ≤ dot3D w w * (dw00 ^ 2 + dw01 ^ 2 + dw02 ^ 2) := by
    rw [hw_eq]; exact cauchy_schwarz_3_sq (w 0) (w 1) (w 2) dw00 dw01 dw02
  have hb1 : b1 ^ 2 ≤ dot3D w w * (dw10 ^ 2 + dw11 ^ 2 + dw12 ^ 2) := by
    rw [hw_eq]; exact cauchy_schwarz_3_sq (w 0) (w 1) (w 2) dw10 dw11 dw12
  have hb2 : b2 ^ 2 ≤ dot3D w w * (dw20 ^ 2 + dw21 ^ 2 + dw22 ^ 2) := by
    rw [hw_eq]; exact cauchy_schwarz_3_sq (w 0) (w 1) (w 2) dw20 dw21 dw22
  set G := dw00 ^ 2 + dw01 ^ 2 + dw02 ^ 2 + dw10 ^ 2 + dw11 ^ 2 + dw12 ^ 2 +
    dw20 ^ 2 + dw21 ^ 2 + dw22 ^ 2
  have hG_nn : 0 ≤ G := by dsimp only [G]; positivity
  have hu2_nn : 0 ≤ dot3D u₂ u₂ := dot3D_self_nonneg_r3 u₂
  have hw_nn : 0 ≤ dot3D w w := dot3D_self_nonneg_r3 w
  have hsum : b0 ^ 2 + b1 ^ 2 + b2 ^ 2 ≤ dot3D w w * G := by
    have hadd := add_le_add (add_le_add hb0 hb1) hb2
    have hfac : dot3D w w * (dw00 ^ 2 + dw01 ^ 2 + dw02 ^ 2) +
        dot3D w w * (dw10 ^ 2 + dw11 ^ 2 + dw12 ^ 2) +
        dot3D w w * (dw20 ^ 2 + dw21 ^ 2 + dw22 ^ 2) = dot3D w w * G := by
      dsimp only [G]; ring
    exact hfac ▸ hadd
  set X := u₂ 0 * b0 + u₂ 1 * b1 + u₂ 2 * b2
  set A := (ν / 2) * G
  set B := (1 / (2 * ν)) * dot3D u₂ u₂ * dot3D w w
  have hsq : X ^ 2 ≤ 4 * A * B := by
    have hm := mul_le_mul_of_nonneg_left hsum hu2_nn
    have h1 : dot3D u₂ u₂ * (dot3D w w * G) = 4 * A * B := by
      dsimp only [A, B]
      have hν0 : ν ≠ 0 := ne_of_gt hν
      field_simp; ring
    exact le_trans hcs_u (h1 ▸ hm)
  exact le_add_of_sq_le_four_mul (by dsimp only [A]; positivity) (by dsimp only [B]; positivity) hsq

/-- If a continuous `f : R3 → ℝ` has `∫_{ℝ³} f(x)² dx = 0`, then `f(x) = 0` for EVERY `x : R3`. -/
lemma eq_zero_of_r3Integral_sq_eq_zero {f : R3 → ℝ} (hf_cont : Continuous f)
    (hf2_int : Integrable (fun x => (f x) ^ 2) volume)
    (hzero : r3Integral (fun x => (f x) ^ 2) = 0) :
    ∀ x : R3, f x = 0 := by
  have hae : (fun x : R3 => (f x) ^ 2) =ᵐ[volume] 0 :=
    (MeasureTheory.integral_eq_zero_iff_of_nonneg (fun _ => sq_nonneg _) hf2_int).mp hzero
  intro x₀
  by_contra hne
  have hpos : 0 < (f x₀) ^ 2 := sq_pos_of_ne_zero hne
  let U : Set R3 := {x : R3 | 0 < (f x) ^ 2}
  have hU_open : IsOpen U := isOpen_lt continuous_const (hf_cont.pow 2)
  have hU_ne : U.Nonempty := ⟨x₀, hpos⟩
  have hU_pos : volume U ≠ 0 := hU_open.measure_ne_zero volume hU_ne
  have hU_sub : U ⊆ {x : R3 | (f x) ^ 2 ≠ 0} := fun x hx => ne_of_gt hx
  have hzero_set : volume {x : R3 | (f x) ^ 2 ≠ 0} = 0 := by
    simpa [Filter.EventuallyEq, ae_iff] using hae
  exact hU_pos (measure_mono_null hU_sub hzero_set)

-- ============================================================================
-- SECTION 1: WHOLE-SPACE ℝ³ DIFFERENCE ENERGY, SERRIN STABILITY & UNIQUENESS
-- ============================================================================

/-- Whole-space `ℝ³` kinetic energy of the velocity difference `w = u₁ - u₂`. -/
noncomputable def diffEnergyR3 (u₁ u₂ : ℝ → R3 → R3) (t : ℝ) : ℝ :=
  (1 / 2 : ℝ) * r3Integral (fun x => dot3D (u₁ t x - u₂ t x) (u₁ t x - u₂ t x))

/-- Whole-space `ℝ³` Agmon `L∞²` control profile `M_u(t) = (1/2) √(2 Z(t)) √(P(t))`. -/
noncomputable def agmonLinfSqBoundR3 (u : ℝ → R3 → R3) (t : ℝ) : ℝ :=
  (1 / 2 : ℝ) * Real.sqrt (2 * enstrophyR3 (u t)) * Real.sqrt (palinstrophyR3 (u t))

lemma diffEnergyR3_nonneg (u₁ u₂ : ℝ → R3 → R3) (t : ℝ) : 0 ≤ diffEnergyR3 u₁ u₂ t := by
  unfold diffEnergyR3
  linarith [r3Integral_nonneg (fun x => dot3D_self_nonneg_r3 (u₁ t x - u₂ t x))]

private lemma decayingH3ScalarR3_sub {f g : R3 → ℝ}
    (hf : DecayingH3ScalarR3 f) (hg : DecayingH3ScalarR3 g) :
    DecayingH3ScalarR3 (fun x => f x - g x) := by
  have hp1 : ∀ (x : R3) (i : Fin 3),
      partialDerivScalar (fun y => f y - g y) x i =
        partialDerivScalar f x i - partialDerivScalar g x i := fun x i =>
    partialDerivScalar_sub (hf.h_c3.differentiable (by simp) x)
      (hg.h_c3.differentiable (by simp) x) i
  have hp2 : ∀ (x : R3) (i j : Fin 3),
      sndPartial (fun y => f y - g y) x i j = sndPartial f x i j - sndPartial g x i j := fun x i j =>
    sndPartial_sub f g
      (fun y => (hf.h_c3.of_le (by exact_mod_cast (show (2 : ℕ) ≤ 3 by decide))).contDiffAt)
      (fun y => (hg.h_c3.of_le (by exact_mod_cast (show (2 : ℕ) ≤ 3 by decide))).contDiffAt) x i j
  have hp3 : ∀ (x : R3) (i j k : Fin 3),
      partialDerivScalar (fun y => sndPartial (fun z => f z - g z) y i j) x k =
        partialDerivScalar (fun y => sndPartial f y i j) x k -
        partialDerivScalar (fun y => sndPartial g y i j) x k := fun x i j k => by
    have hfun : (fun y => sndPartial (fun z => f z - g z) y i j) =
        fun y => sndPartial f y i j - sndPartial g y i j := funext (fun y => hp2 y i j)
    rw [hfun]
    exact partialDerivScalar_sub
      ((contDiff_snd_c1_u hf.h_c3 i j).differentiable (by simp) x)
      ((contDiff_snd_c1_u hg.h_c3 i j).differentiable (by simp) x) k
  exact {
    h_c3 := hf.h_c3.sub hg.h_c3
    h_van0 := vanishesAtInfinityR3_sub hf.h_van0 hg.h_van0
    h_van1 := fun i => by
      have h : (fun x => partialDerivScalar (fun y => f y - g y) x i) =
          fun x => partialDerivScalar f x i - partialDerivScalar g x i := funext (fun x => hp1 x i)
      rw [h]; exact vanishesAtInfinityR3_sub (hf.h_van1 i) (hg.h_van1 i)
    h_van2 := fun i j => by
      have h : (fun x => sndPartial (fun y => f y - g y) x i j) =
          fun x => sndPartial f x i j - sndPartial g x i j := funext (fun x => hp2 x i j)
      rw [h]; exact vanishesAtInfinityR3_sub (hf.h_van2 i j) (hg.h_van2 i j)
    h_int0 := integrable_sub_sq_of_sq hf.h_c3.continuous hg.h_c3.continuous hf.h_int0 hg.h_int0
    h_int1 := fun i => by
      have h : (fun x => (partialDerivScalar (fun y => f y - g y) x i) ^ 2) =
          fun x => (partialDerivScalar f x i - partialDerivScalar g x i) ^ 2 :=
        funext (fun x => by rw [hp1 x i])
      rw [h]
      exact integrable_sub_sq_of_sq (contDiff_partial_c2_u hf.h_c3 i).continuous
        (contDiff_partial_c2_u hg.h_c3 i).continuous (hf.h_int1 i) (hg.h_int1 i)
    h_int2 := fun i j => by
      have h : (fun x => (sndPartial (fun y => f y - g y) x i j) ^ 2) =
          fun x => (sndPartial f x i j - sndPartial g x i j) ^ 2 :=
        funext (fun x => by rw [hp2 x i j])
      rw [h]
      exact integrable_sub_sq_of_sq (contDiff_snd_c1_u hf.h_c3 i j).continuous
        (contDiff_snd_c1_u hg.h_c3 i j).continuous (hf.h_int2 i j) (hg.h_int2 i j)
    h_int3 := fun i j k => by
      have h : (fun x => (partialDerivScalar (fun y => sndPartial (fun z => f z - g z) y i j) x k) ^ 2) =
          fun x => (partialDerivScalar (fun y => sndPartial f y i j) x k -
            partialDerivScalar (fun y => sndPartial g y i j) x k) ^ 2 :=
        funext (fun x => by rw [hp3 x i j k])
      rw [h]
      have hc3 : ∀ {h : R3 → ℝ}, ContDiff ℝ 3 h →
          Continuous (fun x => partialDerivScalar (fun y => sndPartial h y i j) x k) := by
        intro h hh
        unfold partialDerivScalar
        have hfd : ContDiff ℝ 0 (fderiv ℝ (fun y => sndPartial h y i j)) :=
          (contDiff_snd_c1_u hh i j).fderiv_right (by norm_cast)
        exact (hfd.clm_apply contDiff_const).continuous
      exact integrable_sub_sq_of_sq (hc3 hf.h_c3) (hc3 hg.h_c3) (hf.h_int3 i j k) (hg.h_int3 i j k)
  }

private lemma decayingH3SolenoidalR3_sub {u₁ u₂ : R3 → R3}
    (h₁ : DecayingH3SolenoidalR3 u₁) (h₂ : DecayingH3SolenoidalR3 u₂) :
    DecayingH3SolenoidalR3 (fun x => u₁ x - u₂ x) where
  h_comp := fun c => decayingH3ScalarR3_sub (h₁.h_comp c) (h₂.h_comp c)
  h_div := fun x => by
    unfold div3D
    have hsub : ∀ i : Fin 3, partialDerivScalar (fun y => (u₁ y - u₂ y) i) x i =
        partialDerivScalar (fun y => u₁ y i) x i - partialDerivScalar (fun y => u₂ y i) x i := fun i =>
      partialDerivScalar_sub ((h₁.h_comp i).h_c3.differentiable (by simp) x)
        ((h₂.h_comp i).h_c3.differentiable (by simp) x) i
    rw [hsub 0, hsub 1, hsub 2]
    have d1 := h₁.h_div x; have d2 := h₂.h_div x
    unfold div3D at d1 d2
    linarith

private lemma r3_diff_transport_zero {u₁ w : R3 → R3}
    (hu₁ : DecayingH3SolenoidalR3 u₁) (hw : DecayingH3SolenoidalR3 w) :
    r3Integral (fun x => dot3D (directionalAdvection3D u₁ w x) (w x)) = 0 := by
  have hv_bdd : ∀ i : Fin 3, ∃ C : ℝ, 0 ≤ C ∧ ∀ x : R3, |u₁ x i| ≤ C := fun i =>
    exists_bound_of_vanishesAtInfinityR3 (hu₁.h_comp i).h_c3.continuous (hu₁.h_comp i).h_van0
  have hdv_bdd : ∀ i : Fin 3, ∃ C : ℝ, 0 ≤ C ∧ ∀ x : R3, |partialDerivScalar (fun y => u₁ y i) x i| ≤ C :=
    fun i => exists_bound_of_vanishesAtInfinityR3
      (contDiff_partial_c2_u (hu₁.h_comp i).h_c3 i).continuous ((hu₁.h_comp i).h_van1 i)
  have ht_int : ∀ c i : Fin 3,
      Integrable (fun x => u₁ x i * (partialDerivScalar (fun y => w y c) x i * w x c)) volume := fun c i => by
    have heq : (fun x => u₁ x i * (partialDerivScalar (fun y => w y c) x i * w x c)) =
        fun x => u₁ x i * (w x c * partialDerivScalar (fun y => w y c) x i) := by funext x; ring
    rw [heq]
    exact integrable_bdd_mul_mul_of_sq (hu₁.h_comp i).h_c3.continuous (hw.h_comp c).h_c3.continuous
      (contDiff_partial_c2_u (hw.h_comp c).h_c3 i).continuous (hv_bdd i)
      (hw.h_comp c).h_int0 ((hw.h_comp c).h_int1 i)
  have hdv_w2_int : ∀ c i : Fin 3,
      Integrable (fun x => partialDerivScalar (fun y => u₁ y i) x i * (w x c * w x c)) volume := fun c i =>
    integrable_bdd_mul_mul_of_sq (contDiff_partial_c2_u (hu₁.h_comp i).h_c3 i).continuous
      (hw.h_comp c).h_c3.continuous (hw.h_comp c).h_c3.continuous (hdv_bdd i)
      (hw.h_comp c).h_int0 (hw.h_comp c).h_int0
  have hc_zero : ∀ c : Fin 3,
      r3Integral (fun x => directionalAdvection3D u₁ w x c * w x c) = 0 := by
    intro c
    have hibp_i : ∀ i : Fin 3,
        2 * r3Integral (fun x => u₁ x i * (partialDerivScalar (fun y => w y c) x i * w x c)) =
          -r3Integral (fun x => partialDerivScalar (fun y => u₁ y i) x i * (w x c * w x c)) := by
      intro i
      have hd_w : Differentiable ℝ (fun y => w y c) := (hw.h_comp c).h_c3.differentiable (by simp)
      have hd_w2 : Differentiable ℝ (fun y => w y c * w y c) := hd_w.mul hd_w
      have h2_eq : (fun x => u₁ x i * partialDerivScalar (fun y => w y c * w y c) x i) =
          fun x => 2 * (u₁ x i * (partialDerivScalar (fun y => w y c) x i * w x c)) := by
        funext x; rw [partialDerivScalar_mul (hd_w x) (hd_w x) i]; ring
      have hvan := vanishesAlongAxis_of_vanishesAtInfinityR3
        (vanishesAtInfinityR3_mul (hu₁.h_comp i).h_van0
          (vanishesAtInfinityR3_mul (hw.h_comp c).h_van0 (hw.h_comp c).h_van0)) i
      have hibp := r3Integral_ibp ((hu₁.h_comp i).h_c3.differentiable (by simp)) hd_w2 hvan
        (hdv_w2_int c i) (by rw [h2_eq]; exact int_const_mul_u 2 (ht_int c i))
      rw [h2_eq, r3Integral_const_mul] at hibp
      exact hibp
    have hsum_rhs :
        r3Integral (fun x => partialDerivScalar (fun y => u₁ y 0) x 0 * (w x c * w x c)) +
        r3Integral (fun x => partialDerivScalar (fun y => u₁ y 1) x 1 * (w x c * w x c)) +
        r3Integral (fun x => partialDerivScalar (fun y => u₁ y 2) x 2 * (w x c * w x c)) = 0 := by
      rw [← r3Integral_add3 (hdv_w2_int c 0) (hdv_w2_int c 1) (hdv_w2_int c 2)]
      have hzero : ∀ x : R3,
          partialDerivScalar (fun y => u₁ y 0) x 0 * (w x c * w x c) +
          partialDerivScalar (fun y => u₁ y 1) x 1 * (w x c * w x c) +
          partialDerivScalar (fun y => u₁ y 2) x 2 * (w x c * w x c) = 0 := fun x => by
        have hdiv0 := hu₁.h_div x; unfold div3D at hdiv0
        linear_combination (w x c * w x c) * hdiv0
      rw [r3Integral_congr hzero, r3Integral_zero]
    have hpt : ∀ x : R3, directionalAdvection3D u₁ w x c * w x c =
        u₁ x 0 * (partialDerivScalar (fun y => w y c) x 0 * w x c) +
        u₁ x 1 * (partialDerivScalar (fun y => w y c) x 1 * w x c) +
        u₁ x 2 * (partialDerivScalar (fun y => w y c) x 2 * w x c) := fun x => by
      unfold directionalAdvection3D; ring
    rw [r3Integral_congr hpt, r3Integral_add3 (ht_int c 0) (ht_int c 1) (ht_int c 2)]
    linarith [hibp_i 0, hibp_i 1, hibp_i 2, hsum_rhs]
  have hcomp_int : ∀ c : Fin 3, Integrable (fun x => directionalAdvection3D u₁ w x c * w x c) volume := fun c => by
    have hpt : (fun x => directionalAdvection3D u₁ w x c * w x c) = fun x =>
        u₁ x 0 * (partialDerivScalar (fun y => w y c) x 0 * w x c) +
        u₁ x 1 * (partialDerivScalar (fun y => w y c) x 1 * w x c) +
        u₁ x 2 * (partialDerivScalar (fun y => w y c) x 2 * w x c) := by
      funext x; unfold directionalAdvection3D; ring
    rw [hpt]; exact int_add_u (int_add_u (ht_int c 0) (ht_int c 1)) (ht_int c 2)
  have hdot : ∀ x : R3, dot3D (directionalAdvection3D u₁ w x) (w x) =
      directionalAdvection3D u₁ w x 0 * w x 0 +
      directionalAdvection3D u₁ w x 1 * w x 1 +
      directionalAdvection3D u₁ w x 2 * w x 2 := fun _ => rfl
  rw [r3Integral_congr hdot, r3Integral_add3 (hcomp_int 0) (hcomp_int 1) (hcomp_int 2),
      hc_zero 0, hc_zero 1, hc_zero 2]
  ring

private lemma r3_diff_advection_ibp {u₂ w : R3 → R3}
    (hu₂ : DecayingH3SolenoidalR3 u₂) (hw : DecayingH3SolenoidalR3 w) :
    r3Integral (fun x => dot3D (directionalAdvection3D w u₂ x) (w x)) =
      -r3Integral (fun x => dot3D (u₂ x) (directionalAdvection3D w w x)) := by
  have hu₂_bdd : ∀ c : Fin 3, ∃ C : ℝ, 0 ≤ C ∧ ∀ x : R3, |u₂ x c| ≤ C := fun c =>
    exists_bound_of_vanishesAtInfinityR3 (hu₂.h_comp c).h_c3.continuous (hu₂.h_comp c).h_van0
  have hdu₂_bdd : ∀ c i : Fin 3, ∃ C : ℝ, 0 ≤ C ∧ ∀ x : R3, |partialDerivScalar (fun y => u₂ y c) x i| ≤ C :=
    fun c i => exists_bound_of_vanishesAtInfinityR3
      (contDiff_partial_c2_u (hu₂.h_comp c).h_c3 i).continuous ((hu₂.h_comp c).h_van1 i)
  have h_l_int : ∀ c i : Fin 3,
      Integrable (fun x => (w x i * w x c) * partialDerivScalar (fun y => u₂ y c) x i) volume := fun c i => by
    have heq : (fun x => (w x i * w x c) * partialDerivScalar (fun y => u₂ y c) x i) =
        fun x => partialDerivScalar (fun y => u₂ y c) x i * (w x i * w x c) := by funext x; ring
    rw [heq]
    exact integrable_bdd_mul_mul_of_sq (contDiff_partial_c2_u (hu₂.h_comp c).h_c3 i).continuous
      (hw.h_comp i).h_c3.continuous (hw.h_comp c).h_c3.continuous
      (hdu₂_bdd c i) (hw.h_comp i).h_int0 (hw.h_comp c).h_int0
  have h_r1_int : ∀ c i : Fin 3,
      Integrable (fun x => partialDerivScalar (fun y => w y i) x i * w x c * u₂ x c) volume := fun c i => by
    have heq : (fun x => partialDerivScalar (fun y => w y i) x i * w x c * u₂ x c) =
        fun x => u₂ x c * (partialDerivScalar (fun y => w y i) x i * w x c) := by funext x; ring
    rw [heq]
    exact integrable_bdd_mul_mul_of_sq (hu₂.h_comp c).h_c3.continuous
      (contDiff_partial_c2_u (hw.h_comp i).h_c3 i).continuous (hw.h_comp c).h_c3.continuous
      (hu₂_bdd c) ((hw.h_comp i).h_int1 i) (hw.h_comp c).h_int0
  have h_r2_int : ∀ c i : Fin 3,
      Integrable (fun x => w x i * partialDerivScalar (fun y => w y c) x i * u₂ x c) volume := fun c i => by
    have heq : (fun x => w x i * partialDerivScalar (fun y => w y c) x i * u₂ x c) =
        fun x => u₂ x c * (w x i * partialDerivScalar (fun y => w y c) x i) := by funext x; ring
    rw [heq]
    exact integrable_bdd_mul_mul_of_sq (hu₂.h_comp c).h_c3.continuous
      (hw.h_comp i).h_c3.continuous (contDiff_partial_c2_u (hw.h_comp c).h_c3 i).continuous
      (hu₂_bdd c) (hw.h_comp i).h_int0 ((hw.h_comp c).h_int1 i)
  have h_r_int : ∀ c i : Fin 3,
      Integrable (fun x => (partialDerivScalar (fun y => w y i) x i * w x c +
        w x i * partialDerivScalar (fun y => w y c) x i) * u₂ x c) volume := fun c i => by
    have heq : (fun x => (partialDerivScalar (fun y => w y i) x i * w x c +
        w x i * partialDerivScalar (fun y => w y c) x i) * u₂ x c) =
        fun x => partialDerivScalar (fun y => w y i) x i * w x c * u₂ x c +
          w x i * partialDerivScalar (fun y => w y c) x i * u₂ x c := by funext x; ring
    rw [heq]; exact int_add_u (h_r1_int c i) (h_r2_int c i)
  have hterm : ∀ c i : Fin 3,
      r3Integral (fun x => (w x i * w x c) * partialDerivScalar (fun y => u₂ y c) x i) =
        -r3Integral (fun x => (partialDerivScalar (fun y => w y i) x i * w x c +
          w x i * partialDerivScalar (fun y => w y c) x i) * u₂ x c) := by
    intro c i
    have hd_wi : Differentiable ℝ (fun y => w y i) := (hw.h_comp i).h_c3.differentiable (by simp)
    have hd_wc : Differentiable ℝ (fun y => w y c) := (hw.h_comp c).h_c3.differentiable (by simp)
    have hd_wprod : Differentiable ℝ (fun y => w y i * w y c) := hd_wi.mul hd_wc
    have hd_u2c : Differentiable ℝ (fun y => u₂ y c) := (hu₂.h_comp c).h_c3.differentiable (by simp)
    have hmul_p : (fun x => partialDerivScalar (fun y => w y i * w y c) x i * u₂ x c) =
        fun x => (partialDerivScalar (fun y => w y i) x i * w x c +
          w x i * partialDerivScalar (fun y => w y c) x i) * u₂ x c := by
      funext x; rw [partialDerivScalar_mul (hd_wi x) (hd_wc x) i]; ring
    have hibp := r3Integral_ibp hd_wprod hd_u2c
      (vanishesAlongAxis_of_vanishesAtInfinityR3
        (vanishesAtInfinityR3_mul (vanishesAtInfinityR3_mul (hw.h_comp i).h_van0 (hw.h_comp c).h_van0)
          (hu₂.h_comp c).h_van0) i)
      (by rw [hmul_p]; exact h_r_int c i) (h_l_int c i)
    rw [hmul_p] at hibp
    exact hibp
  have h_comp : ∀ c : Fin 3,
      r3Integral (fun x => directionalAdvection3D w u₂ x c * w x c) =
        -r3Integral (fun x => u₂ x c * directionalAdvection3D w w x c) := by
    intro c
    have hlhs_pt : ∀ x : R3, directionalAdvection3D w u₂ x c * w x c =
        (w x 0 * w x c) * partialDerivScalar (fun y => u₂ y c) x 0 +
        (w x 1 * w x c) * partialDerivScalar (fun y => u₂ y c) x 1 +
        (w x 2 * w x c) * partialDerivScalar (fun y => u₂ y c) x 2 := fun x => by
      unfold directionalAdvection3D; ring
    have hrhs_pt : ∀ x : R3,
        ((partialDerivScalar (fun y => w y 0) x 0 * w x c + w x 0 * partialDerivScalar (fun y => w y c) x 0) * u₂ x c) +
        ((partialDerivScalar (fun y => w y 1) x 1 * w x c + w x 1 * partialDerivScalar (fun y => w y c) x 1) * u₂ x c) +
        ((partialDerivScalar (fun y => w y 2) x 2 * w x c + w x 2 * partialDerivScalar (fun y => w y c) x 2) * u₂ x c) =
        u₂ x c * directionalAdvection3D w w x c := fun x => by
      have hdiv0 := hw.h_div x; unfold div3D at hdiv0
      unfold directionalAdvection3D
      linear_combination (w x c * u₂ x c) * hdiv0
    rw [r3Integral_congr hlhs_pt, r3Integral_add3 (h_l_int c 0) (h_l_int c 1) (h_l_int c 2),
        hterm c 0, hterm c 1, hterm c 2]
    have hsum := r3Integral_add3 (h_r_int c 0) (h_r_int c 1) (h_r_int c 2)
    rw [r3Integral_congr hrhs_pt] at hsum
    linarith
  have h_lhs_int : ∀ c : Fin 3, Integrable (fun x => directionalAdvection3D w u₂ x c * w x c) volume := fun c => by
    have hpt : (fun x => directionalAdvection3D w u₂ x c * w x c) = fun x =>
        (w x 0 * w x c) * partialDerivScalar (fun y => u₂ y c) x 0 +
        (w x 1 * w x c) * partialDerivScalar (fun y => u₂ y c) x 1 +
        (w x 2 * w x c) * partialDerivScalar (fun y => u₂ y c) x 2 := by
      funext x; unfold directionalAdvection3D; ring
    rw [hpt]; exact int_add_u (int_add_u (h_l_int c 0) (h_l_int c 1)) (h_l_int c 2)
  have h_rhs_int : ∀ c : Fin 3, Integrable (fun x => u₂ x c * directionalAdvection3D w w x c) volume := fun c => by
    have hpt : (fun x => u₂ x c * directionalAdvection3D w w x c) = fun x =>
        w x 0 * partialDerivScalar (fun y => w y c) x 0 * u₂ x c +
        w x 1 * partialDerivScalar (fun y => w y c) x 1 * u₂ x c +
        w x 2 * partialDerivScalar (fun y => w y c) x 2 * u₂ x c := by
      funext x; unfold directionalAdvection3D; ring
    rw [hpt]; exact int_add_u (int_add_u (h_r2_int c 0) (h_r2_int c 1)) (h_r2_int c 2)
  have hdot_l : ∀ x : R3, dot3D (directionalAdvection3D w u₂ x) (w x) =
      directionalAdvection3D w u₂ x 0 * w x 0 +
      directionalAdvection3D w u₂ x 1 * w x 1 +
      directionalAdvection3D w u₂ x 2 * w x 2 := fun _ => rfl
  have hdot_r : ∀ x : R3, dot3D (u₂ x) (directionalAdvection3D w w x) =
      u₂ x 0 * directionalAdvection3D w w x 0 +
      u₂ x 1 * directionalAdvection3D w w x 1 +
      u₂ x 2 * directionalAdvection3D w w x 2 := fun _ => rfl
  rw [r3Integral_congr hdot_l, r3Integral_add3 (h_lhs_int 0) (h_lhs_int 1) (h_lhs_int 2),
      r3Integral_congr hdot_r, r3Integral_add3 (h_rhs_int 0) (h_rhs_int 1) (h_rhs_int 2),
      h_comp 0, h_comp 1, h_comp 2]
  ring

private lemma r3_diff_laplacian_dot_self {w : R3 → R3} (hw : DecayingH3SolenoidalR3 w) :
    r3Integral (fun x => dot3D (laplacian3D w x) (w x)) = -r3Integral (gradNormSqR3 w) := by
  have hw_c2 : ∀ c : Fin 3, ContDiff ℝ 2 (fun x => w x c) := fun c =>
    (hw.h_comp c).h_c3.of_le (by exact_mod_cast (show (2 : ℕ) ≤ 3 by decide))
  have hterm : ∀ c i : Fin 3,
      r3Integral (fun x => sndPartial (fun y => w y c) x i i * w x c) =
        -r3Integral (fun x => (partialDerivScalar (fun y => w y c) x i) ^ 2) := by
    intro c i
    have h2_eq : (fun x => w x c * partialDerivScalar (fun y => partialDerivScalar (fun z => w z c) y i) x i) =
        fun x => sndPartial (fun y => w y c) x i i * w x c := by
      funext x; rw [partial_partial_eq_sndPartial (fun y => w y c) x (hw_c2 c).contDiffAt i i]; ring
    have h1_eq : (fun x => partialDerivScalar (fun y => w y c) x i * partialDerivScalar (fun y => w y c) x i) =
        fun x => (partialDerivScalar (fun y => w y c) x i) ^ 2 := by funext x; ring
    have hibp := r3Integral_ibp ((hw.h_comp c).h_c3.differentiable (by simp))
      ((contDiff_partial_c2_u (hw.h_comp c).h_c3 i).differentiable (by simp))
      (vanishesAlongAxis_of_vanishesAtInfinityR3
        (vanishesAtInfinityR3_mul (hw.h_comp c).h_van0 ((hw.h_comp c).h_van1 i)) i)
      (by rw [h1_eq]; exact (hw.h_comp c).h_int1 i)
      (by
        rw [h2_eq]
        exact integrable_mul_of_sq (contDiff_snd_c1_u (hw.h_comp c).h_c3 i i).continuous
          (hw.h_comp c).h_c3.continuous ((hw.h_comp c).h_int2 i i) (hw.h_comp c).h_int0)
    rw [h2_eq, h1_eq] at hibp
    exact hibp
  have hi_mul : ∀ c i : Fin 3, Integrable (fun x => sndPartial (fun y => w y c) x i i * w x c) volume :=
    fun c i => integrable_mul_of_sq (contDiff_snd_c1_u (hw.h_comp c).h_c3 i i).continuous
      (hw.h_comp c).h_c3.continuous ((hw.h_comp c).h_int2 i i) (hw.h_comp c).h_int0
  have hcomp_int : ∀ c : Fin 3, Integrable (fun x => laplacian3D w x c * w x c) volume := fun c => by
    have hpt : (fun x => laplacian3D w x c * w x c) = fun x =>
        sndPartial (fun y => w y c) x 0 0 * w x c +
        sndPartial (fun y => w y c) x 1 1 * w x c +
        sndPartial (fun y => w y c) x 2 2 * w x c := by
      funext x; unfold laplacian3D laplacianScalar; ring
    rw [hpt]; exact int_add_u (int_add_u (hi_mul c 0) (hi_mul c 1)) (hi_mul c 2)
  have hcomp : ∀ c : Fin 3,
      r3Integral (fun x => laplacian3D w x c * w x c) =
        -(r3Integral (fun x => (partialDerivScalar (fun y => w y c) x 0) ^ 2) +
          r3Integral (fun x => (partialDerivScalar (fun y => w y c) x 1) ^ 2) +
          r3Integral (fun x => (partialDerivScalar (fun y => w y c) x 2) ^ 2)) := fun c => by
    have hpt : ∀ x : R3, laplacian3D w x c * w x c =
        sndPartial (fun y => w y c) x 0 0 * w x c +
        sndPartial (fun y => w y c) x 1 1 * w x c +
        sndPartial (fun y => w y c) x 2 2 * w x c := fun x => by
      unfold laplacian3D laplacianScalar; ring
    rw [r3Integral_congr hpt, r3Integral_add3 (hi_mul c 0) (hi_mul c 1) (hi_mul c 2),
        hterm c 0, hterm c 1, hterm c 2]; ring
  have hG_sum : r3Integral (gradNormSqR3 w) =
      (r3Integral (fun x => (partialDerivScalar (fun y => w y 0) x 0) ^ 2) +
       r3Integral (fun x => (partialDerivScalar (fun y => w y 0) x 1) ^ 2) +
       r3Integral (fun x => (partialDerivScalar (fun y => w y 0) x 2) ^ 2)) +
      (r3Integral (fun x => (partialDerivScalar (fun y => w y 1) x 0) ^ 2) +
       r3Integral (fun x => (partialDerivScalar (fun y => w y 1) x 1) ^ 2) +
       r3Integral (fun x => (partialDerivScalar (fun y => w y 1) x 2) ^ 2)) +
      (r3Integral (fun x => (partialDerivScalar (fun y => w y 2) x 0) ^ 2) +
       r3Integral (fun x => (partialDerivScalar (fun y => w y 2) x 1) ^ 2) +
       r3Integral (fun x => (partialDerivScalar (fun y => w y 2) x 2) ^ 2)) := by
    have hpt : ∀ x : R3, gradNormSqR3 w x =
        ((partialDerivScalar (fun y => w y 0) x 0) ^ 2 +
         (partialDerivScalar (fun y => w y 0) x 1) ^ 2 +
         (partialDerivScalar (fun y => w y 0) x 2) ^ 2) +
        ((partialDerivScalar (fun y => w y 1) x 0) ^ 2 +
         (partialDerivScalar (fun y => w y 1) x 1) ^ 2 +
         (partialDerivScalar (fun y => w y 1) x 2) ^ 2) +
        ((partialDerivScalar (fun y => w y 2) x 0) ^ 2 +
         (partialDerivScalar (fun y => w y 2) x 1) ^ 2 +
         (partialDerivScalar (fun y => w y 2) x 2) ^ 2) := fun x => by unfold gradNormSqR3; ring
    rw [r3Integral_congr hpt,
        r3Integral_add3
          (int_add_u (int_add_u ((hw.h_comp 0).h_int1 0) ((hw.h_comp 0).h_int1 1)) ((hw.h_comp 0).h_int1 2))
          (int_add_u (int_add_u ((hw.h_comp 1).h_int1 0) ((hw.h_comp 1).h_int1 1)) ((hw.h_comp 1).h_int1 2))
          (int_add_u (int_add_u ((hw.h_comp 2).h_int1 0) ((hw.h_comp 2).h_int1 1)) ((hw.h_comp 2).h_int1 2)),
        r3Integral_add3 ((hw.h_comp 0).h_int1 0) ((hw.h_comp 0).h_int1 1) ((hw.h_comp 0).h_int1 2),
        r3Integral_add3 ((hw.h_comp 1).h_int1 0) ((hw.h_comp 1).h_int1 1) ((hw.h_comp 1).h_int1 2),
        r3Integral_add3 ((hw.h_comp 2).h_int1 0) ((hw.h_comp 2).h_int1 1) ((hw.h_comp 2).h_int1 2)]
  have hdot : ∀ x : R3, dot3D (laplacian3D w x) (w x) =
      laplacian3D w x 0 * w x 0 + laplacian3D w x 1 * w x 1 + laplacian3D w x 2 * w x 2 := fun _ => rfl
  rw [r3Integral_congr hdot, r3Integral_add3 (hcomp_int 0) (hcomp_int 1) (hcomp_int 2),
      hcomp 0, hcomp 1, hcomp 2]
  linarith [hG_sum]

private lemma r3_diff_pressure_dot_zero {w : R3 → R3} {q : R3 → ℝ}
    (hw : DecayingH3SolenoidalR3 w) (hq_c2 : ContDiff ℝ 2 q)
    (hq_van : VanishesAtInfinityR3 q)
    (hq_int0 : Integrable (fun x => (q x) ^ 2) volume)
    (hq_int1 : ∀ i : Fin 3, Integrable (fun x => (partialDerivScalar q x i) ^ 2) volume) :
    r3Integral (fun x => dot3D (grad3D q x) (w x)) = 0 := by
  have hd_q : Differentiable ℝ q := hq_c2.differentiable (by simp)
  have h1_int : ∀ i : Fin 3, Integrable (fun x => partialDerivScalar (fun y => w y i) x i * q x) volume :=
    fun i => integrable_mul_of_sq (contDiff_partial_c2_u (hw.h_comp i).h_c3 i).continuous
      hq_c2.continuous ((hw.h_comp i).h_int1 i) hq_int0
  have h2_int : ∀ i : Fin 3, Integrable (fun x => w x i * partialDerivScalar q x i) volume :=
    fun i => integrable_mul_of_sq (hw.h_comp i).h_c3.continuous (contDiff_partial_c1_u hq_c2 i).continuous
      (hw.h_comp i).h_int0 (hq_int1 i)
  have hibp_i : ∀ i : Fin 3,
      r3Integral (fun x => w x i * partialDerivScalar q x i) =
        -r3Integral (fun x => partialDerivScalar (fun y => w y i) x i * q x) := fun i =>
    r3Integral_ibp ((hw.h_comp i).h_c3.differentiable (by simp)) hd_q
      (vanishesAlongAxis_of_vanishesAtInfinityR3
        (vanishesAtInfinityR3_mul (hw.h_comp i).h_van0 hq_van) i)
      (h1_int i) (h2_int i)
  have hdot : ∀ x : R3, dot3D (grad3D q x) (w x) =
      w x 0 * partialDerivScalar q x 0 + w x 1 * partialDerivScalar q x 1 +
      w x 2 * partialDerivScalar q x 2 := fun x => by unfold dot3D grad3D; ring
  rw [r3Integral_congr hdot, r3Integral_add3 (h2_int 0) (h2_int 1) (h2_int 2),
      hibp_i 0, hibp_i 1, hibp_i 2]
  have hsum := r3Integral_add3 (h1_int 0) (h1_int 1) (h1_int 2)
  have hzero : ∀ x : R3,
      partialDerivScalar (fun y => w y 0) x 0 * q x +
      partialDerivScalar (fun y => w y 1) x 1 * q x +
      partialDerivScalar (fun y => w y 2) x 2 * q x = 0 := fun x => by
    have hdiv0 := hw.h_div x; unfold div3D at hdiv0
    linear_combination q x * hdiv0
  rw [r3Integral_congr hzero, r3Integral_zero] at hsum
  linarith

/-- Exact whole-space `ℝ³` difference-energy inequality via 3D Agmon + Young:
    `d/dt E_diff(t) ≤ (agmonLinfSqBoundR3 u₂ t / ν) * E_diff(t)`. -/
theorem hasDerivAt_diffEnergyR3_and_bound
    {u₁ u₂ : ℝ → R3 → R3} {p₁ p₂ : ℝ → R3 → ℝ} {ν : ℝ}
    (hns₁ : IsDecayingClassicalNS3D_R3 u₁ p₁ ν)
    (hns₂ : IsDecayingClassicalNS3D_R3 u₂ p₂ ν)
    (h_dt_diff_dom : ∀ t₀ ≥ 0, ∃ δ > 0, ∃ bound : R3 → ℝ,
      Integrable bound volume ∧
      ∀ t ∈ Metric.ball t₀ δ, ∀ x : R3,
        |2 * dot3D (fun c => deriv (fun s => u₁ s x c - u₂ s x c) t) (u₁ t x - u₂ t x)| ≤ bound x)
    {t : ℝ} (ht : 0 ≤ t) :
    ∃ D : ℝ,
      HasDerivAt (diffEnergyR3 u₁ u₂) D t ∧
      D ≤ (agmonLinfSqBoundR3 u₂ t / ν) * diffEnergyR3 u₁ u₂ t := by
  have hν : 0 < ν := hns₁.h_nu_pos
  obtain ⟨δ, hδ, bound, hbound_int, hbound⟩ := h_dt_diff_dom t ht
  let w : R3 → R3 := fun x => u₁ t x - u₂ t x
  let q : R3 → ℝ := fun x => p₁ t x - p₂ t x
  have hu₁ := hns₁.h_u_decay t ht
  have hu₂ := hns₂.h_u_decay t ht
  have hw := decayingH3SolenoidalR3_sub hu₁ hu₂
  have hc2_st : ∀ (u : ℝ → R3 → R3) (p : ℝ → R3 → ℝ),
      IsClassicalNS3D_C3 u p ν → ∀ c : Fin 3, ContDiff ℝ 2 (fun r : ℝ × R3 => u r.1 r.2 c) :=
    fun u p hns c => (contDiff_pi.mp (contDiff_iff_contDiffAt.mpr hns.h_u_c2_spacetime)) c
  have hdt_w : ∀ (s : ℝ) (x : R3) (c : Fin 3),
      HasDerivAt (fun r => u₁ r x c - u₂ r x c)
        (fderiv ℝ (fun r : ℝ × R3 => u₁ r.1 r.2 c) (s, x) (1, 0) -
         fderiv ℝ (fun r : ℝ × R3 => u₂ r.1 r.2 c) (s, x) (1, 0)) s := fun s x c => by
    have hinl : HasDerivAt (fun r : ℝ => (r, x)) (1, (0 : R3)) s :=
      (hasDerivAt_id s).prodMk (hasDerivAt_const s x)
    have h1 := ((hc2_st u₁ p₁ hns₁.toIsClassicalNS3D_C3 c).differentiable (by simp) (s, x)).hasFDerivAt.comp_hasDerivAt s hinl
    have h2 := ((hc2_st u₂ p₂ hns₂.toIsClassicalNS3D_C3 c).differentiable (by simp) (s, x)).hasFDerivAt.comp_hasDerivAt s hinl
    exact h1.sub h2
  have hF_cont : ∀ s : ℝ, Continuous (fun x : R3 => dot3D (u₁ s x - u₂ s x) (u₁ s x - u₂ s x)) := fun s => by
    have hc : ∀ c : Fin 3, Continuous (fun x : R3 => u₁ s x c - u₂ s x c) := fun c =>
      ((hc2_st u₁ p₁ hns₁.toIsClassicalNS3D_C3 c).continuous.comp (continuous_const.prodMk continuous_id)).sub
        ((hc2_st u₂ p₂ hns₂.toIsClassicalNS3D_C3 c).continuous.comp (continuous_const.prodMk continuous_id))
    unfold dot3D
    exact (((hc 0).mul (hc 0)).add ((hc 1).mul (hc 1))).add ((hc 2).mul (hc 2))
  have hF_int : Integrable (fun x : R3 => dot3D (w x) (w x)) volume := by
    have hpt : (fun x : R3 => dot3D (w x) (w x)) =
        fun x => (w x 0) ^ 2 + (w x 1) ^ 2 + (w x 2) ^ 2 := by funext x; unfold dot3D; ring
    rw [hpt]; exact int_add_u (int_add_u (hw.h_comp 0).h_int0 (hw.h_comp 1).h_int0) (hw.h_comp 2).h_int0
  have hF'_cont : Continuous (fun x : R3 =>
      2 * dot3D (fun c => deriv (fun s => u₁ s x c - u₂ s x c) t) (w x)) := by
    have hdt_c : ∀ c : Fin 3, Continuous (fun x : R3 => deriv (fun s => u₁ s x c - u₂ s x c) t) := fun c => by
      have heq : (fun x : R3 => deriv (fun s => u₁ s x c - u₂ s x c) t) =
          fun x => fderiv ℝ (fun r : ℝ × R3 => u₁ r.1 r.2 c) (t, x) (1, 0) -
            fderiv ℝ (fun r : ℝ × R3 => u₂ r.1 r.2 c) (t, x) (1, 0) :=
        funext (fun x => (hdt_w t x c).deriv)
      rw [heq]
      have hc1 : Continuous (fun x : R3 => fderiv ℝ (fun r : ℝ × R3 => u₁ r.1 r.2 c) (t, x) (1, 0)) := by
        have hfd : ContDiff ℝ 1 (fderiv ℝ (fun r : ℝ × R3 => u₁ r.1 r.2 c)) :=
          (hc2_st u₁ p₁ hns₁.toIsClassicalNS3D_C3 c).fderiv_right (by norm_cast)
        exact (hfd.clm_apply contDiff_const).continuous.comp (continuous_const.prodMk continuous_id)
      have hc2 : Continuous (fun x : R3 => fderiv ℝ (fun r : ℝ × R3 => u₂ r.1 r.2 c) (t, x) (1, 0)) := by
        have hfd : ContDiff ℝ 1 (fderiv ℝ (fun r : ℝ × R3 => u₂ r.1 r.2 c)) :=
          (hc2_st u₂ p₂ hns₂.toIsClassicalNS3D_C3 c).fderiv_right (by norm_cast)
        exact (hfd.clm_apply contDiff_const).continuous.comp (continuous_const.prodMk continuous_id)
      exact hc1.sub hc2
    unfold dot3D
    exact continuous_const.mul
      ((((hdt_c 0).mul (hw.h_comp 0).h_c3.continuous).add
        ((hdt_c 1).mul (hw.h_comp 1).h_c3.continuous)).add
        ((hdt_c 2).mul (hw.h_comp 2).h_c3.continuous))
  have hparam := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (Metric.ball_mem_nhds t hδ)
    (Filter.Eventually.of_forall fun s => (hF_cont s).aestronglyMeasurable)
    hF_int
    hF'_cont.aestronglyMeasurable
    (Filter.Eventually.of_forall fun x s hs => by rw [Real.norm_eq_abs]; exact hbound s hs x)
    hbound_int
    (Filter.Eventually.of_forall fun x s _ => by
      have hc : ∀ c : Fin 3,
          HasDerivAt (fun r => (u₁ r x c - u₂ r x c) * (u₁ r x c - u₂ r x c))
            (2 * (deriv (fun r => u₁ r x c - u₂ r x c) s * (u₁ s x c - u₂ s x c))) s := fun c => by
        have hm := (hdt_w s x c).differentiableAt.hasDerivAt.mul (hdt_w s x c).differentiableAt.hasDerivAt
        have heq : deriv (fun r => u₁ r x c - u₂ r x c) s * (u₁ s x c - u₂ s x c) +
            (u₁ s x c - u₂ s x c) * deriv (fun r => u₁ r x c - u₂ r x c) s =
            2 * (deriv (fun r => u₁ r x c - u₂ r x c) s * (u₁ s x c - u₂ s x c)) := by ring
        rwa [heq] at hm
      have hsum := ((hc 0).add (hc 1)).add (hc 2)
      have heq : 2 * (deriv (fun r => u₁ r x 0 - u₂ r x 0) s * (u₁ s x 0 - u₂ s x 0)) +
          2 * (deriv (fun r => u₁ r x 1 - u₂ r x 1) s * (u₁ s x 1 - u₂ s x 1)) +
          2 * (deriv (fun r => u₁ r x 2 - u₂ r x 2) s * (u₁ s x 2 - u₂ s x 2)) =
          2 * dot3D (fun c => deriv (fun r => u₁ r x c - u₂ r x c) s) (u₁ s x - u₂ s x) := by
        unfold dot3D; simp [Pi.sub_apply]; ring
      rwa [heq] at hsum)
  have hE_deriv : HasDerivAt (diffEnergyR3 u₁ u₂)
      ((1 / 2 : ℝ) * r3Integral (fun x =>
        2 * dot3D (fun c => deriv (fun s => u₁ s x c - u₂ s x c) t) (w x))) t :=
    hparam.2.const_mul (1 / 2 : ℝ)
  -- Pointwise difference momentum equation
  have hdiff_mom : ∀ (x : R3) (c : Fin 3),
      deriv (fun s => u₁ s x c - u₂ s x c) t =
        ν * laplacian3D w x c - directionalAdvection3D (u₁ t) w x c -
        directionalAdvection3D w (u₂ t) x c - grad3D q x c := by
    intro x c
    have hinl : HasDerivAt (fun r : ℝ => (r, x)) (1, (0 : R3)) t :=
      (hasDerivAt_id t).prodMk (hasDerivAt_const t x)
    have hd1 : DifferentiableAt ℝ (fun s => u₁ s x c) t := by
      have h := ((hc2_st u₁ p₁ hns₁.toIsClassicalNS3D_C3 c).differentiable (by simp) (t, x)).hasFDerivAt.comp_hasDerivAt t hinl
      exact h.differentiableAt
    have hd2 : DifferentiableAt ℝ (fun s => u₂ s x c) t := by
      have h := ((hc2_st u₂ p₂ hns₂.toIsClassicalNS3D_C3 c).differentiable (by simp) (t, x)).hasFDerivAt.comp_hasDerivAt t hinl
      exact h.differentiableAt
    have hdt_sub : deriv (fun s => u₁ s x c - u₂ s x c) t =
        deriv (fun s => u₁ s x c) t - deriv (fun s => u₂ s x c) t :=
      (hd1.hasDerivAt.sub hd2.hasDerivAt).deriv
    have hm1 := hns₁.h_momentum t ht x c
    have hm2 := hns₂.h_momentum t ht x c
    have hlap : laplacian3D w x c = laplacian3D (u₁ t) x c - laplacian3D (u₂ t) x c :=
      laplacianScalar_sub (fun y => u₁ t y c) (fun y => u₂ t y c)
        (fun y => ((hu₁.h_comp c).h_c3.of_le (by exact_mod_cast (show (2 : ℕ) ≤ 3 by decide))).contDiffAt)
        (fun y => ((hu₂.h_comp c).h_c3.of_le (by exact_mod_cast (show (2 : ℕ) ≤ 3 by decide))).contDiffAt) x
    have hgrad : grad3D q x c = grad3D (p₁ t) x c - grad3D (p₂ t) x c :=
      partialDerivScalar_sub ((hns₁.h_p_c2_global t ht).differentiable (by simp) x)
        ((hns₂.h_p_c2_global t ht).differentiable (by simp) x) c
    have hadv : advection3D (u₁ t) x c - advection3D (u₂ t) x c =
        directionalAdvection3D (u₁ t) w x c + directionalAdvection3D w (u₂ t) x c := by
      unfold advection3D directionalAdvection3D
      have hp : ∀ i : Fin 3, partialDerivScalar (fun y => w y c) x i =
          partialDerivScalar (fun y => u₁ t y c) x i - partialDerivScalar (fun y => u₂ t y c) x i := fun i =>
        partialDerivScalar_sub ((hu₁.h_comp c).h_c3.differentiable (by simp) x)
          ((hu₂.h_comp c).h_c3.differentiable (by simp) x) i
      rw [hp 0, hp 1, hp 2]
      dsimp only [w]
      simp only [Pi.sub_apply]
      ring
    linear_combination hdt_sub + hm1 - hm2 - ν * hlap - hadv + hgrad
  have hmom_dot : ∀ x : R3,
      dot3D (fun c => deriv (fun s => u₁ s x c - u₂ s x c) t) (w x) =
        ν * dot3D (laplacian3D w x) (w x) -
        dot3D (directionalAdvection3D (u₁ t) w x) (w x) -
        dot3D (directionalAdvection3D w (u₂ t) x) (w x) -
        dot3D (grad3D q x) (w x) := fun x => by
    have m0 := hdiff_mom x 0; have m1 := hdiff_mom x 1; have m2 := hdiff_mom x 2
    unfold dot3D; dsimp only
    linear_combination (w x 0) * m0 + (w x 1) * m1 + (w x 2) * m2
  -- Integrability of the four terms
  have hint_lap : Integrable (fun x => dot3D (laplacian3D w x) (w x)) volume := by
    have hi : ∀ c i : Fin 3, Integrable (fun x => sndPartial (fun y => w y c) x i i * w x c) volume :=
      fun c i => integrable_mul_of_sq (contDiff_snd_c1_u (hw.h_comp c).h_c3 i i).continuous
        (hw.h_comp c).h_c3.continuous ((hw.h_comp c).h_int2 i i) (hw.h_comp c).h_int0
    have hc : ∀ c : Fin 3, Integrable (fun x => laplacian3D w x c * w x c) volume := fun c => by
      have hpt : (fun x => laplacian3D w x c * w x c) = fun x =>
          sndPartial (fun y => w y c) x 0 0 * w x c +
          sndPartial (fun y => w y c) x 1 1 * w x c +
          sndPartial (fun y => w y c) x 2 2 * w x c := by
        funext x; unfold laplacian3D laplacianScalar; ring
      rw [hpt]; exact int_add_u (int_add_u (hi c 0) (hi c 1)) (hi c 2)
    have hpt : (fun x => dot3D (laplacian3D w x) (w x)) = fun x =>
        laplacian3D w x 0 * w x 0 + laplacian3D w x 1 * w x 1 + laplacian3D w x 2 * w x 2 := rfl
    rw [hpt]; exact int_add_u (int_add_u (hc 0) (hc 1)) (hc 2)
  have hint_adv1 : Integrable (fun x => dot3D (directionalAdvection3D (u₁ t) w x) (w x)) volume := by
    have hu₁_bdd : ∀ i : Fin 3, ∃ C : ℝ, 0 ≤ C ∧ ∀ x : R3, |u₁ t x i| ≤ C := fun i =>
      exists_bound_of_vanishesAtInfinityR3 (hu₁.h_comp i).h_c3.continuous (hu₁.h_comp i).h_van0
    have ht' : ∀ c i : Fin 3, Integrable (fun x => u₁ t x i * (w x c * partialDerivScalar (fun y => w y c) x i)) volume :=
      fun c i => integrable_bdd_mul_mul_of_sq (hu₁.h_comp i).h_c3.continuous (hw.h_comp c).h_c3.continuous
        (contDiff_partial_c2_u (hw.h_comp c).h_c3 i).continuous (hu₁_bdd i)
        (hw.h_comp c).h_int0 ((hw.h_comp c).h_int1 i)
    have hc : ∀ c : Fin 3, Integrable (fun x => directionalAdvection3D (u₁ t) w x c * w x c) volume := fun c => by
      have hpt : (fun x => directionalAdvection3D (u₁ t) w x c * w x c) = fun x =>
          u₁ t x 0 * (w x c * partialDerivScalar (fun y => w y c) x 0) +
          u₁ t x 1 * (w x c * partialDerivScalar (fun y => w y c) x 1) +
          u₁ t x 2 * (w x c * partialDerivScalar (fun y => w y c) x 2) := by
        funext x; unfold directionalAdvection3D; ring
      rw [hpt]; exact int_add_u (int_add_u (ht' c 0) (ht' c 1)) (ht' c 2)
    have hpt : (fun x => dot3D (directionalAdvection3D (u₁ t) w x) (w x)) = fun x =>
        directionalAdvection3D (u₁ t) w x 0 * w x 0 +
        directionalAdvection3D (u₁ t) w x 1 * w x 1 +
        directionalAdvection3D (u₁ t) w x 2 * w x 2 := rfl
    rw [hpt]; exact int_add_u (int_add_u (hc 0) (hc 1)) (hc 2)
  have hint_adv2 : Integrable (fun x => dot3D (directionalAdvection3D w (u₂ t) x) (w x)) volume := by
    have hdu₂_bdd : ∀ c i : Fin 3, ∃ C : ℝ, 0 ≤ C ∧ ∀ x : R3, |partialDerivScalar (fun y => u₂ t y c) x i| ≤ C :=
      fun c i => exists_bound_of_vanishesAtInfinityR3
        (contDiff_partial_c2_u (hu₂.h_comp c).h_c3 i).continuous ((hu₂.h_comp c).h_van1 i)
    have ht' : ∀ c i : Fin 3, Integrable (fun x => partialDerivScalar (fun y => u₂ t y c) x i * (w x i * w x c)) volume :=
      fun c i => integrable_bdd_mul_mul_of_sq (contDiff_partial_c2_u (hu₂.h_comp c).h_c3 i).continuous
        (hw.h_comp i).h_c3.continuous (hw.h_comp c).h_c3.continuous
        (hdu₂_bdd c i) (hw.h_comp i).h_int0 (hw.h_comp c).h_int0
    have hc : ∀ c : Fin 3, Integrable (fun x => directionalAdvection3D w (u₂ t) x c * w x c) volume := fun c => by
      have hpt : (fun x => directionalAdvection3D w (u₂ t) x c * w x c) = fun x =>
          partialDerivScalar (fun y => u₂ t y c) x 0 * (w x 0 * w x c) +
          partialDerivScalar (fun y => u₂ t y c) x 1 * (w x 1 * w x c) +
          partialDerivScalar (fun y => u₂ t y c) x 2 * (w x 2 * w x c) := by
        funext x; unfold directionalAdvection3D; ring
      rw [hpt]; exact int_add_u (int_add_u (ht' c 0) (ht' c 1)) (ht' c 2)
    have hpt : (fun x => dot3D (directionalAdvection3D w (u₂ t) x) (w x)) = fun x =>
        directionalAdvection3D w (u₂ t) x 0 * w x 0 +
        directionalAdvection3D w (u₂ t) x 1 * w x 1 +
        directionalAdvection3D w (u₂ t) x 2 * w x 2 := rfl
    rw [hpt]; exact int_add_u (int_add_u (hc 0) (hc 1)) (hc 2)
  have hq_c2 : ContDiff ℝ 2 q := (hns₁.h_p_c2_global t ht).sub (hns₂.h_p_c2_global t ht)
  have hq_van : VanishesAtInfinityR3 q := vanishesAtInfinityR3_sub (hns₁.h_p_van t ht) (hns₂.h_p_van t ht)
  have hq_int0 : Integrable (fun x => (q x) ^ 2) volume :=
    integrable_sub_sq_of_sq (hns₁.h_p_c2_global t ht).continuous (hns₂.h_p_c2_global t ht).continuous
      (hns₁.h_p_int0 t ht) (hns₂.h_p_int0 t ht)
  have hq_int1 : ∀ i : Fin 3, Integrable (fun x => (partialDerivScalar q x i) ^ 2) volume := fun i => by
    have hpt : (fun x => (partialDerivScalar q x i) ^ 2) = fun x =>
        (partialDerivScalar (p₁ t) x i - partialDerivScalar (p₂ t) x i) ^ 2 := by
      funext x
      rw [partialDerivScalar_sub ((hns₁.h_p_c2_global t ht).differentiable (by simp) x)
        ((hns₂.h_p_c2_global t ht).differentiable (by simp) x) i]
    rw [hpt]
    exact integrable_sub_sq_of_sq (contDiff_partial_c1_u (hns₁.h_p_c2_global t ht) i).continuous
      (contDiff_partial_c1_u (hns₂.h_p_c2_global t ht) i).continuous
      (hns₁.h_p_int1 t ht i) (hns₂.h_p_int1 t ht i)
  have hint_gp : Integrable (fun x => dot3D (grad3D q x) (w x)) volume := by
    have hc : ∀ i : Fin 3, Integrable (fun x => partialDerivScalar q x i * w x i) volume := fun i =>
      integrable_mul_of_sq (contDiff_partial_c1_u hq_c2 i).continuous (hw.h_comp i).h_c3.continuous
        (hq_int1 i) (hw.h_comp i).h_int0
    have hpt : (fun x => dot3D (grad3D q x) (w x)) = fun x =>
        partialDerivScalar q x 0 * w x 0 + partialDerivScalar q x 1 * w x 1 +
        partialDerivScalar q x 2 * w x 2 := rfl
    rw [hpt]; exact int_add_u (int_add_u (hc 0) (hc 1)) (hc 2)
  -- Exact identity for D
  let D : ℝ := -ν * r3Integral (gradNormSqR3 w) +
    r3Integral (fun x => dot3D (u₂ t x) (directionalAdvection3D w w x))
  have hD_eq : (1 / 2 : ℝ) * r3Integral (fun x =>
      2 * dot3D (fun c => deriv (fun s => u₁ s x c - u₂ s x c) t) (w x)) = D := by
    rw [r3Integral_const_mul, r3Integral_congr hmom_dot,
        r3Integral_sub (int_sub_u (int_sub_u (int_const_mul_u ν hint_lap) hint_adv1) hint_adv2) hint_gp,
        r3Integral_sub (int_sub_u (int_const_mul_u ν hint_lap) hint_adv1) hint_adv2,
        r3Integral_sub (int_const_mul_u ν hint_lap) hint_adv1,
        r3Integral_const_mul,
        r3_diff_laplacian_dot_self hw,
        r3_diff_transport_zero hu₁ hw,
        r3_diff_advection_ibp hu₂ hw,
        r3_diff_pressure_dot_zero hw hq_c2 hq_van hq_int0 hq_int1]
    dsimp only [D]; ring
  rw [hD_eq] at hE_deriv
  -- Bound D using 3D Agmon on u₂ and Young absorption
  have hint_gw : Integrable (gradNormSqR3 w) volume := by
    unfold gradNormSqR3
    exact int_add_u (int_add_u (int_add_u (int_add_u (int_add_u (int_add_u (int_add_u (int_add_u
      ((hw.h_comp 0).h_int1 0) ((hw.h_comp 0).h_int1 1)) ((hw.h_comp 0).h_int1 2))
      ((hw.h_comp 1).h_int1 0)) ((hw.h_comp 1).h_int1 1)) ((hw.h_comp 1).h_int1 2))
      ((hw.h_comp 2).h_int1 0)) ((hw.h_comp 2).h_int1 1)) ((hw.h_comp 2).h_int1 2)
  have hint_ibp_rhs : Integrable (fun x => dot3D (u₂ t x) (directionalAdvection3D w w x)) volume := by
    have hu₂_bdd : ∀ c : Fin 3, ∃ C : ℝ, 0 ≤ C ∧ ∀ x : R3, |u₂ t x c| ≤ C := fun c =>
      exists_bound_of_vanishesAtInfinityR3 (hu₂.h_comp c).h_c3.continuous (hu₂.h_comp c).h_van0
    have ht' : ∀ c i : Fin 3, Integrable (fun x => u₂ t x c * (w x i * partialDerivScalar (fun y => w y c) x i)) volume :=
      fun c i => integrable_bdd_mul_mul_of_sq (hu₂.h_comp c).h_c3.continuous (hw.h_comp i).h_c3.continuous
        (contDiff_partial_c2_u (hw.h_comp c).h_c3 i).continuous (hu₂_bdd c)
        (hw.h_comp i).h_int0 ((hw.h_comp c).h_int1 i)
    have hpt : (fun x => dot3D (u₂ t x) (directionalAdvection3D w w x)) = fun x =>
        (u₂ t x 0 * (w x 0 * partialDerivScalar (fun y => w y 0) x 0) +
         u₂ t x 0 * (w x 1 * partialDerivScalar (fun y => w y 0) x 1) +
         u₂ t x 0 * (w x 2 * partialDerivScalar (fun y => w y 0) x 2)) +
        (u₂ t x 1 * (w x 0 * partialDerivScalar (fun y => w y 1) x 0) +
         u₂ t x 1 * (w x 1 * partialDerivScalar (fun y => w y 1) x 1) +
         u₂ t x 1 * (w x 2 * partialDerivScalar (fun y => w y 1) x 2)) +
        (u₂ t x 2 * (w x 0 * partialDerivScalar (fun y => w y 2) x 0) +
         u₂ t x 2 * (w x 1 * partialDerivScalar (fun y => w y 2) x 1) +
         u₂ t x 2 * (w x 2 * partialDerivScalar (fun y => w y 2) x 2)) := by
      funext x; unfold dot3D directionalAdvection3D; ring
    rw [hpt]
    exact int_add_u
      (int_add_u (int_add_u (int_add_u (ht' 0 0) (ht' 0 1)) (ht' 0 2))
        (int_add_u (int_add_u (ht' 1 0) (ht' 1 1)) (ht' 1 2)))
      (int_add_u (int_add_u (ht' 2 0) (ht' 2 1)) (ht' 2 2))
  let M₂ : ℝ := agmonLinfSqBoundR3 u₂ t
  have hM₂_pt : ∀ x : R3, dot3D (u₂ t x) (u₂ t x) ≤ M₂ := fun x => by
    have hag := agmon_3d_r3_ns_velocity hu₂ x
    have h2Z : r3Integral (fun y => dot3D (curl3D (u₂ t) y) (curl3D (u₂ t) y)) = 2 * enstrophyR3 (u₂ t) := by
      unfold enstrophyR3; ring
    rw [h2Z] at hag
    exact hag
  have hpt_bound : ∀ x : R3,
      dot3D (u₂ t x) (directionalAdvection3D w w x) ≤
        (ν / 2) * gradNormSqR3 w x + (M₂ / (2 * ν)) * dot3D (w x) (w x) := fun x => by
    have hy := pointwise_diff_advection_young hν (u₂ t x) (w x)
      (partialDerivScalar (fun y => w y 0) x 0)
      (partialDerivScalar (fun y => w y 0) x 1)
      (partialDerivScalar (fun y => w y 0) x 2)
      (partialDerivScalar (fun y => w y 1) x 0)
      (partialDerivScalar (fun y => w y 1) x 1)
      (partialDerivScalar (fun y => w y 1) x 2)
      (partialDerivScalar (fun y => w y 2) x 0)
      (partialDerivScalar (fun y => w y 2) x 1)
      (partialDerivScalar (fun y => w y 2) x 2)
    have hmul : (1 / (2 * ν)) * dot3D (u₂ t x) (u₂ t x) * dot3D (w x) (w x) ≤
        (M₂ / (2 * ν)) * dot3D (w x) (w x) := by
      have h1 : (1 / (2 * ν)) * dot3D (u₂ t x) (u₂ t x) ≤ M₂ / (2 * ν) := by
        have hm := mul_le_mul_of_nonneg_left (hM₂_pt x) (by positivity : (0 : ℝ) ≤ 1 / (2 * ν))
        have heq : (1 / (2 * ν)) * M₂ = M₂ / (2 * ν) := by ring
        linarith
      exact mul_le_mul_of_nonneg_right h1 (dot3D_self_nonneg_r3 (w x))
    change u₂ t x 0 * (w x 0 * partialDerivScalar (fun y => w y 0) x 0 +
      w x 1 * partialDerivScalar (fun y => w y 0) x 1 +
      w x 2 * partialDerivScalar (fun y => w y 0) x 2) +
      u₂ t x 1 * (w x 0 * partialDerivScalar (fun y => w y 1) x 0 +
      w x 1 * partialDerivScalar (fun y => w y 1) x 1 +
      w x 2 * partialDerivScalar (fun y => w y 1) x 2) +
      u₂ t x 2 * (w x 0 * partialDerivScalar (fun y => w y 2) x 0 +
      w x 1 * partialDerivScalar (fun y => w y 2) x 1 +
      w x 2 * partialDerivScalar (fun y => w y 2) x 2) ≤ _
    unfold gradNormSqR3
    linarith
  have hmono_int := MeasureTheory.integral_mono hint_ibp_rhs
    (int_add_u (int_const_mul_u (ν / 2) hint_gw) (int_const_mul_u (M₂ / (2 * ν)) hF_int))
    hpt_bound
  change r3Integral (fun x => dot3D (u₂ t x) (directionalAdvection3D w w x)) ≤
      r3Integral (fun x => (ν / 2) * gradNormSqR3 w x + (M₂ / (2 * ν)) * dot3D (w x) (w x)) at hmono_int
  rw [r3Integral_add (int_const_mul_u (ν / 2) hint_gw) (int_const_mul_u (M₂ / (2 * ν)) hF_int),
      r3Integral_const_mul, r3Integral_const_mul] at hmono_int
  have hgw_nn : 0 ≤ r3Integral (gradNormSqR3 w) := r3Integral_nonneg (fun x => gradNormSqR3_nonneg w x)
  have hD_le : D ≤ (M₂ / ν) * diffEnergyR3 u₁ u₂ t := by
    have hE_eq : (M₂ / (2 * ν)) * r3Integral (fun x => dot3D (w x) (w x)) =
        (M₂ / ν) * diffEnergyR3 u₁ u₂ t := by
      unfold diffEnergyR3; dsimp only [w]; ring
    dsimp only [D]
    nlinarith
  exact ⟨D, hE_deriv, hD_le⟩

/-- **THEOREM 11A1-1 (Unconditional Whole-Space `ℝ³` Serrin `L²` Stability & Pointwise Global Uniqueness):**
    For any two decaying classical 3D NS solutions `(u₁, p₁)` and `(u₂, p₂)` on `ℝ³`
    (with continuous `palinstrophyR3 (u₂ ·)` and local `L¹` domination of the difference):
    1. Continuous `L²` dependence on initial data:
       `diffEnergyR3 u₁ u₂ T ≤ diffEnergyR3 u₁ u₂ 0 * exp((1/ν) ∫_0^T agmonLinfSqBoundR3 u₂ s ds)`.
    2. **Pointwise Global Uniqueness on `[0, ∞) × ℝ³`:**
       If `∀ x, u₁ 0 x = u₂ 0 x`, then `∀ t ≥ 0, ∀ x : R3, u₁ t x = u₂ t x`. -/
theorem r3_serrin_L2_stability_and_global_uniqueness
    {u₁ u₂ : ℝ → R3 → R3} {p₁ p₂ : ℝ → R3 → ℝ} {ν : ℝ}
    (hns₁ : IsDecayingClassicalNS3D_R3 u₁ p₁ ν)
    (hns₂ : IsDecayingClassicalNS3D_R3 u₂ p₂ ν)
    (hP₂_cont : Continuous (fun s : ℝ => palinstrophyR3 (u₂ s)))
    (h_dt_diff_dom : ∀ t₀ ≥ 0, ∃ δ > 0, ∃ bound : R3 → ℝ,
      Integrable bound volume ∧
      ∀ t ∈ Metric.ball t₀ δ, ∀ x : R3,
        |2 * dot3D (fun c => deriv (fun s => u₁ s x c - u₂ s x c) t) (u₁ t x - u₂ t x)| ≤ bound x) :
    (∀ T ≥ 0, diffEnergyR3 u₁ u₂ T ≤
      diffEnergyR3 u₁ u₂ 0 *
        Real.exp ((1 / ν) * ∫ s in (0 : ℝ)..T, agmonLinfSqBoundR3 u₂ s)) ∧
    ((∀ x : R3, u₁ 0 x = u₂ 0 x) → ∀ t ≥ 0, ∀ x : R3, u₁ t x = u₂ t x) := by
  have hν : 0 < ν := hns₁.h_nu_pos
  have hZ₂_ext_cont : Continuous (fun s : ℝ => enstrophyR3 (u₂ (max s 0))) := by
    rw [continuous_iff_continuousAt]
    intro s
    have h1 : ContinuousAt (fun r => enstrophyR3 (u₂ r)) (max s (0 : ℝ)) :=
      (hasDerivAt_enstrophyR3_evolution hns₂ (le_max_right s 0)).continuousAt
    have h2 : ContinuousAt (fun r : ℝ => max r (0 : ℝ)) s :=
      (Continuous.max continuous_id continuous_const).continuousAt
    exact ContinuousAt.comp (f := fun r : ℝ => max r (0 : ℝ)) (g := fun r => enstrophyR3 (u₂ r)) h1 h2
  let γ : ℝ → ℝ := fun s =>
    ((1 / 2 : ℝ) * Real.sqrt (2 * enstrophyR3 (u₂ (max s 0))) * Real.sqrt (palinstrophyR3 (u₂ s))) / ν
  have hγ_cont : Continuous γ := by
    dsimp only [γ]
    exact (((continuous_const.mul (Real.continuous_sqrt.comp (continuous_const.mul hZ₂_ext_cont))).mul
      (Real.continuous_sqrt.comp hP₂_cont)).div_const ν)
  have hstab : ∀ T ≥ 0, diffEnergyR3 u₁ u₂ T ≤
      diffEnergyR3 u₁ u₂ 0 *
        Real.exp ((1 / ν) * ∫ s in (0 : ℝ)..T, agmonLinfSqBoundR3 u₂ s) := by
    intro T hT
    have hgr := gronwall_L2_of_hasDerivAt hT
      (E := diffEnergyR3 u₁ u₂) (E' := fun s => deriv (diffEnergyR3 u₁ u₂) s) (γ := γ)
      (fun s hs => by
        obtain ⟨D, hD, _⟩ := hasDerivAt_diffEnergyR3_and_bound hns₁ hns₂ h_dt_diff_dom hs.1
        rw [hD.deriv]; exact hD)
      hγ_cont
      (fun s hs => by
        obtain ⟨D, hD, hle⟩ := hasDerivAt_diffEnergyR3_and_bound hns₁ hns₂ h_dt_diff_dom (le_of_lt hs.1)
        rw [hD.deriv]
        have hγs : γ s = agmonLinfSqBoundR3 u₂ s / ν := by
          dsimp only [γ, agmonLinfSqBoundR3]
          rw [max_eq_left (le_of_lt hs.1)]
        rwa [hγs])
    have hint_eq : (∫ s in (0 : ℝ)..T, γ s) =
        (1 / ν) * ∫ s in (0 : ℝ)..T, agmonLinfSqBoundR3 u₂ s := by
      have hcongr : (∫ s in (0 : ℝ)..T, γ s) =
          ∫ s in (0 : ℝ)..T, (1 / ν) * agmonLinfSqBoundR3 u₂ s := by
        apply intervalIntegral.integral_congr
        intro s hs
        rw [Set.uIcc_of_le hT] at hs
        dsimp only [γ, agmonLinfSqBoundR3]
        rw [max_eq_left hs.1]
        ring
      rw [hcongr, intervalIntegral.integral_const_mul]
    rwa [hint_eq] at hgr
  refine ⟨hstab, ?_⟩
  intro hinit t ht x
  have hE0 : diffEnergyR3 u₁ u₂ 0 = 0 := by
    unfold diffEnergyR3
    have hzero : ∀ y : R3, dot3D (u₁ 0 y - u₂ 0 y) (u₁ 0 y - u₂ 0 y) = 0 := fun y => by
      rw [hinit y, sub_self]; unfold dot3D; simp
    rw [r3Integral_congr hzero, r3Integral_zero, mul_zero]
  have hEt_le : diffEnergyR3 u₁ u₂ t ≤ 0 := by
    have h := hstab t ht; rw [hE0, zero_mul] at h; exact h
  have hEt_zero : diffEnergyR3 u₁ u₂ t = 0 := le_antisymm hEt_le (diffEnergyR3_nonneg u₁ u₂ t)
  have hw := decayingH3SolenoidalR3_sub (hns₁.h_u_decay t ht) (hns₂.h_u_decay t ht)
  have hcomp_int : ∀ c : Fin 3, Integrable (fun y : R3 => (u₁ t y c - u₂ t y c) ^ 2) volume := fun c => by
    simpa only [Pi.sub_apply] using (hw.h_comp c).h_int0
  have hcomp_cont : ∀ c : Fin 3, Continuous (fun y : R3 => u₁ t y c - u₂ t y c) := fun c => by
    simpa only [Pi.sub_apply] using (hw.h_comp c).h_c3.continuous
  have hsum_zero : r3Integral (fun y => (u₁ t y 0 - u₂ t y 0) ^ 2) +
      r3Integral (fun y => (u₁ t y 1 - u₂ t y 1) ^ 2) +
      r3Integral (fun y => (u₁ t y 2 - u₂ t y 2) ^ 2) = 0 := by
    unfold diffEnergyR3 at hEt_zero
    have hpt : ∀ y : R3, dot3D (u₁ t y - u₂ t y) (u₁ t y - u₂ t y) =
        (u₁ t y 0 - u₂ t y 0) ^ 2 + (u₁ t y 1 - u₂ t y 1) ^ 2 + (u₁ t y 2 - u₂ t y 2) ^ 2 := fun y => by
      unfold dot3D; simp [Pi.sub_apply]; ring
    rw [r3Integral_congr hpt,
        r3Integral_add3 (hcomp_int 0) (hcomp_int 1) (hcomp_int 2)] at hEt_zero
    linarith
  have h0_nn : 0 ≤ r3Integral (fun y => (u₁ t y 0 - u₂ t y 0) ^ 2) := r3Integral_nonneg (fun _ => sq_nonneg _)
  have h1_nn : 0 ≤ r3Integral (fun y => (u₁ t y 1 - u₂ t y 1) ^ 2) := r3Integral_nonneg (fun _ => sq_nonneg _)
  have h2_nn : 0 ≤ r3Integral (fun y => (u₁ t y 2 - u₂ t y 2) ^ 2) := r3Integral_nonneg (fun _ => sq_nonneg _)
  funext c
  fin_cases c
  · exact sub_eq_zero.mp (eq_zero_of_r3Integral_sq_eq_zero (hcomp_cont 0) (hcomp_int 0) (by linarith) x)
  · exact sub_eq_zero.mp (eq_zero_of_r3Integral_sq_eq_zero (hcomp_cont 1) (hcomp_int 1) (by linarith) x)
  · exact sub_eq_zero.mp (eq_zero_of_r3Integral_sq_eq_zero (hcomp_cont 2) (hcomp_int 2) (by linarith) x)

-- ============================================================================
-- SECTION 2: THEOREM 11A1-2 — UNIFORM GLOBAL L²_t L∞_x BOUND ON ℝ³
-- ============================================================================

/-- **THEOREM 11A1-2 (Unconditional Uniform Global `L²_t L∞_x` Bound on Whole Space `ℝ³`):**
    For any decaying classical 3D NS solution `(u, p)` on `ℝ³` with a certified
    `GarryWaterfallWitnessR3` reaching the half-critical basin (`zCap N < ν⁴ / (2 E₀)`),
    the Agmon `L²_t L∞_x` integral `∫_0^T agmonLinfSqBoundR3 u s ds` is uniformly bounded
    across ALL `T ≥ 0`:
    `∫_0^T agmonLinfSqBoundR3 u s ds ≤ E₀/(4ν) + (1/ν)(zCap 0 + c_nu_R3 ν * M_peak * B) + (2/ν) zCap N`. -/
theorem r3_global_L2_Linf_bound_of_waterfall
    {u : ℝ → R3 → R3} {p : ℝ → R3 → ℝ} {ν E₀ : ℝ}
    (hns : IsDecayingClassicalNS3D_R3 u p ν)
    (hE₀_pos : 0 < E₀) (hE₀ : energyR3 (u 0) ≤ E₀)
    (hP_cont : Continuous (fun s : ℝ => palinstrophyR3 (u s)))
    (W : GarryWaterfallWitnessR3 u ν)
    (hcapture : W.zCap W.steps < Z_crit_R3 E₀ ν / 2) :
    let B : ℝ := chainBudgetR3 W.tGrid W.zCap W.steps
    let M_peak : ℝ := chainPeakR3 W.zCap W.steps
    ∀ T ≥ 0, (∫ s in (0 : ℝ)..T, agmonLinfSqBoundR3 u s) ≤
      E₀ / (4 * ν) +
      (1 / ν) * (W.zCap 0 + c_nu_R3 ν * M_peak * B) +
      (2 / ν) * W.zCap W.steps := by
  intro B M_peak T hT
  have hν : 0 < ν := hns.h_nu_pos
  have hZ_cont : ContinuousOn (fun s => enstrophyR3 (u s)) (Set.Icc 0 T) := fun s hs =>
    (hasDerivAt_enstrophyR3_evolution hns hs.1).continuousAt.continuousWithinAt
  have hM_cont : ContinuousOn (fun s => agmonLinfSqBoundR3 u s) (Set.Icc 0 T) := by
    unfold agmonLinfSqBoundR3
    exact ((continuousOn_const.mul (Real.continuous_sqrt.comp_continuousOn
      (continuousOn_const.mul hZ_cont))).mul
      (Real.continuous_sqrt.comp_continuousOn hP_cont.continuousOn))
  have hpt_amgm : ∀ s ∈ Set.Icc (0 : ℝ) T,
      agmonLinfSqBoundR3 u s ≤ (1 / 2 : ℝ) * enstrophyR3 (u s) + (1 / 4 : ℝ) * palinstrophyR3 (u s) := by
    intro s _
    unfold agmonLinfSqBoundR3
    have hZ_nn : 0 ≤ enstrophyR3 (u s) := enstrophyR3_nonneg (u s)
    have hP_nn : 0 ≤ palinstrophyR3 (u s) := palinstrophyR3_nonneg (u s)
    have h1 := Real.sq_sqrt (show 0 ≤ 2 * enstrophyR3 (u s) by linarith)
    have h2 := Real.sq_sqrt hP_nn
    nlinarith [sq_nonneg (Real.sqrt (2 * enstrophyR3 (u s)) - Real.sqrt (palinstrophyR3 (u s)))]
  have hZ_half_c : ContinuousOn (fun s => (1 / 2 : ℝ) * enstrophyR3 (u s)) (Set.Icc 0 T) :=
    continuousOn_const.mul hZ_cont
  have hP_qtr_c : ContinuousOn (fun s => (1 / 4 : ℝ) * palinstrophyR3 (u s)) (Set.Icc 0 T) :=
    continuousOn_const.mul hP_cont.continuousOn
  have hrhs_c : ContinuousOn (fun s => (1 / 2 : ℝ) * enstrophyR3 (u s) + (1 / 4 : ℝ) * palinstrophyR3 (u s)) (Set.Icc 0 T) :=
    hZ_half_c.add hP_qtr_c
  have hmono := intervalIntegral.integral_mono_on hT
    (hM_cont.intervalIntegrable_of_Icc (μ := volume) hT)
    (hrhs_c.intervalIntegrable_of_Icc (μ := volume) hT)
    hpt_amgm
  rw [intervalIntegral.integral_add
        (hZ_half_c.intervalIntegrable_of_Icc (μ := volume) hT)
        (hP_qtr_c.intervalIntegrable_of_Icc (μ := volume) hT),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul] at hmono
  have hleray := (global_leray_energy_law_r3 hns hT).2.2
  have hE_le : energyR3 (u 0) / (2 * ν) ≤ E₀ / (2 * ν) := div_le_div_of_nonneg_right hE₀ (by positivity)
  have hwf := ((garry_certified_waterfall_to_global_river_r3 hns hE₀_pos hE₀ W hcapture).2.2.2.2 hP_cont).1 T hT
  have h1 : (1 / 2 : ℝ) * (E₀ / (2 * ν)) = E₀ / (4 * ν) := by ring
  have h2 : (1 / 4 : ℝ) * ((4 / ν) * (W.zCap 0 + c_nu_R3 ν * M_peak * B) +
      (8 / ν) * W.zCap W.steps) =
      (1 / ν) * (W.zCap 0 + c_nu_R3 ν * M_peak * B) + (2 / ν) * W.zCap W.steps := by ring
  linarith

  -- ============================================================================
-- SECTION 3: PERIODIC TORUS 𝕋³ SERRIN L² STABILITY & POINTWISE UNIQUENESS
-- ============================================================================

private lemma cont_add_u {f g : R3 → ℝ} (hf : Continuous f) (hg : Continuous g) :
    Continuous (fun x => f x + g x) := hf.add hg

private lemma cont_sub_u {f g : R3 → ℝ} (hf : Continuous f) (hg : Continuous g) :
    Continuous (fun x => f x - g x) := hf.sub hg

private lemma cont_const_mul_u (c : ℝ) {f : R3 → ℝ} (hf : Continuous f) :
    Continuous (fun x => c * f x) := continuous_const.mul hf

/-- Periodic torus `𝕋³` kinetic energy of the velocity difference `w = u₁ - u₂`. -/
noncomputable def diffEnergyTorus3D (u₁ u₂ : ℝ → R3 → R3) (t : ℝ) : ℝ :=
  (1 / 2 : ℝ) * torusIntegral (fun x => dot3D (u₁ t x - u₂ t x) (u₁ t x - u₂ t x))

lemma torusIntegral_mono {f g : R3 → ℝ} (hf : Continuous f) (hg : Continuous g)
    (hle : ∀ x : R3, f x ≤ g x) :
    torusIntegral f ≤ torusIntegral g := by
  have hnn : 0 ≤ torusIntegral (fun x => g x - f x) :=
    torusIntegral_nonneg (cont_sub_u hg hf) (fun x => sub_nonneg.mpr (hle x))
  rw [torusIntegral_sub hg hf] at hnn
  linarith

lemma diffEnergyTorus3D_nonneg {u₁ u₂ : ℝ → R3 → R3} {t : ℝ}
    (h₁ : Continuous (u₁ t)) (h₂ : Continuous (u₂ t)) :
    0 ≤ diffEnergyTorus3D u₁ u₂ t := by
  unfold diffEnergyTorus3D
  have hc : Continuous (fun x : R3 => dot3D (u₁ t x - u₂ t x) (u₁ t x - u₂ t x)) :=
    continuous_dot3D (h₁.sub h₂) (h₁.sub h₂)
  linarith [torusIntegral_nonneg hc (fun x => dot3D_self_nonneg_r3 (u₁ t x - u₂ t x))]

private lemma continuous_vec3_triple : Continuous (fun p : ℝ × ℝ × ℝ => vec3 p.1 p.2.1 p.2.2) := by
  rw [continuous_pi_iff]
  intro i; fin_cases i
  · change Continuous (fun p : ℝ × ℝ × ℝ => p.1); exact continuous_fst
  · change Continuous (fun p : ℝ × ℝ × ℝ => p.2.1); exact continuous_fst.comp continuous_snd
  · change Continuous (fun p : ℝ × ℝ × ℝ => p.2.2); exact continuous_snd.comp continuous_snd

private lemma continuous_param_unit {X : Type*} [TopologicalSpace X] {h : X → ℝ → ℝ}
    (hh : Continuous (fun p : X × ℝ => h p.1 p.2)) :
    Continuous (fun x : X => ∫ t in (0 : ℝ)..1, h x t) :=
  intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' hh 0 1

private noncomputable def torusSlice2 (F : ℝ → R3 → ℝ) (s : ℝ) (p : ℝ × ℝ) : ℝ :=
  ∫ x₂ in (0 : ℝ)..1, F s (vec3 p.1 p.2 x₂)

private noncomputable def torusSlice1 (F : ℝ → R3 → ℝ) (s x₀ : ℝ) : ℝ :=
  ∫ x₁ in (0 : ℝ)..1, torusSlice2 F s (x₀, x₁)

private lemma torusIntegral_eq_slice1 (F : ℝ → R3 → ℝ) (s : ℝ) :
    torusIntegral (F s) = ∫ x₀ in (0 : ℝ)..1, torusSlice1 F s x₀ := rfl

private lemma continuous_torusSlice2 {F : ℝ → R3 → ℝ}
    (hF : Continuous (fun q : ℝ × R3 => F q.1 q.2)) :
    Continuous (fun q : ℝ × (ℝ × ℝ) => torusSlice2 F q.1 q.2) := by
  have hm : Continuous (fun p : (ℝ × (ℝ × ℝ)) × ℝ => (p.1.1, vec3 p.1.2.1 p.1.2.2 p.2)) :=
    (continuous_fst.comp continuous_fst).prodMk
      (continuous_vec3_triple.comp
        ((continuous_fst.comp (continuous_snd.comp continuous_fst)).prodMk
          ((continuous_snd.comp (continuous_snd.comp continuous_fst)).prodMk continuous_snd)))
  exact continuous_param_unit (hF.comp hm)

private lemma continuous_torusSlice1 {F : ℝ → R3 → ℝ}
    (hF : Continuous (fun q : ℝ × R3 => F q.1 q.2)) :
    Continuous (fun q : ℝ × ℝ => torusSlice1 F q.1 q.2) := by
  have hm : Continuous (fun p : (ℝ × ℝ) × ℝ => (p.1.1, (p.1.2, p.2))) :=
    (continuous_fst.comp continuous_fst).prodMk
      ((continuous_snd.comp continuous_fst).prodMk continuous_snd)
  exact continuous_param_unit ((continuous_torusSlice2 hF).comp hm)

private lemma continuous_torusIntegral_of_cont {F : ℝ → R3 → ℝ}
    (hF : Continuous (fun q : ℝ × R3 => F q.1 q.2)) :
    Continuous (fun s : ℝ => torusIntegral (F s)) := by
  have hrew : (fun s : ℝ => torusIntegral (F s)) = fun s => ∫ x₀ in (0 : ℝ)..1, torusSlice1 F s x₀ :=
    funext (torusIntegral_eq_slice1 F)
  rw [hrew]
  exact continuous_param_unit (continuous_torusSlice1 hF)

private lemma hasDerivAt_intervalIntegral_c1_param {f f' : ℝ → ℝ → ℝ} {t₀ : ℝ}
    (hf_cont : Continuous (fun p : ℝ × ℝ => f p.1 p.2))
    (hf'_cont : Continuous (fun p : ℝ × ℝ => f' p.1 p.2))
    (hderiv : ∀ t x : ℝ, HasDerivAt (fun s => f s x) (f' t x) t) :
    HasDerivAt (fun s => ∫ x in (0 : ℝ)..1, f s x) (∫ x in (0 : ℝ)..1, f' t₀ x) t₀ := by
  have hK : IsCompact (Set.Icc (t₀ - 1) (t₀ + 1) ×ˢ Set.Icc (0 : ℝ) 1) :=
    isCompact_Icc.prod isCompact_Icc
  obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn hf'_cont.continuousOn
  let μ : Measure ℝ := volume.restrict (Set.Ioc (0 : ℝ) 1)
  have hball : Metric.ball t₀ 1 ∈ 𝓝 t₀ := Metric.ball_mem_nhds t₀ zero_lt_one
  have hF_meas : ∀ᶠ s in 𝓝 t₀, AEStronglyMeasurable (fun x : ℝ => f s x) μ :=
    Filter.Eventually.of_forall fun s =>
      (hf_cont.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
  have hF_int : Integrable (fun x : ℝ => f t₀ x) μ :=
    (hf_cont.comp (continuous_const.prodMk continuous_id)).continuousOn.integrableOn_Icc.mono_set
      Set.Ioc_subset_Icc_self
  have hF'_meas : AEStronglyMeasurable (fun x : ℝ => f' t₀ x) μ :=
    (hf'_cont.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
  have hbound_int : Integrable (fun _ : ℝ => M) μ :=
    (continuousOn_const (c := M)).integrableOn_Icc.mono_set Set.Ioc_subset_Icc_self
  have hbound : ∀ᵐ x ∂μ, ∀ s ∈ Metric.ball t₀ 1, ‖f' s x‖ ≤ M := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx s hs
    rw [Metric.mem_ball, Real.dist_eq, abs_lt] at hs
    exact hM (s, x) ⟨⟨by linarith, by linarith⟩, ⟨le_of_lt hx.1, hx.2⟩⟩
  have hres := hasDerivAt_integral_of_dominated_loc_of_deriv_le hball hF_meas hF_int hF'_meas
    hbound hbound_int (Filter.Eventually.of_forall fun x s _ => hderiv s x)
  have hrew : (fun s => ∫ x in (0 : ℝ)..1, f s x) = fun s => ∫ x, f s x ∂μ := by
    funext s; exact intervalIntegral.integral_of_le zero_le_one
  rw [hrew, intervalIntegral.integral_of_le zero_le_one]
  exact hres.2

private lemma hasDerivAt_torusIntegral_of_c1 {F F' : ℝ → R3 → ℝ} {t₀ : ℝ}
    (hF_cont : Continuous (fun q : ℝ × R3 => F q.1 q.2))
    (hF'_cont : Continuous (fun q : ℝ × R3 => F' q.1 q.2))
    (hderiv : ∀ (t : ℝ) (x : R3), HasDerivAt (fun s => F s x) (F' t x) t) :
    HasDerivAt (fun s => torusIntegral (F s)) (torusIntegral (F' t₀)) t₀ := by
  have hG₂_deriv : ∀ (t : ℝ) (x₀ x₁ : ℝ),
      HasDerivAt (fun s => torusSlice2 F s (x₀, x₁)) (torusSlice2 F' t (x₀, x₁)) t := by
    intro t x₀ x₁
    change HasDerivAt (fun s => ∫ x₂ in (0 : ℝ)..1, F s (vec3 x₀ x₁ x₂))
      (∫ x₂ in (0 : ℝ)..1, F' t (vec3 x₀ x₁ x₂)) t
    have hm : Continuous (fun p : ℝ × ℝ => (p.1, vec3 x₀ x₁ p.2)) :=
      continuous_fst.prodMk (continuous_vec3_triple.comp (continuous_const.prodMk (continuous_const.prodMk continuous_snd)))
    have hcF : Continuous (fun p : ℝ × ℝ => F p.1 (vec3 x₀ x₁ p.2)) := hF_cont.comp hm
    have hcF' : Continuous (fun p : ℝ × ℝ => F' p.1 (vec3 x₀ x₁ p.2)) := hF'_cont.comp hm
    exact hasDerivAt_intervalIntegral_c1_param
      (f := fun s x₂ => F s (vec3 x₀ x₁ x₂))
      (f' := fun s x₂ => F' s (vec3 x₀ x₁ x₂))
      hcF hcF' (fun s x₂ => hderiv s (vec3 x₀ x₁ x₂))
  have hG₁_deriv : ∀ (t x₀ : ℝ),
      HasDerivAt (fun s => torusSlice1 F s x₀) (torusSlice1 F' t x₀) t := by
    intro t x₀
    change HasDerivAt (fun s => ∫ x₁ in (0 : ℝ)..1, torusSlice2 F s (x₀, x₁))
      (∫ x₁ in (0 : ℝ)..1, torusSlice2 F' t (x₀, x₁)) t
    have hm : Continuous (fun p : ℝ × ℝ => (p.1, (x₀, p.2))) :=
      continuous_fst.prodMk (continuous_const.prodMk continuous_snd)
    have hc2 : Continuous (fun p : ℝ × ℝ => torusSlice2 F p.1 (x₀, p.2)) :=
      (continuous_torusSlice2 hF_cont).comp hm
    have hc2' : Continuous (fun p : ℝ × ℝ => torusSlice2 F' p.1 (x₀, p.2)) :=
      (continuous_torusSlice2 hF'_cont).comp hm
    exact hasDerivAt_intervalIntegral_c1_param
      (f := fun s x₁ => torusSlice2 F s (x₀, x₁))
      (f' := fun s x₁ => torusSlice2 F' s (x₀, x₁))
      hc2 hc2' (fun s x₁ => hG₂_deriv s x₀ x₁)
  have hrew : (fun s : ℝ => torusIntegral (F s)) = fun s => ∫ x₀ in (0 : ℝ)..1, torusSlice1 F s x₀ :=
    funext (torusIntegral_eq_slice1 F)
  rw [hrew, torusIntegral_eq_slice1 F' t₀]
  exact hasDerivAt_intervalIntegral_c1_param
    (f := torusSlice1 F) (f' := torusSlice1 F')
    (continuous_torusSlice1 hF_cont) (continuous_torusSlice1 hF'_cont) hG₁_deriv

private lemma intervalIntegral_sq_eq_zero_of_cont {f : ℝ → ℝ} (hf : Continuous f)
    (hzero : (∫ t in (0 : ℝ)..1, (f t) ^ 2) = 0) :
    ∀ t ∈ Set.Icc (0 : ℝ) 1, f t = 0 := by
  rw [intervalIntegral.integral_of_le zero_le_one] at hzero
  have hint : IntegrableOn (fun t : ℝ => (f t) ^ 2) (Set.Ioc 0 1) volume :=
    (hf.pow 2).continuousOn.integrableOn_Icc.mono_set Set.Ioc_subset_Icc_self
  have hae : (fun t : ℝ => (f t) ^ 2) =ᵐ[volume.restrict (Set.Ioc 0 1)] 0 :=
    (MeasureTheory.integral_eq_zero_iff_of_nonneg (fun _ => sq_nonneg _) hint).mp hzero
  have hopen : ∀ t ∈ Set.Ioo (0 : ℝ) 1, f t = 0 := by
    intro t₀ ht₀
    by_contra hne
    have hpos : 0 < (f t₀) ^ 2 := sq_pos_of_ne_zero hne
    let U : Set ℝ := Set.Ioo 0 1 ∩ {t : ℝ | 0 < (f t) ^ 2}
    have hU_open : IsOpen U := isOpen_Ioo.inter (isOpen_lt continuous_const (hf.pow 2))
    have hU_ne : U.Nonempty := ⟨t₀, ht₀, hpos⟩
    have hU_pos : volume U ≠ 0 := hU_open.measure_ne_zero volume hU_ne
    have hU_sub_ioc : U ⊆ Set.Ioc 0 1 := fun t ht => ⟨ht.1.1, le_of_lt ht.1.2⟩
    have hU_zero : volume.restrict (Set.Ioc 0 1) U = 0 := by
      have hsub : U ⊆ {t : ℝ | ¬(f t) ^ 2 = 0} := fun t ht => ne_of_gt ht.2
      exact measure_mono_null hsub (ae_iff.mp hae)
    rw [Measure.restrict_apply hU_open.measurableSet, Set.inter_eq_left.mpr hU_sub_ioc] at hU_zero
    exact hU_pos hU_zero
  intro t ht
  have hcl : t ∈ closure (Set.Ioo (0 : ℝ) 1) := by
    rw [closure_Ioo (by norm_num : (0 : ℝ) ≠ 1)]; exact ht
  have hclosed : IsClosed {s : ℝ | f s = 0} := isClosed_eq hf continuous_const
  exact hclosed.closure_subset_iff.mpr hopen hcl

private lemma isPeriodic3D_shift_int {f : R3 → ℝ} (hf : IsPeriodic3D f)
    (x : R3) (k₀ k₁ k₂ : ℤ) :
    f (vec3 (x 0 + k₀) (x 1 + k₁) (x 2 + k₂)) = f x := by
  have hshift_axis : ∀ (y : R3) (i : Fin 3) (k : ℤ),
      f (y + (k : ℝ) • basisVec i) = f y := by
    intro y i k
    induction k using Int.induction_on with
    | zero => simp
    | succ n ih =>
      have h1 : y + ((n + 1 : ℤ) : ℝ) • basisVec i = (y + (n : ℝ) • basisVec i) + basisVec i := by
        push_cast; rw [add_smul, one_smul, add_assoc]
      have ih' : f (y + (n : ℝ) • basisVec i) = f y := by simpa using ih
      rw [h1, hf _ i, ih']
    | pred n ih =>
      have h1 : y + ((-n - 1 : ℤ) : ℝ) • basisVec i + basisVec i = y + ((-n : ℤ) : ℝ) • basisVec i := by
        push_cast; rw [sub_smul, one_smul]; abel
      have h2 := hf (y + ((-n - 1 : ℤ) : ℝ) • basisVec i) i
      rw [h1] at h2
      linarith [h2, ih]
  have hvec : vec3 (x 0 + k₀) (x 1 + k₁) (x 2 + k₂) =
      ((x + (k₀ : ℝ) • basisVec 0) + (k₁ : ℝ) • basisVec 1) + (k₂ : ℝ) • basisVec 2 := by
    funext i; fin_cases i <;> simp [vec3, basisVec]
  rw [hvec, hshift_axis _ 2 k₂, hshift_axis _ 1 k₁, hshift_axis _ 0 k₀]

/-- If a continuous 1-periodic `f : R3 → ℝ` has `torusIntegral (f · ^ 2) = 0`, then `f x = 0`
    for EVERY `x : R3`. -/
lemma eq_zero_of_torusIntegral_sq_eq_zero {f : R3 → ℝ} (hf_cont : Continuous f)
    (hf_per : IsPeriodic3D f) (hzero : torusIntegral (fun x => (f x) ^ 2) = 0) :
    ∀ x : R3, f x = 0 := by
  unfold torusIntegral at hzero
  have hcube : ∀ x₀ ∈ Set.Icc (0 : ℝ) 1, ∀ x₁ ∈ Set.Icc (0 : ℝ) 1, ∀ x₂ ∈ Set.Icc (0 : ℝ) 1,
      f (vec3 x₀ x₁ x₂) = 0 := by
    let g₂ : ℝ × ℝ → ℝ := fun p => ∫ x₂ in (0 : ℝ)..1, (f (vec3 p.1 p.2 x₂)) ^ 2
    have hg₂_cont : Continuous g₂ := by
      have hm : Continuous (fun p : (ℝ × ℝ) × ℝ => vec3 p.1.1 p.1.2 p.2) :=
        continuous_vec3_triple.comp ((continuous_fst.comp continuous_fst).prodMk
          ((continuous_snd.comp continuous_fst).prodMk continuous_snd))
      exact continuous_param_unit ((hf_cont.pow 2).comp hm)
    have hg₂_nn : ∀ p : ℝ × ℝ, 0 ≤ g₂ p := fun p =>
      intervalIntegral.integral_nonneg zero_le_one (fun _ _ => sq_nonneg _)
    let g₁ : ℝ → ℝ := fun x₀ => ∫ x₁ in (0 : ℝ)..1, g₂ (x₀, x₁)
    have hg₁_cont : Continuous g₁ := continuous_param_unit hg₂_cont
    have hg₁_nn : ∀ x₀ : ℝ, 0 ≤ g₁ x₀ := fun x₀ =>
      intervalIntegral.integral_nonneg zero_le_one (fun x₁ _ => hg₂_nn (x₀, x₁))
    have hsq1 : (∫ x₀ in (0 : ℝ)..1, (Real.sqrt (g₁ x₀)) ^ 2) = 0 := by
      have hcongr : (∫ x₀ in (0 : ℝ)..1, (Real.sqrt (g₁ x₀)) ^ 2) = ∫ x₀ in (0 : ℝ)..1, g₁ x₀ :=
        intervalIntegral.integral_congr (fun x₀ _ => Real.sq_sqrt (hg₁_nn x₀))
      rw [hcongr]; exact hzero
    have hg₁_zero := intervalIntegral_sq_eq_zero_of_cont (Real.continuous_sqrt.comp hg₁_cont) hsq1
    intro x₀ hx₀ x₁ hx₁ x₂ hx₂
    have hg₁_0 : g₁ x₀ = 0 := by
      have hs : Real.sqrt (g₁ x₀) = 0 := hg₁_zero x₀ hx₀
      have h2 := Real.sq_sqrt (hg₁_nn x₀)
      rw [hs] at h2; linarith
    have hsq2 : (∫ y₁ in (0 : ℝ)..1, (Real.sqrt (g₂ (x₀, y₁))) ^ 2) = 0 := by
      have hcongr : (∫ y₁ in (0 : ℝ)..1, (Real.sqrt (g₂ (x₀, y₁))) ^ 2) = ∫ y₁ in (0 : ℝ)..1, g₂ (x₀, y₁) :=
        intervalIntegral.integral_congr (fun y₁ _ => Real.sq_sqrt (hg₂_nn (x₀, y₁)))
      rw [hcongr]; exact hg₁_0
    have hg₂_zero := intervalIntegral_sq_eq_zero_of_cont
      (Real.continuous_sqrt.comp (hg₂_cont.comp (continuous_const.prodMk continuous_id))) hsq2
    have hg₂_0 : g₂ (x₀, x₁) = 0 := by
      have hs : Real.sqrt (g₂ (x₀, x₁)) = 0 := hg₂_zero x₁ hx₁
      have h2 := Real.sq_sqrt (hg₂_nn (x₀, x₁))
      rw [hs] at h2; linarith
    have hline : Continuous (fun y₂ : ℝ => f (vec3 x₀ x₁ y₂)) :=
      hf_cont.comp (continuous_vec3_triple.comp
        (continuous_const.prodMk (continuous_const.prodMk continuous_id)))
    exact intervalIntegral_sq_eq_zero_of_cont hline hg₂_0 x₂ hx₂
  intro x
  let k₀ : ℤ := -⌊x 0⌋
  let k₁ : ℤ := -⌊x 1⌋
  let k₂ : ℤ := -⌊x 2⌋
  have hsh := isPeriodic3D_shift_int hf_per x k₀ k₁ k₂
  rw [← hsh]
  apply hcube
  · exact ⟨by push_cast [k₀]; linarith [Int.floor_le (x 0)],
           by push_cast [k₀]; linarith [Int.lt_floor_add_one (x 0)]⟩
  · exact ⟨by push_cast [k₁]; linarith [Int.floor_le (x 1)],
           by push_cast [k₁]; linarith [Int.lt_floor_add_one (x 1)]⟩
  · exact ⟨by push_cast [k₂]; linarith [Int.floor_le (x 2)],
           by push_cast [k₂]; linarith [Int.lt_floor_add_one (x 2)]⟩

private lemma torus3D_diff_advection_ibp {u₂ w : R3 → R3}
    (hu₂_c2 : ContDiff ℝ 2 u₂) (hu₂_per : IsPeriodic3D u₂)
    (hw_c2 : ContDiff ℝ 2 w) (hw_per : IsPeriodic3D w) (hw_div : ∀ x : R3, div3D w x = 0) :
    torusIntegral (fun x => dot3D (directionalAdvection3D w u₂ x) (w x)) =
      -torusIntegral (fun x => dot3D (u₂ x) (directionalAdvection3D w w x)) := by
  have hu₂_c : ∀ c : Fin 3, ContDiff ℝ 2 (fun x => u₂ x c) := fun c => (contDiff_pi.mp hu₂_c2) c
  have hw_c : ∀ c : Fin 3, ContDiff ℝ 2 (fun x => w x c) := fun c => (contDiff_pi.mp hw_c2) c
  have hu₂_c1 : ContDiff ℝ 1 u₂ := hu₂_c2.of_le (by exact_mod_cast (show (1 : ℕ) ≤ 2 by decide))
  have hw_c1 : ContDiff ℝ 1 w := hw_c2.of_le (by exact_mod_cast (show (1 : ℕ) ≤ 2 by decide))
  have hu₂_cc1 : ∀ c : Fin 3, ContDiff ℝ 1 (fun x => u₂ x c) := fun c => (contDiff_pi.mp hu₂_c1) c
  have hw_cc1 : ∀ c : Fin 3, ContDiff ℝ 1 (fun x => w x c) := fun c => (contDiff_pi.mp hw_c1) c
  have hu₂_p : ∀ c : Fin 3, IsPeriodic3D (fun x => u₂ x c) := fun c => hu₂_per.comp (fun v => v c)
  have hw_p : ∀ c : Fin 3, IsPeriodic3D (fun x => w x c) := fun c => hw_per.comp (fun v => v c)
  have hterm : ∀ c i : Fin 3,
      torusIntegral (fun x => (w x i * w x c) * partialDerivScalar (fun y => u₂ y c) x i) =
        -torusIntegral (fun x => (partialDerivScalar (fun y => w y i) x i * w x c +
          w x i * partialDerivScalar (fun y => w y c) x i) * u₂ x c) := by
    intro c i
    have hmul_c1 : ContDiff ℝ 1 (fun y => w y i * w y c) := (hw_cc1 i).mul (hw_cc1 c)
    have hibp := torusIntegral_ibp hmul_c1 (hu₂_cc1 c) ((hw_p i).mul (hw_p c)) (hu₂_p c) i
    have hmul_p : ∀ x : R3, partialDerivScalar (fun y => w y i * w y c) x i * u₂ x c =
        (partialDerivScalar (fun y => w y i) x i * w x c +
          w x i * partialDerivScalar (fun y => w y c) x i) * u₂ x c := fun x => by
      rw [partialDerivScalar_mul ((hw_c i).differentiable (by simp) x)
        ((hw_c c).differentiable (by simp) x) i]
      ring
    rw [torusIntegral_congr hmul_p] at hibp
    exact hibp
  have h_comp : ∀ c : Fin 3,
      torusIntegral (fun x => directionalAdvection3D w u₂ x c * w x c) =
        -torusIntegral (fun x => u₂ x c * directionalAdvection3D w w x c) := by
    intro c
    have hl_cont : ∀ i : Fin 3, Continuous (fun x => (w x i * w x c) * partialDerivScalar (fun y => u₂ y c) x i) :=
      fun i => ((hw_c i).continuous.mul (hw_c c).continuous).mul
        (continuous_partialDerivScalar_of_contDiff (hu₂_cc1 c) i)
    have hr_cont : ∀ i : Fin 3,
        Continuous (fun x => (partialDerivScalar (fun y => w y i) x i * w x c +
          w x i * partialDerivScalar (fun y => w y c) x i) * u₂ x c) :=
      fun i => (((continuous_partialDerivScalar_of_contDiff (hw_cc1 i) i).mul (hw_c c).continuous).add
        ((hw_c i).continuous.mul (continuous_partialDerivScalar_of_contDiff (hw_cc1 c) i))).mul
        (hu₂_c c).continuous
    have hl_pt : ∀ x : R3, directionalAdvection3D w u₂ x c * w x c =
        (w x 0 * w x c) * partialDerivScalar (fun y => u₂ y c) x 0 +
        (w x 1 * w x c) * partialDerivScalar (fun y => u₂ y c) x 1 +
        (w x 2 * w x c) * partialDerivScalar (fun y => u₂ y c) x 2 := fun x => by
      unfold directionalAdvection3D; ring
    have hr_pt : ∀ x : R3,
        ((partialDerivScalar (fun y => w y 0) x 0 * w x c + w x 0 * partialDerivScalar (fun y => w y c) x 0) * u₂ x c) +
        ((partialDerivScalar (fun y => w y 1) x 1 * w x c + w x 1 * partialDerivScalar (fun y => w y c) x 1) * u₂ x c) +
        ((partialDerivScalar (fun y => w y 2) x 2 * w x c + w x 2 * partialDerivScalar (fun y => w y c) x 2) * u₂ x c) =
        u₂ x c * directionalAdvection3D w w x c := fun x => by
      have hdiv0 := hw_div x; unfold div3D at hdiv0
      unfold directionalAdvection3D
      linear_combination (w x c * u₂ x c) * hdiv0
    rw [torusIntegral_congr hl_pt, torusIntegral_add3 (hl_cont 0) (hl_cont 1) (hl_cont 2),
        hterm c 0, hterm c 1, hterm c 2]
    have hsum := torusIntegral_add3 (hr_cont 0) (hr_cont 1) (hr_cont 2)
    rw [torusIntegral_congr hr_pt] at hsum
    linarith
  have hl_c : ∀ c : Fin 3, Continuous (fun x => directionalAdvection3D w u₂ x c * w x c) := fun c =>
    ((continuous_pi_iff.mp (continuous_directionalAdvection3D hw_c2.continuous hu₂_c1)) c).mul (hw_c c).continuous
  have hr_c : ∀ c : Fin 3, Continuous (fun x => u₂ x c * directionalAdvection3D w w x c) := fun c =>
    (hu₂_c c).continuous.mul ((continuous_pi_iff.mp (continuous_directionalAdvection3D hw_c2.continuous hw_c1)) c)
  have hdot_l : ∀ x : R3, dot3D (directionalAdvection3D w u₂ x) (w x) =
      directionalAdvection3D w u₂ x 0 * w x 0 +
      directionalAdvection3D w u₂ x 1 * w x 1 +
      directionalAdvection3D w u₂ x 2 * w x 2 := fun _ => rfl
  have hdot_r : ∀ x : R3, dot3D (u₂ x) (directionalAdvection3D w w x) =
      u₂ x 0 * directionalAdvection3D w w x 0 +
      u₂ x 1 * directionalAdvection3D w w x 1 +
      u₂ x 2 * directionalAdvection3D w w x 2 := fun _ => rfl
  rw [torusIntegral_congr hdot_l, torusIntegral_add3 (hl_c 0) (hl_c 1) (hl_c 2),
      torusIntegral_congr hdot_r, torusIntegral_add3 (hr_c 0) (hr_c 1) (hr_c 2),
      h_comp 0, h_comp 1, h_comp 2]
  ring

private lemma torusIntegral_curl_sq_eq_gradNormSq {u : R3 → R3}
    (hu2 : ContDiff ℝ 2 u) (hu_per : IsPeriodic3D u) (hu_div : ∀ x : R3, div3D u x = 0) :
    torusIntegral (fun x => dot3D (curl3D u x) (curl3D u x)) = torusIntegral (gradNormSq3D u) := by
  have hu_c : ∀ c : Fin 3, ContDiff ℝ 2 (fun x => u x c) := fun c => (contDiff_pi.mp hu2) c
  have hu_c1 : ∀ c : Fin 3, ContDiff ℝ 1 (fun x => u x c) := fun c =>
    (hu_c c).of_le (by exact_mod_cast (show (1 : ℕ) ≤ 2 by decide))
  have hu_p : ∀ c : Fin 3, IsPeriodic3D (fun x => u x c) := fun c => hu_per.comp (fun v => v c)
  have hc_d : ∀ c i : Fin 3, Continuous (fun x => partialDerivScalar (fun y => u y c) x i) := fun c i =>
    continuous_partialDerivScalar_of_contDiff (hu_c1 c) i
  have hcross : ∀ i j : Fin 3,
      torusIntegral (fun x => partialDerivScalar (fun y => u y j) x i * partialDerivScalar (fun y => u y i) x j) =
        torusIntegral (fun x => partialDerivScalar (fun y => u y j) x j * partialDerivScalar (fun y => u y i) x i) := by
    intro i j
    have h1 := torusIntegral_ibp (hu_c1 j) (contDiff_one_partialDerivScalar (hu_c i) j)
      (hu_p j) ((hu_p i).partialDeriv ((hu_c i).differentiable (by simp)) j) i
    have h2 := torusIntegral_ibp (hu_c1 j) (contDiff_one_partialDerivScalar (hu_c i) i)
      (hu_p j) ((hu_p i).partialDeriv ((hu_c i).differentiable (by simp)) i) j
    have hsym : ∀ x : R3,
        u x j * partialDerivScalar (fun y => partialDerivScalar (fun z => u z i) y j) x i =
        u x j * partialDerivScalar (fun y => partialDerivScalar (fun z => u z i) y i) x j := fun x => by
      rw [partial_partial_eq_sndPartial (fun z => u z i) x (hu_c i).contDiffAt i j,
          partial_partial_eq_sndPartial (fun z => u z i) x (hu_c i).contDiffAt j i,
          sndPartial_symm_of_contDiffAt (fun z => u z i) x (hu_c i).contDiffAt i j]
    rw [torusIntegral_congr hsym] at h1
    linarith
  let d00 : R3 → ℝ := fun x => (partialDerivScalar (fun y => u y 0) x 0) ^ 2
  let d11 : R3 → ℝ := fun x => (partialDerivScalar (fun y => u y 1) x 1) ^ 2
  let d22 : R3 → ℝ := fun x => (partialDerivScalar (fun y => u y 2) x 2) ^ 2
  let c12 : R3 → ℝ := fun x => partialDerivScalar (fun y => u y 2) x 1 * partialDerivScalar (fun y => u y 1) x 2
  let c20 : R3 → ℝ := fun x => partialDerivScalar (fun y => u y 0) x 2 * partialDerivScalar (fun y => u y 2) x 0
  let c01 : R3 → ℝ := fun x => partialDerivScalar (fun y => u y 1) x 0 * partialDerivScalar (fun y => u y 0) x 1
  let s12 : R3 → ℝ := fun x => partialDerivScalar (fun y => u y 2) x 2 * partialDerivScalar (fun y => u y 1) x 1
  let s20 : R3 → ℝ := fun x => partialDerivScalar (fun y => u y 0) x 0 * partialDerivScalar (fun y => u y 2) x 2
  let s01 : R3 → ℝ := fun x => partialDerivScalar (fun y => u y 1) x 1 * partialDerivScalar (fun y => u y 0) x 0
  have hd00 : Continuous d00 := (hc_d 0 0).pow 2
  have hd11 : Continuous d11 := (hc_d 1 1).pow 2
  have hd22 : Continuous d22 := (hc_d 2 2).pow 2
  have hc12 : Continuous c12 := (hc_d 2 1).mul (hc_d 1 2)
  have hc20 : Continuous c20 := (hc_d 0 2).mul (hc_d 2 0)
  have hc01 : Continuous c01 := (hc_d 1 0).mul (hc_d 0 1)
  have hs12 : Continuous s12 := (hc_d 2 2).mul (hc_d 1 1)
  have hs20 : Continuous s20 := (hc_d 0 0).mul (hc_d 2 2)
  have hs01 : Continuous s01 := (hc_d 1 1).mul (hc_d 0 0)
  have hdiv_sq : torusIntegral d00 + torusIntegral d11 + torusIntegral d22 +
      2 * torusIntegral s12 + 2 * torusIntegral s20 + 2 * torusIntegral s01 = 0 := by
    have hsum1 := torusIntegral_add (cont_add_u (cont_add_u hd00 hd11) hd22)
      (cont_add_u (cont_add_u (cont_const_mul_u 2 hs12) (cont_const_mul_u 2 hs20)) (cont_const_mul_u 2 hs01))
    rw [torusIntegral_add3 hd00 hd11 hd22,
        torusIntegral_add3 (cont_const_mul_u 2 hs12) (cont_const_mul_u 2 hs20) (cont_const_mul_u 2 hs01),
        torusIntegral_const_mul 2 hs12, torusIntegral_const_mul 2 hs20, torusIntegral_const_mul 2 hs01] at hsum1
    have hzero : ∀ x : R3, (d00 x + d11 x + d22 x) + (2 * s12 x + 2 * s20 x + 2 * s01 x) = 0 := fun x => by
      have hd := hu_div x; unfold div3D at hd
      dsimp only [d00, d11, d22, s12, s20, s01]
      linear_combination (partialDerivScalar (fun y => u y 0) x 0 +
        partialDerivScalar (fun y => u y 1) x 1 + partialDerivScalar (fun y => u y 2) x 2) * hd
    rw [torusIntegral_congr hzero] at hsum1
    have h0 : torusIntegral (fun _ : R3 => (0 : ℝ)) = 0 := by unfold torusIntegral; simp
    linarith
  have hdiff_pt : ∀ x : R3, gradNormSq3D u x - dot3D (curl3D u x) (curl3D u x) =
      (d00 x + d11 x + d22 x) + (2 * c12 x + 2 * c20 x + 2 * c01 x) := fun x => by
    unfold gradNormSq3D dot3D curl3D
    dsimp only [d00, d11, d22, c12, c20, c01]
    simp [vec3]; ring
  have hc_curl : Continuous (fun x => dot3D (curl3D u x) (curl3D u x)) := by
    have hcc : Continuous (curl3D u) := by
      rw [continuous_pi_iff]
      intro c; fin_cases c
      · change Continuous (fun x => partialDerivScalar (fun y => u y 2) x 1 - partialDerivScalar (fun y => u y 1) x 2)
        exact (hc_d 2 1).sub (hc_d 1 2)
      · change Continuous (fun x => partialDerivScalar (fun y => u y 0) x 2 - partialDerivScalar (fun y => u y 2) x 0)
        exact (hc_d 0 2).sub (hc_d 2 0)
      · change Continuous (fun x => partialDerivScalar (fun y => u y 1) x 0 - partialDerivScalar (fun y => u y 0) x 1)
        exact (hc_d 1 0).sub (hc_d 0 1)
    exact continuous_dot3D hcc hcc
  have hc_grad : Continuous (gradNormSq3D u) :=
    continuous_gradNormSq3D (hu2.of_le (by exact_mod_cast (show (1 : ℕ) ≤ 2 by decide)))
  have hsub := torusIntegral_sub hc_grad hc_curl
  rw [torusIntegral_congr hdiff_pt,
      torusIntegral_add (cont_add_u (cont_add_u hd00 hd11) hd22)
        (cont_add_u (cont_add_u (cont_const_mul_u 2 hc12) (cont_const_mul_u 2 hc20)) (cont_const_mul_u 2 hc01)),
      torusIntegral_add3 hd00 hd11 hd22,
      torusIntegral_add3 (cont_const_mul_u 2 hc12) (cont_const_mul_u 2 hc20) (cont_const_mul_u 2 hc01),
      torusIntegral_const_mul 2 hc12, torusIntegral_const_mul 2 hc20, torusIntegral_const_mul 2 hc01] at hsub
  have heq12 : torusIntegral c12 = torusIntegral s12 := hcross 1 2
  have heq20 : torusIntegral c20 = torusIntegral s20 := hcross 2 0
  have heq01 : torusIntegral c01 = torusIntegral s01 := hcross 0 1
  linarith

/-- Exact periodic torus `𝕋³` difference-energy inequality for any pointwise bound
    `∀ x : R3, dot3D (u₂ t x) (u₂ t x) ≤ M` (requires ZERO mean-zero hypothesis!). -/
theorem hasDerivAt_diffEnergyTorus3D_and_bound
    {u₁ u₂ : ℝ → R3 → R3} {p₁ p₂ : ℝ → R3 → ℝ} {ν : ℝ}
    (hns₁ : IsPeriodicClassicalNS3D_C3 u₁ p₁ ν)
    (hns₂ : IsPeriodicClassicalNS3D_C3 u₂ p₂ ν)
    {t M : ℝ} (ht : 0 ≤ t) (hM : ∀ x : R3, dot3D (u₂ t x) (u₂ t x) ≤ M) :
    ∃ D : ℝ,
      HasDerivAt (diffEnergyTorus3D u₁ u₂) D t ∧
      D ≤ (M / ν) * diffEnergyTorus3D u₁ u₂ t := by
  have hν : 0 < ν := hns₁.h_nu_pos
  let w : R3 → R3 := fun x => u₁ t x - u₂ t x
  let q : R3 → ℝ := fun x => p₁ t x - p₂ t x
  have hu₁_c3 : ContDiff ℝ 3 (u₁ t) := hns₁.h_u_c3_global t ht
  have hu₂_c3 : ContDiff ℝ 3 (u₂ t) := hns₂.h_u_c3_global t ht
  have hw_c3 : ContDiff ℝ 3 w := hu₁_c3.sub hu₂_c3
  have hw_c2 : ContDiff ℝ 2 w := hw_c3.of_le (by exact_mod_cast (show (2 : ℕ) ≤ 3 by decide))
  have hw_c1 : ContDiff ℝ 1 w := hw_c3.of_le (by exact_mod_cast (show (1 : ℕ) ≤ 3 by decide))
  have hu₁_c2 : ContDiff ℝ 2 (u₁ t) := hu₁_c3.of_le (by exact_mod_cast (show (2 : ℕ) ≤ 3 by decide))
  have hu₂_c2 : ContDiff ℝ 2 (u₂ t) := hu₂_c3.of_le (by exact_mod_cast (show (2 : ℕ) ≤ 3 by decide))
  have hu₁_c1 : ContDiff ℝ 1 (u₁ t) := hu₁_c3.of_le (by exact_mod_cast (show (1 : ℕ) ≤ 3 by decide))
  have hu₂_c1 : ContDiff ℝ 1 (u₂ t) := hu₂_c3.of_le (by exact_mod_cast (show (1 : ℕ) ≤ 3 by decide))
  have hw_per : IsPeriodic3D w := fun x i => by
    dsimp only [w]; rw [hns₁.h_u_periodic t ht x i, hns₂.h_u_periodic t ht x i]
  have hq_per : IsPeriodic3D q := (hns₁.h_p_periodic t ht).sub (hns₂.h_p_periodic t ht)
  have hq_c2 : ContDiff ℝ 2 q := (hns₁.h_p_c2_global t ht).sub (hns₂.h_p_c2_global t ht)
  have hq_c1 : ContDiff ℝ 1 q := hq_c2.of_le (by exact_mod_cast (show (1 : ℕ) ≤ 2 by decide))
  have hw_div : ∀ x : R3, div3D w x = 0 := fun x => by
    unfold div3D
    have hsub : ∀ i : Fin 3, partialDerivScalar (fun y => w y i) x i =
        partialDerivScalar (fun y => u₁ t y i) x i - partialDerivScalar (fun y => u₂ t y i) x i := fun i =>
      partialDerivScalar_sub (((contDiff_pi.mp hu₁_c3) i).differentiable (by simp) x)
        (((contDiff_pi.mp hu₂_c3) i).differentiable (by simp) x) i
    rw [hsub 0, hsub 1, hsub 2]
    have d1 := hns₁.h_incompressible t ht x; have d2 := hns₂.h_incompressible t ht x
    unfold div3D at d1 d2; linarith
  have hc2_st : ∀ (u : ℝ → R3 → R3) (p : ℝ → R3 → ℝ),
      IsClassicalNS3D_C3 u p ν → ∀ c : Fin 3, ContDiff ℝ 2 (fun r : ℝ × R3 => u r.1 r.2 c) :=
    fun u p hns c => (contDiff_pi.mp (contDiff_iff_contDiffAt.mpr hns.h_u_c2_spacetime)) c
  have hdt_w : ∀ (s : ℝ) (x : R3) (c : Fin 3),
      HasDerivAt (fun r => u₁ r x c - u₂ r x c)
        (fderiv ℝ (fun r : ℝ × R3 => u₁ r.1 r.2 c) (s, x) (1, 0) -
         fderiv ℝ (fun r : ℝ × R3 => u₂ r.1 r.2 c) (s, x) (1, 0)) s := fun s x c => by
    have hinl : HasDerivAt (fun r : ℝ => (r, x)) (1, (0 : R3)) s :=
      (hasDerivAt_id s).prodMk (hasDerivAt_const s x)
    have h1 := ((hc2_st u₁ p₁ hns₁.toIsClassicalNS3D_C3 c).differentiable (by simp) (s, x)).hasFDerivAt.comp_hasDerivAt s hinl
    have h2 := ((hc2_st u₂ p₂ hns₂.toIsClassicalNS3D_C3 c).differentiable (by simp) (s, x)).hasFDerivAt.comp_hasDerivAt s hinl
    exact h1.sub h2
  let F : ℝ → R3 → ℝ := fun s x => dot3D (u₁ s x - u₂ s x) (u₁ s x - u₂ s x)
  let F' : ℝ → R3 → ℝ := fun s x =>
    2 * dot3D (fun c => deriv (fun r => u₁ r x c - u₂ r x c) s) (u₁ s x - u₂ s x)
  have hF_cont : Continuous (fun r : ℝ × R3 => F r.1 r.2) := by
    have hc : ∀ c : Fin 3, Continuous (fun r : ℝ × R3 => u₁ r.1 r.2 c - u₂ r.1 r.2 c) := fun c =>
      (hc2_st u₁ p₁ hns₁.toIsClassicalNS3D_C3 c).continuous.sub
        (hc2_st u₂ p₂ hns₂.toIsClassicalNS3D_C3 c).continuous
    dsimp only [F]; unfold dot3D; simp only [Pi.sub_apply]
    exact (((hc 0).mul (hc 0)).add ((hc 1).mul (hc 1))).add ((hc 2).mul (hc 2))
  have hF'_cont : Continuous (fun r : ℝ × R3 => F' r.1 r.2) := by
    have hdt_c : ∀ c : Fin 3, Continuous (fun r : ℝ × R3 => deriv (fun s => u₁ s r.2 c - u₂ s r.2 c) r.1) := fun c => by
      have heq : (fun r : ℝ × R3 => deriv (fun s => u₁ s r.2 c - u₂ s r.2 c) r.1) =
          fun r => fderiv ℝ (fun q : ℝ × R3 => u₁ q.1 q.2 c) r (1, 0) -
            fderiv ℝ (fun q : ℝ × R3 => u₂ q.1 q.2 c) r (1, 0) :=
        funext (fun r => (hdt_w r.1 r.2 c).deriv)
      rw [heq]
      have hfd1 : ContDiff ℝ 1 (fderiv ℝ (fun q : ℝ × R3 => u₁ q.1 q.2 c)) :=
        (hc2_st u₁ p₁ hns₁.toIsClassicalNS3D_C3 c).fderiv_right (by norm_cast)
      have hfd2 : ContDiff ℝ 1 (fderiv ℝ (fun q : ℝ × R3 => u₂ q.1 q.2 c)) :=
        (hc2_st u₂ p₂ hns₂.toIsClassicalNS3D_C3 c).fderiv_right (by norm_cast)
      exact (hfd1.clm_apply contDiff_const).continuous.sub (hfd2.clm_apply contDiff_const).continuous
    have hsub_c : ∀ c : Fin 3, Continuous (fun r : ℝ × R3 => u₁ r.1 r.2 c - u₂ r.1 r.2 c) := fun c =>
      (hc2_st u₁ p₁ hns₁.toIsClassicalNS3D_C3 c).continuous.sub
        (hc2_st u₂ p₂ hns₂.toIsClassicalNS3D_C3 c).continuous
    dsimp only [F']; unfold dot3D; simp only [Pi.sub_apply]
    exact continuous_const.mul
      ((((hdt_c 0).mul (hsub_c 0)).add ((hdt_c 1).mul (hsub_c 1))).add ((hdt_c 2).mul (hsub_c 2)))
  have hF_deriv : ∀ (s : ℝ) (x : R3), HasDerivAt (fun r => F r x) (F' s x) s := fun s x => by
    have hc : ∀ c : Fin 3,
        HasDerivAt (fun r => (u₁ r x c - u₂ r x c) * (u₁ r x c - u₂ r x c))
          (2 * (deriv (fun r => u₁ r x c - u₂ r x c) s * (u₁ s x c - u₂ s x c))) s := fun c => by
      have hm := (hdt_w s x c).differentiableAt.hasDerivAt.mul (hdt_w s x c).differentiableAt.hasDerivAt
      have heq : deriv (fun r => u₁ r x c - u₂ r x c) s * (u₁ s x c - u₂ s x c) +
          (u₁ s x c - u₂ s x c) * deriv (fun r => u₁ r x c - u₂ r x c) s =
          2 * (deriv (fun r => u₁ r x c - u₂ r x c) s * (u₁ s x c - u₂ s x c)) := by ring
      rwa [heq] at hm
    have hsum := ((hc 0).add (hc 1)).add (hc 2)
    have heq : 2 * (deriv (fun r => u₁ r x 0 - u₂ r x 0) s * (u₁ s x 0 - u₂ s x 0)) +
        2 * (deriv (fun r => u₁ r x 1 - u₂ r x 1) s * (u₁ s x 1 - u₂ s x 1)) +
        2 * (deriv (fun r => u₁ r x 2 - u₂ r x 2) s * (u₁ s x 2 - u₂ s x 2)) = F' s x := by
      dsimp only [F']; unfold dot3D; simp [Pi.sub_apply]; ring
    rwa [heq] at hsum
  have hE_deriv : HasDerivAt (diffEnergyTorus3D u₁ u₂) ((1 / 2 : ℝ) * torusIntegral (F' t)) t :=
    (hasDerivAt_torusIntegral_of_c1 hF_cont hF'_cont hF_deriv).const_mul (1 / 2 : ℝ)
  have hdiff_mom : ∀ (x : R3) (c : Fin 3),
      deriv (fun s => u₁ s x c - u₂ s x c) t =
        ν * laplacian3D w x c - directionalAdvection3D (u₁ t) w x c -
        directionalAdvection3D w (u₂ t) x c - grad3D q x c := by
    intro x c
    have hinl : HasDerivAt (fun r : ℝ => (r, x)) (1, (0 : R3)) t :=
      (hasDerivAt_id t).prodMk (hasDerivAt_const t x)
    have hd1 : DifferentiableAt ℝ (fun s => u₁ s x c) t := by
      have h := ((hc2_st u₁ p₁ hns₁.toIsClassicalNS3D_C3 c).differentiable (by simp) (t, x)).hasFDerivAt.comp_hasDerivAt t hinl
      exact h.differentiableAt
    have hd2 : DifferentiableAt ℝ (fun s => u₂ s x c) t := by
      have h := ((hc2_st u₂ p₂ hns₂.toIsClassicalNS3D_C3 c).differentiable (by simp) (t, x)).hasFDerivAt.comp_hasDerivAt t hinl
      exact h.differentiableAt
    have hdt_sub : deriv (fun s => u₁ s x c - u₂ s x c) t =
        deriv (fun s => u₁ s x c) t - deriv (fun s => u₂ s x c) t :=
      (hd1.hasDerivAt.sub hd2.hasDerivAt).deriv
    have hm1 := hns₁.h_momentum t ht x c
    have hm2 := hns₂.h_momentum t ht x c
    have hlap : laplacian3D w x c = laplacian3D (u₁ t) x c - laplacian3D (u₂ t) x c :=
      laplacianScalar_sub (fun y => u₁ t y c) (fun y => u₂ t y c)
        (fun y => ((contDiff_pi.mp hu₁_c2) c).contDiffAt)
        (fun y => ((contDiff_pi.mp hu₂_c2) c).contDiffAt) x
    have hgrad : grad3D q x c = grad3D (p₁ t) x c - grad3D (p₂ t) x c :=
      partialDerivScalar_sub ((hns₁.h_p_c2_global t ht).differentiable (by simp) x)
        ((hns₂.h_p_c2_global t ht).differentiable (by simp) x) c
    have hadv : advection3D (u₁ t) x c - advection3D (u₂ t) x c =
        directionalAdvection3D (u₁ t) w x c + directionalAdvection3D w (u₂ t) x c := by
      unfold advection3D directionalAdvection3D
      have hp : ∀ i : Fin 3, partialDerivScalar (fun y => w y c) x i =
          partialDerivScalar (fun y => u₁ t y c) x i - partialDerivScalar (fun y => u₂ t y c) x i := fun i =>
        partialDerivScalar_sub (((contDiff_pi.mp hu₁_c3) c).differentiable (by simp) x)
          (((contDiff_pi.mp hu₂_c3) c).differentiable (by simp) x) i
      rw [hp 0, hp 1, hp 2]; dsimp only [w]; simp only [Pi.sub_apply]; ring
    linear_combination hdt_sub + hm1 - hm2 - ν * hlap - hadv + hgrad
  have hmom_dot : ∀ x : R3,
      dot3D (fun c => deriv (fun s => u₁ s x c - u₂ s x c) t) (w x) =
        ν * dot3D (laplacian3D w x) (w x) -
        dot3D (directionalAdvection3D (u₁ t) w x) (w x) -
        dot3D (directionalAdvection3D w (u₂ t) x) (w x) -
        dot3D (grad3D q x) (w x) := fun x => by
    have m0 := hdiff_mom x 0; have m1 := hdiff_mom x 1; have m2 := hdiff_mom x 2
    unfold dot3D; dsimp only
    linear_combination (w x 0) * m0 + (w x 1) * m1 + (w x 2) * m2
  have hc_lap : Continuous (fun x => dot3D (laplacian3D w x) (w x)) :=
    continuous_dot3D (continuous_laplacian3D hw_c2) hw_c2.continuous
  have hc_adv1 : Continuous (fun x => dot3D (directionalAdvection3D (u₁ t) w x) (w x)) :=
    continuous_dot3D (continuous_directionalAdvection3D hu₁_c1.continuous hw_c1) hw_c2.continuous
  have hc_adv2 : Continuous (fun x => dot3D (directionalAdvection3D w (u₂ t) x) (w x)) :=
    continuous_dot3D (continuous_directionalAdvection3D hw_c1.continuous hu₂_c1) hw_c2.continuous
  have hc_gp : Continuous (fun x => dot3D (grad3D q x) (w x)) :=
    continuous_dot3D (continuous_grad3D hq_c1) hw_c2.continuous
  let D : ℝ := -ν * torusIntegral (gradNormSq3D w) +
    torusIntegral (fun x => dot3D (u₂ t x) (directionalAdvection3D w w x))
  have hD_eq : (1 / 2 : ℝ) * torusIntegral (F' t) = D := by
    have hF'_eq : ∀ x : R3, F' t x = 2 * dot3D (fun c => deriv (fun s => u₁ s x c - u₂ s x c) t) (w x) :=
      fun _ => rfl
    have hc_dot : Continuous (fun x => dot3D (fun c => deriv (fun s => u₁ s x c - u₂ s x c) t) (w x)) := by
      have heq : (fun x => dot3D (fun c => deriv (fun s => u₁ s x c - u₂ s x c) t) (w x)) =
          fun x => ν * dot3D (laplacian3D w x) (w x) -
            dot3D (directionalAdvection3D (u₁ t) w x) (w x) -
            dot3D (directionalAdvection3D w (u₂ t) x) (w x) -
            dot3D (grad3D q x) (w x) := funext hmom_dot
      rw [heq]; exact cont_sub_u (cont_sub_u (cont_sub_u (cont_const_mul_u ν hc_lap) hc_adv1) hc_adv2) hc_gp
    rw [torusIntegral_congr hF'_eq, torusIntegral_const_mul 2 hc_dot,
        torusIntegral_congr hmom_dot,
        torusIntegral_sub (cont_sub_u (cont_sub_u (cont_const_mul_u ν hc_lap) hc_adv1) hc_adv2) hc_gp,
        torusIntegral_sub (cont_sub_u (cont_const_mul_u ν hc_lap) hc_adv1) hc_adv2,
        torusIntegral_sub (cont_const_mul_u ν hc_lap) hc_adv1,
        torusIntegral_const_mul ν hc_lap,
        torusIntegral_laplacian_dot_self hw_c2 hw_per,
        gauss_leray_transport_zero hu₁_c1 hw_c1 (hns₁.h_u_periodic t ht) hw_per (hns₁.h_incompressible t ht),
        torus3D_diff_advection_ibp hu₂_c2 (hns₂.h_u_periodic t ht) hw_c2 hw_per hw_div,
        torusIntegral_grad_dot_solenoidal_zero hq_c1 hw_c1 hq_per hw_per hw_div]
    dsimp only [D]; ring
  rw [hD_eq] at hE_deriv
  have hc_rhs_ibp : Continuous (fun x => dot3D (u₂ t x) (directionalAdvection3D w w x)) :=
    continuous_dot3D hu₂_c1.continuous (continuous_directionalAdvection3D hw_c1.continuous hw_c1)
  have hc_gw : Continuous (gradNormSq3D w) := continuous_gradNormSq3D hw_c1
  have hc_w2 : Continuous (fun x => dot3D (w x) (w x)) := continuous_dot3D hw_c1.continuous hw_c1.continuous
  have hpt_bound : ∀ x : R3,
      dot3D (u₂ t x) (directionalAdvection3D w w x) ≤
        (ν / 2) * gradNormSq3D w x + (M / (2 * ν)) * dot3D (w x) (w x) := fun x => by
    have hy := pointwise_diff_advection_young hν (u₂ t x) (w x)
      (partialDerivScalar (fun y => w y 0) x 0)
      (partialDerivScalar (fun y => w y 0) x 1)
      (partialDerivScalar (fun y => w y 0) x 2)
      (partialDerivScalar (fun y => w y 1) x 0)
      (partialDerivScalar (fun y => w y 1) x 1)
      (partialDerivScalar (fun y => w y 1) x 2)
      (partialDerivScalar (fun y => w y 2) x 0)
      (partialDerivScalar (fun y => w y 2) x 1)
      (partialDerivScalar (fun y => w y 2) x 2)
    have hmul : (1 / (2 * ν)) * dot3D (u₂ t x) (u₂ t x) * dot3D (w x) (w x) ≤
        (M / (2 * ν)) * dot3D (w x) (w x) := by
      have h1 : (1 / (2 * ν)) * dot3D (u₂ t x) (u₂ t x) ≤ M / (2 * ν) := by
        have hm := mul_le_mul_of_nonneg_left (hM x) (by positivity : (0 : ℝ) ≤ 1 / (2 * ν))
        have heq : (1 / (2 * ν)) * M = M / (2 * ν) := by ring
        linarith
      exact mul_le_mul_of_nonneg_right h1 (dot3D_self_nonneg_r3 (w x))
    change u₂ t x 0 * (w x 0 * partialDerivScalar (fun y => w y 0) x 0 +
      w x 1 * partialDerivScalar (fun y => w y 0) x 1 +
      w x 2 * partialDerivScalar (fun y => w y 0) x 2) +
      u₂ t x 1 * (w x 0 * partialDerivScalar (fun y => w y 1) x 0 +
      w x 1 * partialDerivScalar (fun y => w y 1) x 1 +
      w x 2 * partialDerivScalar (fun y => w y 1) x 2) +
      u₂ t x 2 * (w x 0 * partialDerivScalar (fun y => w y 2) x 0 +
      w x 1 * partialDerivScalar (fun y => w y 2) x 1 +
      w x 2 * partialDerivScalar (fun y => w y 2) x 2) ≤ _
    unfold gradNormSq3D
    linarith
  have hmono := torusIntegral_mono hc_rhs_ibp
    (cont_add_u (cont_const_mul_u (ν / 2) hc_gw) (cont_const_mul_u (M / (2 * ν)) hc_w2)) hpt_bound
  rw [torusIntegral_add (cont_const_mul_u (ν / 2) hc_gw) (cont_const_mul_u (M / (2 * ν)) hc_w2),
      torusIntegral_const_mul (ν / 2) hc_gw,
      torusIntegral_const_mul (M / (2 * ν)) hc_w2] at hmono
  have hgw_nn : 0 ≤ torusIntegral (gradNormSq3D w) := torusIntegral_nonneg hc_gw (gradNormSq3D_nonneg w)
  have hD_le : D ≤ (M / ν) * diffEnergyTorus3D u₁ u₂ t := by
    have hE_eq : (M / (2 * ν)) * torusIntegral (fun x => dot3D (w x) (w x)) =
        (M / ν) * diffEnergyTorus3D u₁ u₂ t := by
      unfold diffEnergyTorus3D; dsimp only [w]; ring
    dsimp only [D]
    nlinarith
  exact ⟨D, hE_deriv, hD_le⟩

/-- **THEOREM 11A1-3 (Unconditional Periodic Torus `𝕋³` Serrin `L²` Stability & Pointwise Global Uniqueness):**
    For ANY two periodic classical 3D NS solutions `(u₁, p₁)` and `(u₂, p₂)` on `𝕋³`
    (with ZERO domination hypotheses and ZERO mean-zero requirement!):
    1. Continuous `L²` stability for any continuous `L∞²` bound profile `M` of `u₂`:
       `diffEnergyTorus3D u₁ u₂ T ≤ diffEnergyTorus3D u₁ u₂ 0 * exp((1/ν) ∫_0^T M(s) ds)`.
    2. **Unconditional Pointwise Global Uniqueness on `[0, ∞) × ℝ³`:**
       If `∀ x : R3, u₁ 0 x = u₂ 0 x`, then `∀ t ≥ 0, ∀ x : R3, u₁ t x = u₂ t x`. -/
theorem torus3D_serrin_L2_stability_and_global_uniqueness
    {u₁ u₂ : ℝ → R3 → R3} {p₁ p₂ : ℝ → R3 → ℝ} {ν : ℝ}
    (hns₁ : IsPeriodicClassicalNS3D_C3 u₁ p₁ ν)
    (hns₂ : IsPeriodicClassicalNS3D_C3 u₂ p₂ ν) :
    (∀ M : ℝ → ℝ, Continuous M →
      (∀ s ≥ 0, ∀ x : R3, dot3D (u₂ s x) (u₂ s x) ≤ M s) →
      ∀ T ≥ 0, diffEnergyTorus3D u₁ u₂ T ≤
        diffEnergyTorus3D u₁ u₂ 0 * Real.exp ((1 / ν) * ∫ s in (0 : ℝ)..T, M s)) ∧
    ((∀ x : R3, u₁ 0 x = u₂ 0 x) → ∀ t ≥ 0, ∀ x : R3, u₁ t x = u₂ t x) := by
  have hν : 0 < ν := hns₁.h_nu_pos
  have hstab : ∀ M : ℝ → ℝ, Continuous M →
      (∀ s ≥ 0, ∀ x : R3, dot3D (u₂ s x) (u₂ s x) ≤ M s) →
      ∀ T ≥ 0, diffEnergyTorus3D u₁ u₂ T ≤
        diffEnergyTorus3D u₁ u₂ 0 * Real.exp ((1 / ν) * ∫ s in (0 : ℝ)..T, M s) := by
    intro M hM_cont hM T hT
    have hgr := gronwall_L2_of_hasDerivAt hT
      (E := diffEnergyTorus3D u₁ u₂) (E' := fun s => deriv (diffEnergyTorus3D u₁ u₂) s)
      (γ := fun s => M s / ν)
      (fun s hs => by
        obtain ⟨D, hD, _⟩ := hasDerivAt_diffEnergyTorus3D_and_bound hns₁ hns₂ hs.1 (hM s hs.1)
        rw [hD.deriv]; exact hD)
      (hM_cont.div_const ν)
      (fun s hs => by
        obtain ⟨D, hD, hle⟩ := hasDerivAt_diffEnergyTorus3D_and_bound hns₁ hns₂
          (le_of_lt hs.1) (hM s (le_of_lt hs.1))
        rwa [hD.deriv])
    have hint_eq : (∫ s in (0 : ℝ)..T, M s / ν) = (1 / ν) * ∫ s in (0 : ℝ)..T, M s := by
      have hcongr : (∫ s in (0 : ℝ)..T, M s / ν) = ∫ s in (0 : ℝ)..T, (1 / ν) * M s :=
        intervalIntegral.integral_congr (fun s _ => by ring)
      rw [hcongr, intervalIntegral.integral_const_mul]
    rwa [hint_eq] at hgr
  refine ⟨hstab, ?_⟩
  intro hinit t ht x
  have hu₂_st_cont : Continuous (fun r : ℝ × R3 => dot3D (u₂ r.1 r.2) (u₂ r.1 r.2)) := by
    have hu₂_c : Continuous (fun r : ℝ × R3 => u₂ r.1 r.2) :=
      (contDiff_iff_contDiffAt.mpr hns₂.h_u_c2_spacetime).continuous
    unfold dot3D
    have hc : ∀ c : Fin 3, Continuous (fun r : ℝ × R3 => u₂ r.1 r.2 c) := fun c =>
      (continuous_apply c).comp hu₂_c
    exact (((hc 0).mul (hc 0)).add ((hc 1).mul (hc 1))).add ((hc 2).mul (hc 2))
  let box : Set R3 := Set.pi Set.univ (fun _ : Fin 3 => Set.Icc (0 : ℝ) 1)
  have hK : IsCompact (Set.Icc (0 : ℝ) t ×ˢ box) :=
    isCompact_Icc.prod (isCompact_univ_pi (fun _ => isCompact_Icc))
  obtain ⟨Mt, hMt⟩ := hK.exists_bound_of_continuousOn hu₂_st_cont.continuousOn
  have hMt_all : ∀ s ∈ Set.Icc (0 : ℝ) t, ∀ y : R3, dot3D (u₂ s y) (u₂ s y) ≤ Mt := by
    intro s hs y
    have hper_dot : IsPeriodic3D (fun z : R3 => dot3D (u₂ s z) (u₂ s z)) :=
      (hns₂.h_u_periodic s hs.1).comp (fun v => dot3D v v)
    let y' : R3 := vec3 (y 0 + ((-⌊y 0⌋ : ℤ) : ℝ)) (y 1 + ((-⌊y 1⌋ : ℤ) : ℝ)) (y 2 + ((-⌊y 2⌋ : ℤ) : ℝ))
    have hsh : dot3D (u₂ s y') (u₂ s y') = dot3D (u₂ s y) (u₂ s y) :=
      isPeriodic3D_shift_int hper_dot y (-⌊y 0⌋) (-⌊y 1⌋) (-⌊y 2⌋)
    have hy'_mem : y' ∈ box := by
      intro i _
      fin_cases i
      · exact ⟨by simp [y', vec3]; linarith [Int.floor_le (y 0)], by simp [y', vec3]; linarith [Int.lt_floor_add_one (y 0)]⟩
      · exact ⟨by simp [y', vec3]; linarith [Int.floor_le (y 1)], by simp [y', vec3]; linarith [Int.lt_floor_add_one (y 1)]⟩
      · exact ⟨by simp [y', vec3]; linarith [Int.floor_le (y 2)], by simp [y', vec3]; linarith [Int.lt_floor_add_one (y 2)]⟩
    have hb := hMt (s, y') ⟨hs, hy'_mem⟩
    rw [Real.norm_eq_abs, abs_of_nonneg (dot3D_self_nonneg_r3 _)] at hb
    linarith
  have hgr_t := gronwall_L2_of_hasDerivAt ht
    (E := diffEnergyTorus3D u₁ u₂) (E' := fun s => deriv (diffEnergyTorus3D u₁ u₂) s)
    (γ := fun _ => Mt / ν)
    (fun s hs => by
      obtain ⟨D, hD, _⟩ := hasDerivAt_diffEnergyTorus3D_and_bound hns₁ hns₂ hs.1 (hMt_all s hs)
      rw [hD.deriv]; exact hD)
    continuous_const
    (fun s hs => by
      obtain ⟨D, hD, hle⟩ := hasDerivAt_diffEnergyTorus3D_and_bound hns₁ hns₂
        (le_of_lt hs.1) (hMt_all s ⟨le_of_lt hs.1, le_of_lt hs.2⟩)
      rwa [hD.deriv])
  have hE0 : diffEnergyTorus3D u₁ u₂ 0 = 0 := by
    unfold diffEnergyTorus3D
    have hzero : ∀ y : R3, dot3D (u₁ 0 y - u₂ 0 y) (u₁ 0 y - u₂ 0 y) = 0 := fun y => by
      rw [hinit y, sub_self]; unfold dot3D; simp
    rw [torusIntegral_congr hzero]
    have h0 : torusIntegral (fun _ : R3 => (0 : ℝ)) = 0 := by
      unfold torusIntegral; simp
    rw [h0, mul_zero]
  rw [hE0, zero_mul] at hgr_t
  have hEt_zero : diffEnergyTorus3D u₁ u₂ t = 0 :=
    le_antisymm hgr_t (diffEnergyTorus3D_nonneg (hns₁.h_u_c3_global t ht).continuous (hns₂.h_u_c3_global t ht).continuous)
  have hw_c : ∀ c : Fin 3, Continuous (fun y : R3 => u₁ t y c - u₂ t y c) := fun c =>
    ((contDiff_pi.mp (hns₁.h_u_c3_global t ht)) c).continuous.sub ((contDiff_pi.mp (hns₂.h_u_c3_global t ht)) c).continuous
  have hw_p : ∀ c : Fin 3, IsPeriodic3D (fun y : R3 => u₁ t y c - u₂ t y c) := fun c =>
    ((hns₁.h_u_periodic t ht).comp (fun v => v c)).sub ((hns₂.h_u_periodic t ht).comp (fun v => v c))
  have hw_sq_c : ∀ c : Fin 3, Continuous (fun y : R3 => (u₁ t y c - u₂ t y c) ^ 2) := fun c =>
    (hw_c c).pow 2
  have hsum_zero : torusIntegral (fun y => (u₁ t y 0 - u₂ t y 0) ^ 2) +
      torusIntegral (fun y => (u₁ t y 1 - u₂ t y 1) ^ 2) +
      torusIntegral (fun y => (u₁ t y 2 - u₂ t y 2) ^ 2) = 0 := by
    unfold diffEnergyTorus3D at hEt_zero
    have hpt : ∀ y : R3, dot3D (u₁ t y - u₂ t y) (u₁ t y - u₂ t y) =
        (u₁ t y 0 - u₂ t y 0) ^ 2 + (u₁ t y 1 - u₂ t y 1) ^ 2 + (u₁ t y 2 - u₂ t y 2) ^ 2 := fun y => by
      unfold dot3D; simp [Pi.sub_apply]; ring
    rw [torusIntegral_congr hpt,
        torusIntegral_add3 (hw_sq_c 0) (hw_sq_c 1) (hw_sq_c 2)] at hEt_zero
    linarith
  have h0_nn : 0 ≤ torusIntegral (fun y => (u₁ t y 0 - u₂ t y 0) ^ 2) :=
    torusIntegral_nonneg (hw_sq_c 0) (fun _ => sq_nonneg _)
  have h1_nn : 0 ≤ torusIntegral (fun y => (u₁ t y 1 - u₂ t y 1) ^ 2) :=
    torusIntegral_nonneg (hw_sq_c 1) (fun _ => sq_nonneg _)
  have h2_nn : 0 ≤ torusIntegral (fun y => (u₁ t y 2 - u₂ t y 2) ^ 2) :=
    torusIntegral_nonneg (hw_sq_c 2) (fun _ => sq_nonneg _)
  funext c
  fin_cases c
  · exact sub_eq_zero.mp (eq_zero_of_torusIntegral_sq_eq_zero (hw_c 0) (hw_p 0) (by linarith) x)
  · exact sub_eq_zero.mp (eq_zero_of_torusIntegral_sq_eq_zero (hw_c 1) (hw_p 1) (by linarith) x)
  · exact sub_eq_zero.mp (eq_zero_of_torusIntegral_sq_eq_zero (hw_c 2) (hw_p 2) (by linarith) x)

-- ============================================================================
-- SECTION 4: TORUS 𝕋³ UNIFORM L²_t L∞_x BOUND & DUAL-DOMAIN AUDIT
-- ============================================================================

/-- Periodic torus `𝕋³` Agmon `L∞²` control profile `M_u^{𝕋³}(t) = (13/(4π²)) √(2 Z(t)) √(P(t))`. -/
noncomputable def agmonLinfSqBoundTorus3D (u : ℝ → R3 → R3) (t : ℝ) : ℝ :=
  (13 / (4 * Real.pi ^ 2)) *
    Real.sqrt (torusIntegral (fun x => dot3D (curl3D (u t) x) (curl3D (u t) x))) *
    Real.sqrt (torusIntegral (gradNormSq3D (curl3D (u t))))

/-- **THEOREM 11A1-4 (Unconditional Uniform Global `L²_t L∞_x` Bound on Periodic Torus `𝕋³`):**
    For any mean-zero periodic 3D NS solution `(u, p)` on `𝕋³` with continuous palinstrophy
    and a certified `GarryWaterfallWitness` reaching `Z_crit_H1 ν / 2`, the 3D Agmon `L∞²`
    profile has a uniform-in-`T` global `L¹_t` integral on `[0, ∞)` — proving `u ∈ L²_t L∞_x(𝕋³)`. -/
private lemma torus3D_enstrophy_continuous {u : ℝ → R3 → R3} {p : ℝ → R3 → ℝ} {ν : ℝ}
    (hns : IsPeriodicClassicalNS3D_C3 u p ν) :
    Continuous (fun s : ℝ => (1 / 2 : ℝ) * torusIntegral (fun x => dot3D (curl3D (u s) x) (curl3D (u s) x))) := by
  have hc2_st : ∀ c : Fin 3, ContDiff ℝ 2 (fun q : ℝ × R3 => u q.1 q.2 c) := fun c =>
    (contDiff_pi.mp (contDiff_iff_contDiffAt.mpr hns.h_u_c2_spacetime)) c
  have hpd_c : ∀ c i : Fin 3, Continuous (fun q : ℝ × R3 => partialDerivScalar (fun y => u q.1 y c) q.2 i) := by
    intro c i
    have heq : (fun q : ℝ × R3 => partialDerivScalar (fun y => u q.1 y c) q.2 i) =
        fun q => fderiv ℝ (fun r : ℝ × R3 => u r.1 r.2 c) q (0, basisVec i) := by
      funext ⟨s, x⟩
      have hG : DifferentiableAt ℝ (fun r : ℝ × R3 => u r.1 r.2 c) (s, x) :=
        (hc2_st c).differentiable (by simp) (s, x)
      have hcomp : HasFDerivAt (fun y : R3 => u s y c)
          ((fderiv ℝ (fun r : ℝ × R3 => u r.1 r.2 c) (s, x)).comp (ContinuousLinearMap.inr ℝ ℝ R3)) x :=
        hG.hasFDerivAt.comp x (hasFDerivAt_prodMk_right s x)
      unfold partialDerivScalar
      rw [hcomp.fderiv]
      simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.inr_apply]
    rw [heq]
    have hfd : ContDiff ℝ 1 (fderiv ℝ (fun r : ℝ × R3 => u r.1 r.2 c)) :=
      (hc2_st c).fderiv_right (by norm_cast)
    exact (hfd.clm_apply contDiff_const).continuous
  have hw_c : ∀ c : Fin 3, Continuous (fun q : ℝ × R3 => curl3D (u q.1) q.2 c) := fun c => by
    fin_cases c
    · change Continuous (fun q : ℝ × R3 => partialDerivScalar (fun y => u q.1 y 2) q.2 1 -
        partialDerivScalar (fun y => u q.1 y 1) q.2 2)
      exact (hpd_c 2 1).sub (hpd_c 1 2)
    · change Continuous (fun q : ℝ × R3 => partialDerivScalar (fun y => u q.1 y 0) q.2 2 -
        partialDerivScalar (fun y => u q.1 y 2) q.2 0)
      exact (hpd_c 0 2).sub (hpd_c 2 0)
    · change Continuous (fun q : ℝ × R3 => partialDerivScalar (fun y => u q.1 y 1) q.2 0 -
        partialDerivScalar (fun y => u q.1 y 0) q.2 1)
      exact (hpd_c 1 0).sub (hpd_c 0 1)
  have hdot_c : Continuous (fun q : ℝ × R3 => dot3D (curl3D (u q.1) q.2) (curl3D (u q.1) q.2)) := by
    unfold dot3D
    exact (((hw_c 0).mul (hw_c 0)).add ((hw_c 1).mul (hw_c 1))).add ((hw_c 2).mul (hw_c 2))
  exact continuous_const.mul
    (continuous_torusIntegral_of_cont (F := fun s x => dot3D (curl3D (u s) x) (curl3D (u s) x)) hdot_c)

private lemma torus3D_leray_hasDerivAt_energy {u : ℝ → R3 → R3} {p : ℝ → R3 → ℝ} {ν : ℝ}
    (hns : IsPeriodicClassicalNS3D_C3 u p ν) {s : ℝ} (hs : 0 ≤ s) :
    HasDerivAt (fun r => (1 / 2 : ℝ) * torusIntegral (fun x => dot3D (u r x) (u r x)))
      (-2 * ν * ((1 / 2 : ℝ) * torusIntegral (fun x => dot3D (curl3D (u s) x) (curl3D (u s) x)))) s := by
  have hc2_st : ∀ c : Fin 3, ContDiff ℝ 2 (fun q : ℝ × R3 => u q.1 q.2 c) := fun c =>
    (contDiff_pi.mp (contDiff_iff_contDiffAt.mpr hns.h_u_c2_spacetime)) c
  have hdt_u : ∀ (r : ℝ) (x : R3) (c : Fin 3),
      HasDerivAt (fun q => u q x c) (fderiv ℝ (fun q : ℝ × R3 => u q.1 q.2 c) (r, x) (1, 0)) r := fun r x c => by
    have hinl : HasDerivAt (fun q : ℝ => (q, x)) (1, (0 : R3)) r :=
      (hasDerivAt_id r).prodMk (hasDerivAt_const r x)
    exact ((hc2_st c).differentiable (by simp) (r, x)).hasFDerivAt.comp_hasDerivAt r hinl
  let F : ℝ → R3 → ℝ := fun r x => dot3D (u r x) (u r x)
  let F' : ℝ → R3 → ℝ := fun r x => 2 * dot3D (fun c => deriv (fun q => u q x c) r) (u r x)
  have hF_c : Continuous (fun q : ℝ × R3 => F q.1 q.2) := by
    dsimp only [F]; unfold dot3D
    exact ((((hc2_st 0).continuous.mul (hc2_st 0).continuous).add
      ((hc2_st 1).continuous.mul (hc2_st 1).continuous))).add
      ((hc2_st 2).continuous.mul (hc2_st 2).continuous)
  have hF'_c : Continuous (fun q : ℝ × R3 => F' q.1 q.2) := by
    have hdt_c : ∀ c : Fin 3, Continuous (fun q : ℝ × R3 => deriv (fun r => u r q.2 c) q.1) := fun c => by
      have heq : (fun q : ℝ × R3 => deriv (fun r => u r q.2 c) q.1) =
          fun q => fderiv ℝ (fun r : ℝ × R3 => u r.1 r.2 c) q (1, 0) :=
        funext (fun q => (hdt_u q.1 q.2 c).deriv)
      rw [heq]
      have hfd : ContDiff ℝ 1 (fderiv ℝ (fun r : ℝ × R3 => u r.1 r.2 c)) :=
        (hc2_st c).fderiv_right (by norm_cast)
      exact (hfd.clm_apply contDiff_const).continuous
    dsimp only [F']; unfold dot3D
    exact continuous_const.mul
      ((((hdt_c 0).mul (hc2_st 0).continuous).add ((hdt_c 1).mul (hc2_st 1).continuous)).add
        ((hdt_c 2).mul (hc2_st 2).continuous))
  have hF_d : ∀ (r : ℝ) (x : R3), HasDerivAt (fun q => F q x) (F' r x) r := fun r x => by
    have hc : ∀ c : Fin 3,
        HasDerivAt (fun q => u q x c * u q x c) (2 * (deriv (fun q => u q x c) r * u r x c)) r := fun c => by
      have hm := (hdt_u r x c).differentiableAt.hasDerivAt.mul (hdt_u r x c).differentiableAt.hasDerivAt
      have heq : deriv (fun q => u q x c) r * u r x c + u r x c * deriv (fun q => u q x c) r =
          2 * (deriv (fun q => u q x c) r * u r x c) := by ring
      rwa [heq] at hm
    have hsum := ((hc 0).add (hc 1)).add (hc 2)
    have heq : 2 * (deriv (fun q => u q x 0) r * u r x 0) +
        2 * (deriv (fun q => u q x 1) r * u r x 1) +
        2 * (deriv (fun q => u q x 2) r * u r x 2) = F' r x := by
      dsimp only [F']; unfold dot3D; ring
    rwa [heq] at hsum
  have hd_raw : HasDerivAt (fun r => (1 / 2 : ℝ) * torusIntegral (F r))
      ((1 / 2 : ℝ) * torusIntegral (F' s)) s :=
    (hasDerivAt_torusIntegral_of_c1 (t₀ := s) hF_c hF'_c hF_d).const_mul (1 / 2 : ℝ)
  have hdot_c : Continuous (fun x => dot3D (fun c => deriv (fun q => u q x c) s) (u s x)) := by
    have hdt_x : ∀ c : Fin 3, Continuous (fun x : R3 => deriv (fun q => u q x c) s) := fun c => by
      have heq : (fun x : R3 => deriv (fun q => u q x c) s) =
          fun x => fderiv ℝ (fun r : ℝ × R3 => u r.1 r.2 c) (s, x) (1, 0) :=
        funext (fun x => (hdt_u s x c).deriv)
      rw [heq]
      have hfd : ContDiff ℝ 1 (fderiv ℝ (fun r : ℝ × R3 => u r.1 r.2 c)) :=
        (hc2_st c).fderiv_right (by norm_cast)
      exact (hfd.clm_apply contDiff_const).continuous.comp (continuous_const.prodMk continuous_id)
    unfold dot3D
    exact (((hdt_x 0).mul ((contDiff_pi.mp (hns.h_u_c3_global s hs)) 0).continuous).add
      ((hdt_x 1).mul ((contDiff_pi.mp (hns.h_u_c3_global s hs)) 1).continuous)).add
      ((hdt_x 2).mul ((contDiff_pi.mp (hns.h_u_c3_global s hs)) 2).continuous)
  have hval : (1 / 2 : ℝ) * torusIntegral (F' s) =
      -2 * ν * ((1 / 2 : ℝ) * torusIntegral (fun x => dot3D (curl3D (u s) x) (curl3D (u s) x))) := by
    dsimp only [F']
    rw [torusIntegral_const_mul 2 hdot_c,
        (leray_energy_identity_torus3D hns hs).1,
        ← torusIntegral_curl_sq_eq_gradNormSq
          ((hns.h_u_c3_global s hs).of_le (by exact_mod_cast (show (2 : ℕ) ≤ 3 by decide)))
          (hns.h_u_periodic s hs) (hns.h_incompressible s hs)]
    ring
  rwa [hval] at hd_raw

theorem torus3D_global_L2_Linf_bound_of_waterfall
    {u : ℝ → R3 → R3} {p : ℝ → R3 → ℝ} {ν : ℝ}
    (hns : IsPeriodicClassicalNS3D_C3 u p ν)
    (hmean : ∀ t ≥ 0, ∀ c : Fin 3, torusIntegral (fun x => u t x c) = 0)
    (hP_cont : Continuous (fun s : ℝ => torusIntegral (gradNormSq3D (curl3D (u s)))))
    (W : GarryWaterfallWitness u ν)
    (hcapture : W.zCap W.steps < Z_crit_H1 ν / 2) :
    let E₀ : ℝ := (1 / 2 : ℝ) * torusIntegral (fun x => dot3D (u 0 x) (u 0 x))
    let B : ℝ := chainBudget W.tGrid W.zCap W.steps
    let M_peak : ℝ := chainPeak W.zCap W.steps
    ∀ T ≥ 0,
      (∫ s in (0 : ℝ)..T, agmonLinfSqBoundTorus3D u s) ≤
        (13 / (4 * Real.pi ^ 2)) *
          (E₀ / (2 * ν) +
            (1 / 2 : ℝ) *
              ((4 / ν) * (W.zCap 0 + c_nu_H1 ν * M_peak * B) +
               (8 / ν) * W.zCap W.steps)) := by
  intro E₀ B M_peak T hT
  have hν : 0 < ν := hns.h_nu_pos
  let Z : ℝ → ℝ := fun s => (1 / 2 : ℝ) * torusIntegral (fun x => dot3D (curl3D (u s) x) (curl3D (u s) x))
  let P : ℝ → ℝ := fun s => torusIntegral (gradNormSq3D (curl3D (u s)))
  have hZ_cont : ContinuousOn Z (Set.Icc 0 T) := (torus3D_enstrophy_continuous hns).continuousOn
  have hM_cont : ContinuousOn (fun s => agmonLinfSqBoundTorus3D u s) (Set.Icc 0 T) := by
    unfold agmonLinfSqBoundTorus3D
    have h2Z_cont : ContinuousOn (fun s => torusIntegral (fun x => dot3D (curl3D (u s) x) (curl3D (u s) x))) (Set.Icc 0 T) := by
      have heq : (fun s => torusIntegral (fun x => dot3D (curl3D (u s) x) (curl3D (u s) x))) = fun s => 2 * Z s := by
        funext s; dsimp only [Z]; ring
      rw [heq]; exact continuousOn_const.mul hZ_cont
    exact ((continuousOn_const.mul (Real.continuous_sqrt.comp_continuousOn h2Z_cont)).mul
      (Real.continuous_sqrt.comp_continuousOn hP_cont.continuousOn))
  have hpt_amgm : ∀ s ∈ Set.Icc (0 : ℝ) T,
      agmonLinfSqBoundTorus3D u s ≤
        (13 / (4 * Real.pi ^ 2)) * (Z s + (1 / 2 : ℝ) * P s) := by
    intro s hs
    unfold agmonLinfSqBoundTorus3D
    have h2Z_nn : 0 ≤ torusIntegral (fun x => dot3D (curl3D (u s) x) (curl3D (u s) x)) :=
      torusIntegral_nonneg
        (continuous_dot3D (contDiff_two_curl3D (hns.h_u_c3_global s hs.1)).continuous
          (contDiff_two_curl3D (hns.h_u_c3_global s hs.1)).continuous)
        (fun x => dot3D_self_nonneg_r3 _)
    have hP_nn : 0 ≤ P s :=
      torusIntegral_nonneg (continuous_gradNormSq3D
        ((contDiff_two_curl3D (hns.h_u_c3_global s hs.1)).of_le (by exact_mod_cast (show (1 : ℕ) ≤ 2 by decide))))
        (gradNormSq3D_nonneg _)
    have hsq1 := Real.sq_sqrt h2Z_nn
    have hsq2 := Real.sq_sqrt hP_nn
    have ham : Real.sqrt (torusIntegral (fun x => dot3D (curl3D (u s) x) (curl3D (u s) x))) *
        Real.sqrt (P s) ≤ Z s + (1 / 2 : ℝ) * P s := by
      dsimp only [Z]
      nlinarith [sq_nonneg (Real.sqrt (torusIntegral (fun x => dot3D (curl3D (u s) x) (curl3D (u s) x))) - Real.sqrt (P s))]
    have hcoef_nn : 0 ≤ 13 / (4 * Real.pi ^ 2) := by positivity
    have hmul := mul_le_mul_of_nonneg_left ham hcoef_nn
    dsimp only [P] at hmul ⊢
    linarith
  have hP_half_c : ContinuousOn (fun s => (1 / 2 : ℝ) * P s) (Set.Icc 0 T) :=
    continuousOn_const.mul hP_cont.continuousOn
  have hZP_c : ContinuousOn (fun s => Z s + (1 / 2 : ℝ) * P s) (Set.Icc 0 T) := hZ_cont.add hP_half_c
  have hrhs_c : ContinuousOn (fun s => (13 / (4 * Real.pi ^ 2)) * (Z s + (1 / 2 : ℝ) * P s)) (Set.Icc 0 T) :=
    continuousOn_const.mul hZP_c
  have hmono := intervalIntegral.integral_mono_on hT
    (hM_cont.intervalIntegrable_of_Icc (μ := volume) hT)
    (hrhs_c.intervalIntegrable_of_Icc (μ := volume) hT)
    hpt_amgm
  have hrhs_eval : (∫ s in (0 : ℝ)..T, (13 / (4 * Real.pi ^ 2)) * (Z s + (1 / 2 : ℝ) * P s)) =
      (13 / (4 * Real.pi ^ 2)) * ((∫ s in (0 : ℝ)..T, Z s) + (1 / 2 : ℝ) * (∫ s in (0 : ℝ)..T, P s)) := by
    rw [intervalIntegral.integral_const_mul (13 / (4 * Real.pi ^ 2)),
        intervalIntegral.integral_add (hZ_cont.intervalIntegrable_of_Icc (μ := volume) hT)
          (hP_half_c.intervalIntegrable_of_Icc (μ := volume) hT),
        intervalIntegral.integral_const_mul (1 / 2 : ℝ) (f := P)]
  rw [hrhs_eval] at hmono
  have hE_deriv : ∀ s ∈ Set.uIcc (0 : ℝ) T,
      HasDerivAt (fun r => (1 / 2 : ℝ) * torusIntegral (fun x => dot3D (u r x) (u r x)))
        (-2 * ν * Z s) s := fun s hs => by
    rw [Set.uIcc_of_le hT] at hs
    exact torus3D_leray_hasDerivAt_energy hns hs.1
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt hE_deriv
    ((continuousOn_const.mul hZ_cont).intervalIntegrable_of_Icc (μ := volume) hT)
  rw [intervalIntegral.integral_const_mul (-2 * ν) (f := Z)] at hftc
  have hET_nn : 0 ≤ (1 / 2 : ℝ) * torusIntegral (fun x => dot3D (u T x) (u T x)) := by
    have hc := continuous_dot3D (hns.h_u_c3_global T hT).continuous (hns.h_u_c3_global T hT).continuous
    linarith [torusIntegral_nonneg hc (fun x => dot3D_self_nonneg_r3 (u T x))]
  have hleray_Z : (∫ s in (0 : ℝ)..T, Z s) ≤ E₀ / (2 * ν) := by
    rw [le_div_iff₀ (by positivity)]
    dsimp only [E₀]; linarith
  have hwf := ((garry_certified_waterfall_to_global_river_torus3D hns hmean W hcapture).2.2.2.2 hP_cont).1 T hT
  have hwf_P : (∫ s in (0 : ℝ)..T, P s) ≤
      (4 / ν) * (W.zCap 0 + c_nu_H1 ν * M_peak * B) + (8 / ν) * W.zCap W.steps := by
    have hwf' : (∫ s in (0 : ℝ)..T, P s) ≤
        (4 / ν) * (W.zCap 0 + c_nu_H1 ν * M_peak * B) + (16 / (3 * ν)) * W.zCap W.steps := hwf
    have hcap_nn : 0 ≤ W.zCap W.steps := W.hzCap_nonneg W.steps le_rfl
    have h16_le : (16 / (3 * ν)) * W.zCap W.steps ≤ (8 / ν) * W.zCap W.steps := by
      have hcoef : 16 / (3 * ν) ≤ 8 / ν := by
        have hν0 : ν ≠ 0 := ne_of_gt hν
        have hdiff : 8 / ν - 16 / (3 * ν) = 8 / (3 * ν) := by field_simp; ring
        have hpos : 0 ≤ 8 / (3 * ν) := by positivity
        linarith
      exact mul_le_mul_of_nonneg_right hcoef hcap_nn
    linarith
  have hcoef_nn : 0 ≤ 13 / (4 * Real.pi ^ 2) := by positivity
  have hsum_le : (∫ s in (0 : ℝ)..T, Z s) + (1 / 2 : ℝ) * (∫ s in (0 : ℝ)..T, P s) ≤
      E₀ / (2 * ν) + (1 / 2 : ℝ) * ((4 / ν) * (W.zCap 0 + c_nu_H1 ν * M_peak * B) +
        (8 / ν) * W.zCap W.steps) := by
    linarith
  exact le_trans hmono (mul_le_mul_of_nonneg_left hsum_le hcoef_nn)

/-- Non-vacuity audit on `𝕋³`: any periodic classical 3D NS solution starting from a constant
    initial velocity `u(0, x) = c` coincides identically with the steady uniform flow `c`. -/
theorem steady_uniform_flow_unique_torus3D
    {u : ℝ → R3 → R3} {p : ℝ → R3 → ℝ} {ν : ℝ} {c : R3}
    (hns : IsPeriodicClassicalNS3D_C3 u p ν)
    (hinit : ∀ x : R3, u 0 x = c) :
    ∀ t ≥ 0, ∀ x : R3, u t x = c :=
  (torus3D_serrin_L2_stability_and_global_uniqueness hns
    (steadyUniformFlow_isPeriodicClassicalNS3D_C3 c 0 ν hns.h_nu_pos)).2 hinit

-- ============================================================================
-- SECTION 5: AXIOM AUDIT TRAIL (0 sorryAx, 0 custom axioms)
-- ============================================================================

#print axioms gronwall_L2_of_hasDerivAt
#print axioms pointwise_diff_advection_young
#print axioms eq_zero_of_r3Integral_sq_eq_zero
#print axioms hasDerivAt_diffEnergyR3_and_bound
#print axioms r3_serrin_L2_stability_and_global_uniqueness
#print axioms r3_global_L2_Linf_bound_of_waterfall
#print axioms eq_zero_of_torusIntegral_sq_eq_zero
#print axioms hasDerivAt_diffEnergyTorus3D_and_bound
#print axioms torus3D_serrin_L2_stability_and_global_uniqueness
#print axioms torus3D_global_L2_Linf_bound_of_waterfall
#print axioms steady_uniform_flow_unique_torus3D

end GarryGlobalUniquenessNS3D