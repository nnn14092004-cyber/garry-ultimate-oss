import VorticityEquation3D
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

/-!
# Milestone 10A-1 (Hurdle 1 — Tier I, 100% Unconditional): Whole-Space `ℝ³` Lebesgue Integration,
  Boundary-Free IBP & Exact Solenoidal Identities (`0 sorryAx`)

This module lifts the spatial integral calculus from the compact torus `𝕋³` to the full
unbounded Euclidean space `ℝ³ = Fin 3 → ℝ` (with zero `Torus3D` imports and zero compactness
or Poincaré assumptions):

1. Canonical 3D Lebesgue integral `r3Integral f := ∫ x : R3, f x` and uniform axis-slice Fubini.
2. Clay-standard decay at infinity `VanishesAtInfinityR3 f := Tendsto f (cocompact R3) (𝓝 0)`,
   implying both directional decay along every axis and global boundedness.
3. Exact boundary-free 3D integration by parts `r3Integral_ibp` on `ℝ³`.
4. Five unconditional whole-space `ℝ³` identities for `DecayingH3SolenoidalR3 u`:
   - **Theorem 10A1-1:** Hessian–Laplacian identity `∫_{ℝ³} |D² f|² = ∫_{ℝ³} (Δ f)²`.
   - **Theorem 10A1-2:** Solenoidal enstrophy identity `∫_{ℝ³} |ω|² = ∫_{ℝ³} |∇ u|²`.
   - **Theorem 10A1-3:** Solenoidal palinstrophy identity `∫_{ℝ³} |∇ ω|² = ∫_{ℝ³} |Δ u|²`.
   - **Theorem 10A1-4:** Scale-invariant derivative interpolation (replacing Wirtinger–Poincaré
     on `ℝ³`): `2 Z_{ℝ³} ≤ √(2 E_{ℝ³}) √P_{ℝ³}` and `2 Z_{ℝ³}² ≤ E_{ℝ³} P_{ℝ³}`.
   - **Theorem 10A1-5:** Exact whole-space vortex stretching IBP
     `S_stretch^{ℝ³} = -∫_{ℝ³} ⟨u, (ω · ∇)ω⟩ dx`.
-/

namespace GarryWholeSpaceR3

open MeasureTheory Filter Topology
open GarryReal3DCalculus
open GarryVorticity3D

-- ============================================================================
-- SECTION 0: WHOLE-SPACE DEFINITIONS, DECAY AT INFINITY & INTEGRABILITY TOOLS
-- ============================================================================

/-- Canonical Lebesgue integral on full Euclidean space `ℝ³ = Fin 3 → ℝ`. -/
noncomputable def r3Integral (f : R3 → ℝ) : ℝ :=
  ∫ x : R3, f x

/-- Standard decay at infinity on `ℝ³`: `f(x) → 0` as `|x| → ∞`. -/
def VanishesAtInfinityR3 (f : R3 → ℝ) : Prop :=
  Tendsto f (cocompact R3) (𝓝 0)

/-- Decay along coordinate axis `i` for every transverse fiber `y : Fin 2 → ℝ`. -/
def VanishesAlongAxis (f : R3 → ℝ) (i : Fin 3) : Prop :=
  ∀ y : Fin 2 → ℝ,
    Tendsto (fun t : ℝ => f (i.insertNth t y)) atTop (𝓝 0) ∧
    Tendsto (fun t : ℝ => f (i.insertNth t y)) atBot (𝓝 0)

/-- Pointwise squared Frobenius norm of the spatial gradient `|∇ u(x)|²` on `ℝ³`. -/
noncomputable def gradNormSqR3 (u : R3 → R3) (x : R3) : ℝ :=
  (partialDerivScalar (fun y => u y 0) x 0) ^ 2 +
  (partialDerivScalar (fun y => u y 0) x 1) ^ 2 +
  (partialDerivScalar (fun y => u y 0) x 2) ^ 2 +
  (partialDerivScalar (fun y => u y 1) x 0) ^ 2 +
  (partialDerivScalar (fun y => u y 1) x 1) ^ 2 +
  (partialDerivScalar (fun y => u y 1) x 2) ^ 2 +
  (partialDerivScalar (fun y => u y 2) x 0) ^ 2 +
  (partialDerivScalar (fun y => u y 2) x 1) ^ 2 +
  (partialDerivScalar (fun y => u y 2) x 2) ^ 2

/-- Pointwise squared Frobenius norm of the Hessian `|D² f(x)|²` of a scalar field on `ℝ³`. -/
noncomputable def hessianNormSqR3 (f : R3 → ℝ) (x : R3) : ℝ :=
  (sndPartial f x 0 0) ^ 2 + (sndPartial f x 0 1) ^ 2 + (sndPartial f x 0 2) ^ 2 +
  (sndPartial f x 1 0) ^ 2 + (sndPartial f x 1 1) ^ 2 + (sndPartial f x 1 2) ^ 2 +
  (sndPartial f x 2 0) ^ 2 + (sndPartial f x 2 1) ^ 2 + (sndPartial f x 2 2) ^ 2

/-- Whole-space `ℝ³` kinetic energy `E(u) = ½ ∫_{ℝ³} |u(x)|² dx`. -/
noncomputable def energyR3 (u : R3 → R3) : ℝ :=
  (1 / 2 : ℝ) * r3Integral (fun x => dot3D (u x) (u x))

/-- Whole-space `ℝ³` enstrophy `Z(u) = ½ ∫_{ℝ³} |∇ × u(x)|² dx`. -/
noncomputable def enstrophyR3 (u : R3 → R3) : ℝ :=
  (1 / 2 : ℝ) * r3Integral (fun x => dot3D (curl3D u x) (curl3D u x))

/-- Whole-space `ℝ³` palinstrophy `P(u) = ∫_{ℝ³} |∇(∇ × u)(x)|² dx`. -/
noncomputable def palinstrophyR3 (u : R3 → R3) : ℝ :=
  r3Integral (gradNormSqR3 (curl3D u))

/-- Whole-space `ℝ³` 3D vortex stretching integral `∫_{ℝ³} ⟨(ω · ∇)u, ω⟩ dx`. -/
noncomputable def vortexStretchingR3 (u : R3 → R3) : ℝ :=
  r3Integral (fun x => dot3D (directionalAdvection3D (curl3D u) u x) (curl3D u x))

/-- Regularity, decay, and `H³(ℝ³)` integrability class for scalar fields on `ℝ³`. -/
structure DecayingH3ScalarR3 (f : R3 → ℝ) : Prop where
  h_c3 : ContDiff ℝ 3 f
  h_van0 : VanishesAtInfinityR3 f
  h_van1 : ∀ i : Fin 3, VanishesAtInfinityR3 (fun x => partialDerivScalar f x i)
  h_van2 : ∀ i j : Fin 3, VanishesAtInfinityR3 (fun x => sndPartial f x i j)
  h_int0 : Integrable (fun x => (f x) ^ 2) volume
  h_int1 : ∀ i : Fin 3, Integrable (fun x => (partialDerivScalar f x i) ^ 2) volume
  h_int2 : ∀ i j : Fin 3, Integrable (fun x => (sndPartial f x i j) ^ 2) volume
  h_int3 : ∀ i j k : Fin 3,
    Integrable (fun x => (partialDerivScalar (fun y => sndPartial f y i j) x k) ^ 2) volume

/-- Regularity, decay, incompressibility, and `H³(ℝ³)` class for 3D velocity fields on `ℝ³`. -/
structure DecayingH3SolenoidalR3 (u : R3 → R3) : Prop where
  h_comp : ∀ c : Fin 3, DecayingH3ScalarR3 (fun x => u x c)
  h_div : ∀ x : R3, div3D u x = 0

private lemma int_add {f g : R3 → ℝ} (hf : Integrable f volume) (hg : Integrable g volume) :
    Integrable (fun x => f x + g x) volume := hf.add hg

private lemma int_const_mul (c : ℝ) {f : R3 → ℝ} (hf : Integrable f volume) :
    Integrable (fun x => c * f x) volume := hf.const_mul c

private lemma curl3D_zero (u : R3 → R3) (x : R3) :
    curl3D u x 0 = partialDerivScalar (fun y => u y 2) x 1 -
      partialDerivScalar (fun y => u y 1) x 2 := rfl

private lemma curl3D_one (u : R3 → R3) (x : R3) :
    curl3D u x 1 = partialDerivScalar (fun y => u y 0) x 2 -
      partialDerivScalar (fun y => u y 2) x 0 := rfl

private lemma curl3D_two (u : R3 → R3) (x : R3) :
    curl3D u x 2 = partialDerivScalar (fun y => u y 1) x 0 -
      partialDerivScalar (fun y => u y 0) x 1 := rfl

lemma dot3D_self_nonneg_r3 (v : R3) : 0 ≤ dot3D v v := by
  unfold dot3D
  exact add_nonneg (add_nonneg (mul_self_nonneg _) (mul_self_nonneg _)) (mul_self_nonneg _)

lemma gradNormSqR3_nonneg (u : R3 → R3) (x : R3) : 0 ≤ gradNormSqR3 u x := by
  unfold gradNormSqR3; positivity

lemma r3Integral_zero : r3Integral (fun _ : R3 => (0 : ℝ)) = 0 := by
  unfold r3Integral; simp

lemma r3Integral_congr {f g : R3 → ℝ} (h : ∀ x : R3, f x = g x) :
    r3Integral f = r3Integral g := by
  unfold r3Integral; exact integral_congr_ae (Filter.Eventually.of_forall h)

lemma r3Integral_add {f g : R3 → ℝ} (hf : Integrable f volume) (hg : Integrable g volume) :
    r3Integral (fun x => f x + g x) = r3Integral f + r3Integral g :=
  MeasureTheory.integral_add hf hg

lemma r3Integral_add3 {f g h : R3 → ℝ}
    (hf : Integrable f volume) (hg : Integrable g volume) (hh : Integrable h volume) :
    r3Integral (fun x => f x + g x + h x) = r3Integral f + r3Integral g + r3Integral h := by
  rw [r3Integral_add (int_add hf hg) hh, r3Integral_add hf hg]

lemma r3Integral_sub {f g : R3 → ℝ} (hf : Integrable f volume) (hg : Integrable g volume) :
    r3Integral (fun x => f x - g x) = r3Integral f - r3Integral g :=
  MeasureTheory.integral_sub hf hg

lemma r3Integral_neg (f : R3 → ℝ) :
    r3Integral (fun x => -f x) = -r3Integral f :=
  MeasureTheory.integral_neg f

lemma r3Integral_const_mul (c : ℝ) (f : R3 → ℝ) :
    r3Integral (fun x => c * f x) = c * r3Integral f :=
  MeasureTheory.integral_const_mul c f

lemma r3Integral_nonneg {f : R3 → ℝ} (hf : ∀ x : R3, 0 ≤ f x) :
    0 ≤ r3Integral f :=
  MeasureTheory.integral_nonneg hf

lemma integrable_mul_of_sq {f g : R3 → ℝ}
    (hf_c : Continuous f) (hg_c : Continuous g)
    (hf2 : Integrable (fun x => (f x) ^ 2) volume)
    (hg2 : Integrable (fun x => (g x) ^ 2) volume) :
    Integrable (fun x => f x * g x) volume := by
  have hdom : Integrable (fun x => ((f x) ^ 2 + (g x) ^ 2) / 2) volume :=
    (hf2.add hg2).div_const 2
  refine hdom.mono' (hf_c.mul hg_c).aestronglyMeasurable (Filter.Eventually.of_forall fun x => ?_)
  rw [Real.norm_eq_abs]
  exact abs_le.mpr ⟨by nlinarith [sq_nonneg (f x + g x)], by nlinarith [sq_nonneg (f x - g x)]⟩

lemma integrable_add_sq_of_sq {f g : R3 → ℝ}
    (hf_c : Continuous f) (hg_c : Continuous g)
    (hf2 : Integrable (fun x => (f x) ^ 2) volume)
    (hg2 : Integrable (fun x => (g x) ^ 2) volume) :
    Integrable (fun x => (f x + g x) ^ 2) volume := by
  have heq : (fun x => (f x + g x) ^ 2) = fun x => (f x) ^ 2 + 2 * (f x * g x) + (g x) ^ 2 := by
    funext x; ring
  rw [heq]
  exact (hf2.add ((integrable_mul_of_sq hf_c hg_c hf2 hg2).const_mul 2)).add hg2

lemma integrable_sub_sq_of_sq {f g : R3 → ℝ}
    (hf_c : Continuous f) (hg_c : Continuous g)
    (hf2 : Integrable (fun x => (f x) ^ 2) volume)
    (hg2 : Integrable (fun x => (g x) ^ 2) volume) :
    Integrable (fun x => (f x - g x) ^ 2) volume := by
  have heq : (fun x => (f x - g x) ^ 2) = fun x => (f x) ^ 2 - 2 * (f x * g x) + (g x) ^ 2 := by
    funext x; ring
  rw [heq]
  exact (hf2.sub ((integrable_mul_of_sq hf_c hg_c hf2 hg2).const_mul 2)).add hg2

lemma integrable_bdd_mul_mul_of_sq {h f g : R3 → ℝ}
    (hh_c : Continuous h) (hf_c : Continuous f) (hg_c : Continuous g)
    (hh_bdd : ∃ C : ℝ, 0 ≤ C ∧ ∀ x : R3, |h x| ≤ C)
    (hf2 : Integrable (fun x => (f x) ^ 2) volume)
    (hg2 : Integrable (fun x => (g x) ^ 2) volume) :
    Integrable (fun x => h x * (f x * g x)) volume := by
  obtain ⟨C, hC_nn, hC⟩ := hh_bdd
  have hdom : Integrable (fun x => C * (((f x) ^ 2 + (g x) ^ 2) / 2)) volume :=
    ((hf2.add hg2).div_const 2).const_mul C
  refine hdom.mono' (hh_c.mul (hf_c.mul hg_c)).aestronglyMeasurable
    (Filter.Eventually.of_forall fun x => ?_)
  rw [Real.norm_eq_abs, abs_mul]
  have hfg : |f x * g x| ≤ ((f x) ^ 2 + (g x) ^ 2) / 2 := abs_le.mpr
    ⟨by nlinarith [sq_nonneg (f x + g x)], by nlinarith [sq_nonneg (f x - g x)]⟩
  exact mul_le_mul (hC x) hfg (abs_nonneg _) hC_nn

/-- Whole-space `ℝ³` Cauchy–Schwarz inequality for `r3Integral`. -/
theorem r3_cauchy_schwarz_sq {f g : R3 → ℝ}
    (hf_c : Continuous f) (hg_c : Continuous g)
    (hf2 : Integrable (fun x => (f x) ^ 2) volume)
    (hg2 : Integrable (fun x => (g x) ^ 2) volume) :
    (r3Integral (fun x => f x * g x)) ^ 2 ≤
      r3Integral (fun x => (f x) ^ 2) * r3Integral (fun x => (g x) ^ 2) := by
  set A := r3Integral (fun x => (f x) ^ 2)
  set B := r3Integral (fun x => f x * g x)
  set C := r3Integral (fun x => (g x) ^ 2)
  have hfg : Integrable (fun x => f x * g x) volume := integrable_mul_of_sq hf_c hg_c hf2 hg2
  have hA_nn : 0 ≤ A := r3Integral_nonneg (fun x => sq_nonneg _)
  have hquad : ∀ t : ℝ, 0 ≤ t ^ 2 * A + 2 * t * B + C := by
    intro t
    have hnn : 0 ≤ r3Integral (fun x => (t * f x + g x) ^ 2) :=
      r3Integral_nonneg (fun x => sq_nonneg _)
    have hexp : (fun x => (t * f x + g x) ^ 2) =
        fun x => t ^ 2 * (f x) ^ 2 + (2 * t) * (f x * g x) + (g x) ^ 2 := by
      funext x; ring
    rw [hexp, r3Integral_add3 (hf2.const_mul (t ^ 2)) (hfg.const_mul (2 * t)) hg2,
        r3Integral_const_mul, r3Integral_const_mul] at hnn
    exact hnn
  rcases eq_or_lt_of_le hA_nn with hA0 | hA_pos
  · have hB0 : B = 0 := by
      by_contra hBne
      have hq := hquad (-(C + 1) / (2 * B))
      rw [← hA0] at hq
      have hcalc : (-(C + 1) / (2 * B)) ^ 2 * 0 + 2 * (-(C + 1) / (2 * B)) * B + C = -1 := by
        field_simp; ring
      linarith
    rw [hB0, ← hA0]; norm_num
  · have hq := hquad (-B / A)
    have hA_ne : A ≠ 0 := ne_of_gt hA_pos
    have hmul := mul_nonneg (le_of_lt hA_pos) hq
    have hcalc : A * ((-B / A) ^ 2 * A + 2 * (-B / A) * B + C) = A * C - B ^ 2 := by
      field_simp; ring
    linarith

-- ============================================================================
-- SECTION 1: DECAY AT INFINITY, AXIS-SLICE FUBINI & BOUNDARY-FREE 3D IBP
-- ============================================================================

lemma tendsto_insertNth_atTop_cocompact (i : Fin 3) (y : Fin 2 → ℝ) :
    Tendsto (fun t : ℝ => i.insertNth t y) atTop (cocompact R3) := by
  rw [Filter.hasBasis_cocompact.tendsto_right_iff]
  intro K hK
  obtain ⟨C, hC⟩ := hK.isBounded.subset_closedBall (0 : R3)
  rw [Filter.eventually_atTop]
  refine ⟨C + 1, fun t ht hmem => ?_⟩
  let x : R3 := i.insertNth t y
  have hball : dist x 0 ≤ C := hC hmem
  rw [dist_zero_right] at hball
  have hcoord : ‖x i‖ ≤ ‖x‖ := norm_le_pi_norm x i
  have hxi : x i = t := by simp [x]
  rw [hxi, Real.norm_eq_abs] at hcoord
  have ht_abs : C + 1 ≤ |t| := le_trans ht (le_abs_self t)
  linarith

lemma tendsto_insertNth_atBot_cocompact (i : Fin 3) (y : Fin 2 → ℝ) :
    Tendsto (fun t : ℝ => i.insertNth t y) atBot (cocompact R3) := by
  rw [Filter.hasBasis_cocompact.tendsto_right_iff]
  intro K hK
  obtain ⟨C, hC⟩ := hK.isBounded.subset_closedBall (0 : R3)
  rw [Filter.eventually_atBot]
  refine ⟨-(C + 1), fun t ht hmem => ?_⟩
  let x : R3 := i.insertNth t y
  have hball : dist x 0 ≤ C := hC hmem
  rw [dist_zero_right] at hball
  have hcoord : ‖x i‖ ≤ ‖x‖ := norm_le_pi_norm x i
  have hxi : x i = t := by simp [x]
  rw [hxi, Real.norm_eq_abs] at hcoord
  have ht_abs : C + 1 ≤ |t| := le_trans (by linarith) (neg_le_abs t)
  linarith

lemma vanishesAlongAxis_of_vanishesAtInfinityR3 {f : R3 → ℝ}
    (hf : VanishesAtInfinityR3 f) (i : Fin 3) :
    VanishesAlongAxis f i := fun y =>
  ⟨hf.comp (tendsto_insertNth_atTop_cocompact i y),
   hf.comp (tendsto_insertNth_atBot_cocompact i y)⟩

lemma vanishesAtInfinityR3_mul {f g : R3 → ℝ}
    (hf : VanishesAtInfinityR3 f) (hg : VanishesAtInfinityR3 g) :
    VanishesAtInfinityR3 (fun x => f x * g x) := by
  unfold VanishesAtInfinityR3 at *
  simpa using hf.mul hg

lemma vanishesAtInfinityR3_sub {f g : R3 → ℝ}
    (hf : VanishesAtInfinityR3 f) (hg : VanishesAtInfinityR3 g) :
    VanishesAtInfinityR3 (fun x => f x - g x) := by
  unfold VanishesAtInfinityR3 at *
  simpa using hf.sub hg

lemma exists_bound_of_vanishesAtInfinityR3 {f : R3 → ℝ} (hf : Continuous f)
    (hvan : VanishesAtInfinityR3 f) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : R3, |f x| ≤ C := by
  have hev : ∀ᶠ x in cocompact R3, |f x| ≤ 1 := by
    have h1 : Metric.closedBall (0 : ℝ) 1 ∈ 𝓝 (0 : ℝ) := Metric.closedBall_mem_nhds 0 zero_lt_one
    filter_upwards [hvan h1] with x hx
    simpa [Metric.mem_closedBall, Real.dist_eq] using hx
  rw [Filter.hasBasis_cocompact.eventually_iff] at hev
  obtain ⟨K, hK, hK_out⟩ := hev
  obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn hf.continuousOn
  refine ⟨max 1 M, le_trans zero_le_one (le_max_left 1 M), fun x => ?_⟩
  by_cases hx : x ∈ K
  · exact le_trans (by simpa [Real.norm_eq_abs] using hM x hx) (le_max_right 1 M)
  · exact le_trans (hK_out hx) (le_max_left 1 M)

private lemma insertNth_eq_add_smul (i : Fin 3) (y : Fin 2 → ℝ) (t : ℝ) :
    i.insertNth t y = i.insertNth 0 y + t • basisVec i := by
  funext j
  by_cases hji : j = i
  · subst hji
    simp [basisVec]
  · obtain ⟨k, rfl⟩ := Fin.exists_succAbove_eq hji
    simp [basisVec]

lemma hasDerivAt_comp_insertNth {f : R3 → ℝ} (i : Fin 3) (y : Fin 2 → ℝ) {t : ℝ}
    (hf : DifferentiableAt ℝ f (i.insertNth t y)) :
    HasDerivAt (fun s : ℝ => f (i.insertNth s y))
      (partialDerivScalar f (i.insertNth t y) i) t := by
  have hφ : HasDerivAt (fun s : ℝ => (i.insertNth s y : R3)) (basisVec i) t := by
    have heq : (fun s : ℝ => (i.insertNth s y : R3)) =
        fun s => (i.insertNth 0 y : R3) + s • basisVec i := by
      funext s; exact insertNth_eq_add_smul i y s
    rw [heq]
    have h1 : HasDerivAt (fun s : ℝ => (i.insertNth 0 y : R3) + s • basisVec i)
        ((0 : R3) + (1 : ℝ) • basisVec i) t :=
      (hasDerivAt_const t (i.insertNth 0 y : R3)).add
        ((hasDerivAt_id t).smul_const (basisVec i))
    have hd : (0 : R3) + (1 : ℝ) • basisVec i = basisVec i := by simp
    rwa [hd] at h1
  exact hf.hasFDerivAt.comp_hasDerivAt t hφ

/-- 1D vanishing-derivative integral identity on `ℝ`. -/
lemma integral_deriv_eq_zero_of_tendsto_zero {h h' : ℝ → ℝ}
    (hderiv : ∀ t : ℝ, HasDerivAt h (h' t) t)
    (hint : Integrable h' volume)
    (htop : Tendsto h atTop (𝓝 0))
    (hbot : Tendsto h atBot (𝓝 0)) :
    ∫ t : ℝ, h' t = 0 := by
  have hI : Tendsto (fun R : ℝ => ∫ t in (-R)..R, h' t) atTop (𝓝 (∫ t : ℝ, h' t)) :=
    MeasureTheory.intervalIntegral_tendsto_integral hint tendsto_neg_atTop_atBot tendsto_id
  have hftc : ∀ R : ℝ, ∫ t in (-R)..R, h' t = h R - h (-R) := fun R =>
    intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun t _ => hderiv t) hint.intervalIntegrable
  have hsub : Tendsto (fun R : ℝ => h R - h (-R)) atTop (𝓝 (0 - 0)) :=
    htop.sub (hbot.comp tendsto_neg_atTop_atBot)
  rw [sub_self] at hsub
  have hI' : Tendsto (fun R : ℝ => h R - h (-R)) atTop (𝓝 (∫ t : ℝ, h' t)) := by
    simpa only [hftc] using hI
  exact tendsto_nhds_unique hI' hsub

/-- Uniform 3D-to-1D axis-slice Fubini theorem on `ℝ³` for any coordinate `i : Fin 3`. -/
lemma r3Integral_eq_iterated_slice {f : R3 → ℝ} (hf : Integrable f volume) (i : Fin 3) :
    r3Integral f = ∫ y : Fin 2 → ℝ, ∫ t : ℝ, f (i.insertNth t y) := by
  let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin 3 => ℝ) i
  have hmp : MeasurePreserving e (volume : Measure R3)
      ((volume : Measure ℝ).prod (volume : Measure (Fin 2 → ℝ))) :=
    MeasureTheory.measurePreserving_piFinSuccAbove (fun _ : Fin 3 => (volume : Measure ℝ)) i
  have hcomp : ∫ p : ℝ × (Fin 2 → ℝ), f (e.symm p)
      ∂((volume : Measure ℝ).prod (volume : Measure (Fin 2 → ℝ))) = ∫ x : R3, f x :=
    hmp.symm.integral_comp' f
  have hf_prod : Integrable (fun p : ℝ × (Fin 2 → ℝ) => f (e.symm p))
      ((volume : Measure ℝ).prod (volume : Measure (Fin 2 → ℝ))) :=
    (hmp.symm.integrable_comp_emb e.symm.measurableEmbedding).mpr hf
  unfold r3Integral
  rw [← hcomp, MeasureTheory.integral_prod_symm _ hf_prod]
  rfl

/-- Whole-space `ℝ³` divergence-free total derivative theorem:
    if `f` is `C¹`, vanishes along axis `i`, and `∂_i f ∈ L¹(ℝ³)`, then `∫_{ℝ³} ∂_i f = 0`. -/
theorem r3Integral_partialDeriv_eq_zero {f : R3 → ℝ} {i : Fin 3}
    (hf : Differentiable ℝ f)
    (hvan : VanishesAlongAxis f i)
    (hint : Integrable (fun x => partialDerivScalar f x i) volume) :
    r3Integral (fun x => partialDerivScalar f x i) = 0 := by
  let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin 3 => ℝ) i
  have hmp : MeasurePreserving e (volume : Measure R3)
      ((volume : Measure ℝ).prod (volume : Measure (Fin 2 → ℝ))) :=
    MeasureTheory.measurePreserving_piFinSuccAbove (fun _ : Fin 3 => (volume : Measure ℝ)) i
  have hf_prod : Integrable (fun p : ℝ × (Fin 2 → ℝ) => partialDerivScalar f (e.symm p) i)
      ((volume : Measure ℝ).prod (volume : Measure (Fin 2 → ℝ))) :=
    (hmp.symm.integrable_comp_emb e.symm.measurableEmbedding).mpr hint
  have hslice_int : ∀ᵐ y : Fin 2 → ℝ ∂volume,
      Integrable (fun t : ℝ => partialDerivScalar f (i.insertNth t y) i) volume :=
    hf_prod.prod_left_ae
  rw [r3Integral_eq_iterated_slice hint i]
  have hzero_ae : (fun y : Fin 2 → ℝ => ∫ t : ℝ, partialDerivScalar f (i.insertNth t y) i) =ᵐ[volume]
      fun _ => (0 : ℝ) := by
    filter_upwards [hslice_int] with y hy
    exact integral_deriv_eq_zero_of_tendsto_zero
      (fun t => hasDerivAt_comp_insertNth i y (hf (i.insertNth t y)))
      hy (hvan y).1 (hvan y).2
  rw [integral_congr_ae hzero_ae]
  simp

/-- **Exact Boundary-Free 3D Integration by Parts on `ℝ³`:**
    `∫_{ℝ³} f ∂_i g dx = -∫_{ℝ³} (∂_i f) g dx`. -/
theorem r3Integral_ibp {f g : R3 → ℝ} {i : Fin 3}
    (hf : Differentiable ℝ f) (hg : Differentiable ℝ g)
    (hvan : VanishesAlongAxis (fun x => f x * g x) i)
    (h1 : Integrable (fun x => partialDerivScalar f x i * g x) volume)
    (h2 : Integrable (fun x => f x * partialDerivScalar g x i) volume) :
    r3Integral (fun x => f x * partialDerivScalar g x i) =
      -r3Integral (fun x => partialDerivScalar f x i * g x) := by
  have hprod_eq : (fun x => partialDerivScalar (fun y => f y * g y) x i) =
      fun x => partialDerivScalar f x i * g x + f x * partialDerivScalar g x i := by
    funext x
    rw [partialDerivScalar_mul (hf x) (hg x) i]
    ring
  have hint_prod : Integrable (fun x => partialDerivScalar (fun y => f y * g y) x i) volume := by
    rw [hprod_eq]; exact h1.add h2
  have hdiff_fg : Differentiable ℝ (fun y => f y * g y) := hf.mul hg
  have hzero := r3Integral_partialDeriv_eq_zero hdiff_fg hvan hint_prod
  rw [hprod_eq, r3Integral_add h1 h2] at hzero
  linarith

-- ============================================================================
-- SECTION 2: REGULARITY HELPERS FOR PARTIAL & SECOND DERIVATIVES
-- ============================================================================

private lemma contDiff_one_of_three {f : R3 → ℝ} (h : ContDiff ℝ 3 f) : ContDiff ℝ 1 f :=
  h.of_le (by exact_mod_cast (show (1 : ℕ) ≤ 3 by decide))

private lemma contDiff_two_of_three {f : R3 → ℝ} (h : ContDiff ℝ 3 f) : ContDiff ℝ 2 f :=
  h.of_le (by exact_mod_cast (show (2 : ℕ) ≤ 3 by decide))

private lemma contDiff_partialDerivScalar_of_succ {f : R3 → ℝ} {n : ℕ}
    (hf : ContDiff ℝ (n + 1 : ℕ) f) (i : Fin 3) :
    ContDiff ℝ n (fun x => partialDerivScalar f x i) := by
  unfold partialDerivScalar
  have hfd : ContDiff ℝ n (fderiv ℝ f) := hf.fderiv_right (by norm_cast)
  exact hfd.clm_apply contDiff_const

private lemma contDiff_two_partialDerivScalar_of_three {f : R3 → ℝ} (hf : ContDiff ℝ 3 f) (i : Fin 3) :
    ContDiff ℝ 2 (fun x => partialDerivScalar f x i) :=
  contDiff_partialDerivScalar_of_succ (n := 2) hf i

private lemma contDiff_one_partialDerivScalar_of_two {f : R3 → ℝ} (hf : ContDiff ℝ 2 f) (i : Fin 3) :
    ContDiff ℝ 1 (fun x => partialDerivScalar f x i) :=
  contDiff_partialDerivScalar_of_succ (n := 1) hf i

private lemma partial_partial_eq_snd {f : R3 → ℝ} (hf : ContDiff ℝ 2 f) (x : R3) (i j : Fin 3) :
    partialDerivScalar (fun y => partialDerivScalar f y i) x j = sndPartial f x i j :=
  (partial_partial_eq_sndPartial f x hf.contDiffAt j i).trans
    (sndPartial_symm_of_contDiffAt f x hf.contDiffAt j i)

private lemma contDiff_one_sndPartial_of_three {f : R3 → ℝ} (hf : ContDiff ℝ 3 f) (i j : Fin 3) :
    ContDiff ℝ 1 (fun x => sndPartial f x i j) := by
  have h1 : ContDiff ℝ 1 (fun x => partialDerivScalar (fun y => partialDerivScalar f y i) x j) :=
    contDiff_one_partialDerivScalar_of_two (contDiff_two_partialDerivScalar_of_three hf i) j
  have heq : (fun x => sndPartial f x i j) =
      fun x => partialDerivScalar (fun y => partialDerivScalar f y i) x j := by
    funext x
    exact (partial_partial_eq_snd (contDiff_two_of_three hf) x i j).symm
  rwa [heq]

private lemma snd_symm {f : R3 → ℝ} (hf : ContDiff ℝ 2 f) (x : R3) (i j : Fin 3) :
    sndPartial f x i j = sndPartial f x j i :=
  sndPartial_symm_of_contDiffAt f x hf.contDiffAt i j

private lemma partial_snd_comm {f : R3 → ℝ} (hf : ContDiff ℝ 3 f) (x : R3) (i j : Fin 3) :
    partialDerivScalar (fun y => sndPartial f y i j) x i =
      partialDerivScalar (fun y => sndPartial f y i i) x j := by
  have hg2 : ContDiff ℝ 2 (fun y => partialDerivScalar f y i) :=
    contDiff_two_partialDerivScalar_of_three hf i
  have h1 : (fun y => sndPartial f y i j) =
      fun y => partialDerivScalar (fun z => partialDerivScalar f z i) y j := by
    funext y; exact (partial_partial_eq_snd (contDiff_two_of_three hf) y i j).symm
  have h2 : (fun y => sndPartial f y i i) =
      fun y => partialDerivScalar (fun z => partialDerivScalar f z i) y i := by
    funext y; exact (partial_partial_eq_snd (contDiff_two_of_three hf) y i i).symm
  rw [h1, h2, partial_partial_eq_snd hg2 x j i, partial_partial_eq_snd hg2 x i j]
  exact snd_symm hg2 x j i

-- ============================================================================
-- SECTION 3: FIVE UNCONDITIONAL WHOLE-SPACE ℝ³ IDENTITIES
-- ============================================================================

/-- **THEOREM 10A1-1 (Whole-Space `ℝ³` Hessian–Laplacian Identity):**
    For any scalar field `f` in `DecayingH3ScalarR3`,
    `∫_{ℝ³} |D² f(x)|² dx = ∫_{ℝ³} (Δ f(x))² dx`. -/
theorem r3_hessian_eq_laplacian_sq {f : R3 → ℝ} (hf : DecayingH3ScalarR3 f) :
    r3Integral (hessianNormSqR3 f) = r3Integral (fun x => (laplacianScalar f x) ^ 2) := by
  have hpair : ∀ i j : Fin 3,
      r3Integral (fun x => (sndPartial f x i j) ^ 2) =
        r3Integral (fun x => sndPartial f x i i * sndPartial f x j j) := by
    intro i j
    have hd_dj : Differentiable ℝ (fun x => partialDerivScalar f x j) :=
      (contDiff_one_partialDerivScalar_of_two (contDiff_two_of_three hf.h_c3) j).differentiable (by simp)
    have hd_ij : Differentiable ℝ (fun x => sndPartial f x i j) :=
      (contDiff_one_sndPartial_of_three hf.h_c3 i j).differentiable (by simp)
    have hd_ii : Differentiable ℝ (fun x => sndPartial f x i i) :=
      (contDiff_one_sndPartial_of_three hf.h_c3 i i).differentiable (by simp)
    have hc_dj : Continuous (fun x => partialDerivScalar f x j) := hd_dj.continuous
    have hc_ij : Continuous (fun x => sndPartial f x i j) := hd_ij.continuous
    have hc_ii : Continuous (fun x => sndPartial f x i i) := hd_ii.continuous
    have hc_dij : Continuous (fun x => partialDerivScalar (fun y => sndPartial f y i j) x i) := by
      have h2 := contDiff_one_sndPartial_of_three hf.h_c3 i j
      exact (contDiff_partialDerivScalar_of_succ (n := 0) h2 i).continuous
    have hc_dii : Continuous (fun x => partialDerivScalar (fun y => sndPartial f y i i) x j) := by
      have h2 := contDiff_one_sndPartial_of_three hf.h_c3 i i
      exact (contDiff_partialDerivScalar_of_succ (n := 0) h2 j).continuous
    have hibp1 := r3Integral_ibp hd_ij hd_dj
      (vanishesAlongAxis_of_vanishesAtInfinityR3
        (vanishesAtInfinityR3_mul (hf.h_van2 i j) (hf.h_van1 j)) i)
      (integrable_mul_of_sq hc_dij hc_dj (hf.h_int3 i j i) (hf.h_int1 j))
      (by
        have heq : (fun x => sndPartial f x i j *
            partialDerivScalar (fun y => partialDerivScalar f y j) x i) =
            fun x => (sndPartial f x i j) ^ 2 := by
          funext x
          rw [partial_partial_eq_snd (contDiff_two_of_three hf.h_c3) x j i,
              snd_symm (contDiff_two_of_three hf.h_c3) x j i]
          ring
        rw [heq]; exact hf.h_int2 i j)
    have hibp2 := r3Integral_ibp hd_ii hd_dj
      (vanishesAlongAxis_of_vanishesAtInfinityR3
        (vanishesAtInfinityR3_mul (hf.h_van2 i i) (hf.h_van1 j)) j)
      (integrable_mul_of_sq hc_dii hc_dj (hf.h_int3 i i j) (hf.h_int1 j))
      (by
        have heq : (fun x => sndPartial f x i i *
            partialDerivScalar (fun y => partialDerivScalar f y j) x j) =
            fun x => sndPartial f x i i * sndPartial f x j j := by
          funext x
          rw [partial_partial_eq_snd (contDiff_two_of_three hf.h_c3) x j j]
        rw [heq]
        exact integrable_mul_of_sq hc_ii
          (contDiff_one_sndPartial_of_three hf.h_c3 j j).continuous (hf.h_int2 i i) (hf.h_int2 j j))
    have hL : r3Integral (fun x => (sndPartial f x i j) ^ 2) =
        -r3Integral (fun x => partialDerivScalar (fun y => sndPartial f y i j) x i *
          partialDerivScalar f x j) := by
      have heq : (fun x => (sndPartial f x i j) ^ 2) =
          fun x => sndPartial f x i j *
            partialDerivScalar (fun y => partialDerivScalar f y j) x i := by
        funext x
        rw [partial_partial_eq_snd (contDiff_two_of_three hf.h_c3) x j i,
            snd_symm (contDiff_two_of_three hf.h_c3) x j i]
        ring
      rw [heq]; exact hibp1
    have hR : r3Integral (fun x => sndPartial f x i i * sndPartial f x j j) =
        -r3Integral (fun x => partialDerivScalar (fun y => sndPartial f y i i) x j *
          partialDerivScalar f x j) := by
      have heq : (fun x => sndPartial f x i i * sndPartial f x j j) =
          fun x => sndPartial f x i i *
            partialDerivScalar (fun y => partialDerivScalar f y j) x j := by
        funext x
        rw [partial_partial_eq_snd (contDiff_two_of_three hf.h_c3) x j j]
      rw [heq]; exact hibp2
    rw [hL, hR]
    congr 1
    apply r3Integral_congr
    intro x
    rw [partial_snd_comm hf.h_c3 x i j]
  have hint_prod : ∀ i j : Fin 3,
      Integrable (fun x => sndPartial f x i i * sndPartial f x j j) volume := fun i j =>
    integrable_mul_of_sq
      (contDiff_one_sndPartial_of_three hf.h_c3 i i).continuous
      (contDiff_one_sndPartial_of_three hf.h_c3 j j).continuous
      (hf.h_int2 i i) (hf.h_int2 j j)
  have hlhs_exp : r3Integral (hessianNormSqR3 f) =
      (r3Integral (fun x => (sndPartial f x 0 0) ^ 2) +
       r3Integral (fun x => (sndPartial f x 0 1) ^ 2) +
       r3Integral (fun x => (sndPartial f x 0 2) ^ 2)) +
      (r3Integral (fun x => (sndPartial f x 1 0) ^ 2) +
       r3Integral (fun x => (sndPartial f x 1 1) ^ 2) +
       r3Integral (fun x => (sndPartial f x 1 2) ^ 2)) +
      (r3Integral (fun x => (sndPartial f x 2 0) ^ 2) +
       r3Integral (fun x => (sndPartial f x 2 1) ^ 2) +
       r3Integral (fun x => (sndPartial f x 2 2) ^ 2)) := by
    have hpt : ∀ x : R3, hessianNormSqR3 f x =
        ((sndPartial f x 0 0) ^ 2 + (sndPartial f x 0 1) ^ 2 + (sndPartial f x 0 2) ^ 2) +
        ((sndPartial f x 1 0) ^ 2 + (sndPartial f x 1 1) ^ 2 + (sndPartial f x 1 2) ^ 2) +
        ((sndPartial f x 2 0) ^ 2 + (sndPartial f x 2 1) ^ 2 + (sndPartial f x 2 2) ^ 2) := by
      intro x; unfold hessianNormSqR3; ring
    rw [r3Integral_congr hpt,
        r3Integral_add3
          (int_add (int_add (hf.h_int2 0 0) (hf.h_int2 0 1)) (hf.h_int2 0 2))
          (int_add (int_add (hf.h_int2 1 0) (hf.h_int2 1 1)) (hf.h_int2 1 2))
          (int_add (int_add (hf.h_int2 2 0) (hf.h_int2 2 1)) (hf.h_int2 2 2)),
        r3Integral_add3 (hf.h_int2 0 0) (hf.h_int2 0 1) (hf.h_int2 0 2),
        r3Integral_add3 (hf.h_int2 1 0) (hf.h_int2 1 1) (hf.h_int2 1 2),
        r3Integral_add3 (hf.h_int2 2 0) (hf.h_int2 2 1) (hf.h_int2 2 2)]
  have hrhs_exp : r3Integral (fun x => (laplacianScalar f x) ^ 2) =
      (r3Integral (fun x => sndPartial f x 0 0 * sndPartial f x 0 0) +
       r3Integral (fun x => sndPartial f x 0 0 * sndPartial f x 1 1) +
       r3Integral (fun x => sndPartial f x 0 0 * sndPartial f x 2 2)) +
      (r3Integral (fun x => sndPartial f x 1 1 * sndPartial f x 0 0) +
       r3Integral (fun x => sndPartial f x 1 1 * sndPartial f x 1 1) +
       r3Integral (fun x => sndPartial f x 1 1 * sndPartial f x 2 2)) +
      (r3Integral (fun x => sndPartial f x 2 2 * sndPartial f x 0 0) +
       r3Integral (fun x => sndPartial f x 2 2 * sndPartial f x 1 1) +
       r3Integral (fun x => sndPartial f x 2 2 * sndPartial f x 2 2)) := by
    have hpt : ∀ x : R3, (laplacianScalar f x) ^ 2 =
        (sndPartial f x 0 0 * sndPartial f x 0 0 +
         sndPartial f x 0 0 * sndPartial f x 1 1 +
         sndPartial f x 0 0 * sndPartial f x 2 2) +
        (sndPartial f x 1 1 * sndPartial f x 0 0 +
         sndPartial f x 1 1 * sndPartial f x 1 1 +
         sndPartial f x 1 1 * sndPartial f x 2 2) +
        (sndPartial f x 2 2 * sndPartial f x 0 0 +
         sndPartial f x 2 2 * sndPartial f x 1 1 +
         sndPartial f x 2 2 * sndPartial f x 2 2) := by
      intro x; unfold laplacianScalar; ring
    rw [r3Integral_congr hpt,
        r3Integral_add3
          (int_add (int_add (hint_prod 0 0) (hint_prod 0 1)) (hint_prod 0 2))
          (int_add (int_add (hint_prod 1 0) (hint_prod 1 1)) (hint_prod 1 2))
          (int_add (int_add (hint_prod 2 0) (hint_prod 2 1)) (hint_prod 2 2)),
        r3Integral_add3 (hint_prod 0 0) (hint_prod 0 1) (hint_prod 0 2),
        r3Integral_add3 (hint_prod 1 0) (hint_prod 1 1) (hint_prod 1 2),
        r3Integral_add3 (hint_prod 2 0) (hint_prod 2 1) (hint_prod 2 2)]
  rw [hlhs_exp, hrhs_exp,
      hpair 0 0, hpair 0 1, hpair 0 2,
      hpair 1 0, hpair 1 1, hpair 1 2,
      hpair 2 0, hpair 2 1, hpair 2 2]

/-- Core cross-derivative cancellation on `ℝ³` for solenoidal identity:
    `∫_{ℝ³} (∂_i u_i ∂_j u_j - ∂_i u_j ∂_j u_i) dx = 0`. -/
private lemma r3_cross_grad_cancel {f g : R3 → ℝ}
    (hf_c2 : ContDiff ℝ 2 f) (hg_c2 : ContDiff ℝ 2 g)
    (hf_van : VanishesAtInfinityR3 f)
    (hg_van1 : ∀ k : Fin 3, VanishesAtInfinityR3 (fun x => partialDerivScalar g x k))
    (hf_int0 : Integrable (fun x => (f x) ^ 2) volume)
    (hf_int1 : ∀ k : Fin 3, Integrable (fun x => (partialDerivScalar f x k) ^ 2) volume)
    (hg_int1 : ∀ k : Fin 3, Integrable (fun x => (partialDerivScalar g x k) ^ 2) volume)
    (hg_int2 : ∀ k l : Fin 3, Integrable (fun x => (sndPartial g x k l) ^ 2) volume)
    (i j : Fin 3) :
    r3Integral (fun x => partialDerivScalar f x i * partialDerivScalar g x j -
        partialDerivScalar f x j * partialDerivScalar g x i) = 0 := by
  have hd_f : Differentiable ℝ f := hf_c2.differentiable (by simp)
  have hd_gj : Differentiable ℝ (fun x => partialDerivScalar g x j) :=
    (contDiff_one_partialDerivScalar_of_two hg_c2 j).differentiable (by simp)
  have hd_gi : Differentiable ℝ (fun x => partialDerivScalar g x i) :=
    (contDiff_one_partialDerivScalar_of_two hg_c2 i).differentiable (by simp)
  have hc_f : Continuous f := hd_f.continuous
  have hc_fi : Continuous (fun x => partialDerivScalar f x i) :=
    (contDiff_one_partialDerivScalar_of_two hf_c2 i).continuous
  have hc_fj : Continuous (fun x => partialDerivScalar f x j) :=
    (contDiff_one_partialDerivScalar_of_two hf_c2 j).continuous
  have hc_gi : Continuous (fun x => partialDerivScalar g x i) := hd_gi.continuous
  have hc_gj : Continuous (fun x => partialDerivScalar g x j) := hd_gj.continuous
  have h1_int : Integrable (fun x => partialDerivScalar f x i * partialDerivScalar g x j) volume :=
    integrable_mul_of_sq hc_fi hc_gj (hf_int1 i) (hg_int1 j)
  have h2_int : Integrable (fun x => partialDerivScalar f x j * partialDerivScalar g x i) volume :=
    integrable_mul_of_sq hc_fj hc_gi (hf_int1 j) (hg_int1 i)
  have hc_d2ji : Continuous (fun x => partialDerivScalar (fun y => partialDerivScalar g y j) x i) :=
    (contDiff_partialDerivScalar_of_succ (n := 0) (contDiff_one_partialDerivScalar_of_two hg_c2 j) i).continuous
  have hc_d2ij : Continuous (fun x => partialDerivScalar (fun y => partialDerivScalar g y i) x j) :=
    (contDiff_partialDerivScalar_of_succ (n := 0) (contDiff_one_partialDerivScalar_of_two hg_c2 i) j).continuous
  have h_d2ji_sq : Integrable (fun x =>
      (partialDerivScalar (fun y => partialDerivScalar g y j) x i) ^ 2) volume := by
    have heq : (fun x => (partialDerivScalar (fun y => partialDerivScalar g y j) x i) ^ 2) =
        fun x => (sndPartial g x j i) ^ 2 := by
      funext x; rw [partial_partial_eq_snd hg_c2 x j i]
    rw [heq]; exact hg_int2 j i
  have h_d2ij_sq : Integrable (fun x =>
      (partialDerivScalar (fun y => partialDerivScalar g y i) x j) ^ 2) volume := by
    have heq : (fun x => (partialDerivScalar (fun y => partialDerivScalar g y i) x j) ^ 2) =
        fun x => (sndPartial g x i j) ^ 2 := by
      funext x; rw [partial_partial_eq_snd hg_c2 x i j]
    rw [heq]; exact hg_int2 i j
  have hibp1 := r3Integral_ibp hd_f hd_gj
    (vanishesAlongAxis_of_vanishesAtInfinityR3 (vanishesAtInfinityR3_mul hf_van (hg_van1 j)) i)
    h1_int (integrable_mul_of_sq hc_f hc_d2ji hf_int0 h_d2ji_sq)
  have hibp2 := r3Integral_ibp hd_f hd_gi
    (vanishesAlongAxis_of_vanishesAtInfinityR3 (vanishesAtInfinityR3_mul hf_van (hg_van1 i)) j)
    h2_int (integrable_mul_of_sq hc_f hc_d2ij hf_int0 h_d2ij_sq)
  rw [r3Integral_sub h1_int h2_int]
  have hsame : r3Integral (fun x => f x * partialDerivScalar (fun y => partialDerivScalar g y j) x i) =
      r3Integral (fun x => f x * partialDerivScalar (fun y => partialDerivScalar g y i) x j) := by
    apply r3Integral_congr
    intro x
    rw [partial_partial_eq_snd hg_c2 x j i, partial_partial_eq_snd hg_c2 x i j,
        snd_symm hg_c2 x j i]
  linarith

/-- **THEOREM 10A1-2 (Whole-Space `ℝ³` Solenoidal Enstrophy Identity):**
    For any `C²` decaying solenoidal velocity field `u` on `ℝ³` with `∇u, D²u ∈ L²(ℝ³)`,
    `∫_{ℝ³} |∇ × u(x)|² dx = ∫_{ℝ³} |∇ u(x)|² dx` (hence `2 Z_{ℝ³}(u) = ∫_{ℝ³} |∇ u|²`). -/
theorem r3_enstrophy_eq_gradNormSq_of_c2 {u : R3 → R3}
    (hu_c2 : ∀ c : Fin 3, ContDiff ℝ 2 (fun x => u x c))
    (hdiv : ∀ x : R3, div3D u x = 0)
    (hvan0 : ∀ c : Fin 3, VanishesAtInfinityR3 (fun x => u x c))
    (hvan1 : ∀ c i : Fin 3, VanishesAtInfinityR3 (fun x => partialDerivScalar (fun y => u y c) x i))
    (hint0 : ∀ c : Fin 3, Integrable (fun x => (u x c) ^ 2) volume)
    (hint1 : ∀ c i : Fin 3, Integrable (fun x => (partialDerivScalar (fun y => u y c) x i) ^ 2) volume)
    (hint2 : ∀ c i j : Fin 3, Integrable (fun x => (sndPartial (fun y => u y c) x i j) ^ 2) volume) :
    r3Integral (fun x => dot3D (curl3D u x) (curl3D u x)) = r3Integral (gradNormSqR3 u) := by
  let D : Fin 3 → Fin 3 → R3 → ℝ := fun c i x => partialDerivScalar (fun y => u y c) x i
  have hcD : ∀ c i : Fin 3, Continuous (D c i) := fun c i =>
    (contDiff_one_partialDerivScalar_of_two (hu_c2 c) i).continuous
  have hpt : ∀ x : R3,
      dot3D (curl3D u x) (curl3D u x) =
        gradNormSqR3 u x +
        2 * (D 0 0 x * D 1 1 x - D 0 1 x * D 1 0 x) +
        2 * (D 0 0 x * D 2 2 x - D 0 2 x * D 2 0 x) +
        2 * (D 1 1 x * D 2 2 x - D 1 2 x * D 2 1 x) := by
    intro x
    have hdiv0 := hdiv x
    unfold div3D at hdiv0
    unfold dot3D gradNormSqR3
    rw [curl3D_zero, curl3D_one, curl3D_two]
    dsimp only [D]
    linear_combination -((partialDerivScalar (fun y => u y 0) x 0 +
      partialDerivScalar (fun y => u y 1) x 1 +
      partialDerivScalar (fun y => u y 2) x 2) * hdiv0)
  have hint_g : Integrable (gradNormSqR3 u) volume := by
    unfold gradNormSqR3
    exact ((((((((hint1 0 0).add (hint1 0 1)).add (hint1 0 2)).add
      (hint1 1 0)).add (hint1 1 1)).add (hint1 1 2)).add
      (hint1 2 0)).add (hint1 2 1)).add (hint1 2 2)
  have hint_cross : ∀ i j : Fin 3,
      Integrable (fun x => D i i x * D j j x - D i j x * D j i x) volume := fun i j =>
    (integrable_mul_of_sq (hcD i i) (hcD j j) (hint1 i i) (hint1 j j)).sub
      (integrable_mul_of_sq (hcD i j) (hcD j i) (hint1 i j) (hint1 j i))
  have hc01 := r3_cross_grad_cancel (hu_c2 0) (hu_c2 1) (hvan0 0) (hvan1 1)
    (hint0 0) (hint1 0) (hint1 1) (hint2 1) 0 1
  have hc02 := r3_cross_grad_cancel (hu_c2 0) (hu_c2 2) (hvan0 0) (hvan1 2)
    (hint0 0) (hint1 0) (hint1 2) (hint2 2) 0 2
  have hc12 := r3_cross_grad_cancel (hu_c2 1) (hu_c2 2) (hvan0 1) (hvan1 2)
    (hint0 1) (hint1 1) (hint1 2) (hint2 2) 1 2
  rw [r3Integral_congr hpt,
      r3Integral_add
        (int_add (int_add hint_g (int_const_mul 2 (hint_cross 0 1)))
          (int_const_mul 2 (hint_cross 0 2)))
        (int_const_mul 2 (hint_cross 1 2)),
      r3Integral_add (int_add hint_g (int_const_mul 2 (hint_cross 0 1)))
        (int_const_mul 2 (hint_cross 0 2)),
      r3Integral_add hint_g (int_const_mul 2 (hint_cross 0 1)),
      r3Integral_const_mul, r3Integral_const_mul, r3Integral_const_mul]
  dsimp only [D] at hc01 hc02 hc12 ⊢
  rw [hc01, hc02, hc12]
  ring

theorem r3_enstrophy_eq_half_gradNormSq {u : R3 → R3} (hu : DecayingH3SolenoidalR3 u) :
    r3Integral (fun x => dot3D (curl3D u x) (curl3D u x)) = r3Integral (gradNormSqR3 u) :=
  r3_enstrophy_eq_gradNormSq_of_c2
    (fun c => contDiff_two_of_three (hu.h_comp c).h_c3) hu.h_div
    (fun c => (hu.h_comp c).h_van0) (fun c i => (hu.h_comp c).h_van1 i)
    (fun c => (hu.h_comp c).h_int0) (fun c i => (hu.h_comp c).h_int1 i)
    (fun c i j => (hu.h_comp c).h_int2 i j)

private lemma curl3D_curl3D_eq_neg_laplacian {u : R3 → R3}
    (hu_c2 : ∀ c : Fin 3, ContDiff ℝ 2 (fun x => u x c))
    (hdiv : ∀ x : R3, div3D u x = 0) (x : R3) (c : Fin 3) :
    curl3D (curl3D u) x c = -laplacian3D u x c := by
  have hdiv_zero : ∀ y : R3, div3D u y = 0 := hdiv
  have hdiv_d : ∀ i : Fin 3, partialDerivScalar (div3D u) x i = 0 := fun i => by
    have heq : div3D u = fun _ => (0 : ℝ) := funext hdiv_zero
    rw [heq]; exact partialDerivScalar_const 0 x i
  have hdiv_exp : ∀ i : Fin 3,
      sndPartial (fun y => u y 0) x 0 i +
      sndPartial (fun y => u y 1) x 1 i +
      sndPartial (fun y => u y 2) x 2 i = 0 := fun i => by
    have h0 := hdiv_d i
    have hd0 : DifferentiableAt ℝ (fun y => partialDerivScalar (fun z => u z 0) y 0) x :=
      ((contDiff_one_partialDerivScalar_of_two (hu_c2 0) 0).differentiable (by simp)) x
    have hd1 : DifferentiableAt ℝ (fun y => partialDerivScalar (fun z => u z 1) y 1) x :=
      ((contDiff_one_partialDerivScalar_of_two (hu_c2 1) 1).differentiable (by simp)) x
    have hd2 : DifferentiableAt ℝ (fun y => partialDerivScalar (fun z => u z 2) y 2) x :=
      ((contDiff_one_partialDerivScalar_of_two (hu_c2 2) 2).differentiable (by simp)) x
    have hadd := partialDerivScalar_add3 hd0 hd1 hd2 i
    unfold div3D at h0
    rw [hadd,
        partial_partial_eq_snd (hu_c2 0) x 0 i,
        partial_partial_eq_snd (hu_c2 1) x 1 i,
        partial_partial_eq_snd (hu_c2 2) x 2 i] at h0
    exact h0
  have hd_p : ∀ a b : Fin 3,
      DifferentiableAt ℝ (fun y => partialDerivScalar (fun z => u z a) y b) x := fun a b =>
    ((contDiff_one_partialDerivScalar_of_two (hu_c2 a) b).differentiable (by simp)) x
  have hsub_d : ∀ a b a' b' i : Fin 3,
      partialDerivScalar (fun y => partialDerivScalar (fun z => u z a) y b -
        partialDerivScalar (fun z => u z a') y b') x i =
        sndPartial (fun z => u z a) x b i - sndPartial (fun z => u z a') x b' i := fun a b a' b' i => by
    rw [partialDerivScalar_sub (hd_p a b) (hd_p a' b') i,
        partial_partial_eq_snd (hu_c2 a) x b i,
        partial_partial_eq_snd (hu_c2 a') x b' i]
  have hc0 : (fun y => curl3D u y 0) = fun y =>
      partialDerivScalar (fun z => u z 2) y 1 - partialDerivScalar (fun z => u z 1) y 2 := by
    funext y; exact curl3D_zero u y
  have hc1 : (fun y => curl3D u y 1) = fun y =>
      partialDerivScalar (fun z => u z 0) y 2 - partialDerivScalar (fun z => u z 2) y 0 := by
    funext y; exact curl3D_one u y
  have hc2 : (fun y => curl3D u y 2) = fun y =>
      partialDerivScalar (fun z => u z 1) y 0 - partialDerivScalar (fun z => u z 0) y 1 := by
    funext y; exact curl3D_two u y
  fin_cases c
  · change curl3D (curl3D u) x 0 = -laplacian3D u x 0
    rw [curl3D_zero, hc2, hc1, hsub_d 1 0 0 1 1, hsub_d 0 2 2 0 2,
        snd_symm (hu_c2 1) x 0 1, snd_symm (hu_c2 2) x 0 2]
    unfold laplacian3D laplacianScalar
    linarith [hdiv_exp 0]
  · change curl3D (curl3D u) x 1 = -laplacian3D u x 1
    rw [curl3D_one, hc0, hc2, hsub_d 2 1 1 2 2, hsub_d 1 0 0 1 0,
        snd_symm (hu_c2 2) x 1 2, snd_symm (hu_c2 0) x 1 0]
    unfold laplacian3D laplacianScalar
    linarith [hdiv_exp 1]
  · change curl3D (curl3D u) x 2 = -laplacian3D u x 2
    rw [curl3D_two, hc1, hc0, hsub_d 0 2 2 0 0, hsub_d 2 1 1 2 1,
        snd_symm (hu_c2 0) x 2 0, snd_symm (hu_c2 1) x 2 1]
    unfold laplacian3D laplacianScalar
    linarith [hdiv_exp 2]

/-- **THEOREM 10A1-3 (Whole-Space `ℝ³` Solenoidal Palinstrophy Identity):**
    For any `u` in `DecayingH3SolenoidalR3`,
    `palinstrophyR3 u = ∫_{ℝ³} |∇(∇ × u)|² dx = ∫_{ℝ³} |Δ u|² dx`. -/
theorem r3_palinstrophy_eq_laplacianNormSq {u : R3 → R3} (hu : DecayingH3SolenoidalR3 u) :
    palinstrophyR3 u = r3Integral (fun x => dot3D (laplacian3D u x) (laplacian3D u x)) := by
  have hu_c2 : ∀ c : Fin 3, ContDiff ℝ 2 (fun x => u x c) := fun c =>
    contDiff_two_of_three (hu.h_comp c).h_c3
  have hw_c2 : ∀ c : Fin 3, ContDiff ℝ 2 (fun x => curl3D u x c) := fun c => by
    fin_cases c <;> simp only [curl3D, Fin.isValue]
    · exact (contDiff_two_partialDerivScalar_of_three (hu.h_comp 2).h_c3 1).sub
        (contDiff_two_partialDerivScalar_of_three (hu.h_comp 1).h_c3 2)
    · exact (contDiff_two_partialDerivScalar_of_three (hu.h_comp 0).h_c3 2).sub
        (contDiff_two_partialDerivScalar_of_three (hu.h_comp 2).h_c3 0)
    · exact (contDiff_two_partialDerivScalar_of_three (hu.h_comp 1).h_c3 0).sub
        (contDiff_two_partialDerivScalar_of_three (hu.h_comp 0).h_c3 1)
  have hw_div : ∀ x : R3, div3D (curl3D u) x = 0 := fun x =>
    div3D_curl3D_eq_zero u x (contDiff_pi.mpr hu_c2).contDiffAt
  have hw_van0 : ∀ c : Fin 3, VanishesAtInfinityR3 (fun x => curl3D u x c) := fun c => by
    fin_cases c <;> simp only [curl3D, Fin.isValue]
    · exact vanishesAtInfinityR3_sub ((hu.h_comp 2).h_van1 1) ((hu.h_comp 1).h_van1 2)
    · exact vanishesAtInfinityR3_sub ((hu.h_comp 0).h_van1 2) ((hu.h_comp 2).h_van1 0)
    · exact vanishesAtInfinityR3_sub ((hu.h_comp 1).h_van1 0) ((hu.h_comp 0).h_van1 1)
  have hw_p1 : ∀ c i : Fin 3,
      (fun x => partialDerivScalar (fun y => curl3D u y c) x i) =
        match c with
        | 0 => fun x => sndPartial (fun y => u y 2) x 1 i - sndPartial (fun y => u y 1) x 2 i
        | 1 => fun x => sndPartial (fun y => u y 0) x 2 i - sndPartial (fun y => u y 2) x 0 i
        | 2 => fun x => sndPartial (fun y => u y 1) x 0 i - sndPartial (fun y => u y 0) x 1 i := by
    intro c i
    funext x
    fin_cases c
    · change partialDerivScalar (fun y => curl3D u y 0) x i =
        sndPartial (fun y => u y 2) x 1 i - sndPartial (fun y => u y 1) x 2 i
      have h0 : (fun y => curl3D u y 0) = fun y =>
          partialDerivScalar (fun z => u z 2) y 1 - partialDerivScalar (fun z => u z 1) y 2 := by
        funext y; exact curl3D_zero u y
      rw [h0, partialDerivScalar_sub
            ((contDiff_one_partialDerivScalar_of_two (hu_c2 2) 1).differentiable (by simp) x)
            ((contDiff_one_partialDerivScalar_of_two (hu_c2 1) 2).differentiable (by simp) x) i,
          partial_partial_eq_snd (hu_c2 2) x 1 i, partial_partial_eq_snd (hu_c2 1) x 2 i]
    · change partialDerivScalar (fun y => curl3D u y 1) x i =
        sndPartial (fun y => u y 0) x 2 i - sndPartial (fun y => u y 2) x 0 i
      have h1 : (fun y => curl3D u y 1) = fun y =>
          partialDerivScalar (fun z => u z 0) y 2 - partialDerivScalar (fun z => u z 2) y 0 := by
        funext y; exact curl3D_one u y
      rw [h1, partialDerivScalar_sub
            ((contDiff_one_partialDerivScalar_of_two (hu_c2 0) 2).differentiable (by simp) x)
            ((contDiff_one_partialDerivScalar_of_two (hu_c2 2) 0).differentiable (by simp) x) i,
          partial_partial_eq_snd (hu_c2 0) x 2 i, partial_partial_eq_snd (hu_c2 2) x 0 i]
    · change partialDerivScalar (fun y => curl3D u y 2) x i =
        sndPartial (fun y => u y 1) x 0 i - sndPartial (fun y => u y 0) x 1 i
      have h2 : (fun y => curl3D u y 2) = fun y =>
          partialDerivScalar (fun z => u z 1) y 0 - partialDerivScalar (fun z => u z 0) y 1 := by
        funext y; exact curl3D_two u y
      rw [h2, partialDerivScalar_sub
            ((contDiff_one_partialDerivScalar_of_two (hu_c2 1) 0).differentiable (by simp) x)
            ((contDiff_one_partialDerivScalar_of_two (hu_c2 0) 1).differentiable (by simp) x) i,
          partial_partial_eq_snd (hu_c2 1) x 0 i, partial_partial_eq_snd (hu_c2 0) x 1 i]
  have hw_van1 : ∀ c i : Fin 3,
      VanishesAtInfinityR3 (fun x => partialDerivScalar (fun y => curl3D u y c) x i) := fun c i => by
    rw [hw_p1 c i]
    fin_cases c
    · exact vanishesAtInfinityR3_sub ((hu.h_comp 2).h_van2 1 i) ((hu.h_comp 1).h_van2 2 i)
    · exact vanishesAtInfinityR3_sub ((hu.h_comp 0).h_van2 2 i) ((hu.h_comp 2).h_van2 0 i)
    · exact vanishesAtInfinityR3_sub ((hu.h_comp 1).h_van2 0 i) ((hu.h_comp 0).h_van2 1 i)
  have hw_int0 : ∀ c : Fin 3, Integrable (fun x => (curl3D u x c) ^ 2) volume := fun c => by
    fin_cases c <;> simp only [curl3D, Fin.isValue]
    · exact integrable_sub_sq_of_sq
        (contDiff_one_partialDerivScalar_of_two (hu_c2 2) 1).continuous
        (contDiff_one_partialDerivScalar_of_two (hu_c2 1) 2).continuous
        ((hu.h_comp 2).h_int1 1) ((hu.h_comp 1).h_int1 2)
    · exact integrable_sub_sq_of_sq
        (contDiff_one_partialDerivScalar_of_two (hu_c2 0) 2).continuous
        (contDiff_one_partialDerivScalar_of_two (hu_c2 2) 0).continuous
        ((hu.h_comp 0).h_int1 2) ((hu.h_comp 2).h_int1 0)
    · exact integrable_sub_sq_of_sq
        (contDiff_one_partialDerivScalar_of_two (hu_c2 1) 0).continuous
        (contDiff_one_partialDerivScalar_of_two (hu_c2 0) 1).continuous
        ((hu.h_comp 1).h_int1 0) ((hu.h_comp 0).h_int1 1)
  have hw_int1 : ∀ c i : Fin 3,
      Integrable (fun x => (partialDerivScalar (fun y => curl3D u y c) x i) ^ 2) volume := fun c i => by
    have hfun : (fun x => (partialDerivScalar (fun y => curl3D u y c) x i) ^ 2) =
        fun x => ((fun z => partialDerivScalar (fun y => curl3D u y c) z i) x) ^ 2 := rfl
    rw [hfun, hw_p1 c i]
    fin_cases c
    · exact integrable_sub_sq_of_sq
        (contDiff_one_sndPartial_of_three (hu.h_comp 2).h_c3 1 i).continuous
        (contDiff_one_sndPartial_of_three (hu.h_comp 1).h_c3 2 i).continuous
        ((hu.h_comp 2).h_int2 1 i) ((hu.h_comp 1).h_int2 2 i)
    · exact integrable_sub_sq_of_sq
        (contDiff_one_sndPartial_of_three (hu.h_comp 0).h_c3 2 i).continuous
        (contDiff_one_sndPartial_of_three (hu.h_comp 2).h_c3 0 i).continuous
        ((hu.h_comp 0).h_int2 2 i) ((hu.h_comp 2).h_int2 0 i)
    · exact integrable_sub_sq_of_sq
        (contDiff_one_sndPartial_of_three (hu.h_comp 1).h_c3 0 i).continuous
        (contDiff_one_sndPartial_of_three (hu.h_comp 0).h_c3 1 i).continuous
        ((hu.h_comp 1).h_int2 0 i) ((hu.h_comp 0).h_int2 1 i)
  have hw_int2 : ∀ c i j : Fin 3,
      Integrable (fun x => (sndPartial (fun y => curl3D u y c) x i j) ^ 2) volume := fun c i j => by
    have heq : (fun x => (sndPartial (fun y => curl3D u y c) x i j) ^ 2) =
        fun x => (partialDerivScalar (fun y => partialDerivScalar (fun z => curl3D u z c) y i) x j) ^ 2 := by
      funext x; rw [partial_partial_eq_snd (hw_c2 c) x i j]
    rw [heq, hw_p1 c i]
    have hc3_diff : ∀ a b d e : Fin 3,
        Integrable (fun x => (partialDerivScalar (fun y => sndPartial (fun z => u z a) y b d) x e) ^ 2) volume :=
      fun a b d e => (hu.h_comp a).h_int3 b d e
    have hc3_cont : ∀ a b d e : Fin 3,
        Continuous (fun x => partialDerivScalar (fun y => sndPartial (fun z => u z a) y b d) x e) :=
      fun a b d e =>
        (contDiff_partialDerivScalar_of_succ (n := 0)
          (contDiff_one_sndPartial_of_three (hu.h_comp a).h_c3 b d) e).continuous
    fin_cases c
    · have hsub : (fun x => (partialDerivScalar (fun y =>
          sndPartial (fun z => u z 2) y 1 i - sndPartial (fun z => u z 1) y 2 i) x j) ^ 2) =
          fun x => (partialDerivScalar (fun y => sndPartial (fun z => u z 2) y 1 i) x j -
            partialDerivScalar (fun y => sndPartial (fun z => u z 1) y 2 i) x j) ^ 2 := by
        funext x
        rw [partialDerivScalar_sub
          ((contDiff_one_sndPartial_of_three (hu.h_comp 2).h_c3 1 i).differentiable (by simp) x)
          ((contDiff_one_sndPartial_of_three (hu.h_comp 1).h_c3 2 i).differentiable (by simp) x) j]
      rw [hsub]
      exact integrable_sub_sq_of_sq (hc3_cont 2 1 i j) (hc3_cont 1 2 i j)
        (hc3_diff 2 1 i j) (hc3_diff 1 2 i j)
    · have hsub : (fun x => (partialDerivScalar (fun y =>
          sndPartial (fun z => u z 0) y 2 i - sndPartial (fun z => u z 2) y 0 i) x j) ^ 2) =
          fun x => (partialDerivScalar (fun y => sndPartial (fun z => u z 0) y 2 i) x j -
            partialDerivScalar (fun y => sndPartial (fun z => u z 2) y 0 i) x j) ^ 2 := by
        funext x
        rw [partialDerivScalar_sub
          ((contDiff_one_sndPartial_of_three (hu.h_comp 0).h_c3 2 i).differentiable (by simp) x)
          ((contDiff_one_sndPartial_of_three (hu.h_comp 2).h_c3 0 i).differentiable (by simp) x) j]
      rw [hsub]
      exact integrable_sub_sq_of_sq (hc3_cont 0 2 i j) (hc3_cont 2 0 i j)
        (hc3_diff 0 2 i j) (hc3_diff 2 0 i j)
    · have hsub : (fun x => (partialDerivScalar (fun y =>
          sndPartial (fun z => u z 1) y 0 i - sndPartial (fun z => u z 0) y 1 i) x j) ^ 2) =
          fun x => (partialDerivScalar (fun y => sndPartial (fun z => u z 1) y 0 i) x j -
            partialDerivScalar (fun y => sndPartial (fun z => u z 0) y 1 i) x j) ^ 2 := by
        funext x
        rw [partialDerivScalar_sub
          ((contDiff_one_sndPartial_of_three (hu.h_comp 1).h_c3 0 i).differentiable (by simp) x)
          ((contDiff_one_sndPartial_of_three (hu.h_comp 0).h_c3 1 i).differentiable (by simp) x) j]
      rw [hsub]
      exact integrable_sub_sq_of_sq (hc3_cont 1 0 i j) (hc3_cont 0 1 i j)
        (hc3_diff 1 0 i j) (hc3_diff 0 1 i j)
  have hmain := r3_enstrophy_eq_gradNormSq_of_c2 hw_c2 hw_div hw_van0 hw_van1 hw_int0 hw_int1 hw_int2
  unfold palinstrophyR3
  rw [← hmain]
  apply r3Integral_congr
  intro x
  unfold dot3D
  rw [curl3D_curl3D_eq_neg_laplacian hu_c2 hu.h_div x 0,
      curl3D_curl3D_eq_neg_laplacian hu_c2 hu.h_div x 1,
      curl3D_curl3D_eq_neg_laplacian hu_c2 hu.h_div x 2]
  ring

/-- **THEOREM 10A1-4 (Whole-Space `ℝ³` Derivative Interpolation — Replacing Poincaré on `ℝ³`):**
    On unbounded `ℝ³`, Wirtinger–Poincaré fails at low frequencies (`|ξ| → 0`). It is
    replaced unconditionally by the exact scale-invariant interpolation inequality:
    1. `2 Z_{ℝ³}(u) ≤ √(2 E_{ℝ³}(u)) * √(P_{ℝ³}(u))`,
    2. `2 (Z_{ℝ³}(u))² ≤ E_{ℝ³}(u) * P_{ℝ³}(u)`. -/
theorem r3_interpolation_enstrophy_le {u : R3 → R3} (hu : DecayingH3SolenoidalR3 u) :
    2 * enstrophyR3 u ≤ Real.sqrt (2 * energyR3 u) * Real.sqrt (palinstrophyR3 u) ∧
    2 * (enstrophyR3 u) ^ 2 ≤ energyR3 u * palinstrophyR3 u := by
  have hu_c2 : ∀ c : Fin 3, ContDiff ℝ 2 (fun x => u x c) := fun c =>
    contDiff_two_of_three (hu.h_comp c).h_c3
  have hterm : ∀ c i : Fin 3,
      r3Integral (fun x => (partialDerivScalar (fun y => u y c) x i) ^ 2) =
        -r3Integral (fun x => u x c * sndPartial (fun y => u y c) x i i) := by
    intro c i
    have hd_u : Differentiable ℝ (fun x => u x c) :=
      (contDiff_one_of_three (hu.h_comp c).h_c3).differentiable (by simp)
    have hd_du : Differentiable ℝ (fun x => partialDerivScalar (fun y => u y c) x i) :=
      (contDiff_one_partialDerivScalar_of_two (hu_c2 c) i).differentiable (by simp)
    have hc_u : Continuous (fun x => u x c) := hd_u.continuous
    have hc_s : Continuous (fun x => sndPartial (fun y => u y c) x i i) :=
      (contDiff_one_sndPartial_of_three (hu.h_comp c).h_c3 i i).continuous
    have hibp := r3Integral_ibp hd_u hd_du
      (vanishesAlongAxis_of_vanishesAtInfinityR3
        (vanishesAtInfinityR3_mul (hu.h_comp c).h_van0 ((hu.h_comp c).h_van1 i)) i)
      (by
        have heq : (fun x => partialDerivScalar (fun y => u y c) x i *
            partialDerivScalar (fun y => u y c) x i) =
            fun x => (partialDerivScalar (fun y => u y c) x i) ^ 2 := by funext x; ring
        rw [heq]; exact (hu.h_comp c).h_int1 i)
      (by
        have heq : (fun x => u x c *
            partialDerivScalar (fun y => partialDerivScalar (fun z => u z c) y i) x i) =
            fun x => u x c * sndPartial (fun y => u y c) x i i := by
          funext x; rw [partial_partial_eq_snd (hu_c2 c) x i i]
        rw [heq]; exact integrable_mul_of_sq hc_u hc_s (hu.h_comp c).h_int0 ((hu.h_comp c).h_int2 i i))
    have hL : r3Integral (fun x => u x c *
        partialDerivScalar (fun y => partialDerivScalar (fun z => u z c) y i) x i) =
        r3Integral (fun x => u x c * sndPartial (fun y => u y c) x i i) := by
      apply r3Integral_congr; intro x; rw [partial_partial_eq_snd (hu_c2 c) x i i]
    have hR : r3Integral (fun x => partialDerivScalar (fun y => u y c) x i *
        partialDerivScalar (fun y => u y c) x i) =
        r3Integral (fun x => (partialDerivScalar (fun y => u y c) x i) ^ 2) := by
      apply r3Integral_congr; intro x; ring
    linarith
  have hcomp_ibp : ∀ c : Fin 3,
      r3Integral (fun x =>
        (partialDerivScalar (fun y => u y c) x 0) ^ 2 +
        (partialDerivScalar (fun y => u y c) x 1) ^ 2 +
        (partialDerivScalar (fun y => u y c) x 2) ^ 2) =
      -r3Integral (fun x => u x c * laplacianScalar (fun y => u y c) x) := by
    intro c
    have hc_u : Continuous (fun x => u x c) := (hu.h_comp c).h_c3.continuous
    have hi_mul : ∀ i : Fin 3,
        Integrable (fun x => u x c * sndPartial (fun y => u y c) x i i) volume := fun i =>
      integrable_mul_of_sq hc_u (contDiff_one_sndPartial_of_three (hu.h_comp c).h_c3 i i).continuous
        (hu.h_comp c).h_int0 ((hu.h_comp c).h_int2 i i)
    rw [r3Integral_add3 ((hu.h_comp c).h_int1 0) ((hu.h_comp c).h_int1 1) ((hu.h_comp c).h_int1 2),
        hterm c 0, hterm c 1, hterm c 2]
    have hsum := r3Integral_add3 (hi_mul 0) (hi_mul 1) (hi_mul 2)
    have hpt : ∀ x : R3,
        u x c * sndPartial (fun y => u y c) x 0 0 +
        u x c * sndPartial (fun y => u y c) x 1 1 +
        u x c * sndPartial (fun y => u y c) x 2 2 =
        u x c * laplacianScalar (fun y => u y c) x := fun x => by
      unfold laplacianScalar; ring
    rw [r3Integral_congr hpt] at hsum
    linarith
  have hcomp_cs : ∀ c : Fin 3,
      (r3Integral (fun x => u x c * laplacianScalar (fun y => u y c) x)) ^ 2 ≤
        r3Integral (fun x => (u x c) ^ 2) *
        r3Integral (fun x => (laplacianScalar (fun y => u y c) x) ^ 2) := by
    intro c
    have hc_u : Continuous (fun x => u x c) := (hu.h_comp c).h_c3.continuous
    have hc_l : Continuous (fun x => laplacianScalar (fun y => u y c) x) := by
      unfold laplacianScalar
      exact ((contDiff_one_sndPartial_of_three (hu.h_comp c).h_c3 0 0).continuous.add
        (contDiff_one_sndPartial_of_three (hu.h_comp c).h_c3 1 1).continuous).add
        (contDiff_one_sndPartial_of_three (hu.h_comp c).h_c3 2 2).continuous
    have hl_int : Integrable (fun x => (laplacianScalar (fun y => u y c) x) ^ 2) volume := by
      unfold laplacianScalar
      have c0 := (contDiff_one_sndPartial_of_three (hu.h_comp c).h_c3 0 0).continuous
      have c1 := (contDiff_one_sndPartial_of_three (hu.h_comp c).h_c3 1 1).continuous
      have c2 := (contDiff_one_sndPartial_of_three (hu.h_comp c).h_c3 2 2).continuous
      exact integrable_add_sq_of_sq (c0.add c1) c2
        (integrable_add_sq_of_sq c0 c1 ((hu.h_comp c).h_int2 0 0) ((hu.h_comp c).h_int2 1 1))
        ((hu.h_comp c).h_int2 2 2)
    exact r3_cauchy_schwarz_sq hc_u hc_l (hu.h_comp c).h_int0 hl_int
  let A : Fin 3 → ℝ := fun c => r3Integral (fun x => (u x c) ^ 2)
  let B : Fin 3 → ℝ := fun c => r3Integral (fun x => (laplacianScalar (fun y => u y c) x) ^ 2)
  have hA_nn : ∀ c : Fin 3, 0 ≤ A c := fun c => r3Integral_nonneg (fun _ => sq_nonneg _)
  have hB_nn : ∀ c : Fin 3, 0 ≤ B c := fun c => r3Integral_nonneg (fun _ => sq_nonneg _)
  have hG_le : ∀ c : Fin 3,
      r3Integral (fun x =>
        (partialDerivScalar (fun y => u y c) x 0) ^ 2 +
        (partialDerivScalar (fun y => u y c) x 1) ^ 2 +
        (partialDerivScalar (fun y => u y c) x 2) ^ 2) ≤
      Real.sqrt (A c) * Real.sqrt (B c) := fun c => by
    have hnn_L : 0 ≤ r3Integral (fun x =>
        (partialDerivScalar (fun y => u y c) x 0) ^ 2 +
        (partialDerivScalar (fun y => u y c) x 1) ^ 2 +
        (partialDerivScalar (fun y => u y c) x 2) ^ 2) :=
      r3Integral_nonneg (fun _ => by positivity)
    have hnn_R : 0 ≤ Real.sqrt (A c) * Real.sqrt (B c) := by positivity
    have hsq : (r3Integral (fun x =>
        (partialDerivScalar (fun y => u y c) x 0) ^ 2 +
        (partialDerivScalar (fun y => u y c) x 1) ^ 2 +
        (partialDerivScalar (fun y => u y c) x 2) ^ 2)) ^ 2 ≤
        (Real.sqrt (A c) * Real.sqrt (B c)) ^ 2 := by
      rw [hcomp_ibp c, neg_sq, mul_pow, Real.sq_sqrt (hA_nn c), Real.sq_sqrt (hB_nn c)]
      exact hcomp_cs c
    nlinarith
  have h2Z_eq : 2 * enstrophyR3 u = r3Integral (gradNormSqR3 u) := by
    unfold enstrophyR3
    rw [r3_enstrophy_eq_half_gradNormSq hu]
    ring
  have hG_split : r3Integral (gradNormSqR3 u) =
      r3Integral (fun x =>
        (partialDerivScalar (fun y => u y 0) x 0) ^ 2 +
        (partialDerivScalar (fun y => u y 0) x 1) ^ 2 +
        (partialDerivScalar (fun y => u y 0) x 2) ^ 2) +
      r3Integral (fun x =>
        (partialDerivScalar (fun y => u y 1) x 0) ^ 2 +
        (partialDerivScalar (fun y => u y 1) x 1) ^ 2 +
        (partialDerivScalar (fun y => u y 1) x 2) ^ 2) +
      r3Integral (fun x =>
        (partialDerivScalar (fun y => u y 2) x 0) ^ 2 +
        (partialDerivScalar (fun y => u y 2) x 1) ^ 2 +
        (partialDerivScalar (fun y => u y 2) x 2) ^ 2) := by
    have hpt : ∀ x : R3, gradNormSqR3 u x =
        ((partialDerivScalar (fun y => u y 0) x 0) ^ 2 +
         (partialDerivScalar (fun y => u y 0) x 1) ^ 2 +
         (partialDerivScalar (fun y => u y 0) x 2) ^ 2) +
        ((partialDerivScalar (fun y => u y 1) x 0) ^ 2 +
         (partialDerivScalar (fun y => u y 1) x 1) ^ 2 +
         (partialDerivScalar (fun y => u y 1) x 2) ^ 2) +
        ((partialDerivScalar (fun y => u y 2) x 0) ^ 2 +
         (partialDerivScalar (fun y => u y 2) x 1) ^ 2 +
         (partialDerivScalar (fun y => u y 2) x 2) ^ 2) := fun x => by
      unfold gradNormSqR3; ring
    rw [r3Integral_congr hpt,
        r3Integral_add3
          (int_add (int_add ((hu.h_comp 0).h_int1 0) ((hu.h_comp 0).h_int1 1)) ((hu.h_comp 0).h_int1 2))
          (int_add (int_add ((hu.h_comp 1).h_int1 0) ((hu.h_comp 1).h_int1 1)) ((hu.h_comp 1).h_int1 2))
          (int_add (int_add ((hu.h_comp 2).h_int1 0) ((hu.h_comp 2).h_int1 1)) ((hu.h_comp 2).h_int1 2))]
  have h2E_eq : 2 * energyR3 u = A 0 + A 1 + A 2 := by
    unfold energyR3
    have hpt : ∀ x : R3, dot3D (u x) (u x) = (u x 0) ^ 2 + (u x 1) ^ 2 + (u x 2) ^ 2 := fun x => by
      unfold dot3D; ring
    rw [r3Integral_congr hpt,
        r3Integral_add3 (hu.h_comp 0).h_int0 (hu.h_comp 1).h_int0 (hu.h_comp 2).h_int0]
    dsimp only [A]; ring
  have hP_eq : palinstrophyR3 u = B 0 + B 1 + B 2 := by
    rw [r3_palinstrophy_eq_laplacianNormSq hu]
    have hpt : ∀ x : R3, dot3D (laplacian3D u x) (laplacian3D u x) =
        (laplacianScalar (fun y => u y 0) x) ^ 2 +
        (laplacianScalar (fun y => u y 1) x) ^ 2 +
        (laplacianScalar (fun y => u y 2) x) ^ 2 := fun x => by
      unfold dot3D laplacian3D; ring
    have hl_int : ∀ c : Fin 3, Integrable (fun x => (laplacianScalar (fun y => u y c) x) ^ 2) volume := by
      intro c
      unfold laplacianScalar
      have c0 := (contDiff_one_sndPartial_of_three (hu.h_comp c).h_c3 0 0).continuous
      have c1 := (contDiff_one_sndPartial_of_three (hu.h_comp c).h_c3 1 1).continuous
      have c2 := (contDiff_one_sndPartial_of_three (hu.h_comp c).h_c3 2 2).continuous
      exact integrable_add_sq_of_sq (c0.add c1) c2
        (integrable_add_sq_of_sq c0 c1 ((hu.h_comp c).h_int2 0 0) ((hu.h_comp c).h_int2 1 1))
        ((hu.h_comp c).h_int2 2 2)
    rw [r3Integral_congr hpt, r3Integral_add3 (hl_int 0) (hl_int 1) (hl_int 2)]
  have hcs3 : Real.sqrt (A 0) * Real.sqrt (B 0) + Real.sqrt (A 1) * Real.sqrt (B 1) +
      Real.sqrt (A 2) * Real.sqrt (B 2) ≤
      Real.sqrt (A 0 + A 1 + A 2) * Real.sqrt (B 0 + B 1 + B 2) := by
    have hL_nn : 0 ≤ Real.sqrt (A 0) * Real.sqrt (B 0) + Real.sqrt (A 1) * Real.sqrt (B 1) +
        Real.sqrt (A 2) * Real.sqrt (B 2) := by positivity
    have hR_nn : 0 ≤ Real.sqrt (A 0 + A 1 + A 2) * Real.sqrt (B 0 + B 1 + B 2) := by positivity
    have hsq : (Real.sqrt (A 0) * Real.sqrt (B 0) + Real.sqrt (A 1) * Real.sqrt (B 1) +
        Real.sqrt (A 2) * Real.sqrt (B 2)) ^ 2 ≤
        (Real.sqrt (A 0 + A 1 + A 2) * Real.sqrt (B 0 + B 1 + B 2)) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt (by linarith [hA_nn 0, hA_nn 1, hA_nn 2]),
          Real.sq_sqrt (by linarith [hB_nn 0, hB_nn 1, hB_nn 2])]
      have s0 := Real.sq_sqrt (hA_nn 0); have s1 := Real.sq_sqrt (hA_nn 1); have s2 := Real.sq_sqrt (hA_nn 2)
      have t0 := Real.sq_sqrt (hB_nn 0); have t1 := Real.sq_sqrt (hB_nn 1); have t2 := Real.sq_sqrt (hB_nn 2)
      nlinarith [sq_nonneg (Real.sqrt (A 0) * Real.sqrt (B 1) - Real.sqrt (A 1) * Real.sqrt (B 0)),
                 sq_nonneg (Real.sqrt (A 0) * Real.sqrt (B 2) - Real.sqrt (A 2) * Real.sqrt (B 0)),
                 sq_nonneg (Real.sqrt (A 1) * Real.sqrt (B 2) - Real.sqrt (A 2) * Real.sqrt (B 1))]
    nlinarith
  have h1 : 2 * enstrophyR3 u ≤ Real.sqrt (2 * energyR3 u) * Real.sqrt (palinstrophyR3 u) := by
    rw [h2Z_eq, hG_split, h2E_eq, hP_eq]
    linarith [hG_le 0, hG_le 1, hG_le 2, hcs3]
  have hZ_nn : 0 ≤ enstrophyR3 u := by
    unfold enstrophyR3; linarith [r3Integral_nonneg (fun x => dot3D_self_nonneg_r3 (curl3D u x))]
  have hE_nn : 0 ≤ energyR3 u := by
    unfold energyR3; linarith [r3Integral_nonneg (fun x => dot3D_self_nonneg_r3 (u x))]
  have hP_nn : 0 ≤ palinstrophyR3 u := r3Integral_nonneg (fun x => gradNormSqR3_nonneg (curl3D u) x)
  have h2 : 2 * (enstrophyR3 u) ^ 2 ≤ energyR3 u * palinstrophyR3 u := by
    have hsq : (2 * enstrophyR3 u) ^ 2 ≤
        (Real.sqrt (2 * energyR3 u) * Real.sqrt (palinstrophyR3 u)) ^ 2 := by
      nlinarith
    rw [mul_pow, mul_pow, Real.sq_sqrt (by linarith), Real.sq_sqrt hP_nn] at hsq
    linarith
  exact ⟨h1, h2⟩

/-- **THEOREM 10A1-5 (Whole-Space `ℝ³` Exact Vortex Stretching IBP Identity):**
    For any `u` in `DecayingH3SolenoidalR3`, using `∇ · ω = 0` and decay at infinity:
    `vortexStretchingR3 u = -∫_{ℝ³} ⟨u, (ω · ∇)ω⟩ dx`. -/
theorem r3_vortexStretching_eq_neg_ibp {u : R3 → R3} (hu : DecayingH3SolenoidalR3 u) :
    vortexStretchingR3 u =
      -r3Integral (fun x => dot3D (u x) (directionalAdvection3D (curl3D u) (curl3D u) x)) := by
  have hu_c2 : ∀ c : Fin 3, ContDiff ℝ 2 (fun x => u x c) := fun c =>
    contDiff_two_of_three (hu.h_comp c).h_c3
  have hw_c2 : ∀ c : Fin 3, ContDiff ℝ 2 (fun x => curl3D u x c) := fun c => by
    fin_cases c <;> simp only [curl3D, Fin.isValue]
    · exact (contDiff_two_partialDerivScalar_of_three (hu.h_comp 2).h_c3 1).sub
        (contDiff_two_partialDerivScalar_of_three (hu.h_comp 1).h_c3 2)
    · exact (contDiff_two_partialDerivScalar_of_three (hu.h_comp 0).h_c3 2).sub
        (contDiff_two_partialDerivScalar_of_three (hu.h_comp 2).h_c3 0)
    · exact (contDiff_two_partialDerivScalar_of_three (hu.h_comp 1).h_c3 0).sub
        (contDiff_two_partialDerivScalar_of_three (hu.h_comp 0).h_c3 1)
  have hw_van0 : ∀ c : Fin 3, VanishesAtInfinityR3 (fun x => curl3D u x c) := fun c => by
    fin_cases c <;> simp only [curl3D, Fin.isValue]
    · exact vanishesAtInfinityR3_sub ((hu.h_comp 2).h_van1 1) ((hu.h_comp 1).h_van1 2)
    · exact vanishesAtInfinityR3_sub ((hu.h_comp 0).h_van1 2) ((hu.h_comp 2).h_van1 0)
    · exact vanishesAtInfinityR3_sub ((hu.h_comp 1).h_van1 0) ((hu.h_comp 0).h_van1 1)
  have hw_int0 : ∀ c : Fin 3, Integrable (fun x => (curl3D u x c) ^ 2) volume := fun c => by
    fin_cases c <;> simp only [curl3D, Fin.isValue]
    · exact integrable_sub_sq_of_sq
        (contDiff_one_partialDerivScalar_of_two (hu_c2 2) 1).continuous
        (contDiff_one_partialDerivScalar_of_two (hu_c2 1) 2).continuous
        ((hu.h_comp 2).h_int1 1) ((hu.h_comp 1).h_int1 2)
    · exact integrable_sub_sq_of_sq
        (contDiff_one_partialDerivScalar_of_two (hu_c2 0) 2).continuous
        (contDiff_one_partialDerivScalar_of_two (hu_c2 2) 0).continuous
        ((hu.h_comp 0).h_int1 2) ((hu.h_comp 2).h_int1 0)
    · exact integrable_sub_sq_of_sq
        (contDiff_one_partialDerivScalar_of_two (hu_c2 1) 0).continuous
        (contDiff_one_partialDerivScalar_of_two (hu_c2 0) 1).continuous
        ((hu.h_comp 1).h_int1 0) ((hu.h_comp 0).h_int1 1)
  have hw_int1 : ∀ c i : Fin 3,
      Integrable (fun x => (partialDerivScalar (fun y => curl3D u y c) x i) ^ 2) volume := fun c i => by
    fin_cases c
    · change Integrable (fun x => (partialDerivScalar (fun y => curl3D u y 0) x i) ^ 2) volume
      have h0 : (fun y => curl3D u y 0) = fun y =>
          partialDerivScalar (fun z => u z 2) y 1 - partialDerivScalar (fun z => u z 1) y 2 := by
        funext y; exact curl3D_zero u y
      have heq : (fun x => (partialDerivScalar (fun y => curl3D u y 0) x i) ^ 2) =
          fun x => (sndPartial (fun y => u y 2) x 1 i - sndPartial (fun y => u y 1) x 2 i) ^ 2 := by
        funext x
        rw [h0, partialDerivScalar_sub
              ((contDiff_one_partialDerivScalar_of_two (hu_c2 2) 1).differentiable (by simp) x)
              ((contDiff_one_partialDerivScalar_of_two (hu_c2 1) 2).differentiable (by simp) x) i,
            partial_partial_eq_snd (hu_c2 2) x 1 i, partial_partial_eq_snd (hu_c2 1) x 2 i]
      rw [heq]
      exact integrable_sub_sq_of_sq
        (contDiff_one_sndPartial_of_three (hu.h_comp 2).h_c3 1 i).continuous
        (contDiff_one_sndPartial_of_three (hu.h_comp 1).h_c3 2 i).continuous
        ((hu.h_comp 2).h_int2 1 i) ((hu.h_comp 1).h_int2 2 i)
    · change Integrable (fun x => (partialDerivScalar (fun y => curl3D u y 1) x i) ^ 2) volume
      have h1 : (fun y => curl3D u y 1) = fun y =>
          partialDerivScalar (fun z => u z 0) y 2 - partialDerivScalar (fun z => u z 2) y 0 := by
        funext y; exact curl3D_one u y
      have heq : (fun x => (partialDerivScalar (fun y => curl3D u y 1) x i) ^ 2) =
          fun x => (sndPartial (fun y => u y 0) x 2 i - sndPartial (fun y => u y 2) x 0 i) ^ 2 := by
        funext x
        rw [h1, partialDerivScalar_sub
              ((contDiff_one_partialDerivScalar_of_two (hu_c2 0) 2).differentiable (by simp) x)
              ((contDiff_one_partialDerivScalar_of_two (hu_c2 2) 0).differentiable (by simp) x) i,
            partial_partial_eq_snd (hu_c2 0) x 2 i, partial_partial_eq_snd (hu_c2 2) x 0 i]
      rw [heq]
      exact integrable_sub_sq_of_sq
        (contDiff_one_sndPartial_of_three (hu.h_comp 0).h_c3 2 i).continuous
        (contDiff_one_sndPartial_of_three (hu.h_comp 2).h_c3 0 i).continuous
        ((hu.h_comp 0).h_int2 2 i) ((hu.h_comp 2).h_int2 0 i)
    · change Integrable (fun x => (partialDerivScalar (fun y => curl3D u y 2) x i) ^ 2) volume
      have h2 : (fun y => curl3D u y 2) = fun y =>
          partialDerivScalar (fun z => u z 1) y 0 - partialDerivScalar (fun z => u z 0) y 1 := by
        funext y; exact curl3D_two u y
      have heq : (fun x => (partialDerivScalar (fun y => curl3D u y 2) x i) ^ 2) =
          fun x => (sndPartial (fun y => u y 1) x 0 i - sndPartial (fun y => u y 0) x 1 i) ^ 2 := by
        funext x
        rw [h2, partialDerivScalar_sub
              ((contDiff_one_partialDerivScalar_of_two (hu_c2 1) 0).differentiable (by simp) x)
              ((contDiff_one_partialDerivScalar_of_two (hu_c2 0) 1).differentiable (by simp) x) i,
            partial_partial_eq_snd (hu_c2 1) x 0 i, partial_partial_eq_snd (hu_c2 0) x 1 i]
      rw [heq]
      exact integrable_sub_sq_of_sq
        (contDiff_one_sndPartial_of_three (hu.h_comp 1).h_c3 0 i).continuous
        (contDiff_one_sndPartial_of_three (hu.h_comp 0).h_c3 1 i).continuous
        ((hu.h_comp 1).h_int2 0 i) ((hu.h_comp 0).h_int2 1 i)
  have hu_bdd : ∀ c : Fin 3, ∃ C : ℝ, 0 ≤ C ∧ ∀ x : R3, |u x c| ≤ C := fun c =>
    exists_bound_of_vanishesAtInfinityR3 (hu.h_comp c).h_c3.continuous (hu.h_comp c).h_van0
  have hdu_bdd : ∀ c i : Fin 3,
      ∃ C : ℝ, 0 ≤ C ∧ ∀ x : R3, |partialDerivScalar (fun y => u y c) x i| ≤ C := fun c i =>
    exists_bound_of_vanishesAtInfinityR3
      (contDiff_one_partialDerivScalar_of_two (hu_c2 c) i).continuous ((hu.h_comp c).h_van1 i)
  have h_l_int : ∀ c i : Fin 3,
      Integrable (fun x => (curl3D u x i * curl3D u x c) *
        partialDerivScalar (fun y => u y c) x i) volume := fun c i => by
    have heq : (fun x => (curl3D u x i * curl3D u x c) *
        partialDerivScalar (fun y => u y c) x i) =
        fun x => partialDerivScalar (fun y => u y c) x i * (curl3D u x i * curl3D u x c) := by
      funext x; ring
    rw [heq]
    exact integrable_bdd_mul_mul_of_sq
      (contDiff_one_partialDerivScalar_of_two (hu_c2 c) i).continuous
      (hw_c2 i).continuous (hw_c2 c).continuous (hdu_bdd c i) (hw_int0 i) (hw_int0 c)
  have h_r1_int : ∀ c i : Fin 3,
      Integrable (fun x => partialDerivScalar (fun y => curl3D u y i) x i *
        curl3D u x c * u x c) volume := fun c i => by
    have heq : (fun x => partialDerivScalar (fun y => curl3D u y i) x i * curl3D u x c * u x c) =
        fun x => u x c * (partialDerivScalar (fun y => curl3D u y i) x i * curl3D u x c) := by
      funext x; ring
    rw [heq]
    exact integrable_bdd_mul_mul_of_sq
      (hu.h_comp c).h_c3.continuous
      (contDiff_one_partialDerivScalar_of_two (hw_c2 i) i).continuous
      (hw_c2 c).continuous (hu_bdd c) (hw_int1 i i) (hw_int0 c)
  have h_r2_int : ∀ c i : Fin 3,
      Integrable (fun x => curl3D u x i *
        partialDerivScalar (fun y => curl3D u y c) x i * u x c) volume := fun c i => by
    have heq : (fun x => curl3D u x i * partialDerivScalar (fun y => curl3D u y c) x i * u x c) =
        fun x => u x c * (curl3D u x i * partialDerivScalar (fun y => curl3D u y c) x i) := by
      funext x; ring
    rw [heq]
    exact integrable_bdd_mul_mul_of_sq
      (hu.h_comp c).h_c3.continuous
      (hw_c2 i).continuous
      (contDiff_one_partialDerivScalar_of_two (hw_c2 c) i).continuous
      (hu_bdd c) (hw_int0 i) (hw_int1 c i)
  have h_r_int : ∀ c i : Fin 3,
      Integrable (fun x =>
        (partialDerivScalar (fun y => curl3D u y i) x i * curl3D u x c +
         curl3D u x i * partialDerivScalar (fun y => curl3D u y c) x i) * u x c) volume := fun c i => by
    have heq : (fun x =>
        (partialDerivScalar (fun y => curl3D u y i) x i * curl3D u x c +
         curl3D u x i * partialDerivScalar (fun y => curl3D u y c) x i) * u x c) =
        fun x => partialDerivScalar (fun y => curl3D u y i) x i * curl3D u x c * u x c +
          curl3D u x i * partialDerivScalar (fun y => curl3D u y c) x i * u x c := by
      funext x; ring
    rw [heq]; exact (h_r1_int c i).add (h_r2_int c i)
  have hterm : ∀ c i : Fin 3,
      r3Integral (fun x => (curl3D u x i * curl3D u x c) *
          partialDerivScalar (fun y => u y c) x i) =
        -r3Integral (fun x =>
          (partialDerivScalar (fun y => curl3D u y i) x i * curl3D u x c +
           curl3D u x i * partialDerivScalar (fun y => curl3D u y c) x i) * u x c) := by
    intro c i
    have hd_wi : Differentiable ℝ (fun y => curl3D u y i) :=
      (hw_c2 i).differentiable (by simp)
    have hd_wc : Differentiable ℝ (fun y => curl3D u y c) :=
      (hw_c2 c).differentiable (by simp)
    have hd_uc : Differentiable ℝ (fun y => u y c) :=
      (contDiff_one_of_three (hu.h_comp c).h_c3).differentiable (by simp)
    have hd_wprod : Differentiable ℝ (fun y => curl3D u y i * curl3D u y c) := hd_wi.mul hd_wc
    have hmul_p : (fun x => partialDerivScalar (fun y => curl3D u y i * curl3D u y c) x i * u x c) =
        fun x => (partialDerivScalar (fun y => curl3D u y i) x i * curl3D u x c +
          curl3D u x i * partialDerivScalar (fun y => curl3D u y c) x i) * u x c := by
      funext x
      rw [partialDerivScalar_mul (hd_wi x) (hd_wc x) i]
      ring
    have hibp := r3Integral_ibp hd_wprod hd_uc
      (vanishesAlongAxis_of_vanishesAtInfinityR3
        (vanishesAtInfinityR3_mul (vanishesAtInfinityR3_mul (hw_van0 i) (hw_van0 c))
          (hu.h_comp c).h_van0) i)
      (by rw [hmul_p]; exact h_r_int c i) (h_l_int c i)
    rw [hmul_p] at hibp
    exact hibp
  have h_comp : ∀ c : Fin 3,
      r3Integral (fun x => directionalAdvection3D (curl3D u) u x c * curl3D u x c) =
        -r3Integral (fun x => u x c * directionalAdvection3D (curl3D u) (curl3D u) x c) := by
    intro c
    have hlhs_pt : ∀ x : R3,
        directionalAdvection3D (curl3D u) u x c * curl3D u x c =
          (curl3D u x 0 * curl3D u x c) * partialDerivScalar (fun y => u y c) x 0 +
          (curl3D u x 1 * curl3D u x c) * partialDerivScalar (fun y => u y c) x 1 +
          (curl3D u x 2 * curl3D u x c) * partialDerivScalar (fun y => u y c) x 2 := fun x => by
      unfold directionalAdvection3D; ring
    have hrhs_pt : ∀ x : R3,
        ((partialDerivScalar (fun y => curl3D u y 0) x 0 * curl3D u x c +
          curl3D u x 0 * partialDerivScalar (fun y => curl3D u y c) x 0) * u x c) +
        ((partialDerivScalar (fun y => curl3D u y 1) x 1 * curl3D u x c +
          curl3D u x 1 * partialDerivScalar (fun y => curl3D u y c) x 1) * u x c) +
        ((partialDerivScalar (fun y => curl3D u y 2) x 2 * curl3D u x c +
          curl3D u x 2 * partialDerivScalar (fun y => curl3D u y c) x 2) * u x c) =
        u x c * directionalAdvection3D (curl3D u) (curl3D u) x c := fun x => by
      have hdiv0 : div3D (curl3D u) x = 0 :=
        div3D_curl3D_eq_zero u x (contDiff_pi.mpr hu_c2).contDiffAt
      unfold div3D at hdiv0
      unfold directionalAdvection3D
      linear_combination (curl3D u x c * u x c) * hdiv0
    rw [r3Integral_congr hlhs_pt,
        r3Integral_add3 (h_l_int c 0) (h_l_int c 1) (h_l_int c 2),
        hterm c 0, hterm c 1, hterm c 2]
    have hsum := r3Integral_add3 (h_r_int c 0) (h_r_int c 1) (h_r_int c 2)
    rw [r3Integral_congr hrhs_pt] at hsum
    linarith
  have h_lhs_comp_int : ∀ c : Fin 3,
      Integrable (fun x => directionalAdvection3D (curl3D u) u x c * curl3D u x c) volume := fun c => by
    have hpt : (fun x => directionalAdvection3D (curl3D u) u x c * curl3D u x c) =
        fun x => (curl3D u x 0 * curl3D u x c) * partialDerivScalar (fun y => u y c) x 0 +
          (curl3D u x 1 * curl3D u x c) * partialDerivScalar (fun y => u y c) x 1 +
          (curl3D u x 2 * curl3D u x c) * partialDerivScalar (fun y => u y c) x 2 := by
      funext x; unfold directionalAdvection3D; ring
    rw [hpt]; exact ((h_l_int c 0).add (h_l_int c 1)).add (h_l_int c 2)
  have h_rhs_comp_int : ∀ c : Fin 3,
      Integrable (fun x => u x c * directionalAdvection3D (curl3D u) (curl3D u) x c) volume := fun c => by
    have hpt : (fun x => u x c * directionalAdvection3D (curl3D u) (curl3D u) x c) =
        fun x => curl3D u x 0 * partialDerivScalar (fun y => curl3D u y c) x 0 * u x c +
          curl3D u x 1 * partialDerivScalar (fun y => curl3D u y c) x 1 * u x c +
          curl3D u x 2 * partialDerivScalar (fun y => curl3D u y c) x 2 * u x c := by
      funext x; unfold directionalAdvection3D; ring
    rw [hpt]; exact ((h_r2_int c 0).add (h_r2_int c 1)).add (h_r2_int c 2)
  unfold vortexStretchingR3
  have hdot_l : ∀ x : R3,
      dot3D (directionalAdvection3D (curl3D u) u x) (curl3D u x) =
        directionalAdvection3D (curl3D u) u x 0 * curl3D u x 0 +
        directionalAdvection3D (curl3D u) u x 1 * curl3D u x 1 +
        directionalAdvection3D (curl3D u) u x 2 * curl3D u x 2 := fun _ => rfl
  have hdot_r : ∀ x : R3,
      dot3D (u x) (directionalAdvection3D (curl3D u) (curl3D u) x) =
        u x 0 * directionalAdvection3D (curl3D u) (curl3D u) x 0 +
        u x 1 * directionalAdvection3D (curl3D u) (curl3D u) x 1 +
        u x 2 * directionalAdvection3D (curl3D u) (curl3D u) x 2 := fun _ => rfl
  rw [r3Integral_congr hdot_l,
      r3Integral_add3 (h_lhs_comp_int 0) (h_lhs_comp_int 1) (h_lhs_comp_int 2),
      r3Integral_congr hdot_r,
      r3Integral_add3 (h_rhs_comp_int 0) (h_rhs_comp_int 1) (h_rhs_comp_int 2),
      h_comp 0, h_comp 1, h_comp 2]
  ring

-- ============================================================================
-- SECTION 4: NON-VACUITY AUDIT & AXIOM TRAIL (0 sorryAx, 0 custom axioms)
-- ============================================================================

/-- Non-vacuity witness: the identically zero velocity field belongs to `DecayingH3SolenoidalR3`. -/
theorem zero_is_decayingH3SolenoidalR3 :
    DecayingH3SolenoidalR3 (fun _ : R3 => (0 : R3)) where
  h_comp := fun _ => {
    h_c3 := contDiff_const
    h_van0 := by
      change VanishesAtInfinityR3 (fun _ : R3 => (0 : ℝ))
      exact tendsto_const_nhds
    h_van1 := fun i => by
      change VanishesAtInfinityR3 (fun x : R3 => partialDerivScalar (fun _ : R3 => (0 : ℝ)) x i)
      have h : (fun x : R3 => partialDerivScalar (fun _ : R3 => (0 : ℝ)) x i) = fun _ => 0 := by
        funext x; exact partialDerivScalar_const 0 x i
      rw [h]; exact tendsto_const_nhds
    h_van2 := fun i j => by
      change VanishesAtInfinityR3 (fun x : R3 => sndPartial (fun _ : R3 => (0 : ℝ)) x i j)
      have h : (fun x : R3 => sndPartial (fun _ : R3 => (0 : ℝ)) x i j) = fun _ => 0 := by
        funext x; exact sndPartial_const 0 x i j
      rw [h]; exact tendsto_const_nhds
    h_int0 := by simp
    h_int1 := fun i => by
      change Integrable (fun x : R3 => (partialDerivScalar (fun _ : R3 => (0 : ℝ)) x i) ^ 2) volume
      have h : (fun x : R3 => (partialDerivScalar (fun _ : R3 => (0 : ℝ)) x i) ^ 2) = fun _ => 0 := by
        funext x; rw [partialDerivScalar_const]; norm_num
      rw [h]; simp
    h_int2 := fun i j => by
      change Integrable (fun x : R3 => (sndPartial (fun _ : R3 => (0 : ℝ)) x i j) ^ 2) volume
      have h : (fun x : R3 => (sndPartial (fun _ : R3 => (0 : ℝ)) x i j) ^ 2) = fun _ => 0 := by
        funext x; rw [sndPartial_const]; norm_num
      rw [h]; simp
    h_int3 := fun i j k => by
      change Integrable (fun x : R3 =>
        (partialDerivScalar (fun y => sndPartial (fun _ : R3 => (0 : ℝ)) y i j) x k) ^ 2) volume
      have h1 : (fun y : R3 => sndPartial (fun _ : R3 => (0 : ℝ)) y i j) = fun _ => 0 := by
        funext y; exact sndPartial_const 0 y i j
      have h2 : (fun x : R3 => (partialDerivScalar (fun y => sndPartial (fun _ : R3 => (0 : ℝ)) y i j) x k) ^ 2) =
          fun _ => 0 := by
        funext x; rw [h1, partialDerivScalar_const]; norm_num
      rw [h2]; simp
  }
  h_div := fun x => by
    unfold div3D
    have h0 : (fun y : R3 => (0 : R3) 0) = fun _ => (0 : ℝ) := rfl
    have h1 : (fun y : R3 => (0 : R3) 1) = fun _ => (0 : ℝ) := rfl
    have h2 : (fun y : R3 => (0 : R3) 2) = fun _ => (0 : ℝ) := rfl
    simp [partialDerivScalar_const]

#print axioms r3Integral_ibp
#print axioms r3_hessian_eq_laplacian_sq
#print axioms r3_enstrophy_eq_half_gradNormSq
#print axioms r3_palinstrophy_eq_laplacianNormSq
#print axioms r3_interpolation_enstrophy_le
#print axioms r3_vortexStretching_eq_neg_ibp
#print axioms zero_is_decayingH3SolenoidalR3

end GarryWholeSpaceR3