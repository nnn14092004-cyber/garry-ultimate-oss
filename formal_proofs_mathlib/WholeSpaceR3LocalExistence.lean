import AdversarialSupercriticalLabNS3D
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

/-!
# Milestone 15D-1 (Whole-Space `ℝ³` Local Existence — Part 1/2):
  Continuous `H²(ℝ³)` Fourier Convolution Banach Algebra (`C = 16π²`),
  Tame Moser–Wiener Estimate (`C = 8`), Continuous 3D Young Inequality (`L¹ * L² → L²`),
  Complex Leray–Helmholtz Projector `ℙ_ξ`, Heat-Smoothed Bilinear Operator (`8π²/(ντ)`)
  & Reverse Fourier Synthesis `H²(ℝ³) ↪ C⁰_b(ℝ³)` (`0 sorryAx`)

This module builds the concrete continuous whole-space `ℝ³` counterpart of Milestones 6A
(`SpectralAlgebraTorus3D` & `SpectralBilinearTorus3D`) directly on top of
`r3Integral_inv_rho_pow4` (`∫_{ℝ³} (1 + |ξ|²)⁻² dξ = π²`), `heatMultiplier3D`, and
`fourierSynthR3`:
1. **Section 0 (`H²(ℝ³)` Convolution Banach Algebra):**
   - `r3Integral_inv_h2WeightR3`: exact `∫_{ℝ³} (1 + |ξ|²)⁻² dξ = π²`.
   - `h2R3_l1_embedding`: `(∫_{ℝ³} ‖a(ξ)‖ dξ)² ≤ π² · h2NormSqR3 a`.
   - `young_l1_l2_r3`: continuous 3D Young convolution inequality `L¹(ℝ³) * L²(ℝ³) → L²(ℝ³)`.
   - `convR3_tame_and_banach_algebra` & `convR3_self_sub_lipschitz`: tame `C = 8`, Banach
     algebra `C = 16π²`, and quadratic Lipschitz `C = 32π²` in `H²(ℝ³)`.
2. **Section 1 (Solenoidal `H²_σ(ℝ³)`, Heat-Smoothed Bilinear Operator & Physical Synthesis):**
   - `lerayProjR3C_solenoidal_and_contraction`: divergence-free image, orthogonal contraction,
     Hermitian reality symmetry, and linearity.
   - `heatSmoothedBilinearR3_structure`, `heatSmoothedBilinearR3_inH2_and_bound`, and
     `heatSmoothedBilinearR3_self_sub_lipschitz`: explicit `8π²/(ντ)` bound and `16π²/(ντ)`
     quadratic Lipschitz bound preserving solenoidality and reality symmetry.
   - `synthVecR3_continuous_Linf_and_fourierSynth_bridge`: `H²(ℝ³) ↪ C⁰_b(ℝ³)` with
     `|U(x)|² ≤ π² ‖u‖²_{H²}` and exact equivalence with `fourierSynthR3`.
-/

namespace GarryWholeSpaceR3LocalExistence

open MeasureTheory Filter Topology
open GarryReal3DCalculus
open GarryWholeSpaceR3
open GarryWholeSpaceR3Agmon
open GarryHeatLerayMildNS3D
open GarryConcreteNS3DClosures

-- ============================================================================
-- SECTION 0: CONTINUOUS H²(ℝ³) CONVOLUTION BANACH ALGEBRA & 3D YOUNG LAW
-- ============================================================================

/-- Continuous `H²(ℝ³)` spectral weight `w(ξ) = (1 + |ξ|²)² = ⟨ξ⟩⁴ ≥ 1`. -/
noncomputable def h2WeightR3 (ξ : R3) : ℝ :=
  (1 + dot3D ξ ξ) ^ 2

/-- Membership in the continuous complex Sobolev space `H²(ℝ³; ℂ)` in frequency variables. -/
def InH2R3 (a : R3 → ℂ) : Prop :=
  AEStronglyMeasurable a volume ∧
  Integrable (fun ξ : R3 => h2WeightR3 ξ * ‖a ξ‖ ^ 2) volume

/-- Squared `H²(ℝ³)` norm `∫_{ℝ³} (1 + |ξ|²)² ‖a(ξ)‖² dξ`. -/
noncomputable def h2NormSqR3 (a : R3 → ℂ) : ℝ :=
  r3Integral (fun ξ : R3 => h2WeightR3 ξ * ‖a ξ‖ ^ 2)

lemma one_le_h2WeightR3 (ξ : R3) : 1 ≤ h2WeightR3 ξ := by
  unfold h2WeightR3
  have h0 : 0 ≤ dot3D ξ ξ := dot3D_self_nonneg_r3 ξ
  nlinarith

lemma h2WeightR3_pos (ξ : R3) : 0 < h2WeightR3 ξ :=
  lt_of_lt_of_le zero_lt_one (one_le_h2WeightR3 ξ)

lemma h2WeightR3_continuous : Continuous h2WeightR3 := by
  unfold h2WeightR3 dot3D
  fun_prop

lemma h2NormSqR3_nonneg (a : R3 → ℂ) : 0 ≤ h2NormSqR3 a :=
  r3Integral_nonneg fun ξ => mul_nonneg (h2WeightR3_pos ξ).le (sq_nonneg _)

lemma sqrt_h2WeightR3_eq (ξ : R3) :
    Real.sqrt (h2WeightR3 ξ) = 1 + dot3D ξ ξ := by
  unfold h2WeightR3
  exact Real.sqrt_sq (by linarith [dot3D_self_nonneg_r3 ξ])

/-- Sharp sub-additivity of `√(h2WeightR3 ξ) = 1 + |ξ|²`:
    `1 + |ξ + η|² ≤ 2 (1 + |ξ|²) + 2 (1 + |η|²)`. -/
lemma sqrt_h2WeightR3_add_le (ξ η : R3) :
    Real.sqrt (h2WeightR3 (ξ + η)) ≤
      2 * (Real.sqrt (h2WeightR3 ξ) + Real.sqrt (h2WeightR3 η)) := by
  rw [sqrt_h2WeightR3_eq, sqrt_h2WeightR3_eq, sqrt_h2WeightR3_eq]
  unfold dot3D
  simp only [Pi.add_apply]
  have h0 : 0 ≤ (ξ 0 - η 0) ^ 2 + (ξ 1 - η 1) ^ 2 + (ξ 2 - η 2) ^ 2 := by positivity
  linarith

lemma h2WeightR3_eq_r3Rho_pow4 (ξ : R3) :
    h2WeightR3 ξ = (r3Rho 1 ξ) ^ 4 := by
  have hsq : (r3Rho 1 ξ) ^ 2 = (ξ 0) ^ 2 + (ξ 1) ^ 2 + (ξ 2) ^ 2 + 1 ^ 2 := r3Rho_sq 1 ξ
  calc h2WeightR3 ξ = (1 + dot3D ξ ξ) ^ 2 := rfl
    _ = ((ξ 0) ^ 2 + (ξ 1) ^ 2 + (ξ 2) ^ 2 + 1 ^ 2) ^ 2 := by unfold dot3D; ring
    _ = ((r3Rho 1 ξ) ^ 2) ^ 2 := by rw [← hsq]
    _ = (r3Rho 1 ξ) ^ 4 := by ring

/-- **THEOREM 15D1-1 (Exact 3D Sobolev Weight Reciprocal Integral `∫_{ℝ³} (1 + |ξ|²)⁻² dξ = π²`):** -/
theorem r3Integral_inv_h2WeightR3 :
    Integrable (fun ξ : R3 => (h2WeightR3 ξ)⁻¹) volume ∧
    r3Integral (fun ξ : R3 => (h2WeightR3 ξ)⁻¹) = Real.pi ^ 2 := by
  have hraw := r3Integral_inv_rho_pow4 (a := 1) (by norm_num)
  have heq : (fun ξ : R3 => (h2WeightR3 ξ)⁻¹) = (fun ξ : R3 => ((r3Rho 1 ξ) ^ 4)⁻¹) :=
    funext fun ξ => by rw [h2WeightR3_eq_r3Rho_pow4]
  rw [heq]
  exact ⟨hraw.1, by rw [hraw.2, div_one]⟩

private lemma integrable_mul_of_sq_ae_15d {f g : R3 → ℝ}
    (hf_m : AEStronglyMeasurable f volume) (hg_m : AEStronglyMeasurable g volume)
    (hf2 : Integrable (fun ξ => (f ξ) ^ 2) volume)
    (hg2 : Integrable (fun ξ => (g ξ) ^ 2) volume) :
    Integrable (fun ξ => f ξ * g ξ) volume := by
  have hdom : Integrable (fun ξ => (1 / 2 : ℝ) * (f ξ) ^ 2 + (1 / 2 : ℝ) * (g ξ) ^ 2) volume :=
    (hf2.const_mul (1 / 2 : ℝ)).add (hg2.const_mul (1 / 2 : ℝ))
  refine hdom.mono' (hf_m.mul hg_m) (Filter.Eventually.of_forall fun ξ => ?_)
  rw [Real.norm_eq_abs, abs_mul]
  have hsq : 0 ≤ (|f ξ| - |g ξ|) ^ 2 := sq_nonneg _
  have h1 : |f ξ| ^ 2 = (f ξ) ^ 2 := sq_abs (f ξ)
  have h2 : |g ξ| ^ 2 = (g ξ) ^ 2 := sq_abs (g ξ)
  nlinarith

private lemma r3_cauchy_schwarz_sq_ae_15d {f g : R3 → ℝ}
    (hf_m : AEStronglyMeasurable f volume) (hg_m : AEStronglyMeasurable g volume)
    (hf2 : Integrable (fun ξ => (f ξ) ^ 2) volume)
    (hg2 : Integrable (fun ξ => (g ξ) ^ 2) volume) :
    (r3Integral (fun ξ => f ξ * g ξ)) ^ 2 ≤
      r3Integral (fun ξ => (f ξ) ^ 2) * r3Integral (fun ξ => (g ξ) ^ 2) := by
  set A : ℝ := r3Integral (fun ξ => (f ξ) ^ 2)
  set B : ℝ := r3Integral (fun ξ => f ξ * g ξ)
  set C : ℝ := r3Integral (fun ξ => (g ξ) ^ 2)
  have hfg : Integrable (fun ξ => f ξ * g ξ) volume := integrable_mul_of_sq_ae_15d hf_m hg_m hf2 hg2
  have hquad : ∀ t : ℝ, 0 ≤ A - 2 * t * B + t ^ 2 * C := by
    intro t
    have hpt : ∀ ξ : R3, (f ξ - t * g ξ) ^ 2 =
        (f ξ) ^ 2 - 2 * t * (f ξ * g ξ) + t ^ 2 * (g ξ) ^ 2 := fun ξ => by ring
    have hnn : 0 ≤ r3Integral (fun ξ => (f ξ - t * g ξ) ^ 2) :=
      r3Integral_nonneg fun ξ => sq_nonneg _
    have hsub_int : Integrable (fun ξ => (f ξ) ^ 2 - 2 * t * (f ξ * g ξ)) volume :=
      hf2.sub (hfg.const_mul (2 * t))
    rw [r3Integral_congr hpt,
        r3Integral_add hsub_int (hg2.const_mul (t ^ 2)),
        r3Integral_sub hf2 (hfg.const_mul (2 * t)),
        r3Integral_const_mul, r3Integral_const_mul] at hnn
    exact hnn
  have hC_nn : 0 ≤ C := r3Integral_nonneg fun ξ => sq_nonneg _
  by_cases hC0 : C = 0
  · have hlin : ∀ t : ℝ, 0 ≤ A - 2 * t * B := fun t => by have := hquad t; rw [hC0] at this; linarith
    have hB0 : B = 0 := by
      by_contra hne
      have := hlin ((A + 1) / (2 * B))
      have hmul : 2 * ((A + 1) / (2 * B)) * B = A + 1 := by field_simp [hne]
      linarith
    rw [hB0, hC0]; norm_num
  · have hC_pos : 0 < C := lt_of_le_of_ne hC_nn (Ne.symm hC0)
    have hval := hquad (B / C)
    have hmul := mul_nonneg hval hC_pos.le
    have hsimp : (A - 2 * (B / C) * B + (B / C) ^ 2 * C) * C = A * C - B ^ 2 := by
      field_simp [hC_pos.ne']; ring
    linarith

/-- **THEOREM 15D1-2 (Sharp Continuous Sobolev Embedding `H²(ℝ³) ↪ L¹(ℝ³)` with Exact Constant `π²`):** -/
theorem h2R3_l1_embedding {a : R3 → ℂ} (ha : InH2R3 a) :
    Integrable (fun ξ : R3 => ‖a ξ‖) volume ∧
    (r3Integral (fun ξ : R3 => ‖a ξ‖)) ^ 2 ≤ Real.pi ^ 2 * h2NormSqR3 a := by
  have hinv := r3Integral_inv_h2WeightR3
  have hf_m : AEStronglyMeasurable (fun ξ : R3 => Real.sqrt ((h2WeightR3 ξ)⁻¹)) volume :=
    (Real.continuous_sqrt.comp (h2WeightR3_continuous.inv₀ fun ξ => (h2WeightR3_pos ξ).ne')).aestronglyMeasurable
  have hg_m : AEStronglyMeasurable (fun ξ : R3 => Real.sqrt (h2WeightR3 ξ) * ‖a ξ‖) volume :=
    (Real.continuous_sqrt.comp h2WeightR3_continuous).aestronglyMeasurable.mul ha.1.norm
  have hf2 : Integrable (fun ξ : R3 => (Real.sqrt ((h2WeightR3 ξ)⁻¹)) ^ 2) volume :=
    hinv.1.congr (Filter.Eventually.of_forall fun ξ =>
      (Real.sq_sqrt (inv_nonneg.2 (h2WeightR3_pos ξ).le)).symm)
  have hg2_pt : ∀ ξ : R3, (Real.sqrt (h2WeightR3 ξ) * ‖a ξ‖) ^ 2 = h2WeightR3 ξ * ‖a ξ‖ ^ 2 :=
    fun ξ => by rw [mul_pow, Real.sq_sqrt (h2WeightR3_pos ξ).le]
  have hg2 : Integrable (fun ξ : R3 => (Real.sqrt (h2WeightR3 ξ) * ‖a ξ‖) ^ 2) volume :=
    ha.2.congr (Filter.Eventually.of_forall fun ξ => (hg2_pt ξ).symm)
  have hprod_eq : ∀ ξ : R3,
      Real.sqrt ((h2WeightR3 ξ)⁻¹) * (Real.sqrt (h2WeightR3 ξ) * ‖a ξ‖) = ‖a ξ‖ := by
    intro ξ
    have hw := h2WeightR3_pos ξ
    rw [Real.sqrt_inv, ← mul_assoc, inv_mul_cancel₀ (Real.sqrt_pos.2 hw).ne', one_mul]
  have hint_norm : Integrable (fun ξ : R3 => ‖a ξ‖) volume :=
    (integrable_mul_of_sq_ae_15d hf_m hg_m hf2 hg2).congr (Filter.Eventually.of_forall hprod_eq)
  have hcs := r3_cauchy_schwarz_sq_ae_15d hf_m hg_m hf2 hg2
  have hI1 : r3Integral (fun ξ : R3 => Real.sqrt ((h2WeightR3 ξ)⁻¹) * (Real.sqrt (h2WeightR3 ξ) * ‖a ξ‖)) =
      r3Integral (fun ξ : R3 => ‖a ξ‖) := r3Integral_congr hprod_eq
  have hI2 : r3Integral (fun ξ : R3 => (Real.sqrt ((h2WeightR3 ξ)⁻¹)) ^ 2) = Real.pi ^ 2 := by
    rw [r3Integral_congr fun ξ => Real.sq_sqrt (inv_nonneg.2 (h2WeightR3_pos ξ).le), hinv.2]
  have hI3 : r3Integral (fun ξ : R3 => (Real.sqrt (h2WeightR3 ξ) * ‖a ξ‖) ^ 2) = h2NormSqR3 a :=
    r3Integral_congr hg2_pt
  rw [hI1, hI2, hI3] at hcs
  exact ⟨hint_norm, hcs⟩

theorem h2R3_l2_integrable {a : R3 → ℂ} (ha : InH2R3 a) :
    Integrable (fun ξ : R3 => ‖a ξ‖ ^ 2) volume ∧
    r3Integral (fun ξ : R3 => ‖a ξ‖ ^ 2) ≤ h2NormSqR3 a := by
  have hint : Integrable (fun ξ : R3 => ‖a ξ‖ ^ 2) volume :=
    ha.2.mono' (ha.1.norm.pow 2) (Filter.Eventually.of_forall fun ξ => by
      rw [Real.norm_of_nonneg (sq_nonneg _)]
      calc ‖a ξ‖ ^ 2 = 1 * ‖a ξ‖ ^ 2 := (one_mul _).symm
        _ ≤ h2WeightR3 ξ * ‖a ξ‖ ^ 2 := mul_le_mul_of_nonneg_right (one_le_h2WeightR3 ξ) (sq_nonneg _))
  refine ⟨hint, ?_⟩
  unfold h2NormSqR3 r3Integral
  exact integral_mono hint ha.2 fun ξ => by
    calc ‖a ξ‖ ^ 2 = 1 * ‖a ξ‖ ^ 2 := (one_mul _).symm
      _ ≤ h2WeightR3 ξ * ‖a ξ‖ ^ 2 := mul_le_mul_of_nonneg_right (one_le_h2WeightR3 ξ) (sq_nonneg _)

theorem inH2R3_add {a b : R3 → ℂ} (ha : InH2R3 a) (hb : InH2R3 b) :
    InH2R3 (fun ξ => a ξ + b ξ) ∧
    h2NormSqR3 (fun ξ => a ξ + b ξ) ≤ 2 * h2NormSqR3 a + 2 * h2NormSqR3 b := by
  have hm : AEStronglyMeasurable (fun ξ => a ξ + b ξ) volume := ha.1.add hb.1
  have hpt : ∀ ξ : R3, h2WeightR3 ξ * ‖a ξ + b ξ‖ ^ 2 ≤
      2 * (h2WeightR3 ξ * ‖a ξ‖ ^ 2) + 2 * (h2WeightR3 ξ * ‖b ξ‖ ^ 2) := by
    intro ξ
    have htri : ‖a ξ + b ξ‖ ≤ ‖a ξ‖ + ‖b ξ‖ := norm_add_le _ _
    have hsq : ‖a ξ + b ξ‖ ^ 2 ≤ 2 * ‖a ξ‖ ^ 2 + 2 * ‖b ξ‖ ^ 2 := by
      have h1 : ‖a ξ + b ξ‖ ^ 2 ≤ (‖a ξ‖ + ‖b ξ‖) ^ 2 := by nlinarith [norm_nonneg (a ξ + b ξ)]
      nlinarith [sq_nonneg (‖a ξ‖ - ‖b ξ‖)]
    nlinarith [h2WeightR3_pos ξ]
  have hdom : Integrable (fun ξ => 2 * (h2WeightR3 ξ * ‖a ξ‖ ^ 2) + 2 * (h2WeightR3 ξ * ‖b ξ‖ ^ 2)) volume :=
    (ha.2.const_mul 2).add (hb.2.const_mul 2)
  have hint : Integrable (fun ξ => h2WeightR3 ξ * ‖a ξ + b ξ‖ ^ 2) volume :=
    hdom.mono' (h2WeightR3_continuous.aestronglyMeasurable.mul (hm.norm.pow 2))
      (Filter.Eventually.of_forall fun ξ => by
        rw [Real.norm_of_nonneg (mul_nonneg (h2WeightR3_pos ξ).le (sq_nonneg _))]
        exact hpt ξ)
  refine ⟨⟨hm, hint⟩, ?_⟩
  unfold h2NormSqR3
  have hle : r3Integral (fun ξ => h2WeightR3 ξ * ‖a ξ + b ξ‖ ^ 2) ≤
      r3Integral (fun ξ => 2 * (h2WeightR3 ξ * ‖a ξ‖ ^ 2) + 2 * (h2WeightR3 ξ * ‖b ξ‖ ^ 2)) :=
    integral_mono hint hdom hpt
  rw [r3Integral_add (ha.2.const_mul 2) (hb.2.const_mul 2),
      r3Integral_const_mul, r3Integral_const_mul] at hle
  exact hle

theorem inH2R3_sub {a b : R3 → ℂ} (ha : InH2R3 a) (hb : InH2R3 b) :
    InH2R3 (fun ξ => a ξ - b ξ) ∧
    h2NormSqR3 (fun ξ => a ξ - b ξ) ≤ 2 * h2NormSqR3 a + 2 * h2NormSqR3 b := by
  have hneg : InH2R3 (fun ξ => -b ξ) :=
    ⟨hb.1.neg, hb.2.congr (Filter.Eventually.of_forall fun ξ => by simp)⟩
  have hneg_norm : h2NormSqR3 (fun ξ => -b ξ) = h2NormSqR3 b :=
    r3Integral_congr fun ξ => by simp
  have hadd := inH2R3_add ha hneg
  rw [hneg_norm] at hadd
  simpa only [sub_eq_add_neg] using hadd

-- ----------------------------------------------------------------------------
-- ENNReal Cauchy–Schwarz & Continuous 3D Young Inequality (L¹ * L² → L²)
-- ----------------------------------------------------------------------------

private noncomputable def esqrt15d (x : ENNReal) : ENNReal := x ^ (1 / 2 : ℝ)

private lemma esqrt15d_sq (x : ENNReal) : (esqrt15d x) ^ 2 = x := by
  unfold esqrt15d; rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]; norm_num

private lemma esqrt15d_mul (x y : ENNReal) : esqrt15d (x * y) = esqrt15d x * esqrt15d y :=
  ENNReal.mul_rpow_of_nonneg x y (by norm_num)

private lemma esqrt15d_ofReal {x : ℝ} (hx : 0 ≤ x) :
    esqrt15d (ENNReal.ofReal x) = ENNReal.ofReal (Real.sqrt x) := by
  unfold esqrt15d; rw [Real.sqrt_eq_rpow, ENNReal.ofReal_rpow_of_nonneg hx (by norm_num)]

private lemma esqrt15d_zero : esqrt15d 0 = 0 := by
  unfold esqrt15d; rw [ENNReal.zero_rpow_of_pos (by norm_num)]

private lemma esqrt15d_top : esqrt15d ⊤ = ⊤ := by
  unfold esqrt15d; rw [ENNReal.top_rpow_of_pos (by norm_num)]

private lemma ennreal_amgm_15d (a b c : ENNReal) (hc0 : c ≠ 0) (hctop : c ≠ ⊤) :
    2 * (a * b) ≤ c * a ^ 2 + c⁻¹ * b ^ 2 := by
  by_cases ha : a = ⊤
  · subst ha
    have : c * (⊤ : ENNReal) ^ 2 = ⊤ := by rw [sq, ENNReal.top_mul_top, ENNReal.mul_top hc0]
    rw [this, top_add]; exact le_top
  by_cases hb : b = ⊤
  · subst hb
    have hci : c⁻¹ ≠ 0 := ENNReal.inv_ne_zero.2 hctop
    have : c⁻¹ * (⊤ : ENNReal) ^ 2 = ⊤ := by rw [sq, ENNReal.top_mul_top, ENNReal.mul_top hci]
    rw [this, add_top]; exact le_top
  lift a to NNReal using ha
  lift b to NNReal using hb
  lift c to NNReal using hctop
  have hc_pos : (0 : ℝ) < (c : ℝ) := by
    have : c ≠ 0 := fun h => hc0 (by exact_mod_cast h)
    exact_mod_cast pos_iff_ne_zero.2 this
  have hreal : (2 : ℝ) * ((a : ℝ) * (b : ℝ)) ≤ (c : ℝ) * (a : ℝ) ^ 2 + (c : ℝ)⁻¹ * (b : ℝ) ^ 2 := by
    have hsq : 0 ≤ (Real.sqrt (c : ℝ) * (a : ℝ) - (b : ℝ) / Real.sqrt (c : ℝ)) ^ 2 := sq_nonneg _
    have hs : (Real.sqrt (c : ℝ)) ^ 2 = (c : ℝ) := Real.sq_sqrt hc_pos.le
    have hspos : 0 < Real.sqrt (c : ℝ) := Real.sqrt_pos.2 hc_pos
    have hexp : (Real.sqrt (c : ℝ) * (a : ℝ) - (b : ℝ) / Real.sqrt (c : ℝ)) ^ 2 =
        (c : ℝ) * (a : ℝ) ^ 2 + (c : ℝ)⁻¹ * (b : ℝ) ^ 2 - 2 * ((a : ℝ) * (b : ℝ)) := by
      rw [sub_sq, mul_pow, div_pow, hs]
      have hmid : 2 * (Real.sqrt (c : ℝ) * (a : ℝ)) * ((b : ℝ) / Real.sqrt (c : ℝ)) =
          2 * ((a : ℝ) * (b : ℝ)) := by field_simp [hspos.ne']
      rw [hmid, div_eq_mul_inv]; ring
    linarith
  have h1 : (2 * ((a : ENNReal) * b)) = ENNReal.ofReal (2 * ((a : ℝ) * (b : ℝ))) := by
    rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_mul (NNReal.coe_nonneg a),
        ENNReal.ofReal_coe_nnreal, ENNReal.ofReal_coe_nnreal]; norm_num
  have h2 : ((c : ENNReal) * (a : ENNReal) ^ 2 + (c : ENNReal)⁻¹ * (b : ENNReal) ^ 2) =
      ENNReal.ofReal ((c : ℝ) * (a : ℝ) ^ 2 + (c : ℝ)⁻¹ * (b : ℝ) ^ 2) := by
    rw [ENNReal.ofReal_add (by positivity) (by positivity),
        ENNReal.ofReal_mul (NNReal.coe_nonneg c), ENNReal.ofReal_mul (by positivity),
        ENNReal.ofReal_pow (NNReal.coe_nonneg a), ENNReal.ofReal_pow (NNReal.coe_nonneg b),
        ENNReal.ofReal_inv_of_pos hc_pos,
        ENNReal.ofReal_coe_nnreal, ENNReal.ofReal_coe_nnreal, ENNReal.ofReal_coe_nnreal]
  rw [h1, h2]
  exact ENNReal.ofReal_le_ofReal hreal

private lemma lintegral_cs_esqrt_15d {α : Type*} [MeasurableSpace α] (μ : Measure α)
    {F G : α → ENNReal} (hF : AEMeasurable F μ) (hG : AEMeasurable G μ) :
    ∫⁻ x, esqrt15d (F x) * esqrt15d (G x) ∂μ ≤ esqrt15d (∫⁻ x, F x ∂μ) * esqrt15d (∫⁻ x, G x ∂μ) := by
  set IF : ENNReal := ∫⁻ x, F x ∂μ
  set IG : ENNReal := ∫⁻ x, G x ∂μ
  by_cases hIF0 : IF = 0
  · have hae : ∀ᵐ x ∂μ, F x = 0 := (lintegral_eq_zero_iff' hF).1 hIF0
    have h0 : ∫⁻ x, esqrt15d (F x) * esqrt15d (G x) ∂μ = 0 := by
      rw [lintegral_congr_ae (hae.mono fun x hx => by rw [hx, esqrt15d_zero, zero_mul]), lintegral_zero]
    rw [h0]; exact bot_le
  by_cases hIG0 : IG = 0
  · have hae : ∀ᵐ x ∂μ, G x = 0 := (lintegral_eq_zero_iff' hG).1 hIG0
    have h0 : ∫⁻ x, esqrt15d (F x) * esqrt15d (G x) ∂μ = 0 := by
      rw [lintegral_congr_ae (hae.mono fun x hx => by rw [hx, esqrt15d_zero, mul_zero]), lintegral_zero]
    rw [h0]; exact bot_le
  by_cases hIFtop : IF = ⊤
  · rw [hIFtop, esqrt15d_top, ENNReal.top_mul]
    · exact le_top
    · intro h; apply hIG0
      have := congrArg (fun z => z ^ 2) h; rwa [esqrt15d_sq, zero_pow (by norm_num)] at this
  by_cases hIGtop : IG = ⊤
  · rw [hIGtop, esqrt15d_top, ENNReal.mul_top]
    · exact le_top
    · intro h; apply hIF0
      have := congrArg (fun z => z ^ 2) h; rwa [esqrt15d_sq, zero_pow (by norm_num)] at this
  have hIF_pos : 0 < IF.toReal := ENNReal.toReal_pos hIF0 hIFtop
  have hIG_pos : 0 < IG.toReal := ENNReal.toReal_pos hIG0 hIGtop
  set c_r : ℝ := Real.sqrt (IG.toReal / IF.toReal)
  have hcr_pos : 0 < c_r := Real.sqrt_pos.2 (div_pos hIG_pos hIF_pos)
  set c : ENNReal := ENNReal.ofReal c_r
  have hc0 : c ≠ 0 := (ENNReal.ofReal_pos.2 hcr_pos).ne'
  have hctop : c ≠ ⊤ := ENNReal.ofReal_ne_top
  have h2le : 2 * ∫⁻ x, esqrt15d (F x) * esqrt15d (G x) ∂μ ≤ c * IF + c⁻¹ * IG := by
    rw [← lintegral_const_mul' 2 _ (by norm_num)]
    calc ∫⁻ x, 2 * (esqrt15d (F x) * esqrt15d (G x)) ∂μ
        ≤ ∫⁻ x, (c * (esqrt15d (F x)) ^ 2 + c⁻¹ * (esqrt15d (G x)) ^ 2) ∂μ :=
          lintegral_mono fun x => ennreal_amgm_15d (esqrt15d (F x)) (esqrt15d (G x)) c hc0 hctop
      _ = ∫⁻ x, (c * F x + c⁻¹ * G x) ∂μ := by simp_rw [esqrt15d_sq]
      _ = (∫⁻ x, c * F x ∂μ) + (∫⁻ x, c⁻¹ * G x ∂μ) := lintegral_add_left' (hF.const_mul c) _
      _ = c * IF + c⁻¹ * IG := by
          rw [lintegral_const_mul' c _ hctop, lintegral_const_mul' c⁻¹ _ (ENNReal.inv_ne_top.2 hc0)]
  have hrhs_eq : c * IF + c⁻¹ * IG = 2 * (esqrt15d IF * esqrt15d IG) := by
    have hIF_eq : IF = ENNReal.ofReal IF.toReal := (ENNReal.ofReal_toReal hIFtop).symm
    have hIG_eq : IG = ENNReal.ofReal IG.toReal := (ENNReal.ofReal_toReal hIGtop).symm
    have hreal : c_r * IF.toReal + c_r⁻¹ * IG.toReal =
        2 * (Real.sqrt IF.toReal * Real.sqrt IG.toReal) := by
      dsimp only [c_r]; rw [Real.sqrt_div hIG_pos.le]
      have hsF : 0 < Real.sqrt IF.toReal := Real.sqrt_pos.2 hIF_pos
      have hsG : 0 < Real.sqrt IG.toReal := Real.sqrt_pos.2 hIG_pos
      field_simp [hsF.ne', hsG.ne']
      nlinarith [Real.sq_sqrt hIF_pos.le, Real.sq_sqrt hIG_pos.le]
    rw [hIF_eq, hIG_eq, esqrt15d_ofReal hIF_pos.le, esqrt15d_ofReal hIG_pos.le]
    dsimp only [c]
    rw [← ENNReal.ofReal_inv_of_pos hcr_pos, ← ENNReal.ofReal_mul hcr_pos.le,
        ← ENNReal.ofReal_mul (inv_nonneg.2 hcr_pos.le),
        ← ENNReal.ofReal_add (by positivity) (by positivity),
        hreal, ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_mul (Real.sqrt_nonneg _)]
    norm_num
  rw [hrhs_eq] at h2le
  exact (ENNReal.mul_le_mul_iff_right (by norm_num : (2 : ENNReal) ≠ 0) (by norm_num : (2 : ENNReal) ≠ ⊤)).1 h2le

/-- **THEOREM 15D1-3 (Continuous 3D Young's Convolution Inequality `L¹(ℝ³) * L²(ℝ³) → L²(ℝ³)`):**
    For any measurable nonnegative `f ∈ L¹(ℝ³)` and `g ∈ L²(ℝ³)`:
    `∫_{ℝ³} (∫_{ℝ³} f(η) g(ξ - η) dη)² dξ ≤ (∫_{ℝ³} f)² · (∫_{ℝ³} g²)`. -/
theorem young_l1_l2_r3 {f g : R3 → ℝ}
    (hf_m : AEStronglyMeasurable f volume) (hg_m : AEStronglyMeasurable g volume)
    (hf_nn : ∀ η, 0 ≤ f η) (hg_nn : ∀ ζ, 0 ≤ g ζ)
    (hf_int : Integrable f volume) (hg2_int : Integrable (fun ζ => (g ζ) ^ 2) volume) :
    AEStronglyMeasurable (fun ξ : R3 => ∫ η : R3, f η * g (ξ - η)) volume ∧
    Integrable (fun ξ : R3 => (∫ η : R3, f η * g (ξ - η)) ^ 2) volume ∧
    r3Integral (fun ξ : R3 => (∫ η : R3, f η * g (ξ - η)) ^ 2) ≤
      (r3Integral f) ^ 2 * r3Integral (fun ζ : R3 => (g ζ) ^ 2) := by
  -- Nonnegative strongly measurable representatives fm =ᵐ f and gm =ᵐ g
  let fm : R3 → ℝ := fun η => max 0 (hf_m.mk f η)
  let gm : R3 → ℝ := fun ζ => max 0 (hg_m.mk g ζ)
  have hfm_sm : StronglyMeasurable fm := stronglyMeasurable_const.sup hf_m.stronglyMeasurable_mk
  have hgm_sm : StronglyMeasurable gm := stronglyMeasurable_const.sup hg_m.stronglyMeasurable_mk
  have hfm_nn : ∀ η, 0 ≤ fm η := fun η => le_max_left 0 _
  have hgm_nn : ∀ ζ, 0 ≤ gm ζ := fun ζ => le_max_left 0 _
  have hfm_ae : f =ᵐ[volume] fm := hf_m.ae_eq_mk.mono fun η hη => by
    dsimp only [fm]; rw [← hη, max_eq_right (hf_nn η)]
  have hgm_ae : g =ᵐ[volume] gm := hg_m.ae_eq_mk.mono fun ζ hζ => by
    dsimp only [gm]; rw [← hζ, max_eq_right (hg_nn ζ)]
  -- Pointwise equality of convolution integrals for EVERY ξ ∈ ℝ³
  have hconv_eq : ∀ ξ : R3, (∫ η : R3, f η * g (ξ - η)) = ∫ η : R3, fm η * gm (ξ - η) := by
    intro ξ
    have hshift : (fun η : R3 => g (ξ - η)) =ᵐ[volume] (fun η : R3 => gm (ξ - η)) :=
      (Measure.measurePreserving_sub_left (volume : Measure R3) ξ).quasiMeasurePreserving.ae_eq_comp hgm_ae
    exact integral_congr_ae (hfm_ae.mul hshift)
  have hprod_sm : StronglyMeasurable (fun p : R3 × R3 => fm p.2 * gm (p.1 - p.2)) :=
    (hfm_sm.comp_measurable measurable_snd).mul
      (hgm_sm.comp_measurable (measurable_fst.sub measurable_snd))
  have hconv_sm : StronglyMeasurable (fun ξ : R3 => ∫ η : R3, fm η * gm (ξ - η)) :=
    hprod_sm.integral_prod_right'
  have hconv_aem : AEStronglyMeasurable (fun ξ : R3 => ∫ η : R3, f η * g (ξ - η)) volume :=
    hconv_sm.aestronglyMeasurable.congr (Filter.Eventually.of_forall fun ξ => (hconv_eq ξ).symm)
  -- ENNReal Young bound on lintegrals
  let F : R3 → ENNReal := fun η => ENNReal.ofReal (fm η)
  let G : R3 → ENNReal := fun ζ => ENNReal.ofReal (gm ζ)
  have hF_meas : Measurable F := ENNReal.continuous_ofReal.measurable.comp hfm_sm.measurable
  have hG_meas : Measurable G := ENNReal.continuous_ofReal.measurable.comp hgm_sm.measurable
  have hIF : (∫⁻ η : R3, F η) = ENNReal.ofReal (r3Integral f) := by
    unfold r3Integral
    rw [integral_congr_ae hfm_ae,
        ofReal_integral_eq_lintegral_ofReal (hf_int.congr hfm_ae) (Filter.Eventually.of_forall hfm_nn)]
  have hIG2 : (∫⁻ ζ : R3, (G ζ) ^ 2) = ENNReal.ofReal (r3Integral (fun ζ => (g ζ) ^ 2)) := by
    unfold r3Integral
    have hsq_ae : (fun ζ => (g ζ) ^ 2) =ᵐ[volume] (fun ζ => (gm ζ) ^ 2) :=
      hgm_ae.mono fun ζ hζ => by dsimp only; rw [hζ]
    rw [integral_congr_ae hsq_ae,
        ofReal_integral_eq_lintegral_ofReal (hg2_int.congr hsq_ae) (Filter.Eventually.of_forall fun ζ => sq_nonneg _)]
    refine lintegral_congr fun ζ => ?_
    dsimp only [G]; rw [ENNReal.ofReal_pow (hgm_nn ζ)]
  have hpt_sq : ∀ ξ : R3,
      ENNReal.ofReal ((∫ η : R3, fm η * gm (ξ - η)) ^ 2) ≤
        (∫⁻ η : R3, F η) * (∫⁻ η : R3, F η * (G (ξ - η)) ^ 2) := by
    intro ξ
    have hnn_int : 0 ≤ ∫ η : R3, fm η * gm (ξ - η) :=
      integral_nonneg fun η => mul_nonneg (hfm_nn η) (hgm_nn _)
    have h1 : ENNReal.ofReal (∫ η : R3, fm η * gm (ξ - η)) ≤ ∫⁻ η : R3, F η * G (ξ - η) := by
      by_cases hint : Integrable (fun η : R3 => fm η * gm (ξ - η)) volume
      · rw [ofReal_integral_eq_lintegral_ofReal hint
          (Filter.Eventually.of_forall fun η => mul_nonneg (hfm_nn η) (hgm_nn _))]
        refine le_of_eq (lintegral_congr fun η => ?_)
        dsimp only [F, G]; exact ENNReal.ofReal_mul (hfm_nn η)
      · rw [integral_undef hint, ENNReal.ofReal_zero]; exact bot_le
    have hcs : (∫⁻ η : R3, F η * G (ξ - η)) ≤
        esqrt15d (∫⁻ η : R3, F η) * esqrt15d (∫⁻ η : R3, F η * (G (ξ - η)) ^ 2) := by
      have hrew : ∀ η : R3, F η * G (ξ - η) = esqrt15d (F η) * esqrt15d (F η * (G (ξ - η)) ^ 2) := by
        intro η
        rw [esqrt15d_mul, ← mul_assoc, ← sq, esqrt15d_sq]
        congr 1
        unfold esqrt15d; rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]; norm_num
      simp_rw [hrew]
      have hG2_m : Measurable (fun η : R3 => F η * (G (ξ - η)) ^ 2) :=
        hF_meas.mul ((hG_meas.comp (measurable_const.sub measurable_id)).pow_const 2)
      exact lintegral_cs_esqrt_15d volume hF_meas.aemeasurable hG2_m.aemeasurable
    have hle := le_trans h1 hcs
    rw [ENNReal.ofReal_pow hnn_int]
    calc (ENNReal.ofReal (∫ η : R3, fm η * gm (ξ - η))) ^ 2
        ≤ (esqrt15d (∫⁻ η : R3, F η) * esqrt15d (∫⁻ η : R3, F η * (G (ξ - η)) ^ 2)) ^ 2 :=
          pow_le_pow_left' hle 2
      _ = (esqrt15d (∫⁻ η : R3, F η)) ^ 2 * (esqrt15d (∫⁻ η : R3, F η * (G (ξ - η)) ^ 2)) ^ 2 :=
          mul_pow _ _ 2
      _ = (∫⁻ η : R3, F η) * (∫⁻ η : R3, F η * (G (ξ - η)) ^ 2) := by rw [esqrt15d_sq, esqrt15d_sq]
  have hlint_bound : (∫⁻ ξ : R3, ENNReal.ofReal ((∫ η : R3, fm η * gm (ξ - η)) ^ 2)) ≤
      ENNReal.ofReal ((r3Integral f) ^ 2 * r3Integral (fun ζ => (g ζ) ^ 2)) := by
    have hIF_ne_top : (∫⁻ η : R3, F η) ≠ ⊤ := by rw [hIF]; exact ENNReal.ofReal_ne_top
    have hprod_m : AEMeasurable (fun p : R3 × R3 => F p.2 * (G (p.1 - p.2)) ^ 2) (volume.prod volume) :=
      ((hF_meas.comp measurable_snd).mul
        ((hG_meas.comp (measurable_fst.sub measurable_snd)).pow_const 2)).aemeasurable
    have hton : (∫⁻ ξ : R3, ∫⁻ η : R3, F η * (G (ξ - η)) ^ 2) =
        (∫⁻ η : R3, F η) * (∫⁻ ζ : R3, (G ζ) ^ 2) := by
      rw [← lintegral_prod (fun p : R3 × R3 => F p.2 * (G (p.1 - p.2)) ^ 2) hprod_m,
          lintegral_prod_symm (fun p : R3 × R3 => F p.2 * (G (p.1 - p.2)) ^ 2) hprod_m]
      have hinner : ∀ η : R3, (∫⁻ ξ : R3, F η * (G (ξ - η)) ^ 2) = F η * (∫⁻ ζ : R3, (G ζ) ^ 2) := by
        intro η
        have hFη_top : F η ≠ ⊤ := ENNReal.ofReal_ne_top
        rw [lintegral_const_mul' (F η) (fun ξ : R3 => (G (ξ - η)) ^ 2) hFη_top,
            lintegral_sub_right_eq_self (fun ζ : R3 => (G ζ) ^ 2) η]
      simp_rw [hinner]
      exact lintegral_mul_const _ hF_meas
    calc (∫⁻ ξ : R3, ENNReal.ofReal ((∫ η : R3, fm η * gm (ξ - η)) ^ 2))
        ≤ ∫⁻ ξ : R3, (∫⁻ η : R3, F η) * (∫⁻ η : R3, F η * (G (ξ - η)) ^ 2) :=
          lintegral_mono hpt_sq
      _ = (∫⁻ η : R3, F η) * (∫⁻ ξ : R3, ∫⁻ η : R3, F η * (G (ξ - η)) ^ 2) :=
          lintegral_const_mul' _ _ hIF_ne_top
      _ = (∫⁻ η : R3, F η) * ((∫⁻ η : R3, F η) * (∫⁻ ζ : R3, (G ζ) ^ 2)) := by rw [hton]
      _ = ((∫⁻ η : R3, F η) ^ 2) * (∫⁻ ζ : R3, (G ζ) ^ 2) := by ring
      _ = ENNReal.ofReal ((r3Integral f) ^ 2 * r3Integral (fun ζ => (g ζ) ^ 2)) := by
          rw [hIF, hIG2, ← ENNReal.ofReal_pow (r3Integral_nonneg hf_nn),
              ← ENNReal.ofReal_mul (sq_nonneg _)]
  have hsq_int : Integrable (fun ξ : R3 => (∫ η : R3, f η * g (ξ - η)) ^ 2) volume := by
    refine ⟨hconv_aem.pow 2, ?_⟩
    change (∫⁻ ξ : R3, ‖(∫ η : R3, f η * g (ξ - η)) ^ 2‖ₑ) < ⊤
    have heq : (fun ξ : R3 => ‖(∫ η : R3, f η * g (ξ - η)) ^ 2‖ₑ) =
        (fun ξ : R3 => ENNReal.ofReal ((∫ η : R3, fm η * gm (ξ - η)) ^ 2)) := by
      funext ξ; rw [← ofReal_norm, Real.norm_of_nonneg (sq_nonneg _), hconv_eq ξ]
    rw [heq]; exact lt_of_le_of_lt hlint_bound ENNReal.ofReal_lt_top
  have hreal_le : r3Integral (fun ξ : R3 => (∫ η : R3, f η * g (ξ - η)) ^ 2) ≤
      (r3Integral f) ^ 2 * r3Integral (fun ζ : R3 => (g ζ) ^ 2) := by
    have h1 := ofReal_integral_eq_lintegral_ofReal hsq_int (Filter.Eventually.of_forall fun ξ => sq_nonneg _)
    have h2 : ENNReal.ofReal (r3Integral (fun ξ : R3 => (∫ η : R3, f η * g (ξ - η)) ^ 2)) ≤
        ENNReal.ofReal ((r3Integral f) ^ 2 * r3Integral (fun ζ => (g ζ) ^ 2)) := by
      unfold r3Integral at *
      rw [h1]
      simpa only [hconv_eq] using hlint_bound
    exact (ENNReal.ofReal_le_ofReal_iff (mul_nonneg (sq_nonneg _) (r3Integral_nonneg fun ζ => sq_nonneg _))).1 h2
  exact ⟨hconv_aem, hsq_int, hreal_le⟩

/-- Continuous 3D Fourier convolution `(a * b)(ξ) = ∫_{ℝ³} a(η) b(ξ - η) dη`. -/
noncomputable def convR3 (a b : R3 → ℂ) (ξ : R3) : ℂ :=
  ∫ η : R3, a η * b (ξ - η)

lemma convR3_integrable_at {a b : R3 → ℂ} (ha : InH2R3 a) (hb : InH2R3 b) (ξ : R3) :
    Integrable (fun η : R3 => a η * b (ξ - η)) volume := by
  have ha2 := (h2R3_l2_integrable ha).1
  have hb2 := (h2R3_l2_integrable hb).1
  have hb_shift_m : AEStronglyMeasurable (fun η : R3 => b (ξ - η)) volume :=
    hb.1.comp_quasiMeasurePreserving (Measure.measurePreserving_sub_left (volume : Measure R3) ξ).quasiMeasurePreserving
  have hb2_shift : Integrable (fun η : R3 => ‖b (ξ - η)‖ ^ 2) volume :=
    hb2.comp_sub_left ξ
  have hnorm_int : Integrable (fun η : R3 => ‖a η‖ * ‖b (ξ - η)‖) volume :=
    integrable_mul_of_sq_ae_15d ha.1.norm hb_shift_m.norm ha2 hb2_shift
  exact hnorm_int.mono' (ha.1.mul hb_shift_m) (Filter.Eventually.of_forall fun η => by
    rw [norm_mul])

theorem convR3_sub_left {a₁ a₂ b : R3 → ℂ} (ha₁ : InH2R3 a₁) (ha₂ : InH2R3 a₂) (hb : InH2R3 b) (ξ : R3) :
    convR3 (fun η => a₁ η - a₂ η) b ξ = convR3 a₁ b ξ - convR3 a₂ b ξ := by
  unfold convR3
  have hpt : (fun η : R3 => (a₁ η - a₂ η) * b (ξ - η)) =
      (fun η : R3 => a₁ η * b (ξ - η) - a₂ η * b (ξ - η)) := funext fun η => sub_mul _ _ _
  rw [hpt, integral_sub (convR3_integrable_at ha₁ hb ξ) (convR3_integrable_at ha₂ hb ξ)]

theorem convR3_sub_right {a b₁ b₂ : R3 → ℂ} (ha : InH2R3 a) (hb₁ : InH2R3 b₁) (hb₂ : InH2R3 b₂) (ξ : R3) :
    convR3 a (fun η => b₁ η - b₂ η) ξ = convR3 a b₁ ξ - convR3 a b₂ ξ := by
  unfold convR3
  have hpt : (fun η : R3 => a η * (b₁ (ξ - η) - b₂ (ξ - η))) =
      (fun η : R3 => a η * b₁ (ξ - η) - a η * b₂ (ξ - η)) := funext fun η => mul_sub _ _ _
  rw [hpt, integral_sub (convR3_integrable_at ha hb₁ ξ) (convR3_integrable_at ha hb₂ ξ)]

theorem convR3_conj_symm {a b : R3 → ℂ} (_ha : InH2R3 a) (_hb : InH2R3 b)
    (hsa : ∀ η, starRingEnd ℂ (a η) = a (-η))
    (hsb : ∀ η, starRingEnd ℂ (b η) = b (-η)) (ξ : R3) :
    starRingEnd ℂ (convR3 a b ξ) = convR3 a b (-ξ) := by
  unfold convR3
  have h1 := (Complex.conjCLE.integral_comp_comm (μ := volume) (fun η : R3 => a η * b (ξ - η))).symm
  change starRingEnd ℂ (∫ η : R3, a η * b (ξ - η)) = ∫ η : R3, starRingEnd ℂ (a η * b (ξ - η)) at h1
  rw [h1]
  have h2 : (fun η : R3 => starRingEnd ℂ (a η * b (ξ - η))) =
      (fun η : R3 => a (-η) * b (-ξ - (-η))) := by
    funext η
    rw [map_mul, hsa η, hsb (ξ - η)]
    congr 2; abel
  rw [h2]
  exact integral_neg_eq_self (fun η : R3 => a η * b (-ξ - η)) volume

/-- **THEOREM 15D1-4 (`H²(ℝ³)` Tame Moser–Wiener & Convolution Banach Algebra Theorem):**
    For ALL `a, b ∈ InH2R3`:
    1. `InH2R3 (convR3 a b)`;
    2. **Tame Moser–Wiener estimate:**
       `h2NormSqR3 (convR3 a b) ≤ 8 (‖b‖_{L¹}² h2NormSqR3 a + ‖a‖_{L¹}² h2NormSqR3 b)`;
    3. **Banach Algebra Bound:** `h2NormSqR3 (convR3 a b) ≤ 16 π² · h2NormSqR3 a · h2NormSqR3 b`. -/
theorem convR3_tame_and_banach_algebra {a b : R3 → ℂ} (ha : InH2R3 a) (hb : InH2R3 b) :
    InH2R3 (convR3 a b) ∧
    h2NormSqR3 (convR3 a b) ≤
      8 * ((r3Integral (fun ξ => ‖b ξ‖)) ^ 2 * h2NormSqR3 a +
           (r3Integral (fun ξ => ‖a ξ‖)) ^ 2 * h2NormSqR3 b) ∧
    h2NormSqR3 (convR3 a b) ≤ 16 * Real.pi ^ 2 * h2NormSqR3 a * h2NormSqR3 b := by
  -- Measurability of convR3 a b via strongly measurable representatives
  let am : R3 → ℂ := ha.1.mk a
  let bm : R3 → ℂ := hb.1.mk b
  have hconv_eq : ∀ ξ : R3, convR3 a b ξ = ∫ η : R3, am η * bm (ξ - η) := fun ξ =>
    integral_congr_ae (ha.1.ae_eq_mk.mul
      ((Measure.measurePreserving_sub_left (volume : Measure R3) ξ).quasiMeasurePreserving.ae_eq_comp hb.1.ae_eq_mk))
  have hprod_sm : StronglyMeasurable (fun p : R3 × R3 => am p.2 * bm (p.1 - p.2)) :=
    (ha.1.stronglyMeasurable_mk.comp_measurable measurable_snd).mul
      (hb.1.stronglyMeasurable_mk.comp_measurable (measurable_fst.sub measurable_snd))
  have hconv_aem : AEStronglyMeasurable (convR3 a b) volume :=
    hprod_sm.integral_prod_right'.aestronglyMeasurable.congr
      (Filter.Eventually.of_forall fun ξ => (hconv_eq ξ).symm)
  -- Prepare L¹ and weighted L² pieces for Young's inequality
  have hal1 := h2R3_l1_embedding ha
  have hbl1 := h2R3_l1_embedding hb
  let wa : R3 → ℝ := fun ξ => Real.sqrt (h2WeightR3 ξ) * ‖a ξ‖
  let wb : R3 → ℝ := fun ξ => Real.sqrt (h2WeightR3 ξ) * ‖b ξ‖
  have hwa_m : AEStronglyMeasurable wa volume :=
    (Real.continuous_sqrt.comp h2WeightR3_continuous).aestronglyMeasurable.mul ha.1.norm
  have hwb_m : AEStronglyMeasurable wb volume :=
    (Real.continuous_sqrt.comp h2WeightR3_continuous).aestronglyMeasurable.mul hb.1.norm
  have hwa2 : Integrable (fun ξ => (wa ξ) ^ 2) volume :=
    ha.2.congr (Filter.Eventually.of_forall fun ξ => by
      dsimp only [wa]; rw [mul_pow, Real.sq_sqrt (h2WeightR3_pos ξ).le])
  have hwb2 : Integrable (fun ξ => (wb ξ) ^ 2) volume :=
    hb.2.congr (Filter.Eventually.of_forall fun ξ => by
      dsimp only [wb]; rw [mul_pow, Real.sq_sqrt (h2WeightR3_pos ξ).le])
  have hwa2_eq : r3Integral (fun ξ => (wa ξ) ^ 2) = h2NormSqR3 a :=
    r3Integral_congr fun ξ => by dsimp only [wa]; rw [mul_pow, Real.sq_sqrt (h2WeightR3_pos ξ).le]
  have hwb2_eq : r3Integral (fun ξ => (wb ξ) ^ 2) = h2NormSqR3 b :=
    r3Integral_congr fun ξ => by dsimp only [wb]; rw [mul_pow, Real.sq_sqrt (h2WeightR3_pos ξ).le]
  -- Young Term 1: ∫ |b(η)| * wa(ξ - η) dη   (using change of variables η ↦ ξ - η!)
  have hy1 := young_l1_l2_r3 hb.1.norm hwa_m (fun _ => norm_nonneg _)
    (fun _ => mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _)) hbl1.1 hwa2
  -- Young Term 2: ∫ |a(η)| * wb(ξ - η) dη
  have hy2 := young_l1_l2_r3 ha.1.norm hwb_m (fun _ => norm_nonneg _)
    (fun _ => mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _)) hal1.1 hwb2
  -- Pointwise domination: h2WeightR3 ξ * ‖convR3 a b ξ‖² ≤ 8 * (I1 ξ)² + 8 * (I2 ξ)²
  have hpt : ∀ ξ : R3, h2WeightR3 ξ * ‖convR3 a b ξ‖ ^ 2 ≤
      8 * (∫ η : R3, ‖b η‖ * wa (ξ - η)) ^ 2 + 8 * (∫ η : R3, ‖a η‖ * wb (ξ - η)) ^ 2 := by
    intro ξ
    have hnorm_le : Real.sqrt (h2WeightR3 ξ) * ‖convR3 a b ξ‖ ≤
        ∫ η : R3, Real.sqrt (h2WeightR3 ξ) * (‖a η‖ * ‖b (ξ - η)‖) := by
      rw [integral_const_mul]
      refine mul_le_mul_of_nonneg_left ?_ (Real.sqrt_nonneg _)
      unfold convR3
      calc ‖∫ η : R3, a η * b (ξ - η)‖
          ≤ ∫ η : R3, ‖a η * b (ξ - η)‖ := norm_integral_le_integral_norm _
        _ = ∫ η : R3, ‖a η‖ * ‖b (ξ - η)‖ := integral_congr_ae (Filter.Eventually.of_forall fun η => norm_mul _ _)
    have hterm1_int : Integrable (fun η : R3 => wa η * ‖b (ξ - η)‖) volume := by
      have h1 : Integrable (fun η : R3 => ‖b (ξ - η)‖ ^ 2) volume :=
        (h2R3_l2_integrable hb).1.comp_sub_left ξ
      have hbm : AEStronglyMeasurable (fun η : R3 => ‖b (ξ - η)‖) volume :=
        hb.1.norm.comp_quasiMeasurePreserving (Measure.measurePreserving_sub_left (volume : Measure R3) ξ).quasiMeasurePreserving
      exact integrable_mul_of_sq_ae_15d hwa_m hbm hwa2 h1
    have hterm2_int : Integrable (fun η : R3 => ‖a η‖ * wb (ξ - η)) volume := by
      have h1 : Integrable (fun η : R3 => (wb (ξ - η)) ^ 2) volume := hwb2.comp_sub_left ξ
      have hwbm : AEStronglyMeasurable (fun η : R3 => wb (ξ - η)) volume :=
        hwb_m.comp_quasiMeasurePreserving (Measure.measurePreserving_sub_left (volume : Measure R3) ξ).quasiMeasurePreserving
      exact integrable_mul_of_sq_ae_15d ha.1.norm hwbm (h2R3_l2_integrable ha).1 h1
    have hprod_int : Integrable (fun η : R3 => Real.sqrt (h2WeightR3 ξ) * (‖a η‖ * ‖b (ξ - η)‖)) volume :=
      ((convR3_integrable_at ha hb ξ).norm.congr (Filter.Eventually.of_forall fun η => norm_mul _ _)).const_mul _
    have hsub_pt : ∀ η : R3, Real.sqrt (h2WeightR3 ξ) * (‖a η‖ * ‖b (ξ - η)‖) ≤
        2 * (wa η * ‖b (ξ - η)‖) + 2 * (‖a η‖ * wb (ξ - η)) := by
      intro η
      have hsub := sqrt_h2WeightR3_add_le η (ξ - η)
      rw [add_sub_cancel] at hsub
      have hnn : 0 ≤ ‖a η‖ * ‖b (ξ - η)‖ := mul_nonneg (norm_nonneg _) (norm_nonneg _)
      have hmul := mul_le_mul_of_nonneg_right hsub hnn
      dsimp only [wa, wb]; linarith
    have hint_le : (∫ η : R3, Real.sqrt (h2WeightR3 ξ) * (‖a η‖ * ‖b (ξ - η)‖)) ≤
        2 * (∫ η : R3, wa η * ‖b (ξ - η)‖) + 2 * (∫ η : R3, ‖a η‖ * wb (ξ - η)) := by
      have hsum_int : Integrable (fun η : R3 => 2 * (wa η * ‖b (ξ - η)‖) + 2 * (‖a η‖ * wb (ξ - η))) volume :=
        (hterm1_int.const_mul 2).add (hterm2_int.const_mul 2)
      have h1 := integral_mono hprod_int hsum_int hsub_pt
      rw [integral_add (hterm1_int.const_mul 2) (hterm2_int.const_mul 2),
          integral_const_mul 2, integral_const_mul 2] at h1
      exact h1
    have hswap1 : (∫ η : R3, wa η * ‖b (ξ - η)‖) = ∫ η : R3, ‖b η‖ * wa (ξ - η) := by
      have h1 := integral_sub_left_eq_self (fun η : R3 => ‖b η‖ * wa (ξ - η)) volume ξ
      rw [← h1]
      refine integral_congr_ae (Filter.Eventually.of_forall fun η => ?_)
      dsimp only; rw [sub_sub_cancel]; ring
    rw [hswap1] at hint_le
    have hcomb := le_trans hnorm_le hint_le
    have hL_nn : 0 ≤ Real.sqrt (h2WeightR3 ξ) * ‖convR3 a b ξ‖ := mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _)
    have hsq_le : (Real.sqrt (h2WeightR3 ξ) * ‖convR3 a b ξ‖) ^ 2 ≤
        (2 * (∫ η : R3, ‖b η‖ * wa (ξ - η)) + 2 * (∫ η : R3, ‖a η‖ * wb (ξ - η))) ^ 2 := by
      nlinarith
    rw [mul_pow, Real.sq_sqrt (h2WeightR3_pos ξ).le] at hsq_le
    have h2ab : (2 * (∫ η : R3, ‖b η‖ * wa (ξ - η)) + 2 * (∫ η : R3, ‖a η‖ * wb (ξ - η))) ^ 2 ≤
        8 * (∫ η : R3, ‖b η‖ * wa (ξ - η)) ^ 2 + 8 * (∫ η : R3, ‖a η‖ * wb (ξ - η)) ^ 2 := by
      nlinarith [sq_nonneg ((∫ η : R3, ‖b η‖ * wa (ξ - η)) - (∫ η : R3, ‖a η‖ * wb (ξ - η)))]
    exact le_trans hsq_le h2ab
  have hdom : Integrable (fun ξ : R3 =>
      8 * (∫ η : R3, ‖b η‖ * wa (ξ - η)) ^ 2 + 8 * (∫ η : R3, ‖a η‖ * wb (ξ - η)) ^ 2) volume :=
    (hy1.2.1.const_mul 8).add (hy2.2.1.const_mul 8)
  have hint_conv : Integrable (fun ξ : R3 => h2WeightR3 ξ * ‖convR3 a b ξ‖ ^ 2) volume :=
    hdom.mono' (h2WeightR3_continuous.aestronglyMeasurable.mul (hconv_aem.norm.pow 2))
      (Filter.Eventually.of_forall fun ξ => by
        rw [Real.norm_of_nonneg (mul_nonneg (h2WeightR3_pos ξ).le (sq_nonneg _))]
        exact hpt ξ)
  have htame : h2NormSqR3 (convR3 a b) ≤
      8 * ((r3Integral (fun ξ => ‖b ξ‖)) ^ 2 * h2NormSqR3 a +
           (r3Integral (fun ξ => ‖a ξ‖)) ^ 2 * h2NormSqR3 b) := by
    have h1 : h2NormSqR3 (convR3 a b) ≤
        r3Integral (fun ξ => 8 * (∫ η : R3, ‖b η‖ * wa (ξ - η)) ^ 2 +
          8 * (∫ η : R3, ‖a η‖ * wb (ξ - η)) ^ 2) :=
      integral_mono hint_conv hdom hpt
    rw [r3Integral_add (hy1.2.1.const_mul 8) (hy2.2.1.const_mul 8),
        r3Integral_const_mul, r3Integral_const_mul] at h1
    have hb1 := hy1.2.2; rw [hwa2_eq] at hb1
    have hb2 := hy2.2.2; rw [hwb2_eq] at hb2
    linarith
  have hbanach : h2NormSqR3 (convR3 a b) ≤ 16 * Real.pi ^ 2 * h2NormSqR3 a * h2NormSqR3 b := by
    have hna := h2NormSqR3_nonneg a
    have hnb := h2NormSqR3_nonneg b
    have h1 : (r3Integral (fun ξ => ‖b ξ‖)) ^ 2 * h2NormSqR3 a ≤
        Real.pi ^ 2 * h2NormSqR3 b * h2NormSqR3 a :=
      mul_le_mul_of_nonneg_right hbl1.2 hna
    have h2 : (r3Integral (fun ξ => ‖a ξ‖)) ^ 2 * h2NormSqR3 b ≤
        Real.pi ^ 2 * h2NormSqR3 a * h2NormSqR3 b :=
      mul_le_mul_of_nonneg_right hal1.2 hnb
    linarith
  exact ⟨⟨hconv_aem, hint_conv⟩, htame, hbanach⟩

/-- **THEOREM 15D1-5 (Quadratic Convolution Lipschitz Estimate in `H²(ℝ³)`):** -/
theorem convR3_self_sub_lipschitz {a b : R3 → ℂ} (ha : InH2R3 a) (hb : InH2R3 b) :
    InH2R3 (fun ξ => convR3 a a ξ - convR3 b b ξ) ∧
    h2NormSqR3 (fun ξ => convR3 a a ξ - convR3 b b ξ) ≤
      32 * Real.pi ^ 2 * (h2NormSqR3 a + h2NormSqR3 b) * h2NormSqR3 (fun ξ => a ξ - b ξ) := by
  have hsub := (inH2R3_sub ha hb).1
  have h1 := convR3_tame_and_banach_algebra hsub ha
  have h2 := convR3_tame_and_banach_algebra hb hsub
  have hsplit : (fun ξ : R3 => convR3 a a ξ - convR3 b b ξ) =
      (fun ξ : R3 => convR3 (fun η => a η - b η) a ξ + convR3 b (fun η => a η - b η) ξ) := by
    funext ξ
    rw [convR3_sub_left ha hb ha ξ, convR3_sub_right hb ha hb ξ]
    ring
  rw [hsplit]
  have hadd := inH2R3_add h1.1 h2.1
  refine ⟨hadd.1, ?_⟩
  linarith [hadd.2, h1.2.2, h2.2.2]

-- ============================================================================
-- SECTION 1: SOLENOIDAL VECTOR H²_σ(ℝ³), COMPLEX LERAY PROJECTOR ℙ_ξ,
--            HEAT-SMOOTHED BILINEAR OPERATOR & PHYSICAL SYNTHESIS H² ↪ C⁰_b
-- ============================================================================

/-- Complex 3D Fourier vector field `ξ ↦ û(ξ) ∈ ℂ³` on `ℝ³`. -/
abbrev VecFieldR3C := R3 → (Fin 3 → ℂ)

/-- Squared Hermitian Euclidean norm on `ℂ³`. -/
noncomputable def vecNormSqR3C (v : Fin 3 → ℂ) : ℝ :=
  ‖v 0‖ ^ 2 + ‖v 1‖ ^ 2 + ‖v 2‖ ^ 2

/-- Membership in vector `H²(ℝ³; ℂ³)`. -/
def InH2VecR3 (u : VecFieldR3C) : Prop :=
  ∀ c : Fin 3, InH2R3 (fun ξ => u ξ c)

/-- Squared vector `H²(ℝ³)` norm `∑_{c=0}^2 ∫_{ℝ³} (1 + |ξ|²)² ‖û_c(ξ)‖² dξ`. -/
noncomputable def h2VecNormSqR3 (u : VecFieldR3C) : ℝ :=
  h2NormSqR3 (fun ξ => u ξ 0) + h2NormSqR3 (fun ξ => u ξ 1) + h2NormSqR3 (fun ξ => u ξ 2)

/-- Spectral divergence-free condition `ξ · û(ξ) = 0` on `ℝ³`. -/
def IsSolenoidalR3C (u : VecFieldR3C) : Prop :=
  ∀ ξ : R3, (ξ 0 : ℂ) * u ξ 0 + (ξ 1 : ℂ) * u ξ 1 + (ξ 2 : ℂ) * u ξ 2 = 0

/-- Hermitian reality symmetry `conj(û(ξ)) = û(-ξ)` guaranteeing real-valued synthesis. -/
def IsRealSymmR3C (u : VecFieldR3C) : Prop :=
  ∀ (ξ : R3) (c : Fin 3), starRingEnd ℂ (u ξ c) = u (-ξ) c

lemma vecNormSqR3C_nonneg (v : Fin 3 → ℂ) : 0 ≤ vecNormSqR3C v := by
  unfold vecNormSqR3C; positivity

lemma h2VecNormSqR3_nonneg (u : VecFieldR3C) : 0 ≤ h2VecNormSqR3 u := by
  unfold h2VecNormSqR3
  linarith [h2NormSqR3_nonneg (fun ξ => u ξ 0),
    h2NormSqR3_nonneg (fun ξ => u ξ 1), h2NormSqR3_nonneg (fun ξ => u ξ 2)]

lemma h2VecNormSqR3_eq_integral {u : VecFieldR3C} (hu : InH2VecR3 u) :
    h2VecNormSqR3 u = r3Integral (fun ξ : R3 => h2WeightR3 ξ * vecNormSqR3C (u ξ)) := by
  unfold h2VecNormSqR3 h2NormSqR3
  rw [← r3Integral_add3 (hu 0).2 (hu 1).2 (hu 2).2]
  exact r3Integral_congr fun ξ => by unfold vecNormSqR3C; ring

theorem inH2VecR3_add {u v : VecFieldR3C} (hu : InH2VecR3 u) (hv : InH2VecR3 v) :
    InH2VecR3 (fun ξ c => u ξ c + v ξ c) ∧
    h2VecNormSqR3 (fun ξ c => u ξ c + v ξ c) ≤ 2 * h2VecNormSqR3 u + 2 * h2VecNormSqR3 v := by
  have hc : ∀ c : Fin 3, InH2R3 (fun ξ => u ξ c + v ξ c) ∧
      h2NormSqR3 (fun ξ => u ξ c + v ξ c) ≤ 2 * h2NormSqR3 (fun ξ => u ξ c) + 2 * h2NormSqR3 (fun ξ => v ξ c) :=
    fun c => inH2R3_add (hu c) (hv c)
  refine ⟨fun c => (hc c).1, ?_⟩
  unfold h2VecNormSqR3
  linarith [(hc 0).2, (hc 1).2, (hc 2).2]

theorem inH2VecR3_sub {u v : VecFieldR3C} (hu : InH2VecR3 u) (hv : InH2VecR3 v) :
    InH2VecR3 (fun ξ c => u ξ c - v ξ c) ∧
    h2VecNormSqR3 (fun ξ c => u ξ c - v ξ c) ≤ 2 * h2VecNormSqR3 u + 2 * h2VecNormSqR3 v := by
  have hc : ∀ c : Fin 3, InH2R3 (fun ξ => u ξ c - v ξ c) ∧
      h2NormSqR3 (fun ξ => u ξ c - v ξ c) ≤ 2 * h2NormSqR3 (fun ξ => u ξ c) + 2 * h2NormSqR3 (fun ξ => v ξ c) :=
    fun c => inH2R3_sub (hu c) (hv c)
  refine ⟨fun c => (hc c).1, ?_⟩
  unfold h2VecNormSqR3
  linarith [(hc 0).2, (hc 1).2, (hc 2).2]

/-- Complex 3D Leray–Helmholtz orthogonal projection onto `{v ∈ ℂ³ : ξ · v = 0}` on `ℝ³`. -/
noncomputable def lerayProjR3C (ξ : R3) (v : Fin 3 → ℂ) : Fin 3 → ℂ :=
  if dot3D ξ ξ = 0 then v
  else fun c =>
    v c - (((ξ 0 : ℂ) * v 0 + (ξ 1 : ℂ) * v 1 + (ξ 2 : ℂ) * v 2) /
      ((dot3D ξ ξ : ℝ) : ℂ)) * (ξ c : ℂ)

/-- **THEOREM 15D1-6 (Complete Algebraic & Hermitian Laws of Complex `ℝ³` Leray Projector `ℙ_ξ`):** -/
theorem lerayProjR3C_solenoidal_and_contraction (ξ : R3) :
    (∀ v : Fin 3 → ℂ,
      (ξ 0 : ℂ) * lerayProjR3C ξ v 0 + (ξ 1 : ℂ) * lerayProjR3C ξ v 1 +
        (ξ 2 : ℂ) * lerayProjR3C ξ v 2 = 0) ∧
    (∀ v : Fin 3 → ℂ, vecNormSqR3C (lerayProjR3C ξ v) ≤ vecNormSqR3C v) ∧
    (∀ (v : Fin 3 → ℂ) (c : Fin 3),
      starRingEnd ℂ (lerayProjR3C ξ v c) = lerayProjR3C (-ξ) (fun j => starRingEnd ℂ (v j)) c) ∧
    (∀ (v w : Fin 3 → ℂ) (c : Fin 3),
      lerayProjR3C ξ (fun j => v j + w j) c = lerayProjR3C ξ v c + lerayProjR3C ξ w c) ∧
    (∀ (v w : Fin 3 → ℂ) (c : Fin 3),
      lerayProjR3C ξ (fun j => v j - w j) c = lerayProjR3C ξ v c - lerayProjR3C ξ w c) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro v
    unfold lerayProjR3C
    split_ifs with h0
    · have hξ0 : ξ 0 = 0 := by unfold dot3D at h0; nlinarith [sq_nonneg (ξ 0), sq_nonneg (ξ 1), sq_nonneg (ξ 2)]
      have hξ1 : ξ 1 = 0 := by unfold dot3D at h0; nlinarith [sq_nonneg (ξ 0), sq_nonneg (ξ 1), sq_nonneg (ξ 2)]
      have hξ2 : ξ 2 = 0 := by unfold dot3D at h0; nlinarith [sq_nonneg (ξ 0), sq_nonneg (ξ 1), sq_nonneg (ξ 2)]
      simp [hξ0, hξ1, hξ2]
    · have hneC : ((dot3D ξ ξ : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 h0
      have hdotC : ((dot3D ξ ξ : ℝ) : ℂ) = (ξ 0 : ℂ) * (ξ 0 : ℂ) + (ξ 1 : ℂ) * (ξ 1 : ℂ) + (ξ 2 : ℂ) * (ξ 2 : ℂ) := by
        unfold dot3D; push_cast; ring
      field_simp [hneC]
      rw [hdotC]; ring
  · intro v
    unfold lerayProjR3C
    split_ifs with h0
    · exact le_rfl
    · have hr_pos : 0 < dot3D ξ ξ := lt_of_le_of_ne (dot3D_self_nonneg_r3 ξ) (Ne.symm h0)
      set r : ℝ := dot3D ξ ξ
      set z : ℂ := (ξ 0 : ℂ) * v 0 + (ξ 1 : ℂ) * v 1 + (ξ 2 : ℂ) * v 2
      have hnorm : ∀ w : ℂ, ‖w‖ ^ 2 = w.re ^ 2 + w.im ^ 2 := fun w => by
        rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]; ring
      have hre : ∀ c : Fin 3, (v c - (z / (r : ℂ)) * (ξ c : ℂ)).re = (v c).re - (z.re / r) * ξ c := by
        intro c
        rw [Complex.sub_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero,
            Complex.div_ofReal_re]
      have him : ∀ c : Fin 3, (v c - (z / (r : ℂ)) * (ξ c : ℂ)).im = (v c).im - (z.im / r) * ξ c := by
        intro c
        rw [Complex.sub_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, mul_zero, zero_add,
            Complex.div_ofReal_im]
      have hzre : z.re = ξ 0 * (v 0).re + ξ 1 * (v 1).re + ξ 2 * (v 2).re := by
        dsimp only [z]; simp
      have hzim : z.im = ξ 0 * (v 0).im + ξ 1 * (v 1).im + ξ 2 * (v 2).im := by
        dsimp only [z]; simp
      have hpyth_re :
          ((v 0).re - (z.re / r) * ξ 0) ^ 2 + ((v 1).re - (z.re / r) * ξ 1) ^ 2 +
            ((v 2).re - (z.re / r) * ξ 2) ^ 2 =
          (v 0).re ^ 2 + (v 1).re ^ 2 + (v 2).re ^ 2 - z.re ^ 2 / r := by
        have hr_eq : ξ 0 ^ 2 + ξ 1 ^ 2 + ξ 2 ^ 2 = r := by dsimp only [r, dot3D]; ring
        field_simp [hr_pos.ne']
        linear_combination (z.re ^ 2) * hr_eq + 2 * r * z.re * hzre
      have hpyth_im :
          ((v 0).im - (z.im / r) * ξ 0) ^ 2 + ((v 1).im - (z.im / r) * ξ 1) ^ 2 +
            ((v 2).im - (z.im / r) * ξ 2) ^ 2 =
          (v 0).im ^ 2 + (v 1).im ^ 2 + (v 2).im ^ 2 - z.im ^ 2 / r := by
        have hr_eq : ξ 0 ^ 2 + ξ 1 ^ 2 + ξ 2 ^ 2 = r := by dsimp only [r, dot3D]; ring
        field_simp [hr_pos.ne']
        linear_combination (z.im ^ 2) * hr_eq + 2 * r * z.im * hzim
      unfold vecNormSqR3C
      simp only [hnorm, hre, him]
      have hnn1 : 0 ≤ z.re ^ 2 / r := div_nonneg (sq_nonneg _) hr_pos.le
      have hnn2 : 0 ≤ z.im ^ 2 / r := div_nonneg (sq_nonneg _) hr_pos.le
      linarith
  · intro v c
    have hdot_neg : dot3D (-ξ) (-ξ) = dot3D ξ ξ := by unfold dot3D; simp
    unfold lerayProjR3C
    rw [hdot_neg]
    split_ifs with h0
    · rfl
    · simp only [map_sub, map_mul, map_div₀, map_add, Complex.conj_ofReal, Pi.neg_apply, Complex.ofReal_neg]
      ring
  · intro v w c
    unfold lerayProjR3C
    split_ifs with h0
    · rfl
    · ring
  · intro v w c
    unfold lerayProjR3C
    split_ifs with h0
    · rfl
    · ring

/-- Unprojected divergence-form nonlinear flux on `ℝ³`:
    `F(u, v)_ξ(c) = i ∑_{j=0}^2 ξ_j (u_j * v_c)(ξ)`. -/
noncomputable def nsFluxR3 (u v : VecFieldR3C) (ξ : R3) (c : Fin 3) : ℂ :=
  Complex.I *
    ((ξ 0 : ℂ) * convR3 (fun η => u η 0) (fun η => v η c) ξ +
     (ξ 1 : ℂ) * convR3 (fun η => u η 1) (fun η => v η c) ξ +
     (ξ 2 : ℂ) * convR3 (fun η => u η 2) (fun η => v η c) ξ)

/-- Leray-projected Navier–Stokes bilinear operator on `ℝ³`: `B(u, v)_ξ = -ℙ_ξ(F(u, v)_ξ)`. -/
noncomputable def nsBilinearR3 (u v : VecFieldR3C) (ξ : R3) : Fin 3 → ℂ :=
  fun c => -lerayProjR3C ξ (nsFluxR3 u v ξ) c

/-- Heat-smoothed Navier–Stokes bilinear operator on `ℝ³`:
    `S_τ(u, v)_ξ = e^{-ν |ξ|² τ} B(u, v)_ξ`. -/
noncomputable def heatSmoothedBilinearR3 (ν τ : ℝ) (u v : VecFieldR3C) (ξ : R3) : Fin 3 → ℂ :=
  fun c => (heatMultiplier3D ν τ ξ : ℂ) * nsBilinearR3 u v ξ c

/-- **THEOREM 15D1-7 (Solenoidality & Reality Symmetry of `heatSmoothedBilinearR3`):** -/
theorem heatSmoothedBilinearR3_structure (ν τ : ℝ) {u v : VecFieldR3C}
    (hu : InH2VecR3 u) (hv : InH2VecR3 v)
    (hsu : IsRealSymmR3C u) (hsv : IsRealSymmR3C v) :
    IsSolenoidalR3C (nsBilinearR3 u v) ∧
    IsSolenoidalR3C (heatSmoothedBilinearR3 ν τ u v) ∧
    IsRealSymmR3C (heatSmoothedBilinearR3 ν τ u v) := by
  have hsol_B : IsSolenoidalR3C (nsBilinearR3 u v) := by
    intro ξ; unfold nsBilinearR3
    have h := (lerayProjR3C_solenoidal_and_contraction ξ).1 (nsFluxR3 u v ξ)
    linear_combination -h
  have hsol_S : IsSolenoidalR3C (heatSmoothedBilinearR3 ν τ u v) := by
    intro ξ; unfold heatSmoothedBilinearR3
    have h := hsol_B ξ
    linear_combination (heatMultiplier3D ν τ ξ : ℂ) * h
  have hsym_S : IsRealSymmR3C (heatSmoothedBilinearR3 ν τ u v) := by
    intro ξ c
    have hhm_neg : heatMultiplier3D ν τ (-ξ) = heatMultiplier3D ν τ ξ := by
      unfold heatMultiplier3D dot3D; congr 1; simp
    have hflux_conj : ∀ j : Fin 3, starRingEnd ℂ (nsFluxR3 u v ξ j) = nsFluxR3 u v (-ξ) j := by
      intro j; unfold nsFluxR3
      simp only [map_mul, map_add, Complex.conj_I, Complex.conj_ofReal, Pi.neg_apply, Complex.ofReal_neg]
      rw [convR3_conj_symm (hu 0) (hv j) (fun η => hsu η 0) (fun η => hsv η j) ξ,
          convR3_conj_symm (hu 1) (hv j) (fun η => hsu η 1) (fun η => hsv η j) ξ,
          convR3_conj_symm (hu 2) (hv j) (fun η => hsu η 2) (fun η => hsv η j) ξ]
      ring
    unfold heatSmoothedBilinearR3 nsBilinearR3
    rw [map_mul, Complex.conj_ofReal, map_neg,
        (lerayProjR3C_solenoidal_and_contraction ξ).2.2.1 (nsFluxR3 u v ξ) c, hhm_neg]
    have hfun : (fun j => starRingEnd ℂ (nsFluxR3 u v ξ j)) = nsFluxR3 u v (-ξ) :=
      funext hflux_conj
    rw [hfun]
  exact ⟨hsol_B, hsol_S, hsym_S⟩

private lemma lerayProjR3C_aestronglyMeasurable_15d {v : VecFieldR3C}
    (hv : ∀ c : Fin 3, AEStronglyMeasurable (fun ξ => v ξ c) volume) (c : Fin 3) :
    AEStronglyMeasurable (fun ξ => lerayProjR3C ξ (v ξ) c) volume := by
  have hdot_c : Continuous (fun ξ : R3 => dot3D ξ ξ) := by unfold dot3D; fun_prop
  have hset : MeasurableSet {ξ : R3 | dot3D ξ ξ = 0} :=
    isClosed_eq hdot_c continuous_const |>.measurableSet
  have hcoord : ∀ j : Fin 3, Continuous (fun ξ : R3 => (ξ j : ℂ)) := fun j =>
    Complex.continuous_ofReal.comp (continuous_apply j)
  have hnum : AEStronglyMeasurable (fun ξ : R3 =>
      (ξ 0 : ℂ) * v ξ 0 + (ξ 1 : ℂ) * v ξ 1 + (ξ 2 : ℂ) * v ξ 2) volume :=
    (((hcoord 0).aestronglyMeasurable.mul (hv 0)).add
      ((hcoord 1).aestronglyMeasurable.mul (hv 1))).add
      ((hcoord 2).aestronglyMeasurable.mul (hv 2))
  have hden_inv : AEStronglyMeasurable (fun ξ : R3 => (((dot3D ξ ξ : ℝ) : ℂ))⁻¹) volume :=
    (Complex.continuous_ofReal.comp hdot_c).measurable.inv.aestronglyMeasurable
  have helse : AEStronglyMeasurable (fun ξ : R3 =>
      v ξ c - (((ξ 0 : ℂ) * v ξ 0 + (ξ 1 : ℂ) * v ξ 1 + (ξ 2 : ℂ) * v ξ 2) /
        ((dot3D ξ ξ : ℝ) : ℂ)) * (ξ c : ℂ)) volume := by
    have heq_div : (fun ξ : R3 =>
        v ξ c - (((ξ 0 : ℂ) * v ξ 0 + (ξ 1 : ℂ) * v ξ 1 + (ξ 2 : ℂ) * v ξ 2) /
          ((dot3D ξ ξ : ℝ) : ℂ)) * (ξ c : ℂ)) =
      (fun ξ : R3 =>
        v ξ c - (((ξ 0 : ℂ) * v ξ 0 + (ξ 1 : ℂ) * v ξ 1 + (ξ 2 : ℂ) * v ξ 2) *
          (((dot3D ξ ξ : ℝ) : ℂ))⁻¹) * (ξ c : ℂ)) := by
      funext ξ; rw [div_eq_mul_inv]
    rw [heq_div]
    exact (hv c).sub ((hnum.mul hden_inv).mul (hcoord c).aestronglyMeasurable)
  have heq : (fun ξ : R3 => lerayProjR3C ξ (v ξ) c) =
      Set.piecewise {ξ : R3 | dot3D ξ ξ = 0} (fun ξ => v ξ c)
        (fun ξ => v ξ c - (((ξ 0 : ℂ) * v ξ 0 + (ξ 1 : ℂ) * v ξ 1 + (ξ 2 : ℂ) * v ξ 2) /
          ((dot3D ξ ξ : ℝ) : ℂ)) * (ξ c : ℂ)) := by
    funext ξ; unfold lerayProjR3C Set.piecewise
    by_cases h0 : dot3D ξ ξ = 0 <;> simp [h0]
  rw [heq]
  exact AEStronglyMeasurable.piecewise hset.nullMeasurableSet (hv c).restrict helse.restrict

/-- **THEOREM 15D1-8 (Heat-Smoothed Bilinear `H²(ℝ³)` Smoothing Bound `8π² / (ν τ)`):** -/
theorem heatSmoothedBilinearR3_inH2_and_bound
    {ν τ : ℝ} (hν : 0 < ν) (hτ : 0 < τ) {u v : VecFieldR3C} (hu : InH2VecR3 u) (hv : InH2VecR3 v) :
    InH2VecR3 (heatSmoothedBilinearR3 ν τ u v) ∧
    h2VecNormSqR3 (heatSmoothedBilinearR3 ν τ u v) ≤
      (8 * Real.pi ^ 2 / (ν * τ)) * h2VecNormSqR3 u * h2VecNormSqR3 v := by
  have hconv : ∀ j c : Fin 3, InH2R3 (convR3 (fun η => u η j) (fun η => v η c)) ∧
      h2NormSqR3 (convR3 (fun η => u η j) (fun η => v η c)) ≤
        16 * Real.pi ^ 2 * h2NormSqR3 (fun η => u η j) * h2NormSqR3 (fun η => v η c) := fun j c =>
    ⟨(convR3_tame_and_banach_algebra (hu j) (hv c)).1, (convR3_tame_and_banach_algebra (hu j) (hv c)).2.2⟩
  have hcoord : ∀ j : Fin 3, Continuous (fun ξ : R3 => (ξ j : ℂ)) := fun j =>
    Complex.continuous_ofReal.comp (continuous_apply j)
  have hflux_m : ∀ c : Fin 3, AEStronglyMeasurable (fun ξ => nsFluxR3 u v ξ c) volume := fun c => by
    unfold nsFluxR3
    exact aestronglyMeasurable_const.mul
      ((((hcoord 0).aestronglyMeasurable.mul (hconv 0 c).1.1).add
        ((hcoord 1).aestronglyMeasurable.mul (hconv 1 c).1.1)).add
        ((hcoord 2).aestronglyMeasurable.mul (hconv 2 c).1.1))
  have hhm_c : Continuous (fun ξ : R3 => (heatMultiplier3D ν τ ξ : ℂ)) :=
    Complex.continuous_ofReal.comp (Real.continuous_exp.comp (by unfold dot3D; fun_prop))
  have hS_m : ∀ c : Fin 3, AEStronglyMeasurable (fun ξ => heatSmoothedBilinearR3 ν τ u v ξ c) volume :=
    fun c => hhm_c.aestronglyMeasurable.mul (lerayProjR3C_aestronglyMeasurable_15d hflux_m c).neg
  -- Pointwise heat smoothing bound: dot3D ξ ξ * (heatMultiplier3D ν τ ξ)² ≤ 1 / (2 ν τ)
  have hsmooth : ∀ ξ : R3, dot3D ξ ξ * (heatMultiplier3D ν τ ξ) ^ 2 ≤ 1 / (2 * ν * τ) := by
    intro ξ
    have h1 := (heatMultiplier3D_smoothing_and_L1_integral hν).1 τ hτ ξ
    have hL_nn : 0 ≤ Real.sqrt (dot3D ξ ξ) * heatMultiplier3D ν τ ξ :=
      mul_nonneg (Real.sqrt_nonneg _) (heatMultiplier3D_pos ν τ ξ).le
    have hsq : (Real.sqrt (dot3D ξ ξ) * heatMultiplier3D ν τ ξ) ^ 2 ≤ (1 / Real.sqrt (2 * ν * τ)) ^ 2 := by
      nlinarith
    rw [mul_pow, Real.sq_sqrt (dot3D_self_nonneg_r3 ξ), div_pow, one_pow,
        Real.sq_sqrt (by positivity : (0 : ℝ) ≤ 2 * ν * τ)] at hsq
    exact hsq
  -- Pointwise norm bound on nsFluxR3 u v ξ c
  have hflux_pt : ∀ (ξ : R3) (c : Fin 3),
      ‖nsFluxR3 u v ξ c‖ ^ 2 ≤ dot3D ξ ξ *
        (‖convR3 (fun η => u η 0) (fun η => v η c) ξ‖ ^ 2 +
         ‖convR3 (fun η => u η 1) (fun η => v η c) ξ‖ ^ 2 +
         ‖convR3 (fun η => u η 2) (fun η => v η c) ξ‖ ^ 2) := by
    intro ξ c
    unfold nsFluxR3
    rw [norm_mul, Complex.norm_I, one_mul]
    set a0 : ℝ := ‖convR3 (fun η => u η 0) (fun η => v η c) ξ‖
    set a1 : ℝ := ‖convR3 (fun η => u η 1) (fun η => v η c) ξ‖
    set a2 : ℝ := ‖convR3 (fun η => u η 2) (fun η => v η c) ξ‖
    have htri : ‖(ξ 0 : ℂ) * convR3 (fun η => u η 0) (fun η => v η c) ξ +
        (ξ 1 : ℂ) * convR3 (fun η => u η 1) (fun η => v η c) ξ +
        (ξ 2 : ℂ) * convR3 (fun η => u η 2) (fun η => v η c) ξ‖ ≤
        |ξ 0| * a0 + |ξ 1| * a1 + |ξ 2| * a2 := by
      calc _ ≤ ‖(ξ 0 : ℂ) * convR3 (fun η => u η 0) (fun η => v η c) ξ +
                (ξ 1 : ℂ) * convR3 (fun η => u η 1) (fun η => v η c) ξ‖ +
              ‖(ξ 2 : ℂ) * convR3 (fun η => u η 2) (fun η => v η c) ξ‖ := norm_add_le _ _
        _ ≤ (‖(ξ 0 : ℂ) * convR3 (fun η => u η 0) (fun η => v η c) ξ‖ +
             ‖(ξ 1 : ℂ) * convR3 (fun η => u η 1) (fun η => v η c) ξ‖) +
            ‖(ξ 2 : ℂ) * convR3 (fun η => u η 2) (fun η => v η c) ξ‖ := by
              linarith [norm_add_le ((ξ 0 : ℂ) * convR3 (fun η => u η 0) (fun η => v η c) ξ)
                ((ξ 1 : ℂ) * convR3 (fun η => u η 1) (fun η => v η c) ξ)]
        _ = |ξ 0| * a0 + |ξ 1| * a1 + |ξ 2| * a2 := by
              simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs]; rfl
    have hsq1 : ‖(ξ 0 : ℂ) * convR3 (fun η => u η 0) (fun η => v η c) ξ +
        (ξ 1 : ℂ) * convR3 (fun η => u η 1) (fun η => v η c) ξ +
        (ξ 2 : ℂ) * convR3 (fun η => u η 2) (fun η => v η c) ξ‖ ^ 2 ≤
        (|ξ 0| * a0 + |ξ 1| * a1 + |ξ 2| * a2) ^ 2 := by nlinarith [norm_nonneg ((ξ 0 : ℂ) * convR3 (fun η => u η 0) (fun η => v η c) ξ +
          (ξ 1 : ℂ) * convR3 (fun η => u η 1) (fun η => v η c) ξ +
          (ξ 2 : ℂ) * convR3 (fun η => u η 2) (fun η => v η c) ξ)]
    have hcs3 : (|ξ 0| * a0 + |ξ 1| * a1 + |ξ 2| * a2) ^ 2 ≤
        dot3D ξ ξ * (a0 ^ 2 + a1 ^ 2 + a2 ^ 2) := by
      unfold dot3D
      have h0 : 0 ≤ (|ξ 0| * a1 - |ξ 1| * a0) ^ 2 + (|ξ 0| * a2 - |ξ 2| * a0) ^ 2 +
          (|ξ 1| * a2 - |ξ 2| * a1) ^ 2 := by positivity
      have hs0 : |ξ 0| ^ 2 = (ξ 0) ^ 2 := sq_abs _
      have hs1 : |ξ 1| ^ 2 = (ξ 1) ^ 2 := sq_abs _
      have hs2 : |ξ 2| ^ 2 = (ξ 2) ^ 2 := sq_abs _
      nlinarith
    exact le_trans hsq1 hcs3
  -- Pointwise domination of vecNormSqR3C (heatSmoothedBilinearR3 ν τ u v ξ)
  let dom : R3 → ℝ := fun ξ => (1 / (2 * ν * τ)) * h2WeightR3 ξ *
    ((‖convR3 (fun η => u η 0) (fun η => v η 0) ξ‖ ^ 2 +
      ‖convR3 (fun η => u η 1) (fun η => v η 0) ξ‖ ^ 2 +
      ‖convR3 (fun η => u η 2) (fun η => v η 0) ξ‖ ^ 2) +
     (‖convR3 (fun η => u η 0) (fun η => v η 1) ξ‖ ^ 2 +
      ‖convR3 (fun η => u η 1) (fun η => v η 1) ξ‖ ^ 2 +
      ‖convR3 (fun η => u η 2) (fun η => v η 1) ξ‖ ^ 2) +
     (‖convR3 (fun η => u η 0) (fun η => v η 2) ξ‖ ^ 2 +
      ‖convR3 (fun η => u η 1) (fun η => v η 2) ξ‖ ^ 2 +
      ‖convR3 (fun η => u η 2) (fun η => v η 2) ξ‖ ^ 2))
  have hdom_int : Integrable dom volume := by
    have hrow : ∀ c : Fin 3, Integrable (fun ξ : R3 =>
        h2WeightR3 ξ * ‖convR3 (fun η => u η 0) (fun η => v η c) ξ‖ ^ 2 +
        h2WeightR3 ξ * ‖convR3 (fun η => u η 1) (fun η => v η c) ξ‖ ^ 2 +
        h2WeightR3 ξ * ‖convR3 (fun η => u η 2) (fun η => v η c) ξ‖ ^ 2) volume :=
      fun c => ((hconv 0 c).1.2.add (hconv 1 c).1.2).add (hconv 2 c).1.2
    exact (((hrow 0).add (hrow 1)).add (hrow 2)).const_mul (1 / (2 * ν * τ)) |>.congr
      (Filter.Eventually.of_forall fun ξ => by dsimp only [dom, Pi.add_apply]; ring)
  have hvec_pt : ∀ ξ : R3, h2WeightR3 ξ * vecNormSqR3C (heatSmoothedBilinearR3 ν τ u v ξ) ≤ dom ξ := by
    intro ξ
    have h1 : vecNormSqR3C (heatSmoothedBilinearR3 ν τ u v ξ) =
        (heatMultiplier3D ν τ ξ) ^ 2 * vecNormSqR3C (lerayProjR3C ξ (nsFluxR3 u v ξ)) := by
      unfold vecNormSqR3C heatSmoothedBilinearR3 nsBilinearR3
      simp only [norm_mul, norm_neg, Complex.norm_real, Real.norm_of_nonneg (heatMultiplier3D_pos ν τ ξ).le]
      ring
    have h2 : vecNormSqR3C (lerayProjR3C ξ (nsFluxR3 u v ξ)) ≤ vecNormSqR3C (nsFluxR3 u v ξ) :=
      (lerayProjR3C_solenoidal_and_contraction ξ).2.1 _
    have h3 : vecNormSqR3C (nsFluxR3 u v ξ) ≤ dot3D ξ ξ *
        ((‖convR3 (fun η => u η 0) (fun η => v η 0) ξ‖ ^ 2 +
          ‖convR3 (fun η => u η 1) (fun η => v η 0) ξ‖ ^ 2 +
          ‖convR3 (fun η => u η 2) (fun η => v η 0) ξ‖ ^ 2) +
         (‖convR3 (fun η => u η 0) (fun η => v η 1) ξ‖ ^ 2 +
          ‖convR3 (fun η => u η 1) (fun η => v η 1) ξ‖ ^ 2 +
          ‖convR3 (fun η => u η 2) (fun η => v η 1) ξ‖ ^ 2) +
         (‖convR3 (fun η => u η 0) (fun η => v η 2) ξ‖ ^ 2 +
          ‖convR3 (fun η => u η 1) (fun η => v η 2) ξ‖ ^ 2 +
          ‖convR3 (fun η => u η 2) (fun η => v η 2) ξ‖ ^ 2)) := by
      unfold vecNormSqR3C
      linarith [hflux_pt ξ 0, hflux_pt ξ 1, hflux_pt ξ 2]
    have hS_nn : 0 ≤ (‖convR3 (fun η => u η 0) (fun η => v η 0) ξ‖ ^ 2 +
          ‖convR3 (fun η => u η 1) (fun η => v η 0) ξ‖ ^ 2 +
          ‖convR3 (fun η => u η 2) (fun η => v η 0) ξ‖ ^ 2) +
         (‖convR3 (fun η => u η 0) (fun η => v η 1) ξ‖ ^ 2 +
          ‖convR3 (fun η => u η 1) (fun η => v η 1) ξ‖ ^ 2 +
          ‖convR3 (fun η => u η 2) (fun η => v η 1) ξ‖ ^ 2) +
         (‖convR3 (fun η => u η 0) (fun η => v η 2) ξ‖ ^ 2 +
          ‖convR3 (fun η => u η 1) (fun η => v η 2) ξ‖ ^ 2 +
          ‖convR3 (fun η => u η 2) (fun η => v η 2) ξ‖ ^ 2) := by positivity
    have h4 : (heatMultiplier3D ν τ ξ) ^ 2 * vecNormSqR3C (nsFluxR3 u v ξ) ≤
        (1 / (2 * ν * τ)) * ((‖convR3 (fun η => u η 0) (fun η => v η 0) ξ‖ ^ 2 +
          ‖convR3 (fun η => u η 1) (fun η => v η 0) ξ‖ ^ 2 +
          ‖convR3 (fun η => u η 2) (fun η => v η 0) ξ‖ ^ 2) +
         (‖convR3 (fun η => u η 0) (fun η => v η 1) ξ‖ ^ 2 +
          ‖convR3 (fun η => u η 1) (fun η => v η 1) ξ‖ ^ 2 +
          ‖convR3 (fun η => u η 2) (fun η => v η 1) ξ‖ ^ 2) +
         (‖convR3 (fun η => u η 0) (fun η => v η 2) ξ‖ ^ 2 +
          ‖convR3 (fun η => u η 1) (fun η => v η 2) ξ‖ ^ 2 +
          ‖convR3 (fun η => u η 2) (fun η => v η 2) ξ‖ ^ 2)) := by
      calc (heatMultiplier3D ν τ ξ) ^ 2 * vecNormSqR3C (nsFluxR3 u v ξ)
          ≤ (heatMultiplier3D ν τ ξ) ^ 2 * (dot3D ξ ξ * _) :=
            mul_le_mul_of_nonneg_left h3 (sq_nonneg _)
        _ = (dot3D ξ ξ * (heatMultiplier3D ν τ ξ) ^ 2) * _ := by ring
        _ ≤ (1 / (2 * ν * τ)) * _ := mul_le_mul_of_nonneg_right (hsmooth ξ) hS_nn
    rw [h1]
    have h5 := mul_le_mul_of_nonneg_left (le_trans (mul_le_mul_of_nonneg_left h2 (sq_nonneg _)) h4)
      (h2WeightR3_pos ξ).le
    dsimp only [dom]; linarith
  have hS_inH2 : InH2VecR3 (heatSmoothedBilinearR3 ν τ u v) := fun c => by
    refine ⟨hS_m c, hdom_int.mono' (h2WeightR3_continuous.aestronglyMeasurable.mul ((hS_m c).norm.pow 2))
      (Filter.Eventually.of_forall fun ξ => ?_)⟩
    rw [Real.norm_of_nonneg (mul_nonneg (h2WeightR3_pos ξ).le (sq_nonneg _))]
    have hcomp_le : ‖heatSmoothedBilinearR3 ν τ u v ξ c‖ ^ 2 ≤
        vecNormSqR3C (heatSmoothedBilinearR3 ν τ u v ξ) := by
      unfold vecNormSqR3C
      have h0 : 0 ≤ ‖heatSmoothedBilinearR3 ν τ u v ξ 0‖ ^ 2 := sq_nonneg _
      have h1 : 0 ≤ ‖heatSmoothedBilinearR3 ν τ u v ξ 1‖ ^ 2 := sq_nonneg _
      have h2 : 0 ≤ ‖heatSmoothedBilinearR3 ν τ u v ξ 2‖ ^ 2 := sq_nonneg _
      fin_cases c
      · change ‖heatSmoothedBilinearR3 ν τ u v ξ 0‖ ^ 2 ≤ _; linarith
      · change ‖heatSmoothedBilinearR3 ν τ u v ξ 1‖ ^ 2 ≤ _; linarith
      · change ‖heatSmoothedBilinearR3 ν τ u v ξ 2‖ ^ 2 ≤ _; linarith
    exact le_trans (mul_le_mul_of_nonneg_left hcomp_le (h2WeightR3_pos ξ).le) (hvec_pt ξ)
  refine ⟨hS_inH2, ?_⟩
  rw [h2VecNormSqR3_eq_integral hS_inH2]
  have hvec_int : Integrable (fun ξ => h2WeightR3 ξ * vecNormSqR3C (heatSmoothedBilinearR3 ν τ u v ξ)) volume :=
    (((hS_inH2 0).2.add (hS_inH2 1).2).add (hS_inH2 2).2).congr
      (Filter.Eventually.of_forall fun ξ => by dsimp only [Pi.add_apply]; unfold vecNormSqR3C; ring)
  have hint_le : r3Integral (fun ξ => h2WeightR3 ξ * vecNormSqR3C (heatSmoothedBilinearR3 ν τ u v ξ)) ≤
      r3Integral dom := integral_mono hvec_int hdom_int hvec_pt
  have hdom_val : r3Integral dom = (1 / (2 * ν * τ)) *
      ((h2NormSqR3 (convR3 (fun η => u η 0) (fun η => v η 0)) +
        h2NormSqR3 (convR3 (fun η => u η 1) (fun η => v η 0)) +
        h2NormSqR3 (convR3 (fun η => u η 2) (fun η => v η 0))) +
       (h2NormSqR3 (convR3 (fun η => u η 0) (fun η => v η 1)) +
        h2NormSqR3 (convR3 (fun η => u η 1) (fun η => v η 1)) +
        h2NormSqR3 (convR3 (fun η => u η 2) (fun η => v η 1))) +
       (h2NormSqR3 (convR3 (fun η => u η 0) (fun η => v η 2)) +
        h2NormSqR3 (convR3 (fun η => u η 1) (fun η => v η 2)) +
        h2NormSqR3 (convR3 (fun η => u η 2) (fun η => v η 2)))) := by
    have hrow : ∀ c : Fin 3, Integrable (fun ξ : R3 =>
        h2WeightR3 ξ * ‖convR3 (fun η => u η 0) (fun η => v η c) ξ‖ ^ 2 +
        h2WeightR3 ξ * ‖convR3 (fun η => u η 1) (fun η => v η c) ξ‖ ^ 2 +
        h2WeightR3 ξ * ‖convR3 (fun η => u η 2) (fun η => v η c) ξ‖ ^ 2) volume :=
      fun c => ((hconv 0 c).1.2.add (hconv 1 c).1.2).add (hconv 2 c).1.2
    have hpt_d : ∀ ξ : R3, dom ξ = (1 / (2 * ν * τ)) *
        ((h2WeightR3 ξ * ‖convR3 (fun η => u η 0) (fun η => v η 0) ξ‖ ^ 2 +
          h2WeightR3 ξ * ‖convR3 (fun η => u η 1) (fun η => v η 0) ξ‖ ^ 2 +
          h2WeightR3 ξ * ‖convR3 (fun η => u η 2) (fun η => v η 0) ξ‖ ^ 2) +
         (h2WeightR3 ξ * ‖convR3 (fun η => u η 0) (fun η => v η 1) ξ‖ ^ 2 +
          h2WeightR3 ξ * ‖convR3 (fun η => u η 1) (fun η => v η 1) ξ‖ ^ 2 +
          h2WeightR3 ξ * ‖convR3 (fun η => u η 2) (fun η => v η 1) ξ‖ ^ 2) +
         (h2WeightR3 ξ * ‖convR3 (fun η => u η 0) (fun η => v η 2) ξ‖ ^ 2 +
          h2WeightR3 ξ * ‖convR3 (fun η => u η 1) (fun η => v η 2) ξ‖ ^ 2 +
          h2WeightR3 ξ * ‖convR3 (fun η => u η 2) (fun η => v η 2) ξ‖ ^ 2)) :=
      fun ξ => by dsimp only [dom]; ring
    rw [r3Integral_congr hpt_d, r3Integral_const_mul,
        r3Integral_add3 (hrow 0) (hrow 1) (hrow 2),
        r3Integral_add3 (hconv 0 0).1.2 (hconv 1 0).1.2 (hconv 2 0).1.2,
        r3Integral_add3 (hconv 0 1).1.2 (hconv 1 1).1.2 (hconv 2 1).1.2,
        r3Integral_add3 (hconv 0 2).1.2 (hconv 1 2).1.2 (hconv 2 2).1.2]
    rfl
  rw [hdom_val] at hint_le
  have hsum_le :
      (h2NormSqR3 (convR3 (fun η => u η 0) (fun η => v η 0)) +
       h2NormSqR3 (convR3 (fun η => u η 1) (fun η => v η 0)) +
       h2NormSqR3 (convR3 (fun η => u η 2) (fun η => v η 0))) +
      (h2NormSqR3 (convR3 (fun η => u η 0) (fun η => v η 1)) +
       h2NormSqR3 (convR3 (fun η => u η 1) (fun η => v η 1)) +
       h2NormSqR3 (convR3 (fun η => u η 2) (fun η => v η 1))) +
      (h2NormSqR3 (convR3 (fun η => u η 0) (fun η => v η 2)) +
       h2NormSqR3 (convR3 (fun η => u η 1) (fun η => v η 2)) +
       h2NormSqR3 (convR3 (fun η => u η 2) (fun η => v η 2))) ≤
      16 * Real.pi ^ 2 * h2VecNormSqR3 u * h2VecNormSqR3 v := by
    unfold h2VecNormSqR3
    linarith [(hconv 0 0).2, (hconv 1 0).2, (hconv 2 0).2,
      (hconv 0 1).2, (hconv 1 1).2, (hconv 2 1).2,
      (hconv 0 2).2, (hconv 1 2).2, (hconv 2 2).2]
  have hmul := mul_le_mul_of_nonneg_left hsum_le (by positivity : (0 : ℝ) ≤ 1 / (2 * ν * τ))
  have hrhs : (1 / (2 * ν * τ)) * (16 * Real.pi ^ 2 * h2VecNormSqR3 u * h2VecNormSqR3 v) =
      (8 * Real.pi ^ 2 / (ν * τ)) * h2VecNormSqR3 u * h2VecNormSqR3 v := by
    field_simp [hν.ne', hτ.ne']; ring
  linarith

/-- **THEOREM 15D1-9 (Quadratic Lipschitz Bound for `heatSmoothedBilinearR3` in `H²(ℝ³)`):** -/
theorem heatSmoothedBilinearR3_self_sub_lipschitz
    {ν τ : ℝ} (hν : 0 < ν) (hτ : 0 < τ) {u v : VecFieldR3C} (hu : InH2VecR3 u) (hv : InH2VecR3 v) :
    InH2VecR3 (fun ξ c => heatSmoothedBilinearR3 ν τ u u ξ c - heatSmoothedBilinearR3 ν τ v v ξ c) ∧
    h2VecNormSqR3 (fun ξ c => heatSmoothedBilinearR3 ν τ u u ξ c - heatSmoothedBilinearR3 ν τ v v ξ c) ≤
      (16 * Real.pi ^ 2 / (ν * τ)) * (h2VecNormSqR3 u + h2VecNormSqR3 v) *
        h2VecNormSqR3 (fun ξ c => u ξ c - v ξ c) := by
  have hsub := (inH2VecR3_sub hu hv).1
  have h1 := heatSmoothedBilinearR3_inH2_and_bound hν hτ hsub hu
  have h2 := heatSmoothedBilinearR3_inH2_and_bound hν hτ hv hsub
  have hsplit : ∀ (ξ : R3) (c : Fin 3),
      heatSmoothedBilinearR3 ν τ u u ξ c - heatSmoothedBilinearR3 ν τ v v ξ c =
        heatSmoothedBilinearR3 ν τ (fun η j => u η j - v η j) u ξ c +
        heatSmoothedBilinearR3 ν τ v (fun η j => u η j - v η j) ξ c := by
    intro ξ c
    have hflux_split : ∀ j : Fin 3,
        nsFluxR3 u u ξ j - nsFluxR3 v v ξ j =
          nsFluxR3 (fun η k => u η k - v η k) u ξ j +
          nsFluxR3 v (fun η k => u η k - v η k) ξ j := by
      intro j; unfold nsFluxR3
      rw [convR3_sub_left (hu 0) (hv 0) (hu j) ξ, convR3_sub_left (hu 1) (hv 1) (hu j) ξ,
          convR3_sub_left (hu 2) (hv 2) (hu j) ξ,
          convR3_sub_right (hv 0) (hu j) (hv j) ξ, convR3_sub_right (hv 1) (hu j) (hv j) ξ,
          convR3_sub_right (hv 2) (hu j) (hv j) ξ]
      ring
    unfold heatSmoothedBilinearR3 nsBilinearR3
    have hlin_sub : lerayProjR3C ξ (nsFluxR3 u u ξ) c - lerayProjR3C ξ (nsFluxR3 v v ξ) c =
        lerayProjR3C ξ (nsFluxR3 (fun η k => u η k - v η k) u ξ) c +
        lerayProjR3C ξ (nsFluxR3 v (fun η k => u η k - v η k) ξ) c := by
      rw [← (lerayProjR3C_solenoidal_and_contraction ξ).2.2.2.2]
      have hfun : (fun j => nsFluxR3 u u ξ j - nsFluxR3 v v ξ j) =
          (fun j => nsFluxR3 (fun η k => u η k - v η k) u ξ j +
            nsFluxR3 v (fun η k => u η k - v η k) ξ j) := funext hflux_split
      rw [hfun, (lerayProjR3C_solenoidal_and_contraction ξ).2.2.2.1]
    linear_combination -(heatMultiplier3D ν τ ξ : ℂ) * hlin_sub
  have hfun_eq : (fun ξ c => heatSmoothedBilinearR3 ν τ u u ξ c - heatSmoothedBilinearR3 ν τ v v ξ c) =
      (fun ξ c => heatSmoothedBilinearR3 ν τ (fun η j => u η j - v η j) u ξ c +
        heatSmoothedBilinearR3 ν τ v (fun η j => u η j - v η j) ξ c) := by
    funext ξ c; exact hsplit ξ c
  rw [hfun_eq]
  have hadd := inH2VecR3_add h1.1 h2.1
  refine ⟨hadd.1, ?_⟩
  have hlin : 2 * ((8 * Real.pi ^ 2 / (ν * τ)) * h2VecNormSqR3 (fun ξ c => u ξ c - v ξ c) * h2VecNormSqR3 u) +
      2 * ((8 * Real.pi ^ 2 / (ν * τ)) * h2VecNormSqR3 v * h2VecNormSqR3 (fun ξ c => u ξ c - v ξ c)) =
      (16 * Real.pi ^ 2 / (ν * τ)) * (h2VecNormSqR3 u + h2VecNormSqR3 v) *
        h2VecNormSqR3 (fun ξ c => u ξ c - v ξ c) := by ring
  linarith [hadd.2, h1.2, h2.2]

/-- Reverse continuous 3D Fourier synthesis of a scalar frequency field `a ∈ H²(ℝ³; ℂ)`. -/
noncomputable def synthScalarR3 (a : R3 → ℂ) (x : R3) : ℝ :=
  (∫ ξ : R3, a ξ * Complex.exp ((dot3D x ξ : ℂ) * Complex.I)).re

/-- Reverse continuous 3D Fourier synthesis of a vector frequency field `u ∈ H²(ℝ³; ℂ³)`. -/
noncomputable def synthVecR3 (u : VecFieldR3C) (x : R3) : R3 :=
  fun c => synthScalarR3 (fun ξ => u ξ c) x

/-- **THEOREM 15D1-10 (Continuous Reverse Fourier Synthesis `H²(ℝ³) ↪ C⁰_b(ℝ³)` & Exact Bridge
    to `ConcreteNS3DClosures.fourierSynthR3`):**
    1. Scalar synthesis: `Continuous (synthScalarR3 a)`, `(synthScalarR3 a x)² ≤ π² h2NormSqR3 a`,
       and exact identity `synthScalarR3 a x = fourierSynthR3 (re a) (-im a) x`;
    2. Vector synthesis: `Continuous (synthVecR3 u)` and
       `dot3D (synthVecR3 u x) (synthVecR3 u x) ≤ π² h2VecNormSqR3 u`. -/
theorem synthVecR3_continuous_Linf_and_fourierSynth_bridge :
    (∀ {a : R3 → ℂ}, InH2R3 a →
      Continuous (synthScalarR3 a) ∧
      (∀ x : R3, (synthScalarR3 a x) ^ 2 ≤ Real.pi ^ 2 * h2NormSqR3 a) ∧
      (∀ x : R3, synthScalarR3 a x = fourierSynthR3 (fun ξ => (a ξ).re) (fun ξ => -(a ξ).im) x)) ∧
    (∀ {u : VecFieldR3C}, InH2VecR3 u →
      Continuous (synthVecR3 u) ∧
      (∀ x : R3, dot3D (synthVecR3 u x) (synthVecR3 u x) ≤ Real.pi ^ 2 * h2VecNormSqR3 u)) := by
  have hscalar : ∀ {a : R3 → ℂ}, InH2R3 a →
      Continuous (synthScalarR3 a) ∧
      (∀ x : R3, (synthScalarR3 a x) ^ 2 ≤ Real.pi ^ 2 * h2NormSqR3 a) ∧
      (∀ x : R3, synthScalarR3 a x = fourierSynthR3 (fun ξ => (a ξ).re) (fun ξ => -(a ξ).im) x) := by
    intro a ha
    have hal1 := h2R3_l1_embedding ha
    have hexp_norm : ∀ (x ξ : R3), ‖Complex.exp ((dot3D x ξ : ℂ) * Complex.I)‖ = 1 := fun x ξ =>
      Complex.norm_exp_ofReal_mul_I (dot3D x ξ)
    have hcontC : Continuous (fun x : R3 => ∫ ξ : R3, a ξ * Complex.exp ((dot3D x ξ : ℂ) * Complex.I)) := by
      refine MeasureTheory.continuous_of_dominated (bound := fun ξ => ‖a ξ‖) ?_ ?_ hal1.1 ?_
      · intro x
        have he_c : Continuous (fun ξ : R3 => Complex.exp ((dot3D x ξ : ℂ) * Complex.I)) :=
          Complex.continuous_exp.comp ((Complex.continuous_ofReal.comp (by unfold dot3D; fun_prop)).mul continuous_const)
        exact ha.1.mul he_c.aestronglyMeasurable
      · intro x
        exact Filter.Eventually.of_forall fun ξ => by rw [norm_mul, hexp_norm, mul_one]
      · exact Filter.Eventually.of_forall fun ξ =>
          continuous_const.mul (Complex.continuous_exp.comp
            ((Complex.continuous_ofReal.comp (by unfold dot3D; fun_prop)).mul continuous_const))
    have hcont : Continuous (synthScalarR3 a) := Complex.continuous_re.comp hcontC
    have hLinf : ∀ x : R3, (synthScalarR3 a x) ^ 2 ≤ Real.pi ^ 2 * h2NormSqR3 a := by
      intro x
      have habs : |synthScalarR3 a x| ≤ r3Integral (fun ξ => ‖a ξ‖) := by
        unfold synthScalarR3 r3Integral
        calc |(∫ ξ : R3, a ξ * Complex.exp ((dot3D x ξ : ℂ) * Complex.I)).re|
            ≤ ‖∫ ξ : R3, a ξ * Complex.exp ((dot3D x ξ : ℂ) * Complex.I)‖ := Complex.abs_re_le_norm _
          _ ≤ ∫ ξ : R3, ‖a ξ * Complex.exp ((dot3D x ξ : ℂ) * Complex.I)‖ := norm_integral_le_integral_norm _
          _ = ∫ ξ : R3, ‖a ξ‖ := integral_congr_ae (Filter.Eventually.of_forall fun ξ => by
                dsimp only; rw [norm_mul, hexp_norm, mul_one])
      have hsq : (synthScalarR3 a x) ^ 2 ≤ (r3Integral (fun ξ => ‖a ξ‖)) ^ 2 := by
        rw [← sq_abs]
        nlinarith [abs_nonneg (synthScalarR3 a x), r3Integral_nonneg fun ξ => norm_nonneg (a ξ)]
      exact le_trans hsq hal1.2
    have hbridge : ∀ x : R3,
        synthScalarR3 a x = fourierSynthR3 (fun ξ => (a ξ).re) (fun ξ => -(a ξ).im) x := by
      intro x
      have hint_x : Integrable (fun ξ : R3 => a ξ * Complex.exp ((dot3D x ξ : ℂ) * Complex.I)) volume := by
        have he_c : Continuous (fun ξ : R3 => Complex.exp ((dot3D x ξ : ℂ) * Complex.I)) :=
          Complex.continuous_exp.comp ((Complex.continuous_ofReal.comp (by unfold dot3D; fun_prop)).mul continuous_const)
        exact hal1.1.mono' (ha.1.mul he_c.aestronglyMeasurable)
          (Filter.Eventually.of_forall fun ξ => by rw [norm_mul, hexp_norm, mul_one])
      have hre := (Complex.reCLM.integral_comp_comm hint_x).symm
      change synthScalarR3 a x = ∫ ξ : R3, (a ξ * Complex.exp ((dot3D x ξ : ℂ) * Complex.I)).re at hre
      rw [hre]
      unfold fourierSynthR3 r3Integral
      refine integral_congr_ae (Filter.Eventually.of_forall fun ξ => ?_)
      dsimp only
      rw [Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
      simp only [Complex.mul_re, Complex.add_re, Complex.add_im, Complex.mul_im,
        Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im]
      ring
    exact ⟨hcont, hLinf, hbridge⟩
  refine ⟨fun ha => hscalar ha, fun {u} hu => ?_⟩
  refine ⟨continuous_pi fun c => (hscalar (hu c)).1, fun x => ?_⟩
  unfold dot3D synthVecR3 h2VecNormSqR3
  have h0 := (hscalar (hu 0)).2.1 x
  have h1 := (hscalar (hu 1)).2.1 x
  have h2 := (hscalar (hu 2)).2.1 x
  linarith [show synthScalarR3 (fun ξ => u ξ 0) x * synthScalarR3 (fun ξ => u ξ 0) x =
      (synthScalarR3 (fun ξ => u ξ 0) x) ^ 2 by ring,
    show synthScalarR3 (fun ξ => u ξ 1) x * synthScalarR3 (fun ξ => u ξ 1) x =
      (synthScalarR3 (fun ξ => u ξ 1) x) ^ 2 by ring,
    show synthScalarR3 (fun ξ => u ξ 2) x * synthScalarR3 (fun ξ => u ξ 2) x =
      (synthScalarR3 (fun ξ => u ξ 2) x) ^ 2 by ring]

-- ============================================================================
-- SECTION 2 (MILESTONE 15D-2A): CONTINUOUS ℝ³ DUHAMEL OPERATOR Φ,
--   WEIGHTED PARABOLIC INTEGRAL BOUND (4 t K), SELF-MAP & 1/4-CONTRACTION
-- ============================================================================

/-- Time clamp onto `[0, T]` ensuring global boundedness and continuity on `ℝ`. -/
def clampTR3 (T t : ℝ) : ℝ := max 0 (min T t)

lemma continuous_clampTR3 (T : ℝ) : Continuous (clampTR3 T) :=
  continuous_const.max (continuous_const.min continuous_id)

lemma clampTR3_mem_Icc {T : ℝ} (hT : 0 ≤ T) (t : ℝ) : clampTR3 T t ∈ Set.Icc 0 T :=
  ⟨le_max_left 0 _, max_le hT (min_le_left T t)⟩

lemma clampTR3_eq_self {T t : ℝ} (ht : t ∈ Set.Icc 0 T) : clampTR3 T t = t := by
  unfold clampTR3; rw [min_eq_right ht.2, max_eq_right ht.1]

/-- Explicit whole-space `ℝ³` local `H²` existence horizon:
    `T_loc(M, ν) = ν / (512 π² (4 M + 1)) > 0`. -/
noncomputable def localHorizonH2R3 (ν M : ℝ) : ℝ :=
  ν / (512 * Real.pi ^ 2 * (4 * M + 1))

lemma localHorizonH2R3_pos {ν M : ℝ} (hν : 0 < ν) (hM : 0 ≤ M) :
    0 < localHorizonH2R3 ν M := by
  unfold localHorizonH2R3; positivity

lemma localHorizonH2R3_antitone {ν M₁ M₂ : ℝ} (hν : 0 < ν) (hM₁ : 0 ≤ M₁) (hle : M₁ ≤ M₂) :
    localHorizonH2R3 ν M₂ ≤ localHorizonH2R3 ν M₁ := by
  unfold localHorizonH2R3
  exact div_le_div_of_nonneg_left hν.le (by positivity) (by nlinarith [sq_pos_of_pos Real.pi_pos])

/-- **THEOREM 15D2-1 (Core Weighted Parabolic `H²(ℝ³)` Integral Estimate — `4 t K`):**
    If `G : ℝ → VecFieldR3C` is continuous in `s` for every `(ξ, c)`, jointly measurable
    on `(0, t] × ℝ³`, and satisfies `h2VecNormSqR3 (G s) ≤ K / (t - s)` for all `s ∈ [0, t)`,
    then `∫_0^t G(s) ds ∈ H²(ℝ³)` with `h2VecNormSqR3 (∫_0^t G(s) ds) ≤ 4 t K`. -/
theorem integral_h2R3_bound_of_inv_sqrt_decay
    {t K : ℝ} (ht : 0 ≤ t) (hK : 0 ≤ K) {G : ℝ → VecFieldR3C}
    (hG_cont : ∀ (ξ : R3) (c : Fin 3), Continuous (fun s : ℝ => G s ξ c))
    (hG_joint : ∀ c : Fin 3,
      AEStronglyMeasurable (fun p : ℝ × R3 => G p.1 p.2 c)
        ((volume.restrict (Set.Ioc (0 : ℝ) t)).prod volume))
    (hG_bound : ∀ s ∈ Set.Ico (0 : ℝ) t, InH2VecR3 (G s) ∧ h2VecNormSqR3 (G s) ≤ K / (t - s)) :
    InH2VecR3 (fun ξ c => ∫ s in (0 : ℝ)..t, G s ξ c) ∧
    h2VecNormSqR3 (fun ξ c => ∫ s in (0 : ℝ)..t, G s ξ c) ≤ 4 * t * K := by
  by_cases ht0 : t = 0
  · subst ht0
    have hzero : (fun (ξ : R3) (c : Fin 3) => ∫ s in (0 : ℝ)..0, G s ξ c) = fun _ _ => 0 := by
      funext ξ c; exact intervalIntegral.integral_same
    rw [hzero]
    refine ⟨fun _ => ⟨aestronglyMeasurable_const, ?_⟩, ?_⟩
    · simp only [norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero]
      exact integrable_zero _ _ _
    · unfold h2VecNormSqR3 h2NormSqR3
      simp only [norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero,
        r3Integral_zero, add_zero, zero_mul, le_refl]
  · have ht_pos : 0 < t := lt_of_le_of_ne ht (Ne.symm ht0)
    let μt : Measure ℝ := volume.restrict (Set.Ioc (0 : ℝ) t)
    have hG_aem_int : ∀ c : Fin 3,
        AEStronglyMeasurable (fun ξ : R3 => ∫ s in (0 : ℝ)..t, G s ξ c) volume := by
      intro c
      have hsm := (hG_joint c).stronglyMeasurable_mk.integral_prod_left' (μ := μt)
      have hae_eq : ∀ᵐ ξ ∂volume,
          (∫ s in (0 : ℝ)..t, G s ξ c) =
            ∫ s, (hG_joint c).mk (fun p : ℝ × R3 => G p.1 p.2 c) (s, ξ) ∂μt := by
        have hsw := (Measure.measurePreserving_swap (μ := volume) (ν := μt)).quasiMeasurePreserving.ae_eq_comp
          (hG_joint c).ae_eq_mk
        exact (Measure.ae_ae_of_ae_prod hsw).mono fun ξ hξ => by
          rw [intervalIntegral.integral_of_le ht]
          exact integral_congr_ae hξ
      exact hsm.aestronglyMeasurable.congr (hae_eq.mono fun _ h => h.symm)
    have hint_inv_sqrt : (∫⁻ s in Set.Ioc (0 : ℝ) t, ENNReal.ofReal ((Real.sqrt (t - s))⁻¹)) =
        ENNReal.ofReal (2 * Real.sqrt t) := by
      have h1 : IntervalIntegrable (fun s : ℝ => (Real.sqrt (t - s))⁻¹) volume 0 t := by
        have hsub : IntervalIntegrable (fun u : ℝ => u ^ (-(1 / 2 : ℝ))) volume 0 t :=
          intervalIntegral.intervalIntegrable_rpow' (by norm_num)
        have hcomp := hsub.comp_sub_left t
        simp only [sub_zero, sub_self] at hcomp
        exact hcomp.symm.congr fun s hs => by
          rw [Set.uIoc_of_le ht] at hs
          rw [Real.sqrt_eq_rpow, ← Real.rpow_neg (by linarith [hs.2])]
      have h_i : IntegrableOn (fun s : ℝ => (Real.sqrt (t - s))⁻¹) (Set.Ioc 0 t) volume :=
        (intervalIntegrable_iff_integrableOn_Ioc_of_le ht).1 h1
      rw [← ofReal_integral_eq_lintegral_ofReal h_i
        (Filter.Eventually.of_forall fun s => inv_nonneg.2 (Real.sqrt_nonneg _))]
      congr 1
      rw [← intervalIntegral.integral_of_le ht]
      have hsub : (∫ s in (0 : ℝ)..t, (Real.sqrt (t - s))⁻¹) = ∫ u in (0 : ℝ)..t, u ^ (-(1 / 2 : ℝ)) := by
        have hc := intervalIntegral.integral_comp_sub_left (fun u : ℝ => u ^ (-(1 / 2 : ℝ))) t (a := 0) (b := t)
        simp only [sub_zero, sub_self] at hc
        rw [← hc]
        refine intervalIntegral.integral_congr fun s hs => ?_
        rw [Set.uIcc_of_le ht] at hs
        rw [Real.sqrt_eq_rpow, ← Real.rpow_neg (by linarith [hs.2])]
      rw [hsub, integral_rpow (Or.inl (by norm_num))]
      rw [Real.zero_rpow (by norm_num), sub_zero, Real.sqrt_eq_rpow]
      norm_num; ring
    have hpt_cs : ∀ (c : Fin 3) (ξ : R3),
        ENNReal.ofReal (h2WeightR3 ξ * ‖∫ s in (0 : ℝ)..t, G s ξ c‖ ^ 2) ≤
          ENNReal.ofReal (2 * Real.sqrt t) *
            ∫⁻ s in Set.Ioc (0 : ℝ) t,
              ENNReal.ofReal (Real.sqrt (t - s)) * ENNReal.ofReal (h2WeightR3 ξ * ‖G s ξ c‖ ^ 2) := by
      intro c ξ
      have h1 : ENNReal.ofReal ‖∫ s in (0 : ℝ)..t, G s ξ c‖ ≤
          ∫⁻ s in Set.Ioc (0 : ℝ) t, ENNReal.ofReal ‖G s ξ c‖ := by
        rw [intervalIntegral.integral_of_le ht]
        calc ENNReal.ofReal ‖∫ s in Set.Ioc (0 : ℝ) t, G s ξ c‖
            = ‖∫ s in Set.Ioc (0 : ℝ) t, G s ξ c‖ₑ := ofReal_norm _
          _ ≤ ∫⁻ s in Set.Ioc (0 : ℝ) t, ‖G s ξ c‖ₑ := eNorm_integral_le_lintegral_eNorm _
          _ = ∫⁻ s in Set.Ioc (0 : ℝ) t, ENNReal.ofReal ‖G s ξ c‖ :=
              lintegral_congr fun s => (ofReal_norm _).symm
      have hae_ioo : ∀ᵐ s ∂μt, s ∈ Set.Ioo (0 : ℝ) t := by
        rw [ae_iff]
        have hsub : {s : ℝ | ¬s ∈ Set.Ioo 0 t} ∩ Set.Ioc 0 t ⊆ {t} := by
          intro s ⟨hn, h0, hle⟩; simp only [Set.mem_singleton_iff]
          exact le_antisymm hle (by by_contra hlt; exact hn ⟨h0, lt_of_le_of_ne hle (ne_of_lt (not_le.1 hlt))⟩)
        rw [Measure.restrict_apply' measurableSet_Ioc]
        exact measure_mono_null hsub (by simp)
      have hae_split : ∀ᵐ s ∂μt,
          ENNReal.ofReal ‖G s ξ c‖ =
            esqrt15d (ENNReal.ofReal ((Real.sqrt (t - s))⁻¹)) *
            esqrt15d (ENNReal.ofReal (Real.sqrt (t - s) * ‖G s ξ c‖ ^ 2)) :=
        hae_ioo.mono fun s hs => by
          have hts_pos : 0 < Real.sqrt (t - s) := Real.sqrt_pos.2 (sub_pos.2 hs.2)
          rw [esqrt15d_ofReal (inv_nonneg.2 hts_pos.le),
              esqrt15d_ofReal (mul_nonneg hts_pos.le (sq_nonneg _)),
              ← ENNReal.ofReal_mul (Real.sqrt_nonneg _)]
          congr 1
          rw [← Real.sqrt_mul (inv_nonneg.2 hts_pos.le), ← mul_assoc,
              inv_mul_cancel₀ hts_pos.ne', one_mul, Real.sqrt_sq (norm_nonneg _)]
      have hF_m : AEMeasurable (fun s : ℝ => ENNReal.ofReal ((Real.sqrt (t - s))⁻¹)) μt :=
        (ENNReal.continuous_ofReal.measurable.comp
          ((Real.continuous_sqrt.comp (continuous_const.sub continuous_id)).measurable.inv)).aemeasurable
      have hG_m : AEMeasurable (fun s : ℝ => ENNReal.ofReal (Real.sqrt (t - s) * ‖G s ξ c‖ ^ 2)) μt :=
        (ENNReal.continuous_ofReal.comp
          ((Real.continuous_sqrt.comp (continuous_const.sub continuous_id)).mul
            (((hG_cont ξ c).norm).pow 2))).measurable.aemeasurable
      have hcs := lintegral_cs_esqrt_15d μt hF_m hG_m
      rw [← lintegral_congr_ae hae_split] at hcs
      have hsq : ENNReal.ofReal (‖∫ s in (0 : ℝ)..t, G s ξ c‖ ^ 2) ≤
          ENNReal.ofReal (2 * Real.sqrt t) *
            ∫⁻ s in Set.Ioc (0 : ℝ) t, ENNReal.ofReal (Real.sqrt (t - s) * ‖G s ξ c‖ ^ 2) := by
        rw [ENNReal.ofReal_pow (norm_nonneg _)]
        have hle := le_trans h1 hcs
        calc (ENNReal.ofReal ‖∫ s in (0 : ℝ)..t, G s ξ c‖) ^ 2
            ≤ (esqrt15d (∫⁻ s in Set.Ioc (0 : ℝ) t, ENNReal.ofReal ((Real.sqrt (t - s))⁻¹)) *
               esqrt15d (∫⁻ s in Set.Ioc (0 : ℝ) t, ENNReal.ofReal (Real.sqrt (t - s) * ‖G s ξ c‖ ^ 2))) ^ 2 :=
              pow_le_pow_left' hle 2
          _ = (esqrt15d (∫⁻ s in Set.Ioc (0 : ℝ) t, ENNReal.ofReal ((Real.sqrt (t - s))⁻¹))) ^ 2 *
              (esqrt15d (∫⁻ s in Set.Ioc (0 : ℝ) t, ENNReal.ofReal (Real.sqrt (t - s) * ‖G s ξ c‖ ^ 2))) ^ 2 :=
              mul_pow _ _ 2
          _ = ENNReal.ofReal (2 * Real.sqrt t) *
              ∫⁻ s in Set.Ioc (0 : ℝ) t, ENNReal.ofReal (Real.sqrt (t - s) * ‖G s ξ c‖ ^ 2) := by
              rw [esqrt15d_sq, esqrt15d_sq, hint_inv_sqrt]
      rw [ENNReal.ofReal_mul (h2WeightR3_pos ξ).le]
      calc ENNReal.ofReal (h2WeightR3 ξ) * ENNReal.ofReal (‖∫ s in (0 : ℝ)..t, G s ξ c‖ ^ 2)
          ≤ ENNReal.ofReal (h2WeightR3 ξ) *
              (ENNReal.ofReal (2 * Real.sqrt t) *
                ∫⁻ s in Set.Ioc (0 : ℝ) t, ENNReal.ofReal (Real.sqrt (t - s) * ‖G s ξ c‖ ^ 2)) :=
            mul_le_mul' le_rfl hsq
        _ = ENNReal.ofReal (2 * Real.sqrt t) *
              (ENNReal.ofReal (h2WeightR3 ξ) *
                ∫⁻ s in Set.Ioc (0 : ℝ) t, ENNReal.ofReal (Real.sqrt (t - s) * ‖G s ξ c‖ ^ 2)) := by ring
        _ = ENNReal.ofReal (2 * Real.sqrt t) *
              ∫⁻ s in Set.Ioc (0 : ℝ) t,
                ENNReal.ofReal (Real.sqrt (t - s)) * ENNReal.ofReal (h2WeightR3 ξ * ‖G s ξ c‖ ^ 2) := by
            congr 1
            rw [← lintegral_const_mul' (ENNReal.ofReal (h2WeightR3 ξ)) _ ENNReal.ofReal_ne_top]
            refine lintegral_congr fun s => ?_
            rw [← ENNReal.ofReal_mul (h2WeightR3_pos ξ).le,
                ← ENNReal.ofReal_mul (Real.sqrt_nonneg _)]
            congr 1; ring
    have hton_c : ∀ c : Fin 3,
        (∫⁻ ξ : R3, ENNReal.ofReal (h2WeightR3 ξ * ‖∫ s in (0 : ℝ)..t, G s ξ c‖ ^ 2)) ≤
          ENNReal.ofReal (2 * Real.sqrt t) *
            ∫⁻ s in Set.Ioc (0 : ℝ) t,
              ENNReal.ofReal (Real.sqrt (t - s)) *
                ∫⁻ ξ : R3, ENNReal.ofReal (h2WeightR3 ξ * ‖G s ξ c‖ ^ 2) := by
      intro c
      have hprod_m : AEMeasurable
          (fun p : ℝ × R3 => ENNReal.ofReal (Real.sqrt (t - p.1)) *
            ENNReal.ofReal (h2WeightR3 p.2 * ‖G p.1 p.2 c‖ ^ 2)) (μt.prod volume) := by
        have h1 : AEMeasurable (fun p : ℝ × R3 => ENNReal.ofReal (Real.sqrt (t - p.1))) (μt.prod volume) :=
          (ENNReal.continuous_ofReal.comp
            (Real.continuous_sqrt.comp (continuous_const.sub continuous_fst))).measurable.aemeasurable
        have h2 : AEMeasurable (fun p : ℝ × R3 => ENNReal.ofReal (h2WeightR3 p.2 * ‖G p.1 p.2 c‖ ^ 2))
            (μt.prod volume) :=
          ENNReal.continuous_ofReal.measurable.comp_aemeasurable
            ((h2WeightR3_continuous.comp continuous_snd).measurable.aemeasurable.mul
              (((hG_joint c).norm.pow 2).aemeasurable))
        exact h1.mul h2
      calc (∫⁻ ξ : R3, ENNReal.ofReal (h2WeightR3 ξ * ‖∫ s in (0 : ℝ)..t, G s ξ c‖ ^ 2))
          ≤ ∫⁻ ξ : R3, ENNReal.ofReal (2 * Real.sqrt t) *
              ∫⁻ s in Set.Ioc (0 : ℝ) t,
                ENNReal.ofReal (Real.sqrt (t - s)) * ENNReal.ofReal (h2WeightR3 ξ * ‖G s ξ c‖ ^ 2) :=
            lintegral_mono (hpt_cs c)
        _ = ENNReal.ofReal (2 * Real.sqrt t) *
              ∫⁻ ξ : R3, ∫⁻ s in Set.Ioc (0 : ℝ) t,
                ENNReal.ofReal (Real.sqrt (t - s)) * ENNReal.ofReal (h2WeightR3 ξ * ‖G s ξ c‖ ^ 2) :=
            lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
        _ = ENNReal.ofReal (2 * Real.sqrt t) *
              ∫⁻ s in Set.Ioc (0 : ℝ) t, ∫⁻ ξ : R3,
                ENNReal.ofReal (Real.sqrt (t - s)) * ENNReal.ofReal (h2WeightR3 ξ * ‖G s ξ c‖ ^ 2) := by
            congr 1
            rw [← lintegral_prod_symm _ hprod_m, lintegral_prod _ hprod_m]
        _ = ENNReal.ofReal (2 * Real.sqrt t) *
              ∫⁻ s in Set.Ioc (0 : ℝ) t,
                ENNReal.ofReal (Real.sqrt (t - s)) *
                  ∫⁻ ξ : R3, ENNReal.ofReal (h2WeightR3 ξ * ‖G s ξ c‖ ^ 2) := by
            congr 1
            exact lintegral_congr fun s => lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    have hsum_lint :
        (∫⁻ ξ : R3, ENNReal.ofReal (h2WeightR3 ξ * ‖∫ s in (0 : ℝ)..t, G s ξ 0‖ ^ 2)) +
        (∫⁻ ξ : R3, ENNReal.ofReal (h2WeightR3 ξ * ‖∫ s in (0 : ℝ)..t, G s ξ 1‖ ^ 2)) +
        (∫⁻ ξ : R3, ENNReal.ofReal (h2WeightR3 ξ * ‖∫ s in (0 : ℝ)..t, G s ξ 2‖ ^ 2)) ≤
          ENNReal.ofReal (4 * t * K) := by
      have hae_ioo : ∀ᵐ s ∂μt, s ∈ Set.Ioo (0 : ℝ) t := by
        rw [ae_iff]
        have hsub : {s : ℝ | ¬s ∈ Set.Ioo 0 t} ∩ Set.Ioc 0 t ⊆ {t} := by
          intro s ⟨hn, h0, hle⟩; simp only [Set.mem_singleton_iff]
          exact le_antisymm hle (by by_contra hlt; exact hn ⟨h0, lt_of_le_of_ne hle (ne_of_lt (not_le.1 hlt))⟩)
        rw [Measure.restrict_apply' measurableSet_Ioc]
        exact measure_mono_null hsub (by simp)
      have hsum_s : ∀ᵐ s ∂μt,
          ENNReal.ofReal (Real.sqrt (t - s)) *
            ((∫⁻ ξ : R3, ENNReal.ofReal (h2WeightR3 ξ * ‖G s ξ 0‖ ^ 2)) +
             (∫⁻ ξ : R3, ENNReal.ofReal (h2WeightR3 ξ * ‖G s ξ 1‖ ^ 2)) +
             (∫⁻ ξ : R3, ENNReal.ofReal (h2WeightR3 ξ * ‖G s ξ 2‖ ^ 2))) ≤
          ENNReal.ofReal K * ENNReal.ofReal ((Real.sqrt (t - s))⁻¹) :=
        hae_ioo.mono fun s hs => by
          obtain ⟨hinH2, hbd⟩ := hG_bound s ⟨hs.1.le, hs.2⟩
          have hc_eq : ∀ c : Fin 3,
              (∫⁻ ξ : R3, ENNReal.ofReal (h2WeightR3 ξ * ‖G s ξ c‖ ^ 2)) =
                ENNReal.ofReal (h2NormSqR3 (fun ξ => G s ξ c)) := fun c =>
            (ofReal_integral_eq_lintegral_ofReal (hinH2 c).2
              (Filter.Eventually.of_forall fun ξ => mul_nonneg (h2WeightR3_pos ξ).le (sq_nonneg _))).symm
          rw [hc_eq 0, hc_eq 1, hc_eq 2,
              ← ENNReal.ofReal_add (h2NormSqR3_nonneg _) (h2NormSqR3_nonneg _),
              ← ENNReal.ofReal_add (add_nonneg (h2NormSqR3_nonneg _) (h2NormSqR3_nonneg _)) (h2NormSqR3_nonneg _)]
          change ENNReal.ofReal (Real.sqrt (t - s)) * ENNReal.ofReal (h2VecNormSqR3 (G s)) ≤ _
          rw [← ENNReal.ofReal_mul (Real.sqrt_nonneg _), ← ENNReal.ofReal_mul hK]
          apply ENNReal.ofReal_le_ofReal
          have hts_pos : 0 < t - s := sub_pos.2 hs.2
          have hsq : Real.sqrt (t - s) * (K / (t - s)) = K * (Real.sqrt (t - s))⁻¹ := by
            have hspos : 0 < Real.sqrt (t - s) := Real.sqrt_pos.2 hts_pos
            have hssq : (Real.sqrt (t - s)) ^ 2 = t - s := Real.sq_sqrt hts_pos.le
            field_simp [hspos.ne', hts_pos.ne']
            nlinarith
          calc Real.sqrt (t - s) * h2VecNormSqR3 (G s)
              ≤ Real.sqrt (t - s) * (K / (t - s)) := mul_le_mul_of_nonneg_left hbd (Real.sqrt_nonneg _)
            _ = K * (Real.sqrt (t - s))⁻¹ := hsq
      have hterm_m : ∀ c : Fin 3, AEMeasurable
          (fun s : ℝ => ENNReal.ofReal (Real.sqrt (t - s)) *
            ∫⁻ ξ : R3, ENNReal.ofReal (h2WeightR3 ξ * ‖G s ξ c‖ ^ 2)) μt := fun c => by
        have h1 : AEMeasurable (fun s : ℝ => ENNReal.ofReal (Real.sqrt (t - s))) μt :=
          (ENNReal.continuous_ofReal.comp
            (Real.continuous_sqrt.comp (continuous_const.sub continuous_id))).measurable.aemeasurable
        have h2 : AEMeasurable (fun p : ℝ × R3 => ENNReal.ofReal (h2WeightR3 p.2 * ‖G p.1 p.2 c‖ ^ 2))
            (μt.prod volume) :=
          ENNReal.continuous_ofReal.measurable.comp_aemeasurable
            ((h2WeightR3_continuous.comp continuous_snd).measurable.aemeasurable.mul
              (((hG_joint c).norm.pow 2).aemeasurable))
        exact h1.mul h2.lintegral_prod_right'
      have hadd_t :
          (∫⁻ s in Set.Ioc (0 : ℝ) t, ENNReal.ofReal (Real.sqrt (t - s)) *
            ∫⁻ ξ : R3, ENNReal.ofReal (h2WeightR3 ξ * ‖G s ξ 0‖ ^ 2)) +
          (∫⁻ s in Set.Ioc (0 : ℝ) t, ENNReal.ofReal (Real.sqrt (t - s)) *
            ∫⁻ ξ : R3, ENNReal.ofReal (h2WeightR3 ξ * ‖G s ξ 1‖ ^ 2)) +
          (∫⁻ s in Set.Ioc (0 : ℝ) t, ENNReal.ofReal (Real.sqrt (t - s)) *
            ∫⁻ ξ : R3, ENNReal.ofReal (h2WeightR3 ξ * ‖G s ξ 2‖ ^ 2)) =
          ∫⁻ s in Set.Ioc (0 : ℝ) t,
            ENNReal.ofReal (Real.sqrt (t - s)) *
              ((∫⁻ ξ : R3, ENNReal.ofReal (h2WeightR3 ξ * ‖G s ξ 0‖ ^ 2)) +
               (∫⁻ ξ : R3, ENNReal.ofReal (h2WeightR3 ξ * ‖G s ξ 1‖ ^ 2)) +
               (∫⁻ ξ : R3, ENNReal.ofReal (h2WeightR3 ξ * ‖G s ξ 2‖ ^ 2))) := by
        have h01 : AEMeasurable (fun s : ℝ =>
            (ENNReal.ofReal (Real.sqrt (t - s)) * ∫⁻ ξ : R3, ENNReal.ofReal (h2WeightR3 ξ * ‖G s ξ 0‖ ^ 2)) +
            (ENNReal.ofReal (Real.sqrt (t - s)) * ∫⁻ ξ : R3, ENNReal.ofReal (h2WeightR3 ξ * ‖G s ξ 1‖ ^ 2))) μt :=
          (hterm_m 0).add (hterm_m 1)
        rw [← lintegral_add_left' (hterm_m 0), ← lintegral_add_left' h01]
        refine lintegral_congr fun s => by ring
      have hbound_int :
          (∫⁻ s in Set.Ioc (0 : ℝ) t,
            ENNReal.ofReal (Real.sqrt (t - s)) *
              ((∫⁻ ξ : R3, ENNReal.ofReal (h2WeightR3 ξ * ‖G s ξ 0‖ ^ 2)) +
               (∫⁻ ξ : R3, ENNReal.ofReal (h2WeightR3 ξ * ‖G s ξ 1‖ ^ 2)) +
               (∫⁻ ξ : R3, ENNReal.ofReal (h2WeightR3 ξ * ‖G s ξ 2‖ ^ 2)))) ≤
          ENNReal.ofReal K * ENNReal.ofReal (2 * Real.sqrt t) := by
        calc _ ≤ ∫⁻ s in Set.Ioc (0 : ℝ) t, ENNReal.ofReal K * ENNReal.ofReal ((Real.sqrt (t - s))⁻¹) :=
              lintegral_mono_ae hsum_s
          _ = ENNReal.ofReal K * ENNReal.ofReal (2 * Real.sqrt t) := by
              rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, hint_inv_sqrt]
      calc _ ≤ ENNReal.ofReal (2 * Real.sqrt t) *
              ((∫⁻ s in Set.Ioc (0 : ℝ) t, ENNReal.ofReal (Real.sqrt (t - s)) *
                  ∫⁻ ξ : R3, ENNReal.ofReal (h2WeightR3 ξ * ‖G s ξ 0‖ ^ 2)) +
               (∫⁻ s in Set.Ioc (0 : ℝ) t, ENNReal.ofReal (Real.sqrt (t - s)) *
                  ∫⁻ ξ : R3, ENNReal.ofReal (h2WeightR3 ξ * ‖G s ξ 1‖ ^ 2)) +
               (∫⁻ s in Set.Ioc (0 : ℝ) t, ENNReal.ofReal (Real.sqrt (t - s)) *
                  ∫⁻ ξ : R3, ENNReal.ofReal (h2WeightR3 ξ * ‖G s ξ 2‖ ^ 2))) := by
            have h0 := hton_c 0; have h1 := hton_c 1; have h2 := hton_c 2
            calc _ ≤ _ + _ + _ := add_le_add (add_le_add h0 h1) h2
              _ = _ := by ring
        _ = ENNReal.ofReal (2 * Real.sqrt t) *
              ∫⁻ s in Set.Ioc (0 : ℝ) t,
                ENNReal.ofReal (Real.sqrt (t - s)) *
                  ((∫⁻ ξ : R3, ENNReal.ofReal (h2WeightR3 ξ * ‖G s ξ 0‖ ^ 2)) +
                   (∫⁻ ξ : R3, ENNReal.ofReal (h2WeightR3 ξ * ‖G s ξ 1‖ ^ 2)) +
                   (∫⁻ ξ : R3, ENNReal.ofReal (h2WeightR3 ξ * ‖G s ξ 2‖ ^ 2))) := by rw [hadd_t]
        _ ≤ ENNReal.ofReal (2 * Real.sqrt t) * (ENNReal.ofReal K * ENNReal.ofReal (2 * Real.sqrt t)) :=
            mul_le_mul' le_rfl hbound_int
        _ = ENNReal.ofReal (4 * t * K) := by
            rw [← ENNReal.ofReal_mul hK, ← ENNReal.ofReal_mul (by positivity)]
            congr 1
            have hsq : (Real.sqrt t) ^ 2 = t := Real.sq_sqrt ht
            nlinarith
    have hinH2 : InH2VecR3 (fun ξ c => ∫ s in (0 : ℝ)..t, G s ξ c) := fun c => by
      refine ⟨hG_aem_int c, ⟨h2WeightR3_continuous.aestronglyMeasurable.mul ((hG_aem_int c).norm.pow 2), ?_⟩⟩
      change (∫⁻ ξ : R3, ‖h2WeightR3 ξ * ‖∫ s in (0 : ℝ)..t, G s ξ c‖ ^ 2‖ₑ) < ⊤
      have heq : (fun ξ : R3 => ‖h2WeightR3 ξ * ‖∫ s in (0 : ℝ)..t, G s ξ c‖ ^ 2‖ₑ) =
          (fun ξ : R3 => ENNReal.ofReal (h2WeightR3 ξ * ‖∫ s in (0 : ℝ)..t, G s ξ c‖ ^ 2)) := by
        funext ξ; rw [← ofReal_norm, Real.norm_of_nonneg (mul_nonneg (h2WeightR3_pos ξ).le (sq_nonneg _))]
      rw [heq]
      have hle_sum : (∫⁻ ξ : R3, ENNReal.ofReal (h2WeightR3 ξ * ‖∫ s in (0 : ℝ)..t, G s ξ c‖ ^ 2)) ≤
          ENNReal.ofReal (4 * t * K) := by
        fin_cases c
        · exact le_trans (le_trans le_self_add le_self_add) hsum_lint
        · exact le_trans (le_trans le_add_self le_self_add) hsum_lint
        · exact le_trans le_add_self hsum_lint
      exact lt_of_le_of_lt hle_sum ENNReal.ofReal_lt_top
    refine ⟨hinH2, ?_⟩
    have hc_eq : ∀ c : Fin 3,
        ENNReal.ofReal (h2NormSqR3 (fun ξ => ∫ s in (0 : ℝ)..t, G s ξ c)) =
          ∫⁻ ξ : R3, ENNReal.ofReal (h2WeightR3 ξ * ‖∫ s in (0 : ℝ)..t, G s ξ c‖ ^ 2) := fun c =>
      ofReal_integral_eq_lintegral_ofReal (hinH2 c).2
        (Filter.Eventually.of_forall fun ξ => mul_nonneg (h2WeightR3_pos ξ).le (sq_nonneg _))
    have hle_enn : ENNReal.ofReal (h2VecNormSqR3 (fun ξ c => ∫ s in (0 : ℝ)..t, G s ξ c)) ≤
        ENNReal.ofReal (4 * t * K) := by
      unfold h2VecNormSqR3
      rw [ENNReal.ofReal_add (add_nonneg (h2NormSqR3_nonneg _) (h2NormSqR3_nonneg _)) (h2NormSqR3_nonneg _),
          ENNReal.ofReal_add (h2NormSqR3_nonneg _) (h2NormSqR3_nonneg _),
          hc_eq 0, hc_eq 1, hc_eq 2]
      exact hsum_lint
    exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 hle_enn

/-- Admissible `H²(ℝ³)` solution curve uniformly bounded in the closed ball of squared radius `M`. -/
structure IsAdmissibleCurveR3 (M : ℝ) (u : ℝ → VecFieldR3C) : Prop where
  h_inH2 : ∀ t : ℝ, InH2VecR3 (u t)
  h_bound : ∀ t : ℝ, h2VecNormSqR3 (u t) ≤ M
  h_cont_H2 : ∀ t₀ : ℝ, Tendsto (fun t => h2VecNormSqR3 (fun ξ c => u t ξ c - u t₀ ξ c)) (𝓝 t₀) (𝓝 0)
  h_cont_pt : ∀ (ξ : R3) (c : Fin 3), Continuous (fun t : ℝ => u t ξ c)
  h_joint : ∀ c : Fin 3, AEStronglyMeasurable (fun p : ℝ × R3 => u p.1 p.2 c) (volume.prod volume)

/-- Raw continuous `ℝ³` spectral Duhamel operator at time `t`. -/
noncomputable def duhamelRawR3 (ν : ℝ) (u₀ : VecFieldR3C) (u : ℝ → VecFieldR3C) (t : ℝ) : VecFieldR3C :=
  fun ξ c =>
    (heatMultiplier3D ν t ξ : ℂ) * u₀ ξ c +
    ∫ s in (0 : ℝ)..t, heatSmoothedBilinearR3 ν (t - s) (u s) (u s) ξ c

/-- Time-clamped continuous `ℝ³` Duhamel operator `Φ` on `[0, T]`. -/
noncomputable def duhamelOpR3 (ν T : ℝ) (u₀ : VecFieldR3C) (u : ℝ → VecFieldR3C) (t : ℝ) : VecFieldR3C :=
  duhamelRawR3 ν u₀ u (clampTR3 T t)

lemma duhamelOpR3_eq_raw {ν T t : ℝ} (ht : t ∈ Set.Icc 0 T) (u₀ : VecFieldR3C) (u : ℝ → VecFieldR3C) :
    duhamelOpR3 ν T u₀ u t = duhamelRawR3 ν u₀ u t := by
  unfold duhamelOpR3; rw [clampTR3_eq_self ht]

/-- Pointwise continuity of `t ↦ convR3 (a t) (b t) ξ` from `H²(ℝ³)`-norm continuity. -/
theorem continuous_convR3_of_H2_cont {M : ℝ} {a b : ℝ → R3 → ℂ}
    (ha_in : ∀ t, InH2R3 (a t)) (hb_in : ∀ t, InH2R3 (b t))
    (ha_bd : ∀ t, h2NormSqR3 (a t) ≤ M) (hb_bd : ∀ t, h2NormSqR3 (b t) ≤ M)
    (ha_cont : ∀ t₀, Tendsto (fun t => h2NormSqR3 (fun η => a t η - a t₀ η)) (𝓝 t₀) (𝓝 0))
    (hb_cont : ∀ t₀, Tendsto (fun t => h2NormSqR3 (fun η => b t η - b t₀ η)) (𝓝 t₀) (𝓝 0))
    (ξ : R3) :
    Continuous (fun t : ℝ => convR3 (a t) (b t) ξ) := by
  have hM_nn : 0 ≤ M := le_trans (h2NormSqR3_nonneg (a 0)) (ha_bd 0)
  rw [continuous_iff_continuousAt]
  intro t₀
  have hconv_cs : ∀ {f g : R3 → ℂ}, InH2R3 f → InH2R3 g →
      ‖convR3 f g ξ‖ ≤ Real.sqrt (h2NormSqR3 f) * Real.sqrt (h2NormSqR3 g) := by
    intro f g hf hg
    have hf2 := h2R3_l2_integrable hf
    have hg2 := h2R3_l2_integrable hg
    have hg_sh_m : AEStronglyMeasurable (fun η : R3 => ‖g (ξ - η)‖) volume :=
      hg.1.norm.comp_quasiMeasurePreserving (Measure.measurePreserving_sub_left (volume : Measure R3) ξ).quasiMeasurePreserving
    have hg2_sh : Integrable (fun η : R3 => ‖g (ξ - η)‖ ^ 2) volume := hg2.1.comp_sub_left ξ
    have hcs := r3_cauchy_schwarz_sq_ae_15d hf.1.norm hg_sh_m hf2.1 hg2_sh
    have hg2_eq : r3Integral (fun η : R3 => ‖g (ξ - η)‖ ^ 2) = r3Integral (fun η : R3 => ‖g η‖ ^ 2) :=
      integral_sub_left_eq_self (fun η : R3 => ‖g η‖ ^ 2) volume ξ
    rw [hg2_eq] at hcs
    have hnorm : ‖convR3 f g ξ‖ ≤ r3Integral (fun η : R3 => ‖f η‖ * ‖g (ξ - η)‖) := by
      unfold convR3 r3Integral
      calc ‖∫ η : R3, f η * g (ξ - η)‖
          ≤ ∫ η : R3, ‖f η * g (ξ - η)‖ := norm_integral_le_integral_norm _
        _ = ∫ η : R3, ‖f η‖ * ‖g (ξ - η)‖ := integral_congr_ae (Filter.Eventually.of_forall fun η => norm_mul _ _)
    have hsq : ‖convR3 f g ξ‖ ^ 2 ≤ h2NormSqR3 f * h2NormSqR3 g := by
      have h1 : ‖convR3 f g ξ‖ ^ 2 ≤ (r3Integral (fun η : R3 => ‖f η‖ * ‖g (ξ - η)‖)) ^ 2 := by
        nlinarith [norm_nonneg (convR3 f g ξ), r3Integral_nonneg fun η => mul_nonneg (norm_nonneg (f η)) (norm_nonneg (g (ξ - η)))]
      have h2 := mul_le_mul hf2.2 hg2.2 (r3Integral_nonneg fun _ => sq_nonneg _) (h2NormSqR3_nonneg f)
      exact le_trans h1 (le_trans hcs h2)
    rw [← Real.sqrt_sq (norm_nonneg _), ← Real.sqrt_mul (h2NormSqR3_nonneg f)]
    exact Real.sqrt_le_sqrt hsq
  have hbound : ∀ t : ℝ, ‖convR3 (a t) (b t) ξ - convR3 (a t₀) (b t₀) ξ‖ ≤
      Real.sqrt M * (Real.sqrt (h2NormSqR3 (fun η => a t η - a t₀ η)) +
        Real.sqrt (h2NormSqR3 (fun η => b t η - b t₀ η))) := by
    intro t
    have hsplit : convR3 (a t) (b t) ξ - convR3 (a t₀) (b t₀) ξ =
        convR3 (fun η => a t η - a t₀ η) (b t) ξ + convR3 (a t₀) (fun η => b t η - b t₀ η) ξ := by
      rw [convR3_sub_left (ha_in t) (ha_in t₀) (hb_in t) ξ,
          convR3_sub_right (ha_in t₀) (hb_in t) (hb_in t₀) ξ]
      ring
    rw [hsplit]
    have h1 := hconv_cs (inH2R3_sub (ha_in t) (ha_in t₀)).1 (hb_in t)
    have h2 := hconv_cs (ha_in t₀) (inH2R3_sub (hb_in t) (hb_in t₀)).1
    have h3 : Real.sqrt (h2NormSqR3 (b t)) ≤ Real.sqrt M := Real.sqrt_le_sqrt (hb_bd t)
    have h4 : Real.sqrt (h2NormSqR3 (a t₀)) ≤ Real.sqrt M := Real.sqrt_le_sqrt (ha_bd t₀)
    calc ‖convR3 (fun η => a t η - a t₀ η) (b t) ξ + convR3 (a t₀) (fun η => b t η - b t₀ η) ξ‖
        ≤ ‖convR3 (fun η => a t η - a t₀ η) (b t) ξ‖ + ‖convR3 (a t₀) (fun η => b t η - b t₀ η) ξ‖ := norm_add_le _ _
      _ ≤ Real.sqrt (h2NormSqR3 (fun η => a t η - a t₀ η)) * Real.sqrt M +
          Real.sqrt M * Real.sqrt (h2NormSqR3 (fun η => b t η - b t₀ η)) := by
            have hm1 := mul_le_mul_of_nonneg_left h3 (Real.sqrt_nonneg (h2NormSqR3 (fun η => a t η - a t₀ η)))
            have hm2 := mul_le_mul_of_nonneg_right h4 (Real.sqrt_nonneg (h2NormSqR3 (fun η => b t η - b t₀ η)))
            linarith
      _ = _ := by ring
  rw [Metric.continuousAt_iff]
  intro ε hε
  have htend : Tendsto (fun t => Real.sqrt M *
      (Real.sqrt (h2NormSqR3 (fun η => a t η - a t₀ η)) +
       Real.sqrt (h2NormSqR3 (fun η => b t η - b t₀ η)))) (𝓝 t₀) (𝓝 0) := by
    have h1 : Tendsto (fun t => Real.sqrt (h2NormSqR3 (fun η => a t η - a t₀ η))) (𝓝 t₀) (𝓝 0) := by
      simpa only [Real.sqrt_zero, Function.comp_def] using (Real.continuous_sqrt.tendsto 0).comp (ha_cont t₀)
    have h2 : Tendsto (fun t => Real.sqrt (h2NormSqR3 (fun η => b t η - b t₀ η))) (𝓝 t₀) (𝓝 0) := by
      simpa only [Real.sqrt_zero, Function.comp_def] using (Real.continuous_sqrt.tendsto 0).comp (hb_cont t₀)
    simpa only [add_zero, mul_zero] using (tendsto_const_nhds (x := Real.sqrt M)).mul (h1.add h2)
  have hev := (Metric.tendsto_nhds.1 htend) ε hε
  rw [Metric.eventually_nhds_iff] at hev
  obtain ⟨δ, hδ, hprop⟩ := hev
  refine ⟨δ, hδ, fun {t} ht => ?_⟩
  rw [dist_eq_norm]
  have hlt := hprop ht
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (by positivity)] at hlt
  exact lt_of_le_of_lt (hbound t) hlt

private lemma continuous_nsBilinearR3_of_admissible_15d {M : ℝ}
    {u v : ℝ → VecFieldR3C} (hu : IsAdmissibleCurveR3 M u) (hv : IsAdmissibleCurveR3 M v)
    (ξ : R3) (c : Fin 3) :
    Continuous (fun t : ℝ => nsBilinearR3 (u t) (v t) ξ c) := by
  have hcomp_bd : ∀ (w : ℝ → VecFieldR3C), IsAdmissibleCurveR3 M w → ∀ (j : Fin 3) (t : ℝ),
      h2NormSqR3 (fun η => w t η j) ≤ M := fun w hw j t => by
    have hb := hw.h_bound t; unfold h2VecNormSqR3 at hb
    fin_cases j
    · change h2NormSqR3 (fun η => w t η 0) ≤ M
      linarith [h2NormSqR3_nonneg (fun η => w t η 1), h2NormSqR3_nonneg (fun η => w t η 2)]
    · change h2NormSqR3 (fun η => w t η 1) ≤ M
      linarith [h2NormSqR3_nonneg (fun η => w t η 0), h2NormSqR3_nonneg (fun η => w t η 2)]
    · change h2NormSqR3 (fun η => w t η 2) ≤ M
      linarith [h2NormSqR3_nonneg (fun η => w t η 0), h2NormSqR3_nonneg (fun η => w t η 1)]
  have hcomp_cont : ∀ (w : ℝ → VecFieldR3C), IsAdmissibleCurveR3 M w → ∀ (j : Fin 3) (t₀ : ℝ),
      Tendsto (fun t => h2NormSqR3 (fun η => w t η j - w t₀ η j)) (𝓝 t₀) (𝓝 0) := fun w hw j t₀ =>
    squeeze_zero (fun _ => h2NormSqR3_nonneg _)
      (fun t => by
        unfold h2VecNormSqR3
        fin_cases j
        · change h2NormSqR3 (fun η => w t η 0 - w t₀ η 0) ≤ _
          linarith [h2NormSqR3_nonneg (fun η => w t η 1 - w t₀ η 1), h2NormSqR3_nonneg (fun η => w t η 2 - w t₀ η 2)]
        · change h2NormSqR3 (fun η => w t η 1 - w t₀ η 1) ≤ _
          linarith [h2NormSqR3_nonneg (fun η => w t η 0 - w t₀ η 0), h2NormSqR3_nonneg (fun η => w t η 2 - w t₀ η 2)]
        · change h2NormSqR3 (fun η => w t η 2 - w t₀ η 2) ≤ _
          linarith [h2NormSqR3_nonneg (fun η => w t η 0 - w t₀ η 0), h2NormSqR3_nonneg (fun η => w t η 1 - w t₀ η 1)])
      (hw.h_cont_H2 t₀)
  have hflux_c : ∀ k : Fin 3, Continuous (fun t : ℝ => nsFluxR3 (u t) (v t) ξ k) := fun k => by
    unfold nsFluxR3
    have hc : ∀ j : Fin 3, Continuous (fun t : ℝ => convR3 (fun η => u t η j) (fun η => v t η k) ξ) :=
      fun j => continuous_convR3_of_H2_cont (fun t => hu.h_inH2 t j) (fun t => hv.h_inH2 t k)
        (hcomp_bd u hu j) (hcomp_bd v hv k) (hcomp_cont u hu j) (hcomp_cont v hv k) ξ
    exact continuous_const.mul (((continuous_const.mul (hc 0)).add (continuous_const.mul (hc 1))).add
      (continuous_const.mul (hc 2)))
  unfold nsBilinearR3 lerayProjR3C
  split_ifs with h0
  · exact (hflux_c c).neg
  · exact ((hflux_c c).sub (((((continuous_const.mul (hflux_c 0)).add
      (continuous_const.mul (hflux_c 1))).add (continuous_const.mul (hflux_c 2))).div_const _).mul continuous_const)).neg

private lemma heatSmoothedBilinearR3_joint_meas_15d {ν t M : ℝ}
    {u v : ℝ → VecFieldR3C} (hu : IsAdmissibleCurveR3 M u) (hv : IsAdmissibleCurveR3 M v) (c : Fin 3) :
    AEStronglyMeasurable (fun p : ℝ × R3 => heatSmoothedBilinearR3 ν (t - p.1) (u p.1) (v p.1) p.2 c)
      ((volume.restrict (Set.Ioc (0 : ℝ) t)).prod volume) := by
  let μt : Measure ℝ := volume.restrict (Set.Ioc (0 : ℝ) t)
  have hconv_m : ∀ j k : Fin 3,
      AEStronglyMeasurable (fun p : ℝ × R3 => convR3 (fun η => u p.1 η j) (fun η => v p.1 η k) p.2)
        (μt.prod volume) := by
    intro j k
    let um := (hu.h_joint j).mk (fun p : ℝ × R3 => u p.1 p.2 j)
    let vm := (hv.h_joint k).mk (fun p : ℝ × R3 => v p.1 p.2 k)
    have h3_sm : StronglyMeasurable (fun q : (ℝ × R3) × R3 => um (q.1.1, q.2) * vm (q.1.1, q.1.2 - q.2)) :=
      ((hu.h_joint j).stronglyMeasurable_mk.comp_measurable
        ((measurable_fst.comp measurable_fst).prodMk measurable_snd)).mul
      ((hv.h_joint k).stronglyMeasurable_mk.comp_measurable
        ((measurable_fst.comp measurable_fst).prodMk ((measurable_snd.comp measurable_fst).sub measurable_snd)))
    have hint_sm : StronglyMeasurable (fun p : ℝ × R3 => ∫ η : R3, um (p.1, η) * vm (p.1, p.2 - η)) :=
      h3_sm.integral_prod_right'
    have hae_s : ∀ᵐ s ∂μt, (∀ᵐ η ∂volume, u s η j = um (s, η)) ∧ (∀ᵐ η ∂volume, v s η k = vm (s, η)) := by
      have h1 : ∀ᵐ s ∂volume, ∀ᵐ η ∂volume, u s η j = um (s, η) := Measure.ae_ae_of_ae_prod (hu.h_joint j).ae_eq_mk
      have h2 : ∀ᵐ s ∂volume, ∀ᵐ η ∂volume, v s η k = vm (s, η) := Measure.ae_ae_of_ae_prod (hv.h_joint k).ae_eq_mk
      exact ae_restrict_of_ae (h1.and h2)
    have hae_p : ∀ᵐ p ∂(μt.prod volume),
        convR3 (fun η => u p.1 η j) (fun η => v p.1 η k) p.2 =
          ∫ η : R3, um (p.1, η) * vm (p.1, p.2 - η) := by
      have hfst : ∀ᵐ p ∂(μt.prod volume),
          (∀ᵐ η ∂volume, u p.1 η j = um (p.1, η)) ∧ (∀ᵐ η ∂volume, v p.1 η k = vm (p.1, η)) :=
        (Measure.quasiMeasurePreserving_fst (μ := μt) (ν := (volume : Measure R3))).ae hae_s
      exact hfst.mono fun p ⟨hs1, hs2⟩ => by
        unfold convR3
        have hs2' : ∀ᵐ η ∂volume, v p.1 (p.2 - η) k = vm (p.1, p.2 - η) :=
          (Measure.measurePreserving_sub_left (volume : Measure R3) p.2).quasiMeasurePreserving.ae_eq_comp hs2
        exact integral_congr_ae ((hs1.and hs2').mono fun η ⟨h1, h2⟩ => by dsimp only; rw [h1, h2])
    exact hint_sm.aestronglyMeasurable.congr (hae_p.mono fun _ h => h.symm)
  have hcoord : ∀ j : Fin 3, Continuous (fun p : ℝ × R3 => (p.2 j : ℂ)) := fun j =>
    Complex.continuous_ofReal.comp ((continuous_apply j).comp continuous_snd)
  have hflux_m : ∀ k : Fin 3, AEStronglyMeasurable (fun p : ℝ × R3 => nsFluxR3 (u p.1) (v p.1) p.2 k)
      (μt.prod volume) := fun k => by
    unfold nsFluxR3
    exact aestronglyMeasurable_const.mul
      ((((hcoord 0).aestronglyMeasurable.mul (hconv_m 0 k)).add
        ((hcoord 1).aestronglyMeasurable.mul (hconv_m 1 k))).add
        ((hcoord 2).aestronglyMeasurable.mul (hconv_m 2 k)))
  have hdot_c : Continuous (fun p : ℝ × R3 => dot3D p.2 p.2) := by
    unfold dot3D; fun_prop
  have hset : MeasurableSet {p : ℝ × R3 | dot3D p.2 p.2 = 0} :=
    (isClosed_eq hdot_c continuous_const).measurableSet
  have hnum : AEStronglyMeasurable (fun p : ℝ × R3 =>
      (p.2 0 : ℂ) * nsFluxR3 (u p.1) (v p.1) p.2 0 +
      (p.2 1 : ℂ) * nsFluxR3 (u p.1) (v p.1) p.2 1 +
      (p.2 2 : ℂ) * nsFluxR3 (u p.1) (v p.1) p.2 2) (μt.prod volume) :=
    (((hcoord 0).aestronglyMeasurable.mul (hflux_m 0)).add
      ((hcoord 1).aestronglyMeasurable.mul (hflux_m 1))).add
      ((hcoord 2).aestronglyMeasurable.mul (hflux_m 2))
  have hden_inv : AEStronglyMeasurable (fun p : ℝ × R3 => (((dot3D p.2 p.2 : ℝ) : ℂ))⁻¹) (μt.prod volume) :=
    (Complex.continuous_ofReal.comp hdot_c).measurable.inv.aestronglyMeasurable
  have helse : AEStronglyMeasurable (fun p : ℝ × R3 =>
      nsFluxR3 (u p.1) (v p.1) p.2 c -
        (((p.2 0 : ℂ) * nsFluxR3 (u p.1) (v p.1) p.2 0 +
          (p.2 1 : ℂ) * nsFluxR3 (u p.1) (v p.1) p.2 1 +
          (p.2 2 : ℂ) * nsFluxR3 (u p.1) (v p.1) p.2 2) / ((dot3D p.2 p.2 : ℝ) : ℂ)) * (p.2 c : ℂ))
      (μt.prod volume) := by
    have heq : (fun p : ℝ × R3 =>
        nsFluxR3 (u p.1) (v p.1) p.2 c -
          (((p.2 0 : ℂ) * nsFluxR3 (u p.1) (v p.1) p.2 0 +
            (p.2 1 : ℂ) * nsFluxR3 (u p.1) (v p.1) p.2 1 +
            (p.2 2 : ℂ) * nsFluxR3 (u p.1) (v p.1) p.2 2) / ((dot3D p.2 p.2 : ℝ) : ℂ)) * (p.2 c : ℂ)) =
      (fun p : ℝ × R3 =>
        nsFluxR3 (u p.1) (v p.1) p.2 c -
          (((p.2 0 : ℂ) * nsFluxR3 (u p.1) (v p.1) p.2 0 +
            (p.2 1 : ℂ) * nsFluxR3 (u p.1) (v p.1) p.2 1 +
            (p.2 2 : ℂ) * nsFluxR3 (u p.1) (v p.1) p.2 2) * (((dot3D p.2 p.2 : ℝ) : ℂ))⁻¹) * (p.2 c : ℂ)) :=
      funext fun p => by rw [div_eq_mul_inv]
    rw [heq]
    exact (hflux_m c).sub ((hnum.mul hden_inv).mul (hcoord c).aestronglyMeasurable)
  have hleray_m : AEStronglyMeasurable (fun p : ℝ × R3 => lerayProjR3C p.2 (nsFluxR3 (u p.1) (v p.1) p.2) c)
      (μt.prod volume) := by
    have heq : (fun p : ℝ × R3 => lerayProjR3C p.2 (nsFluxR3 (u p.1) (v p.1) p.2) c) =
        Set.piecewise {p : ℝ × R3 | dot3D p.2 p.2 = 0} (fun p => nsFluxR3 (u p.1) (v p.1) p.2 c)
          (fun p => nsFluxR3 (u p.1) (v p.1) p.2 c -
            (((p.2 0 : ℂ) * nsFluxR3 (u p.1) (v p.1) p.2 0 +
              (p.2 1 : ℂ) * nsFluxR3 (u p.1) (v p.1) p.2 1 +
              (p.2 2 : ℂ) * nsFluxR3 (u p.1) (v p.1) p.2 2) / ((dot3D p.2 p.2 : ℝ) : ℂ)) * (p.2 c : ℂ)) := by
      funext p; unfold lerayProjR3C Set.piecewise
      by_cases h0 : dot3D p.2 p.2 = 0 <;> simp [h0]
    rw [heq]
    exact AEStronglyMeasurable.piecewise hset.nullMeasurableSet (hflux_m c).restrict helse.restrict
  have hhm_c : Continuous (fun p : ℝ × R3 => (heatMultiplier3D ν (t - p.1) p.2 : ℂ)) :=
    Complex.continuous_ofReal.comp (Real.continuous_exp.comp (by unfold dot3D; fun_prop))
  unfold heatSmoothedBilinearR3 nsBilinearR3
  exact hhm_c.aestronglyMeasurable.mul hleray_m.neg

/-- **THEOREM 15D2-2 (`H²(ℝ³)` Energy Bound for the Continuous Duhamel Operator `Φ`):**
    `h2VecNormSqR3 (duhamelOpR3 ν T u₀ u t) ≤ 2 h2VecNormSqR3 u₀ + (64 π² T / ν) M²`. -/
theorem duhamelOpR3_inH2_and_bound {ν T M : ℝ} (hν : 0 < ν) (hT : 0 ≤ T) (hM : 0 ≤ M)
    {u₀ : VecFieldR3C} (hu₀ : InH2VecR3 u₀) {u : ℝ → VecFieldR3C} (hu : IsAdmissibleCurveR3 M u) (t : ℝ) :
    InH2VecR3 (duhamelOpR3 ν T u₀ u t) ∧
    h2VecNormSqR3 (duhamelOpR3 ν T u₀ u t) ≤ 2 * h2VecNormSqR3 u₀ + (64 * Real.pi ^ 2 * T / ν) * M ^ 2 := by
  set τ : ℝ := clampTR3 T t
  have hτ_mem : τ ∈ Set.Icc 0 T := clampTR3_mem_Icc hT t
  have hlin : InH2VecR3 (fun ξ c => (heatMultiplier3D ν τ ξ : ℂ) * u₀ ξ c) ∧
      h2VecNormSqR3 (fun ξ c => (heatMultiplier3D ν τ ξ : ℂ) * u₀ ξ c) ≤ h2VecNormSqR3 u₀ := by
    have hhm_c : Continuous (fun ξ : R3 => (heatMultiplier3D ν τ ξ : ℂ)) :=
      Complex.continuous_ofReal.comp (Real.continuous_exp.comp (by unfold dot3D; fun_prop))
    have hc : ∀ c : Fin 3, InH2R3 (fun ξ => (heatMultiplier3D ν τ ξ : ℂ) * u₀ ξ c) ∧
        h2NormSqR3 (fun ξ => (heatMultiplier3D ν τ ξ : ℂ) * u₀ ξ c) ≤ h2NormSqR3 (fun ξ => u₀ ξ c) := by
      intro c
      have hpt : ∀ ξ : R3, h2WeightR3 ξ * ‖(heatMultiplier3D ν τ ξ : ℂ) * u₀ ξ c‖ ^ 2 ≤
          h2WeightR3 ξ * ‖u₀ ξ c‖ ^ 2 := fun ξ => by
        rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (heatMultiplier3D_pos ν τ ξ).le, mul_pow]
        have hle1 : (heatMultiplier3D ν τ ξ) ^ 2 ≤ 1 := by
          have := heatMultiplier3D_le_one hν.le hτ_mem.1 ξ
          have := (heatMultiplier3D_pos ν τ ξ).le
          nlinarith
        have hmul1 : (heatMultiplier3D ν τ ξ) ^ 2 * ‖u₀ ξ c‖ ^ 2 ≤ ‖u₀ ξ c‖ ^ 2 := by
          simpa only [one_mul] using mul_le_mul_of_nonneg_right hle1 (sq_nonneg ‖u₀ ξ c‖)
        exact mul_le_mul_of_nonneg_left hmul1 (h2WeightR3_pos ξ).le
      have hm := hhm_c.aestronglyMeasurable.mul (hu₀ c).1
      have hint : Integrable (fun ξ => h2WeightR3 ξ * ‖(heatMultiplier3D ν τ ξ : ℂ) * u₀ ξ c‖ ^ 2) volume :=
        (hu₀ c).2.mono' (h2WeightR3_continuous.aestronglyMeasurable.mul (hm.norm.pow 2))
          (Filter.Eventually.of_forall fun ξ => by
            rw [Real.norm_of_nonneg (mul_nonneg (h2WeightR3_pos ξ).le (sq_nonneg _))]
            exact hpt ξ)
      exact ⟨⟨hm, hint⟩, integral_mono hint (hu₀ c).2 hpt⟩
    refine ⟨fun c => (hc c).1, ?_⟩
    unfold h2VecNormSqR3; linarith [(hc 0).2, (hc 1).2, (hc 2).2]
  have hnl := integral_h2R3_bound_of_inv_sqrt_decay (t := τ) (K := (8 * Real.pi ^ 2 / ν) * M ^ 2)
    hτ_mem.1 (by positivity)
    (G := fun s => heatSmoothedBilinearR3 ν (τ - s) (u s) (u s))
    (fun ξ c => by
      unfold heatSmoothedBilinearR3
      exact (Complex.continuous_ofReal.comp (Real.continuous_exp.comp (by unfold dot3D; fun_prop))).mul
        (continuous_nsBilinearR3_of_admissible_15d hu hu ξ c))
    (fun c => heatSmoothedBilinearR3_joint_meas_15d hu hu c)
    (fun s hs => by
      have hts : 0 < τ - s := sub_pos.2 hs.2
      have h1 := heatSmoothedBilinearR3_inH2_and_bound hν hts (hu.h_inH2 s) (hu.h_inH2 s)
      refine ⟨h1.1, le_trans h1.2 ?_⟩
      have hM2 : h2VecNormSqR3 (u s) * h2VecNormSqR3 (u s) ≤ M ^ 2 := by
        have := hu.h_bound s; have := h2VecNormSqR3_nonneg (u s); nlinarith
      have heq : (8 * Real.pi ^ 2 / (ν * (τ - s))) * M ^ 2 = (8 * Real.pi ^ 2 / ν) * M ^ 2 / (τ - s) := by
        field_simp [hν.ne', hts.ne']
      have hrew : (8 * Real.pi ^ 2 / (ν * (τ - s))) * h2VecNormSqR3 (u s) * h2VecNormSqR3 (u s) =
          (8 * Real.pi ^ 2 / (ν * (τ - s))) * (h2VecNormSqR3 (u s) * h2VecNormSqR3 (u s)) := by ring
      rw [hrew, ← heq]
      exact mul_le_mul_of_nonneg_left hM2 (by positivity))
  have hadd := inH2VecR3_add hlin.1 hnl.1
  refine ⟨hadd.1, ?_⟩
  have hτ_le : τ ≤ T := hτ_mem.2
  have h4τ : 4 * τ * ((8 * Real.pi ^ 2 / ν) * M ^ 2) ≤ (32 * Real.pi ^ 2 * T / ν) * M ^ 2 := by
    have hcoeff : 0 ≤ (32 * Real.pi ^ 2 / ν) * M ^ 2 := by positivity
    have h1 : 4 * τ * ((8 * Real.pi ^ 2 / ν) * M ^ 2) = τ * ((32 * Real.pi ^ 2 / ν) * M ^ 2) := by ring
    have h2 : (32 * Real.pi ^ 2 * T / ν) * M ^ 2 = T * ((32 * Real.pi ^ 2 / ν) * M ^ 2) := by ring
    rw [h1, h2]
    exact mul_le_mul_of_nonneg_right hτ_le hcoeff
  have h64 : 2 * ((32 * Real.pi ^ 2 * T / ν) * M ^ 2) = (64 * Real.pi ^ 2 * T / ν) * M ^ 2 := by ring
  change h2VecNormSqR3 (fun ξ c => (heatMultiplier3D ν τ ξ : ℂ) * u₀ ξ c +
      ∫ s in (0 : ℝ)..τ, heatSmoothedBilinearR3 ν (τ - s) (u s) (u s) ξ c) ≤ _
  linarith [hadd.2, hlin.2, hnl.2, h4τ, h64]

/-- **THEOREM 15D2-3 (Strict `1/4`-Contraction of Continuous `ℝ³` Duhamel Operator `Φ`):**
    Under `512 π² T M ≤ ν`, for any two admissible curves `u, v` with `h2VecNormSqR3 (u s - v s) ≤ D`:
    `h2VecNormSqR3 (Φ u t - Φ v t) ≤ (1 / 4) * D`. -/
theorem duhamelOpR3_contraction_quarter {ν T M D : ℝ}
    (hν : 0 < ν) (hT : 0 ≤ T) (hM : 0 ≤ M) (hD : 0 ≤ D)
    (hsmall : 512 * Real.pi ^ 2 * T * M ≤ ν)
    (u₀ : VecFieldR3C) {u v : ℝ → VecFieldR3C}
    (hu : IsAdmissibleCurveR3 M u) (hv : IsAdmissibleCurveR3 M v)
    (hdiff : ∀ s : ℝ, h2VecNormSqR3 (fun ξ c => u s ξ c - v s ξ c) ≤ D) (t : ℝ) :
    h2VecNormSqR3 (fun ξ c => duhamelOpR3 ν T u₀ u t ξ c - duhamelOpR3 ν T u₀ v t ξ c) ≤
      (1 / 4 : ℝ) * D := by
  set τ : ℝ := clampTR3 T t
  have hτ_mem : τ ∈ Set.Icc 0 T := clampTR3_mem_Icc hT t
  have hsub_eq : (fun ξ c => duhamelOpR3 ν T u₀ u t ξ c - duhamelOpR3 ν T u₀ v t ξ c) =
      (fun ξ c => ∫ s in (0 : ℝ)..τ,
        (heatSmoothedBilinearR3 ν (τ - s) (u s) (u s) ξ c -
         heatSmoothedBilinearR3 ν (τ - s) (v s) (v s) ξ c)) := by
    funext ξ c
    unfold duhamelOpR3 duhamelRawR3
    change ((heatMultiplier3D ν τ ξ : ℂ) * u₀ ξ c + ∫ s in (0 : ℝ)..τ, heatSmoothedBilinearR3 ν (τ - s) (u s) (u s) ξ c) -
        ((heatMultiplier3D ν τ ξ : ℂ) * u₀ ξ c + ∫ s in (0 : ℝ)..τ, heatSmoothedBilinearR3 ν (τ - s) (v s) (v s) ξ c) = _
    have hcu : Continuous (fun s => heatSmoothedBilinearR3 ν (τ - s) (u s) (u s) ξ c) :=
      (Complex.continuous_ofReal.comp (Real.continuous_exp.comp (by unfold dot3D; fun_prop))).mul
        (continuous_nsBilinearR3_of_admissible_15d hu hu ξ c)
    have hcv : Continuous (fun s => heatSmoothedBilinearR3 ν (τ - s) (v s) (v s) ξ c) :=
      (Complex.continuous_ofReal.comp (Real.continuous_exp.comp (by unfold dot3D; fun_prop))).mul
        (continuous_nsBilinearR3_of_admissible_15d hv hv ξ c)
    rw [add_sub_add_left_eq_sub,
        ← intervalIntegral.integral_sub (hcu.intervalIntegrable 0 τ) (hcv.intervalIntegrable 0 τ)]
  rw [hsub_eq]
  have hbd := (integral_h2R3_bound_of_inv_sqrt_decay (t := τ) (K := (32 * Real.pi ^ 2 * M / ν) * D)
    hτ_mem.1 (by positivity)
    (G := fun s ξ c => heatSmoothedBilinearR3 ν (τ - s) (u s) (u s) ξ c -
      heatSmoothedBilinearR3 ν (τ - s) (v s) (v s) ξ c)
    (fun ξ c =>
      ((Complex.continuous_ofReal.comp (Real.continuous_exp.comp (by unfold dot3D; fun_prop))).mul
        (continuous_nsBilinearR3_of_admissible_15d hu hu ξ c)).sub
      ((Complex.continuous_ofReal.comp (Real.continuous_exp.comp (by unfold dot3D; fun_prop))).mul
        (continuous_nsBilinearR3_of_admissible_15d hv hv ξ c)))
    (fun c => (heatSmoothedBilinearR3_joint_meas_15d hu hu c).sub
      (heatSmoothedBilinearR3_joint_meas_15d hv hv c))
    (fun s hs => by
      have hts : 0 < τ - s := sub_pos.2 hs.2
      have hlip := heatSmoothedBilinearR3_self_sub_lipschitz hν hts (hu.h_inH2 s) (hv.h_inH2 s)
      refine ⟨hlip.1, le_trans hlip.2 ?_⟩
      have hsum : h2VecNormSqR3 (u s) + h2VecNormSqR3 (v s) ≤ 2 * M := by
        linarith [hu.h_bound s, hv.h_bound s]
      have h1 := mul_le_mul hsum (hdiff s) (h2VecNormSqR3_nonneg _) (by positivity)
      have h2 := mul_le_mul_of_nonneg_left h1 (by positivity : (0 : ℝ) ≤ 16 * Real.pi ^ 2 / (ν * (τ - s)))
      have heq : 16 * Real.pi ^ 2 / (ν * (τ - s)) * (2 * M * D) = (32 * Real.pi ^ 2 * M / ν) * D / (τ - s) := by
        field_simp [hν.ne', hts.ne']; ring
      linarith)).2
  have hτ_le : τ ≤ T := hτ_mem.2
  have h128 : 4 * τ * ((32 * Real.pi ^ 2 * M / ν) * D) ≤ (128 * Real.pi ^ 2 * T * M / ν) * D := by
    have hcoeff : 0 ≤ (128 * Real.pi ^ 2 * M / ν) * D := by positivity
    have h1 : 4 * τ * ((32 * Real.pi ^ 2 * M / ν) * D) = τ * ((128 * Real.pi ^ 2 * M / ν) * D) := by ring
    have h2 : (128 * Real.pi ^ 2 * T * M / ν) * D = T * ((128 * Real.pi ^ 2 * M / ν) * D) := by ring
    rw [h1, h2]
    exact mul_le_mul_of_nonneg_right hτ_le hcoeff
  have hq : 128 * Real.pi ^ 2 * T * M / ν ≤ 1 / 4 := by
    rw [div_le_iff₀ hν]; linarith
  exact le_trans hbd (le_trans h128 (mul_le_mul_of_nonneg_right hq hD))

-- ============================================================================
-- SECTION 3 (MILESTONE 15D-2B): SPECTRAL PRESSURE RECOVERY (POISSON EQUATION),
--   UNCONDITIONAL MILD UNIQUENESS & MAXIMAL-INTERVAL BLOWUP ALTERNATIVE ON ℝ³
-- ============================================================================

/-- Spectral pressure Fourier field on `ℝ³` recovered via the 3D Pressure Poisson equation:
    `-|ξ|² p̂(ξ) = -i (ξ · F(u, u)_ξ)`. -/
noncomputable def pressureCoeffR3 (u : VecFieldR3C) (ξ : R3) : ℂ :=
  if dot3D ξ ξ = 0 then 0
  else (Complex.I / ((dot3D ξ ξ : ℝ) : ℂ)) *
    ((ξ 0 : ℂ) * nsFluxR3 u u ξ 0 + (ξ 1 : ℂ) * nsFluxR3 u u ξ 1 + (ξ 2 : ℂ) * nsFluxR3 u u ξ 2)

/-- **THEOREM 15D2-4 (Exact Whole-Space `ℝ³` Spectral Pressure Poisson Identity & Momentum Splitting):** -/
theorem pressureCoeffR3_poisson_and_momentum_splitting (u : VecFieldR3C) (ξ : R3) :
    (-((dot3D ξ ξ : ℝ) : ℂ)) * pressureCoeffR3 u ξ =
      -Complex.I *
        ((ξ 0 : ℂ) * nsFluxR3 u u ξ 0 + (ξ 1 : ℂ) * nsFluxR3 u u ξ 1 + (ξ 2 : ℂ) * nsFluxR3 u u ξ 2) ∧
    (∀ c : Fin 3, nsBilinearR3 u u ξ c =
      -nsFluxR3 u u ξ c - Complex.I * (ξ c : ℂ) * pressureCoeffR3 u ξ) := by
  constructor
  · unfold pressureCoeffR3
    split_ifs with h0
    · have hξ0 : ξ 0 = 0 := by unfold dot3D at h0; nlinarith [sq_nonneg (ξ 0), sq_nonneg (ξ 1), sq_nonneg (ξ 2)]
      have hξ1 : ξ 1 = 0 := by unfold dot3D at h0; nlinarith [sq_nonneg (ξ 0), sq_nonneg (ξ 1), sq_nonneg (ξ 2)]
      have hξ2 : ξ 2 = 0 := by unfold dot3D at h0; nlinarith [sq_nonneg (ξ 0), sq_nonneg (ξ 1), sq_nonneg (ξ 2)]
      simp [h0, hξ0, hξ1, hξ2]
    · have hneC : ((dot3D ξ ξ : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 h0
      field_simp [hneC]
  · intro c
    unfold nsBilinearR3 lerayProjR3C pressureCoeffR3
    split_ifs with h0
    · simp
    · have hneC : ((dot3D ξ ξ : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 h0
      have hI2 : Complex.I ^ 2 = -1 := Complex.I_sq
      field_simp [hneC]
      linear_combination ((ξ c : ℂ) * ((ξ 0 : ℂ) * nsFluxR3 u u ξ 0 +
        (ξ 1 : ℂ) * nsFluxR3 u u ξ 1 + (ξ 2 : ℂ) * nsFluxR3 u u ξ 2)) * hI2

/-- **THEOREM 15D2-5 (Unconditional Local Mild Solution Uniqueness on `ℝ³`):**
    Any two admissible `H²(ℝ³)` mild solutions `u, v` starting from `u₀` on `[0, T]` with
    `512 π² T M ≤ ν` are equal almost everywhere at every `t ∈ [0, T]` (`h2VecNormSqR3 (u t - v t) = 0`). -/
private lemma admissible_clamp_15d {T M : ℝ} (hT : 0 ≤ T) {u : ℝ → VecFieldR3C}
    (hu : IsAdmissibleCurveR3 M u) :
    IsAdmissibleCurveR3 M (fun s => u (clampTR3 T s)) where
  h_inH2 := fun s => hu.h_inH2 (clampTR3 T s)
  h_bound := fun s => hu.h_bound (clampTR3 T s)
  h_cont_H2 := fun t₀ => (hu.h_cont_H2 (clampTR3 T t₀)).comp (continuous_clampTR3 T).continuousAt
  h_cont_pt := fun ξ c => (hu.h_cont_pt ξ c).comp (continuous_clampTR3 T)
  h_joint := fun c => by
    have h0 : AEStronglyMeasurable (fun p : ℝ × R3 => u 0 p.2 c) (volume.prod volume) :=
      (hu.h_inH2 0 c).1.comp_quasiMeasurePreserving Measure.quasiMeasurePreserving_snd
    have hT_m : AEStronglyMeasurable (fun p : ℝ × R3 => u T p.2 c) (volume.prod volume) :=
      (hu.h_inH2 T c).1.comp_quasiMeasurePreserving Measure.quasiMeasurePreserving_snd
    have hset1 : MeasurableSet {p : ℝ × R3 | p.1 ≤ 0} :=
      (isClosed_le continuous_fst continuous_const).measurableSet
    have hset2 : MeasurableSet {p : ℝ × R3 | p.1 ≤ T} :=
      (isClosed_le continuous_fst continuous_const).measurableSet
    have hmid : AEStronglyMeasurable (Set.piecewise {p : ℝ × R3 | p.1 ≤ T}
        (fun p : ℝ × R3 => u p.1 p.2 c) (fun p : ℝ × R3 => u T p.2 c)) (volume.prod volume) :=
      AEStronglyMeasurable.piecewise hset2.nullMeasurableSet (hu.h_joint c).restrict hT_m.restrict
    have hfull : AEStronglyMeasurable (Set.piecewise {p : ℝ × R3 | p.1 ≤ 0}
        (fun p : ℝ × R3 => u 0 p.2 c)
        (Set.piecewise {p : ℝ × R3 | p.1 ≤ T}
          (fun p : ℝ × R3 => u p.1 p.2 c) (fun p : ℝ × R3 => u T p.2 c))) (volume.prod volume) :=
      AEStronglyMeasurable.piecewise hset1.nullMeasurableSet h0.restrict hmid.restrict
    refine hfull.congr (Filter.Eventually.of_forall fun p => ?_)
    by_cases hp0 : p.1 ≤ 0
    · have hc : clampTR3 T p.1 = 0 := by unfold clampTR3; rw [min_eq_right (le_trans hp0 hT), max_eq_left hp0]
      simp [Set.piecewise, hp0, hc]
    · by_cases hpT : p.1 ≤ T
      · have hc : clampTR3 T p.1 = p.1 := by unfold clampTR3; rw [min_eq_right hpT, max_eq_right (le_of_not_ge hp0)]
        simp [Set.piecewise, hp0, hpT, hc]
      · have hc : clampTR3 T p.1 = T := by unfold clampTR3; rw [min_eq_left (le_of_not_ge hpT), max_eq_right hT]
        simp [Set.piecewise, hp0, hpT, hc]

theorem mild_solution_unique_r3 {ν T M : ℝ} (hν : 0 < ν) (hT : 0 ≤ T) (hM : 0 ≤ M)
    (hsmall : 512 * Real.pi ^ 2 * T * M ≤ ν) (u₀ : VecFieldR3C)
    {u v : ℝ → VecFieldR3C} (hu : IsAdmissibleCurveR3 M u) (hv : IsAdmissibleCurveR3 M v)
    (hu_sol : ∀ t ∈ Set.Icc (0 : ℝ) T, u t = duhamelRawR3 ν u₀ u t)
    (hv_sol : ∀ t ∈ Set.Icc (0 : ℝ) T, v t = duhamelRawR3 ν u₀ v t) :
    ∀ t ∈ Set.Icc (0 : ℝ) T, h2VecNormSqR3 (fun ξ c => u t ξ c - v t ξ c) = 0 := by
  let uc : ℝ → VecFieldR3C := fun s => u (clampTR3 T s)
  let vc : ℝ → VecFieldR3C := fun s => v (clampTR3 T s)
  have huc : IsAdmissibleCurveR3 M uc := admissible_clamp_15d hT hu
  have hvc : IsAdmissibleCurveR3 M vc := admissible_clamp_15d hT hv
  have huc_fp : ∀ s : ℝ, uc s = duhamelOpR3 ν T u₀ uc s := by
    intro s
    have hmem := clampTR3_mem_Icc hT s
    dsimp only [uc]; rw [hu_sol (clampTR3 T s) hmem]
    funext ξ c
    have hint_eq : (∫ r in (0 : ℝ)..clampTR3 T s,
        heatSmoothedBilinearR3 ν (clampTR3 T s - r) (u r) (u r) ξ c) =
        ∫ r in (0 : ℝ)..clampTR3 T s,
          heatSmoothedBilinearR3 ν (clampTR3 T s - r) (uc r) (uc r) ξ c :=
      intervalIntegral.integral_congr fun r hr => by
        rw [Set.uIcc_of_le hmem.1] at hr
        have hr_mem : r ∈ Set.Icc 0 T := ⟨hr.1, le_trans hr.2 hmem.2⟩
        simp only [uc, clampTR3_eq_self hr_mem]
    dsimp only [duhamelOpR3, duhamelRawR3]
    rw [hint_eq]
  have hvc_fp : ∀ s : ℝ, vc s = duhamelOpR3 ν T u₀ vc s := by
    intro s
    have hmem := clampTR3_mem_Icc hT s
    dsimp only [vc]; rw [hv_sol (clampTR3 T s) hmem]
    funext ξ c
    have hint_eq : (∫ r in (0 : ℝ)..clampTR3 T s,
        heatSmoothedBilinearR3 ν (clampTR3 T s - r) (v r) (v r) ξ c) =
        ∫ r in (0 : ℝ)..clampTR3 T s,
          heatSmoothedBilinearR3 ν (clampTR3 T s - r) (vc r) (vc r) ξ c :=
      intervalIntegral.integral_congr fun r hr => by
        rw [Set.uIcc_of_le hmem.1] at hr
        have hr_mem : r ∈ Set.Icc 0 T := ⟨hr.1, le_trans hr.2 hmem.2⟩
        simp only [vc, clampTR3_eq_self hr_mem]
    dsimp only [duhamelOpR3, duhamelRawR3]
    rw [hint_eq]
  have hiter : ∀ (n : ℕ) (s : ℝ),
      h2VecNormSqR3 (fun ξ c => uc s ξ c - vc s ξ c) ≤ (4 * M) * (1 / 4 : ℝ) ^ n := by
    intro n
    induction n with
    | zero =>
      intro s; simp only [pow_zero, mul_one]
      have h1 := (inH2VecR3_sub (huc.h_inH2 s) (hvc.h_inH2 s)).2
      linarith [huc.h_bound s, hvc.h_bound s]
    | succ k ih =>
      intro s
      rw [huc_fp s, hvc_fp s]
      have hq := duhamelOpR3_contraction_quarter hν hT hM (by positivity) hsmall u₀ huc hvc ih s
      calc _ ≤ (1 / 4 : ℝ) * ((4 * M) * (1 / 4 : ℝ) ^ k) := hq
        _ = (4 * M) * (1 / 4 : ℝ) ^ (k + 1) := by rw [pow_succ]; ring
  intro t ht
  have hnn : 0 ≤ h2VecNormSqR3 (fun ξ c => u t ξ c - v t ξ c) := h2VecNormSqR3_nonneg _
  have hle : h2VecNormSqR3 (fun ξ c => u t ξ c - v t ξ c) ≤ 0 := by
    refine le_of_tendsto_of_tendsto' tendsto_const_nhds
      (show Tendsto (fun n : ℕ => (4 * M) * (1 / 4 : ℝ) ^ n) atTop (𝓝 0) by
        simpa only [mul_zero] using (tendsto_const_nhds (x := 4 * M)).mul
          (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)))
      (fun n => by simpa only [uc, vc, clampTR3_eq_self ht] using hiter n t)
  linarith

/-- **THEOREM 15D2-6 (Concrete Whole-Space `ℝ³` Maximal-Interval Blowup Alternative from `localHorizonH2R3`):**
    Discharges the maximal-interval blowup alternative directly from the concrete `ℝ³`
    `H²` local existence horizon `localHorizonH2R3 ν (‖u(t₀)‖²_{H²})`:
    if `[0, T_star)` is maximal under local `H²(ℝ³)` continuation, then `h2VecNormSqR3 (u t)`
    MUST blow up as `t → T_star⁻` with explicit lower rate
    `ν / (512 π² (4 h2VecNormSqR3 (u t₀) + 1)) ≤ T_star - t₀`. -/
theorem maximal_existence_blowup_alternative_r3
    {ν T_star : ℝ} (hν : 0 < ν) (hT_pos : 0 < T_star)
    {u : ℝ → VecFieldR3C}
    (h_max : ∀ t₀ ∈ Set.Ico (0 : ℝ) T_star,
      t₀ + localHorizonH2R3 ν (h2VecNormSqR3 (u t₀)) ≤ T_star) :
    ((∃ M : ℝ, ∀ t ∈ Set.Ico (0 : ℝ) T_star, h2VecNormSqR3 (u t) ≤ M) → False) ∧
    (∀ t₀ ∈ Set.Ico (0 : ℝ) T_star,
      ν / (512 * Real.pi ^ 2 * (4 * h2VecNormSqR3 (u t₀) + 1)) ≤ T_star - t₀) :=
  blowup_alternative_proved_from_local_existence hT_pos
    (fun t _ => h2VecNormSqR3_nonneg (u t))
    (fun _M hM => localHorizonH2R3_pos hν hM)
    (fun _M₁ _M₂ hM₁ hle => localHorizonH2R3_antitone hν hM₁ hle)
    h_max

/-- Explicit Picard iteration sequence on whole space `ℝ³`:
    `u^{(0)}(t) = u₀`, `u^{(n+1)} = duhamelOpR3 ν T u₀ u^{(n)}`. -/
noncomputable def picardIterR3 (ν T : ℝ) (u₀ : VecFieldR3C) : ℕ → (ℝ → VecFieldR3C)
  | 0 => fun _ => u₀
  | n + 1 => duhamelOpR3 ν T u₀ (picardIterR3 ν T u₀ n)

/-- **THEOREM 15D2-7 (Closed `H²(ℝ³)` Ball Self-Map Property of `duhamelOpR3`):**
    For `M = 4 ‖u₀‖²_{H²} + 1` and `0 ≤ T ≤ localHorizonH2R3 ν (‖u₀‖²_{H²})` (i.e. `512 π² T M ≤ ν`),
    `duhamelOpR3 ν T u₀` maps the closed ball `‖u(t)‖²_{H²} ≤ M` strictly into itself! -/
theorem duhamelOpR3_self_map_ball {ν T M : ℝ} (hν : 0 < ν) (hT : 0 ≤ T)
    {u₀ : VecFieldR3C} (hu₀ : InH2VecR3 u₀)
    (hM_ge : 4 * h2VecNormSqR3 u₀ ≤ M)
    (hsmall : 512 * Real.pi ^ 2 * T * M ≤ ν)
    {u : ℝ → VecFieldR3C} (hu : IsAdmissibleCurveR3 M u) (t : ℝ) :
    InH2VecR3 (duhamelOpR3 ν T u₀ u t) ∧
    h2VecNormSqR3 (duhamelOpR3 ν T u₀ u t) ≤ M := by
  have hM_nn : 0 ≤ M := le_trans (by linarith [h2VecNormSqR3_nonneg u₀]) hM_ge
  have hbd := duhamelOpR3_inH2_and_bound hν hT hM_nn hu₀ hu t
  refine ⟨hbd.1, le_trans hbd.2 ?_⟩
  have hnl : (64 * Real.pi ^ 2 * T / ν) * M ^ 2 ≤ (1 / 8 : ℝ) * M := by
    have hq : 64 * Real.pi ^ 2 * T * M / ν ≤ 1 / 8 := by
      rw [div_le_iff₀ hν]; linarith
    have hmul := mul_le_mul_of_nonneg_right hq hM_nn
    have heq : (64 * Real.pi ^ 2 * T * M / ν) * M = (64 * Real.pi ^ 2 * T / ν) * M ^ 2 := by ring
    linarith
  linarith

/-- **THEOREM 15D2-8 (Geometric `(1/4)^n` Cauchy Contraction of Whole-Space `ℝ³` Picard Iterates):**
    Under `512 π² T M ≤ ν`, successive Picard iterates `picardIterR3 ν T u₀` satisfy the exact
    geometric decay `h2VecNormSqR3 (u^{(n+1)}(t) - u^{(n)}(t)) ≤ (4 M) · (1 / 4)^n` for all `n, t`. -/
theorem picardIterR3_cauchy_geometric_r3 {ν T M : ℝ} (hν : 0 < ν) (hT : 0 ≤ T) (hM : 0 ≤ M)
    (hsmall : 512 * Real.pi ^ 2 * T * M ≤ ν) (u₀ : VecFieldR3C)
    (hadm : ∀ n : ℕ, IsAdmissibleCurveR3 M (picardIterR3 ν T u₀ n)) :
    ∀ (n : ℕ) (t : ℝ),
      h2VecNormSqR3 (fun ξ c =>
        picardIterR3 ν T u₀ (n + 1) t ξ c - picardIterR3 ν T u₀ n t ξ c) ≤
      (4 * M) * (1 / 4 : ℝ) ^ n := by
  intro n
  induction n with
  | zero =>
    intro t
    simp only [pow_zero, mul_one]
    have h1 := (inH2VecR3_sub ((hadm 1).h_inH2 t) ((hadm 0).h_inH2 t)).2
    linarith [(hadm 1).h_bound t, (hadm 0).h_bound t]
  | succ k ih =>
    intro t
    have hq := duhamelOpR3_contraction_quarter hν hT hM (by positivity) hsmall u₀
      (hadm (k + 1)) (hadm k) ih t
    calc h2VecNormSqR3 (fun ξ c =>
          picardIterR3 ν T u₀ (k + 2) t ξ c - picardIterR3 ν T u₀ (k + 1) t ξ c)
        ≤ (1 / 4 : ℝ) * ((4 * M) * (1 / 4 : ℝ) ^ k) := hq
      _ = (4 * M) * (1 / 4 : ℝ) ^ (k + 1) := by rw [pow_succ]; ring

#print axioms r3Integral_inv_h2WeightR3
#print axioms h2R3_l1_embedding
#print axioms young_l1_l2_r3
#print axioms convR3_tame_and_banach_algebra
#print axioms convR3_self_sub_lipschitz
#print axioms lerayProjR3C_solenoidal_and_contraction
#print axioms heatSmoothedBilinearR3_structure
#print axioms heatSmoothedBilinearR3_inH2_and_bound
#print axioms heatSmoothedBilinearR3_self_sub_lipschitz
#print axioms synthVecR3_continuous_Linf_and_fourierSynth_bridge
#print axioms integral_h2R3_bound_of_inv_sqrt_decay
#print axioms continuous_convR3_of_H2_cont
#print axioms duhamelOpR3_inH2_and_bound
#print axioms duhamelOpR3_contraction_quarter
#print axioms pressureCoeffR3_poisson_and_momentum_splitting
#print axioms mild_solution_unique_r3
#print axioms maximal_existence_blowup_alternative_r3
#print axioms duhamelOpR3_self_map_ball
#print axioms picardIterR3_cauchy_geometric_r3

end GarryWholeSpaceR3LocalExistence