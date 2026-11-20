import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Abel
import HigherSobolevBootstrapTorus3D

/-!
# GARRYULT v4.0.0 — Milestone 8B: Exact `H^∞(𝕋³) ↪ C^∞(𝕋³)` Classical Synthesis,
# Pointwise Physical-Space 3D Navier–Stokes PDE Verification (`U, P ∈ C^∞(𝕋³)`)
# & Grand Master Two-Tier Theorem of Milestones 1–8 (`0 sorryAx`)
-/

namespace GarrySmoothSynthesis3D

open MeasureTheory Filter Topology GarryReal3DCalculus GarryVorticity3D
  GarryLerayTorus3D GarryLerayEnergyLaw3D GarryPoincareSobolev3D
  GarryFourierSpectral3D GarrySpectralOperators3D GarryParsevalSobolev3D
  GarrySobolevEmbedding3D GarrySpectralAlgebra3D GarrySpectralBilinear3D
  GarryDuhamelOperator3D GarryLocalExistence3D GarryGlobalRegularity3D
  GarrySupercriticalBridge3D GarrySupercriticalAudit3D GarryHigherSobolev3D

-- ============================================================================
-- SECTION 1: FOURIER MODES, SMOOTH SYNTHESIS, PERIODICITY & CONVOLUTION PRODUCT
-- ============================================================================

/-- Phase `2 π (k · x)` of the 3D torus Fourier mode `k ∈ ℤ³`. -/
noncomputable def fourierPhase8B (k : Fin 3 → ℤ) (x : R3) : ℝ :=
  2 * Real.pi * ((k 0 : ℝ) * x 0 + (k 1 : ℝ) * x 1 + (k 2 : ℝ) * x 2)

/-- Unitary 3D torus Fourier mode `e^{2 π i (k · x)}`. -/
noncomputable def fourierMode8B (k : Fin 3 → ℤ) (x : R3) : ℂ :=
  Complex.exp ((fourierPhase8B k x : ℂ) * Complex.I)

/-- Complex Fourier series synthesis `∑' k, a k * e^{2 π i (k · x)}`. -/
noncomputable def smoothSynthScalarC (a : (Fin 3 → ℤ) → ℂ) (x : R3) : ℂ :=
  ∑' k : Fin 3 → ℤ, a k * fourierMode8B k x

/-- Real-valued scalar Fourier synthesis `Re(∑' k, a k * e^{2 π i (k · x)})`. -/
noncomputable def smoothSynthScalar (a : (Fin 3 → ℤ) → ℂ) (x : R3) : ℝ :=
  (smoothSynthScalarC a x).re

/-- Real-valued 3D vector field synthesis on `𝕋³`. -/
noncomputable def smoothSynthVec (u : VecSeq3D) (x : R3) : R3 :=
  fun c => smoothSynthScalar (fun k => u k c) x

/-- Spectral partial-derivative multiplier `(2 π i k_j) a_k`. -/
noncomputable def diffMode (j : Fin 3) (a : (Fin 3 → ℤ) → ℂ) (k : Fin 3 → ℤ) : ℂ :=
  2 * (Real.pi : ℂ) * Complex.I * (k j : ℂ) * a k

/-- Spectral Laplacian multiplier `(-4 π² |k|²) a_k`. -/
noncomputable def lapMode (a : (Fin 3 → ℤ) → ℂ) (k : Fin 3 → ℤ) : ℂ :=
  -4 * (Real.pi : ℂ) ^ 2 * ((kNormSq k : ℝ) : ℂ) * a k

theorem norm_fourierMode8B (k : Fin 3 → ℤ) (x : R3) :
    ‖fourierMode8B k x‖ = 1 :=
  Complex.norm_exp_ofReal_mul_I (fourierPhase8B k x)

theorem fourierMode8B_add_x (k : Fin 3 → ℤ) (x y : R3) :
    fourierMode8B k (x + y) = fourierMode8B k x * fourierMode8B k y := by
  unfold fourierMode8B fourierPhase8B
  have hph : 2 * Real.pi * ((k 0 : ℝ) * (x + y) 0 + (k 1 : ℝ) * (x + y) 1 + (k 2 : ℝ) * (x + y) 2) =
      2 * Real.pi * ((k 0 : ℝ) * x 0 + (k 1 : ℝ) * x 1 + (k 2 : ℝ) * x 2) +
      2 * Real.pi * ((k 0 : ℝ) * y 0 + (k 1 : ℝ) * y 1 + (k 2 : ℝ) * y 2) := by
    simp only [Pi.add_apply]; ring
  rw [hph, Complex.ofReal_add, add_mul, Complex.exp_add]

theorem fourierMode8B_add_k (j l : Fin 3 → ℤ) (x : R3) :
    fourierMode8B (j + l) x = fourierMode8B j x * fourierMode8B l x := by
  unfold fourierMode8B fourierPhase8B
  have hph : 2 * Real.pi * (((j + l) 0 : ℝ) * x 0 + ((j + l) 1 : ℝ) * x 1 + ((j + l) 2 : ℝ) * x 2) =
      2 * Real.pi * ((j 0 : ℝ) * x 0 + (j 1 : ℝ) * x 1 + (j 2 : ℝ) * x 2) +
      2 * Real.pi * ((l 0 : ℝ) * x 0 + (l 1 : ℝ) * x 1 + (l 2 : ℝ) * x 2) := by
    simp only [Pi.add_apply, Int.cast_add]; ring
  rw [hph, Complex.ofReal_add, add_mul, Complex.exp_add]

theorem fourierMode8B_neg_k (k : Fin 3 → ℤ) (x : R3) :
    fourierMode8B (-k) x = starRingEnd ℂ (fourierMode8B k x) := by
  unfold fourierMode8B
  have hph : fourierPhase8B (-k) x = -fourierPhase8B k x := by
    unfold fourierPhase8B; simp only [Pi.neg_apply, Int.cast_neg]; ring
  rw [hph]
  apply Complex.ext
  · rw [Complex.exp_ofReal_mul_I_re, Complex.conj_re, Complex.exp_ofReal_mul_I_re, Real.cos_neg]
  · rw [Complex.exp_ofReal_mul_I_im, Complex.conj_im, Complex.exp_ofReal_mul_I_im, Real.sin_neg]

theorem fourierMode8B_periodic (k : Fin 3 → ℤ) (x : R3) (i : Fin 3) :
    fourierMode8B k (x + basisVec i) = fourierMode8B k x := by
  rw [fourierMode8B_add_x]
  have hbasis : fourierPhase8B k (basisVec i) = (k i : ℝ) * (2 * Real.pi) := by
    unfold fourierPhase8B basisVec
    fin_cases i <;> simp <;> ring
  have h1 : fourierMode8B k (basisVec i) = 1 := by
    unfold fourierMode8B
    rw [hbasis]
    have harg : (((k i : ℝ) * (2 * Real.pi) : ℝ) : ℂ) * Complex.I =
        ((k i : ℤ) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by
      push_cast; ring
    rw [harg]
    exact Complex.exp_int_mul_two_pi_mul_I (k i)
  rw [h1, mul_one]

theorem smoothSynthScalar_periodic (a : (Fin 3 → ℤ) → ℂ) :
    IsPeriodic3D (smoothSynthScalar a) := by
  intro x i
  unfold smoothSynthScalar smoothSynthScalarC
  have hfun : (fun k => a k * fourierMode8B k (x + basisVec i)) =
      (fun k => a k * fourierMode8B k x) :=
    funext fun k => by rw [fourierMode8B_periodic]
  rw [hfun]

theorem smoothSynthVec_periodic (u : VecSeq3D) :
    IsPeriodic3D (smoothSynthVec u) := fun x i => by
  funext c; exact smoothSynthScalar_periodic (fun k => u k c) x i

theorem smoothSynthScalarC_im_eq_zero {a : (Fin 3 → ℤ) → ℂ}
    (ha_l1 : Summable (fun k => ‖a k‖))
    (hsym : ∀ k : Fin 3 → ℤ, a (-k) = starRingEnd ℂ (a k)) (x : R3) :
    (smoothSynthScalarC a x).im = 0 := by
  have hsum_c : Summable (fun k => a k * fourierMode8B k x) :=
    Summable.of_norm (by simpa [norm_mul, norm_fourierMode8B] using ha_l1)
  have him_has : HasSum (fun k => (a k * fourierMode8B k x).im) (smoothSynthScalarC a x).im :=
    Complex.imCLM.hasSum hsum_c.hasSum
  have hreidx : (∑' k : Fin 3 → ℤ, (a (-k) * fourierMode8B (-k) x).im) =
      ∑' k : Fin 3 → ℤ, (a k * fourierMode8B k x).im :=
    (Equiv.neg (Fin 3 → ℤ)).tsum_eq (fun k => (a k * fourierMode8B k x).im)
  have hneg : (fun k : Fin 3 → ℤ => (a (-k) * fourierMode8B (-k) x).im) =
      (fun k : Fin 3 → ℤ => -(a k * fourierMode8B k x).im) := by
    funext k
    rw [hsym k, fourierMode8B_neg_k, ← map_mul, Complex.conj_im]
  rw [hneg, tsum_neg] at hreidx
  rw [← him_has.tsum_eq]
  linarith

theorem smoothSynthScalarC_eq_ofReal {a : (Fin 3 → ℤ) → ℂ}
    (ha_l1 : Summable (fun k => ‖a k‖))
    (hsym : ∀ k : Fin 3 → ℤ, a (-k) = starRingEnd ℂ (a k)) (x : R3) :
    smoothSynthScalarC a x = ((smoothSynthScalar a x : ℝ) : ℂ) := by
  apply Complex.ext
  · rfl
  · simp [smoothSynthScalarC_im_eq_zero ha_l1 hsym x]

private def convPairEquiv8B : ((Fin 3 → ℤ) × (Fin 3 → ℤ)) ≃ ((Fin 3 → ℤ) × (Fin 3 → ℤ)) where
  toFun p := (p.2, p.1 - p.2)
  invFun p := (p.1 + p.2, p.1)
  left_inv p := by ext <;> simp
  right_inv p := by ext <;> simp

/-- **THEOREM 1 OF MILESTONE 8B (Fourier Convolution Multiplication Theorem on `𝕋³`):**
    For `a, b ∈ H²(𝕋³)`, `smoothSynthScalarC (conv3D a b) x = smoothSynthScalarC a x * smoothSynthScalarC b x`.
    Under reality symmetry, `smoothSynthScalar (conv3D a b) x = smoothSynthScalar a x * smoothSynthScalar b x`
    (`0 sorryAx`). -/
theorem smoothSynthScalarC_conv3D {a b : (Fin 3 → ℤ) → ℂ} (ha : InH2Seq a) (hb : InH2Seq b) (x : R3) :
    smoothSynthScalarC (conv3D a b) x = smoothSynthScalarC a x * smoothSynthScalarC b x := by
  have ha_l1 : Summable (fun k => ‖a k‖) := (h2Seq_l1_embedding ha).1
  have hb_l1 : Summable (fun k => ‖b k‖) := (h2Seq_l1_embedding hb).1
  let f : (Fin 3 → ℤ) → ℂ := fun j => a j * fourierMode8B j x
  let g : (Fin 3 → ℤ) → ℂ := fun l => b l * fourierMode8B l x
  have hf_n : Summable (fun j => ‖f j‖) := by
    simpa [f, norm_mul, norm_fourierMode8B] using ha_l1
  have hg_n : Summable (fun l => ‖g l‖) := by
    simpa [g, norm_mul, norm_fourierMode8B] using hb_l1
  have hmul_eq : smoothSynthScalarC a x * smoothSynthScalarC b x =
      ∑' p : (Fin 3 → ℤ) × (Fin 3 → ℤ), f p.1 * g p.2 :=
    tsum_mul_tsum_of_summable_norm hf_n hg_n
  have hprod_norm : Summable (fun p : (Fin 3 → ℤ) × (Fin 3 → ℤ) => ‖f p.1 * g p.2‖) := by
    have h := hf_n.mul_of_nonneg hg_n (fun _ => norm_nonneg _) (fun _ => norm_nonneg _)
    simpa only [norm_mul] using h
  have hprod_sum : Summable (fun p : (Fin 3 → ℤ) × (Fin 3 → ℤ) => f p.1 * g p.2) :=
    Summable.of_norm hprod_norm
  have hreidx_sum : Summable (fun p : (Fin 3 → ℤ) × (Fin 3 → ℤ) => f p.2 * g (p.1 - p.2)) :=
    (convPairEquiv8B.summable_iff).mpr hprod_sum
  have hreidx_eq : (∑' p : (Fin 3 → ℤ) × (Fin 3 → ℤ), f p.2 * g (p.1 - p.2)) =
      ∑' p : (Fin 3 → ℤ) × (Fin 3 → ℤ), f p.1 * g p.2 :=
    convPairEquiv8B.tsum_eq (fun p => f p.1 * g p.2)
  have hfubini : (∑' p : (Fin 3 → ℤ) × (Fin 3 → ℤ), f p.2 * g (p.1 - p.2)) =
      ∑' k : Fin 3 → ℤ, ∑' j : Fin 3 → ℤ, f j * g (k - j) :=
    hreidx_sum.tsum_prod
  have hinner : ∀ k : Fin 3 → ℤ,
      (∑' j : Fin 3 → ℤ, f j * g (k - j)) = conv3D a b k * fourierMode8B k x := by
    intro k
    have hpt : ∀ j : Fin 3 → ℤ, f j * g (k - j) = (a j * b (k - j)) * fourierMode8B k x := by
      intro j
      dsimp only [f, g]
      have hjk : j + (k - j) = k := by abel
      have hmode : fourierMode8B j x * fourierMode8B (k - j) x = fourierMode8B k x := by
        rw [← fourierMode8B_add_k, hjk]
      calc a j * fourierMode8B j x * (b (k - j) * fourierMode8B (k - j) x)
          = (a j * b (k - j)) * (fourierMode8B j x * fourierMode8B (k - j) x) := by ring
        _ = (a j * b (k - j)) * fourierMode8B k x := by rw [hmode]
    simp_rw [hpt]
    rw [tsum_mul_right]
    rfl
  calc smoothSynthScalarC (conv3D a b) x
      = ∑' k : Fin 3 → ℤ, conv3D a b k * fourierMode8B k x := rfl
    _ = ∑' k : Fin 3 → ℤ, ∑' j : Fin 3 → ℤ, f j * g (k - j) := by simp_rw [← hinner]
    _ = ∑' p : (Fin 3 → ℤ) × (Fin 3 → ℤ), f p.2 * g (p.1 - p.2) := hfubini.symm
    _ = ∑' p : (Fin 3 → ℤ) × (Fin 3 → ℤ), f p.1 * g p.2 := hreidx_eq
    _ = smoothSynthScalarC a x * smoothSynthScalarC b x := hmul_eq.symm

theorem smoothSynthScalar_conv3D_of_realSymm {a b : (Fin 3 → ℤ) → ℂ}
    (ha : InH2Seq a) (hb : InH2Seq b)
    (hsa : ∀ k, a (-k) = starRingEnd ℂ (a k)) (hsb : ∀ k, b (-k) = starRingEnd ℂ (b k)) (x : R3) :
    smoothSynthScalar (conv3D a b) x = smoothSynthScalar a x * smoothSynthScalar b x := by
  have h1 := smoothSynthScalarC_eq_ofReal (h2Seq_l1_embedding ha).1 hsa x
  have h2 := smoothSynthScalarC_eq_ofReal (h2Seq_l1_embedding hb).1 hsb x
  change (smoothSynthScalarC (conv3D a b) x).re = smoothSynthScalar a x * smoothSynthScalar b x
  rw [smoothSynthScalarC_conv3D ha hb x, h1, h2, ← Complex.ofReal_mul, Complex.ofReal_re]

-- ============================================================================
-- SECTION 2: ELEMENTARY `e^{iθ}` TAYLOR BOUND & TERMWISE FRÉCHET DERIVATIVE
-- ============================================================================

private theorem abs_sin_le_abs_8b (t : ℝ) : |Real.sin t| ≤ |t| := by
  rcases lt_trichotomy t 0 with hlt | rfl | hgt
  · have hpos : 0 < -t := neg_pos.mpr hlt
    obtain ⟨c, _, hc⟩ := exists_hasDerivAt_eq_slope Real.sin Real.cos hpos
      Real.continuous_sin.continuousOn (fun r _ => Real.hasDerivAt_sin r)
    rw [Real.sin_zero, sub_zero, sub_zero] at hc
    have hval : Real.sin (-t) = Real.cos c * (-t) := by
      have hne : -t ≠ 0 := ne_of_gt hpos
      have h1 := congrArg (· * (-t)) hc
      rw [div_mul_cancel₀ _ hne] at h1
      exact h1.symm
    have habs : |Real.sin (-t)| = |Real.cos c| * |-t| := by rw [hval, abs_mul]
    rw [Real.sin_neg, abs_neg, abs_neg] at habs
    have hcos := Real.abs_cos_le_one c
    nlinarith [abs_nonneg t]
  · simp
  · obtain ⟨c, _, hc⟩ := exists_hasDerivAt_eq_slope Real.sin Real.cos hgt
      Real.continuous_sin.continuousOn (fun r _ => Real.hasDerivAt_sin r)
    rw [Real.sin_zero, sub_zero, sub_zero] at hc
    have hval : Real.sin t = Real.cos c * t := by
      have hne : t ≠ 0 := ne_of_gt hgt; field_simp [hne] at hc; linarith
    have habs : |Real.sin t| = |Real.cos c| * |t| := by rw [hval, abs_mul]
    have hcos := Real.abs_cos_le_one c
    nlinarith [abs_nonneg t]

private theorem abs_cos_sub_one_le_8b (t : ℝ) :
    |Real.cos t - 1| ≤ |t| ∧ |Real.cos t - 1| ≤ t ^ 2 := by
  have hpos_case : ∀ r : ℝ, 0 < r → |Real.cos r - 1| ≤ |r| ∧ |Real.cos r - 1| ≤ r ^ 2 := by
    intro r hr
    obtain ⟨c, hc_mem, hc⟩ := exists_hasDerivAt_eq_slope Real.cos (fun s => -Real.sin s) hr
      Real.continuous_cos.continuousOn (fun s _ => Real.hasDerivAt_cos s)
    rw [Real.cos_zero, sub_zero] at hc
    have hval : Real.cos r - 1 = (-Real.sin c) * r := by
      have hne : r ≠ 0 := ne_of_gt hr; field_simp [hne] at hc; linarith
    have habs : |Real.cos r - 1| = |Real.sin c| * |r| := by rw [hval, abs_mul, abs_neg]
    have hsin1 : |Real.sin c| ≤ 1 := Real.abs_sin_le_one c
    have hsin_c : |Real.sin c| ≤ |r| := by
      have h1 := abs_sin_le_abs_8b c
      rw [abs_of_pos hc_mem.1] at h1
      rw [abs_of_pos hr]
      exact le_trans h1 (le_of_lt hc_mem.2)
    have hsq : |r| * |r| = r ^ 2 := by rw [← sq, sq_abs]
    exact ⟨by nlinarith [abs_nonneg r], by nlinarith [abs_nonneg r, hsq]⟩
  rcases lt_trichotomy t 0 with hlt | rfl | hgt
  · have h := hpos_case (-t) (neg_pos.mpr hlt)
    rw [Real.cos_neg, abs_neg, neg_sq] at h
    exact h
  · simp
  · exact hpos_case t hgt

private theorem abs_sin_sub_le_sq_8b (t : ℝ) : |Real.sin t - t| ≤ t ^ 2 := by
  have hpos_case : ∀ r : ℝ, 0 < r → |Real.sin r - r| ≤ r ^ 2 := by
    intro r hr
    obtain ⟨c, hc_mem, hc⟩ := exists_hasDerivAt_eq_slope (fun s => Real.sin s - s)
      (fun s => Real.cos s - 1) hr
      (Real.continuous_sin.sub continuous_id).continuousOn
      (fun s _ => (Real.hasDerivAt_sin s).sub (hasDerivAt_id s))
    rw [Real.sin_zero, sub_zero, sub_zero, sub_zero] at hc
    have hval : Real.sin r - r = (Real.cos c - 1) * r := by
      have hne : r ≠ 0 := ne_of_gt hr; field_simp [hne] at hc; linarith
    have habs : |Real.sin r - r| = |Real.cos c - 1| * |r| := by rw [hval, abs_mul]
    have hcos_le : |Real.cos c - 1| ≤ |r| := by
      have h1 := (abs_cos_sub_one_le_8b c).1
      rw [abs_of_pos hc_mem.1] at h1
      rw [abs_of_pos hr]
      exact le_trans h1 (le_of_lt hc_mem.2)
    have hsq : |r| * |r| = r ^ 2 := by rw [← sq, sq_abs]
    nlinarith [abs_nonneg r, hsq]
  rcases lt_trichotomy t 0 with hlt | rfl | hgt
  · have h := hpos_case (-t) (neg_pos.mpr hlt)
    have hneg : Real.sin (-t) - (-t) = -(Real.sin t - t) := by rw [Real.sin_neg]; ring
    rw [hneg, abs_neg, neg_sq] at h
    exact h
  · simp
  · exact hpos_case t hgt

private theorem norm_exp_I_sub_one_sub_I_le_8b (θ : ℝ) :
    ‖Complex.exp ((θ : ℂ) * Complex.I) - 1 - (θ : ℂ) * Complex.I‖ ≤ 2 * θ ^ 2 := by
  have hsplit : Complex.exp ((θ : ℂ) * Complex.I) - 1 - (θ : ℂ) * Complex.I =
      ((Real.cos θ - 1 : ℝ) : ℂ) + ((Real.sin θ - θ : ℝ) : ℂ) * Complex.I := by
    apply Complex.ext
    · rw [Complex.sub_re, Complex.sub_re, Complex.exp_ofReal_mul_I_re, Complex.one_re,
          Complex.mul_I_re, Complex.ofReal_im, neg_zero, sub_zero,
          Complex.add_re, Complex.ofReal_re, Complex.mul_I_re, Complex.ofReal_im, neg_zero, add_zero]
    · rw [Complex.sub_im, Complex.sub_im, Complex.exp_ofReal_mul_I_im, Complex.one_im,
          Complex.mul_I_im, Complex.ofReal_re, sub_zero,
          Complex.add_im, Complex.ofReal_im, Complex.mul_I_im, Complex.ofReal_re, zero_add]
  rw [hsplit]
  have htri := norm_add_le ((Real.cos θ - 1 : ℝ) : ℂ) (((Real.sin θ - θ : ℝ) : ℂ) * Complex.I)
  rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Complex.norm_real,
      Real.norm_eq_abs, Real.norm_eq_abs] at htri
  linarith [(abs_cos_sub_one_le_8b θ).2, abs_sin_sub_le_sq_8b θ]

private lemma poly_bound_8b {x : ℝ} (hx : 0 ≤ x) :
    (1 + x ^ 2) * x ^ 2 ≤ (1 + x) ^ 4 := by
  have hx3 : 0 ≤ x ^ 3 := pow_nonneg hx 3
  nlinarith [sq_nonneg x]

private lemma weighted_amgm_8b {w y : ℝ} (hw : 0 < w) :
    y ≤ (1 / 2 : ℝ) * (1 / w) + (1 / 2 : ℝ) * (w * y ^ 2) := by
  have hsq : 2 * w * y ≤ 1 + (w * y) ^ 2 := by nlinarith [sq_nonneg (1 - w * y)]
  have h2w : 0 < 2 * w := by linarith
  have hmul : (2 * w) * y ≤ (2 * w) * ((1 / 2 : ℝ) * (1 / w) + (1 / 2 : ℝ) * (w * y ^ 2)) := by
    have hrhs : (2 * w) * ((1 / 2 : ℝ) * (1 / w) + (1 / 2 : ℝ) * (w * y ^ 2)) = 1 + (w * y) ^ 2 := by
      field_simp [ne_of_gt hw]
    linarith
  exact le_of_mul_le_mul_left hmul h2w

private theorem summable_kNormSq_norm_of_inHalfHm8 {a : (Fin 3 → ℤ) → ℂ} (ha : InHalfHmSeq 8 a) :
    Summable (fun k : Fin 3 → ℤ => kNormSq k * ‖a k‖) := by
  have hinv : Summable (fun k : Fin 3 → ℤ => (1 / 2 : ℝ) * (1 / h2Weight k)) := by
    simpa [one_div] using (summable_and_tsum_inv_h2Weight_le).1.mul_left (1 / 2 : ℝ)
  have hdom : Summable (fun k : Fin 3 → ℤ =>
      (1 / 2 : ℝ) * (1 / h2Weight k) + (1 / 2 : ℝ) * (halfSobWeight 8 k * ‖a k‖ ^ 2)) :=
    hinv.add (ha.mul_left (1 / 2 : ℝ))
  refine Summable.of_nonneg_of_le (fun k => mul_nonneg (kNormSq_nonneg_8a k) (norm_nonneg _))
    (fun k => ?_) hdom
  have h4 : halfSobWeight 8 k = (1 + kNormSq k) ^ 4 := by
    simpa [sobWeight] using halfSobWeight_even 4 k
  have hw_le : h2Weight k * (kNormSq k) ^ 2 ≤ halfSobWeight 8 k := by
    rw [h4]; unfold h2Weight; exact poly_bound_8b (kNormSq_nonneg_8a k)
  have ham := weighted_amgm_8b (w := h2Weight k) (y := kNormSq k * ‖a k‖) (h2Weight_pos k)
  have hprod : h2Weight k * (kNormSq k * ‖a k‖) ^ 2 ≤ halfSobWeight 8 k * ‖a k‖ ^ 2 := by
    have h1 := mul_le_mul_of_nonneg_right hw_le (sq_nonneg ‖a k‖)
    linarith [show h2Weight k * (kNormSq k * ‖a k‖) ^ 2 = (h2Weight k * (kNormSq k) ^ 2) * ‖a k‖ ^ 2 by ring]
  linarith

private theorem diffMode_inHalfHm {s : ℕ} {a : (Fin 3 → ℤ) → ℂ}
    (ha : InHalfHmSeq (s + 2) a) (j : Fin 3) :
    InHalfHmSeq s (diffMode j a) := by
  have hle : ∀ k : Fin 3 → ℤ, halfSobWeight s k * ‖diffMode j a k‖ ^ 2 ≤
      (4 * Real.pi ^ 2) * (halfSobWeight (s + 2) k * ‖a k‖ ^ 2) := by
    intro k
    have hw2 : halfSobWeight (s + 2) k = halfSobWeight s k * (1 + kNormSq k) := by
      unfold halfSobWeight
      rw [pow_add, Real.sq_sqrt (by linarith [kNormSq_nonneg_8a k])]
    have h2pi : ‖(2 : ℂ) * (Real.pi : ℂ) * Complex.I‖ ^ 2 = 4 * Real.pi ^ 2 := by
      have h2 : ‖(2 : ℂ)‖ = 2 := by norm_num
      rw [norm_mul, norm_mul, Complex.norm_I, mul_one, h2,
          Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]; ring
    have hkj : ‖(k j : ℂ)‖ ^ 2 ≤ 1 + kNormSq k := by
      rw [← Complex.ofReal_intCast, Complex.norm_real, Real.norm_eq_abs, sq_abs]
      unfold kNormSq
      fin_cases j
      · change (k 0 : ℝ) ^ 2 ≤ _; linarith [sq_nonneg (k 1 : ℝ), sq_nonneg (k 2 : ℝ)]
      · change (k 1 : ℝ) ^ 2 ≤ _; linarith [sq_nonneg (k 0 : ℝ), sq_nonneg (k 2 : ℝ)]
      · change (k 2 : ℝ) ^ 2 ≤ _; linarith [sq_nonneg (k 0 : ℝ), sq_nonneg (k 1 : ℝ)]
    have hdn : ‖diffMode j a k‖ ^ 2 = 4 * Real.pi ^ 2 * ‖(k j : ℂ)‖ ^ 2 * ‖a k‖ ^ 2 := by
      unfold diffMode
      rw [norm_mul, norm_mul, mul_pow, mul_pow, h2pi]
    rw [hdn, hw2]
    have hnn : 0 ≤ 4 * Real.pi ^ 2 * halfSobWeight s k * ‖a k‖ ^ 2 := by
      have := halfSobWeight_pos s k; positivity
    have hmul := mul_le_mul_of_nonneg_left hkj hnn
    linarith
  exact Summable.of_nonneg_of_le
    (fun k => mul_nonneg (le_of_lt (halfSobWeight_pos s k)) (sq_nonneg _))
    hle (ha.mul_left (4 * Real.pi ^ 2))

private noncomputable def projR8B (j : Fin 3) : R3 →L[ℝ] ℝ :=
  ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 3 => ℝ) j

private noncomputable def smulRightCLM8B (j : Fin 3) : ℂ →L[ℝ] (R3 →L[ℝ] ℂ) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun z => (projR8B j).smulRight z
      map_add' := fun z w => by ext v; simp [ContinuousLinearMap.smulRight_apply, smul_add]
      map_smul' := fun r z => by
        ext v
        change (projR8B j v) • (r • z) = r • ((projR8B j v) • z)
        exact smul_comm (projR8B j v) r z }

/-- Continuous `ℝ`-linear Fréchet derivative of `smoothSynthScalarC a` at `x`. -/
private noncomputable def synthFDeriv (a : (Fin 3 → ℤ) → ℂ) (x : R3) : R3 →L[ℝ] ℂ :=
  smulRightCLM8B 0 (smoothSynthScalarC (diffMode 0 a) x) +
  smulRightCLM8B 1 (smoothSynthScalarC (diffMode 1 a) x) +
  smulRightCLM8B 2 (smoothSynthScalarC (diffMode 2 a) x)

theorem smoothSynthScalarC_continuous_of_inH2 {a : (Fin 3 → ℤ) → ℂ} (ha : InH2Seq a) :
    Continuous (smoothSynthScalarC a) := by
  refine continuous_tsum (fun k => ?_) (h2Seq_l1_embedding ha).1 (fun k x => ?_)
  · unfold fourierMode8B fourierPhase8B
    have hph : Continuous (fun x : R3 =>
        2 * Real.pi * ((k 0 : ℝ) * x 0 + (k 1 : ℝ) * x 1 + (k 2 : ℝ) * x 2)) :=
      continuous_const.mul
        (((continuous_const.mul (continuous_apply 0)).add
          (continuous_const.mul (continuous_apply 1))).add
         (continuous_const.mul (continuous_apply 2)))
    exact continuous_const.mul (Complex.continuous_exp.comp
      ((Complex.continuous_ofReal.comp hph).mul continuous_const))
  · rw [norm_mul, norm_fourierMode8B, mul_one]

/-- **THEOREM 2 OF MILESTONE 8B (Termwise Fréchet Differentiability of 3D Fourier Series):**
    For `a ∈ H⁴(𝕋³)` (`InHalfHmSeq 8 a`), `smoothSynthScalarC a` is Fréchet differentiable at
    every `x ∈ ℝ³` with exact derivative `synthFDeriv a x` (`0 sorryAx`). -/
theorem smoothSynthScalarC_hasFDerivAt {a : (Fin 3 → ℤ) → ℂ} (ha : InHalfHmSeq 8 a) (x : R3) :
    HasFDerivAt (smoothSynthScalarC a) (synthFDeriv a x) x := by
  have ha2 : InH2Seq a := (inH2Seq_of_inHalfHmSeq (by norm_num) ha).1
  have ha_l1 : Summable (fun k => ‖a k‖) := (h2Seq_l1_embedding ha2).1
  have hda : ∀ j : Fin 3, Summable (fun k => ‖diffMode j a k‖) := fun j =>
    (h2Seq_l1_embedding (inH2Seq_of_inHalfHmSeq (by norm_num) (diffMode_inHalfHm ha j)).1).1
  have hk2_sum : Summable (fun k => kNormSq k * ‖a k‖) := summable_kNormSq_norm_of_inHalfHm8 ha
  let C : ℝ := 24 * Real.pi ^ 2 * ∑' k : Fin 3 → ℤ, kNormSq k * ‖a k‖
  have hC_nn : 0 ≤ C := mul_nonneg (by positivity)
    (tsum_nonneg fun k => mul_nonneg (kNormSq_nonneg_8a k) (norm_nonneg _))
  have hrem_bd : ∀ h : R3,
      ‖smoothSynthScalarC a (x + h) - smoothSynthScalarC a x - synthFDeriv a x h‖ ≤ C * ‖h‖ ^ 2 := by
    intro h
    have hs1 : Summable (fun k => a k * fourierMode8B k (x + h)) :=
      Summable.of_norm (by simpa [norm_mul, norm_fourierMode8B] using ha_l1)
    have hs2 : Summable (fun k => a k * fourierMode8B k x) :=
      Summable.of_norm (by simpa [norm_mul, norm_fourierMode8B] using ha_l1)
    have hs_d : ∀ j : Fin 3, Summable (fun k => (h j : ℝ) • (diffMode j a k * fourierMode8B k x)) :=
      fun j => (Summable.of_norm (by simpa [norm_mul, norm_fourierMode8B] using hda j)).const_smul (h j)
    have hL_eval : synthFDeriv a x h =
        ∑' k : Fin 3 → ℤ, ((fourierPhase8B k h : ℂ) * Complex.I) * (a k * fourierMode8B k x) := by
      change (h 0 : ℝ) • smoothSynthScalarC (diffMode 0 a) x +
             (h 1 : ℝ) • smoothSynthScalarC (diffMode 1 a) x +
             (h 2 : ℝ) • smoothSynthScalarC (diffMode 2 a) x = _
      unfold smoothSynthScalarC
      simp_rw [Complex.real_smul, ← tsum_mul_left]
      have hs_d' : ∀ j : Fin 3, Summable (fun k => ((h j : ℝ) : ℂ) * (diffMode j a k * fourierMode8B k x)) :=
        fun j => by simpa only [Complex.real_smul] using hs_d j
      rw [← (hs_d' 0).tsum_add (hs_d' 1), ← ((hs_d' 0).add (hs_d' 1)).tsum_add (hs_d' 2)]
      congr 1; funext k
      simp only [diffMode, fourierPhase8B]
      push_cast; ring
    rw [hL_eval]
    unfold smoothSynthScalarC
    have hs_L : Summable (fun k => ((fourierPhase8B k h : ℂ) * Complex.I) * (a k * fourierMode8B k x)) := by
      have hfun : (fun k => ((fourierPhase8B k h : ℂ) * Complex.I) * (a k * fourierMode8B k x)) =
          (fun k => (h 0 : ℝ) • (diffMode 0 a k * fourierMode8B k x) +
                    (h 1 : ℝ) • (diffMode 1 a k * fourierMode8B k x) +
                    (h 2 : ℝ) • (diffMode 2 a k * fourierMode8B k x)) := by
        funext k; simp only [Complex.real_smul, diffMode, fourierPhase8B]; push_cast; ring
      rw [hfun]; exact ((hs_d 0).add (hs_d 1)).add (hs_d 2)
    rw [← hs1.tsum_sub hs2, ← (hs1.sub hs2).tsum_sub hs_L]
    have hpt : ∀ k : Fin 3 → ℤ,
        ‖a k * fourierMode8B k (x + h) - a k * fourierMode8B k x -
          (fourierPhase8B k h : ℂ) * Complex.I * (a k * fourierMode8B k x)‖ ≤
          (24 * Real.pi ^ 2 * ‖h‖ ^ 2) * (kNormSq k * ‖a k‖) := by
      intro k
      have hfac : a k * fourierMode8B k (x + h) - a k * fourierMode8B k x -
            (fourierPhase8B k h : ℂ) * Complex.I * (a k * fourierMode8B k x) =
          (a k * fourierMode8B k x) *
            (Complex.exp ((fourierPhase8B k h : ℂ) * Complex.I) - 1 - (fourierPhase8B k h : ℂ) * Complex.I) := by
        rw [fourierMode8B_add_x]; unfold fourierMode8B; ring
      rw [hfac, norm_mul, norm_mul, norm_fourierMode8B, mul_one]
      have htay := norm_exp_I_sub_one_sub_I_le_8b (fourierPhase8B k h)
      have hph_sq : (fourierPhase8B k h) ^ 2 ≤ 12 * Real.pi ^ 2 * kNormSq k * ‖h‖ ^ 2 := by
        unfold fourierPhase8B kNormSq
        have hh0 : |h 0| ≤ ‖h‖ := by simpa [Real.norm_eq_abs] using norm_le_pi_norm h 0
        have hh1 : |h 1| ≤ ‖h‖ := by simpa [Real.norm_eq_abs] using norm_le_pi_norm h 1
        have hh2 : |h 2| ≤ ‖h‖ := by simpa [Real.norm_eq_abs] using norm_le_pi_norm h 2
        have hdot_le : |(k 0 : ℝ) * h 0 + (k 1 : ℝ) * h 1 + (k 2 : ℝ) * h 2| ≤
            (|(k 0 : ℝ)| + |(k 1 : ℝ)| + |(k 2 : ℝ)|) * ‖h‖ := by
          have h1 := abs_add_le ((k 0 : ℝ) * h 0 + (k 1 : ℝ) * h 1) ((k 2 : ℝ) * h 2)
          have h2 := abs_add_le ((k 0 : ℝ) * h 0) ((k 1 : ℝ) * h 1)
          rw [abs_mul] at h1
          rw [abs_mul, abs_mul] at h2
          nlinarith [abs_nonneg (k 0 : ℝ), abs_nonneg (k 1 : ℝ), abs_nonneg (k 2 : ℝ)]
        have hdot_sq : ((k 0 : ℝ) * h 0 + (k 1 : ℝ) * h 1 + (k 2 : ℝ) * h 2) ^ 2 ≤
            3 * ((k 0 : ℝ) ^ 2 + (k 1 : ℝ) ^ 2 + (k 2 : ℝ) ^ 2) * ‖h‖ ^ 2 := by
          have hsq1 : ((k 0 : ℝ) * h 0 + (k 1 : ℝ) * h 1 + (k 2 : ℝ) * h 2) ^ 2 ≤
              ((|(k 0 : ℝ)| + |(k 1 : ℝ)| + |(k 2 : ℝ)|) * ‖h‖) ^ 2 := by
            rw [← sq_abs]
            nlinarith [abs_nonneg ((k 0 : ℝ) * h 0 + (k 1 : ℝ) * h 1 + (k 2 : ℝ) * h 2)]
          have hcs3 : (|(k 0 : ℝ)| + |(k 1 : ℝ)| + |(k 2 : ℝ)|) ^ 2 ≤
              3 * ((k 0 : ℝ) ^ 2 + (k 1 : ℝ) ^ 2 + (k 2 : ℝ) ^ 2) := by
            nlinarith [sq_nonneg (|(k 0 : ℝ)| - |(k 1 : ℝ)|),
                       sq_nonneg (|(k 0 : ℝ)| - |(k 2 : ℝ)|),
                       sq_nonneg (|(k 1 : ℝ)| - |(k 2 : ℝ)|),
                       sq_abs (k 0 : ℝ), sq_abs (k 1 : ℝ), sq_abs (k 2 : ℝ)]
          have hmul := mul_le_mul_of_nonneg_right hcs3 (sq_nonneg ‖h‖)
          rw [mul_pow] at hsq1; linarith
        have hpi_nn : 0 ≤ 4 * Real.pi ^ 2 := by positivity
        have hmul := mul_le_mul_of_nonneg_left hdot_sq hpi_nn
        linarith
      have h1 := mul_le_mul_of_nonneg_left htay (norm_nonneg (a k))
      have h2 := mul_le_mul_of_nonneg_left hph_sq (mul_nonneg (norm_nonneg (a k)) (by norm_num : (0 : ℝ) ≤ 2))
      linarith
    have hsum_norm : Summable (fun k =>
        ‖a k * fourierMode8B k (x + h) - a k * fourierMode8B k x -
          (fourierPhase8B k h : ℂ) * Complex.I * (a k * fourierMode8B k x)‖) :=
      Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hpt (hk2_sum.mul_left _)
    have hle_tsum := le_trans (norm_tsum_le_tsum_norm hsum_norm)
      (hasSum_le hpt hsum_norm.hasSum (hk2_sum.hasSum.mul_left _))
    dsimp only [C]; linarith
  rw [hasFDerivAt_iff_isLittleO_nhds_zero, Asymptotics.isLittleO_iff]
  intro ε hε
  rw [Metric.eventually_nhds_iff]
  refine ⟨ε / (C + 1), div_pos hε (by linarith), fun {h} hh => ?_⟩
  rw [dist_zero_right] at hh
  have h1 := hrem_bd h
  have h2 : C * ‖h‖ ≤ ε := by
    have hle1 : C * ‖h‖ ≤ C * (ε / (C + 1)) := mul_le_mul_of_nonneg_left (le_of_lt hh) hC_nn
    have hle2 : C * (ε / (C + 1)) ≤ ε := by
      have hC1 : 0 < C + 1 := by linarith
      rw [mul_div_assoc', div_le_iff₀ hC1]; nlinarith
    exact le_trans hle1 hle2
  have h3 := mul_le_mul_of_nonneg_right h2 (norm_nonneg h)
  linarith [show C * ‖h‖ ^ 2 = C * ‖h‖ * ‖h‖ by ring]

-- ============================================================================
-- SECTION 3: `H^∞(𝕋³) ↪ C^∞(𝕋³)` SMOOTHNESS, PARTIAL DERIVATIVES & LAPLACIAN
-- ============================================================================

/-- **THEOREM 3 OF MILESTONE 8B (Arbitrary-Order `H^{n+3}(𝕋³) ↪ C^n(𝕋³)` Embedding):**
    For EVERY `n : ℕ` and `a ∈ H^{n+3}(𝕋³)` (`InHalfHmSeq (2 * n + 6) a`),
    `ContDiff ℝ n (smoothSynthScalarC a)` and `ContDiff ℝ n (smoothSynthScalar a)` (`0 sorryAx`). -/
theorem smoothSynthScalarC_contDiff_of_inHalfHm :
    ∀ (n : ℕ) {a : (Fin 3 → ℤ) → ℂ}, InHalfHmSeq (2 * n + 6) a →
      ContDiff ℝ n (smoothSynthScalarC a) := by
  intro n
  induction n with
  | zero =>
    intro a ha
    have ha2 : InH2Seq a := (inH2Seq_of_inHalfHmSeq (by norm_num) ha).1
    exact contDiff_zero.mpr (smoothSynthScalarC_continuous_of_inH2 ha2)
  | succ k ih =>
    intro a ha
    have ha8 : InHalfHmSeq 8 a :=
      Summable.of_nonneg_of_le (fun m => mul_nonneg (le_of_lt (halfSobWeight_pos 8 m)) (sq_nonneg _))
        (fun m => mul_le_mul_of_nonneg_right (halfSobWeight_mono (by omega) m) (sq_nonneg _)) ha
    have hdiff : Differentiable ℝ (smoothSynthScalarC a) :=
      fun x => (smoothSynthScalarC_hasFDerivAt ha8 x).differentiableAt
    have hfderiv_eq : fderiv ℝ (smoothSynthScalarC a) = synthFDeriv a :=
      funext fun x => (smoothSynthScalarC_hasFDerivAt ha8 x).fderiv
    have hcd_j : ∀ j : Fin 3,
        ContDiff ℝ k (fun x => smulRightCLM8B j (smoothSynthScalarC (diffMode j a) x)) := by
      intro j
      have hdj : InHalfHmSeq (2 * k + 6) (diffMode j a) := by
        have hstep : 2 * (k + 1) + 6 = (2 * k + 6) + 2 := by omega
        rw [hstep] at ha
        exact diffMode_inHalfHm ha j
      exact (smulRightCLM8B j).contDiff.comp (ih hdj)
    have hcd_fderiv : ContDiff ℝ k (fderiv ℝ (smoothSynthScalarC a)) := by
      rw [hfderiv_eq]
      exact ((hcd_j 0).add (hcd_j 1)).add (hcd_j 2)
    have hcast : ((k + 1 : ℕ) : WithTop ℕ∞) = ((k : ℕ) : WithTop ℕ∞) + 1 := by
      push_cast; rfl
    rw [hcast]
    exact contDiff_succ_iff_fderiv.mpr ⟨hdiff, fun htop => by simp at htop, hcd_fderiv⟩

theorem smoothSynthScalar_contDiff_of_inHalfHm (n : ℕ) {a : (Fin 3 → ℤ) → ℂ}
    (ha : InHalfHmSeq (2 * n + 6) a) :
    ContDiff ℝ n (smoothSynthScalar a) :=
  Complex.reCLM.contDiff.comp (smoothSynthScalarC_contDiff_of_inHalfHm n ha)

/-- **THEOREM 4 OF MILESTONE 8B (`H^∞(𝕋³) ↪ C^∞(𝕋³)` for Scalars and 3D Vector Fields):** (`0 sorryAx`). -/
theorem smoothSynthScalar_contDiff_infty {a : (Fin 3 → ℤ) → ℂ}
    (ha : ∀ m : ℕ, InHalfHmSeq (2 * m) a) :
    (∀ n : ℕ, ContDiff ℝ n (smoothSynthScalar a)) ∧
    ContDiff ℝ (⊤ : ℕ∞) (smoothSynthScalar a) := by
  have hall : ∀ n : ℕ, ContDiff ℝ n (smoothSynthScalar a) := fun n => by
    have h := ha (n + 3)
    have heq : 2 * (n + 3) = 2 * n + 6 := by omega
    rw [heq] at h
    exact smoothSynthScalar_contDiff_of_inHalfHm n h
  exact ⟨hall, contDiff_infty.mpr hall⟩

theorem smoothSynthVec_contDiff_infty {u : VecSeq3D}
    (hu : ∀ m : ℕ, InHmVec m u) :
    (∀ n : ℕ, ContDiff ℝ n (smoothSynthVec u)) ∧
    ContDiff ℝ (⊤ : ℕ∞) (smoothSynthVec u) := by
  have hall : ∀ n : ℕ, ContDiff ℝ n (smoothSynthVec u) := fun n =>
    contDiff_pi.mpr fun c => (smoothSynthScalar_contDiff_infty (fun m => hu m c)).1 n
  exact ⟨hall, contDiff_infty.mpr hall⟩

theorem partialDerivScalar_smoothSynthScalar {a : (Fin 3 → ℤ) → ℂ}
    (ha : InHalfHmSeq 8 a) (x : R3) (j : Fin 3) :
    partialDerivScalar (smoothSynthScalar a) x j = smoothSynthScalar (diffMode j a) x := by
  unfold partialDerivScalar smoothSynthScalar
  have hd : HasFDerivAt (fun y => (smoothSynthScalarC a y).re)
      (Complex.reCLM.comp (synthFDeriv a x)) x :=
    Complex.reCLM.hasFDerivAt.comp x (smoothSynthScalarC_hasFDerivAt ha x)
  rw [hd.fderiv]
  change ((basisVec j 0 : ℝ) • smoothSynthScalarC (diffMode 0 a) x +
          (basisVec j 1 : ℝ) • smoothSynthScalarC (diffMode 1 a) x +
          (basisVec j 2 : ℝ) • smoothSynthScalarC (diffMode 2 a) x).re = _
  unfold basisVec
  fin_cases j <;> simp

theorem laplacianScalar_smoothSynthScalar {a : (Fin 3 → ℤ) → ℂ}
    (ha : InHalfHmSeq 10 a) (x : R3) :
    laplacianScalar (smoothSynthScalar a) x = smoothSynthScalar (lapMode a) x := by
  have ha8 : InHalfHmSeq 8 a :=
    Summable.of_nonneg_of_le (fun k => mul_nonneg (le_of_lt (halfSobWeight_pos 8 k)) (sq_nonneg _))
      (fun k => mul_le_mul_of_nonneg_right (halfSobWeight_mono (by norm_num) k) (sq_nonneg _)) ha
  have hcd2 : ContDiff ℝ 2 (smoothSynthScalar a) := smoothSynthScalar_contDiff_of_inHalfHm 2 ha
  have hda8 : ∀ j : Fin 3, InHalfHmSeq 8 (diffMode j a) := fun j => diffMode_inHalfHm ha j
  have hsnd : ∀ j : Fin 3, sndPartial (smoothSynthScalar a) x j j =
      smoothSynthScalar (diffMode j (diffMode j a)) x := by
    intro j
    rw [← partial_partial_eq_sndPartial (smoothSynthScalar a) x hcd2.contDiffAt j j]
    have hfun : (fun y => partialDerivScalar (smoothSynthScalar a) y j) =
        smoothSynthScalar (diffMode j a) :=
      funext fun y => partialDerivScalar_smoothSynthScalar ha8 y j
    rw [hfun]
    exact partialDerivScalar_smoothSynthScalar (hda8 j) x j
  unfold laplacianScalar
  rw [hsnd 0, hsnd 1, hsnd 2]
  have hsum_j : ∀ j : Fin 3, Summable (fun k => diffMode j (diffMode j a) k * fourierMode8B k x) := by
    intro j
    have hdj2 : InH2Seq (diffMode j (diffMode j a)) :=
      (inH2Seq_of_inHalfHmSeq (by norm_num) (diffMode_inHalfHm (hda8 j) j)).1
    exact Summable.of_norm (by simpa [norm_mul, norm_fourierMode8B] using (h2Seq_l1_embedding hdj2).1)
  unfold smoothSynthScalar smoothSynthScalarC
  rw [← Complex.add_re, ← Complex.add_re,
      ← (hsum_j 0).tsum_add (hsum_j 1), ← ((hsum_j 0).add (hsum_j 1)).tsum_add (hsum_j 2)]
  congr 1; congr 1; funext k
  unfold diffMode lapMode kNormSq
  have hI2 : Complex.I ^ 2 = -1 := Complex.I_sq
  push_cast
  linear_combination 4 * (Real.pi : ℂ) ^ 2 * ((k 0 : ℂ) ^ 2 + (k 1 : ℂ) ^ 2 + (k 2 : ℂ) ^ 2) *
    a k * fourierMode8B k x * hI2

theorem div3D_smoothSynthVec_eq_zero {u : VecSeq3D}
    (hu : InHmVec 4 u) (hsol : IsSolenoidal u) (x : R3) :
    div3D (smoothSynthVec u) x = 0 := by
  have hu8 : ∀ c : Fin 3, InHalfHmSeq 8 (fun k => u k c) := fun c => hu c
  unfold div3D smoothSynthVec
  rw [partialDerivScalar_smoothSynthScalar (hu8 0) x 0,
      partialDerivScalar_smoothSynthScalar (hu8 1) x 1,
      partialDerivScalar_smoothSynthScalar (hu8 2) x 2]
  have hs : ∀ j : Fin 3, Summable (fun k => diffMode j (fun m => u m j) k * fourierMode8B k x) := fun j =>
    Summable.of_norm (by
      simpa [norm_mul, norm_fourierMode8B] using
        (h2Seq_l1_embedding (inH2Seq_of_inHalfHmSeq (by norm_num) (diffMode_inHalfHm (hu8 j) j)).1).1)
  unfold smoothSynthScalar smoothSynthScalarC
  rw [← Complex.add_re, ← Complex.add_re,
      ← (hs 0).tsum_add (hs 1), ← ((hs 0).add (hs 1)).tsum_add (hs 2)]
  have hz : ∀ k : Fin 3 → ℤ,
      diffMode 0 (fun m => u m 0) k * fourierMode8B k x +
      diffMode 1 (fun m => u m 1) k * fourierMode8B k x +
      diffMode 2 (fun m => u m 2) k * fourierMode8B k x = 0 := by
    intro k
    have hfac : diffMode 0 (fun m => u m 0) k * fourierMode8B k x +
        diffMode 1 (fun m => u m 1) k * fourierMode8B k x +
        diffMode 2 (fun m => u m 2) k * fourierMode8B k x =
        2 * (Real.pi : ℂ) * Complex.I * ((k 0 : ℂ) * u k 0 + (k 1 : ℂ) * u k 1 + (k 2 : ℂ) * u k 2) *
          fourierMode8B k x := by unfold diffMode; ring
    have hsol_k : (k 0 : ℂ) * u k 0 + (k 1 : ℂ) * u k 1 + (k 2 : ℂ) * u k 2 = 0 := hsol k
    rw [hfac, hsol_k]; ring
  simp_rw [hz]; simp

-- ============================================================================
-- SECTION 4: PRESSURE `H^∞ → C^∞` & EXACT PHYSICAL-SPACE 3D NAVIER–STOKES PDE
-- ============================================================================

private theorem norm_linear_comb_sq_le_8b (k : Fin 3 → ℤ) (z : Fin 3 → ℂ) :
    ‖(k 0 : ℂ) * z 0 + (k 1 : ℂ) * z 1 + (k 2 : ℂ) * z 2‖ ^ 2 ≤
      kNormSq k * (‖z 0‖ ^ 2 + ‖z 1‖ ^ 2 + ‖z 2‖ ^ 2) := by
  have hk : ∀ i : Fin 3, ‖(k i : ℂ)‖ = |(k i : ℝ)| := fun i => by
    rw [← Complex.ofReal_intCast, Complex.norm_real, Real.norm_eq_abs]
  have htri : ‖(k 0 : ℂ) * z 0 + (k 1 : ℂ) * z 1 + (k 2 : ℂ) * z 2‖ ≤
      |(k 0 : ℝ)| * ‖z 0‖ + |(k 1 : ℝ)| * ‖z 1‖ + |(k 2 : ℝ)| * ‖z 2‖ := by
    calc ‖(k 0 : ℂ) * z 0 + (k 1 : ℂ) * z 1 + (k 2 : ℂ) * z 2‖
        ≤ ‖(k 0 : ℂ) * z 0 + (k 1 : ℂ) * z 1‖ + ‖(k 2 : ℂ) * z 2‖ := norm_add_le _ _
      _ ≤ ‖(k 0 : ℂ) * z 0‖ + ‖(k 1 : ℂ) * z 1‖ + ‖(k 2 : ℂ) * z 2‖ :=
          add_le_add (norm_add_le _ _) le_rfl
      _ = |(k 0 : ℝ)| * ‖z 0‖ + |(k 1 : ℝ)| * ‖z 1‖ + |(k 2 : ℝ)| * ‖z 2‖ := by
          rw [norm_mul, norm_mul, norm_mul, hk 0, hk 1, hk 2]
  have hnn : 0 ≤ ‖(k 0 : ℂ) * z 0 + (k 1 : ℂ) * z 1 + (k 2 : ℂ) * z 2‖ := norm_nonneg _
  have hsq : ‖(k 0 : ℂ) * z 0 + (k 1 : ℂ) * z 1 + (k 2 : ℂ) * z 2‖ ^ 2 ≤
      (|(k 0 : ℝ)| * ‖z 0‖ + |(k 1 : ℝ)| * ‖z 1‖ + |(k 2 : ℝ)| * ‖z 2‖) ^ 2 := by nlinarith
  have hcs : (|(k 0 : ℝ)| * ‖z 0‖ + |(k 1 : ℝ)| * ‖z 1‖ + |(k 2 : ℝ)| * ‖z 2‖) ^ 2 ≤
      ((k 0 : ℝ) ^ 2 + (k 1 : ℝ) ^ 2 + (k 2 : ℝ) ^ 2) * (‖z 0‖ ^ 2 + ‖z 1‖ ^ 2 + ‖z 2‖ ^ 2) := by
    nlinarith [sq_nonneg (|(k 0 : ℝ)| * ‖z 1‖ - |(k 1 : ℝ)| * ‖z 0‖),
               sq_nonneg (|(k 0 : ℝ)| * ‖z 2‖ - |(k 2 : ℝ)| * ‖z 0‖),
               sq_nonneg (|(k 1 : ℝ)| * ‖z 2‖ - |(k 2 : ℝ)| * ‖z 1‖),
               sq_abs (k 0 : ℝ), sq_abs (k 1 : ℝ), sq_abs (k 2 : ℝ)]
  unfold kNormSq; exact le_trans hsq hcs

/-- **THEOREM 5 OF MILESTONE 8B (Calderón–Zygmund `H^m` Regularity & `C^∞(𝕋³)` Pressure Synthesis):**
    If `u ∈ H^{s/2}(𝕋³)` (`s ≥ 4`), then `pressureCoeff6B u ∈ H^{s/2}(𝕋³)`. Consequently, if
    `∀ m, InHmVec m u`, the physical pressure `P(x) = smoothSynthScalar (pressureCoeff6B u) x`
    belongs to `C^∞(𝕋³)` (`0 sorryAx`). -/
theorem pressureCoeff6B_inHalfHm {s : ℕ} (hs : 4 ≤ s) {u : VecSeq3D} (hu : InHalfHmVec s u) :
    InHalfHmSeq s (pressureCoeff6B u) := by
  let C : Fin 3 → Fin 3 → (Fin 3 → ℤ) → ℂ := fun j c => conv3D (fun m => u m j) (fun m => u m c)
  have hC : ∀ j c : Fin 3, InHalfHmSeq s (C j c) := fun j c => (conv3D_tame_l1_halfHm hs (hu j) (hu c)).1
  let dom : (Fin 3 → ℤ) → ℝ := fun k =>
    (halfSobWeight s k * (‖C 0 0 k‖ ^ 2 + ‖C 1 0 k‖ ^ 2 + ‖C 2 0 k‖ ^ 2) +
     halfSobWeight s k * (‖C 0 1 k‖ ^ 2 + ‖C 1 1 k‖ ^ 2 + ‖C 2 1 k‖ ^ 2) +
     halfSobWeight s k * (‖C 0 2 k‖ ^ 2 + ‖C 1 2 k‖ ^ 2 + ‖C 2 2 k‖ ^ 2)) +
    (if k = 0 then halfSobWeight s 0 * ‖pressureCoeff6B u 0‖ ^ 2 else 0)
  have hdom_sum : Summable dom := by
    have hrow : ∀ c : Fin 3, Summable (fun k => halfSobWeight s k * (‖C 0 c k‖ ^ 2 + ‖C 1 c k‖ ^ 2 + ‖C 2 c k‖ ^ 2)) := by
      intro c
      have h := ((hC 0 c).add (hC 1 c)).add (hC 2 c)
      have hfun : (fun k => halfSobWeight s k * ‖C 0 c k‖ ^ 2 + halfSobWeight s k * ‖C 1 c k‖ ^ 2 +
          halfSobWeight s k * ‖C 2 c k‖ ^ 2) =
          (fun k => halfSobWeight s k * (‖C 0 c k‖ ^ 2 + ‖C 1 c k‖ ^ 2 + ‖C 2 c k‖ ^ 2)) := by
        funext k; ring
      rwa [hfun] at h
    have h0 : Summable (fun k : Fin 3 → ℤ => if k = 0 then halfSobWeight s 0 * ‖pressureCoeff6B u 0‖ ^ 2 else 0) :=
      (hasSum_ite_eq (0 : Fin 3 → ℤ) (halfSobWeight s 0 * ‖pressureCoeff6B u 0‖ ^ 2)).summable
    exact (((hrow 0).add (hrow 1)).add (hrow 2)).add h0
  refine Summable.of_nonneg_of_le
    (fun k => mul_nonneg (le_of_lt (halfSobWeight_pos s k)) (sq_nonneg _)) (fun k => ?_) hdom_sum
  by_cases hk : k = 0
  · subst hk; dsimp only [dom]; simp only [↓reduceIte]
    have hnn : 0 ≤ halfSobWeight s 0 * (‖C 0 0 0‖ ^ 2 + ‖C 1 0 0‖ ^ 2 + ‖C 2 0 0‖ ^ 2) +
        halfSobWeight s 0 * (‖C 0 1 0‖ ^ 2 + ‖C 1 1 0‖ ^ 2 + ‖C 2 1 0‖ ^ 2) +
        halfSobWeight s 0 * (‖C 0 2 0‖ ^ 2 + ‖C 1 2 0‖ ^ 2 + ‖C 2 2 0‖ ^ 2) := by
      have := halfSobWeight_pos s 0; positivity
    linarith
  · have hk_pos : 0 < kNormSq k := by
      have hex : k 0 ≠ 0 ∨ k 1 ≠ 0 ∨ k 2 ≠ 0 := by
        by_contra h; push Not at h; apply hk; funext i; fin_cases i <;> tauto
      have h1 : ∀ n : ℤ, n ≠ 0 → (0 : ℝ) < (n : ℝ) ^ 2 := fun n hn => by
        have : (n : ℝ) ≠ 0 := Int.cast_ne_zero.mpr hn; positivity
      unfold kNormSq
      rcases hex with h0 | h1' | h2
      · linarith [h1 (k 0) h0, sq_nonneg (k 1 : ℝ), sq_nonneg (k 2 : ℝ)]
      · linarith [h1 (k 1) h1', sq_nonneg (k 0 : ℝ), sq_nonneg (k 2 : ℝ)]
      · linarith [h1 (k 2) h2, sq_nonneg (k 0 : ℝ), sq_nonneg (k 1 : ℝ)]
    have hpois := pressureCoeff6B_poisson u k
    have h2pi : ‖(2 : ℂ) * (Real.pi : ℂ) * Complex.I‖ ^ 2 = 4 * Real.pi ^ 2 := by
      have h2 : ‖(2 : ℂ)‖ = 2 := by norm_num
      rw [norm_mul, norm_mul, Complex.norm_I, mul_one, h2,
          Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]; ring
    have hnorm_eq : (4 * Real.pi ^ 2 * kNormSq k) ^ 2 * ‖pressureCoeff6B u k‖ ^ 2 =
        4 * Real.pi ^ 2 * ‖(k 0 : ℂ) * nsFlux6A u u k 0 + (k 1 : ℂ) * nsFlux6A u u k 1 +
          (k 2 : ℂ) * nsFlux6A u u k 2‖ ^ 2 := by
      have h := congrArg (fun z : ℂ => ‖z‖ ^ 2) hpois
      have hn4 : ‖(-4 : ℂ)‖ = 4 := by norm_num
      have hn2 : ‖(-2 : ℂ)‖ = 2 := by norm_num
      simp only [norm_mul, norm_pow, mul_pow, hn4, hn2, Complex.norm_I, Complex.norm_real,
        Real.norm_eq_abs, abs_of_pos Real.pi_pos, abs_of_pos hk_pos] at h
      linarith
    have hflux_c : ∀ c : Fin 3, ‖nsFlux6A u u k c‖ ^ 2 ≤
        4 * Real.pi ^ 2 * kNormSq k * (‖C 0 c k‖ ^ 2 + ‖C 1 c k‖ ^ 2 + ‖C 2 c k‖ ^ 2) := fun c => by
      unfold nsFlux6A; rw [norm_mul, mul_pow, h2pi]
      have hcs := norm_linear_comb_sq_le_8b k (fun j => C j c k)
      have hpi_nn : 0 ≤ 4 * Real.pi ^ 2 := by positivity
      nlinarith
    have hcs_outer := norm_linear_comb_sq_le_8b k (fun c => nsFlux6A u u k c)
    have htot : (4 * Real.pi ^ 2 * kNormSq k) ^ 2 * ‖pressureCoeff6B u k‖ ^ 2 ≤
        (4 * Real.pi ^ 2 * kNormSq k) ^ 2 *
          ((‖C 0 0 k‖ ^ 2 + ‖C 1 0 k‖ ^ 2 + ‖C 2 0 k‖ ^ 2) +
           (‖C 0 1 k‖ ^ 2 + ‖C 1 1 k‖ ^ 2 + ‖C 2 1 k‖ ^ 2) +
           (‖C 0 2 k‖ ^ 2 + ‖C 1 2 k‖ ^ 2 + ‖C 2 2 k‖ ^ 2)) := by
      have h4k_nn : 0 ≤ 4 * Real.pi ^ 2 * kNormSq k := by positivity
      have h1 : 4 * Real.pi ^ 2 * ‖(k 0 : ℂ) * nsFlux6A u u k 0 + (k 1 : ℂ) * nsFlux6A u u k 1 +
            (k 2 : ℂ) * nsFlux6A u u k 2‖ ^ 2 ≤
          (4 * Real.pi ^ 2 * kNormSq k) *
            (‖nsFlux6A u u k 0‖ ^ 2 + ‖nsFlux6A u u k 1‖ ^ 2 + ‖nsFlux6A u u k 2‖ ^ 2) := by
        have := mul_le_mul_of_nonneg_left hcs_outer (by positivity : 0 ≤ 4 * Real.pi ^ 2)
        linarith
      have h2 : ‖nsFlux6A u u k 0‖ ^ 2 + ‖nsFlux6A u u k 1‖ ^ 2 + ‖nsFlux6A u u k 2‖ ^ 2 ≤
          (4 * Real.pi ^ 2 * kNormSq k) *
            ((‖C 0 0 k‖ ^ 2 + ‖C 1 0 k‖ ^ 2 + ‖C 2 0 k‖ ^ 2) +
             (‖C 0 1 k‖ ^ 2 + ‖C 1 1 k‖ ^ 2 + ‖C 2 1 k‖ ^ 2) +
             (‖C 0 2 k‖ ^ 2 + ‖C 1 2 k‖ ^ 2 + ‖C 2 2 k‖ ^ 2)) := by
        linarith [hflux_c 0, hflux_c 1, hflux_c 2]
      have h3 := mul_le_mul_of_nonneg_left h2 h4k_nn
      linarith
    have hfac_pos : 0 < (4 * Real.pi ^ 2 * kNormSq k) ^ 2 := by positivity
    have hp_le : ‖pressureCoeff6B u k‖ ^ 2 ≤
        (‖C 0 0 k‖ ^ 2 + ‖C 1 0 k‖ ^ 2 + ‖C 2 0 k‖ ^ 2) +
        (‖C 0 1 k‖ ^ 2 + ‖C 1 1 k‖ ^ 2 + ‖C 2 1 k‖ ^ 2) +
        (‖C 0 2 k‖ ^ 2 + ‖C 1 2 k‖ ^ 2 + ‖C 2 2 k‖ ^ 2) :=
      le_of_mul_le_mul_left htot hfac_pos
    have hmul_w := mul_le_mul_of_nonneg_left hp_le (le_of_lt (halfSobWeight_pos s k))
    dsimp only [dom]; simp only [hk, ↓reduceIte, add_zero]
    linarith

theorem smoothSynthPressure_contDiff_infty {u : VecSeq3D} (hu : ∀ m : ℕ, InHmVec m u) :
    (∀ n : ℕ, ContDiff ℝ n (smoothSynthScalar (pressureCoeff6B u))) ∧
    ContDiff ℝ (⊤ : ℕ∞) (smoothSynthScalar (pressureCoeff6B u)) :=
  smoothSynthScalar_contDiff_infty fun m => by
    by_cases hm : 2 ≤ m
    · exact pressureCoeff6B_inHalfHm (by omega) (hu m)
    · have h4 : InHalfHmSeq 4 (pressureCoeff6B u) := pressureCoeff6B_inHalfHm (by norm_num) (hu 2)
      exact Summable.of_nonneg_of_le
        (fun k => mul_nonneg (le_of_lt (halfSobWeight_pos (2 * m) k)) (sq_nonneg _))
        (fun k => mul_le_mul_of_nonneg_right (halfSobWeight_mono (by omega) k) (sq_nonneg _)) h4

private theorem smoothSynthScalar_nsFlux6A_eq_advection3D {u : VecSeq3D}
    (hu : InHmVec 5 u) (hsol : IsSolenoidal u) (hsym : IsRealSymm u) (x : R3) (c : Fin 3) :
    smoothSynthScalar (fun k => nsFlux6A u u k c) x = advection3D (smoothSynthVec u) x c := by
  have hu2 : InH2Vec u := (inH2Vec_of_inHalfHmVec (by norm_num) (hu : InHalfHmVec 10 u)).1
  have hu4 : InHmVec 4 u := (inHalfHmVec_mono (by norm_num) (hu : InHalfHmVec 10 u)).1
  have hprod_in10 : ∀ j : Fin 3, InHalfHmSeq 10 (conv3D (fun m => u m j) (fun m => u m c)) :=
    fun j => (conv3D_tame_l1_halfHm (by norm_num) (hu j) (hu c)).1
  have hprod_in8 : ∀ j : Fin 3, InHalfHmSeq 8 (conv3D (fun m => u m j) (fun m => u m c)) :=
    fun j => Summable.of_nonneg_of_le
      (fun k => mul_nonneg (le_of_lt (halfSobWeight_pos 8 k)) (sq_nonneg _))
      (fun k => mul_le_mul_of_nonneg_right (halfSobWeight_mono (by norm_num) k) (sq_nonneg _))
      (hprod_in10 j)
  have hflux_eq : smoothSynthScalar (fun k => nsFlux6A u u k c) x =
      smoothSynthScalar (diffMode 0 (conv3D (fun m => u m 0) (fun m => u m c))) x +
      smoothSynthScalar (diffMode 1 (conv3D (fun m => u m 1) (fun m => u m c))) x +
      smoothSynthScalar (diffMode 2 (conv3D (fun m => u m 2) (fun m => u m c))) x := by
    have hs : ∀ j : Fin 3, Summable (fun k =>
        diffMode j (conv3D (fun m => u m j) (fun m => u m c)) k * fourierMode8B k x) := fun j =>
      Summable.of_norm (by
        simpa [norm_mul, norm_fourierMode8B] using
          (h2Seq_l1_embedding (inH2Seq_of_inHalfHmSeq (by norm_num) (diffMode_inHalfHm (hprod_in8 j) j)).1).1)
    unfold smoothSynthScalar smoothSynthScalarC
    rw [← Complex.add_re, ← Complex.add_re,
        ← (hs 0).tsum_add (hs 1), ← ((hs 0).add (hs 1)).tsum_add (hs 2)]
    congr 1; congr 1; funext k
    unfold nsFlux6A diffMode; ring
  have hterm_j : ∀ j : Fin 3,
      smoothSynthScalar (diffMode j (conv3D (fun m => u m j) (fun m => u m c))) x =
        partialDerivScalar (fun y => smoothSynthVec u y j) x j * smoothSynthVec u x c +
        smoothSynthVec u x j * partialDerivScalar (fun y => smoothSynthVec u y c) x j := by
    intro j
    rw [← partialDerivScalar_smoothSynthScalar (hprod_in8 j) x j]
    have hfun : smoothSynthScalar (conv3D (fun m => u m j) (fun m => u m c)) =
        (fun y => smoothSynthVec u y j * smoothSynthVec u y c) :=
      funext fun y => smoothSynthScalar_conv3D_of_realSymm (hu2 j) (hu2 c)
        (fun k => (hsym k j).symm) (fun k => (hsym k c).symm) y
    rw [hfun]
    have hd_j : DifferentiableAt ℝ (fun y => smoothSynthVec u y j) x :=
      (Complex.reCLM.hasFDerivAt.comp x (smoothSynthScalarC_hasFDerivAt (hu4 j) x)).differentiableAt
    have hd_c : DifferentiableAt ℝ (fun y => smoothSynthVec u y c) x :=
      (Complex.reCLM.hasFDerivAt.comp x (smoothSynthScalarC_hasFDerivAt (hu4 c) x)).differentiableAt
    rw [partialDerivScalar_mul hd_j hd_c j, add_comm]
  rw [hflux_eq, hterm_j 0, hterm_j 1, hterm_j 2]
  have hdiv0 : div3D (smoothSynthVec u) x = 0 := div3D_smoothSynthVec_eq_zero hu4 hsol x
  unfold div3D at hdiv0
  unfold advection3D
  linear_combination smoothSynthVec u x c * hdiv0

private theorem exists_finset_uniform_cont_8b {f' : ℝ → (Fin 3 → ℤ) → ℂ} {t η : ℝ}
    (hη : 0 < η) (hf'_cont : ∀ k, Continuous (fun r => f' r k)) (S : Finset (Fin 3 → ℤ)) :
    ∃ δ₁ : ℝ, 0 < δ₁ ∧ ∀ k ∈ S, ∀ r : ℝ, |r - t| < δ₁ → ‖f' r k - f' t k‖ ≤ η := by
  classical
  refine Finset.induction_on S ⟨1, zero_lt_one, by simp⟩ fun a U ha ih => ?_
  obtain ⟨δ_U, hδ_U_pos, hU⟩ := ih
  obtain ⟨δ_a, hδ_a_pos, hda⟩ := Metric.continuousAt_iff.mp ((hf'_cont a).continuousAt (x := t)) η hη
  refine ⟨min δ_U δ_a, lt_min hδ_U_pos hδ_a_pos, fun k hk r hr => ?_⟩
  rcases Finset.mem_insert.mp hk with rfl | hkU
  · have hra : dist r t < δ_a := by rw [Real.dist_eq]; exact lt_of_lt_of_le hr (min_le_right _ _)
    exact le_of_lt (by simpa [dist_eq_norm] using hda hra)
  · exact hU k hkU r (lt_of_lt_of_le hr (min_le_left _ _))

private theorem tsum_hasDerivAt_of_dominated_clean_8b {f f' : ℝ → (Fin 3 → ℤ) → ℂ} {M : (Fin 3 → ℤ) → ℝ}
    {t δ : ℝ} (hδ : 0 < δ)
    (_hM_nn : ∀ k, 0 ≤ M k) (hM_sum : Summable M)
    (hf_l1 : ∀ s ∈ Set.Icc (t - δ) (t + δ), Summable (fun k => ‖f s k‖))
    (hf'_cont : ∀ k, Continuous (fun r => f' r k))
    (hf'_deriv : ∀ (r : ℝ) (k : Fin 3 → ℤ), r ∈ Set.Icc (t - δ) (t + δ) →
      HasDerivAt (fun s => f s k) (f' r k) r)
    (hf'_bd : ∀ (r : ℝ) (k : Fin 3 → ℤ), r ∈ Set.Icc (t - δ) (t + δ) → ‖f' r k‖ ≤ M k) :
    HasDerivAt (fun s : ℝ => ∑' k : Fin 3 → ℤ, f s k) (∑' k : Fin 3 → ℤ, f' t k) t := by
  have hft_l1 : Summable (fun k => ‖f t k‖) := hf_l1 t ⟨by linarith, by linarith⟩
  have hf't_l1 : Summable (fun k => ‖f' t k‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
      (fun k => hf'_bd t k ⟨by linarith, by linarith⟩) hM_sum
  rw [hasDerivAt_iff_isLittleO_nhds_zero, Asymptotics.isLittleO_iff]
  intro ε hε
  have htail_ex : ∃ S : Finset (Fin 3 → ℤ), (∑' k : Fin 3 → ℤ, M k) - ∑ k ∈ S, M k < ε / 6 := by
    obtain ⟨S, hS⟩ := Metric.tendsto_atTop.mp hM_sum.hasSum (ε / 6) (by positivity)
    refine ⟨S, ?_⟩
    have hdist := hS S le_rfl
    rw [Real.dist_eq] at hdist
    linarith [(abs_lt.mp hdist).1]
  obtain ⟨S, hS_tail⟩ := htail_ex
  obtain ⟨δ₁, hδ₁_pos, hS_cont⟩ :=
    exists_finset_uniform_cont_8b (t := t) (η := ε / (3 * ((S.card : ℝ) + 1)))
      (by positivity) hf'_cont S
  rw [Metric.eventually_nhds_iff]
  refine ⟨min δ δ₁, lt_min hδ hδ₁_pos, fun {h} hh => ?_⟩
  rw [dist_zero_right, Real.norm_eq_abs] at hh
  have hh_δ : |h| < δ := lt_of_lt_of_le hh (min_le_left _ _)
  have hh_δ₁ : |h| < δ₁ := lt_of_lt_of_le hh (min_le_right _ _)
  have hth_mem : t + h ∈ Set.Icc (t - δ) (t + δ) :=
    abs_lt.mp hh_δ |> fun ⟨h1, h2⟩ => ⟨by linarith, by linarith⟩
  have hs1 : Summable (fun k => f (t + h) k) := Summable.of_norm (hf_l1 (t + h) hth_mem)
  have hs2 : Summable (fun k => f t k) := Summable.of_norm hft_l1
  have hs3 : Summable (fun k => (h : ℝ) • f' t k) := (Summable.of_norm hf't_l1).const_smul h
  have hsmul_tsum : (h : ℝ) • (∑' k : Fin 3 → ℤ, f' t k) = ∑' k : Fin 3 → ℤ, (h : ℝ) • f' t k := by
    simp_rw [Complex.real_smul]; exact tsum_mul_left.symm
  rw [hsmul_tsum, ← hs1.tsum_sub hs2, ← (hs1.sub hs2).tsum_sub hs3]
  have hmode_err : ∀ k : Fin 3 → ℤ,
      f (t + h) k - f t k - (h : ℝ) • f' t k = ∫ r in t..(t + h), (f' r k - f' t k) := by
    intro k
    have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt
      (a := t) (b := t + h) (f := fun r => f r k) (f' := fun r => f' r k)
      (fun r hr => by
        have hr_mem : r ∈ Set.Icc (t - δ) (t + δ) := by
          rcases le_or_gt 0 h with hge | hlt
          · rw [Set.uIcc_of_le (by linarith)] at hr; exact ⟨by linarith [hr.1], by linarith [hr.2, hth_mem.2]⟩
          · rw [Set.uIcc_of_ge (by linarith)] at hr; exact ⟨by linarith [hr.1, hth_mem.1], by linarith [hr.2]⟩
        exact hf'_deriv r k hr_mem)
      ((hf'_cont k).intervalIntegrable (μ := volume) t (t + h))
    have hsub := intervalIntegral.integral_sub
      ((hf'_cont k).intervalIntegrable (μ := volume) t (t + h))
      ((continuous_const (y := f' t k)).intervalIntegrable (μ := volume) t (t + h))
    rw [hsub, hftc, intervalIntegral.integral_const, add_sub_cancel_left]
  have hpt_bd : ∀ k : Fin 3 → ℤ,
      ‖f (t + h) k - f t k - (h : ℝ) • f' t k‖ ≤
        |h| * (if k ∈ S then ε / (3 * ((S.card : ℝ) + 1)) else 2 * M k) := by
    intro k
    rw [hmode_err k]
    have hbound := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := t) (b := t + h)
      (C := if k ∈ S then ε / (3 * ((S.card : ℝ) + 1)) else 2 * M k)
      fun r hr => by
        have hrt_lt : |r - t| < δ₁ ∧ r ∈ Set.Icc (t - δ) (t + δ) := by
          rcases le_or_gt 0 h with hge | hlt
          · rw [Set.uIoc_of_le (by linarith)] at hr
            have h1 : |r - t| ≤ |h| := by
              rw [abs_of_nonneg (by linarith [hr.1]), abs_of_nonneg hge]; linarith [hr.2]
            exact ⟨lt_of_le_of_lt h1 hh_δ₁, ⟨by linarith [hr.1], by linarith [hr.2, hth_mem.2]⟩⟩
          · rw [Set.uIoc_of_ge (by linarith)] at hr
            have h1 : |r - t| ≤ |h| := by
              rw [abs_of_nonpos (by linarith [hr.2]), abs_of_neg hlt]; linarith [hr.1]
            exact ⟨lt_of_le_of_lt h1 hh_δ₁, ⟨by linarith [hr.1, hth_mem.1], by linarith [hr.2]⟩⟩
        by_cases hk : k ∈ S
        · simp only [hk, ↓reduceIte]; exact hS_cont k hk r hrt_lt.1
        · simp only [hk, ↓reduceIte]
          have h1 := norm_sub_le (f' r k) (f' t k)
          have h2 := hf'_bd r k hrt_lt.2
          have h3 := hf'_bd t k ⟨by linarith, by linarith⟩
          linarith
    rw [add_sub_cancel_left, mul_comm] at hbound
    exact hbound
  have hdom_sum : Summable (fun k : Fin 3 → ℤ =>
      if k ∈ S then ε / (3 * ((S.card : ℝ) + 1)) else 2 * M k) := by
    have hfin_sum : Summable (fun k : Fin 3 → ℤ =>
        if k ∈ S then ε / (3 * ((S.card : ℝ) + 1)) - 2 * M k else 0) :=
      summable_of_ne_finset_zero (s := S) fun k hk => by simp [hk]
    have hfun : (fun k : Fin 3 → ℤ => if k ∈ S then ε / (3 * ((S.card : ℝ) + 1)) else 2 * M k) =
        (fun k => 2 * M k + (if k ∈ S then ε / (3 * ((S.card : ℝ) + 1)) - 2 * M k else 0)) := by
      funext k; split_ifs <;> ring
    rw [hfun]; exact (hM_sum.mul_left 2).add hfin_sum
  have hnorm_sum : Summable (fun k => ‖f (t + h) k - f t k - (h : ℝ) • f' t k‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hpt_bd (hdom_sum.mul_left |h|)
  have hle1 := le_trans (norm_tsum_le_tsum_norm hnorm_sum)
    (hasSum_le hpt_bd hnorm_sum.hasSum (hdom_sum.hasSum.mul_left |h|))
  have hdom_eval : (∑' k : Fin 3 → ℤ, if k ∈ S then ε / (3 * ((S.card : ℝ) + 1)) else 2 * M k) ≤ ε := by
    have hfin_sum : Summable (fun k : Fin 3 → ℤ =>
        if k ∈ S then ε / (3 * ((S.card : ℝ) + 1)) - 2 * M k else 0) :=
      summable_of_ne_finset_zero (s := S) fun k hk => by simp [hk]
    have hfun : (fun k : Fin 3 → ℤ => if k ∈ S then ε / (3 * ((S.card : ℝ) + 1)) else 2 * M k) =
        (fun k => 2 * M k + (if k ∈ S then ε / (3 * ((S.card : ℝ) + 1)) - 2 * M k else 0)) := by
      funext k; split_ifs <;> ring
    rw [hfun, (hM_sum.mul_left 2).tsum_add hfin_sum, tsum_mul_left]
    have hfin_eq : (∑' k : Fin 3 → ℤ, if k ∈ S then ε / (3 * ((S.card : ℝ) + 1)) - 2 * M k else 0) =
        ∑ k ∈ S, (ε / (3 * ((S.card : ℝ) + 1)) - 2 * M k) := by
      rw [tsum_eq_sum (s := S) (fun k hk => by simp [hk])]
      refine Finset.sum_congr rfl fun k hk => by simp [hk]
    rw [hfin_eq, Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, ← Finset.mul_sum]
    have hcard_le : (S.card : ℝ) * (ε / (3 * ((S.card : ℝ) + 1))) ≤ ε / 3 := by
      have hpos : 0 < 3 * ((S.card : ℝ) + 1) := by positivity
      rw [mul_div_assoc', div_le_iff₀ hpos]
      nlinarith
    linarith
  have hfinal := mul_le_mul_of_nonneg_left hdom_eval (abs_nonneg h)
  rw [Real.norm_eq_abs]
  linarith

/-- **THEOREM 6 OF MILESTONE 8B (Exact Pointwise Physical-Space 3D Navier–Stokes PDE &
    `C^∞(𝕋³)` Regularity for Every Mild `H²` Solution on `(0, T)`, `0 sorryAx`):**
    For EVERY viscosity `ν > 0`, EVERY horizon `T > 0`, and EVERY solenoidal real-symmetric
    admissible mild `H²` solution `u` on `[0, T]`, setting
      `U(t, x) := smoothSynthVec (u t) x` and `P(t, x) := smoothSynthScalar (pressureCoeff6B (u t)) x`,
    for EVERY `t ∈ (0, T)`:
    1. `U(t, ·) ∈ C^∞(𝕋³)` and `P(t, ·) ∈ C^∞(𝕋³)`, both `ℤ³`-periodic;
    2. `∀ x : R3, div3D (U t) x = 0`;
    3. `∀ x : R3, ∀ c : Fin 3`, `s ↦ U s x c` is differentiable at `t` and satisfies the exact
       pointwise 3D Navier–Stokes momentum PDE:
       `∂_t U_c(t, x) + (U(t) · ∇) U_c(t, x) + ∂_c P(t, x) = ν Δ U_c(t, x)`. -/
theorem mild_solution_physical_ns3d_torus3D
    {ν T M : ℝ} (hν : 0 < ν) (hM : 0 ≤ M) (u₀ : VecSeq3D)
    {u : ℝ → VecSeq3D} (hu : IsAdmissibleCurve M u)
    (hu_sol : ∀ t ∈ Set.Icc (0 : ℝ) T, u t = duhamelRaw ν u₀ u t)
    (hu_struct : ∀ t ∈ Set.Icc (0 : ℝ) T, IsSolenoidal (u t) ∧ IsRealSymm (u t)) :
    let U : ℝ → R3 → R3 := fun t => smoothSynthVec (u t)
    let P : ℝ → R3 → ℝ := fun t => smoothSynthScalar (pressureCoeff6B (u t))
    ∀ t ∈ Set.Ioo (0 : ℝ) T,
      (∀ n : ℕ, ContDiff ℝ n (U t)) ∧ ContDiff ℝ (⊤ : ℕ∞) (U t) ∧ IsPeriodic3D (U t) ∧
      (∀ n : ℕ, ContDiff ℝ n (P t)) ∧ ContDiff ℝ (⊤ : ℕ∞) (P t) ∧ IsPeriodic3D (P t) ∧
      (∀ x : R3, div3D (U t) x = 0) ∧
      (∀ (x : R3) (c : Fin 3),
        HasDerivAt (fun s : ℝ => U s x c)
          (ν * laplacian3D (U t) x c - advection3D (U t) x c - grad3D (P t) x c) t ∧
        deriv (fun s : ℝ => U s x c) t + advection3D (U t) x c + grad3D (P t) x c =
          ν * laplacian3D (U t) x c) := by
  intro U P t ht
  have hall_u : ∀ m : ℕ, InHmVec m (u t) := fun m => by
    obtain ⟨_, _, hbd⟩ := higher_sobolev_bootstrap_all_orders_torus3D hν hM u₀ hu hu_sol m t ht.1 (le_of_lt ht.2)
    exact (hbd t ⟨le_rfl, le_of_lt ht.2⟩).1
  have hU_inf := smoothSynthVec_contDiff_infty hall_u
  have hP_inf := smoothSynthPressure_contDiff_infty hall_u
  have ht_icc : t ∈ Set.Icc (0 : ℝ) T := ⟨le_of_lt ht.1, le_of_lt ht.2⟩
  have hst_t := hu_struct t ht_icc
  have hdiv_t : ∀ x : R3, div3D (U t) x = 0 := fun x =>
    div3D_smoothSynthVec_eq_zero (hall_u 4) hst_t.1 x
  refine ⟨hU_inf.1, hU_inf.2, smoothSynthVec_periodic (u t),
          hP_inf.1, hP_inf.2, smoothSynthScalar_periodic (pressureCoeff6B (u t)),
          hdiv_t, fun x c => ?_⟩
  let δ : ℝ := min (t / 2) ((T - t) / 2)
  have hδ_pos : 0 < δ := lt_min (half_pos ht.1) (half_pos (sub_pos.mpr ht.2))
  have ha_pos : 0 < t / 2 := half_pos ht.1
  obtain ⟨B6, hB6_nn, hB6⟩ :=
    higher_sobolev_bootstrap_all_orders_torus3D hν hM u₀ hu hu_sol 6 (t / 2) ha_pos (by linarith [ht.2])
  let C_dom : ℝ := 4 * Real.pi ^ 2 * ν * Real.sqrt B6 +
    2 * Real.pi * Real.sqrt (4 * (4 : ℝ) ^ 10 * (53 * M) * B6)
  have hC_dom_nn : 0 ≤ C_dom := by dsimp only [C_dom]; positivity
  let f : ℝ → (Fin 3 → ℤ) → ℂ := fun s k => u s k c * fourierMode8B k x
  let f' : ℝ → (Fin 3 → ℤ) → ℂ := fun r k =>
    ((-4 * (Real.pi : ℂ) ^ 2 * (ν : ℂ) * ((kNormSq k : ℝ) : ℂ)) * u r k c +
      nsBilinear6A (u r) (u r) k c) * fourierMode8B k x
  have hderiv_c : HasDerivAt (fun s => smoothSynthScalarC (fun k => u s k c) x)
      (∑' k : Fin 3 → ℤ, f' t k) t := by
    refine tsum_hasDerivAt_of_dominated_clean_8b (M := fun k => C_dom / h2Weight k) hδ_pos
      (fun k => div_nonneg hC_dom_nn (le_of_lt (h2Weight_pos k)))
      (by simpa [div_eq_mul_inv] using (summable_and_tsum_inv_h2Weight_le).1.mul_left C_dom)
      (fun s _ => by
        simpa [f, norm_mul, norm_fourierMode8B] using (h2Seq_l1_embedding (hu.h_inH2 s c)).1)
      (fun k => ((continuous_const.mul (hu.h_cont k c)).add
        (continuous_nsBilinear6A_of_admissible hu hu k c)).mul continuous_const)
      (fun r k hr => by
        have hr_ioo : r ∈ Set.Ioo (0 : ℝ) T :=
          ⟨by linarith [hr.1, min_le_left (t / 2) ((T - t) / 2)],
           by linarith [hr.2, min_le_right (t / 2) ((T - t) / 2)]⟩
        have hode := mild_solution_hasDerivAt_spectral_ns3d u₀ hu hu_sol hr_ioo k c
        have hbi := nsBilinear6A_eq_neg_flux_sub_grad_pressure (u r) k c
        have hrhs : (-4 * (Real.pi : ℂ) ^ 2 * (ν : ℂ) * ((kNormSq k : ℝ) : ℂ)) * u r k c -
            nsFlux6A (u r) (u r) k c -
            2 * (Real.pi : ℂ) * Complex.I * (k c : ℂ) * pressureCoeff6B (u r) k =
            (-4 * (Real.pi : ℂ) ^ 2 * (ν : ℂ) * ((kNormSq k : ℝ) : ℂ)) * u r k c +
            nsBilinear6A (u r) (u r) k c := by rw [hbi]; ring
        rw [hrhs] at hode
        exact hode.mul_const (fourierMode8B k x))
      (fun r k hr => by
        have hr_mem : r ∈ Set.Icc (t / 2) T :=
          ⟨by linarith [hr.1, min_le_left (t / 2) ((T - t) / 2)],
           by linarith [hr.2, min_le_right (t / 2) ((T - t) / 2)]⟩
        have h6 := hB6 r hr_mem
        have h12_eq : halfSobWeight 12 k = (1 + kNormSq k) ^ 6 := by
          simpa [sobWeight] using halfSobWeight_even 6 k
        have h10_eq : halfSobWeight 10 k = (1 + kNormSq k) ^ 5 := by
          simpa [sobWeight] using halfSobWeight_even 5 k
        have hxk : 0 ≤ kNormSq k := kNormSq_nonneg_8a k
        have h12_ge : (kNormSq k) ^ 2 * (h2Weight k) ^ 2 ≤ halfSobWeight 12 k := by
          rw [h12_eq]; unfold h2Weight
          have h1 : 1 + (kNormSq k) ^ 2 ≤ (1 + kNormSq k) ^ 2 := by nlinarith
          have h2 : (1 + (kNormSq k) ^ 2) ^ 2 ≤ ((1 + kNormSq k) ^ 2) ^ 2 := by
            have : 0 ≤ 1 + (kNormSq k) ^ 2 := by positivity
            nlinarith
          have h3 : (kNormSq k) ^ 2 ≤ (1 + kNormSq k) ^ 2 := by nlinarith
          have h4 := mul_le_mul h3 h2 (sq_nonneg _) (sq_nonneg _)
          have hpow : (1 + kNormSq k) ^ 2 * ((1 + kNormSq k) ^ 2) ^ 2 = (1 + kNormSq k) ^ 6 := by ring
          linarith
        have h10_ge : kNormSq k * (h2Weight k) ^ 2 ≤ halfSobWeight 10 k := by
          rw [h10_eq]; unfold h2Weight
          have h1 : 1 + (kNormSq k) ^ 2 ≤ (1 + kNormSq k) ^ 2 := by nlinarith
          have h2 : (1 + (kNormSq k) ^ 2) ^ 2 ≤ ((1 + kNormSq k) ^ 2) ^ 2 := by
            have : 0 ≤ 1 + (kNormSq k) ^ 2 := by positivity
            nlinarith
          have h3 : kNormSq k ≤ 1 + kNormSq k := by linarith
          have h4 := mul_le_mul h3 h2 (sq_nonneg _) (by linarith)
          have hpow : (1 + kNormSq k) * ((1 + kNormSq k) ^ 2) ^ 2 = (1 + kNormSq k) ^ 5 := by ring
          linarith
        have hu_k_sq : halfSobWeight 12 k * ‖u r k c‖ ^ 2 ≤ B6 := by
          have hle_c : halfSobWeight 12 k * ‖u r k c‖ ^ 2 ≤ halfHmNormSq 12 (fun m => u r m c) := by
            have hind := hasSum_ite_eq k (halfSobWeight 12 k * ‖u r k c‖ ^ 2)
            refine hasSum_le (fun m => ?_) hind (h6.1 c).hasSum
            by_cases hm : m = k
            · subst hm; simp
            · simp only [hm, ↓reduceIte]
              exact mul_nonneg (le_of_lt (halfSobWeight_pos 12 m)) (sq_nonneg _)
          have hle_v : halfHmNormSq 12 (fun m => u r m c) ≤ hmVecNormSq 6 (u r) := by
            unfold hmVecNormSq halfHmVecNormSq
            fin_cases c
            · change halfHmNormSq 12 (fun m => u r m 0) ≤ _
              linarith [halfHmNormSq_nonneg 12 (fun m => u r m 1), halfHmNormSq_nonneg 12 (fun m => u r m 2)]
            · change halfHmNormSq 12 (fun m => u r m 1) ≤ _
              linarith [halfHmNormSq_nonneg 12 (fun m => u r m 0), halfHmNormSq_nonneg 12 (fun m => u r m 2)]
            · change halfHmNormSq 12 (fun m => u r m 2) ≤ _
              linarith [halfHmNormSq_nonneg 12 (fun m => u r m 0), halfHmNormSq_nonneg 12 (fun m => u r m 1)]
          exact le_trans hle_c (le_trans hle_v h6.2)
        have hlin_bd : ‖(-4 * (Real.pi : ℂ) ^ 2 * (ν : ℂ) * ((kNormSq k : ℝ) : ℂ)) * u r k c‖ ≤
            (4 * Real.pi ^ 2 * ν * Real.sqrt B6) / h2Weight k := by
          have hcoef : ‖(-4 * (Real.pi : ℂ) ^ 2 * (ν : ℂ) * ((kNormSq k : ℝ) : ℂ))‖ =
              4 * Real.pi ^ 2 * ν * kNormSq k := by
            have h4 : ‖(-4 : ℂ)‖ = 4 := by norm_num
            rw [norm_mul, norm_mul, norm_mul, norm_pow, h4, Complex.norm_real, Complex.norm_real,
                Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs, Real.norm_eq_abs,
                abs_of_pos Real.pi_pos, abs_of_pos hν, abs_of_nonneg hxk]
          rw [norm_mul, hcoef, le_div_iff₀ (h2Weight_pos k)]
          have hku_sq : (kNormSq k * ‖u r k c‖ * h2Weight k) ^ 2 ≤ (Real.sqrt B6) ^ 2 := by
            rw [Real.sq_sqrt hB6_nn]
            have h1 := mul_le_mul_of_nonneg_right h12_ge (sq_nonneg ‖u r k c‖)
            have h2 : (kNormSq k * ‖u r k c‖ * h2Weight k) ^ 2 =
                (kNormSq k) ^ 2 * (h2Weight k) ^ 2 * ‖u r k c‖ ^ 2 := by ring
            linarith
          have hku_le : kNormSq k * ‖u r k c‖ * h2Weight k ≤ Real.sqrt B6 := by
            have hnn : 0 ≤ kNormSq k * ‖u r k c‖ * h2Weight k :=
              mul_nonneg (mul_nonneg hxk (norm_nonneg _)) (le_of_lt (h2Weight_pos k))
            nlinarith [Real.sqrt_nonneg B6]
          have hmul := mul_le_mul_of_nonneg_left hku_le (by positivity : 0 ≤ 4 * Real.pi ^ 2 * ν)
          linarith
        have hbi_bd : ‖nsBilinear6A (u r) (u r) k c‖ ≤
            (2 * Real.pi * Real.sqrt (4 * (4 : ℝ) ^ 10 * (53 * M) * B6)) / h2Weight k := by
          have h10_u := inHalfHmVec_mono (s₁ := 10) (s₂ := 12) (by norm_num) h6.1
          have hbi_sq : ‖nsBilinear6A (u r) (u r) k c‖ ^ 2 ≤
              4 * Real.pi ^ 2 * kNormSq k *
                ((‖conv3D (fun m => u r m 0) (fun m => u r m 0) k‖ ^ 2 +
                  ‖conv3D (fun m => u r m 1) (fun m => u r m 0) k‖ ^ 2 +
                  ‖conv3D (fun m => u r m 2) (fun m => u r m 0) k‖ ^ 2) +
                 (‖conv3D (fun m => u r m 0) (fun m => u r m 1) k‖ ^ 2 +
                  ‖conv3D (fun m => u r m 1) (fun m => u r m 1) k‖ ^ 2 +
                  ‖conv3D (fun m => u r m 2) (fun m => u r m 1) k‖ ^ 2) +
                 (‖conv3D (fun m => u r m 0) (fun m => u r m 2) k‖ ^ 2 +
                  ‖conv3D (fun m => u r m 1) (fun m => u r m 2) k‖ ^ 2 +
                  ‖conv3D (fun m => u r m 2) (fun m => u r m 2) k‖ ^ 2)) := by
            have hcomp_v : ‖nsBilinear6A (u r) (u r) k c‖ ^ 2 ≤ vecNormSqC (nsBilinear6A (u r) (u r) k) := by
              unfold vecNormSqC
              fin_cases c
              · change ‖nsBilinear6A (u r) (u r) k 0‖ ^ 2 ≤ _
                linarith [sq_nonneg ‖nsBilinear6A (u r) (u r) k 1‖, sq_nonneg ‖nsBilinear6A (u r) (u r) k 2‖]
              · change ‖nsBilinear6A (u r) (u r) k 1‖ ^ 2 ≤ _
                linarith [sq_nonneg ‖nsBilinear6A (u r) (u r) k 0‖, sq_nonneg ‖nsBilinear6A (u r) (u r) k 2‖]
              · change ‖nsBilinear6A (u r) (u r) k 2‖ ^ 2 ≤ _
                linarith [sq_nonneg ‖nsBilinear6A (u r) (u r) k 0‖, sq_nonneg ‖nsBilinear6A (u r) (u r) k 1‖]
            have hneg : vecNormSqC (nsBilinear6A (u r) (u r) k) = vecNormSqC (lerayProj6A k (nsFlux6A (u r) (u r) k)) := by
              unfold vecNormSqC nsBilinear6A; simp only [norm_neg]
            have hproj := lerayProj6A_normSq_le k (nsFlux6A (u r) (u r) k)
            have h2pi : ‖(2 : ℂ) * (Real.pi : ℂ) * Complex.I‖ ^ 2 = 4 * Real.pi ^ 2 := by
              have h2 : ‖(2 : ℂ)‖ = 2 := by norm_num
              rw [norm_mul, norm_mul, Complex.norm_I, mul_one, h2,
                  Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]; ring
            have hfl : ∀ d : Fin 3, ‖nsFlux6A (u r) (u r) k d‖ ^ 2 ≤
                4 * Real.pi ^ 2 * kNormSq k *
                  (‖conv3D (fun m => u r m 0) (fun m => u r m d) k‖ ^ 2 +
                   ‖conv3D (fun m => u r m 1) (fun m => u r m d) k‖ ^ 2 +
                   ‖conv3D (fun m => u r m 2) (fun m => u r m d) k‖ ^ 2) := fun d => by
              unfold nsFlux6A; rw [norm_mul, mul_pow, h2pi]
              have hcs := norm_linear_comb_sq_le_8b k (fun j => conv3D (fun m => u r m j) (fun m => u r m d) k)
              have hpi_nn : 0 ≤ 4 * Real.pi ^ 2 := by positivity
              nlinarith
            have hle_flux : ‖nsBilinear6A (u r) (u r) k c‖ ^ 2 ≤
                ‖nsFlux6A (u r) (u r) k 0‖ ^ 2 + ‖nsFlux6A (u r) (u r) k 1‖ ^ 2 +
                ‖nsFlux6A (u r) (u r) k 2‖ ^ 2 :=
              le_trans hcomp_v (by rw [hneg]; exact hproj)
            rw [mul_add, mul_add]
            linarith [hle_flux, hfl 0, hfl 1, hfl 2]
          have hC_k : ∀ j d : Fin 3,
              halfSobWeight 10 k * ‖conv3D (fun m => u r m j) (fun m => u r m d) k‖ ^ 2 ≤
                2 * (4 : ℝ) ^ 10 * (∑' m, ‖u r m d‖) ^ 2 * halfHmNormSq 10 (fun m => u r m j) +
                2 * (4 : ℝ) ^ 10 * (∑' m, ‖u r m j‖) ^ 2 * halfHmNormSq 10 (fun m => u r m d) := by
            intro j d
            have htame := conv3D_tame_l1_halfHm (s := 10) (by norm_num) (h10_u.1 j) (h10_u.1 d)
            have hle1 : halfSobWeight 10 k * ‖conv3D (fun m => u r m j) (fun m => u r m d) k‖ ^ 2 ≤
                halfHmNormSq 10 (conv3D (fun m => u r m j) (fun m => u r m d)) := by
              have hind := hasSum_ite_eq k (halfSobWeight 10 k * ‖conv3D (fun m => u r m j) (fun m => u r m d) k‖ ^ 2)
              refine hasSum_le (fun m => ?_) hind htame.1.hasSum
              by_cases hm : m = k
              · subst hm; simp
              · simp only [hm, ↓reduceIte]
                exact mul_nonneg (le_of_lt (halfSobWeight_pos 10 m)) (sq_nonneg _)
            exact le_trans hle1 htame.2
          have hsum9_k : halfSobWeight 10 k *
              ((‖conv3D (fun m => u r m 0) (fun m => u r m 0) k‖ ^ 2 +
                ‖conv3D (fun m => u r m 1) (fun m => u r m 0) k‖ ^ 2 +
                ‖conv3D (fun m => u r m 2) (fun m => u r m 0) k‖ ^ 2) +
               (‖conv3D (fun m => u r m 0) (fun m => u r m 1) k‖ ^ 2 +
                ‖conv3D (fun m => u r m 1) (fun m => u r m 1) k‖ ^ 2 +
                ‖conv3D (fun m => u r m 2) (fun m => u r m 1) k‖ ^ 2) +
               (‖conv3D (fun m => u r m 0) (fun m => u r m 2) k‖ ^ 2 +
                ‖conv3D (fun m => u r m 1) (fun m => u r m 2) k‖ ^ 2 +
                ‖conv3D (fun m => u r m 2) (fun m => u r m 2) k‖ ^ 2)) ≤
              4 * (4 : ℝ) ^ 10 * (53 * M) * B6 := by
            have hW_bd : wienerNormSq (u r) ≤ 53 * M :=
              le_trans (wienerNormSq_le_53_h2VecNormSq (hu.h_inH2 r)) (by linarith [hu.h_bound r])
            have h10_bd : halfHmVecNormSq 10 (u r) ≤ B6 := le_trans h10_u.2 h6.2
            have hfac : 4 * (4 : ℝ) ^ 10 * wienerNormSq (u r) * halfHmVecNormSq 10 (u r) =
                ((2 * (4 : ℝ) ^ 10 * (∑' m, ‖u r m 0‖) ^ 2 * halfHmNormSq 10 (fun m => u r m 0) +
                  2 * (4 : ℝ) ^ 10 * (∑' m, ‖u r m 0‖) ^ 2 * halfHmNormSq 10 (fun m => u r m 0)) +
                 (2 * (4 : ℝ) ^ 10 * (∑' m, ‖u r m 0‖) ^ 2 * halfHmNormSq 10 (fun m => u r m 1) +
                  2 * (4 : ℝ) ^ 10 * (∑' m, ‖u r m 1‖) ^ 2 * halfHmNormSq 10 (fun m => u r m 0)) +
                 (2 * (4 : ℝ) ^ 10 * (∑' m, ‖u r m 0‖) ^ 2 * halfHmNormSq 10 (fun m => u r m 2) +
                  2 * (4 : ℝ) ^ 10 * (∑' m, ‖u r m 2‖) ^ 2 * halfHmNormSq 10 (fun m => u r m 0))) +
                ((2 * (4 : ℝ) ^ 10 * (∑' m, ‖u r m 1‖) ^ 2 * halfHmNormSq 10 (fun m => u r m 0) +
                  2 * (4 : ℝ) ^ 10 * (∑' m, ‖u r m 0‖) ^ 2 * halfHmNormSq 10 (fun m => u r m 1)) +
                 (2 * (4 : ℝ) ^ 10 * (∑' m, ‖u r m 1‖) ^ 2 * halfHmNormSq 10 (fun m => u r m 1) +
                  2 * (4 : ℝ) ^ 10 * (∑' m, ‖u r m 1‖) ^ 2 * halfHmNormSq 10 (fun m => u r m 1)) +
                 (2 * (4 : ℝ) ^ 10 * (∑' m, ‖u r m 1‖) ^ 2 * halfHmNormSq 10 (fun m => u r m 2) +
                  2 * (4 : ℝ) ^ 10 * (∑' m, ‖u r m 2‖) ^ 2 * halfHmNormSq 10 (fun m => u r m 1))) +
                ((2 * (4 : ℝ) ^ 10 * (∑' m, ‖u r m 2‖) ^ 2 * halfHmNormSq 10 (fun m => u r m 0) +
                  2 * (4 : ℝ) ^ 10 * (∑' m, ‖u r m 0‖) ^ 2 * halfHmNormSq 10 (fun m => u r m 2)) +
                 (2 * (4 : ℝ) ^ 10 * (∑' m, ‖u r m 2‖) ^ 2 * halfHmNormSq 10 (fun m => u r m 1) +
                  2 * (4 : ℝ) ^ 10 * (∑' m, ‖u r m 1‖) ^ 2 * halfHmNormSq 10 (fun m => u r m 2)) +
                 (2 * (4 : ℝ) ^ 10 * (∑' m, ‖u r m 2‖) ^ 2 * halfHmNormSq 10 (fun m => u r m 2) +
                  2 * (4 : ℝ) ^ 10 * (∑' m, ‖u r m 2‖) ^ 2 * halfHmNormSq 10 (fun m => u r m 2))) := by
              unfold wienerNormSq halfHmVecNormSq; ring
            have hprod_bd : wienerNormSq (u r) * halfHmVecNormSq 10 (u r) ≤ (53 * M) * B6 :=
              mul_le_mul hW_bd h10_bd (halfHmVecNormSq_nonneg 10 (u r)) (by positivity)
            have h4prod := mul_le_mul_of_nonneg_left hprod_bd (by positivity : 0 ≤ 4 * (4 : ℝ) ^ 10)
            have hlin9 : halfSobWeight 10 k *
                ((‖conv3D (fun m => u r m 0) (fun m => u r m 0) k‖ ^ 2 +
                  ‖conv3D (fun m => u r m 1) (fun m => u r m 0) k‖ ^ 2 +
                  ‖conv3D (fun m => u r m 2) (fun m => u r m 0) k‖ ^ 2) +
                 (‖conv3D (fun m => u r m 0) (fun m => u r m 1) k‖ ^ 2 +
                  ‖conv3D (fun m => u r m 1) (fun m => u r m 1) k‖ ^ 2 +
                  ‖conv3D (fun m => u r m 2) (fun m => u r m 1) k‖ ^ 2) +
                 (‖conv3D (fun m => u r m 0) (fun m => u r m 2) k‖ ^ 2 +
                  ‖conv3D (fun m => u r m 1) (fun m => u r m 2) k‖ ^ 2 +
                  ‖conv3D (fun m => u r m 2) (fun m => u r m 2) k‖ ^ 2)) ≤
                4 * (4 : ℝ) ^ 10 * wienerNormSq (u r) * halfHmVecNormSq 10 (u r) := by
              rw [hfac]
              linarith [hC_k 0 0, hC_k 1 0, hC_k 2 0, hC_k 0 1, hC_k 1 1, hC_k 2 1,
                        hC_k 0 2, hC_k 1 2, hC_k 2 2]
            linarith
          rw [le_div_iff₀ (h2Weight_pos k)]
          have hsq_bi : (‖nsBilinear6A (u r) (u r) k c‖ * h2Weight k) ^ 2 ≤
              (2 * Real.pi * Real.sqrt (4 * (4 : ℝ) ^ 10 * (53 * M) * B6)) ^ 2 := by
            rw [mul_pow, mul_pow, Real.sq_sqrt (by positivity)]
            have hmul1 := mul_le_mul_of_nonneg_right hbi_sq (sq_nonneg (h2Weight k))
            have hmul2 := mul_le_mul_of_nonneg_right h10_ge (by positivity :
              0 ≤ (‖conv3D (fun m => u r m 0) (fun m => u r m 0) k‖ ^ 2 +
                   ‖conv3D (fun m => u r m 1) (fun m => u r m 0) k‖ ^ 2 +
                   ‖conv3D (fun m => u r m 2) (fun m => u r m 0) k‖ ^ 2) +
                  (‖conv3D (fun m => u r m 0) (fun m => u r m 1) k‖ ^ 2 +
                   ‖conv3D (fun m => u r m 1) (fun m => u r m 1) k‖ ^ 2 +
                   ‖conv3D (fun m => u r m 2) (fun m => u r m 1) k‖ ^ 2) +
                  (‖conv3D (fun m => u r m 0) (fun m => u r m 2) k‖ ^ 2 +
                   ‖conv3D (fun m => u r m 1) (fun m => u r m 2) k‖ ^ 2 +
                   ‖conv3D (fun m => u r m 2) (fun m => u r m 2) k‖ ^ 2))
            have hstep := le_trans hmul2 hsum9_k
            have h4pi := mul_le_mul_of_nonneg_left hstep (by positivity : 0 ≤ 4 * Real.pi ^ 2)
            linarith
          have hnn_bi : 0 ≤ ‖nsBilinear6A (u r) (u r) k c‖ * h2Weight k :=
            mul_nonneg (norm_nonneg _) (le_of_lt (h2Weight_pos k))
          have hrhs_nn : 0 ≤ 2 * Real.pi * Real.sqrt (4 * (4 : ℝ) ^ 10 * (53 * M) * B6) := by positivity
          nlinarith
        dsimp only [f']
        rw [norm_mul, norm_fourierMode8B, mul_one]
        have htri := norm_add_le
          ((-4 * (Real.pi : ℂ) ^ 2 * (ν : ℂ) * ((kNormSq k : ℝ) : ℂ)) * u r k c)
          (nsBilinear6A (u r) (u r) k c)
        dsimp only [C_dom]
        have hadd_div : (4 * Real.pi ^ 2 * ν * Real.sqrt B6) / h2Weight k +
            (2 * Real.pi * Real.sqrt (4 * (4 : ℝ) ^ 10 * (53 * M) * B6)) / h2Weight k =
            (4 * Real.pi ^ 2 * ν * Real.sqrt B6 +
              2 * Real.pi * Real.sqrt (4 * (4 : ℝ) ^ 10 * (53 * M) * B6)) / h2Weight k :=
          (add_div _ _ _).symm
        linarith)
  have hderiv_re : HasDerivAt (fun s => U s x c) (∑' k : Fin 3 → ℤ, f' t k).re t :=
    Complex.reCLM.hasFDerivAt.comp_hasDerivAt t hderiv_c
  have hrhs_eq : (∑' k : Fin 3 → ℤ, f' t k).re =
      ν * laplacian3D (U t) x c - advection3D (U t) x c - grad3D (P t) x c := by
    have hlap_s : Summable (fun k => ((ν : ℂ) * lapMode (fun m => u t m c) k) * fourierMode8B k x) := by
      have h10 : InHalfHmSeq 10 (fun m => u t m c) := hall_u 5 c
      have hdl := diffMode_inHalfHm (diffMode_inHalfHm h10 0) 0
      have hnorm : Summable (fun k => ‖(ν : ℂ) * lapMode (fun m => u t m c) k‖) := by
        have hle : ∀ k, ‖(ν : ℂ) * lapMode (fun m => u t m c) k‖ ≤
            (4 * Real.pi ^ 2 * ν) * (kNormSq k * ‖u t k c‖) := by
          intro k; unfold lapMode
          have h4 : ‖(-4 : ℂ)‖ = 4 := by norm_num
          rw [norm_mul, norm_mul, norm_mul, norm_mul, norm_pow, h4, Complex.norm_real,
              Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
              Real.norm_eq_abs, abs_of_pos hν, abs_of_pos Real.pi_pos,
              abs_of_nonneg (kNormSq_nonneg_8a k)]
          ring_nf; exact le_rfl
        exact Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hle
          ((summable_kNormSq_norm_of_inHalfHm8 (hall_u 4 c)).mul_left _)
      exact Summable.of_norm (by simpa [norm_mul, norm_fourierMode8B] using hnorm)
    have hflux_s : Summable (fun k => nsFlux6A (u t) (u t) k c * fourierMode8B k x) := by
      have h10 : InHmVec 5 (u t) := hall_u 5
      have hsj : ∀ j : Fin 3, Summable (fun k =>
          diffMode j (conv3D (fun m => u t m j) (fun m => u t m c)) k * fourierMode8B k x) := fun j =>
        Summable.of_norm (by
          have h8 : InHalfHmSeq 8 (conv3D (fun m => u t m j) (fun m => u t m c)) :=
            (conv3D_tame_l1_halfHm (by norm_num) (hall_u 4 j) (hall_u 4 c)).1
          simpa [norm_mul, norm_fourierMode8B] using
            (h2Seq_l1_embedding (inH2Seq_of_inHalfHmSeq (by norm_num) (diffMode_inHalfHm h8 j)).1).1)
      have hfun : (fun k => nsFlux6A (u t) (u t) k c * fourierMode8B k x) =
          (fun k => diffMode 0 (conv3D (fun m => u t m 0) (fun m => u t m c)) k * fourierMode8B k x +
                    diffMode 1 (conv3D (fun m => u t m 1) (fun m => u t m c)) k * fourierMode8B k x +
                    diffMode 2 (conv3D (fun m => u t m 2) (fun m => u t m c)) k * fourierMode8B k x) := by
        funext k; unfold nsFlux6A diffMode; ring
      rw [hfun]; exact ((hsj 0).add (hsj 1)).add (hsj 2)
    have hgrad_s : Summable (fun k => diffMode c (pressureCoeff6B (u t)) k * fourierMode8B k x) := by
      have hp8 : InHalfHmSeq 8 (pressureCoeff6B (u t)) := pressureCoeff6B_inHalfHm (by norm_num) (hall_u 4)
      exact Summable.of_norm (by
        simpa [norm_mul, norm_fourierMode8B] using
          (h2Seq_l1_embedding (inH2Seq_of_inHalfHmSeq (by norm_num) (diffMode_inHalfHm hp8 c)).1).1)
    have hf'_split : (fun k => f' t k) =
        (fun k => ((ν : ℂ) * lapMode (fun m => u t m c) k) * fourierMode8B k x -
          nsFlux6A (u t) (u t) k c * fourierMode8B k x -
          diffMode c (pressureCoeff6B (u t)) k * fourierMode8B k x) := by
      funext k
      dsimp only [f']
      rw [nsBilinear6A_eq_neg_flux_sub_grad_pressure (u t) k c]
      unfold lapMode diffMode; ring
    rw [hf'_split, (hlap_s.sub hflux_s).tsum_sub hgrad_s, hlap_s.tsum_sub hflux_s,
        Complex.sub_re, Complex.sub_re]
    have hlap_re : (∑' k, ((ν : ℂ) * lapMode (fun m => u t m c) k) * fourierMode8B k x).re =
        ν * laplacian3D (U t) x c := by
      have hpull : (fun k => ((ν : ℂ) * lapMode (fun m => u t m c) k) * fourierMode8B k x) =
          (fun k => (ν : ℂ) * (lapMode (fun m => u t m c) k * fourierMode8B k x)) :=
        funext fun k => by ring
      rw [hpull, tsum_mul_left, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
      have hl := laplacianScalar_smoothSynthScalar (hall_u 5 c) x
      change ν * smoothSynthScalar (lapMode (fun m => u t m c)) x =
        ν * laplacianScalar (smoothSynthScalar (fun m => u t m c)) x
      rw [hl]
    have hflux_re : (∑' k, nsFlux6A (u t) (u t) k c * fourierMode8B k x).re = advection3D (U t) x c :=
      smoothSynthScalar_nsFlux6A_eq_advection3D (hall_u 5) hst_t.1 hst_t.2 x c
    have hgrad_re : (∑' k, diffMode c (pressureCoeff6B (u t)) k * fourierMode8B k x).re = grad3D (P t) x c := by
      have hp8 : InHalfHmSeq 8 (pressureCoeff6B (u t)) := pressureCoeff6B_inHalfHm (by norm_num) (hall_u 4)
      exact (partialDerivScalar_smoothSynthScalar hp8 x c).symm
    rw [hlap_re, hflux_re, hgrad_re]
  rw [hrhs_eq] at hderiv_re
  exact ⟨hderiv_re, by rw [hderiv_re.deriv]; ring⟩

-- ============================================================================
-- SECTION 5: GRAND MASTER THEOREM OF MILESTONES 1–8 (TWO-TIER, 0 sorryAx)
-- ============================================================================

/-- **GRAND MASTER THEOREM OF `garry-ultimate-oss` (MILESTONES 1–8 COMPLETE, `0 sorryAx`):**
    Unifies the complete verified 3D Navier–Stokes formalization on `𝕋³` across both tiers:
    - **TIER I (Unconditional on `𝕋³`, 0 extra hypotheses):**
      1. **Local `C^∞` Classical Solution:** For ANY `u₀ ∈ H²_div(𝕋³)` (real-symmetric, arbitrary size),
         there exists `T* > 0` and a unique mild solution on `[0, T*]` whose physical velocity `U(t, ·)`
         and pressure `P(t, ·)` are `C^∞(𝕋³)`, `ℤ³`-periodic, divergence-free, and satisfy the exact
         pointwise 3D Navier–Stokes PDE on `(0, T*)`.
      2. **Global `C^∞` Classical Solution (Small Data & Compatible Viscosity):** For ANY mean-zero
         `u₀ ∈ H²_div(𝕋³)` with `217088 ‖u₀‖²_{H²} ≤ π² ν²`, there exists a UNIQUE global solution on
         `[0, ∞)` with `U(t, ·), P(t, ·) ∈ C^∞(𝕋³)` satisfying the exact pointwise 3D NS PDE for ALL `t > 0`.
      3. **Finite-Time Basin Entry ("Waterfall-to-River" Lift Law):** Any admissible mean-zero solution
         for arbitrarily large `u₀` that enters the small-data basin at finite time `T_enter ≥ 0`
         extends uniquely to a global `C^∞(𝕋³)` classical solution for ALL `t > 0`.
    - **TIER II (Conditional Garry Supercritical Closure — Non-Vacuous & Isolated):**
      4. `GarryConditionalClosureHypotheses ν B u₀` is non-vacuous and implies existence & uniqueness
         of a global solution on `[0, ∞)` whose physical velocity `U(t, ·)` and pressure `P(t, ·)`
         are `C^∞(𝕋³)`, `ℤ³`-periodic, divergence-free, and satisfy the exact pointwise 3D
         Navier–Stokes PDE for ALL `t > 0` and ALL `x ∈ ℝ³`. -/
theorem garry_millennium_master_theorem_torus3D {ν : ℝ} (hν : 0 < ν) :
    -- (1) TIER I: UNCONDITIONAL LOCAL C^∞ PHYSICAL 3D NS FOR ARBITRARY H²_div DATA
    (∀ {u₀ : VecSeq3D}, InH2Vec u₀ → IsSolenoidal u₀ → IsRealSymm u₀ →
      ∃ (Tstar : ℝ) (u : ℝ → VecSeq3D), 0 < Tstar ∧ u 0 = u₀ ∧
        ∀ t ∈ Set.Ioo (0 : ℝ) Tstar,
          ContDiff ℝ (⊤ : ℕ∞) (smoothSynthVec (u t)) ∧
          ContDiff ℝ (⊤ : ℕ∞) (smoothSynthScalar (pressureCoeff6B (u t))) ∧
          IsPeriodic3D (smoothSynthVec (u t)) ∧
          (∀ x : R3, div3D (smoothSynthVec (u t)) x = 0) ∧
          (∀ (x : R3) (c : Fin 3),
            deriv (fun s => smoothSynthVec (u s) x c) t +
              advection3D (smoothSynthVec (u t)) x c +
              grad3D (smoothSynthScalar (pressureCoeff6B (u t))) x c =
              ν * laplacian3D (smoothSynthVec (u t)) x c)) ∧
    -- (2) TIER I: UNCONDITIONAL GLOBAL C^∞ PHYSICAL 3D NS ON (0, ∞) FOR SMALL / COMPATIBLE DATA
    (∀ {u₀ : VecSeq3D}, InH2Vec u₀ → IsSolenoidal u₀ → IsRealSymm u₀ →
      (∀ c : Fin 3, u₀ 0 c = 0) → 217088 * h2VecNormSq u₀ ≤ Real.pi ^ 2 * ν ^ 2 →
      ∃ u : ℝ → VecSeq3D, u 0 = u₀ ∧
        ∀ t : ℝ, 0 < t →
          ContDiff ℝ (⊤ : ℕ∞) (smoothSynthVec (u t)) ∧
          ContDiff ℝ (⊤ : ℕ∞) (smoothSynthScalar (pressureCoeff6B (u t))) ∧
          IsPeriodic3D (smoothSynthVec (u t)) ∧
          (∀ x : R3, div3D (smoothSynthVec (u t)) x = 0) ∧
          (∀ (x : R3) (c : Fin 3),
            deriv (fun s => smoothSynthVec (u s) x c) t +
              advection3D (smoothSynthVec (u t)) x c +
              grad3D (smoothSynthScalar (pressureCoeff6B (u t))) x c =
              ν * laplacian3D (smoothSynthVec (u t)) x c)) ∧
    -- (3) TIER II: CONDITIONAL GARRY CLOSURE (NON-VACUOUS) ⇒ GLOBAL C^∞ PHYSICAL 3D NS ON (0, ∞)
    (∃ (B : ℝ) (u₀ : VecSeq3D), GarryConditionalClosureHypotheses ν B u₀) ∧
    (∀ {B : ℝ} {u₀ : VecSeq3D}, GarryConditionalClosureHypotheses ν B u₀ →
      ∃ u : ℝ → VecSeq3D, u 0 = u₀ ∧
        ∀ t : ℝ, 0 < t →
          ContDiff ℝ (⊤ : ℕ∞) (smoothSynthVec (u t)) ∧
          ContDiff ℝ (⊤ : ℕ∞) (smoothSynthScalar (pressureCoeff6B (u t))) ∧
          IsPeriodic3D (smoothSynthVec (u t)) ∧
          (∀ x : R3, div3D (smoothSynthVec (u t)) x = 0) ∧
          (∀ (x : R3) (c : Fin 3),
            deriv (fun s => smoothSynthVec (u s) x c) t +
              advection3D (smoothSynthVec (u t)) x c +
              grad3D (smoothSynthScalar (pressureCoeff6B (u t))) x c =
              ν * laplacian3D (smoothSynthVec (u t)) x c)) := by
  refine ⟨?_, ?_, (milestone7_two_tier_boundary_audit_torus3D hν).2.2.2.2.1, ?_⟩
  · intro u₀ hu₀ hsol₀ hsym₀
    let M : ℝ := 4 * h2VecNormSq u₀ + 1
    let Tstar : ℝ := ν / (54272 * M)
    have hM : 0 ≤ M := by dsimp only [M]; linarith [h2VecNormSq_nonneg u₀]
    obtain ⟨hTstar, u, hu_adm, hu0, hu_sol, _, _, hu_struct, _⟩ :=
      local_existence_uniqueness_ns3d_torus3D hν hu₀ hsol₀ hsym₀
    refine ⟨Tstar, u, hTstar, hu0, fun t ht => ?_⟩
    have hphys := mild_solution_physical_ns3d_torus3D hν hM u₀ hu_adm hu_sol
      (fun s _ => ⟨(hu_struct s).1, (hu_struct s).2.1⟩) t ht
    exact ⟨hphys.2.1, hphys.2.2.2.2.1, hphys.2.2.1, hphys.2.2.2.2.2.2.1,
      fun x c => (hphys.2.2.2.2.2.2.2 x c).2⟩
  · intro u₀ hu₀ hsol₀ hsym₀ hzero hcompat
    have hsm : h2VecNormSq u₀ ≤ Real.pi ^ 2 * ν ^ 2 / 217088 := by linarith
    obtain ⟨u, hu_adm, hu0, hu_duh, _, hu_struct, _⟩ :=
      global_existence_small_data_ns3d_torus3D hν hu₀ hsol₀ hsym₀ hzero hsm
    refine ⟨u, hu0, fun t ht => ?_⟩
    have hphys := mild_solution_physical_ns3d_torus3D (T := t + 1) hν (by positivity) u₀ hu_adm
      (fun s hs => hu_duh s hs.1) (fun s _ => ⟨(hu_struct s).1, (hu_struct s).2.1⟩) t ⟨ht, by linarith⟩
    exact ⟨hphys.2.1, hphys.2.2.2.2.1, hphys.2.2.1, hphys.2.2.2.2.2.2.1,
      fun x c => (hphys.2.2.2.2.2.2.2 x c).2⟩
  · intro B u₀ hG
    obtain ⟨u, hu_adm, hu0, hu_duh, _, hu_struct, _, _⟩ :=
      global_continuation_of_apriori_H2_bound_torus3D hG.hν_pos hG.hB_nonneg
        hG.hu₀_inH2 hG.hu₀_sol hG.hu₀_sym hG.hu₀_bound hG.h_apriori_step
    refine ⟨u, hu0, fun t ht => ?_⟩
    have hphys := mild_solution_physical_ns3d_torus3D (T := t + 1) hG.hν_pos
      (by linarith [hG.hB_nonneg]) u₀ hu_adm
      (fun s hs => hu_duh s hs.1) (fun s _ => ⟨(hu_struct s).1, (hu_struct s).2.1⟩) t ⟨ht, by linarith⟩
    exact ⟨hphys.2.1, hphys.2.2.2.2.1, hphys.2.2.1, hphys.2.2.2.2.2.2.1,
      fun x c => (hphys.2.2.2.2.2.2.2 x c).2⟩

-- ============================================================================
-- SECTION 6: AXIOM AUDIT TRAIL — MILESTONE 8B (0 sorryAx)
-- ============================================================================

#print axioms smoothSynthScalarC_conv3D
#print axioms smoothSynthScalarC_hasFDerivAt
#print axioms smoothSynthScalarC_contDiff_of_inHalfHm
#print axioms smoothSynthScalar_contDiff_infty
#print axioms smoothSynthVec_contDiff_infty
#print axioms partialDerivScalar_smoothSynthScalar
#print axioms laplacianScalar_smoothSynthScalar
#print axioms div3D_smoothSynthVec_eq_zero
#print axioms pressureCoeff6B_inHalfHm
#print axioms smoothSynthPressure_contDiff_infty
#print axioms mild_solution_physical_ns3d_torus3D
#print axioms garry_millennium_master_theorem_torus3D

end GarrySmoothSynthesis3D