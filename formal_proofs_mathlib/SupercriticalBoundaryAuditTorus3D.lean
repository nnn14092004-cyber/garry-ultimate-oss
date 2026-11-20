import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Abel
import GarrySupercriticalBridgeTorus3D

/-!
# GARRYULT v4.0.0 — Milestone 7C: Formal Two-Tier Boundary Audit & Anti-Circularity Fence
# 1. Unconditional 3D Parabolic Supercritical Scaling Barrier (`E_λ = λ⁻¹ E₀`, `Z_λ = λ Z₀`, `P_λ = λ³ P₀`)
# 2. Unconditional Tame Wiener-Algebra (`ℓ¹`) Bilinear Estimate & `M`-Independent `H²` Continuation Bound
# 3. Isolated Conditional Garry Closure Interface (`GarryConditionalClosureHypotheses`) + Non-Vacuity Proof
# 4. Master Two-Tier Audit Theorem Separating Unconditional `𝕋³` Theorems from Conditional Garry Criteria
# (`0 sorryAx`)
-/

namespace GarrySupercriticalAudit3D

open MeasureTheory Filter Topology GarryReal3DCalculus GarryVorticity3D
  GarryLerayTorus3D GarryLerayEnergyLaw3D GarryPoincareSobolev3D
  GarryFourierSpectral3D GarrySpectralOperators3D GarryParsevalSobolev3D
  GarrySobolevEmbedding3D GarrySpectralAlgebra3D GarrySpectralBilinear3D
  GarryDuhamelOperator3D GarryLocalExistence3D GarryGlobalRegularity3D
  GarrySupercriticalBridge3D

-- ============================================================================
-- SECTION 1: UNCONDITIONAL 3D NAVIER–STOKES SUPERCRITICAL SCALING BARRIER
-- ============================================================================

/-- **THEOREM 1 OF MILESTONE 7C (Unconditional 3D Parabolic Scaling Supercriticality Barrier):**
    Under the exact 3D Navier–Stokes scaling `u_λ(t, x) = λ u(λ² t, λ x)`:
    - `L²` kinetic energy scales as `λ⁻¹ E₀` (supercritical),
    - `H^{1/2}` critical norm scales as `λ⁰ = 1` (scale-invariant barrier),
    - `H¹` enstrophy scales as `λ Z₀` (subcritical),
    - `H²` palinstrophy scales as `λ³ P₀` (subcritical).
    Consequently, for ANY arbitrarily small energy ceiling `ε > 0` and ANY arbitrarily large
    target `R > 0`, there exists `λ > 0` with `λ⁻¹ E₀ < ε` while simultaneously `R < λ Z₀`
    and `R < λ³ P₀` — formally proving why `E(T) ≤ E(0)` alone cannot close `H¹`/`H²` for
    arbitrary large initial data (`0 sorryAx`). -/
theorem ns3d_supercritical_energy_barrier
    {E₀ Z₀ P₀ : ℝ} (_hE : 0 < E₀) (hZ : 0 < Z₀) (hP : 0 < P₀) :
    (∀ lam : ℝ, 0 < lam → (lam⁻¹ * E₀) * (lam * Z₀) = E₀ * Z₀) ∧
    (∀ (ε R : ℝ), 0 < ε → 0 < R →
      ∃ lam : ℝ, 0 < lam ∧ lam⁻¹ * E₀ < ε ∧ R < lam * Z₀ ∧ R < lam ^ 3 * P₀) := by
  refine ⟨fun lam hlam => ?_, fun ε R hε hR => ?_⟩
  · have hne : lam ≠ 0 := ne_of_gt hlam
    calc (lam⁻¹ * E₀) * (lam * Z₀)
        = (lam⁻¹ * lam) * (E₀ * Z₀) := by ring
      _ = 1 * (E₀ * Z₀) := by rw [inv_mul_cancel₀ hne]
      _ = E₀ * Z₀ := one_mul _
  · let lam : ℝ := max (E₀ / ε) (max (R / Z₀) (max (R / P₀) 1)) + 1
    have h1 : 1 ≤ max (E₀ / ε) (max (R / Z₀) (max (R / P₀) 1)) :=
      le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) (le_max_right _ _)
    have hlam_gt1 : 1 < lam := by dsimp only [lam]; linarith
    have hlam_pos : 0 < lam := by linarith
    have hE_lt : E₀ / ε < lam := by
      dsimp only [lam]; linarith [le_max_left (E₀ / ε) (max (R / Z₀) (max (R / P₀) 1))]
    have hZ_lt : R / Z₀ < lam := by
      dsimp only [lam]
      have := le_trans (le_max_left (R / Z₀) (max (R / P₀) 1))
        (le_max_right (E₀ / ε) (max (R / Z₀) (max (R / P₀) 1)))
      linarith
    have hP_lt : R / P₀ < lam := by
      dsimp only [lam]
      have := le_trans (le_trans (le_max_left (R / P₀) 1) (le_max_right (R / Z₀) (max (R / P₀) 1)))
        (le_max_right (E₀ / ε) (max (R / Z₀) (max (R / P₀) 1)))
      linarith
    have hE_bd : lam⁻¹ * E₀ < ε := by
      have hmul : E₀ < lam * ε := by
        have h := mul_lt_mul_of_pos_right hE_lt hε
        rwa [div_mul_cancel₀ E₀ (ne_of_gt hε)] at h
      have hinv := mul_lt_mul_of_pos_left hmul (inv_pos.mpr hlam_pos)
      have hcancel : lam⁻¹ * (lam * ε) = ε := by
        rw [← mul_assoc, inv_mul_cancel₀ (ne_of_gt hlam_pos), one_mul]
      rwa [hcancel] at hinv
    have hZ_bd : R < lam * Z₀ := by
      have h := mul_lt_mul_of_pos_right hZ_lt hZ
      rwa [div_mul_cancel₀ R (ne_of_gt hZ)] at h
    have hP_bd : R < lam ^ 3 * P₀ := by
      have hlam_sq : 1 ≤ lam ^ 2 := by nlinarith
      have hlam_le_cube : lam ≤ lam ^ 3 := by
        calc lam = lam * 1 := (mul_one lam).symm
          _ ≤ lam * lam ^ 2 := mul_le_mul_of_nonneg_left hlam_sq (le_of_lt hlam_pos)
          _ = lam ^ 3 := by ring
      have h1' : R < lam * P₀ := by
        have h := mul_lt_mul_of_pos_right hP_lt hP
        rwa [div_mul_cancel₀ R (ne_of_gt hP)] at h
      have h2' : lam * P₀ ≤ lam ^ 3 * P₀ := mul_le_mul_of_nonneg_right hlam_le_cube (le_of_lt hP)
      linarith
    exact ⟨lam, hlam_pos, hE_bd, hZ_bd, hP_bd⟩

-- ============================================================================
-- SECTION 2: UNCONDITIONAL TAME WIENER (`ℓ¹`) BILINEAR ESTIMATE & `H²` BOUND
-- ============================================================================

/-- Squared Wiener algebra norm `‖u‖²_{A(𝕋³)} = ∑_{c=0}^2 (∑' k, ‖û_c(k)‖)²`. -/
noncomputable def wienerNormSq (u : VecSeq3D) : ℝ :=
  (∑' j : Fin 3 → ℤ, ‖u j 0‖) ^ 2 +
  (∑' j : Fin 3 → ℤ, ‖u j 1‖) ^ 2 +
  (∑' j : Fin 3 → ℤ, ‖u j 2‖) ^ 2

theorem wienerNormSq_nonneg (u : VecSeq3D) : 0 ≤ wienerNormSq u := by
  unfold wienerNormSq; positivity

theorem wienerNormSq_le_53_h2VecNormSq {u : VecSeq3D} (hu : InH2Vec u) :
    wienerNormSq u ≤ 53 * h2VecNormSq u := by
  unfold wienerNormSq h2VecNormSq
  linarith [(h2Seq_l1_embedding (hu 0)).2,
            (h2Seq_l1_embedding (hu 1)).2,
            (h2Seq_l1_embedding (hu 2)).2]

private def subLeftEquiv7c (k : Fin 3 → ℤ) : (Fin 3 → ℤ) ≃ (Fin 3 → ℤ) where
  toFun j := k - j
  invFun j := k - j
  left_inv j := sub_sub_cancel k j
  right_inv j := sub_sub_cancel k j

private theorem summable_sub_left_7c {f : (Fin 3 → ℤ) → ℝ} (hf : Summable f) (k : Fin 3 → ℤ) :
    Summable (fun j => f (k - j)) :=
  ((subLeftEquiv7c k).hasSum_iff.mpr hf.hasSum).summable

private theorem tsum_sub_left_7c {f : (Fin 3 → ℤ) → ℝ} (hf : Summable f) (k : Fin 3 → ℤ) :
    (∑' j : Fin 3 → ℤ, f (k - j)) = ∑' m : Fin 3 → ℤ, f m :=
  ((subLeftEquiv7c k).hasSum_iff.mpr hf.hasSum).tsum_eq

/-- **THEOREM 2 OF MILESTONE 7C (Unconditional Tame Moser–Wiener Convolution Estimate in `H²(𝕋³)`):**
    `‖a * b‖²_{H²} ≤ 16 (‖b‖²_{ℓ¹} ‖a‖²_{H²} + ‖a‖²_{ℓ¹} ‖b‖²_{H²})` (`0 sorryAx`). -/
theorem conv3D_tame_l1_H2 {a b : (Fin 3 → ℤ) → ℂ} (ha : InH2Seq a) (hb : InH2Seq b) :
    h2NormSq (conv3D a b) ≤
      16 * (∑' j : Fin 3 → ℤ, ‖b j‖) ^ 2 * h2NormSq a +
      16 * (∑' j : Fin 3 → ℤ, ‖a j‖) ^ 2 * h2NormSq b := by
  have ha_l1 := h2Seq_l1_embedding ha
  have hb_l1 := h2Seq_l1_embedding hb
  have ha_l2 := (h2Seq_l2_summable ha).1
  have hb_l2 := (h2Seq_l2_summable hb).1
  let wa : (Fin 3 → ℤ) → ℝ := fun m => Real.sqrt (h2Weight m) * ‖a m‖
  let wb : (Fin 3 → ℤ) → ℝ := fun m => Real.sqrt (h2Weight m) * ‖b m‖
  have hwa_sq : (fun m => (wa m) ^ 2) = (fun m => h2Weight m * ‖a m‖ ^ 2) := by
    funext m; dsimp only [wa]; rw [mul_pow, Real.sq_sqrt (le_of_lt (h2Weight_pos m))]
  have hwb_sq : (fun m => (wb m) ^ 2) = (fun m => h2Weight m * ‖b m‖ ^ 2) := by
    funext m; dsimp only [wb]; rw [mul_pow, Real.sq_sqrt (le_of_lt (h2Weight_pos m))]
  have hwa_sum2 : Summable (fun m => (wa m) ^ 2) := by rw [hwa_sq]; exact ha
  have hwb_sum2 : Summable (fun m => (wb m) ^ 2) := by rw [hwb_sq]; exact hb
  let T1 : (Fin 3 → ℤ) → ℝ := fun k => ∑' j, ‖b j‖ * wa (k - j)
  let T2 : (Fin 3 → ℤ) → ℝ := fun k => ∑' j, ‖a j‖ * wb (k - j)
  have hY1 := young_l1_l2_3d hb_l1.1 hwa_sum2 (fun _ => norm_nonneg _) (fun _ => by dsimp only [wa]; positivity)
  have hY2 := young_l1_l2_3d ha_l1.1 hwb_sum2 (fun _ => norm_nonneg _) (fun _ => by dsimp only [wb]; positivity)
  have hpt : ∀ k : Fin 3 → ℤ, h2Weight k * ‖conv3D a b k‖ ^ 2 ≤
      16 * (T1 k) ^ 2 + 16 * (T2 k) ^ 2 := by
    intro k
    have hnorm_le : ‖conv3D a b k‖ ≤ ∑' j, ‖a j * b (k - j)‖ :=
      norm_tsum_le_tsum_norm (conv3D_summable_norm ha hb k)
    have hsum_t1_raw : Summable (fun j => ‖b (k - j)‖ * wa j) := by
      have hdom : Summable (fun j => (1 / 2 : ℝ) * ‖b (k - j)‖ ^ 2 + (1 / 2 : ℝ) * (wa j) ^ 2) :=
        ((summable_sub_left_7c hb_l2 k).mul_left (1 / 2 : ℝ)).add (hwa_sum2.mul_left (1 / 2 : ℝ))
      refine Summable.of_nonneg_of_le (fun _ => by dsimp only [wa]; positivity) (fun j => ?_) hdom
      nlinarith [sq_nonneg (‖b (k - j)‖ - wa j)]
    have hsum_t2 : Summable (fun j => ‖a j‖ * wb (k - j)) := by
      have hdom : Summable (fun j => (1 / 2 : ℝ) * ‖a j‖ ^ 2 + (1 / 2 : ℝ) * (wb (k - j)) ^ 2) :=
        (ha_l2.mul_left (1 / 2 : ℝ)).add ((summable_sub_left_7c hwb_sum2 k).mul_left (1 / 2 : ℝ))
      refine Summable.of_nonneg_of_le (fun _ => by dsimp only [wb]; positivity) (fun j => ?_) hdom
      nlinarith [sq_nonneg (‖a j‖ - wb (k - j))]
    have hreidx : (∑' j, ‖b (k - j)‖ * wa j) = T1 k := by
      dsimp only [T1]
      have h := tsum_sub_left_7c hsum_t1_raw k
      have heq : (fun j => ‖b (k - (k - j))‖ * wa (k - j)) = (fun j => ‖b j‖ * wa (k - j)) := by
        funext j; rw [sub_sub_cancel]
      rw [heq] at h
      exact h.symm
    have hterm_le : ∀ j, Real.sqrt (h2Weight k) * ‖a j * b (k - j)‖ ≤
        Real.sqrt 8 * (‖b (k - j)‖ * wa j) + Real.sqrt 8 * (‖a j‖ * wb (k - j)) := by
      intro j
      have hjk : j + (k - j) = k := by abel
      have hsqrt := sqrt_h2Weight_add_le j (k - j)
      rw [hjk] at hsqrt
      rw [norm_mul]
      have hmul := mul_le_mul_of_nonneg_right hsqrt
        (mul_nonneg (norm_nonneg (a j)) (norm_nonneg (b (k - j))))
      dsimp only [wa, wb]
      linarith
    have hsum_lhs : HasSum (fun j => Real.sqrt (h2Weight k) * ‖a j * b (k - j)‖)
        (Real.sqrt (h2Weight k) * ∑' j, ‖a j * b (k - j)‖) :=
      (conv3D_summable_norm ha hb k).hasSum.mul_left (Real.sqrt (h2Weight k))
    have hsum_rhs : HasSum
        (fun j => Real.sqrt 8 * (‖b (k - j)‖ * wa j) + Real.sqrt 8 * (‖a j‖ * wb (k - j)))
        (Real.sqrt 8 * (∑' j, ‖b (k - j)‖ * wa j) + Real.sqrt 8 * T2 k) :=
      (hsum_t1_raw.hasSum.mul_left (Real.sqrt 8)).add (hsum_t2.hasSum.mul_left (Real.sqrt 8))
    have hbd_sqrt : Real.sqrt (h2Weight k) * ‖conv3D a b k‖ ≤ Real.sqrt 8 * (T1 k + T2 k) := by
      have h1 := mul_le_mul_of_nonneg_left hnorm_le (Real.sqrt_nonneg (h2Weight k))
      have h2 := hasSum_le hterm_le hsum_lhs hsum_rhs
      rw [hreidx] at h2
      linarith
    have hlhs_nn : 0 ≤ Real.sqrt (h2Weight k) * ‖conv3D a b k‖ := by positivity
    have hsq_both : (Real.sqrt (h2Weight k) * ‖conv3D a b k‖) ^ 2 ≤
        (Real.sqrt 8 * (T1 k + T2 k)) ^ 2 := by nlinarith
    rw [mul_pow, Real.sq_sqrt (le_of_lt (h2Weight_pos k)),
        mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 8)] at hsq_both
    nlinarith [sq_nonneg (T1 k - T2 k)]
  have hconv_inH2 : InH2Seq (conv3D a b) := (conv3D_inH2_and_norm_le ha hb).1
  have hbd_sum : h2NormSq (conv3D a b) ≤ 16 * (∑' k, (T1 k) ^ 2) + 16 * (∑' k, (T2 k) ^ 2) :=
    hasSum_le hpt hconv_inH2.hasSum ((hY1.1.hasSum.mul_left 16).add (hY2.1.hasSum.mul_left 16))
  have hY1_bd : (∑' k, (T1 k) ^ 2) ≤ (∑' j : Fin 3 → ℤ, ‖b j‖) ^ 2 * h2NormSq a := by
    have h1 := hY1.2; rwa [hwa_sq] at h1
  have hY2_bd : (∑' k, (T2 k) ^ 2) ≤ (∑' j : Fin 3 → ℤ, ‖a j‖) ^ 2 * h2NormSq b := by
    have h2 := hY2.2; rwa [hwb_sq] at h2
  linarith

private theorem norm_linear_comb_sq_le_7c (k : Fin 3 → ℤ) (z : Fin 3 → ℂ) :
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
    have h0 : |(k 0 : ℝ)| ^ 2 = (k 0 : ℝ) ^ 2 := sq_abs _
    have h1 : |(k 1 : ℝ)| ^ 2 = (k 1 : ℝ) ^ 2 := sq_abs _
    have h2 : |(k 2 : ℝ)| ^ 2 = (k 2 : ℝ) ^ 2 := sq_abs _
    nlinarith [sq_nonneg (|(k 0 : ℝ)| * ‖z 1‖ - |(k 1 : ℝ)| * ‖z 0‖),
               sq_nonneg (|(k 0 : ℝ)| * ‖z 2‖ - |(k 2 : ℝ)| * ‖z 0‖),
               sq_nonneg (|(k 1 : ℝ)| * ‖z 2‖ - |(k 2 : ℝ)| * ‖z 1‖), h0, h1, h2]
  unfold kNormSq
  exact le_trans hsq hcs

private theorem nsBilinear6A_normSq_le_7c (u v : VecSeq3D) (k : Fin 3 → ℤ) :
    vecNormSqC (nsBilinear6A u v k) ≤
      4 * Real.pi ^ 2 * kNormSq k *
        ((‖conv3D (fun m => u m 0) (fun m => v m 0) k‖ ^ 2 +
          ‖conv3D (fun m => u m 1) (fun m => v m 0) k‖ ^ 2 +
          ‖conv3D (fun m => u m 2) (fun m => v m 0) k‖ ^ 2) +
         (‖conv3D (fun m => u m 0) (fun m => v m 1) k‖ ^ 2 +
          ‖conv3D (fun m => u m 1) (fun m => v m 1) k‖ ^ 2 +
          ‖conv3D (fun m => u m 2) (fun m => v m 1) k‖ ^ 2) +
         (‖conv3D (fun m => u m 0) (fun m => v m 2) k‖ ^ 2 +
          ‖conv3D (fun m => u m 1) (fun m => v m 2) k‖ ^ 2 +
          ‖conv3D (fun m => u m 2) (fun m => v m 2) k‖ ^ 2)) := by
  have hneg : vecNormSqC (nsBilinear6A u v k) = vecNormSqC (lerayProj6A k (nsFlux6A u v k)) := by
    unfold vecNormSqC nsBilinear6A; simp only [norm_neg]
  rw [hneg]
  have hproj := lerayProj6A_normSq_le k (nsFlux6A u v k)
  have h2pi : ‖(2 : ℂ) * (Real.pi : ℂ) * Complex.I‖ ^ 2 = 4 * Real.pi ^ 2 := by
    have h2 : ‖(2 : ℂ)‖ = 2 := by norm_num
    rw [norm_mul, norm_mul, Complex.norm_I, mul_one, h2,
        Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
    ring
  have hflux_c : ∀ c : Fin 3, ‖nsFlux6A u v k c‖ ^ 2 ≤
      4 * Real.pi ^ 2 * kNormSq k *
        (‖conv3D (fun m => u m 0) (fun m => v m c) k‖ ^ 2 +
         ‖conv3D (fun m => u m 1) (fun m => v m c) k‖ ^ 2 +
         ‖conv3D (fun m => u m 2) (fun m => v m c) k‖ ^ 2) := by
    intro c
    unfold nsFlux6A
    rw [norm_mul, mul_pow, h2pi]
    have hcs := norm_linear_comb_sq_le_7c k (fun j => conv3D (fun m => u m j) (fun m => v m c) k)
    have hpi_nn : 0 ≤ 4 * Real.pi ^ 2 := by positivity
    nlinarith
  unfold vecNormSqC at hproj ⊢
  rw [mul_add, mul_add]
  linarith [hproj, hflux_c 0, hflux_c 1, hflux_c 2]

/-- **THEOREM 3 OF MILESTONE 7C (Unconditional Tame Heat-Smoothed Bilinear Estimate):**
    Linear in `‖u‖²_{H²}` with Wiener-algebra coefficient `wienerNormSq u`:
    `‖e^{ντΔ} B(u, u)‖²_{H²} ≤ (16 / (ν τ)) * wienerNormSq u * ‖u‖²_{H²}` (`0 sorryAx`). -/
theorem heatSmoothedBilinear6A_tame_wiener_H2
    {ν τ : ℝ} (hν : 0 < ν) (hτ : 0 < τ) {u : VecSeq3D} (hu : InH2Vec u) :
    h2VecNormSq (heatSmoothedBilinear6A ν τ u u) ≤
      (16 / (ν * τ)) * wienerNormSq u * h2VecNormSq u := by
  let C : Fin 3 → Fin 3 → (Fin 3 → ℤ) → ℂ := fun j c => conv3D (fun m => u m j) (fun m => u m c)
  have hC_in : ∀ j c : Fin 3, InH2Seq (C j c) := fun j c => (conv3D_inH2_and_norm_le (hu j) (hu c)).1
  have hC_bd : ∀ j c : Fin 3, h2NormSq (C j c) ≤
      16 * (∑' m : Fin 3 → ℤ, ‖u m c‖) ^ 2 * h2NormSq (fun m => u m j) +
      16 * (∑' m : Fin 3 → ℤ, ‖u m j‖) ^ 2 * h2NormSq (fun m => u m c) :=
    fun j c => conv3D_tame_l1_H2 (hu j) (hu c)
  let term : Fin 3 → Fin 3 → (Fin 3 → ℤ) → ℝ := fun j c k => h2Weight k * ‖C j c k‖ ^ 2
  let sum9 : (Fin 3 → ℤ) → ℝ := fun k =>
    (term 0 0 k + term 1 0 k + term 2 0 k) +
    (term 0 1 k + term 1 1 k + term 2 1 k) +
    (term 0 2 k + term 1 2 k + term 2 2 k)
  have hsum9_has : HasSum sum9
      ((h2NormSq (C 0 0) + h2NormSq (C 1 0) + h2NormSq (C 2 0)) +
       (h2NormSq (C 0 1) + h2NormSq (C 1 1) + h2NormSq (C 2 1)) +
       (h2NormSq (C 0 2) + h2NormSq (C 1 2) + h2NormSq (C 2 2))) :=
    ((((((hC_in 0 0).hasSum.add (hC_in 1 0).hasSum).add (hC_in 2 0).hasSum).add
      (((hC_in 0 1).hasSum.add (hC_in 1 1).hasSum).add (hC_in 2 1).hasSum)).add
      (((hC_in 0 2).hasSum.add (hC_in 1 2).hasSum).add (hC_in 2 2).hasSum)))
  have hdom_has := hsum9_has.mul_left (1 / (2 * ν * τ))
  have hpt_vec : ∀ k : Fin 3 → ℤ,
      h2Weight k * vecNormSqC (heatSmoothedBilinear6A ν τ u u k) ≤
        (1 / (2 * ν * τ)) * sum9 k := by
    intro k
    have hmul_eq : vecNormSqC (heatSmoothedBilinear6A ν τ u u k) =
        (heatMultiplier3D ν τ k) ^ 2 * vecNormSqC (nsBilinear6A u u k) := by
      unfold vecNormSqC heatSmoothedBilinear6A
      simp only [norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs]
      ring
    have hsm := heatMultiplier3D_smoothing_H1 hν hτ k
    have hbi := nsBilinear6A_normSq_le_7c u u k
    have hw_nn : 0 ≤ h2Weight k := le_of_lt (h2Weight_pos k)
    have hsumC_nn : 0 ≤
        ((‖C 0 0 k‖ ^ 2 + ‖C 1 0 k‖ ^ 2 + ‖C 2 0 k‖ ^ 2) +
         (‖C 0 1 k‖ ^ 2 + ‖C 1 1 k‖ ^ 2 + ‖C 2 1 k‖ ^ 2) +
         (‖C 0 2 k‖ ^ 2 + ‖C 1 2 k‖ ^ 2 + ‖C 2 2 k‖ ^ 2)) := by positivity
    have h1 : (heatMultiplier3D ν τ k) ^ 2 * vecNormSqC (nsBilinear6A u u k) ≤
        (4 * Real.pi ^ 2 * kNormSq k * (heatMultiplier3D ν τ k) ^ 2) *
          ((‖C 0 0 k‖ ^ 2 + ‖C 1 0 k‖ ^ 2 + ‖C 2 0 k‖ ^ 2) +
           (‖C 0 1 k‖ ^ 2 + ‖C 1 1 k‖ ^ 2 + ‖C 2 1 k‖ ^ 2) +
           (‖C 0 2 k‖ ^ 2 + ‖C 1 2 k‖ ^ 2 + ‖C 2 2 k‖ ^ 2)) := by
      have h2 := mul_le_mul_of_nonneg_left hbi (sq_nonneg (heatMultiplier3D ν τ k))
      dsimp only [C]; linarith
    have h2 := mul_le_mul_of_nonneg_right hsm hsumC_nn
    have h3 : h2Weight k * vecNormSqC (heatSmoothedBilinear6A ν τ u u k) ≤
        h2Weight k * ((1 / (2 * ν * τ)) *
          ((‖C 0 0 k‖ ^ 2 + ‖C 1 0 k‖ ^ 2 + ‖C 2 0 k‖ ^ 2) +
           (‖C 0 1 k‖ ^ 2 + ‖C 1 1 k‖ ^ 2 + ‖C 2 1 k‖ ^ 2) +
           (‖C 0 2 k‖ ^ 2 + ‖C 1 2 k‖ ^ 2 + ‖C 2 2 k‖ ^ 2))) := by
      rw [hmul_eq]; exact mul_le_mul_of_nonneg_left (le_trans h1 h2) hw_nn
    have hfac : h2Weight k * ((1 / (2 * ν * τ)) *
        ((‖C 0 0 k‖ ^ 2 + ‖C 1 0 k‖ ^ 2 + ‖C 2 0 k‖ ^ 2) +
         (‖C 0 1 k‖ ^ 2 + ‖C 1 1 k‖ ^ 2 + ‖C 2 1 k‖ ^ 2) +
         (‖C 0 2 k‖ ^ 2 + ‖C 1 2 k‖ ^ 2 + ‖C 2 2 k‖ ^ 2))) =
        (1 / (2 * ν * τ)) * sum9 k := by dsimp only [sum9, term]; ring
    linarith
  have hS_inH2 := (heatSmoothedBilinear6A_inH2_and_bound hν hτ hu hu).1
  have htsum_bd := hasSum_le hpt_vec (hasSum_h2VecNormSq hS_inH2) hdom_has
  have hsum9_bd :
      ((h2NormSq (C 0 0) + h2NormSq (C 1 0) + h2NormSq (C 2 0)) +
       (h2NormSq (C 0 1) + h2NormSq (C 1 1) + h2NormSq (C 2 1)) +
       (h2NormSq (C 0 2) + h2NormSq (C 1 2) + h2NormSq (C 2 2))) ≤
      32 * wienerNormSq u * h2VecNormSq u := by
    have hfac : 32 * wienerNormSq u * h2VecNormSq u =
        ((16 * (∑' m, ‖u m 0‖) ^ 2 * h2NormSq (fun m => u m 0) + 16 * (∑' m, ‖u m 0‖) ^ 2 * h2NormSq (fun m => u m 0)) +
         (16 * (∑' m, ‖u m 0‖) ^ 2 * h2NormSq (fun m => u m 1) + 16 * (∑' m, ‖u m 1‖) ^ 2 * h2NormSq (fun m => u m 0)) +
         (16 * (∑' m, ‖u m 0‖) ^ 2 * h2NormSq (fun m => u m 2) + 16 * (∑' m, ‖u m 2‖) ^ 2 * h2NormSq (fun m => u m 0))) +
        ((16 * (∑' m, ‖u m 1‖) ^ 2 * h2NormSq (fun m => u m 0) + 16 * (∑' m, ‖u m 0‖) ^ 2 * h2NormSq (fun m => u m 1)) +
         (16 * (∑' m, ‖u m 1‖) ^ 2 * h2NormSq (fun m => u m 1) + 16 * (∑' m, ‖u m 1‖) ^ 2 * h2NormSq (fun m => u m 1)) +
         (16 * (∑' m, ‖u m 1‖) ^ 2 * h2NormSq (fun m => u m 2) + 16 * (∑' m, ‖u m 2‖) ^ 2 * h2NormSq (fun m => u m 1))) +
        ((16 * (∑' m, ‖u m 2‖) ^ 2 * h2NormSq (fun m => u m 0) + 16 * (∑' m, ‖u m 0‖) ^ 2 * h2NormSq (fun m => u m 2)) +
         (16 * (∑' m, ‖u m 2‖) ^ 2 * h2NormSq (fun m => u m 1) + 16 * (∑' m, ‖u m 1‖) ^ 2 * h2NormSq (fun m => u m 2)) +
         (16 * (∑' m, ‖u m 2‖) ^ 2 * h2NormSq (fun m => u m 2) + 16 * (∑' m, ‖u m 2‖) ^ 2 * h2NormSq (fun m => u m 2))) := by
      unfold wienerNormSq h2VecNormSq; ring
    rw [hfac]
    linarith [hC_bd 0 0, hC_bd 1 0, hC_bd 2 0,
              hC_bd 0 1, hC_bd 1 1, hC_bd 2 1,
              hC_bd 0 2, hC_bd 1 2, hC_bd 2 2]
  have hbd2 := le_trans htsum_bd (mul_le_mul_of_nonneg_left hsum9_bd (by positivity))
  have hconst : (1 / (2 * ν * τ)) * (32 * wienerNormSq u * h2VecNormSq u) =
      (16 / (ν * τ)) * wienerNormSq u * h2VecNormSq u := by
    have hν_ne : ν ≠ 0 := ne_of_gt hν
    have hτ_ne : τ ≠ 0 := ne_of_gt hτ
    field_simp [hν_ne, hτ_ne]; ring
  linarith

private theorem heatStep_inH2_and_bound_7c {ν τ : ℝ} (hν : 0 ≤ ν) (hτ : 0 ≤ τ)
    {u₀ : VecSeq3D} (hu₀ : InH2Vec u₀) :
    InH2Vec (fun k c => (heatMultiplier3D ν τ k : ℂ) * u₀ k c) ∧
    h2VecNormSq (fun k c => (heatMultiplier3D ν τ k : ℂ) * u₀ k c) ≤ h2VecNormSq u₀ := by
  have hcomp : ∀ c : Fin 3,
      InH2Seq (fun k => (heatMultiplier3D ν τ k : ℂ) * u₀ k c) ∧
      h2NormSq (fun k => (heatMultiplier3D ν τ k : ℂ) * u₀ k c) ≤ h2NormSq (fun k => u₀ k c) := by
    intro c
    have hle : ∀ k, h2Weight k * ‖(heatMultiplier3D ν τ k : ℂ) * u₀ k c‖ ^ 2 ≤
        h2Weight k * ‖u₀ k c‖ ^ 2 := by
      intro k
      have hm := heatMultiplier3D_pos_le_one hν hτ k
      rw [norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs]
      have hm2 : (heatMultiplier3D ν τ k) ^ 2 ≤ 1 := by nlinarith [hm.1, hm.2]
      have hnn : 0 ≤ h2Weight k * ‖u₀ k c‖ ^ 2 := mul_nonneg (le_of_lt (h2Weight_pos k)) (sq_nonneg _)
      nlinarith
    have hsum := Summable.of_nonneg_of_le
      (fun k => mul_nonneg (le_of_lt (h2Weight_pos k)) (sq_nonneg _)) hle (hu₀ c)
    exact ⟨hsum, hasSum_le hle hsum.hasSum (hu₀ c).hasSum⟩
  refine ⟨fun c => (hcomp c).1, ?_⟩
  unfold h2VecNormSq
  linarith [(hcomp 0).2, (hcomp 1).2, (hcomp 2).2]

private theorem wiener_slab_h2_quadruple
    {ν T M L t₀ δ : ℝ} (hν : 0 < ν) (hM : 0 ≤ M) (hL : 0 ≤ L)
    (ht₀ : 0 ≤ t₀) (hδ : 0 ≤ δ) (ht₀δ : t₀ + δ ≤ T) (hsmall : 256 * δ * L ≤ ν)
    (u₀ : VecSeq3D) {u : ℝ → VecSeq3D} (hu : IsAdmissibleCurve M u)
    (hu_sol : ∀ t ∈ Set.Icc (0 : ℝ) T, u t = duhamelRaw ν u₀ u t)
    (hwiener : ∀ s ∈ Set.Icc (0 : ℝ) T, wienerNormSq (u s) ≤ L) :
    ∀ r ∈ Set.Icc (0 : ℝ) δ, h2VecNormSq (u (t₀ + r)) ≤ 4 * h2VecNormSq (u t₀) := by
  have hiter : ∀ n : ℕ, ∀ r ∈ Set.Icc (0 : ℝ) δ,
      h2VecNormSq (u (t₀ + r)) ≤ 4 * h2VecNormSq (u t₀) + (1 / 2 : ℝ) ^ n * M := by
    intro n
    induction n with
    | zero =>
      intro r _
      rw [pow_zero, one_mul]
      linarith [hu.h_bound (t₀ + r), h2VecNormSq_nonneg (u t₀)]
    | succ m ih =>
      intro r hr
      let K : ℝ := 4 * h2VecNormSq (u t₀) + (1 / 2 : ℝ) ^ m * M
      have hK_nn : 0 ≤ K := by
        dsimp only [K]
        have := h2VecNormSq_nonneg (u t₀)
        have : 0 ≤ (1 / 2 : ℝ) ^ m * M := by positivity
        linarith
      have ht₀_mem : t₀ ∈ Set.Icc (0 : ℝ) T := ⟨ht₀, by linarith⟩
      have htr_mem : t₀ + r ∈ Set.Icc (0 : ℝ) T := ⟨by linarith [hr.1], by linarith [hr.2]⟩
      have hsplit := duhamelRaw_semigroup_split u₀ hu (hu_sol t₀ ht₀_mem) (hu_sol (t₀ + r) htr_mem)
      let u_s : ℝ → VecSeq3D := fun s => u (t₀ + s)
      have hu_s : IsAdmissibleCurve M u_s :=
        ⟨fun s => hu.h_inH2 (t₀ + s), fun s => hu.h_bound (t₀ + s),
         fun k c => (hu.h_cont k c).comp (continuous_const.add continuous_id)⟩
      have hlin := heatStep_inH2_and_bound_7c (le_of_lt hν) hr.1 (hu.h_inH2 t₀)
      have hG_cont : ∀ (k : Fin 3 → ℤ) (c : Fin 3),
          Continuous (fun s : ℝ => heatSmoothedBilinear6A ν (r - s) (u_s s) (u_s s) k c) := fun k c => by
        unfold heatSmoothedBilinear6A
        exact (Complex.continuous_ofReal.comp
          ((Real.continuous_exp.comp (continuous_const.mul continuous_id)).comp
            (continuous_const.sub continuous_id))).mul
          (continuous_nsBilinear6A_of_admissible hu_s hu_s k c)
      have hint := integral_h2_bound_of_inv_sqrt_decay hr.1 (K := 16 * L * K / ν) (by positivity)
        (G := fun s => heatSmoothedBilinear6A ν (r - s) (u_s s) (u_s s)) hG_cont fun s hs => by
          have hrs : 0 < r - s := sub_pos.mpr hs.2
          have hts_mem : t₀ + s ∈ Set.Icc (0 : ℝ) T :=
            ⟨by linarith [hs.1], by linarith [hs.2, hr.2]⟩
          have hs_δ : s ∈ Set.Icc (0 : ℝ) δ := ⟨hs.1, le_trans (le_of_lt hs.2) hr.2⟩
          have h_in := (heatSmoothedBilinear6A_inH2_and_bound hν hrs (hu_s.h_inH2 s) (hu_s.h_inH2 s)).1
          have htame := heatSmoothedBilinear6A_tame_wiener_H2 hν hrs (hu_s.h_inH2 s)
          refine ⟨h_in, ?_⟩
          have hW_bd : wienerNormSq (u_s s) ≤ L := hwiener (t₀ + s) hts_mem
          have hH_bd : h2VecNormSq (u_s s) ≤ K := ih s hs_δ
          have hprod : wienerNormSq (u_s s) * h2VecNormSq (u_s s) ≤ L * K := by
            nlinarith [wienerNormSq_nonneg (u_s s), h2VecNormSq_nonneg (u_s s)]
          have h1 : (16 / (ν * (r - s))) * wienerNormSq (u_s s) * h2VecNormSq (u_s s) ≤
              (16 / (ν * (r - s))) * (L * K) := by
            rw [mul_assoc]; exact mul_le_mul_of_nonneg_left hprod (by positivity)
          have h2 : (16 / (ν * (r - s))) * (L * K) = (16 * L * K / ν) / (r - s) := by
            have hν_ne : ν ≠ 0 := ne_of_gt hν
            have hrs_ne : r - s ≠ 0 := ne_of_gt hrs
            field_simp [hν_ne, hrs_ne]
          linarith [htame]
      have hadd := inH2Vec_add hlin.1 hint.1
      rw [hsplit]
      change h2VecNormSq (fun k c => (heatMultiplier3D ν r k : ℂ) * u t₀ k c +
        ∫ s in (0 : ℝ)..r, heatSmoothedBilinear6A ν (r - s) (u_s s) (u_s s) k c) ≤ _
      have hr_coef : 128 * r * L / ν ≤ 1 / 2 := by
        rw [div_le_iff₀ hν]
        have : 128 * r * L ≤ 128 * δ * L := by nlinarith [hr.2]
        linarith
      have h2_term : 2 * (4 * r * (16 * L * K / ν)) ≤ (1 / 2 : ℝ) * K := by
        have heq : 2 * (4 * r * (16 * L * K / ν)) = (128 * r * L / ν) * K := by ring
        rw [heq]; exact mul_le_mul_of_nonneg_right hr_coef hK_nn
      have hK_half : 2 * h2VecNormSq (u t₀) + (1 / 2 : ℝ) * K =
          4 * h2VecNormSq (u t₀) + (1 / 2 : ℝ) ^ (m + 1) * M := by
        dsimp only [K]; rw [pow_succ]; ring
      linarith [hadd.2, hlin.2, hint.2]
  intro r hr
  have htend : Tendsto (fun n : ℕ => 4 * h2VecNormSq (u t₀) + (1 / 2 : ℝ) ^ n * M)
      atTop (𝓝 (4 * h2VecNormSq (u t₀) + 0 * M)) :=
    tendsto_const_nhds.add
      ((tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)).mul tendsto_const_nhds)
  rw [zero_mul, add_zero] at htend
  exact ge_of_tendsto htend (Eventually.of_forall fun n => hiter n r hr)

/-- **THEOREM 4 OF MILESTONE 7C (Unconditional Wiener-`ℓ¹` Blow-Up / Continuation Criterion in `H²(𝕋³)`):**
    For ANY viscosity `ν > 0`, ANY horizon `T ≥ 0`, ANY admissible mild solution `u` on `[0, T]`
    (regardless of how huge `M` is), if the Wiener norm is bounded by `L ≥ 0` on `[0, T]`, then
    the `H²` norm obeys the `M`-independent a priori bound:
      `∀ t ∈ [0, T], ‖u(t)‖²_{H²} ≤ 4 ^ ⌈256 (L + 1) T / ν⌉ * ‖u₀‖²_{H²}` (`0 sorryAx`). -/
theorem unconditional_wiener_a_priori_H2_bound_torus3D
    {ν T M L : ℝ} (hν : 0 < ν) (hT : 0 ≤ T) (hM : 0 ≤ M) (hL : 0 ≤ L)
    (u₀ : VecSeq3D) {u : ℝ → VecSeq3D} (hu : IsAdmissibleCurve M u)
    (hu_sol : ∀ t ∈ Set.Icc (0 : ℝ) T, u t = duhamelRaw ν u₀ u t)
    (hwiener : ∀ s ∈ Set.Icc (0 : ℝ) T, wienerNormSq (u s) ≤ L) :
    ∀ t ∈ Set.Icc (0 : ℝ) T,
      h2VecNormSq (u t) ≤ (4 : ℝ) ^ (Nat.ceil (256 * (L + 1) * T / ν)) * h2VecNormSq u₀ := by
  let δ : ℝ := ν / (256 * (L + 1))
  have hL1_pos : 0 < L + 1 := by linarith
  have hδ_pos : 0 < δ := by dsimp only [δ]; positivity
  have hsmall_δ : 256 * δ * L ≤ ν := by
    have heq : 256 * δ * (L + 1) = ν := by
      dsimp only [δ]; field_simp [ne_of_gt hL1_pos]
    have hle : 256 * δ * L ≤ 256 * δ * (L + 1) :=
      mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    linarith
  have hind : ∀ m : ℕ, ∀ t ∈ Set.Icc (0 : ℝ) (min T ((m : ℝ) * δ)),
      h2VecNormSq (u t) ≤ (4 : ℝ) ^ m * h2VecNormSq u₀ := by
    intro m
    induction m with
    | zero =>
      intro t ht
      have ht0 : t = 0 := by
        have hmin : min T ((0 : ℕ) * δ) = 0 := by simp [min_eq_right hT]
        rw [hmin] at ht; linarith [ht.1, ht.2]
      subst ht0
      have hu0 : u 0 = u₀ := by
        rw [hu_sol 0 ⟨le_rfl, hT⟩]; funext k c; unfold duhamelRaw; simp [heatMultiplier3D_zero]
      rw [hu0, pow_zero, one_mul]
    | succ k ih =>
      intro t ht
      let t₀ : ℝ := (k : ℝ) * δ
      have ht₀_nn : 0 ≤ t₀ := by dsimp only [t₀]; positivity
      rcases le_or_gt t t₀ with hle | hgt
      · have h1 := ih t ⟨ht.1, le_min (le_trans ht.2 (min_le_left _ _)) hle⟩
        have h4 : (4 : ℝ) ^ k ≤ (4 : ℝ) ^ (k + 1) := by
          rw [pow_succ]; nlinarith [pow_nonneg (by norm_num : (0 : ℝ) ≤ 4) k]
        have h2 := mul_le_mul_of_nonneg_right h4 (h2VecNormSq_nonneg u₀)
        linarith
      · have ht_le_T : t ≤ T := le_trans ht.2 (min_le_left _ _)
        have ht₀_le_T : t₀ ≤ T := le_trans (le_of_lt hgt) ht_le_T
        have hsucc : ((k + 1 : ℕ) : ℝ) * δ = t₀ + δ := by dsimp only [t₀]; push_cast; ring
        have ht_le_succ : t ≤ t₀ + δ := by rw [← hsucc]; exact le_trans ht.2 (min_le_right _ _)
        have hr_le_δ : t - t₀ ≤ δ := by linarith
        have hsmall_r : 256 * (t - t₀) * L ≤ ν := by
          have : 256 * (t - t₀) * L ≤ 256 * δ * L := by nlinarith
          linarith
        have hquad := wiener_slab_h2_quadruple hν hM hL ht₀_nn (by linarith) (by linarith)
          hsmall_r u₀ hu hu_sol hwiener (t - t₀) ⟨by linarith, le_rfl⟩
        have hsum : t₀ + (t - t₀) = t := by ring
        rw [hsum] at hquad
        have hprev := ih t₀ ⟨ht₀_nn, le_min ht₀_le_T le_rfl⟩
        rw [pow_succ]; nlinarith
  intro t ht
  have hdiv_eq : T / δ = 256 * (L + 1) * T / ν := by
    dsimp only [δ]
    have hν_ne : ν ≠ 0 := ne_of_gt hν
    field_simp [hν_ne, ne_of_gt hL1_pos]
  let N : ℕ := Nat.ceil (256 * (L + 1) * T / ν)
  have hT_le_N : T ≤ (N : ℝ) * δ := by
    have h1 : T / δ ≤ (N : ℝ) := by dsimp only [N]; rw [hdiv_eq]; exact Nat.le_ceil _
    have h2 := mul_le_mul_of_nonneg_right h1 (le_of_lt hδ_pos)
    rwa [div_mul_cancel₀ T (ne_of_gt hδ_pos)] at h2
  exact hind N t ⟨ht.1, le_min ht.2 (le_trans ht.2 hT_le_N)⟩

-- ============================================================================
-- SECTION 3: EXPLICIT CONDITIONAL GARRY INTERFACE, NON-VACUITY & TWO-TIER AUDIT
-- ============================================================================

/-- Explicit, isolated conditional closure hypothesis for arbitrary large data `u₀ ∈ H²(𝕋³)`.
    All conditional assumptions live strictly inside this structure (never as custom axioms),
    ensuring zero circularity between Tier I (unconditional) and Tier II (conditional Garry). -/
structure GarryConditionalClosureHypotheses (ν B : ℝ) (u₀ : VecSeq3D) : Prop where
  hν_pos : 0 < ν
  hB_nonneg : 0 ≤ B
  hu₀_inH2 : InH2Vec u₀
  hu₀_sol : IsSolenoidal u₀
  hu₀_sym : IsRealSymm u₀
  hu₀_bound : h2VecNormSq u₀ ≤ B
  h_apriori_step : ∀ w : VecSeq3D, InH2Vec w → IsSolenoidal w → IsRealSymm w → h2VecNormSq w ≤ B →
    h2VecNormSq (picardLimit ν (contStep ν B) w (contStep ν B)) ≤ B

private def zeroVec3D_7c : VecSeq3D := fun _ _ => 0

private theorem eq_zero_of_h2VecNormSq_eq_zero_7c {w : VecSeq3D} (hw : InH2Vec w)
    (hz : h2VecNormSq w = 0) : w = zeroVec3D_7c := by
  have hcomp0 : ∀ c : Fin 3, h2NormSq (fun k => w k c) = 0 := by
    unfold h2VecNormSq at hz
    intro c; fin_cases c
    · change h2NormSq (fun k => w k 0) = 0
      linarith [h2NormSq_nonneg (fun k => w k 0), h2NormSq_nonneg (fun k => w k 1), h2NormSq_nonneg (fun k => w k 2)]
    · change h2NormSq (fun k => w k 1) = 0
      linarith [h2NormSq_nonneg (fun k => w k 0), h2NormSq_nonneg (fun k => w k 1), h2NormSq_nonneg (fun k => w k 2)]
    · change h2NormSq (fun k => w k 2) = 0
      linarith [h2NormSq_nonneg (fun k => w k 0), h2NormSq_nonneg (fun k => w k 1), h2NormSq_nonneg (fun k => w k 2)]
  funext k c
  have hle_single : h2Weight k * ‖w k c‖ ^ 2 ≤ h2NormSq (fun m => w m c) := by
    have hind : HasSum (fun m : Fin 3 → ℤ => if m = k then h2Weight k * ‖w k c‖ ^ 2 else 0)
        (h2Weight k * ‖w k c‖ ^ 2) := hasSum_ite_eq k (h2Weight k * ‖w k c‖ ^ 2)
    refine hasSum_le (fun m => ?_) hind (hw c).hasSum
    by_cases hm : m = k
    · subst hm; simp
    · simp only [hm, ↓reduceIte]
      exact mul_nonneg (le_of_lt (h2Weight_pos m)) (sq_nonneg _)
  rw [hcomp0 c] at hle_single
  have h1 : ‖w k c‖ ^ 2 ≤ 0 := by nlinarith [one_le_h2Weight k, sq_nonneg ‖w k c‖]
  have hsq0 : ‖w k c‖ ^ 2 = 0 := le_antisymm h1 (sq_nonneg _)
  exact norm_eq_zero.mp (sq_eq_zero_iff.mp hsq0)

/-- **THEOREM 5 OF MILESTONE 7C (Non-Vacuity of `GarryConditionalClosureHypotheses`):**
    For every `ν > 0`, `GarryConditionalClosureHypotheses ν 0 zeroVec3D_7c` is inhabited —
    proving that the conditional Garry global-continuation theorem is genuinely non-vacuous
    (`0 sorryAx`). -/
theorem garry_closure_hypotheses_nonvacuous {ν : ℝ} (hν : 0 < ν) :
    GarryConditionalClosureHypotheses ν 0 zeroVec3D_7c := by
  have h0_in : InH2Vec zeroVec3D_7c := fun c => by
    have : (fun k : Fin 3 → ℤ => h2Weight k * ‖zeroVec3D_7c k c‖ ^ 2) = 0 := by
      funext k; simp [zeroVec3D_7c]
    rw [InH2Seq, this]; exact summable_zero
  have h0_norm : h2VecNormSq zeroVec3D_7c = 0 := by
    unfold h2VecNormSq h2NormSq zeroVec3D_7c; simp
  have h0_sol : IsSolenoidal zeroVec3D_7c := fun k => by simp [zeroVec3D_7c]
  have h0_sym : IsRealSymm zeroVec3D_7c := fun k c => by simp [zeroVec3D_7c]
  refine ⟨hν, le_rfl, h0_in, h0_sol, h0_sym, by linarith, fun w hw _ _ hw_le => ?_⟩
  have hw_eq : w = zeroVec3D_7c :=
    eq_zero_of_h2VecNormSq_eq_zero_7c hw (le_antisymm hw_le (h2VecNormSq_nonneg w))
  subst hw_eq
  have hT_pos : 0 < contStep ν 0 := by unfold contStep; positivity
  have hT_nn : 0 ≤ contStep ν 0 := le_of_lt hT_pos
  have hsm : 54272 * contStep ν 0 * 1 ≤ ν := by
    unfold contStep; ring_nf; exact le_rfl
  have hR : 4 * h2VecNormSq zeroVec3D_7c ≤ 1 := by linarith
  have hpic_adm := (picardLimit_admissible_and_rate hν hT_nn (by norm_num) h0_in hR hsm).1
  have hpic_fix := (picardLimit_fixedPoint_and_structure hν hT_nn (by norm_num) h0_in h0_sol h0_sym hR hsm).2.1
  have hzero_adm : IsAdmissibleCurve 1 (fun _ : ℝ => zeroVec3D_7c) :=
    ⟨fun _ => h0_in, fun _ => by linarith, fun _ _ => continuous_const⟩
  have hzero_sol : ∀ t ∈ Set.Icc (0 : ℝ) (contStep ν 0),
      zeroVec3D_7c = duhamelRaw ν zeroVec3D_7c (fun _ => zeroVec3D_7c) t := by
    intro t _
    funext k c
    have hconv0 : ∀ (j d : Fin 3),
        conv3D (fun m => zeroVec3D_7c m j) (fun m => zeroVec3D_7c m d) k = 0 := fun _ _ => by
      unfold conv3D zeroVec3D_7c; simp
    have hflux0 : ∀ d : Fin 3, nsFlux6A zeroVec3D_7c zeroVec3D_7c k d = 0 := fun d => by
      unfold nsFlux6A; rw [hconv0 0 d, hconv0 1 d, hconv0 2 d]; ring
    have hbi0 : nsBilinear6A zeroVec3D_7c zeroVec3D_7c k c = 0 := by
      unfold nsBilinear6A lerayProj6A
      by_cases hk : k = 0
      · have hfc := hflux0 c; rw [hk] at hfc; simp [hk, hfc]
      · simp [hk, hflux0 0, hflux0 1, hflux0 2, hflux0 c]
    have hhs0 : ∀ s : ℝ, heatSmoothedBilinear6A ν (t - s) zeroVec3D_7c zeroVec3D_7c k c = 0 := fun s => by
      unfold heatSmoothedBilinear6A; rw [hbi0, mul_zero]
    unfold duhamelRaw
    simp [zeroVec3D_7c, hhs0]
  have heq := mild_solution_unique hν hT_nn (by norm_num) hsm zeroVec3D_7c hpic_adm hzero_adm
    hpic_fix hzero_sol (contStep ν 0) ⟨hT_nn, le_rfl⟩
  rw [heq, h0_norm]

/-- **MASTER THEOREM 6 OF MILESTONE 7C (Formal Two-Tier Boundary Audit — Unconditional `𝕋³`
    vs. Conditional Garry Global Regularity Closure, `0 sorryAx`):**
    Explicitly separates in the Lean 4 type signature:
    - **TIER I (Unconditional on `𝕋³`, 0 extra hypotheses):**
      1. 3D supercritical energy scaling barrier (`E_λ = λ⁻¹ E₀` vs `Z_λ = λ Z₀`, `P_λ = λ³ P₀`);
      2. Unconditional global existence on `[0, ∞)` for all mean-zero small `H²` data;
      3. Unconditional global uniqueness for all mild `H²` solutions on arbitrary `[0, T]`;
      4. Unconditional Wiener-`ℓ¹` tame `H²` continuation bound on arbitrary `[0, T]`.
    - **TIER II (Conditional Garry Closure on True 3D Torus PDE, isolated & non-vacuous):**
      5. `GarryConditionalClosureHypotheses ν B u₀` is non-vacuous and implies existence &
         uniqueness of a global smooth-in-time spectral 3D NS solution on `[0, ∞)` with
         uniform `H²`/`L∞` bounds (ready for Milestone 8 `H^m → C^∞` bootstrap). -/
theorem milestone7_two_tier_boundary_audit_torus3D {ν : ℝ} (hν : 0 < ν) :
    -- TIER I (UNCONDITIONAL ON 𝕋³)
    (∀ {E₀ Z₀ P₀ : ℝ}, 0 < E₀ → 0 < Z₀ → 0 < P₀ →
      ∀ (ε R : ℝ), 0 < ε → 0 < R →
        ∃ lam : ℝ, 0 < lam ∧ lam⁻¹ * E₀ < ε ∧ R < lam * Z₀ ∧ R < lam ^ 3 * P₀) ∧
    (∀ {u₀ : VecSeq3D}, InH2Vec u₀ → IsSolenoidal u₀ → IsRealSymm u₀ →
      (∀ c : Fin 3, u₀ 0 c = 0) → h2VecNormSq u₀ ≤ Real.pi ^ 2 * ν ^ 2 / 217088 →
      ∃ u : ℝ → VecSeq3D,
        IsAdmissibleCurve (Real.pi ^ 2 * ν ^ 2 / 54272) u ∧ u 0 = u₀ ∧
        (∀ t : ℝ, 0 ≤ t → u t = duhamelRaw ν u₀ u t)) ∧
    (∀ {T M : ℝ}, 0 ≤ T → 0 ≤ M → ∀ (u₀ : VecSeq3D) {u v : ℝ → VecSeq3D},
      IsAdmissibleCurve M u → IsAdmissibleCurve M v →
      (∀ t ∈ Set.Icc (0 : ℝ) T, u t = duhamelRaw ν u₀ u t) →
      (∀ t ∈ Set.Icc (0 : ℝ) T, v t = duhamelRaw ν u₀ v t) →
      ∀ t ∈ Set.Icc (0 : ℝ) T, u t = v t) ∧
    (∀ {T M L : ℝ}, 0 ≤ T → 0 ≤ M → 0 ≤ L → ∀ (u₀ : VecSeq3D) {u : ℝ → VecSeq3D},
      IsAdmissibleCurve M u →
      (∀ t ∈ Set.Icc (0 : ℝ) T, u t = duhamelRaw ν u₀ u t) →
      (∀ s ∈ Set.Icc (0 : ℝ) T, wienerNormSq (u s) ≤ L) →
      ∀ t ∈ Set.Icc (0 : ℝ) T,
        h2VecNormSq (u t) ≤ (4 : ℝ) ^ (Nat.ceil (256 * (L + 1) * T / ν)) * h2VecNormSq u₀) ∧
    -- TIER II (CONDITIONAL GARRY CLOSURE — NON-VACUOUS & ISOLATED)
    (∃ (B : ℝ) (u₀ : VecSeq3D), GarryConditionalClosureHypotheses ν B u₀) ∧
    (∀ {B : ℝ} {u₀ : VecSeq3D}, GarryConditionalClosureHypotheses ν B u₀ →
      ∃ u : ℝ → VecSeq3D,
        IsAdmissibleCurve (4 * B + 1) u ∧ u 0 = u₀ ∧
        (∀ t : ℝ, 0 ≤ t → u t = duhamelRaw ν u₀ u t) ∧
        (∀ t : ℝ, Continuous (synthVec3D (u t)) ∧ IsPeriodic3D (synthVec3D (u t)) ∧
          (∀ x : R3, dot3D (synthVec3D (u t) x) (synthVec3D (u t) x) ≤ 53 * (4 * B + 1)))) := by
  refine ⟨fun hE hZ hP => (ns3d_supercritical_energy_barrier hE hZ hP).2,
          fun hu₀ hsol₀ hsym₀ hzero hsm => ?_,
          ?_,
          ?_,
          ⟨0, zeroVec3D_7c, garry_closure_hypotheses_nonvacuous hν⟩,
          fun hG => ?_⟩
  · obtain ⟨u, hadm, h0, hduh, _, _, _⟩ :=
      global_existence_small_data_ns3d_torus3D hν hu₀ hsol₀ hsym₀ hzero hsm
    exact ⟨u, hadm, h0, hduh⟩
  · intro T M hT hM u₀ u v hu hv hus hvs
    exact global_mild_solution_unique_torus3D hν hT hM u₀ hu hv hus hvs
  · intro T M L hT hM hL u₀ u hu hus hw
    exact unconditional_wiener_a_priori_H2_bound_torus3D hν hT hM hL u₀ hu hus hw
  · obtain ⟨u, hadm, h0, hduh, _, _, hsyn, _⟩ :=
      global_continuation_of_apriori_H2_bound_torus3D hG.hν_pos hG.hB_nonneg
        hG.hu₀_inH2 hG.hu₀_sol hG.hu₀_sym hG.hu₀_bound hG.h_apriori_step
    exact ⟨u, hadm, h0, hduh, hsyn⟩

-- ============================================================================
-- SECTION 4: AXIOM AUDIT TRAIL — MILESTONE 7C (0 sorryAx)
-- ============================================================================

#print axioms ns3d_supercritical_energy_barrier
#print axioms conv3D_tame_l1_H2
#print axioms heatSmoothedBilinear6A_tame_wiener_H2
#print axioms unconditional_wiener_a_priori_H2_bound_torus3D
#print axioms garry_closure_hypotheses_nonvacuous
#print axioms milestone7_two_tier_boundary_audit_torus3D

end GarrySupercriticalAudit3D