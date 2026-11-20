import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Abel
import SobolevEmbeddingTorus3D

/-!
# GARRYULT v4.0.0 — Milestone 6A (Stage 1): Discrete 3D Sobolev Algebra `H²(𝕋³)`
# Weight `1 + |k|⁴`, Embedding `ℓ²₂ ↪ ℓ¹` (`C = 53`), Discrete Young Inequality
# (`ℓ¹ * ℓ² → ℓ²`), 3D Convolution Banach Algebra (`C = 1696`) & Quadratic Lipschitz Bound
-/

namespace GarrySpectralAlgebra3D

open MeasureTheory Filter Topology GarryReal3DCalculus GarryVorticity3D
  GarryLerayTorus3D GarryLerayEnergyLaw3D GarryPoincareSobolev3D
  GarryFourierSpectral3D GarrySpectralOperators3D GarryParsevalSobolev3D
  GarrySobolevEmbedding3D

-- ============================================================================
-- SECTION 1: DISCRETE H²(𝕋³) WEIGHT & SUMMABILITY HELPERS
-- ============================================================================

/-- Discrete `H²(𝕋³)` spectral weight `w(k) = 1 + |k|⁴ ≥ 1`. -/
noncomputable def h2Weight (k : Fin 3 → ℤ) : ℝ :=
  1 + (kNormSq k) ^ 2

/-- Membership in the discrete Sobolev space `H²(𝕋³)` (complex scalar sequences). -/
def InH2Seq (a : (Fin 3 → ℤ) → ℂ) : Prop :=
  Summable (fun k : Fin 3 → ℤ => h2Weight k * ‖a k‖ ^ 2)

/-- Squared `H²(𝕋³)` norm `∑' k, (1 + |k|⁴) ‖a(k)‖²`. -/
noncomputable def h2NormSq (a : (Fin 3 → ℤ) → ℂ) : ℝ :=
  ∑' k : Fin 3 → ℤ, h2Weight k * ‖a k‖ ^ 2

private theorem kNormSq_zero_6a : kNormSq 0 = 0 := by
  unfold kNormSq; simp

private theorem kNormSq_nonneg_6a (k : Fin 3 → ℤ) : 0 ≤ kNormSq k := by
  unfold kNormSq; positivity

theorem one_le_h2Weight (k : Fin 3 → ℤ) : 1 ≤ h2Weight k := by
  unfold h2Weight
  have : 0 ≤ (kNormSq k) ^ 2 := sq_nonneg _
  linarith

theorem h2Weight_pos (k : Fin 3 → ℤ) : 0 < h2Weight k :=
  lt_of_lt_of_le zero_lt_one (one_le_h2Weight k)

theorem h2NormSq_nonneg (a : (Fin 3 → ℤ) → ℂ) : 0 ≤ h2NormSq a :=
  tsum_nonneg fun k => mul_nonneg (le_of_lt (h2Weight_pos k)) (sq_nonneg _)

private theorem kNormSq_add_le (j m : Fin 3 → ℤ) :
    kNormSq (j + m) ≤ 2 * (kNormSq j + kNormSq m) := by
  unfold kNormSq
  simp only [Pi.add_apply, Int.cast_add]
  nlinarith [sq_nonneg ((j 0 : ℝ) - (m 0 : ℝ)),
             sq_nonneg ((j 1 : ℝ) - (m 1 : ℝ)),
             sq_nonneg ((j 2 : ℝ) - (m 2 : ℝ))]

/-- **Sub-additivity of `H²` Weight:** `1 + |j + m|⁴ ≤ 8 ((1 + |j|⁴) + (1 + |m|⁴))`. -/
theorem h2Weight_add_le (j m : Fin 3 → ℤ) :
    h2Weight (j + m) ≤ 8 * (h2Weight j + h2Weight m) := by
  have h1 : kNormSq (j + m) ≤ 2 * (kNormSq j + kNormSq m) := kNormSq_add_le j m
  have hnn : 0 ≤ kNormSq (j + m) := kNormSq_nonneg_6a (j + m)
  have hnj : 0 ≤ kNormSq j := kNormSq_nonneg_6a j
  have hnm : 0 ≤ kNormSq m := kNormSq_nonneg_6a m
  have hsq : (kNormSq (j + m)) ^ 2 ≤ 4 * (kNormSq j + kNormSq m) ^ 2 := by nlinarith
  have h4 : (kNormSq (j + m)) ^ 2 ≤ 8 * ((kNormSq j) ^ 2 + (kNormSq m) ^ 2) := by
    nlinarith [sq_nonneg (kNormSq j - kNormSq m)]
  unfold h2Weight
  linarith

theorem sqrt_h2Weight_add_le (j m : Fin 3 → ℤ) :
    Real.sqrt (h2Weight (j + m)) ≤
      Real.sqrt 8 * (Real.sqrt (h2Weight j) + Real.sqrt (h2Weight m)) := by
  have hj : 0 ≤ h2Weight j := le_of_lt (h2Weight_pos j)
  have hm : 0 ≤ h2Weight m := le_of_lt (h2Weight_pos m)
  have hsum_nn : 0 ≤ Real.sqrt 8 * (Real.sqrt (h2Weight j) + Real.sqrt (h2Weight m)) := by positivity
  have hsq_le : h2Weight (j + m) ≤
      (Real.sqrt 8 * (Real.sqrt (h2Weight j) + Real.sqrt (h2Weight m))) ^ 2 := by
    have h8 : Real.sqrt 8 ^ 2 = 8 := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 8)
    have hsqj : Real.sqrt (h2Weight j) ^ 2 = h2Weight j := Real.sq_sqrt hj
    have hsqm : Real.sqrt (h2Weight m) ^ 2 = h2Weight m := Real.sq_sqrt hm
    have hcross : 0 ≤ Real.sqrt (h2Weight j) * Real.sqrt (h2Weight m) := by positivity
    have hadd := h2Weight_add_le j m
    have hexp : (Real.sqrt 8 * (Real.sqrt (h2Weight j) + Real.sqrt (h2Weight m))) ^ 2 =
        8 * (h2Weight j + h2Weight m + 2 * (Real.sqrt (h2Weight j) * Real.sqrt (h2Weight m))) := by
      rw [mul_pow, h8]; nlinarith [hsqj, hsqm]
    linarith
  calc Real.sqrt (h2Weight (j + m))
      ≤ Real.sqrt ((Real.sqrt 8 * (Real.sqrt (h2Weight j) + Real.sqrt (h2Weight m))) ^ 2) :=
        Real.sqrt_le_sqrt hsq_le
    _ = Real.sqrt 8 * (Real.sqrt (h2Weight j) + Real.sqrt (h2Weight m)) :=
        Real.sqrt_sq hsum_nn

private def subLeftEquiv (k : Fin 3 → ℤ) : (Fin 3 → ℤ) ≃ (Fin 3 → ℤ) where
  toFun j := k - j
  invFun j := k - j
  left_inv j := sub_sub_cancel k j
  right_inv j := sub_sub_cancel k j

private theorem summable_sub_left {f : (Fin 3 → ℤ) → ℝ} (hf : Summable f) (k : Fin 3 → ℤ) :
    Summable (fun j => f (k - j)) :=
  ((subLeftEquiv k).hasSum_iff.mpr hf.hasSum).summable

private theorem tsum_sub_left {f : (Fin 3 → ℤ) → ℝ} (hf : Summable f) (k : Fin 3 → ℤ) :
    (∑' j : Fin 3 → ℤ, f (k - j)) = ∑' m : Fin 3 → ℤ, f m :=
  ((subLeftEquiv k).hasSum_iff.mpr hf.hasSum).tsum_eq

private theorem finset_sum_le_tsum {f : (Fin 3 → ℤ) → ℝ}
    (hf : Summable f) (hf_nn : ∀ k, 0 ≤ f k) (s : Finset (Fin 3 → ℤ)) :
    ∑ k ∈ s, f k ≤ ∑' k, f k := by
  have hind : HasSum (fun k => if k ∈ s then f k else 0) (∑ k ∈ s, f k) := by
    refine tendsto_atTop_of_eventually_const (i₀ := s) fun t ht => ?_
    rw [← Finset.sum_filter, Finset.filter_mem_eq_inter, Finset.inter_eq_right.mpr ht]
  exact hasSum_le (fun k => by split_ifs; exact le_refl _; exact hf_nn k) hind hf.hasSum

private theorem le_tsum_single {f : (Fin 3 → ℤ) → ℝ}
    (hf : Summable f) (hf_nn : ∀ k, 0 ≤ f k) (k₀ : Fin 3 → ℤ) :
    f k₀ ≤ ∑' k, f k := by
  simpa using finset_sum_le_tsum hf hf_nn {k₀}

private theorem summable_finset_sum {α : Type*} [DecidableEq α] (s : Finset α)
    (F : α → (Fin 3 → ℤ) → ℝ) (hF : ∀ k ∈ s, Summable (F k)) :
    Summable (fun j : Fin 3 → ℤ => ∑ k ∈ s, F k j) := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a t hat ih =>
    have heq : (fun j => ∑ k ∈ insert a t, F k j) = (fun j => F a j + ∑ k ∈ t, F k j) :=
      funext fun j => Finset.sum_insert hat
    rw [heq]
    exact (hF a (Finset.mem_insert_self a t)).add
      (ih fun k hk => hF k (Finset.mem_insert_of_mem hk))

private theorem finset_sum_tsum {α : Type*} [DecidableEq α] (s : Finset α)
    (F : α → (Fin 3 → ℤ) → ℝ) (hF : ∀ k ∈ s, Summable (F k)) :
    (∑ k ∈ s, ∑' j : Fin 3 → ℤ, F k j) = ∑' j : Fin 3 → ℤ, ∑ k ∈ s, F k j := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a t hat ih =>
    have hsum_a : Summable (F a) := hF a (Finset.mem_insert_self a t)
    have hsum_t : Summable (fun j => ∑ k ∈ t, F k j) :=
      summable_finset_sum t F fun k hk => hF k (Finset.mem_insert_of_mem hk)
    have heq : (fun j => ∑ k ∈ insert a t, F k j) = (fun j => F a j + ∑ k ∈ t, F k j) :=
      funext fun j => Finset.sum_insert hat
    rw [Finset.sum_insert hat, heq, hsum_a.tsum_add hsum_t,
        ih fun k hk => hF k (Finset.mem_insert_of_mem hk)]

private theorem tsum_sq_le_mul_of_le {a w b : (Fin 3 → ℤ) → ℝ}
    (ha : Summable a) (hw : Summable w) (hb : Summable b)
    (ha_nn : ∀ k, 0 ≤ a k) (hw_nn : ∀ k, 0 ≤ w k) (hb_nn : ∀ k, 0 ≤ b k)
    (h_pt : ∀ k, (a k) ^ 2 ≤ w k * b k) :
    (∑' k, a k) ^ 2 ≤ (∑' k, w k) * (∑' k, b k) := by
  let A := ∑' k, a k
  let W := ∑' k, w k
  let B := ∑' k, b k
  have hquad : ∀ r : ℝ, 0 ≤ r ^ 2 * W - 2 * r * A + B := by
    intro r
    have hcomb := ((hw.hasSum.mul_left (r ^ 2)).sub (ha.hasSum.mul_left (2 * r))).add hb.hasSum
    have hnn : ∀ k, 0 ≤ r ^ 2 * w k - 2 * r * a k + b k := fun k => by
      have h1 : 0 ≤ (r * Real.sqrt (w k) - Real.sqrt (b k)) ^ 2 := sq_nonneg _
      have hsq_w : Real.sqrt (w k) ^ 2 = w k := Real.sq_sqrt (hw_nn k)
      have hsq_b : Real.sqrt (b k) ^ 2 = b k := Real.sq_sqrt (hb_nn k)
      have hprod : a k ≤ Real.sqrt (w k) * Real.sqrt (b k) := by
        rw [← Real.sqrt_mul (hw_nn k)]; exact Real.le_sqrt_of_sq_le (h_pt k)
      have h2 : (r * Real.sqrt (w k) - Real.sqrt (b k)) ^ 2 =
          r ^ 2 * w k - 2 * r * (Real.sqrt (w k) * Real.sqrt (b k)) + b k := by
        nlinarith [hsq_w, hsq_b]
      by_cases hr : 0 ≤ r
      · nlinarith
      · push Not at hr
        have h3 : 0 ≤ r ^ 2 * w k := mul_nonneg (sq_nonneg _) (hw_nn k)
        have h4 : 0 ≤ -2 * r * a k := by nlinarith [ha_nn k]
        linarith [hb_nn k]
    exact hasSum_le hnn hasSum_zero hcomb
  have hW_nn : 0 ≤ W := tsum_nonneg hw_nn
  change A ^ 2 ≤ W * B
  rcases eq_or_lt_of_le hW_nn with hW0 | hW_pos
  · have hA0 : A = 0 := by
      by_contra hne
      have h1 := hquad ((B + 1) / (2 * A))
      have h2A : 2 * A ≠ 0 := mul_ne_zero (by norm_num) hne
      rw [← hW0, mul_zero, zero_sub] at h1
      have hcalc : 2 * ((B + 1) / (2 * A)) * A = B + 1 := by field_simp [h2A]
      linarith
    rw [hA0, ← hW0]; norm_num
  · have hq := hquad (A / W)
    have hmul : 0 ≤ ((A / W) ^ 2 * W - 2 * (A / W) * A + B) * W := mul_nonneg hq (le_of_lt hW_pos)
    have hW_ne : W ≠ 0 := ne_of_gt hW_pos
    have halg : ((A / W) ^ 2 * W - 2 * (A / W) * A + B) * W = W * B - A ^ 2 := by
      field_simp [hW_ne]; ring
    linarith

-- ============================================================================
-- SECTION 2: `ℓ²₂ ↪ ℓ¹` EMBEDDING & VECTOR SPACE CLOSURE OF `H²(𝕋³)`
-- ============================================================================

/-- **THEOREM 1 OF MILESTONE 6A:** `∑' k : ℤ³, (1 + |k|⁴)⁻¹ ≤ 53` (`0 sorryAx`). -/
theorem summable_and_tsum_inv_h2Weight_le :
    Summable (fun k : Fin 3 → ℤ => (h2Weight k)⁻¹) ∧
    (∑' k : Fin 3 → ℤ, (h2Weight k)⁻¹) ≤ 53 := by
  let dom : (Fin 3 → ℤ) → ℝ := fun k => (if k = 0 then (1 : ℝ) else 0) + invKNormSqSq k
  have h0_sum : Summable (fun k : Fin 3 → ℤ => if k = 0 then (1 : ℝ) else 0) :=
    summable_of_ne_finset_zero (s := {0}) (fun k hk => by
      simp only [Finset.mem_singleton] at hk; simp [hk])
  have hdom_sum : Summable dom := h0_sum.add summable_and_tsum_invKNormSqSq_le.1
  have hle : ∀ k : Fin 3 → ℤ, (h2Weight k)⁻¹ ≤ dom k := fun k => by
    dsimp only [dom]
    by_cases hk : k = 0
    · subst hk; unfold h2Weight invKNormSqSq; simp [kNormSq_zero_6a]
    · unfold h2Weight invKNormSqSq; simp only [hk, ↓reduceIte, zero_add]
      have hk_pos : 0 < kNormSq k := kNormSq_pos_of_ne_zero hk
      rw [inv_pow]
      exact inv_anti₀ (by positivity) (by linarith)
  have hsum : Summable (fun k : Fin 3 → ℤ => (h2Weight k)⁻¹) :=
    Summable.of_nonneg_of_le (fun k => inv_nonneg.mpr (le_of_lt (h2Weight_pos k))) hle hdom_sum
  have htsum : (∑' k, (h2Weight k)⁻¹) ≤ ∑' k, dom k :=
    hasSum_le hle hsum.hasSum hdom_sum.hasSum
  have hdom_val : (∑' k, dom k) = 1 + ∑' k, invKNormSqSq k := by
    dsimp only [dom]; rw [h0_sum.tsum_add summable_and_tsum_invKNormSqSq_le.1, tsum_ite_eq]
  exact ⟨hsum, by linarith [htsum, hdom_val, summable_and_tsum_invKNormSqSq_le.2]⟩

/-- **THEOREM 2 OF MILESTONE 6A (`H²(𝕋³) ↪ ℓ¹(ℤ³)` Embedding):**
    Every sequence `a ∈ H²(𝕋³)` is absolutely summable with `(∑' k, ‖a k‖)² ≤ 53 * ‖a‖²_{H²}` (`0 sorryAx`). -/
theorem h2Seq_l1_embedding {a : (Fin 3 → ℤ) → ℂ} (ha : InH2Seq a) :
    Summable (fun k : Fin 3 → ℤ => ‖a k‖) ∧
    (∑' k : Fin 3 → ℤ, ‖a k‖) ^ 2 ≤ 53 * h2NormSq a := by
  have hinv := summable_and_tsum_inv_h2Weight_le
  have hdom_sum : Summable (fun k => (1 / 2 : ℝ) * (h2Weight k)⁻¹ +
      (1 / 2 : ℝ) * (h2Weight k * ‖a k‖ ^ 2)) :=
    (hinv.1.mul_left (1 / 2 : ℝ)).add (ha.mul_left (1 / 2 : ℝ))
  have hsum_norm : Summable (fun k => ‖a k‖) := by
    refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun k => ?_) hdom_sum
    have hw_pos : 0 < h2Weight k := h2Weight_pos k
    have hsq : 0 ≤ (1 - h2Weight k * ‖a k‖) ^ 2 := sq_nonneg _
    have hmul : 2 * h2Weight k * ‖a k‖ ≤ 1 + (h2Weight k) ^ 2 * ‖a k‖ ^ 2 := by nlinarith
    have hinv_cancel : h2Weight k * (h2Weight k)⁻¹ = 1 := mul_inv_cancel₀ (ne_of_gt hw_pos)
    have hmul2 : h2Weight k * ‖a k‖ ≤
        h2Weight k * ((1 / 2 : ℝ) * (h2Weight k)⁻¹ + (1 / 2 : ℝ) * (h2Weight k * ‖a k‖ ^ 2)) := by
      have hrhs : h2Weight k * ((1 / 2 : ℝ) * (h2Weight k)⁻¹ + (1 / 2 : ℝ) * (h2Weight k * ‖a k‖ ^ 2)) =
          (1 / 2 : ℝ) * (h2Weight k * (h2Weight k)⁻¹) + (1 / 2 : ℝ) * ((h2Weight k) ^ 2 * ‖a k‖ ^ 2) := by
        ring
      rw [hrhs, hinv_cancel]; linarith
    exact le_of_mul_le_mul_left hmul2 hw_pos
  have hcs := tsum_sq_le_mul_of_le hsum_norm hinv.1 ha
    (fun _ => norm_nonneg _)
    (fun k => inv_nonneg.mpr (le_of_lt (h2Weight_pos k)))
    (fun k => mul_nonneg (le_of_lt (h2Weight_pos k)) (sq_nonneg _))
    (fun k => by
      have hw_ne : h2Weight k ≠ 0 := ne_of_gt (h2Weight_pos k)
      rw [← mul_assoc, inv_mul_cancel₀ hw_ne, one_mul])
  exact ⟨hsum_norm, le_trans hcs (mul_le_mul_of_nonneg_right hinv.2 (h2NormSq_nonneg a))⟩

theorem h2Seq_l2_summable {a : (Fin 3 → ℤ) → ℂ} (ha : InH2Seq a) :
    Summable (fun k : Fin 3 → ℤ => ‖a k‖ ^ 2) ∧
    (∑' k : Fin 3 → ℤ, ‖a k‖ ^ 2) ≤ h2NormSq a := by
  have hle : ∀ k, ‖a k‖ ^ 2 ≤ h2Weight k * ‖a k‖ ^ 2 := fun k => by
    nlinarith [one_le_h2Weight k, sq_nonneg ‖a k‖]
  have hsum := Summable.of_nonneg_of_le (fun _ => sq_nonneg _) hle ha
  exact ⟨hsum, hasSum_le hle hsum.hasSum ha.hasSum⟩

theorem inH2Seq_add {a b : (Fin 3 → ℤ) → ℂ} (ha : InH2Seq a) (hb : InH2Seq b) :
    InH2Seq (fun k => a k + b k) ∧
    h2NormSq (fun k => a k + b k) ≤ 2 * h2NormSq a + 2 * h2NormSq b := by
  have hdom : Summable (fun k => 2 * (h2Weight k * ‖a k‖ ^ 2) + 2 * (h2Weight k * ‖b k‖ ^ 2)) :=
    (ha.mul_left 2).add (hb.mul_left 2)
  have hle : ∀ k, h2Weight k * ‖a k + b k‖ ^ 2 ≤
      2 * (h2Weight k * ‖a k‖ ^ 2) + 2 * (h2Weight k * ‖b k‖ ^ 2) := fun k => by
    have htri : ‖a k + b k‖ ≤ ‖a k‖ + ‖b k‖ := norm_add_le _ _
    have hnn : 0 ≤ ‖a k + b k‖ := norm_nonneg _
    have hsq : ‖a k + b k‖ ^ 2 ≤ 2 * ‖a k‖ ^ 2 + 2 * ‖b k‖ ^ 2 := by
      nlinarith [sq_nonneg (‖a k‖ - ‖b k‖)]
    nlinarith [h2Weight_pos k]
  have hsum := Summable.of_nonneg_of_le
    (fun k => mul_nonneg (le_of_lt (h2Weight_pos k)) (sq_nonneg _)) hle hdom
  have hbd := hasSum_le hle hsum.hasSum ((ha.hasSum.mul_left 2).add (hb.hasSum.mul_left 2))
  exact ⟨hsum, hbd⟩

theorem inH2Seq_sub {a b : (Fin 3 → ℤ) → ℂ} (ha : InH2Seq a) (hb : InH2Seq b) :
    InH2Seq (fun k => a k - b k) ∧
    h2NormSq (fun k => a k - b k) ≤ 2 * h2NormSq a + 2 * h2NormSq b := by
  have hdom : Summable (fun k => 2 * (h2Weight k * ‖a k‖ ^ 2) + 2 * (h2Weight k * ‖b k‖ ^ 2)) :=
    (ha.mul_left 2).add (hb.mul_left 2)
  have hle : ∀ k, h2Weight k * ‖a k - b k‖ ^ 2 ≤
      2 * (h2Weight k * ‖a k‖ ^ 2) + 2 * (h2Weight k * ‖b k‖ ^ 2) := fun k => by
    have htri : ‖a k - b k‖ ≤ ‖a k‖ + ‖b k‖ := norm_sub_le _ _
    have hnn : 0 ≤ ‖a k - b k‖ := norm_nonneg _
    have hsq : ‖a k - b k‖ ^ 2 ≤ 2 * ‖a k‖ ^ 2 + 2 * ‖b k‖ ^ 2 := by
      nlinarith [sq_nonneg (‖a k‖ - ‖b k‖)]
    nlinarith [h2Weight_pos k]
  have hsum := Summable.of_nonneg_of_le
    (fun k => mul_nonneg (le_of_lt (h2Weight_pos k)) (sq_nonneg _)) hle hdom
  have hbd := hasSum_le hle hsum.hasSum ((ha.hasSum.mul_left 2).add (hb.hasSum.mul_left 2))
  exact ⟨hsum, hbd⟩

-- ============================================================================
-- SECTION 3: DISCRETE 3D YOUNG INEQUALITY (`ℓ¹ * ℓ² → ℓ²`)
-- ============================================================================

/-- **THEOREM 3 OF MILESTONE 6A (Discrete 3D Young's Convolution Inequality `ℓ¹ * ℓ² → ℓ²`):**
    For nonnegative `f ∈ ℓ¹(ℤ³)` and `g ∈ ℓ²(ℤ³)`:
    `∑' k, (∑' j, f j * g (k - j))² ≤ (∑' j, f j)² * (∑' m, (g m)²)` (`0 sorryAx`). -/
theorem young_l1_l2_3d {f g : (Fin 3 → ℤ) → ℝ}
    (hf : Summable f) (hg2 : Summable (fun m => (g m) ^ 2))
    (hf_nn : ∀ j, 0 ≤ f j) (hg_nn : ∀ m, 0 ≤ g m) :
    Summable (fun k : Fin 3 → ℤ => (∑' j : Fin 3 → ℤ, f j * g (k - j)) ^ 2) ∧
    (∑' k : Fin 3 → ℤ, (∑' j : Fin 3 → ℤ, f j * g (k - j)) ^ 2) ≤
      (∑' j : Fin 3 → ℤ, f j) ^ 2 * (∑' m : Fin 3 → ℤ, (g m) ^ 2) := by
  let F : ℝ := ∑' j, f j
  let G2 : ℝ := ∑' m, (g m) ^ 2
  have hF_nn : 0 ≤ F := tsum_nonneg hf_nn
  have hG2_nn : 0 ≤ G2 := tsum_nonneg fun _ => sq_nonneg _
  have hfg2_sum : ∀ k, Summable (fun j => f j * (g (k - j)) ^ 2) := by
    intro k
    have hg2_shift : Summable (fun j => (g (k - j)) ^ 2) := summable_sub_left hg2 k
    refine Summable.of_nonneg_of_le (fun j => mul_nonneg (hf_nn j) (sq_nonneg _)) (fun j => ?_)
      (hg2_shift.mul_left F)
    exact mul_le_mul_of_nonneg_right (le_tsum_single hf hf_nn j) (sq_nonneg _)
  have hfg_sum : ∀ k, Summable (fun j => f j * g (k - j)) := by
    intro k
    have hdom : Summable (fun j => (1 / 2 : ℝ) * f j + (1 / 2 : ℝ) * (f j * (g (k - j)) ^ 2)) :=
      (hf.mul_left (1 / 2 : ℝ)).add ((hfg2_sum k).mul_left (1 / 2 : ℝ))
    refine Summable.of_nonneg_of_le (fun j => mul_nonneg (hf_nn j) (hg_nn (k - j))) (fun j => ?_) hdom
    have hsq : 0 ≤ (1 - g (k - j)) ^ 2 := sq_nonneg _
    have h1 : g (k - j) ≤ (1 / 2 : ℝ) + (1 / 2 : ℝ) * (g (k - j)) ^ 2 := by nlinarith
    have hmul := mul_le_mul_of_nonneg_left h1 (hf_nn j)
    linarith
  have hpt : ∀ k, (∑' j, f j * g (k - j)) ^ 2 ≤ F * (∑' j, f j * (g (k - j)) ^ 2) := fun k =>
    tsum_sq_le_mul_of_le (hfg_sum k) hf (hfg2_sum k)
      (fun j => mul_nonneg (hf_nn j) (hg_nn (k - j)))
      hf_nn
      (fun j => mul_nonneg (hf_nn j) (sq_nonneg _))
      (fun j => by ring_nf; exact le_refl _)
  have hfin : ∀ s : Finset (Fin 3 → ℤ),
      ∑ k ∈ s, (∑' j, f j * g (k - j)) ^ 2 ≤ F ^ 2 * G2 := by
    intro s
    have h1 : ∑ k ∈ s, (∑' j, f j * g (k - j)) ^ 2 ≤
        ∑ k ∈ s, F * (∑' j, f j * (g (k - j)) ^ 2) := Finset.sum_le_sum fun k _ => hpt k
    rw [← Finset.mul_sum,
        finset_sum_tsum s (fun k j => f j * (g (k - j)) ^ 2) (fun k _ => hfg2_sum k)] at h1
    have h_inner_le : ∀ j : Fin 3 → ℤ,
        (∑ k ∈ s, f j * (g (k - j)) ^ 2) ≤ f j * G2 := by
      intro j
      rw [← Finset.mul_sum]
      refine mul_le_mul_of_nonneg_left ?_ (hf_nn j)
      have hinj : ∀ k₁ ∈ s, ∀ k₂ ∈ s, k₁ - j = k₂ - j → k₁ = k₂ := fun k₁ _ k₂ _ h => by
        simpa [sub_add_cancel] using congrArg (· + j) h
      have himg : (∑ k ∈ s, (g (k - j)) ^ 2) =
          ∑ m ∈ s.image (fun k => k - j), (g m) ^ 2 :=
        (Finset.sum_image (f := fun m => (g m) ^ 2) hinj).symm
      rw [himg]
      exact finset_sum_le_tsum hg2 (fun _ => sq_nonneg _) _
    have hsum_lhs : Summable (fun j => ∑ k ∈ s, f j * (g (k - j)) ^ 2) :=
      summable_finset_sum s (fun k j => f j * (g (k - j)) ^ 2) (fun k _ => hfg2_sum k)
    have htsum_le : (∑' j, ∑ k ∈ s, f j * (g (k - j)) ^ 2) ≤ F * G2 :=
      hasSum_le h_inner_le hsum_lhs.hasSum (hf.hasSum.mul_right G2)
    have h2 : F * (∑' j, ∑ k ∈ s, f j * (g (k - j)) ^ 2) ≤ F * (F * G2) :=
      mul_le_mul_of_nonneg_left htsum_le hF_nn
    linarith [h1, h2]
  have hsum_out : Summable (fun k : Fin 3 → ℤ => (∑' j : Fin 3 → ℤ, f j * g (k - j)) ^ 2) :=
    summable_of_sum_le (fun _ => sq_nonneg _) hfin
  exact ⟨hsum_out, le_of_tendsto hsum_out.hasSum (Eventually.of_forall hfin)⟩

-- ============================================================================
-- SECTION 4: 3D DISCRETE CONVOLUTION BANACH ALGEBRA `H²(𝕋³)` & LIPSCHITZ BOUND
-- ============================================================================

/-- Discrete 3D Fourier convolution `(a * b)(k) = ∑' j : ℤ³, a(j) * b(k - j)`. -/
noncomputable def conv3D (a b : (Fin 3 → ℤ) → ℂ) (k : Fin 3 → ℤ) : ℂ :=
  ∑' j : Fin 3 → ℤ, a j * b (k - j)

theorem conv3D_summable_norm {a b : (Fin 3 → ℤ) → ℂ} (ha : InH2Seq a) (hb : InH2Seq b)
    (k : Fin 3 → ℤ) :
    Summable (fun j : Fin 3 → ℤ => ‖a j * b (k - j)‖) := by
  have ha2 := (h2Seq_l2_summable ha).1
  have hb2 := summable_sub_left (h2Seq_l2_summable hb).1 k
  have hdom : Summable (fun j => (1 / 2 : ℝ) * ‖a j‖ ^ 2 + (1 / 2 : ℝ) * ‖b (k - j)‖ ^ 2) :=
    (ha2.mul_left (1 / 2 : ℝ)).add (hb2.mul_left (1 / 2 : ℝ))
  refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun j => ?_) hdom
  rw [norm_mul]
  nlinarith [sq_nonneg (‖a j‖ - ‖b (k - j)‖)]

theorem conv3D_summable {a b : (Fin 3 → ℤ) → ℂ} (ha : InH2Seq a) (hb : InH2Seq b)
    (k : Fin 3 → ℤ) :
    Summable (fun j : Fin 3 → ℤ => a j * b (k - j)) :=
  Summable.of_norm (conv3D_summable_norm ha hb k)

theorem conv3D_sub_left {a₁ a₂ b : (Fin 3 → ℤ) → ℂ}
    (ha₁ : InH2Seq a₁) (ha₂ : InH2Seq a₂) (hb : InH2Seq b) (k : Fin 3 → ℤ) :
    conv3D (fun j => a₁ j - a₂ j) b k = conv3D a₁ b k - conv3D a₂ b k := by
  unfold conv3D
  have hsub := ((conv3D_summable ha₁ hb k).hasSum.sub (conv3D_summable ha₂ hb k).hasSum).tsum_eq
  have heq : (fun j => (a₁ j - a₂ j) * b (k - j)) = (fun j => a₁ j * b (k - j) - a₂ j * b (k - j)) :=
    funext fun j => sub_mul _ _ _
  rw [heq, hsub]

theorem conv3D_sub_right {a b₁ b₂ : (Fin 3 → ℤ) → ℂ}
    (ha : InH2Seq a) (hb₁ : InH2Seq b₁) (hb₂ : InH2Seq b₂) (k : Fin 3 → ℤ) :
    conv3D a (fun j => b₁ j - b₂ j) k = conv3D a b₁ k - conv3D a b₂ k := by
  unfold conv3D
  have hsub := ((conv3D_summable ha hb₁ k).hasSum.sub (conv3D_summable ha hb₂ k).hasSum).tsum_eq
  have heq : (fun j => a j * (b₁ (k - j) - b₂ (k - j))) =
      (fun j => a j * b₁ (k - j) - a j * b₂ (k - j)) :=
    funext fun j => mul_sub _ _ _
  rw [heq, hsub]

/-- **MAIN THEOREM 4 OF MILESTONE 6A (`H²(𝕋³)` is a Banach Algebra under 3D Convolution):**
    `‖a * b‖²_{H²} ≤ 1696 * ‖a‖²_{H²} * ‖b‖²_{H²}` (`0 sorryAx`). -/
theorem conv3D_inH2_and_norm_le {a b : (Fin 3 → ℤ) → ℂ} (ha : InH2Seq a) (hb : InH2Seq b) :
    InH2Seq (conv3D a b) ∧
    h2NormSq (conv3D a b) ≤ 1696 * h2NormSq a * h2NormSq b := by
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
        ((summable_sub_left hb_l2 k).mul_left (1 / 2 : ℝ)).add (hwa_sum2.mul_left (1 / 2 : ℝ))
      refine Summable.of_nonneg_of_le (fun _ => by dsimp only [wa]; positivity) (fun j => ?_) hdom
      nlinarith [sq_nonneg (‖b (k - j)‖ - wa j)]
    have hsum_t2 : Summable (fun j => ‖a j‖ * wb (k - j)) := by
      have hdom : Summable (fun j => (1 / 2 : ℝ) * ‖a j‖ ^ 2 + (1 / 2 : ℝ) * (wb (k - j)) ^ 2) :=
        (ha_l2.mul_left (1 / 2 : ℝ)).add ((summable_sub_left hwb_sum2 k).mul_left (1 / 2 : ℝ))
      refine Summable.of_nonneg_of_le (fun _ => by dsimp only [wb]; positivity) (fun j => ?_) hdom
      nlinarith [sq_nonneg (‖a j‖ - wb (k - j))]
    have hreidx : (∑' j, ‖b (k - j)‖ * wa j) = T1 k := by
      dsimp only [T1]
      have h := tsum_sub_left hsum_t1_raw k
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
      have hmul := mul_le_mul_of_nonneg_right hsqrt (mul_nonneg (norm_nonneg (a j)) (norm_nonneg (b (k - j))))
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
  have hdom : Summable (fun k => 16 * (T1 k) ^ 2 + 16 * (T2 k) ^ 2) :=
    (hY1.1.mul_left 16).add (hY2.1.mul_left 16)
  have hconv_inH2 : InH2Seq (conv3D a b) :=
    Summable.of_nonneg_of_le (fun k => mul_nonneg (le_of_lt (h2Weight_pos k)) (sq_nonneg _)) hpt hdom
  have hbd_sum : h2NormSq (conv3D a b) ≤ 16 * (∑' k, (T1 k) ^ 2) + 16 * (∑' k, (T2 k) ^ 2) :=
    hasSum_le hpt hconv_inH2.hasSum ((hY1.1.hasSum.mul_left 16).add (hY2.1.hasSum.mul_left 16))
  have hY1_bd : (∑' k, (T1 k) ^ 2) ≤ 53 * h2NormSq b * h2NormSq a := by
    have h1 := hY1.2
    rw [hwa_sq] at h1
    exact le_trans h1 (mul_le_mul_of_nonneg_right hb_l1.2 (h2NormSq_nonneg a))
  have hY2_bd : (∑' k, (T2 k) ^ 2) ≤ 53 * h2NormSq a * h2NormSq b := by
    have h2 := hY2.2
    rw [hwb_sq] at h2
    exact le_trans h2 (mul_le_mul_of_nonneg_right ha_l1.2 (h2NormSq_nonneg b))
  exact ⟨hconv_inH2, by linarith⟩

/-- **MAIN THEOREM 5 OF MILESTONE 6A (Quadratic Convolution Lipschitz Estimate in `H²(𝕋³)`):**
    `‖a * a - b * b‖²_{H²} ≤ 3392 * (‖a‖²_{H²} + ‖b‖²_{H²}) * ‖a - b‖²_{H²}` (`0 sorryAx`). -/
theorem conv3D_self_sub_lipschitz {a b : (Fin 3 → ℤ) → ℂ} (ha : InH2Seq a) (hb : InH2Seq b) :
    InH2Seq (fun k => conv3D a a k - conv3D b b k) ∧
    h2NormSq (fun k => conv3D a a k - conv3D b b k) ≤
      3392 * (h2NormSq a + h2NormSq b) * h2NormSq (fun k => a k - b k) := by
  have hdiff := (inH2Seq_sub ha hb).1
  have hL := conv3D_inH2_and_norm_le hdiff ha
  have hR := conv3D_inH2_and_norm_le hb hdiff
  have hsplit : (fun k => conv3D a a k - conv3D b b k) =
      (fun k => conv3D (fun j => a j - b j) a k + conv3D b (fun j => a j - b j) k) := by
    funext k
    rw [conv3D_sub_left ha hb ha k, conv3D_sub_right hb ha hb k]
    ring
  have hadd := inH2Seq_add hL.1 hR.1
  rw [← hsplit] at hadd
  refine ⟨hadd.1, ?_⟩
  linarith [hadd.2, hL.2, hR.2]

-- ============================================================================
-- SECTION 5: AXIOM AUDIT TRAIL — MILESTONE 6A STAGE 1 (0 sorryAx)
-- ============================================================================

#print axioms summable_and_tsum_inv_h2Weight_le
#print axioms h2Seq_l1_embedding
#print axioms young_l1_l2_3d
#print axioms conv3D_inH2_and_norm_le
#print axioms conv3D_self_sub_lipschitz

end GarrySpectralAlgebra3D