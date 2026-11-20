import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import SpectralBilinearTorus3D

/-!
# GARRYULT v4.0.0 — Milestone 6B (Stage 1): 3D Navier–Stokes Duhamel Operator `Φ`
# Weighted Parabolic Integral Estimate (`4 t K`), Self-Map on the Closed `H²` Ball
# (`54272 T M ≤ ν`), Strict `1/4`-Contraction in Squared `H²` Norm, Solenoidality,
# Reality Symmetry & Momentum Conservation (`0 sorryAx`)
-/

namespace GarryDuhamelOperator3D

open MeasureTheory Filter Topology GarryReal3DCalculus GarryVorticity3D
  GarryLerayTorus3D GarryLerayEnergyLaw3D GarryPoincareSobolev3D
  GarryFourierSpectral3D GarrySpectralOperators3D GarryParsevalSobolev3D
  GarrySobolevEmbedding3D GarrySpectralAlgebra3D GarrySpectralBilinear3D

-- ============================================================================
-- SECTION 1: ELEMENTARY SUMMABILITY, INTEGRAL & WEIGHTED CAUCHY–SCHWARZ LEMMAS
-- ============================================================================

private def subLeftEquiv6b (k : Fin 3 → ℤ) : (Fin 3 → ℤ) ≃ (Fin 3 → ℤ) where
  toFun j := k - j
  invFun j := k - j
  left_inv j := sub_sub_cancel k j
  right_inv j := sub_sub_cancel k j

private theorem summable_sub_left_6b {f : (Fin 3 → ℤ) → ℝ} (hf : Summable f) (k : Fin 3 → ℤ) :
    Summable (fun j => f (k - j)) :=
  ((subLeftEquiv6b k).hasSum_iff.mpr hf.hasSum).summable

private theorem finset_sum_le_tsum_6b {f : (Fin 3 → ℤ) → ℝ}
    (hf : Summable f) (hf_nn : ∀ k, 0 ≤ f k) (s : Finset (Fin 3 → ℤ)) :
    ∑ k ∈ s, f k ≤ ∑' k, f k := by
  have hind : HasSum (fun k => if k ∈ s then f k else 0) (∑ k ∈ s, f k) := by
    refine tendsto_atTop_of_eventually_const (i₀ := s) fun t ht => ?_
    rw [← Finset.sum_filter, Finset.filter_mem_eq_inter, Finset.inter_eq_right.mpr ht]
  exact hasSum_le (fun k => by split_ifs; exact le_refl _; exact hf_nn k) hind hf.hasSum

private theorem le_tsum_single_6b {f : (Fin 3 → ℤ) → ℝ}
    (hf : Summable f) (hf_nn : ∀ k, 0 ≤ f k) (k₀ : Fin 3 → ℤ) :
    f k₀ ≤ ∑' k, f k := by
  simpa using finset_sum_le_tsum_6b hf hf_nn {k₀}

private theorem kNormSq_neg_6b (k : Fin 3 → ℤ) : kNormSq (-k) = kNormSq k := by
  unfold kNormSq
  simp only [Pi.neg_apply, Int.cast_neg, neg_sq]

private theorem heatMultiplier3D_neg_6b (ν τ : ℝ) (k : Fin 3 → ℤ) :
    heatMultiplier3D ν τ (-k) = heatMultiplier3D ν τ k := by
  unfold heatMultiplier3D
  rw [kNormSq_neg_6b]

private theorem heatMultiplier3D_zero_mode (ν τ : ℝ) :
    heatMultiplier3D ν τ 0 = 1 := by
  unfold heatMultiplier3D kNormSq; simp

private theorem heatMultiplier3D_sub_eq (ν t s : ℝ) (k : Fin 3 → ℤ) :
    heatMultiplier3D ν (t - s) k = heatMultiplier3D ν t k * heatMultiplier3D ν (-s) k := by
  rw [sub_eq_add_neg, heatMultiplier3D_add]

private theorem continuous_heatMultiplier3D_time (ν : ℝ) (k : Fin 3 → ℤ) :
    Continuous (fun t : ℝ => heatMultiplier3D ν t k) := by
  unfold heatMultiplier3D
  exact Real.continuous_exp.comp (continuous_const.mul continuous_id)

private theorem conj_intervalIntegral_6b {a b : ℝ} (hab : a ≤ b) (φ : ℝ → ℂ) :
    starRingEnd ℂ (∫ s in a..b, φ s) = ∫ s in a..b, starRingEnd ℂ (φ s) := by
  rw [intervalIntegral.integral_of_le hab, intervalIntegral.integral_of_le hab, ← integral_conj]

private theorem continuousOn_finset_sum_6b {α : Type*} [DecidableEq α] {X : Type*} [TopologicalSpace X]
    {S : Finset α} {A : Set X} (F : α → X → ℝ) (hF : ∀ k ∈ S, ContinuousOn (F k) A) :
    ContinuousOn (fun x => ∑ k ∈ S, F k x) A := by
  induction S using Finset.induction_on with
  | empty => simpa using continuousOn_const
  | insert a t hat ih =>
    have heq : (fun x => ∑ k ∈ insert a t, F k x) = (fun x => F a x + ∑ k ∈ t, F k x) :=
      funext fun x => Finset.sum_insert hat
    rw [heq]
    exact (hF a (Finset.mem_insert_self a t)).add
      (ih fun k hk => hF k (Finset.mem_insert_of_mem hk))

private theorem tendsto_finset_sum_6b {α : Type*} [DecidableEq α] {ι : Type*} {l : Filter ι}
    (S : Finset α) (F : α → ι → ℝ) (L : α → ℝ) (hF : ∀ k ∈ S, Tendsto (F k) l (𝓝 (L k))) :
    Tendsto (fun n => ∑ k ∈ S, F k n) l (𝓝 (∑ k ∈ S, L k)) := by
  induction S using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    exact tendsto_const_nhds
  | insert a t hat ih =>
    have heq : (fun n => ∑ k ∈ insert a t, F k n) = (fun n => F a n + ∑ k ∈ t, F k n) :=
      funext fun n => Finset.sum_insert hat
    rw [heq, Finset.sum_insert hat]
    exact (hF a (Finset.mem_insert_self a t)).add
      (ih fun k hk => hF k (Finset.mem_insert_of_mem hk))

private theorem continuous_integral_upper {h : ℝ → ℂ} (hh : Continuous h) :
    Continuous (fun t : ℝ => ∫ s in (0 : ℝ)..t, h s) := by
  refine continuous_iff_continuousAt.mpr fun t₀ => Metric.continuousAt_iff.mpr fun ε hε => ?_
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hh.continuousOn
    (s := Set.Icc (t₀ - 1) (t₀ + 1))
  let M : ℝ := max C 1
  have hM_pos : 0 < M := lt_of_lt_of_le zero_lt_one (le_max_right C 1)
  let δ : ℝ := min 1 (ε / (2 * M))
  have hδ_pos : 0 < δ := lt_min zero_lt_one (by positivity)
  refine ⟨δ, hδ_pos, fun {t} ht => ?_⟩
  rw [Real.dist_eq] at ht
  have ht1 : |t - t₀| < 1 := lt_of_lt_of_le ht (min_le_left _ _)
  have htε : |t - t₀| < ε / (2 * M) := lt_of_lt_of_le ht (min_le_right _ _)
  have hdiff : (∫ s in (0 : ℝ)..t, h s) - (∫ s in (0 : ℝ)..t₀, h s) = ∫ s in t₀..t, h s := by
    have hadd := intervalIntegral.integral_add_adjacent_intervals
      (hh.intervalIntegrable (μ := volume) 0 t₀) (hh.intervalIntegrable (μ := volume) t₀ t)
    exact (eq_sub_of_add_eq' hadd).symm
  rw [dist_eq_norm, hdiff]
  have hbd : ‖∫ s in t₀..t, h s‖ ≤ M * |t - t₀| := by
    refine intervalIntegral.norm_integral_le_of_norm_le_const fun s hs => ?_
    rw [Set.mem_uIoc] at hs
    have habs_lt : t₀ - 1 < t ∧ t < t₀ + 1 := abs_lt.mp ht1 |> fun ⟨h1, h2⟩ => ⟨by linarith, by linarith⟩
    have hs_mem : s ∈ Set.Icc (t₀ - 1) (t₀ + 1) := by
      rcases hs with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact ⟨by linarith, by linarith⟩
      · exact ⟨by linarith, by linarith⟩
    exact le_trans (hC s hs_mem) (le_max_left C 1)
  have hlt : M * |t - t₀| < M * (ε / (2 * M)) := mul_lt_mul_of_pos_left htε hM_pos
  have hcalc : M * (ε / (2 * M)) = ε / 2 := by
    have hM_ne : M ≠ 0 := ne_of_gt hM_pos
    field_simp [hM_ne]
  linarith

private theorem integral_finset_sum_Icc {α : Type*} [DecidableEq α] {a b : ℝ} (hab : a ≤ b)
    (s : Finset α) (F : α → ℝ → ℝ) (hF : ∀ k ∈ s, ContinuousOn (F k) (Set.Icc a b)) :
    (∫ t in a..b, ∑ k ∈ s, F k t) = ∑ k ∈ s, ∫ t in a..b, F k t := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert x t hxt ih =>
    have hFx : ContinuousOn (F x) (Set.Icc a b) := hF x (Finset.mem_insert_self x t)
    have hFt : ContinuousOn (fun r => ∑ k ∈ t, F k r) (Set.Icc a b) :=
      continuousOn_finset_sum_6b F fun k hk => hF k (Finset.mem_insert_of_mem hk)
    have heq : (fun r => ∑ k ∈ insert x t, F k r) = (fun r => F x r + ∑ k ∈ t, F k r) :=
      funext fun r => Finset.sum_insert hxt
    rw [heq, intervalIntegral.integral_add (hFx.intervalIntegrable_of_Icc hab)
          (hFt.intervalIntegrable_of_Icc hab),
        Finset.sum_insert hxt, ih fun k hk => hF k (Finset.mem_insert_of_mem hk)]

/-- **Weighted Interval Cauchy–Schwarz Inequality:**
    If `φ² ≤ w * b` on `[a, b]`, then `(∫_a^b φ)² ≤ (∫_a^b w) * (∫_a^b b)` (`0 sorryAx`). -/
private theorem intervalIntegral_cs_weighted {a b : ℝ} (hab : a ≤ b)
    {φ w g : ℝ → ℝ}
    (hφ : ContinuousOn φ (Set.Icc a b)) (hw : ContinuousOn w (Set.Icc a b))
    (hg : ContinuousOn g (Set.Icc a b))
    (hφ_nn : ∀ s ∈ Set.Icc a b, 0 ≤ φ s) (hw_nn : ∀ s ∈ Set.Icc a b, 0 ≤ w s)
    (hg_nn : ∀ s ∈ Set.Icc a b, 0 ≤ g s)
    (hpt : ∀ s ∈ Set.Icc a b, (φ s) ^ 2 ≤ w s * g s) :
    (∫ s in a..b, φ s) ^ 2 ≤ (∫ s in a..b, w s) * (∫ s in a..b, g s) := by
  let A : ℝ := ∫ s in a..b, φ s
  let W : ℝ := ∫ s in a..b, w s
  let B : ℝ := ∫ s in a..b, g s
  have hW_nn : 0 ≤ W := intervalIntegral.integral_nonneg hab hw_nn
  have hquad : ∀ r : ℝ, 0 ≤ r ^ 2 * W - 2 * r * A + B := by
    intro r
    have h1 : ContinuousOn (fun s => r ^ 2 * w s) (Set.Icc a b) := continuousOn_const.mul hw
    have h2 : ContinuousOn (fun s => 2 * r * φ s) (Set.Icc a b) := continuousOn_const.mul hφ
    have h12 : ContinuousOn (fun s => r ^ 2 * w s - 2 * r * φ s) (Set.Icc a b) := h1.sub h2
    have hnn : 0 ≤ ∫ s in a..b, (r ^ 2 * w s - 2 * r * φ s + g s) := by
      refine intervalIntegral.integral_nonneg hab fun s hs => ?_
      rcases le_or_gt 0 r with hr | hr
      · have hsq : 0 ≤ (r * Real.sqrt (w s) - Real.sqrt (g s)) ^ 2 := sq_nonneg _
        have hsq_w : Real.sqrt (w s) ^ 2 = w s := Real.sq_sqrt (hw_nn s hs)
        have hsq_g : Real.sqrt (g s) ^ 2 = g s := Real.sq_sqrt (hg_nn s hs)
        have hprod : φ s ≤ Real.sqrt (w s) * Real.sqrt (g s) := by
          rw [← Real.sqrt_mul (hw_nn s hs)]; exact Real.le_sqrt_of_sq_le (hpt s hs)
        have hexp : (r * Real.sqrt (w s) - Real.sqrt (g s)) ^ 2 =
            r ^ 2 * w s - 2 * r * (Real.sqrt (w s) * Real.sqrt (g s)) + g s := by
          nlinarith [hsq_w, hsq_g]
        nlinarith
      · have hw_t : 0 ≤ r ^ 2 * w s := mul_nonneg (sq_nonneg _) (hw_nn s hs)
        have hφ_t : 0 ≤ -2 * r * φ s := by nlinarith [hφ_nn s hs]
        linarith [hg_nn s hs]
    rw [intervalIntegral.integral_add (h12.intervalIntegrable_of_Icc hab) (hg.intervalIntegrable_of_Icc hab),
        intervalIntegral.integral_sub (h1.intervalIntegrable_of_Icc hab) (h2.intervalIntegrable_of_Icc hab),
        intervalIntegral.integral_const_mul (r ^ 2) w,
        intervalIntegral.integral_const_mul (2 * r) φ] at hnn
    exact hnn
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

private theorem continuousOn_inv_sqrt_sub {t δ : ℝ} (hδ : 0 < δ) :
    ContinuousOn (fun s : ℝ => (Real.sqrt (t - s))⁻¹) (Set.Icc 0 (t - δ)) := by
  have h1 : ContinuousOn (fun s : ℝ => Real.sqrt (t - s)) (Set.Icc 0 (t - δ)) :=
    (Real.continuous_sqrt.comp (continuous_const.sub continuous_id)).continuousOn
  exact h1.inv₀ fun s hs => ne_of_gt (Real.sqrt_pos.mpr (by linarith [hs.2]))

/-- Exact elementary integral `∫_0^{t-δ} (t - s)^{-1/2} ds = 2√t - 2√δ ≤ 2√t` (`0 sorryAx`). -/
private theorem integral_inv_sqrt_sub {t δ : ℝ} (hδ : 0 < δ) (hδt : δ < t) :
    (∫ s in (0 : ℝ)..(t - δ), (Real.sqrt (t - s))⁻¹) = 2 * Real.sqrt t - 2 * Real.sqrt δ := by
  have hle : (0 : ℝ) ≤ t - δ := by linarith
  have hderiv : ∀ s ∈ Set.uIcc (0 : ℝ) (t - δ),
      HasDerivAt (fun r : ℝ => (-2 : ℝ) * Real.sqrt (t - r)) ((Real.sqrt (t - s))⁻¹) s := by
    intro s hs
    rw [Set.uIcc_of_le hle] at hs
    have hts_pos : 0 < t - s := by linarith [hs.2]
    have hlin : HasDerivAt (fun r : ℝ => t - r) (-1 : ℝ) s := by
      have h := (hasDerivAt_const s t).sub (hasDerivAt_id s)
      have heq : (0 : ℝ) - 1 = -1 := by norm_num
      rwa [heq] at h
    have hsq : HasDerivAt (fun r : ℝ => Real.sqrt (t - r))
        (1 / (2 * Real.sqrt (t - s)) * (-1)) s :=
      (Real.hasDerivAt_sqrt (ne_of_gt hts_pos)).comp s hlin
    have hmul := hsq.const_mul (-2 : ℝ)
    have hsq_ne : Real.sqrt (t - s) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hts_pos)
    have hval : (-2 : ℝ) * (1 / (2 * Real.sqrt (t - s)) * (-1)) = (Real.sqrt (t - s))⁻¹ := by
      field_simp [hsq_ne]
    rwa [hval] at hmul
  have hcont := continuousOn_inv_sqrt_sub (t := t) hδ
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv (hcont.intervalIntegrable_of_Icc hle)
  have hsub : t - (t - δ) = δ := by ring
  rw [hsub, sub_zero] at hftc
  linarith

private theorem tendsto_sub_div_add_two {t : ℝ} (ht : 0 < t) :
    Tendsto (fun n : ℕ => t - t / ((n : ℝ) + 2)) atTop (𝓝 t) := by
  refine Metric.tendsto_atTop.mpr fun ε hε => ?_
  refine ⟨Nat.ceil (t / ε), fun n hn => ?_⟩
  rw [Real.dist_eq]
  have hdiff : t - t / ((n : ℝ) + 2) - t = -(t / ((n : ℝ) + 2)) := by ring
  have hden : 0 < (n : ℝ) + 2 := by positivity
  rw [hdiff, abs_neg, abs_of_pos (div_pos ht hden), div_lt_iff₀ hden]
  have hceil : t / ε ≤ (n : ℝ) := le_trans (Nat.le_ceil _) (Nat.cast_le.mpr hn)
  have hlt : t / ε < (n : ℝ) + 2 := by linarith
  have h1 := (div_lt_iff₀ hε).mp hlt
  linarith

/-- **Core Parabolic Integral `H²` Estimate (`0 sorryAx`):**
    If `G : ℝ → VecSeq3D` is mode-wise continuous and satisfies `‖G(s)‖²_{H²} ≤ K / (t - s)`
    for all `s ∈ [0, t)`, then `I = ∫_0^t G(s) ds` lies in `H²(𝕋³; ℂ³)` with `‖I‖²_{H²} ≤ 4 t K`. -/
theorem integral_h2_bound_of_inv_sqrt_decay
    {t K : ℝ} (ht : 0 ≤ t) (hK : 0 ≤ K) {G : ℝ → VecSeq3D}
    (hG_cont : ∀ (k : Fin 3 → ℤ) (c : Fin 3), Continuous (fun s : ℝ => G s k c))
    (hG_bound : ∀ s ∈ Set.Ico (0 : ℝ) t, InH2Vec (G s) ∧ h2VecNormSq (G s) ≤ K / (t - s)) :
    InH2Vec (fun k c => ∫ s in (0 : ℝ)..t, G s k c) ∧
    h2VecNormSq (fun k c => ∫ s in (0 : ℝ)..t, G s k c) ≤ 4 * t * K := by
  let I : VecSeq3D := fun k c => ∫ s in (0 : ℝ)..t, G s k c
  rcases eq_or_lt_of_le ht with rfl | ht_pos
  · have hI0 : ∀ k c, I k c = 0 := fun k c => by dsimp only [I]; simp
    have hin : InH2Vec I := fun c => by
      have : (fun k => h2Weight k * ‖I k c‖ ^ 2) = 0 := by funext k; simp [hI0]
      rw [InH2Seq, this]; exact summable_zero
    have hnorm0 : h2VecNormSq I = 0 := by
      unfold h2VecNormSq h2NormSq
      have : ∀ c : Fin 3, (∑' k : Fin 3 → ℤ, h2Weight k * ‖I k c‖ ^ 2) = 0 := fun c => by
        simp [hI0]
      rw [this 0, this 1, this 2]; ring
    exact ⟨hin, by linarith⟩
  · have hfin_S : ∀ S : Finset (Fin 3 → ℤ),
        ∑ k ∈ S, h2Weight k * vecNormSqC (I k) ≤ 4 * t * K := by
      intro S
      let t_n : ℕ → ℝ := fun n => t - t / ((n : ℝ) + 2)
      let I_n : ℕ → VecSeq3D := fun n k c => ∫ s in (0 : ℝ)..(t_n n), G s k c
      have h_le_n : ∀ n : ℕ, ∑ k ∈ S, h2Weight k * vecNormSqC (I_n n k) ≤ 4 * t * K := by
        intro n
        let δ : ℝ := t / ((n : ℝ) + 2)
        have hδ_pos : 0 < δ := by dsimp only [δ]; positivity
        have hδ_lt : δ < t := by
          dsimp only [δ]
          have hden : (1 : ℝ) < (n : ℝ) + 2 := by linarith [Nat.cast_nonneg (α := ℝ) n]
          exact (div_lt_iff₀ (by positivity : (0 : ℝ) < (n : ℝ) + 2)).mpr (by nlinarith)
        have hle_n : (0 : ℝ) ≤ t - δ := by linarith
        have hW_int : (∫ s in (0 : ℝ)..(t - δ), (Real.sqrt (t - s))⁻¹) =
            2 * Real.sqrt t - 2 * Real.sqrt δ := integral_inv_sqrt_sub hδ_pos hδ_lt
        have hW_le : (∫ s in (0 : ℝ)..(t - δ), (Real.sqrt (t - s))⁻¹) ≤ 2 * Real.sqrt t := by
          linarith [Real.sqrt_nonneg δ]
        have hw_cont : ContinuousOn (fun s : ℝ => (Real.sqrt (t - s))⁻¹) (Set.Icc 0 (t - δ)) :=
          continuousOn_inv_sqrt_sub (t := t) hδ_pos
        have hsq_cont : ContinuousOn (fun s : ℝ => Real.sqrt (t - s)) (Set.Icc 0 (t - δ)) :=
          (Real.continuous_sqrt.comp (continuous_const.sub continuous_id)).continuousOn
        have hcomp_bd : ∀ (k : Fin 3 → ℤ) (c : Fin 3),
            ‖I_n n k c‖ ^ 2 ≤ (2 * Real.sqrt t) *
              ∫ s in (0 : ℝ)..(t - δ), Real.sqrt (t - s) * ‖G s k c‖ ^ 2 := by
          intro k c
          have hnorm_int : ‖I_n n k c‖ ≤ ∫ s in (0 : ℝ)..(t - δ), ‖G s k c‖ :=
            intervalIntegral.norm_integral_le_integral_norm hle_n
          have hnn_int : 0 ≤ ‖I_n n k c‖ := norm_nonneg _
          have hsq1 : ‖I_n n k c‖ ^ 2 ≤ (∫ s in (0 : ℝ)..(t - δ), ‖G s k c‖) ^ 2 := by nlinarith
          have hcs := intervalIntegral_cs_weighted hle_n
            (φ := fun s => ‖G s k c‖)
            (w := fun s => (Real.sqrt (t - s))⁻¹)
            (g := fun s => Real.sqrt (t - s) * ‖G s k c‖ ^ 2)
            ((hG_cont k c).norm.continuousOn) hw_cont
            (hsq_cont.mul ((hG_cont k c).norm.pow 2).continuousOn)
            (fun _ _ => norm_nonneg _)
            (fun _ _ => inv_nonneg.mpr (Real.sqrt_nonneg _))
            (fun _ _ => mul_nonneg (Real.sqrt_nonneg _) (sq_nonneg _))
            (fun s hs => by
              have hts_pos : 0 < t - s := by linarith [hs.2]
              have hne : Real.sqrt (t - s) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hts_pos)
              rw [← mul_assoc, inv_mul_cancel₀ hne, one_mul])
          have hB_nn : 0 ≤ ∫ s in (0 : ℝ)..(t - δ), Real.sqrt (t - s) * ‖G s k c‖ ^ 2 :=
            intervalIntegral.integral_nonneg hle_n fun _ _ => mul_nonneg (Real.sqrt_nonneg _) (sq_nonneg _)
          exact le_trans hsq1 (le_trans hcs (mul_le_mul_of_nonneg_right hW_le hB_nn))
        have hvec_bd : ∀ k : Fin 3 → ℤ,
            h2Weight k * vecNormSqC (I_n n k) ≤
              (2 * Real.sqrt t) *
                ∫ s in (0 : ℝ)..(t - δ),
                  h2Weight k * (Real.sqrt (t - s) * vecNormSqC (G s k)) := by
          intro k
          have hc0 := hcomp_bd k 0
          have hc1 := hcomp_bd k 1
          have hc2 := hcomp_bd k 2
          have hcg : ∀ c : Fin 3, ContinuousOn (fun s => Real.sqrt (t - s) * ‖G s k c‖ ^ 2)
              (Set.Icc 0 (t - δ)) :=
            fun c => hsq_cont.mul ((hG_cont k c).norm.pow 2).continuousOn
          have hcg01 : ContinuousOn (fun s => Real.sqrt (t - s) * ‖G s k 0‖ ^ 2 +
              Real.sqrt (t - s) * ‖G s k 1‖ ^ 2) (Set.Icc 0 (t - δ)) :=
            (hcg 0).add (hcg 1)
          have hsum3 : (∫ s in (0 : ℝ)..(t - δ), Real.sqrt (t - s) * ‖G s k 0‖ ^ 2) +
              (∫ s in (0 : ℝ)..(t - δ), Real.sqrt (t - s) * ‖G s k 1‖ ^ 2) +
              (∫ s in (0 : ℝ)..(t - δ), Real.sqrt (t - s) * ‖G s k 2‖ ^ 2) =
              ∫ s in (0 : ℝ)..(t - δ), Real.sqrt (t - s) * vecNormSqC (G s k) := by
            rw [← intervalIntegral.integral_add ((hcg 0).intervalIntegrable_of_Icc hle_n)
                  ((hcg 1).intervalIntegrable_of_Icc hle_n),
                ← intervalIntegral.integral_add (hcg01.intervalIntegrable_of_Icc hle_n)
                  ((hcg 2).intervalIntegrable_of_Icc hle_n)]
            congr 1; funext s; unfold vecNormSqC; ring
          have hle_v : vecNormSqC (I_n n k) ≤
              (2 * Real.sqrt t) * ∫ s in (0 : ℝ)..(t - δ), Real.sqrt (t - s) * vecNormSqC (G s k) := by
            have h1 : ‖I_n n k 0‖ ^ 2 + ‖I_n n k 1‖ ^ 2 + ‖I_n n k 2‖ ^ 2 ≤
                (2 * Real.sqrt t) *
                  ((∫ s in (0 : ℝ)..(t - δ), Real.sqrt (t - s) * ‖G s k 0‖ ^ 2) +
                   (∫ s in (0 : ℝ)..(t - δ), Real.sqrt (t - s) * ‖G s k 1‖ ^ 2) +
                   (∫ s in (0 : ℝ)..(t - δ), Real.sqrt (t - s) * ‖G s k 2‖ ^ 2)) := by
              linarith [hc0, hc1, hc2]
            rw [hsum3] at h1
            exact h1
          have hmul := mul_le_mul_of_nonneg_left hle_v (le_of_lt (h2Weight_pos k))
          rw [← mul_assoc, mul_comm (h2Weight k) (2 * Real.sqrt t), mul_assoc,
              ← intervalIntegral.integral_const_mul (h2Weight k)] at hmul
          exact hmul
        have hS_sum : ∑ k ∈ S, h2Weight k * vecNormSqC (I_n n k) ≤
            (2 * Real.sqrt t) *
              ∫ s in (0 : ℝ)..(t - δ),
                ∑ k ∈ S, h2Weight k * (Real.sqrt (t - s) * vecNormSqC (G s k)) := by
          have h1 := Finset.sum_le_sum fun k (_ : k ∈ S) => hvec_bd k
          rw [← Finset.mul_sum] at h1
          have hcont_k : ∀ k ∈ S, ContinuousOn
              (fun s => h2Weight k * (Real.sqrt (t - s) * vecNormSqC (G s k))) (Set.Icc 0 (t - δ)) :=
            fun k _ => continuousOn_const.mul (hsq_cont.mul
              (((((hG_cont k 0).norm.pow 2).add ((hG_cont k 1).norm.pow 2)).add
                ((hG_cont k 2).norm.pow 2)).continuousOn))
          rw [integral_finset_sum_Icc hle_n S _ hcont_k]
          exact h1
        have hpt_s : ∀ s ∈ Set.Icc (0 : ℝ) (t - δ),
            (∑ k ∈ S, h2Weight k * (Real.sqrt (t - s) * vecNormSqC (G s k))) ≤
              K * (Real.sqrt (t - s))⁻¹ := by
          intro s hs
          have hts_pos : 0 < t - s := by linarith [hs.2]
          have hs_ico : s ∈ Set.Ico (0 : ℝ) t := ⟨hs.1, by linarith [hs.2]⟩
          have hGb := hG_bound s hs_ico
          have hfac : (∑ k ∈ S, h2Weight k * (Real.sqrt (t - s) * vecNormSqC (G s k))) =
              Real.sqrt (t - s) * ∑ k ∈ S, h2Weight k * vecNormSqC (G s k) := by
            rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun k _ => ?_; ring
          rw [hfac]
          have hS_le_H2 : ∑ k ∈ S, h2Weight k * vecNormSqC (G s k) ≤ h2VecNormSq (G s) := by
            have hhas := hasSum_h2VecNormSq hGb.1
            have hle := finset_sum_le_tsum_6b hhas.summable
              (fun k => mul_nonneg (le_of_lt (h2Weight_pos k)) (vecNormSqC_nonneg _)) S
            rwa [hhas.tsum_eq] at hle
          have hS_le_K : ∑ k ∈ S, h2Weight k * vecNormSqC (G s k) ≤ K / (t - s) :=
            le_trans hS_le_H2 hGb.2
          have hmul := mul_le_mul_of_nonneg_left hS_le_K (Real.sqrt_nonneg (t - s))
          have hsq : Real.sqrt (t - s) ^ 2 = t - s := Real.sq_sqrt (le_of_lt hts_pos)
          have hne : Real.sqrt (t - s) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hts_pos)
          have heq_r : Real.sqrt (t - s) * (K / (t - s)) = K * (Real.sqrt (t - s))⁻¹ := by
            calc Real.sqrt (t - s) * (K / (t - s))
                = Real.sqrt (t - s) * (K / (Real.sqrt (t - s) ^ 2)) := by rw [hsq]
              _ = K * (Real.sqrt (t - s))⁻¹ := by field_simp [hne]
          rwa [heq_r] at hmul
        have hcont_lhs : ContinuousOn
            (fun s => ∑ k ∈ S, h2Weight k * (Real.sqrt (t - s) * vecNormSqC (G s k)))
            (Set.Icc 0 (t - δ)) :=
          continuousOn_finset_sum_6b
            (fun k s => h2Weight k * (Real.sqrt (t - s) * vecNormSqC (G s k)))
            fun k _ => continuousOn_const.mul (hsq_cont.mul
              (((((hG_cont k 0).norm.pow 2).add ((hG_cont k 1).norm.pow 2)).add
                ((hG_cont k 2).norm.pow 2)).continuousOn))
        have hcont_rhs : ContinuousOn (fun s => K * (Real.sqrt (t - s))⁻¹) (Set.Icc 0 (t - δ)) :=
          continuousOn_const.mul hw_cont
        have hmono := intervalIntegral.integral_mono_on (μ := volume) hle_n
          (hcont_lhs.intervalIntegrable_of_Icc hle_n)
          (hcont_rhs.intervalIntegrable_of_Icc hle_n)
          hpt_s
        rw [intervalIntegral.integral_const_mul K] at hmono
        have hstep1 := le_trans hS_sum (mul_le_mul_of_nonneg_left hmono (by positivity))
        have hstep2 : (2 * Real.sqrt t) * (K * ∫ s in (0 : ℝ)..(t - δ), (Real.sqrt (t - s))⁻¹) ≤
            (2 * Real.sqrt t) * (K * (2 * Real.sqrt t)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hW_le hK) (by positivity)
        have hcalc : (2 * Real.sqrt t) * (K * (2 * Real.sqrt t)) = 4 * t * K := by
          have hsq_t : Real.sqrt t ^ 2 = t := Real.sq_sqrt ht
          nlinarith [hsq_t]
        linarith
      have htend : Tendsto (fun n : ℕ => ∑ k ∈ S, h2Weight k * vecNormSqC (I_n n k))
          atTop (𝓝 (∑ k ∈ S, h2Weight k * vecNormSqC (I k))) := by
        refine tendsto_finset_sum_6b S (fun k n => h2Weight k * vecNormSqC (I_n n k))
          (fun k => h2Weight k * vecNormSqC (I k)) fun k _ => ?_
        have htc : ∀ c : Fin 3, Tendsto (fun n : ℕ => ‖I_n n k c‖ ^ 2) atTop (𝓝 (‖I k c‖ ^ 2)) :=
          fun c =>
            (((continuous_integral_upper (hG_cont k c)).norm.pow 2).tendsto t).comp
              (tendsto_sub_div_add_two ht_pos)
        exact tendsto_const_nhds.mul (((htc 0).add (htc 1)).add (htc 2))
      exact le_of_tendsto htend (Eventually.of_forall h_le_n)
    have hI_inH2 : InH2Vec I := by
      intro c
      refine summable_of_sum_le (c := 4 * t * K)
        (fun k => mul_nonneg (le_of_lt (h2Weight_pos k)) (sq_nonneg _)) fun S => ?_
      have hle : ∑ k ∈ S, h2Weight k * ‖I k c‖ ^ 2 ≤ ∑ k ∈ S, h2Weight k * vecNormSqC (I k) := by
        refine Finset.sum_le_sum fun k _ => mul_le_mul_of_nonneg_left ?_ (le_of_lt (h2Weight_pos k))
        unfold vecNormSqC
        fin_cases c
        · change ‖I k 0‖ ^ 2 ≤ _; linarith [sq_nonneg ‖I k 1‖, sq_nonneg ‖I k 2‖]
        · change ‖I k 1‖ ^ 2 ≤ _; linarith [sq_nonneg ‖I k 0‖, sq_nonneg ‖I k 2‖]
        · change ‖I k 2‖ ^ 2 ≤ _; linarith [sq_nonneg ‖I k 0‖, sq_nonneg ‖I k 1‖]
      exact le_trans hle (hfin_S S)
    exact ⟨hI_inH2, le_of_tendsto (hasSum_h2VecNormSq hI_inH2) (Eventually.of_forall hfin_S)⟩

-- ============================================================================
-- SECTION 2: ADMISSIBLE CURVES & MODE-WISE CONTINUITY OF BILINEAR FLUX
-- ============================================================================

/-- Curve `u : ℝ → VecSeq3D` uniformly bounded in the closed `H²` ball of squared radius `M`
    and continuous on every Fourier mode `(k, c)`. -/
structure IsAdmissibleCurve (M : ℝ) (u : ℝ → VecSeq3D) : Prop where
  h_inH2 : ∀ t : ℝ, InH2Vec (u t)
  h_bound : ∀ t : ℝ, h2VecNormSq (u t) ≤ M
  h_cont : ∀ (k : Fin 3 → ℤ) (c : Fin 3), Continuous (fun t : ℝ => u t k c)

/-- Mode-wise continuity of discrete 3D convolution under uniform `H²` bounds (`0 sorryAx`). -/
theorem continuous_conv3D_of_uniform_H2 {M : ℝ}
    {a b : ℝ → (Fin 3 → ℤ) → ℂ}
    (ha_in : ∀ t, InH2Seq (a t)) (hb_in : ∀ t, InH2Seq (b t))
    (ha_bd : ∀ t, h2NormSq (a t) ≤ M) (hb_bd : ∀ t, h2NormSq (b t) ≤ M)
    (ha_cont : ∀ j, Continuous (fun t => a t j))
    (hb_cont : ∀ j, Continuous (fun t => b t j))
    (k : Fin 3 → ℤ) :
    Continuous (fun t : ℝ => conv3D (a t) (b t) k) := by
  let dom : (Fin 3 → ℤ) → ℝ := fun j =>
    (M / 2) * (h2Weight j)⁻¹ + (M / 2) * (h2Weight (k - j))⁻¹
  have hinv := summable_and_tsum_inv_h2Weight_le.1
  have hdom_sum : Summable dom :=
    (hinv.mul_left (M / 2)).add ((summable_sub_left_6b hinv k).mul_left (M / 2))
  unfold conv3D
  refine continuous_tsum (fun j => (ha_cont j).mul (hb_cont (k - j))) hdom_sum fun j t => ?_
  have ha_pt : h2Weight j * ‖a t j‖ ^ 2 ≤ M :=
    le_trans (le_tsum_single_6b (ha_in t)
      (fun m => mul_nonneg (le_of_lt (h2Weight_pos m)) (sq_nonneg _)) j) (ha_bd t)
  have hb_pt : h2Weight (k - j) * ‖b t (k - j)‖ ^ 2 ≤ M :=
    le_trans (le_tsum_single_6b (hb_in t)
      (fun m => mul_nonneg (le_of_lt (h2Weight_pos m)) (sq_nonneg _)) (k - j)) (hb_bd t)
  have hw1 : 0 < h2Weight j := h2Weight_pos j
  have hw2 : 0 < h2Weight (k - j) := h2Weight_pos (k - j)
  have h1 : ‖a t j‖ ^ 2 ≤ M * (h2Weight j)⁻¹ := by
    have hmul := mul_le_mul_of_nonneg_right ha_pt (inv_nonneg.mpr (le_of_lt hw1))
    rw [mul_comm (h2Weight j), mul_assoc, mul_inv_cancel₀ (ne_of_gt hw1), mul_one] at hmul
    exact hmul
  have h2 : ‖b t (k - j)‖ ^ 2 ≤ M * (h2Weight (k - j))⁻¹ := by
    have hmul := mul_le_mul_of_nonneg_right hb_pt (inv_nonneg.mpr (le_of_lt hw2))
    rw [mul_comm (h2Weight (k - j)), mul_assoc, mul_inv_cancel₀ (ne_of_gt hw2), mul_one] at hmul
    exact hmul
  rw [norm_mul]
  dsimp only [dom]
  nlinarith [sq_nonneg (‖a t j‖ - ‖b t (k - j)‖)]

theorem continuous_nsBilinear6A_of_admissible {M : ℝ}
    {u v : ℝ → VecSeq3D} (hu : IsAdmissibleCurve M u) (hv : IsAdmissibleCurve M v)
    (k : Fin 3 → ℤ) (c : Fin 3) :
    Continuous (fun t : ℝ => nsBilinear6A (u t) (v t) k c) := by
  have hcomp_bd : ∀ (w : ℝ → VecSeq3D), IsAdmissibleCurve M w →
      ∀ (d : Fin 3) (t : ℝ), h2NormSq (fun m => w t m d) ≤ M := by
    intro w hw d t
    have hbd := hw.h_bound t
    unfold h2VecNormSq at hbd
    fin_cases d
    · change h2NormSq (fun m => w t m 0) ≤ M
      linarith [h2NormSq_nonneg (fun m => w t m 1), h2NormSq_nonneg (fun m => w t m 2)]
    · change h2NormSq (fun m => w t m 1) ≤ M
      linarith [h2NormSq_nonneg (fun m => w t m 0), h2NormSq_nonneg (fun m => w t m 2)]
    · change h2NormSq (fun m => w t m 2) ≤ M
      linarith [h2NormSq_nonneg (fun m => w t m 0), h2NormSq_nonneg (fun m => w t m 1)]
  have hconv : ∀ j d : Fin 3,
      Continuous (fun t : ℝ => conv3D (fun m => u t m j) (fun m => v t m d) k) :=
    fun j d => continuous_conv3D_of_uniform_H2
      (fun t => hu.h_inH2 t j) (fun t => hv.h_inH2 t d)
      (hcomp_bd u hu j) (hcomp_bd v hv d)
      (fun m => hu.h_cont m j) (fun m => hv.h_cont m d) k
  have hflux : ∀ d : Fin 3, Continuous (fun t : ℝ => nsFlux6A (u t) (v t) k d) := fun d => by
    unfold nsFlux6A
    exact continuous_const.mul
      (((continuous_const.mul (hconv 0 d)).add (continuous_const.mul (hconv 1 d))).add
        (continuous_const.mul (hconv 2 d)))
  unfold nsBilinear6A lerayProj6A
  by_cases hk : k = 0
  · subst hk; simp only [↓reduceIte]; exact (hflux c).neg
  · simp only [hk, ↓reduceIte]
    exact ((hflux c).sub
      ((((continuous_const.mul (hflux 0)).add (continuous_const.mul (hflux 1))).add
        (continuous_const.mul (hflux 2))).div_const _ |>.mul continuous_const)).neg

-- ============================================================================
-- SECTION 3: DUHAMEL OPERATOR `Φ`, SELF-MAP & STRICT `1/4`-CONTRACTION
-- ============================================================================

/-- Time clamp onto `[0, T]` ensuring global continuity and boundedness on `ℝ`. -/
def clampT (T t : ℝ) : ℝ := max 0 (min T t)

theorem continuous_clampT (T : ℝ) : Continuous (clampT T) :=
  continuous_const.max (continuous_const.min continuous_id)

theorem clampT_mem_Icc {T : ℝ} (hT : 0 ≤ T) (t : ℝ) : clampT T t ∈ Set.Icc 0 T :=
  ⟨le_max_left _ _, max_le hT (min_le_left _ _)⟩

theorem clampT_eq_self {T t : ℝ} (ht : t ∈ Set.Icc 0 T) : clampT T t = t := by
  unfold clampT
  rw [min_eq_right ht.2, max_eq_right ht.1]

/-- Raw spectral Duhamel integral operator at time `t`. -/
noncomputable def duhamelRaw (ν : ℝ) (u₀ : VecSeq3D) (u : ℝ → VecSeq3D) (t : ℝ) : VecSeq3D :=
  fun k c =>
    (heatMultiplier3D ν t k : ℂ) * u₀ k c +
    ∫ s in (0 : ℝ)..t, heatSmoothedBilinear6A ν (t - s) (u s) (u s) k c

/-- Time-clamped Duhamel operator `Φ` on `[0, T]` extended continuously to `ℝ`. -/
noncomputable def duhamelOp (ν T : ℝ) (u₀ : VecSeq3D) (u : ℝ → VecSeq3D) (t : ℝ) : VecSeq3D :=
  duhamelRaw ν u₀ u (clampT T t)

theorem duhamelOp_eq_raw {ν T t : ℝ} (ht : t ∈ Set.Icc 0 T) (u₀ : VecSeq3D) (u : ℝ → VecSeq3D) :
    duhamelOp ν T u₀ u t = duhamelRaw ν u₀ u t := by
  unfold duhamelOp; rw [clampT_eq_self ht]

private theorem heatStep_inH2_and_bound {ν τ : ℝ} (hν : 0 ≤ ν) (hτ : 0 ≤ τ)
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

/-- **THEOREM 1 OF MILESTONE 6B-1 (Mode-wise Continuity of `duhamelRaw`):** (`0 sorryAx`). -/
theorem duhamelRaw_continuous {ν M : ℝ} (u₀ : VecSeq3D)
    {u : ℝ → VecSeq3D} (hu : IsAdmissibleCurve M u) (k : Fin 3 → ℤ) (c : Fin 3) :
    Continuous (fun t : ℝ => duhamelRaw ν u₀ u t k c) := by
  have h_lin : Continuous (fun t : ℝ => (heatMultiplier3D ν t k : ℂ) * u₀ k c) :=
    (Complex.continuous_ofReal.comp (continuous_heatMultiplier3D_time ν k)).mul continuous_const
  have h_fac : ∀ t : ℝ,
      (∫ s in (0 : ℝ)..t, heatSmoothedBilinear6A ν (t - s) (u s) (u s) k c) =
        (heatMultiplier3D ν t k : ℂ) *
          ∫ s in (0 : ℝ)..t, (heatMultiplier3D ν (-s) k : ℂ) * nsBilinear6A (u s) (u s) k c := by
    intro t
    have hpt : (fun s => heatSmoothedBilinear6A ν (t - s) (u s) (u s) k c) =
        (fun s => (heatMultiplier3D ν t k : ℂ) *
          ((heatMultiplier3D ν (-s) k : ℂ) * nsBilinear6A (u s) (u s) k c)) := by
      funext s
      unfold heatSmoothedBilinear6A
      rw [heatMultiplier3D_sub_eq, Complex.ofReal_mul, mul_assoc]
    rw [hpt, intervalIntegral.integral_const_mul]
  have h_integrand : Continuous (fun s : ℝ =>
      (heatMultiplier3D ν (-s) k : ℂ) * nsBilinear6A (u s) (u s) k c) :=
    (Complex.continuous_ofReal.comp
      ((continuous_heatMultiplier3D_time ν k).comp continuous_neg)).mul
      (continuous_nsBilinear6A_of_admissible hu hu k c)
  have h_int : Continuous (fun t : ℝ =>
      ∫ s in (0 : ℝ)..t, heatSmoothedBilinear6A ν (t - s) (u s) (u s) k c) := by
    simp_rw [h_fac]
    exact (Complex.continuous_ofReal.comp (continuous_heatMultiplier3D_time ν k)).mul
      (continuous_integral_upper h_integrand)
  unfold duhamelRaw
  exact h_lin.add h_int

/-- **MAIN THEOREM 2 OF MILESTONE 6B-1 (`H²` Energy Bound for the Duhamel Operator):**
    For `ν > 0, T ≥ 0`, `u₀ ∈ H²`, and any admissible curve `u` with `‖u(t)‖²_{H²} ≤ M`:
    `‖Φ(u)(t)‖²_{H²} ≤ 2 ‖u₀‖²_{H²} + (6784 T / ν) M²` for all `t ∈ ℝ` (`0 sorryAx`). -/
theorem duhamelOp_inH2_and_bound {ν T M : ℝ} (hν : 0 < ν) (hT : 0 ≤ T) (hM : 0 ≤ M)
    {u₀ : VecSeq3D} (hu₀ : InH2Vec u₀) {u : ℝ → VecSeq3D} (hu : IsAdmissibleCurve M u) (t : ℝ) :
    InH2Vec (duhamelOp ν T u₀ u t) ∧
    h2VecNormSq (duhamelOp ν T u₀ u t) ≤ 2 * h2VecNormSq u₀ + (6784 * T / ν) * M ^ 2 := by
  let τ : ℝ := clampT T t
  have hτ_mem : τ ∈ Set.Icc 0 T := clampT_mem_Icc hT t
  have hlin := heatStep_inH2_and_bound (le_of_lt hν) hτ_mem.1 hu₀
  have hG_cont : ∀ (k : Fin 3 → ℤ) (c : Fin 3),
      Continuous (fun s : ℝ => heatSmoothedBilinear6A ν (τ - s) (u s) (u s) k c) := fun k c => by
    unfold heatSmoothedBilinear6A
    exact (Complex.continuous_ofReal.comp
      ((continuous_heatMultiplier3D_time ν k).comp (continuous_const.sub continuous_id))).mul
      (continuous_nsBilinear6A_of_admissible hu hu k c)
  have hint := integral_h2_bound_of_inv_sqrt_decay hτ_mem.1 (K := 848 * M ^ 2 / ν) (by positivity)
    (G := fun s => heatSmoothedBilinear6A ν (τ - s) (u s) (u s)) hG_cont fun s hs => by
    have hτs : 0 < τ - s := sub_pos.mpr hs.2
    have hbd := heatSmoothedBilinear6A_inH2_and_bound hν hτs (hu.h_inH2 s) (hu.h_inH2 s)
    refine ⟨hbd.1, ?_⟩
    have h1 : h2VecNormSq (u s) * h2VecNormSq (u s) ≤ M ^ 2 := by
      have hnn := h2VecNormSq_nonneg (u s)
      have hle := hu.h_bound s
      nlinarith
    have hcoef : 0 ≤ 848 / (ν * (τ - s)) := by positivity
    have h2 : (848 / (ν * (τ - s))) * h2VecNormSq (u s) * h2VecNormSq (u s) ≤
        (848 / (ν * (τ - s))) * M ^ 2 := by
      rw [mul_assoc]; exact mul_le_mul_of_nonneg_left h1 hcoef
    have h3 : (848 / (ν * (τ - s))) * M ^ 2 = (848 * M ^ 2 / ν) / (τ - s) := by
      have hν_ne : ν ≠ 0 := ne_of_gt hν
      have hts_ne : τ - s ≠ 0 := ne_of_gt hτs
      field_simp [hν_ne, hts_ne]
    linarith [hbd.2]
  have hadd := inH2Vec_add hlin.1 hint.1
  have heq_op : duhamelOp ν T u₀ u t =
      (fun k c => (heatMultiplier3D ν τ k : ℂ) * u₀ k c +
        ∫ s in (0 : ℝ)..τ, heatSmoothedBilinear6A ν (τ - s) (u s) (u s) k c) := rfl
  rw [heq_op]
  refine ⟨hadd.1, ?_⟩
  have htau_le : 2 * (4 * τ * (848 * M ^ 2 / ν)) ≤ (6784 * T / ν) * M ^ 2 := by
    have h1 : 2 * (4 * τ * (848 * M ^ 2 / ν)) = (6784 * τ / ν) * M ^ 2 := by ring
    rw [h1]
    have hle : 6784 * τ / ν ≤ 6784 * T / ν :=
      div_le_div_of_nonneg_right (by linarith [hτ_mem.2]) (le_of_lt hν)
    exact mul_le_mul_of_nonneg_right hle (sq_nonneg M)
  linarith [hadd.2, hlin.2, hint.2, htau_le]

/-- **MAIN THEOREM 3 OF MILESTONE 6B-1 (Self-Map of the Closed `H²` Ball):**
    Whenever `4 ‖u₀‖²_{H²} ≤ M` and `54272 T M ≤ ν`, `Φ` maps `IsAdmissibleCurve M` into itself
    (`0 sorryAx`). -/
theorem duhamelOp_self_map {ν T M : ℝ} (hν : 0 < ν) (hT : 0 ≤ T) (hM : 0 ≤ M)
    {u₀ : VecSeq3D} (hu₀ : InH2Vec u₀)
    (hR : 4 * h2VecNormSq u₀ ≤ M) (hsmall : 54272 * T * M ≤ ν)
    {u : ℝ → VecSeq3D} (hu : IsAdmissibleCurve M u) :
    IsAdmissibleCurve M (duhamelOp ν T u₀ u) := by
  refine ⟨fun t => (duhamelOp_inH2_and_bound hν hT hM hu₀ hu t).1, fun t => ?_, fun k c => ?_⟩
  · have hbd := (duhamelOp_inH2_and_bound hν hT hM hu₀ hu t).2
    have hmul : (6784 * T / ν) * M ^ 2 ≤ (1 / 8 : ℝ) * M := by
      have h1 : 6784 * T * M ^ 2 ≤ (1 / 8 : ℝ) * M * ν := by nlinarith
      have h2 := (div_le_iff₀ hν).mpr h1
      have heq : (6784 * T / ν) * M ^ 2 = 6784 * T * M ^ 2 / ν := by ring
      linarith
    linarith
  · exact (duhamelRaw_continuous u₀ hu k c).comp (continuous_clampT T)

/-- **MAIN THEOREM 4 OF MILESTONE 6B-1 (Strict Contraction of `Φ` on the Closed `H²` Ball):**
    If `‖u(s) - v(s)‖²_{H²} ≤ D` uniformly on `ℝ`, then
    `‖Φ(u)(t) - Φ(v)(t)‖²_{H²} ≤ (13568 T M / ν) * D`, and when `54272 T M ≤ ν`,
    `‖Φ(u)(t) - Φ(v)(t)‖²_{H²} ≤ (1/4) * D` (`0 sorryAx`). -/
theorem duhamelOp_contraction {ν T M D : ℝ} (hν : 0 < ν) (hT : 0 ≤ T) (hM : 0 ≤ M) (hD : 0 ≤ D)
    (u₀ : VecSeq3D) {u v : ℝ → VecSeq3D}
    (hu : IsAdmissibleCurve M u) (hv : IsAdmissibleCurve M v)
    (hdiff : ∀ s : ℝ, h2VecNormSq (fun k c => u s k c - v s k c) ≤ D) (t : ℝ) :
    h2VecNormSq (fun k c => duhamelOp ν T u₀ u t k c - duhamelOp ν T u₀ v t k c) ≤
      (13568 * T * M / ν) * D := by
  let τ : ℝ := clampT T t
  have hτ_mem : τ ∈ Set.Icc 0 T := clampT_mem_Icc hT t
  have hG_cont_u : ∀ (k : Fin 3 → ℤ) (c : Fin 3),
      Continuous (fun s : ℝ => heatSmoothedBilinear6A ν (τ - s) (u s) (u s) k c) := fun k c => by
    unfold heatSmoothedBilinear6A
    exact (Complex.continuous_ofReal.comp
      ((continuous_heatMultiplier3D_time ν k).comp (continuous_const.sub continuous_id))).mul
      (continuous_nsBilinear6A_of_admissible hu hu k c)
  have hG_cont_v : ∀ (k : Fin 3 → ℤ) (c : Fin 3),
      Continuous (fun s : ℝ => heatSmoothedBilinear6A ν (τ - s) (v s) (v s) k c) := fun k c => by
    unfold heatSmoothedBilinear6A
    exact (Complex.continuous_ofReal.comp
      ((continuous_heatMultiplier3D_time ν k).comp (continuous_const.sub continuous_id))).mul
      (continuous_nsBilinear6A_of_admissible hv hv k c)
  have hsub_eq : (fun k c => duhamelOp ν T u₀ u t k c - duhamelOp ν T u₀ v t k c) =
      (fun k c => ∫ s in (0 : ℝ)..τ,
        (heatSmoothedBilinear6A ν (τ - s) (u s) (u s) k c -
         heatSmoothedBilinear6A ν (τ - s) (v s) (v s) k c)) := by
    funext k c
    unfold duhamelOp duhamelRaw
    change ((heatMultiplier3D ν τ k : ℂ) * u₀ k c +
        ∫ s in (0 : ℝ)..τ, heatSmoothedBilinear6A ν (τ - s) (u s) (u s) k c) -
      ((heatMultiplier3D ν τ k : ℂ) * u₀ k c +
        ∫ s in (0 : ℝ)..τ, heatSmoothedBilinear6A ν (τ - s) (v s) (v s) k c) = _
    rw [add_sub_add_left_eq_sub,
        ← intervalIntegral.integral_sub
          ((hG_cont_u k c).intervalIntegrable 0 τ)
          ((hG_cont_v k c).intervalIntegrable 0 τ)]
  rw [hsub_eq]
  have hint := integral_h2_bound_of_inv_sqrt_decay hτ_mem.1 (K := 3392 * M * D / ν) (by positivity)
    (G := fun s k c =>
      heatSmoothedBilinear6A ν (τ - s) (u s) (u s) k c -
      heatSmoothedBilinear6A ν (τ - s) (v s) (v s) k c)
    (fun k c => (hG_cont_u k c).sub (hG_cont_v k c))
    fun s hs => by
      have hτs : 0 < τ - s := sub_pos.mpr hs.2
      have hlip := heatSmoothedBilinear6A_self_sub_lipschitz hν hτs (hu.h_inH2 s) (hv.h_inH2 s)
      refine ⟨hlip.1, ?_⟩
      have hsum_bd : h2VecNormSq (u s) + h2VecNormSq (v s) ≤ 2 * M := by
        linarith [hu.h_bound s, hv.h_bound s]
      have hd_bd : h2VecNormSq (fun k c => u s k c - v s k c) ≤ D := hdiff s
      have hd_nn : 0 ≤ h2VecNormSq (fun k c => u s k c - v s k c) := h2VecNormSq_nonneg _
      have hsum_nn : 0 ≤ h2VecNormSq (u s) + h2VecNormSq (v s) :=
        add_nonneg (h2VecNormSq_nonneg _) (h2VecNormSq_nonneg _)
      have hprod : (h2VecNormSq (u s) + h2VecNormSq (v s)) *
          h2VecNormSq (fun k c => u s k c - v s k c) ≤ (2 * M) * D := by nlinarith
      have hcoef : 0 ≤ 1696 / (ν * (τ - s)) := by positivity
      have h1 : (1696 / (ν * (τ - s))) * (h2VecNormSq (u s) + h2VecNormSq (v s)) *
          h2VecNormSq (fun k c => u s k c - v s k c) ≤
          (1696 / (ν * (τ - s))) * ((2 * M) * D) := by
        rw [mul_assoc]; exact mul_le_mul_of_nonneg_left hprod hcoef
      have h2 : (1696 / (ν * (τ - s))) * ((2 * M) * D) = (3392 * M * D / ν) / (τ - s) := by
        have hν_ne : ν ≠ 0 := ne_of_gt hν
        have hts_ne : τ - s ≠ 0 := ne_of_gt hτs
        field_simp [hν_ne, hts_ne]; ring
      linarith [hlip.2]
  have htau_le : 4 * τ * (3392 * M * D / ν) ≤ (13568 * T * M / ν) * D := by
    have h1 : 4 * τ * (3392 * M * D / ν) = (13568 * τ * M / ν) * D := by ring
    rw [h1]
    have hle : 13568 * τ * M / ν ≤ 13568 * T * M / ν :=
      div_le_div_of_nonneg_right (by nlinarith [hτ_mem.2]) (le_of_lt hν)
    exact mul_le_mul_of_nonneg_right hle hD
  exact le_trans hint.2 htau_le

theorem duhamelOp_contraction_quarter {ν T M D : ℝ} (hν : 0 < ν) (hT : 0 ≤ T) (hM : 0 ≤ M)
    (hD : 0 ≤ D) (hsmall : 54272 * T * M ≤ ν)
    (u₀ : VecSeq3D) {u v : ℝ → VecSeq3D}
    (hu : IsAdmissibleCurve M u) (hv : IsAdmissibleCurve M v)
    (hdiff : ∀ s : ℝ, h2VecNormSq (fun k c => u s k c - v s k c) ≤ D) (t : ℝ) :
    h2VecNormSq (fun k c => duhamelOp ν T u₀ u t k c - duhamelOp ν T u₀ v t k c) ≤
      (1 / 4 : ℝ) * D := by
  have hbd := duhamelOp_contraction hν hT hM hD u₀ hu hv hdiff t
  have hcoef : 13568 * T * M / ν ≤ 1 / 4 := by
    rw [div_le_iff₀ hν]; linarith
  exact le_trans hbd (mul_le_mul_of_nonneg_right hcoef hD)

-- ============================================================================
-- SECTION 4: PRESERVATION OF SOLENOIDALITY, REAL SYMMETRY & MOMENTUM
-- ============================================================================

private theorem integral_add3_complex {a b : ℝ} {f₀ f₁ f₂ : ℝ → ℂ}
    (hf₀ : Continuous f₀) (hf₁ : Continuous f₁) (hf₂ : Continuous f₂) :
    (∫ s in a..b, f₀ s) + (∫ s in a..b, f₁ s) + (∫ s in a..b, f₂ s) =
      ∫ s in a..b, (f₀ s + f₁ s + f₂ s) := by
  have hf01 : Continuous (fun s => f₀ s + f₁ s) := hf₀.add hf₁
  rw [← intervalIntegral.integral_add (hf₀.intervalIntegrable a b) (hf₁.intervalIntegrable a b),
      ← intervalIntegral.integral_add (hf01.intervalIntegrable a b) (hf₂.intervalIntegrable a b)]

private theorem duhamelOp_solenoidal {ν T M : ℝ}
    {u₀ : VecSeq3D} (hsol₀ : IsSolenoidal u₀)
    {u : ℝ → VecSeq3D} (hu : IsAdmissibleCurve M u) (t : ℝ) :
    IsSolenoidal (duhamelOp ν T u₀ u t) := by
  let τ : ℝ := clampT T t
  intro k
  have hG_cont : ∀ c : Fin 3,
      Continuous (fun s : ℝ => heatSmoothedBilinear6A ν (τ - s) (u s) (u s) k c) := fun c => by
    unfold heatSmoothedBilinear6A
    exact (Complex.continuous_ofReal.comp
      ((continuous_heatMultiplier3D_time ν k).comp (continuous_const.sub continuous_id))).mul
      (continuous_nsBilinear6A_of_admissible hu hu k c)
  have hlin0 : (k 0 : ℂ) * ((heatMultiplier3D ν τ k : ℂ) * u₀ k 0) +
      (k 1 : ℂ) * ((heatMultiplier3D ν τ k : ℂ) * u₀ k 1) +
      (k 2 : ℂ) * ((heatMultiplier3D ν τ k : ℂ) * u₀ k 2) = 0 := by
    have hfac : (k 0 : ℂ) * ((heatMultiplier3D ν τ k : ℂ) * u₀ k 0) +
        (k 1 : ℂ) * ((heatMultiplier3D ν τ k : ℂ) * u₀ k 1) +
        (k 2 : ℂ) * ((heatMultiplier3D ν τ k : ℂ) * u₀ k 2) =
        (heatMultiplier3D ν τ k : ℂ) *
          ((k 0 : ℂ) * u₀ k 0 + (k 1 : ℂ) * u₀ k 1 + (k 2 : ℂ) * u₀ k 2) := by ring
    rw [hfac, hsol₀ k, mul_zero]
  have hint0 : (k 0 : ℂ) * (∫ s in (0 : ℝ)..τ, heatSmoothedBilinear6A ν (τ - s) (u s) (u s) k 0) +
      (k 1 : ℂ) * (∫ s in (0 : ℝ)..τ, heatSmoothedBilinear6A ν (τ - s) (u s) (u s) k 1) +
      (k 2 : ℂ) * (∫ s in (0 : ℝ)..τ, heatSmoothedBilinear6A ν (τ - s) (u s) (u s) k 2) = 0 := by
    have hc : ∀ c : Fin 3,
        Continuous (fun s : ℝ => (k c : ℂ) * heatSmoothedBilinear6A ν (τ - s) (u s) (u s) k c) :=
      fun c => continuous_const.mul (hG_cont c)
    rw [← intervalIntegral.integral_const_mul (k 0 : ℂ),
        ← intervalIntegral.integral_const_mul (k 1 : ℂ),
        ← intervalIntegral.integral_const_mul (k 2 : ℂ),
        integral_add3_complex (hc 0) (hc 1) (hc 2)]
    have hpt : (fun s => (k 0 : ℂ) * heatSmoothedBilinear6A ν (τ - s) (u s) (u s) k 0 +
        (k 1 : ℂ) * heatSmoothedBilinear6A ν (τ - s) (u s) (u s) k 1 +
        (k 2 : ℂ) * heatSmoothedBilinear6A ν (τ - s) (u s) (u s) k 2) = (fun _ => (0 : ℂ)) :=
      funext fun s => heatSmoothedBilinear6A_solenoidal ν (τ - s) (u s) (u s) k
    rw [hpt, intervalIntegral.integral_zero]
  unfold duhamelOp duhamelRaw
  change (k 0 : ℂ) * ((heatMultiplier3D ν τ k : ℂ) * u₀ k 0 +
        ∫ s in (0 : ℝ)..τ, heatSmoothedBilinear6A ν (τ - s) (u s) (u s) k 0) +
      (k 1 : ℂ) * ((heatMultiplier3D ν τ k : ℂ) * u₀ k 1 +
        ∫ s in (0 : ℝ)..τ, heatSmoothedBilinear6A ν (τ - s) (u s) (u s) k 1) +
      (k 2 : ℂ) * ((heatMultiplier3D ν τ k : ℂ) * u₀ k 2 +
        ∫ s in (0 : ℝ)..τ, heatSmoothedBilinear6A ν (τ - s) (u s) (u s) k 2) = 0
  linear_combination hlin0 + hint0

private theorem duhamelRaw_realSymm {ν τ M : ℝ} (hτ : 0 ≤ τ)
    {u₀ : VecSeq3D} (hsym₀ : IsRealSymm u₀)
    {u : ℝ → VecSeq3D} (hu : IsAdmissibleCurve M u) (hsym_u : ∀ s : ℝ, IsRealSymm (u s)) :
    IsRealSymm (duhamelRaw ν u₀ u τ) := by
  intro k c
  unfold duhamelRaw
  have h1 : starRingEnd ℂ ((heatMultiplier3D ν τ k : ℂ) * u₀ k c) =
      (heatMultiplier3D ν τ (-k) : ℂ) * u₀ (-k) c := by
    rw [map_mul, Complex.conj_ofReal, heatMultiplier3D_neg_6b, hsym₀ k c]
  have h2 : starRingEnd ℂ (∫ s in (0 : ℝ)..τ, heatSmoothedBilinear6A ν (τ - s) (u s) (u s) k c) =
      ∫ s in (0 : ℝ)..τ, heatSmoothedBilinear6A ν (τ - s) (u s) (u s) (-k) c := by
    rw [conj_intervalIntegral_6b hτ]
    exact intervalIntegral.integral_congr fun s _ =>
      heatSmoothedBilinear6A_realSymm ν (τ - s) (hu.h_inH2 s) (hu.h_inH2 s)
        (hsym_u s) (hsym_u s) k c
  rw [map_add, h1, h2]

private theorem duhamelOp_realSymm {ν T M : ℝ} (hT : 0 ≤ T)
    {u₀ : VecSeq3D} (hsym₀ : IsRealSymm u₀)
    {u : ℝ → VecSeq3D} (hu : IsAdmissibleCurve M u) (hsym_u : ∀ s : ℝ, IsRealSymm (u s)) (t : ℝ) :
    IsRealSymm (duhamelOp ν T u₀ u t) :=
  duhamelRaw_realSymm (clampT_mem_Icc hT t).1 hsym₀ hu hsym_u

private theorem duhamelOp_momentum {ν T : ℝ} (u₀ : VecSeq3D) (u : ℝ → VecSeq3D) (t : ℝ) (c : Fin 3) :
    duhamelOp ν T u₀ u t 0 c = u₀ 0 c := by
  let τ : ℝ := clampT T t
  unfold duhamelOp duhamelRaw
  change (heatMultiplier3D ν τ 0 : ℂ) * u₀ 0 c +
    ∫ s in (0 : ℝ)..τ, heatSmoothedBilinear6A ν (τ - s) (u s) (u s) 0 c = u₀ 0 c
  rw [heatMultiplier3D_zero_mode, Complex.ofReal_one, one_mul]
  have h0 : (fun s => heatSmoothedBilinear6A ν (τ - s) (u s) (u s) 0 c) = (fun _ => (0 : ℂ)) :=
    funext fun s => heatSmoothedBilinear6A_zero ν (τ - s) (u s) (u s) c
  rw [h0, intervalIntegral.integral_zero, add_zero]

/-- **THEOREM 5 OF MILESTONE 6B-1 (`Φ` Preserves Solenoidality, Reality Symmetry & Momentum):**
    (`0 sorryAx`). -/
theorem duhamelOp_preserves_structure {ν T M : ℝ} (hT : 0 ≤ T)
    {u₀ : VecSeq3D} (hsol₀ : IsSolenoidal u₀) (hsym₀ : IsRealSymm u₀)
    {u : ℝ → VecSeq3D} (hu : IsAdmissibleCurve M u) (hsym_u : ∀ s : ℝ, IsRealSymm (u s)) (t : ℝ) :
    IsSolenoidal (duhamelOp ν T u₀ u t) ∧
    IsRealSymm (duhamelOp ν T u₀ u t) ∧
    (∀ c : Fin 3, duhamelOp ν T u₀ u t 0 c = u₀ 0 c) :=
  ⟨duhamelOp_solenoidal hsol₀ hu t, duhamelOp_realSymm hT hsym₀ hu hsym_u t,
   duhamelOp_momentum u₀ u t⟩

-- ============================================================================
-- SECTION 5: AXIOM AUDIT TRAIL — MILESTONE 6B STAGE 1 (0 sorryAx)
-- ============================================================================

#print axioms integral_h2_bound_of_inv_sqrt_decay
#print axioms continuous_conv3D_of_uniform_H2
#print axioms duhamelRaw_continuous
#print axioms duhamelOp_inH2_and_bound
#print axioms duhamelOp_self_map
#print axioms duhamelOp_contraction
#print axioms duhamelOp_contraction_quarter
#print axioms duhamelOp_preserves_structure

end GarryDuhamelOperator3D