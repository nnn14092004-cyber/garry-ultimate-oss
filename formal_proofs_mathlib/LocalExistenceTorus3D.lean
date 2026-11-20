import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import DuhamelOperatorTorus3D

/-!
# GARRYULT v4.0.0 — Milestone 6B (Stage 2): Local Existence & Uniqueness of 3D
# Navier–Stokes Solutions on `𝕋³` via Picard Iteration & Banach Fixed Point
# (`T* = ν / (54272 (4 ‖u₀‖²_{H²} + 1)) > 0`), Mode-wise Spectral Navier–Stokes ODE,
# Spectral Pressure Recovery (Poisson Equation) & Continuous Periodic Physical Velocity
# (`0 sorryAx`)
-/

namespace GarryLocalExistence3D

open MeasureTheory Filter Topology GarryReal3DCalculus GarryVorticity3D
  GarryLerayTorus3D GarryLerayEnergyLaw3D GarryPoincareSobolev3D
  GarryFourierSpectral3D GarrySpectralOperators3D GarryParsevalSobolev3D
  GarrySobolevEmbedding3D GarrySpectralAlgebra3D GarrySpectralBilinear3D
  GarryDuhamelOperator3D

-- ============================================================================
-- SECTION 1: ELEMENTARY GEOMETRIC, SUMMABILITY & NORM HELPERS
-- ============================================================================

private theorem finset_sum_le_tsum_6b2 {f : (Fin 3 → ℤ) → ℝ}
    (hf : Summable f) (hf_nn : ∀ k, 0 ≤ f k) (s : Finset (Fin 3 → ℤ)) :
    ∑ k ∈ s, f k ≤ ∑' k, f k := by
  have hind : HasSum (fun k => if k ∈ s then f k else 0) (∑ k ∈ s, f k) := by
    refine tendsto_atTop_of_eventually_const (i₀ := s) fun t ht => ?_
    rw [← Finset.sum_filter, Finset.filter_mem_eq_inter, Finset.inter_eq_right.mpr ht]
  exact hasSum_le (fun k => by split_ifs; exact le_refl _; exact hf_nn k) hind hf.hasSum

private theorem le_tsum_single_6b2 {f : (Fin 3 → ℤ) → ℝ}
    (hf : Summable f) (hf_nn : ∀ k, 0 ≤ f k) (k₀ : Fin 3 → ℤ) :
    f k₀ ≤ ∑' k, f k := by
  simpa using finset_sum_le_tsum_6b2 hf hf_nn {k₀}

private theorem tendsto_finset_sum_6b2 {α : Type*} [DecidableEq α] {ι : Type*} {l : Filter ι}
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

private theorem finset_range_sum_sq_le_two_mul (L : ℕ) (a : ℕ → ℝ) :
    (∑ r ∈ Finset.range L, a r) ^ 2 ≤ 2 * ∑ r ∈ Finset.range L, (2 : ℝ) ^ r * (a r) ^ 2 := by
  induction L generalizing a with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ', Finset.sum_range_succ']
    have hih := ih (fun r => a (r + 1))
    have hshift : ∑ r ∈ Finset.range n, (2 : ℝ) ^ (r + 1) * a (r + 1) ^ 2 =
        2 * ∑ r ∈ Finset.range n, (2 : ℝ) ^ r * a (r + 1) ^ 2 := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun r _ => ?_
      rw [pow_succ]; ring
    rw [pow_zero, one_mul, hshift]
    have hsq : (∑ r ∈ Finset.range n, a (r + 1) + a 0) ^ 2 ≤
        2 * (∑ r ∈ Finset.range n, a (r + 1)) ^ 2 + 2 * (a 0) ^ 2 := by
      nlinarith [sq_nonneg (∑ r ∈ Finset.range n, a (r + 1) - a 0)]
    linarith

private theorem sum_range_half_pow_le_two (L : ℕ) :
    ∑ r ∈ Finset.range L, (1 / 2 : ℝ) ^ r ≤ 2 := by
  have h : ∑ r ∈ Finset.range L, (1 / 2 : ℝ) ^ r = 2 - (1 / 2 : ℝ) ^ L * 2 := by
    induction L with
    | zero => norm_num
    | succ n ih =>
      rw [Finset.sum_range_succ, ih, pow_succ]
      ring
  rw [h]
  have hnn : 0 ≤ (1 / 2 : ℝ) ^ L * 2 := by positivity
  linarith

private theorem eq_zero_of_nonneg_of_le_mul_quarter_pow {x C : ℝ} (hx : 0 ≤ x)
    (h : ∀ n : ℕ, x ≤ C * (1 / 4 : ℝ) ^ n) : x = 0 := by
  have ht : Tendsto (fun n : ℕ => C * (1 / 4 : ℝ) ^ n) atTop (𝓝 (C * 0)) :=
    tendsto_const_nhds.mul
      (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num))
  rw [mul_zero] at ht
  exact le_antisymm (ge_of_tendsto ht (Eventually.of_forall h)) hx

private theorem norm_sq_le_h2VecNormSq {w : VecSeq3D} (hw : InH2Vec w)
    (k : Fin 3 → ℤ) (c : Fin 3) :
    ‖w k c‖ ^ 2 ≤ h2VecNormSq w := by
  have h1 : ‖w k c‖ ^ 2 ≤ h2Weight k * ‖w k c‖ ^ 2 := by
    nlinarith [one_le_h2Weight k, sq_nonneg ‖w k c‖]
  have h2 : h2Weight k * ‖w k c‖ ^ 2 ≤ h2NormSq (fun m => w m c) :=
    le_tsum_single_6b2 (hw c) (fun m => mul_nonneg (le_of_lt (h2Weight_pos m)) (sq_nonneg _)) k
  have h3 : h2NormSq (fun m => w m c) ≤ h2VecNormSq w := by
    unfold h2VecNormSq
    fin_cases c
    · change h2NormSq (fun m => w m 0) ≤ _
      linarith [h2NormSq_nonneg (fun m => w m 1), h2NormSq_nonneg (fun m => w m 2)]
    · change h2NormSq (fun m => w m 1) ≤ _
      linarith [h2NormSq_nonneg (fun m => w m 0), h2NormSq_nonneg (fun m => w m 2)]
    · change h2NormSq (fun m => w m 2) ≤ _
      linarith [h2NormSq_nonneg (fun m => w m 0), h2NormSq_nonneg (fun m => w m 1)]
  linarith

private theorem eq_zero_of_h2VecNormSq_eq_zero {w : VecSeq3D} (hw : InH2Vec w)
    (hz : h2VecNormSq w = 0) (k : Fin 3 → ℤ) (c : Fin 3) : w k c = 0 := by
  have hle := norm_sq_le_h2VecNormSq hw k c
  rw [hz] at hle
  have hsq : ‖w k c‖ ^ 2 = 0 := le_antisymm hle (sq_nonneg _)
  exact norm_eq_zero.mp (sq_eq_zero_iff.mp hsq)

private theorem h2VecNormSq_neg_sub (u v : VecSeq3D) :
    h2VecNormSq (fun k c => u k c - v k c) = h2VecNormSq (fun k c => v k c - u k c) := by
  unfold h2VecNormSq h2NormSq
  have hc : ∀ c : Fin 3,
      (∑' k : Fin 3 → ℤ, h2Weight k * ‖u k c - v k c‖ ^ 2) =
      (∑' k : Fin 3 → ℤ, h2Weight k * ‖v k c - u k c‖ ^ 2) := fun c =>
    tsum_congr fun k => by rw [norm_sub_rev]
  rw [hc 0, hc 1, hc 2]

-- ============================================================================
-- SECTION 2: PICARD ITERATION, GEOMETRIC CAUCHY CONVERGENCE & LIMIT CURVE
-- ============================================================================

/-- Picard iteration sequence `u_{n+1} = Φ(u_n)` initialized at the constant curve `u₀`. -/
noncomputable def picardSeq (ν T : ℝ) (u₀ : VecSeq3D) : ℕ → (ℝ → VecSeq3D)
  | 0 => fun _ => u₀
  | n + 1 => duhamelOp ν T u₀ (picardSeq ν T u₀ n)

/-- Every Picard iterate remains in the closed admissible `H²` ball `IsAdmissibleCurve M`. -/
theorem picardSeq_admissible {ν T M : ℝ} (hν : 0 < ν) (hT : 0 ≤ T) (hM : 0 ≤ M)
    {u₀ : VecSeq3D} (hu₀ : InH2Vec u₀)
    (hR : 4 * h2VecNormSq u₀ ≤ M) (hsmall : 54272 * T * M ≤ ν) (n : ℕ) :
    IsAdmissibleCurve M (picardSeq ν T u₀ n) := by
  induction n with
  | zero =>
    exact ⟨fun _ => hu₀, fun _ => by change h2VecNormSq u₀ ≤ M; linarith [h2VecNormSq_nonneg u₀],
      fun _ _ => continuous_const⟩
  | succ k ih =>
    exact duhamelOp_self_map hν hT hM hu₀ hR hsmall ih

/-- Every Picard iterate preserves solenoidality, reality symmetry, and total momentum. -/
theorem picardSeq_structure {ν T M : ℝ} (hν : 0 < ν) (hT : 0 ≤ T) (hM : 0 ≤ M)
    {u₀ : VecSeq3D} (hu₀ : InH2Vec u₀) (hsol₀ : IsSolenoidal u₀) (hsym₀ : IsRealSymm u₀)
    (hR : 4 * h2VecNormSq u₀ ≤ M) (hsmall : 54272 * T * M ≤ ν) (n : ℕ) (t : ℝ) :
    IsSolenoidal (picardSeq ν T u₀ n t) ∧
    IsRealSymm (picardSeq ν T u₀ n t) ∧
    (∀ c : Fin 3, picardSeq ν T u₀ n t 0 c = u₀ 0 c) := by
  induction n generalizing t with
  | zero => exact ⟨hsol₀, hsym₀, fun _ => rfl⟩
  | succ k ih =>
    exact duhamelOp_preserves_structure hT hsol₀ hsym₀
      (picardSeq_admissible hν hT hM hu₀ hR hsmall k) (fun s => (ih s).2.1) t

/-- **Geometric Contraction Bound for Successive Picard Iterates:**
    `‖u_{n+1}(t) - u_n(t)‖²_{H²} ≤ 4 M (1/4)^n` for all `n ∈ ℕ, t ∈ ℝ` (`0 sorryAx`). -/
theorem picardSeq_diff_bound {ν T M : ℝ} (hν : 0 < ν) (hT : 0 ≤ T) (hM : 0 ≤ M)
    {u₀ : VecSeq3D} (hu₀ : InH2Vec u₀)
    (hR : 4 * h2VecNormSq u₀ ≤ M) (hsmall : 54272 * T * M ≤ ν) (n : ℕ) (t : ℝ) :
    h2VecNormSq (fun k c => picardSeq ν T u₀ (n + 1) t k c - picardSeq ν T u₀ n t k c) ≤
      (4 * M) * (1 / 4 : ℝ) ^ n := by
  induction n generalizing t with
  | zero =>
    have h0 := picardSeq_admissible hν hT hM hu₀ hR hsmall 0
    have h1 := picardSeq_admissible hν hT hM hu₀ hR hsmall 1
    have hsub := (inH2Vec_sub (h1.h_inH2 t) (h0.h_inH2 t)).2
    rw [pow_zero, mul_one]
    linarith [h1.h_bound t, h0.h_bound t]
  | succ m ih =>
    have hbd := duhamelOp_contraction_quarter hν hT hM (by positivity : 0 ≤ (4 * M) * (1 / 4 : ℝ) ^ m)
      hsmall u₀
      (picardSeq_admissible hν hT hM hu₀ hR hsmall (m + 1))
      (picardSeq_admissible hν hT hM hu₀ hR hsmall m)
      ih t
    have heq : (1 / 4 : ℝ) * ((4 * M) * (1 / 4 : ℝ) ^ m) = (4 * M) * (1 / 4 : ℝ) ^ (m + 1) := by
      rw [pow_succ]; ring
    change h2VecNormSq (fun k c => duhamelOp ν T u₀ (picardSeq ν T u₀ (m + 1)) t k c -
      duhamelOp ν T u₀ (picardSeq ν T u₀ m) t k c) ≤ _
    linarith

private theorem picardSeq_diff_mode_bound {ν T M : ℝ} (hν : 0 < ν) (hT : 0 ≤ T) (hM : 0 ≤ M)
    {u₀ : VecSeq3D} (hu₀ : InH2Vec u₀)
    (hR : 4 * h2VecNormSq u₀ ≤ M) (hsmall : 54272 * T * M ≤ ν)
    (n : ℕ) (t : ℝ) (k : Fin 3 → ℤ) (c : Fin 3) :
    ‖picardSeq ν T u₀ (n + 1) t k c - picardSeq ν T u₀ n t k c‖ ≤
      2 * Real.sqrt M * (1 / 2 : ℝ) ^ n := by
  have hadm1 := picardSeq_admissible hν hT hM hu₀ hR hsmall (n + 1)
  have hadm0 := picardSeq_admissible hν hT hM hu₀ hR hsmall n
  have hsub_in := (inH2Vec_sub (hadm1.h_inH2 t) (hadm0.h_inH2 t)).1
  have hsq1 := norm_sq_le_h2VecNormSq hsub_in k c
  have hsq2 := picardSeq_diff_bound hν hT hM hu₀ hR hsmall n t
  have hsq_rhs : (2 * Real.sqrt M * (1 / 2 : ℝ) ^ n) ^ 2 = (4 * M) * (1 / 4 : ℝ) ^ n := by
    have hpow : ((1 / 2 : ℝ) ^ n) ^ 2 = (1 / 4 : ℝ) ^ n := by
      rw [← pow_mul, mul_comm, pow_mul]
      norm_num
    rw [mul_pow, mul_pow, Real.sq_sqrt hM, hpow]
    ring
  have hlhs_nn : 0 ≤ ‖picardSeq ν T u₀ (n + 1) t k c - picardSeq ν T u₀ n t k c‖ := norm_nonneg _
  have hrhs_nn : 0 ≤ 2 * Real.sqrt M * (1 / 2 : ℝ) ^ n := by positivity
  nlinarith

/-- Explicit telescoping limit of the Picard iteration sequence. -/
noncomputable def picardLimit (ν T : ℝ) (u₀ : VecSeq3D) (t : ℝ) : VecSeq3D :=
  fun k c =>
    u₀ k c + ∑' n : ℕ, (picardSeq ν T u₀ (n + 1) t k c - picardSeq ν T u₀ n t k c)

/-- Mode-wise convergence `picardSeq n t k c → picardLimit t k c` and continuity in `t`. -/
theorem picardLimit_tendsto_and_continuous {ν T M : ℝ} (hν : 0 < ν) (hT : 0 ≤ T) (hM : 0 ≤ M)
    {u₀ : VecSeq3D} (hu₀ : InH2Vec u₀)
    (hR : 4 * h2VecNormSq u₀ ≤ M) (hsmall : 54272 * T * M ≤ ν)
    (k : Fin 3 → ℤ) (c : Fin 3) :
    (∀ t : ℝ, Tendsto (fun n : ℕ => picardSeq ν T u₀ n t k c) atTop
      (𝓝 (picardLimit ν T u₀ t k c))) ∧
    Continuous (fun t : ℝ => picardLimit ν T u₀ t k c) := by
  have hgeom : Summable (fun n : ℕ => 2 * Real.sqrt M * (1 / 2 : ℝ) ^ n) :=
    (summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left (2 * Real.sqrt M)
  constructor
  · intro t
    have hsumm_norm : Summable (fun n : ℕ =>
        ‖picardSeq ν T u₀ (n + 1) t k c - picardSeq ν T u₀ n t k c‖) :=
      Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
        (fun n => picardSeq_diff_mode_bound hν hT hM hu₀ hR hsmall n t k c) hgeom
    have hhas := (Summable.of_norm hsumm_norm).hasSum.tendsto_sum_nat
    have ht_add := tendsto_const_nhds (x := u₀ k c) |>.add hhas
    have htele : (fun N : ℕ => u₀ k c +
        ∑ n ∈ Finset.range N, (picardSeq ν T u₀ (n + 1) t k c - picardSeq ν T u₀ n t k c)) =
        (fun N : ℕ => picardSeq ν T u₀ N t k c) := by
      funext N
      rw [Finset.sum_range_sub (fun n => picardSeq ν T u₀ n t k c) N]
      change u₀ k c + (picardSeq ν T u₀ N t k c - u₀ k c) = picardSeq ν T u₀ N t k c
      ring
    rwa [htele] at ht_add
  · unfold picardLimit
    refine continuous_const.add ?_
    refine continuous_tsum (fun n =>
      ((picardSeq_admissible hν hT hM hu₀ hR hsmall (n + 1)).h_cont k c).sub
        ((picardSeq_admissible hν hT hM hu₀ hR hsmall n).h_cont k c)) hgeom fun n t => ?_
    exact picardSeq_diff_mode_bound hν hT hM hu₀ hR hsmall n t k c

/-- **THEOREM 1 OF MILESTONE 6B-2 (Admissibility & `H²` Convergence Rate of `picardLimit`):**
    `u* = picardLimit` satisfies `IsAdmissibleCurve M u*` and
    `‖u*(t) - u_N(t)‖²_{H²} ≤ 16 M (1/4)^N` for all `N ∈ ℕ, t ∈ ℝ` (`0 sorryAx`). -/
theorem picardLimit_admissible_and_rate {ν T M : ℝ} (hν : 0 < ν) (hT : 0 ≤ T) (hM : 0 ≤ M)
    {u₀ : VecSeq3D} (hu₀ : InH2Vec u₀)
    (hR : 4 * h2VecNormSq u₀ ≤ M) (hsmall : 54272 * T * M ≤ ν) :
    IsAdmissibleCurve M (picardLimit ν T u₀) ∧
    (∀ (N : ℕ) (t : ℝ),
      h2VecNormSq (fun k c => picardLimit ν T u₀ t k c - picardSeq ν T u₀ N t k c) ≤
        (16 * M) * (1 / 4 : ℝ) ^ N) := by
  have hfin_bound : ∀ (t : ℝ) (S : Finset (Fin 3 → ℤ)),
      ∑ k ∈ S, h2Weight k * vecNormSqC (picardLimit ν T u₀ t k) ≤ M := by
    intro t S
    have h_le_n : ∀ n : ℕ, ∑ k ∈ S, h2Weight k * vecNormSqC (picardSeq ν T u₀ n t k) ≤ M := by
      intro n
      have hadm := picardSeq_admissible hν hT hM hu₀ hR hsmall n
      have hhas := hasSum_h2VecNormSq (hadm.h_inH2 t)
      have h1 := finset_sum_le_tsum_6b2 hhas.summable
        (fun k => mul_nonneg (le_of_lt (h2Weight_pos k)) (vecNormSqC_nonneg _)) S
      rw [hhas.tsum_eq] at h1
      exact le_trans h1 (hadm.h_bound t)
    have htend : Tendsto (fun n : ℕ => ∑ k ∈ S, h2Weight k * vecNormSqC (picardSeq ν T u₀ n t k))
        atTop (𝓝 (∑ k ∈ S, h2Weight k * vecNormSqC (picardLimit ν T u₀ t k))) := by
      refine tendsto_finset_sum_6b2 S
        (fun k n => h2Weight k * vecNormSqC (picardSeq ν T u₀ n t k))
        (fun k => h2Weight k * vecNormSqC (picardLimit ν T u₀ t k)) fun k _ => ?_
      have htc : ∀ c : Fin 3, Tendsto (fun n : ℕ => ‖picardSeq ν T u₀ n t k c‖ ^ 2) atTop
          (𝓝 (‖picardLimit ν T u₀ t k c‖ ^ 2)) := fun c =>
        ((picardLimit_tendsto_and_continuous hν hT hM hu₀ hR hsmall k c).1 t).norm.pow 2
      exact tendsto_const_nhds.mul (((htc 0).add (htc 1)).add (htc 2))
    exact le_of_tendsto htend (Eventually.of_forall h_le_n)
  have hlim_inH2 : ∀ t : ℝ, InH2Vec (picardLimit ν T u₀ t) := by
    intro t c
    refine summable_of_sum_le (c := M)
      (fun k => mul_nonneg (le_of_lt (h2Weight_pos k)) (sq_nonneg _)) fun S => ?_
    have hle : ∑ k ∈ S, h2Weight k * ‖picardLimit ν T u₀ t k c‖ ^ 2 ≤
        ∑ k ∈ S, h2Weight k * vecNormSqC (picardLimit ν T u₀ t k) := by
      refine Finset.sum_le_sum fun k _ => mul_le_mul_of_nonneg_left ?_ (le_of_lt (h2Weight_pos k))
      unfold vecNormSqC
      fin_cases c
      · change ‖picardLimit ν T u₀ t k 0‖ ^ 2 ≤ _
        linarith [sq_nonneg ‖picardLimit ν T u₀ t k 1‖, sq_nonneg ‖picardLimit ν T u₀ t k 2‖]
      · change ‖picardLimit ν T u₀ t k 1‖ ^ 2 ≤ _
        linarith [sq_nonneg ‖picardLimit ν T u₀ t k 0‖, sq_nonneg ‖picardLimit ν T u₀ t k 2‖]
      · change ‖picardLimit ν T u₀ t k 2‖ ^ 2 ≤ _
        linarith [sq_nonneg ‖picardLimit ν T u₀ t k 0‖, sq_nonneg ‖picardLimit ν T u₀ t k 1‖]
    exact le_trans hle (hfin_bound t S)
  have hadm_lim : IsAdmissibleCurve M (picardLimit ν T u₀) :=
    ⟨hlim_inH2,
     fun t => le_of_tendsto (hasSum_h2VecNormSq (hlim_inH2 t)) (Eventually.of_forall (hfin_bound t)),
     fun k c => (picardLimit_tendsto_and_continuous hν hT hM hu₀ hR hsmall k c).2⟩
  refine ⟨hadm_lim, fun N t => ?_⟩
  let err : VecSeq3D := fun k c => picardLimit ν T u₀ t k c - picardSeq ν T u₀ N t k c
  have herr_in : InH2Vec err :=
    (inH2Vec_sub (hlim_inH2 t) ((picardSeq_admissible hν hT hM hu₀ hR hsmall N).h_inH2 t)).1
  have hfin_err : ∀ S : Finset (Fin 3 → ℤ),
      ∑ k ∈ S, h2Weight k * vecNormSqC (err k) ≤ (16 * M) * (1 / 4 : ℝ) ^ N := by
    intro S
    let diffN : ℕ → VecSeq3D := fun L k c =>
      picardSeq ν T u₀ (N + L) t k c - picardSeq ν T u₀ N t k c
    have h_le_L : ∀ L : ℕ,
        ∑ k ∈ S, h2Weight k * vecNormSqC (diffN L k) ≤ (16 * M) * (1 / 4 : ℝ) ^ N := by
      intro L
      let step : ℕ → VecSeq3D := fun r k c =>
        picardSeq ν T u₀ (N + r + 1) t k c - picardSeq ν T u₀ (N + r) t k c
      have hcomp_sq : ∀ (k : Fin 3 → ℤ) (c : Fin 3),
          ‖diffN L k c‖ ^ 2 ≤
            2 * ∑ r ∈ Finset.range L, (2 : ℝ) ^ r * ‖step r k c‖ ^ 2 := by
        intro k c
        have htele : diffN L k c = ∑ r ∈ Finset.range L, step r k c := by
          dsimp only [diffN, step]
          have h := Finset.sum_range_sub (fun r => picardSeq ν T u₀ (N + r) t k c) L
          simpa [Nat.add_assoc] using h.symm
        have htri : ‖diffN L k c‖ ≤ ∑ r ∈ Finset.range L, ‖step r k c‖ := by
          rw [htele]; exact norm_sum_le _ _
        have hnn : 0 ≤ ‖diffN L k c‖ := norm_nonneg _
        have hsq1 : ‖diffN L k c‖ ^ 2 ≤ (∑ r ∈ Finset.range L, ‖step r k c‖) ^ 2 := by nlinarith
        exact le_trans hsq1 (finset_range_sum_sq_le_two_mul L fun r => ‖step r k c‖)
      have hvec_sq : ∀ k : Fin 3 → ℤ,
          h2Weight k * vecNormSqC (diffN L k) ≤
            2 * ∑ r ∈ Finset.range L, (2 : ℝ) ^ r * (h2Weight k * vecNormSqC (step r k)) := by
        intro k
        have h0 := hcomp_sq k 0
        have h1 := hcomp_sq k 1
        have h2 := hcomp_sq k 2
        have hadd3 : (∑ r ∈ Finset.range L, (2 : ℝ) ^ r * ‖step r k 0‖ ^ 2) +
            (∑ r ∈ Finset.range L, (2 : ℝ) ^ r * ‖step r k 1‖ ^ 2) +
            (∑ r ∈ Finset.range L, (2 : ℝ) ^ r * ‖step r k 2‖ ^ 2) =
            ∑ r ∈ Finset.range L, (2 : ℝ) ^ r * vecNormSqC (step r k) := by
          rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl fun r _ => ?_; unfold vecNormSqC; ring
        have hv : vecNormSqC (diffN L k) ≤
            2 * ∑ r ∈ Finset.range L, (2 : ℝ) ^ r * vecNormSqC (step r k) := by
          have h123 : ‖diffN L k 0‖ ^ 2 + ‖diffN L k 1‖ ^ 2 + ‖diffN L k 2‖ ^ 2 ≤
              2 * ((∑ r ∈ Finset.range L, (2 : ℝ) ^ r * ‖step r k 0‖ ^ 2) +
                   (∑ r ∈ Finset.range L, (2 : ℝ) ^ r * ‖step r k 1‖ ^ 2) +
                   (∑ r ∈ Finset.range L, (2 : ℝ) ^ r * ‖step r k 2‖ ^ 2)) := by
            linarith [h0, h1, h2]
          rw [hadd3] at h123
          exact h123
        have hmul := mul_le_mul_of_nonneg_left hv (le_of_lt (h2Weight_pos k))
        have hpush : h2Weight k * (2 * ∑ r ∈ Finset.range L, (2 : ℝ) ^ r * vecNormSqC (step r k)) =
            2 * ∑ r ∈ Finset.range L, (2 : ℝ) ^ r * (h2Weight k * vecNormSqC (step r k)) := by
          rw [← mul_assoc, mul_comm (h2Weight k) 2, mul_assoc, Finset.mul_sum]
          congr 1; refine Finset.sum_congr rfl fun r _ => ?_; ring
        linarith
      have hsumS : ∑ k ∈ S, h2Weight k * vecNormSqC (diffN L k) ≤
          2 * ∑ r ∈ Finset.range L,
            (2 : ℝ) ^ r * (∑ k ∈ S, h2Weight k * vecNormSqC (step r k)) := by
        have h1 := Finset.sum_le_sum fun k (_ : k ∈ S) => hvec_sq k
        rw [← Finset.mul_sum, Finset.sum_comm] at h1
        have hfac : ∑ r ∈ Finset.range L, ∑ k ∈ S, (2 : ℝ) ^ r * (h2Weight k * vecNormSqC (step r k)) =
            ∑ r ∈ Finset.range L, (2 : ℝ) ^ r * (∑ k ∈ S, h2Weight k * vecNormSqC (step r k)) :=
          Finset.sum_congr rfl fun r _ => (Finset.mul_sum _ _ _).symm
        rwa [hfac] at h1
      have hstep_bd : ∀ r ∈ Finset.range L,
          (2 : ℝ) ^ r * (∑ k ∈ S, h2Weight k * vecNormSqC (step r k)) ≤
            ((4 * M) * (1 / 4 : ℝ) ^ N) * (1 / 2 : ℝ) ^ r := by
        intro r _
        have hstep_in := (inH2Vec_sub
          ((picardSeq_admissible hν hT hM hu₀ hR hsmall (N + r + 1)).h_inH2 t)
          ((picardSeq_admissible hν hT hM hu₀ hR hsmall (N + r)).h_inH2 t)).1
        have hhas := hasSum_h2VecNormSq hstep_in
        have hS_le : ∑ k ∈ S, h2Weight k * vecNormSqC (step r k) ≤ h2VecNormSq (step r) := by
          have h := finset_sum_le_tsum_6b2 hhas.summable
            (fun k => mul_nonneg (le_of_lt (h2Weight_pos k)) (vecNormSqC_nonneg _)) S
          rwa [hhas.tsum_eq] at h
        have hdiff_le : h2VecNormSq (step r) ≤ (4 * M) * (1 / 4 : ℝ) ^ (N + r) :=
          picardSeq_diff_bound hν hT hM hu₀ hR hsmall (N + r) t
        have hmul := mul_le_mul_of_nonneg_left (le_trans hS_le hdiff_le) (by positivity : (0 : ℝ) ≤ (2 : ℝ) ^ r)
        have hpow : (2 : ℝ) ^ r * ((4 * M) * (1 / 4 : ℝ) ^ (N + r)) =
            ((4 * M) * (1 / 4 : ℝ) ^ N) * (1 / 2 : ℝ) ^ r := by
          rw [pow_add]
          have h24 : (2 : ℝ) ^ r * (1 / 4 : ℝ) ^ r = (1 / 2 : ℝ) ^ r := by
            rw [← mul_pow]; norm_num
          calc (2 : ℝ) ^ r * ((4 * M) * ((1 / 4 : ℝ) ^ N * (1 / 4 : ℝ) ^ r))
              = ((4 * M) * (1 / 4 : ℝ) ^ N) * ((2 : ℝ) ^ r * (1 / 4 : ℝ) ^ r) := by ring
            _ = ((4 * M) * (1 / 4 : ℝ) ^ N) * (1 / 2 : ℝ) ^ r := by rw [h24]
        linarith
      have hsum_r := Finset.sum_le_sum hstep_bd
      rw [← Finset.mul_sum] at hsum_r
      have hgeom_r : ((4 * M) * (1 / 4 : ℝ) ^ N) * ∑ r ∈ Finset.range L, (1 / 2 : ℝ) ^ r ≤
          ((4 * M) * (1 / 4 : ℝ) ^ N) * 2 :=
        mul_le_mul_of_nonneg_left (sum_range_half_pow_le_two L) (by positivity)
      linarith
    have htend : Tendsto (fun L : ℕ => ∑ k ∈ S, h2Weight k * vecNormSqC (diffN L k))
        atTop (𝓝 (∑ k ∈ S, h2Weight k * vecNormSqC (err k))) := by
      refine tendsto_finset_sum_6b2 S
        (fun k L => h2Weight k * vecNormSqC (diffN L k))
        (fun k => h2Weight k * vecNormSqC (err k)) fun k _ => ?_
      have htc : ∀ c : Fin 3, Tendsto (fun L : ℕ => ‖diffN L k c‖ ^ 2) atTop (𝓝 (‖err k c‖ ^ 2)) := by
        intro c
        have ht1 : Tendsto (fun L : ℕ => picardSeq ν T u₀ (N + L) t k c) atTop
            (𝓝 (picardLimit ν T u₀ t k c)) := by
          have h := ((picardLimit_tendsto_and_continuous hν hT hM hu₀ hR hsmall k c).1 t).comp
            (tendsto_add_atTop_nat N)
          have heq : ((fun n => picardSeq ν T u₀ n t k c) ∘ (fun L => L + N)) =
              (fun L => picardSeq ν T u₀ (N + L) t k c) :=
            funext fun L => by simp only [Function.comp_apply, Nat.add_comm]
          rwa [heq] at h
        have hsub_t : Tendsto (fun L : ℕ => picardSeq ν T u₀ (N + L) t k c - picardSeq ν T u₀ N t k c)
            atTop (𝓝 (picardLimit ν T u₀ t k c - picardSeq ν T u₀ N t k c)) :=
          ht1.sub tendsto_const_nhds
        exact hsub_t.norm.pow 2
      exact tendsto_const_nhds.mul (((htc 0).add (htc 1)).add (htc 2))
    exact le_of_tendsto htend (Eventually.of_forall h_le_L)
  exact le_of_tendsto (hasSum_h2VecNormSq herr_in) (Eventually.of_forall hfin_err)

-- ============================================================================
-- SECTION 3: BANACH FIXED POINT, STRUCTURE PRESERVATION & UNIQUENESS
-- ============================================================================

/-- **THEOREM 2 OF MILESTONE 6B-2 (Fixed Point & Structure of `picardLimit`):**
    `u* = picardLimit` is an exact fixed point of `duhamelOp`, satisfies `u*(t) = duhamelRaw(u*)(t)`
    for all `t ∈ [0, T]`, `u*(0) = u₀`, and preserves solenoidality, reality symmetry & momentum
    (`0 sorryAx`). -/
theorem picardLimit_fixedPoint_and_structure {ν T M : ℝ} (hν : 0 < ν) (hT : 0 ≤ T) (hM : 0 ≤ M)
    {u₀ : VecSeq3D} (hu₀ : InH2Vec u₀) (hsol₀ : IsSolenoidal u₀) (hsym₀ : IsRealSymm u₀)
    (hR : 4 * h2VecNormSq u₀ ≤ M) (hsmall : 54272 * T * M ≤ ν) :
    (∀ t : ℝ, duhamelOp ν T u₀ (picardLimit ν T u₀) t = picardLimit ν T u₀ t) ∧
    (∀ t ∈ Set.Icc (0 : ℝ) T, picardLimit ν T u₀ t = duhamelRaw ν u₀ (picardLimit ν T u₀) t) ∧
    (picardLimit ν T u₀ 0 = u₀) ∧
    (∀ t : ℝ, IsSolenoidal (picardLimit ν T u₀ t) ∧
              IsRealSymm (picardLimit ν T u₀ t) ∧
              (∀ c : Fin 3, picardLimit ν T u₀ t 0 c = u₀ 0 c)) := by
  have hlim := picardLimit_admissible_and_rate hν hT hM hu₀ hR hsmall
  have hadm_lim := hlim.1
  have hrate := hlim.2
  have hfixed : ∀ t : ℝ, duhamelOp ν T u₀ (picardLimit ν T u₀) t = picardLimit ν T u₀ t := by
    intro t
    have hΦ_adm := duhamelOp_self_map hν hT hM hu₀ hR hsmall hadm_lim
    have hdiff_in := (inH2Vec_sub (hΦ_adm.h_inH2 t) (hadm_lim.h_inH2 t)).1
    have hnorm0 : h2VecNormSq
        (fun k c => duhamelOp ν T u₀ (picardLimit ν T u₀) t k c - picardLimit ν T u₀ t k c) = 0 := by
      refine eq_zero_of_nonneg_of_le_mul_quarter_pow (C := 16 * M) (h2VecNormSq_nonneg _) fun N => ?_
      have hN_adm := picardSeq_admissible hν hT hM hu₀ hR hsmall N
      have hN1_adm := picardSeq_admissible hν hT hM hu₀ hR hsmall (N + 1)
      have hpart1 : h2VecNormSq
          (fun k c => duhamelOp ν T u₀ (picardLimit ν T u₀) t k c -
                      picardSeq ν T u₀ (N + 1) t k c) ≤
          (1 / 4 : ℝ) * ((16 * M) * (1 / 4 : ℝ) ^ N) :=
        duhamelOp_contraction_quarter hν hT hM (by positivity) hsmall u₀ hadm_lim hN_adm (hrate N) t
      have hpart2 : h2VecNormSq
          (fun k c => picardSeq ν T u₀ (N + 1) t k c - picardLimit ν T u₀ t k c) ≤
          (16 * M) * (1 / 4 : ℝ) ^ (N + 1) := by
        rw [h2VecNormSq_neg_sub]; exact hrate (N + 1) t
      have hsplit :
          (fun k c => duhamelOp ν T u₀ (picardLimit ν T u₀) t k c - picardLimit ν T u₀ t k c) =
          (fun k c => (duhamelOp ν T u₀ (picardLimit ν T u₀) t k c - picardSeq ν T u₀ (N + 1) t k c) +
                      (picardSeq ν T u₀ (N + 1) t k c - picardLimit ν T u₀ t k c)) := by
        funext k c; ring
      have htri := (inH2Vec_add
        (inH2Vec_sub (hΦ_adm.h_inH2 t) (hN1_adm.h_inH2 t)).1
        (inH2Vec_sub (hN1_adm.h_inH2 t) (hadm_lim.h_inH2 t)).1).2
      rw [← hsplit] at htri
      have hpow : (16 * M) * (1 / 4 : ℝ) ^ (N + 1) = (4 * M) * (1 / 4 : ℝ) ^ N := by
        rw [pow_succ]; ring
      linarith
    funext k c
    exact sub_eq_zero.mp (eq_zero_of_h2VecNormSq_eq_zero hdiff_in hnorm0 k c)
  have hraw : ∀ t ∈ Set.Icc (0 : ℝ) T,
      picardLimit ν T u₀ t = duhamelRaw ν u₀ (picardLimit ν T u₀) t := fun t ht => by
    rw [← hfixed t, duhamelOp_eq_raw ht]
  have hinit : picardLimit ν T u₀ 0 = u₀ := by
    rw [hraw 0 ⟨le_rfl, hT⟩]
    funext k c
    unfold duhamelRaw
    simp [heatMultiplier3D_zero]
  have hstruct : ∀ t : ℝ, IsSolenoidal (picardLimit ν T u₀ t) ∧
      IsRealSymm (picardLimit ν T u₀ t) ∧
      (∀ c : Fin 3, picardLimit ν T u₀ t 0 c = u₀ 0 c) := by
    intro t
    have hsol : IsSolenoidal (picardLimit ν T u₀ t) := by
      intro k
      have htc : ∀ c : Fin 3, Tendsto (fun n : ℕ => picardSeq ν T u₀ n t k c) atTop
          (𝓝 (picardLimit ν T u₀ t k c)) := fun c =>
        (picardLimit_tendsto_and_continuous hν hT hM hu₀ hR hsmall k c).1 t
      have hcomb : Tendsto (fun n : ℕ =>
          (k 0 : ℂ) * picardSeq ν T u₀ n t k 0 +
          (k 1 : ℂ) * picardSeq ν T u₀ n t k 1 +
          (k 2 : ℂ) * picardSeq ν T u₀ n t k 2) atTop
          (𝓝 ((k 0 : ℂ) * picardLimit ν T u₀ t k 0 +
              (k 1 : ℂ) * picardLimit ν T u₀ t k 1 +
              (k 2 : ℂ) * picardLimit ν T u₀ t k 2)) :=
        ((tendsto_const_nhds.mul (htc 0)).add (tendsto_const_nhds.mul (htc 1))).add
          (tendsto_const_nhds.mul (htc 2))
      have hzero : (fun n : ℕ =>
          (k 0 : ℂ) * picardSeq ν T u₀ n t k 0 +
          (k 1 : ℂ) * picardSeq ν T u₀ n t k 1 +
          (k 2 : ℂ) * picardSeq ν T u₀ n t k 2) = fun _ => (0 : ℂ) :=
        funext fun n => (picardSeq_structure hν hT hM hu₀ hsol₀ hsym₀ hR hsmall n t).1 k
      rw [hzero] at hcomb
      exact tendsto_nhds_unique hcomb tendsto_const_nhds
    have hsym : IsRealSymm (picardLimit ν T u₀ t) := by
      intro k c
      have ht1 := ((picardLimit_tendsto_and_continuous hν hT hM hu₀ hR hsmall k c).1 t)
      have ht1_conj : Tendsto (fun n : ℕ => starRingEnd ℂ (picardSeq ν T u₀ n t k c)) atTop
          (𝓝 (starRingEnd ℂ (picardLimit ν T u₀ t k c))) :=
        (Complex.continuous_conj.tendsto _).comp ht1
      have ht2 := (picardLimit_tendsto_and_continuous hν hT hM hu₀ hR hsmall (-k) c).1 t
      have heq_n : (fun n : ℕ => starRingEnd ℂ (picardSeq ν T u₀ n t k c)) =
          (fun n : ℕ => picardSeq ν T u₀ n t (-k) c) :=
        funext fun n => (picardSeq_structure hν hT hM hu₀ hsol₀ hsym₀ hR hsmall n t).2.1 k c
      rw [heq_n] at ht1_conj
      exact tendsto_nhds_unique ht1_conj ht2
    have hmom : ∀ c : Fin 3, picardLimit ν T u₀ t 0 c = u₀ 0 c := by
      intro c
      have ht0 := (picardLimit_tendsto_and_continuous hν hT hM hu₀ hR hsmall 0 c).1 t
      have heq_n : (fun n : ℕ => picardSeq ν T u₀ n t 0 c) = fun _ => u₀ 0 c :=
        funext fun n => (picardSeq_structure hν hT hM hu₀ hsol₀ hsym₀ hR hsmall n t).2.2 c
      rw [heq_n] at ht0
      exact tendsto_nhds_unique ht0 tendsto_const_nhds
    exact ⟨hsol, hsym, hmom⟩
  exact ⟨hfixed, hraw, hinit, hstruct⟩

/-- **THEOREM 3 OF MILESTONE 6B-2 (Uniqueness of Mild Solutions in `B_M` on `[0, T]`):**
    Any two admissible curves `u, v ∈ IsAdmissibleCurve M` solving `u(t) = duhamelRaw(u)(t)` on
    `[0, T]` coincide identically on `[0, T]` (`0 sorryAx`). -/
private theorem duhamelOp_clamp_eq_of_raw {ν T : ℝ} (hT : 0 ≤ T) (u₀ : VecSeq3D)
    {w : ℝ → VecSeq3D} (hw : ∀ t ∈ Set.Icc (0 : ℝ) T, w t = duhamelRaw ν u₀ w t) (t : ℝ) :
    w (clampT T t) = duhamelOp ν T u₀ (fun s => w (clampT T s)) t := by
  have hτ : clampT T t ∈ Set.Icc (0 : ℝ) T := clampT_mem_Icc hT t
  rw [hw (clampT T t) hτ]
  funext k c
  unfold duhamelOp duhamelRaw
  have hint : (∫ s in (0 : ℝ)..(clampT T t),
        heatSmoothedBilinear6A ν (clampT T t - s) (w s) (w s) k c) =
      ∫ s in (0 : ℝ)..(clampT T t),
        heatSmoothedBilinear6A ν (clampT T t - s) (w (clampT T s)) (w (clampT T s)) k c := by
    refine intervalIntegral.integral_congr fun s hs => ?_
    rw [Set.uIcc_of_le hτ.1] at hs
    have hs_mem : s ∈ Set.Icc (0 : ℝ) T := ⟨hs.1, le_trans hs.2 hτ.2⟩
    rw [clampT_eq_self hs_mem]
  rw [hint]

theorem mild_solution_unique {ν T M : ℝ} (hν : 0 < ν) (hT : 0 ≤ T) (hM : 0 ≤ M)
    (hsmall : 54272 * T * M ≤ ν) (u₀ : VecSeq3D)
    {u v : ℝ → VecSeq3D} (hu : IsAdmissibleCurve M u) (hv : IsAdmissibleCurve M v)
    (hu_sol : ∀ t ∈ Set.Icc (0 : ℝ) T, u t = duhamelRaw ν u₀ u t)
    (hv_sol : ∀ t ∈ Set.Icc (0 : ℝ) T, v t = duhamelRaw ν u₀ v t) :
    ∀ t ∈ Set.Icc (0 : ℝ) T, u t = v t := by
  let u' : ℝ → VecSeq3D := fun t => u (clampT T t)
  let v' : ℝ → VecSeq3D := fun t => v (clampT T t)
  have hu' : IsAdmissibleCurve M u' :=
    ⟨fun t => hu.h_inH2 (clampT T t), fun t => hu.h_bound (clampT T t),
     fun k c => (hu.h_cont k c).comp (continuous_clampT T)⟩
  have hv' : IsAdmissibleCurve M v' :=
    ⟨fun t => hv.h_inH2 (clampT T t), fun t => hv.h_bound (clampT T t),
     fun k c => (hv.h_cont k c).comp (continuous_clampT T)⟩
  have hu'_fix : ∀ t : ℝ, u' t = duhamelOp ν T u₀ u' t := duhamelOp_clamp_eq_of_raw hT u₀ hu_sol
  have hv'_fix : ∀ t : ℝ, v' t = duhamelOp ν T u₀ v' t := duhamelOp_clamp_eq_of_raw hT u₀ hv_sol
  have hdecay : ∀ (n : ℕ) (t : ℝ),
      h2VecNormSq (fun k c => u' t k c - v' t k c) ≤ (4 * M) * (1 / 4 : ℝ) ^ n := by
    intro n
    induction n with
    | zero =>
      intro t
      rw [pow_zero, mul_one]
      have hsub := (inH2Vec_sub (hu'.h_inH2 t) (hv'.h_inH2 t)).2
      linarith [hu'.h_bound t, hv'.h_bound t]
    | succ m ih =>
      intro t
      have hbd := duhamelOp_contraction_quarter hν hT hM (by positivity : 0 ≤ (4 * M) * (1 / 4 : ℝ) ^ m)
        hsmall u₀ hu' hv' ih t
      have heq_f : (fun k c => duhamelOp ν T u₀ u' t k c - duhamelOp ν T u₀ v' t k c) =
          (fun k c => u' t k c - v' t k c) := by
        funext k c; rw [← hu'_fix t, ← hv'_fix t]
      rw [heq_f] at hbd
      have hpow : (1 / 4 : ℝ) * ((4 * M) * (1 / 4 : ℝ) ^ m) = (4 * M) * (1 / 4 : ℝ) ^ (m + 1) := by
        rw [pow_succ]; ring
      linarith
  intro t ht
  have hdiff_in := (inH2Vec_sub (hu'.h_inH2 t) (hv'.h_inH2 t)).1
  have h0 : h2VecNormSq (fun k c => u' t k c - v' t k c) = 0 :=
    eq_zero_of_nonneg_of_le_mul_quarter_pow (h2VecNormSq_nonneg _) (fun n => hdecay n t)
  have heq' : u' t = v' t := by
    funext k c; exact sub_eq_zero.mp (eq_zero_of_h2VecNormSq_eq_zero hdiff_in h0 k c)
  dsimp only [u', v'] at heq'
  rwa [clampT_eq_self ht] at heq'

-- ============================================================================
-- SECTION 4: SPECTRAL PRESSURE RECOVERY & DIFFERENTIATION TO 3D NS ODE
-- ============================================================================

/-- Spectral pressure Fourier coefficient recovered via the 3D pressure Poisson equation
    `-4π² |k|² p̂(k) = -2π i (k · ℱ[(u · ∇)u](k))`. -/
noncomputable def pressureCoeff6B (u : VecSeq3D) (k : Fin 3 → ℤ) : ℂ :=
  if k = 0 then 0
  else (Complex.I / ((2 * Real.pi * kNormSq k : ℝ) : ℂ)) *
    ((k 0 : ℂ) * nsFlux6A u u k 0 + (k 1 : ℂ) * nsFlux6A u u k 1 + (k 2 : ℂ) * nsFlux6A u u k 2)

/-- **Spectral Pressure Poisson Identity:** `-4π² |k|² p̂_k = -2π i (k · F_k)` (`0 sorryAx`). -/
theorem pressureCoeff6B_poisson (u : VecSeq3D) (k : Fin 3 → ℤ) :
    (-4 : ℂ) * (Real.pi : ℂ) ^ 2 * ((kNormSq k : ℝ) : ℂ) * pressureCoeff6B u k =
      -2 * (Real.pi : ℂ) * Complex.I *
        ((k 0 : ℂ) * nsFlux6A u u k 0 + (k 1 : ℂ) * nsFlux6A u u k 1 + (k 2 : ℂ) * nsFlux6A u u k 2) := by
  unfold pressureCoeff6B
  by_cases hk : k = 0
  · subst hk; simp [kNormSq]
  · simp only [hk, ↓reduceIte]
    have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
    have hk_pos : 0 < kNormSq k := kNormSq_pos_of_ne_zero hk
    have hk_ne : ((kNormSq k : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hk_pos)
    have hcast : ((2 * Real.pi * kNormSq k : ℝ) : ℂ) = 2 * (Real.pi : ℂ) * ((kNormSq k : ℝ) : ℂ) := by
      push_cast; ring
    rw [hcast]
    field_simp [hpi, hk_ne]
    ring

/-- **Exact Momentum Splitting Identity:**
    `B(u, u)_k(c) = -F(u, u)_k(c) - 2π i k_c p̂_k` (`0 sorryAx`). -/
theorem nsBilinear6A_eq_neg_flux_sub_grad_pressure (u : VecSeq3D) (k : Fin 3 → ℤ) (c : Fin 3) :
    nsBilinear6A u u k c =
      -nsFlux6A u u k c - 2 * (Real.pi : ℂ) * Complex.I * (k c : ℂ) * pressureCoeff6B u k := by
  unfold nsBilinear6A lerayProj6A pressureCoeff6B
  by_cases hk : k = 0
  · subst hk; simp [nsFlux6A]
  · simp only [hk, ↓reduceIte]
    have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
    have hk_pos : 0 < kNormSq k := kNormSq_pos_of_ne_zero hk
    have hk_ne : ((kNormSq k : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hk_pos)
    have hcast : ((2 * Real.pi * kNormSq k : ℝ) : ℂ) = 2 * (Real.pi : ℂ) * ((kNormSq k : ℝ) : ℂ) := by
      push_cast; ring
    rw [hcast]
    field_simp [hpi, hk_ne]
    ring_nf
    rw [Complex.I_sq]
    ring

private theorem hasDerivAt_heatMultiplier3D_complex (ν : ℝ) (k : Fin 3 → ℤ) (t : ℝ) :
    HasDerivAt (fun s : ℝ => (heatMultiplier3D ν s k : ℂ))
      ((-4 * (Real.pi : ℂ) ^ 2 * (ν : ℂ) * ((kNormSq k : ℝ) : ℂ)) * (heatMultiplier3D ν t k : ℂ)) t := by
  let a : ℝ := -4 * Real.pi ^ 2 * ν * kNormSq k
  have hlin : HasDerivAt (fun s : ℝ => a * s) a t := by
    have h := (hasDerivAt_id t).const_mul a
    rwa [mul_one] at h
  have hexp : HasDerivAt (fun s : ℝ => Real.exp (a * s)) (Real.exp (a * t) * a) t :=
    (Real.hasDerivAt_exp (a * t)).comp t hlin
  have hC := hexp.ofReal_comp
  have hfun : (fun s : ℝ => ((Real.exp (a * s) : ℝ) : ℂ)) =
      (fun s : ℝ => (heatMultiplier3D ν s k : ℂ)) := by
    funext s; unfold heatMultiplier3D; rfl
  have hval : ((Real.exp (a * t) * a : ℝ) : ℂ) =
      ((-4 * (Real.pi : ℂ) ^ 2 * (ν : ℂ) * ((kNormSq k : ℝ) : ℂ)) * (heatMultiplier3D ν t k : ℂ)) := by
    unfold heatMultiplier3D; dsimp only [a]; push_cast; ring
  rwa [hfun, hval] at hC

/-- **THEOREM 4 OF MILESTONE 6B-2 (Exact Mode-wise 3D Navier–Stokes Momentum ODE):**
    Every admissible mild solution `u` on `[0, T]` is differentiable on `(0, T)` at every mode
    `(k, c)` and satisfies the full 3D Navier–Stokes spectral momentum equation with pressure:
    `d/dt û_k(c) = -4π² ν |k|² û_k(c) - ℱ[(u·∇)u]_k(c) - 2π i k_c p̂_k` (`0 sorryAx`). -/
theorem mild_solution_hasDerivAt_spectral_ns3d {ν T M : ℝ}
    (u₀ : VecSeq3D) {u : ℝ → VecSeq3D} (hu : IsAdmissibleCurve M u)
    (hu_sol : ∀ t ∈ Set.Icc (0 : ℝ) T, u t = duhamelRaw ν u₀ u t)
    {t : ℝ} (ht : t ∈ Set.Ioo (0 : ℝ) T) (k : Fin 3 → ℤ) (c : Fin 3) :
    HasDerivAt (fun s : ℝ => u s k c)
      ((-4 * (Real.pi : ℂ) ^ 2 * (ν : ℂ) * ((kNormSq k : ℝ) : ℂ)) * u t k c -
        nsFlux6A (u t) (u t) k c -
        2 * (Real.pi : ℂ) * Complex.I * (k c : ℂ) * pressureCoeff6B (u t) k) t := by
  let g : ℝ → ℂ := fun s =>
    (heatMultiplier3D ν (-s) k : ℂ) * nsBilinear6A (u s) (u s) k c
  have hg_cont : Continuous g := by
    have hmul : Continuous (fun s : ℝ => heatMultiplier3D ν (-s) k) := by
      unfold heatMultiplier3D
      exact Real.continuous_exp.comp (continuous_const.mul continuous_neg)
    exact (Complex.continuous_ofReal.comp hmul).mul (continuous_nsBilinear6A_of_admissible hu hu k c)
  have hraw_eq : ∀ s : ℝ, duhamelRaw ν u₀ u s k c =
      (heatMultiplier3D ν s k : ℂ) * (u₀ k c + ∫ r in (0 : ℝ)..s, g r) := by
    intro s
    unfold duhamelRaw
    have hpt : (fun r => heatSmoothedBilinear6A ν (s - r) (u r) (u r) k c) =
        (fun r => (heatMultiplier3D ν s k : ℂ) * g r) := by
      funext r
      unfold heatSmoothedBilinear6A
      dsimp only [g]
      have hsub : heatMultiplier3D ν (s - r) k =
          heatMultiplier3D ν s k * heatMultiplier3D ν (-r) k := by
        rw [sub_eq_add_neg, heatMultiplier3D_add]
      rw [hsub, Complex.ofReal_mul, mul_assoc]
    rw [hpt, intervalIntegral.integral_const_mul, mul_add]
  have hint_deriv : HasDerivAt (fun s : ℝ => u₀ k c + ∫ r in (0 : ℝ)..s, g r) (g t) t := by
    have h1 := intervalIntegral.integral_hasDerivAt_right (a := (0 : ℝ)) (b := t)
      (hg_cont.intervalIntegrable (μ := volume) 0 t)
      (hg_cont.stronglyMeasurable.stronglyMeasurableAtFilter)
      hg_cont.continuousAt
    exact h1.const_add (u₀ k c)
  have hprod := (hasDerivAt_heatMultiplier3D_complex ν k t).mul hint_deriv
  have hcancel : (heatMultiplier3D ν t k : ℂ) * (heatMultiplier3D ν (-t) k : ℂ) = 1 := by
    rw [← Complex.ofReal_mul, ← heatMultiplier3D_add, add_neg_cancel, heatMultiplier3D_zero,
        Complex.ofReal_one]
  have hderiv_val :
      (-4 * (Real.pi : ℂ) ^ 2 * (ν : ℂ) * ((kNormSq k : ℝ) : ℂ)) * (heatMultiplier3D ν t k : ℂ) *
          (u₀ k c + ∫ r in (0 : ℝ)..t, g r) +
        (heatMultiplier3D ν t k : ℂ) * g t =
      (-4 * (Real.pi : ℂ) ^ 2 * (ν : ℂ) * ((kNormSq k : ℝ) : ℂ)) * u t k c -
        nsFlux6A (u t) (u t) k c -
        2 * (Real.pi : ℂ) * Complex.I * (k c : ℂ) * pressureCoeff6B (u t) k := by
    have hut : u t k c = (heatMultiplier3D ν t k : ℂ) * (u₀ k c + ∫ r in (0 : ℝ)..t, g r) := by
      rw [hu_sol t ⟨le_of_lt ht.1, le_of_lt ht.2⟩, hraw_eq t]
    have hg_term : (heatMultiplier3D ν t k : ℂ) * g t = nsBilinear6A (u t) (u t) k c := by
      dsimp only [g]; rw [← mul_assoc, hcancel, one_mul]
    rw [hg_term, mul_assoc, ← hut, nsBilinear6A_eq_neg_flux_sub_grad_pressure (u t) k c]
    ring
  rw [hderiv_val] at hprod
  refine hprod.congr_of_eventuallyEq ?_
  filter_upwards [Ioo_mem_nhds ht.1 ht.2] with s hs
  change u s k c = (heatMultiplier3D ν s k : ℂ) * (u₀ k c + ∫ r in (0 : ℝ)..s, g r)
  rw [hu_sol s ⟨le_of_lt hs.1, le_of_lt hs.2⟩, hraw_eq s]

-- ============================================================================
-- SECTION 5: MASTER THEOREM OF MILESTONE 6 — LOCAL EXISTENCE & UNIQUENESS ON `𝕋³`
-- ============================================================================

/-- **MASTER THEOREM OF MILESTONE 6 (Unconditional Local Existence & Uniqueness for 3D
    Navier–Stokes on `𝕋³` from Arbitrary `H²` Solenoidal Initial Data, `0 sorryAx`):**
    For EVERY viscosity `ν > 0` and EVERY real, divergence-free initial velocity `u₀ ∈ H²(𝕋³)`,
    setting `M = 4 ‖u₀‖²_{H²} + 1` and `T* = ν / (54272 M) > 0`, there EXISTS a UNIQUE
    admissible solution curve `u : ℝ → VecSeq3D` on `[0, T*]` (with recovered spectral pressure
    `p` and continuous periodic physical-space velocity field `U(t, x) = synthVec3D (u t) x`)
    satisfying:
    1. Exact initial condition `u(0) = u₀` and uniform `H²` bound `‖u(t)‖²_{H²} ≤ M`;
    2. Exact Duhamel mild formulation on `[0, T*]` and mode-wise 3D Navier–Stokes momentum ODE
       with recovered Poisson pressure on `(0, T*)`;
    3. Incompressibility (`IsSolenoidal`), reality (`IsRealSymm`), and momentum conservation;
    4. Continuous `ℤ³`-periodic physical velocity `U(t, ·)` with `|U(t, x)|² ≤ 53 M`;
    5. Uniqueness among all admissible mild solutions in `B_M` on `[0, T*]`. -/
theorem local_existence_uniqueness_ns3d_torus3D
    {ν : ℝ} (hν : 0 < ν) {u₀ : VecSeq3D}
    (hu₀ : InH2Vec u₀) (hsol₀ : IsSolenoidal u₀) (hsym₀ : IsRealSymm u₀) :
    let M : ℝ := 4 * h2VecNormSq u₀ + 1
    let T_star : ℝ := ν / (54272 * M)
    0 < T_star ∧
    ∃ u : ℝ → VecSeq3D,
      IsAdmissibleCurve M u ∧
      u 0 = u₀ ∧
      (∀ t ∈ Set.Icc (0 : ℝ) T_star, u t = duhamelRaw ν u₀ u t) ∧
      (∀ t ∈ Set.Ioo (0 : ℝ) T_star, ∀ (k : Fin 3 → ℤ) (c : Fin 3),
        HasDerivAt (fun s : ℝ => u s k c)
          ((-4 * (Real.pi : ℂ) ^ 2 * (ν : ℂ) * ((kNormSq k : ℝ) : ℂ)) * u t k c -
            nsFlux6A (u t) (u t) k c -
            2 * (Real.pi : ℂ) * Complex.I * (k c : ℂ) * pressureCoeff6B (u t) k) t) ∧
      (∀ (t : ℝ) (k : Fin 3 → ℤ),
        (-4 : ℂ) * (Real.pi : ℂ) ^ 2 * ((kNormSq k : ℝ) : ℂ) * pressureCoeff6B (u t) k =
          -2 * (Real.pi : ℂ) * Complex.I *
            ((k 0 : ℂ) * nsFlux6A (u t) (u t) k 0 +
             (k 1 : ℂ) * nsFlux6A (u t) (u t) k 1 +
             (k 2 : ℂ) * nsFlux6A (u t) (u t) k 2)) ∧
      (∀ t : ℝ, IsSolenoidal (u t) ∧ IsRealSymm (u t) ∧ (∀ c : Fin 3, u t 0 c = u₀ 0 c)) ∧
      (∀ t : ℝ, Continuous (synthVec3D (u t)) ∧ IsPeriodic3D (synthVec3D (u t)) ∧
        (∀ x : R3, dot3D (synthVec3D (u t) x) (synthVec3D (u t) x) ≤ 53 * M)) ∧
      (∀ v : ℝ → VecSeq3D, IsAdmissibleCurve M v →
        (∀ t ∈ Set.Icc (0 : ℝ) T_star, v t = duhamelRaw ν u₀ v t) →
        ∀ t ∈ Set.Icc (0 : ℝ) T_star, v t = u t) := by
  intro M T_star
  have hM_pos : 0 < M := by
    dsimp only [M]; linarith [h2VecNormSq_nonneg u₀]
  have hM_nn : 0 ≤ M := le_of_lt hM_pos
  have hT_pos : 0 < T_star := by
    dsimp only [T_star]; positivity
  have hT_nn : 0 ≤ T_star := le_of_lt hT_pos
  have hR : 4 * h2VecNormSq u₀ ≤ M := by dsimp only [M]; linarith
  have hsmall : 54272 * T_star * M ≤ ν := by
    dsimp only [T_star]
    have hM_ne : M ≠ 0 := ne_of_gt hM_pos
    have heq : 54272 * (ν / (54272 * M)) * M = ν := by field_simp [hM_ne]
    linarith
  have hadm := (picardLimit_admissible_and_rate hν hT_nn hM_nn hu₀ hR hsmall).1
  have hfix := picardLimit_fixedPoint_and_structure hν hT_nn hM_nn hu₀ hsol₀ hsym₀ hR hsmall
  refine ⟨hT_pos, picardLimit ν T_star u₀, hadm, hfix.2.2.1, hfix.2.1, ?_, ?_, hfix.2.2.2, ?_, ?_⟩
  · intro t ht k c
    exact mild_solution_hasDerivAt_spectral_ns3d u₀ hadm hfix.2.1 ht k c
  · intro t k
    exact pressureCoeff6B_poisson (picardLimit ν T_star u₀ t) k
  · intro t
    have hsyn := synthVec3D_continuous_periodic_and_Linf (hadm.h_inH2 t)
    refine ⟨hsyn.1, hsyn.2.1, fun x => ?_⟩
    have hbd := hadm.h_bound t
    linarith [hsyn.2.2 x]
  · intro v hv hv_sol t ht
    exact mild_solution_unique hν hT_nn hM_nn hsmall u₀ hv hadm hv_sol hfix.2.1 t ht

-- ============================================================================
-- SECTION 6: AXIOM AUDIT TRAIL — MILESTONE 6B STAGE 2 (0 sorryAx)
-- ============================================================================

#print axioms picardSeq_admissible
#print axioms picardSeq_diff_bound
#print axioms picardLimit_tendsto_and_continuous
#print axioms picardLimit_admissible_and_rate
#print axioms picardLimit_fixedPoint_and_structure
#print axioms mild_solution_unique
#print axioms pressureCoeff6B_poisson
#print axioms nsBilinear6A_eq_neg_flux_sub_grad_pressure
#print axioms mild_solution_hasDerivAt_spectral_ns3d
#print axioms local_existence_uniqueness_ns3d_torus3D

end GarryLocalExistence3D