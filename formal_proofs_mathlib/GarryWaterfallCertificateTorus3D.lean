import CriticalProdiSerrinTorus3D
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

/-!
# Milestone 9B-1 (Tier I — 100% Unconditional): Multi-Step Garry Waterfall Certificate
  & Complete `𝕋³` Waterfall-to-River Global Closure (`0 sorryAx`)

This module seals the entire `𝕋³` tower (Milestones 1–9) before transitioning to the three
post-Milestone-9 hurdles (`𝕋³ → ℝ³`, global existence/`C^∞` closure, independent audit):

1. **Structure `GarryWaterfallWitness u ν`:** Audit-ready interface for finite multi-step
   conservative upper-bound witnesses `(t_k, zCap_k)` emitted by Garry (Rust) / SMT-LIB2.
2. **Theorem 9B-1 (`garry_multistep_waterfall_chain_torus3D`):** Unconditional induction over
   `0 = t_0 ≤ t_1 ≤ ... ≤ t_N` proving:
   - cumulative critical `L⁴_t Ḣ¹_x` budget `∫_0^{t_N} Z(s)² ds ≤ chainBudget ≤ N / (2 c_ν)`,
   - uniform waterfall peak ceiling `∀ s ∈ [0, t_N], Z(s) ≤ chainPeak`,
   - exponential-free palinstrophy balance on `[0, t_N]` controlled by `chainPeak * chainBudget`.
3. **Theorem 9B-2 (`garry_certified_waterfall_to_global_river_torus3D`):** Whenever the final
   certified cap enters the half-critical `H¹` basin (`zCap N < Z_crit_H1 ν / 2`), locks all
   global norms (`L∞_t H¹_x`, `L⁴_t Ḣ¹_x`, `L²_t Ḣ²_x`) on `[0, ∞)`, permanent exponential
   decay on `[t_N, ∞)`, and finite-time entry into Milestone 8A's `H²` threshold.
4. **Theorem 9B-3 (`garry_waterfall_witness_nonvacuous_torus3D`):** Non-vacuity audit showing
   any initial datum inside the half-critical `H¹` basin admits a certified 0-step witness.
-/

namespace GarryWaterfallCertificate3D

open MeasureTheory Filter Topology
open GarryReal3DCalculus
open GarryVorticity3D
open GarryLerayTorus3D
open GarryLerayEnergyLaw3D
open GarryPoincareSobolev3D
open GarryFourierSpectral3D
open GarryParsevalSobolev3D
open GarrySobolevEmbedding3D
open GarrySupercriticalBridge3D
open GarryEnstrophyBasin3D
open GarryCriticalProdiSerrin3D

-- ============================================================================
-- SECTION 0: PRIVATE CALCULUS HELPERS (SELF-CONTAINED, 0 SORRY)
-- ============================================================================

private lemma antitone_of_hasDerivAt_nonpos_9b {f f' : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
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

private lemma enstrophy_nonneg_9b {u : ℝ → R3 → R3} {p : ℝ → R3 → ℝ} {ν : ℝ}
    (hns : IsPeriodicClassicalNS3D_C3 u p ν) {t : ℝ} (ht : 0 ≤ t) :
    0 ≤ enstrophy u t := by
  have hu3 := hns.h_u_c3_global t ht
  have hw1 : ContDiff ℝ 1 (curl3D (u t)) :=
    (contDiff_two_curl3D hu3).of_le (by exact_mod_cast (show (1 : ℕ) ≤ 2 by decide))
  have hc : Continuous (fun x => dot3D (curl3D (u t) x) (curl3D (u t) x)) := by
    unfold dot3D
    have c0 := (contDiff_pi.mp hw1 0).continuous
    have c1 := (contDiff_pi.mp hw1 1).continuous
    have c2 := (contDiff_pi.mp hw1 2).continuous
    exact ((c0.mul c0).add (c1.mul c1)).add (c2.mul c2)
  unfold enstrophy
  have h := torusIntegral_nonneg hc (fun x => dot3D_self_nonneg _)
  linarith

private lemma palinstrophy_nonneg_9b {u : ℝ → R3 → R3} {p : ℝ → R3 → ℝ} {ν : ℝ}
    (hns : IsPeriodicClassicalNS3D_C3 u p ν) {t : ℝ} (ht : 0 ≤ t) :
    0 ≤ palinstrophy3D (u t) := by
  have hZ := enstrophy_nonneg_9b hns ht
  have hwirt := (sharp_analytical_lemma4_bernstein_poincare_vorticity hns ht).1
  nlinarith [Real.pi_pos]

private lemma enstrophy_ext_continuous_9b {u : ℝ → R3 → R3} {p : ℝ → R3 → ℝ} {ν : ℝ}
    (hns : IsPeriodicClassicalNS3D_C3 u p ν) :
    Continuous (fun s : ℝ => enstrophy u (max s 0)) := by
  rw [continuous_iff_continuousAt]
  intro s
  have h1 : ContinuousAt (enstrophy u) (max s (0 : ℝ)) :=
    (hasDerivAt_enstrophy_evolution_3D hns (le_max_right s 0)).1.continuousAt
  have h2 : ContinuousAt (fun r : ℝ => max r (0 : ℝ)) s :=
    (Continuous.max continuous_id continuous_const).continuousAt
  exact ContinuousAt.comp (f := fun r : ℝ => max r (0 : ℝ)) (g := enstrophy u) h1 h2

private lemma integral_enstrophy_sq_ext_eq_9b {u : ℝ → R3 → R3} {a b : ℝ}
    (ha : 0 ≤ a) (hab : a ≤ b) :
    (∫ s in a..b, (enstrophy u (max s 0)) ^ 2) = ∫ s in a..b, (enstrophy u s) ^ 2 := by
  apply intervalIntegral.integral_congr
  intro s hs
  rw [Set.uIcc_of_le hab] at hs
  simp only [max_eq_left (le_trans ha hs.1)]

private lemma hasDerivAt_integral_enstrophy_sq_ext_9b {u : ℝ → R3 → R3} {p : ℝ → R3 → ℝ} {ν : ℝ}
    (hns : IsPeriodicClassicalNS3D_C3 u p ν) (t₀ : ℝ) {r : ℝ} (hr : 0 ≤ r) :
    HasDerivAt (fun q : ℝ => ∫ s in t₀..q, (enstrophy u (max s 0)) ^ 2)
      ((enstrophy u r) ^ 2) r := by
  have hc : Continuous (fun s : ℝ => (enstrophy u (max s 0)) ^ 2) :=
    (enstrophy_ext_continuous_9b hns).pow 2
  have h := intervalIntegral.integral_hasDerivAt_right
    (hc.intervalIntegrable t₀ r)
    (hc.stronglyMeasurableAtFilter volume (nhds r))
    hc.continuousAt
  simpa [max_eq_left hr] using h

private lemma integral_enstrophy_sq_add_9b {u : ℝ → R3 → R3} {p : ℝ → R3 → ℝ} {ν : ℝ}
    (hns : IsPeriodicClassicalNS3D_C3 u p ν) {a b c : ℝ}
    (ha : 0 ≤ a) (hab : a ≤ b) (hbc : b ≤ c) :
    (∫ s in a..b, (enstrophy u s) ^ 2) + (∫ s in b..c, (enstrophy u s) ^ 2) =
      ∫ s in a..c, (enstrophy u s) ^ 2 := by
  have hc : Continuous (fun s : ℝ => (enstrophy u (max s 0)) ^ 2) :=
    (enstrophy_ext_continuous_9b hns).pow 2
  rw [← integral_enstrophy_sq_ext_eq_9b ha hab,
      ← integral_enstrophy_sq_ext_eq_9b (le_trans ha hab) hbc,
      ← integral_enstrophy_sq_ext_eq_9b ha (le_trans hab hbc)]
  exact intervalIntegral.integral_add_adjacent_intervals
    (hc.intervalIntegrable (μ := volume) a b) (hc.intervalIntegrable (μ := volume) b c)

private lemma integral_enstrophy_sq_mono_9b {u : ℝ → R3 → R3} {p : ℝ → R3 → ℝ} {ν : ℝ}
    (hns : IsPeriodicClassicalNS3D_C3 u p ν) {a b c : ℝ}
    (ha : 0 ≤ a) (hab : a ≤ b) (hbc : b ≤ c) :
    (∫ s in a..b, (enstrophy u s) ^ 2) ≤ ∫ s in a..c, (enstrophy u s) ^ 2 := by
  have hc : Continuous (fun s : ℝ => (enstrophy u (max s 0)) ^ 2) :=
    (enstrophy_ext_continuous_9b hns).pow 2
  have hadd := integral_enstrophy_sq_add_9b hns ha hab hbc
  have hnn : 0 ≤ ∫ s in b..c, (enstrophy u s) ^ 2 := by
    rw [← integral_enstrophy_sq_ext_eq_9b (le_trans ha hab) hbc]
    exact intervalIntegral.integral_nonneg hbc (fun _ _ => sq_nonneg _)
  linarith

private lemma river_tail_L4_bound_9b
    {u : ℝ → R3 → R3} {p : ℝ → R3 → ℝ} {ν : ℝ}
    (hns : IsPeriodicClassicalNS3D_C3 u p ν)
    (hmean : ∀ s ≥ 0, ∀ c : Fin 3, torusIntegral (fun x => u s x c) = 0)
    {t₀ : ℝ} (ht₀ : 0 ≤ t₀) (hhalf : enstrophy u t₀ ≤ Z_crit_H1 ν / 2) :
    ∀ T ≥ t₀,
      (∫ s in t₀..T, (enstrophy u s) ^ 2) ≤ (enstrophy u t₀) ^ 2 / (3 * Real.pi ^ 2 * ν) := by
  have hν : 0 < ν := hns.h_nu_pos
  have hZ0_nn : 0 ≤ enstrophy u t₀ := enstrophy_nonneg_9b hns ht₀
  have hbasin : enstrophy u t₀ < Z_crit_H1 ν := by linarith [Z_crit_H1_pos hν]
  have hdec := (unconditional_H1_enstrophy_basin_invariance_and_exp_decay_torus3D
    hns hmean ht₀ hbasin).2.2.2 hhalf
  intro T hT
  let k : ℝ := 3 * Real.pi ^ 2 * ν
  have hk_pos : 0 < k := by dsimp only [k]; positivity
  have hk_ne : k ≠ 0 := ne_of_gt hk_pos
  let q : ℝ → ℝ := fun r =>
    (∫ s in t₀..r, (enstrophy u (max s 0)) ^ 2) +
      ((enstrophy u t₀) ^ 2 / k) * Real.exp (-k * (r - t₀))
  let q' : ℝ → ℝ := fun r =>
    (enstrophy u r) ^ 2 - (enstrophy u t₀) ^ 2 * Real.exp (-k * (r - t₀))
  have hq_deriv : ∀ r ≥ t₀, HasDerivAt q (q' r) r := fun r hr => by
    have hI := hasDerivAt_integral_enstrophy_sq_ext_9b hns t₀ (le_trans ht₀ hr)
    have hlin : HasDerivAt (fun s : ℝ => -k * (s - t₀)) (-k) r := by
      simpa [mul_one] using ((hasDerivAt_id r).sub_const t₀).const_mul (-k)
    have he : HasDerivAt (fun s : ℝ => Real.exp (-k * (s - t₀)))
        (Real.exp (-k * (r - t₀)) * (-k)) r := hlin.exp
    have hsum := hI.add (he.const_mul ((enstrophy u t₀) ^ 2 / k))
    convert hsum using 1
    dsimp only [q']
    field_simp
    ring
  have hq_cont : ContinuousOn q (Set.Icc t₀ T) :=
    fun r hr => (hq_deriv r hr.1).continuousAt.continuousWithinAt
  have hq_nonpos : ∀ r ∈ Set.Ioo t₀ T, q' r ≤ 0 := fun r hr => by
    have hr_ge : r ≥ t₀ := le_of_lt hr.1
    have hZr_nn : 0 ≤ enstrophy u r := enstrophy_nonneg_9b hns (le_trans ht₀ hr_ge)
    have hle := hdec r hr_ge
    have hexp_nn : 0 ≤ enstrophy u t₀ *
        Real.exp (-(3 / 2 * Real.pi ^ 2 * ν) * (r - t₀)) :=
      mul_nonneg hZ0_nn (le_of_lt (Real.exp_pos _))
    have hsq_le : (enstrophy u r) ^ 2 ≤
        (enstrophy u t₀ * Real.exp (-(3 / 2 * Real.pi ^ 2 * ν) * (r - t₀))) ^ 2 := by
      nlinarith
    have hexp_sq : (Real.exp (-(3 / 2 * Real.pi ^ 2 * ν) * (r - t₀))) ^ 2 =
        Real.exp (-k * (r - t₀)) := by
      rw [sq, ← Real.exp_add]
      congr 1
      dsimp only [k]
      ring
    rw [mul_pow, hexp_sq] at hsq_le
    dsimp only [q']
    linarith
  have hqT_le : q T ≤ q t₀ :=
    antitone_of_hasDerivAt_nonpos_9b hT hq_cont (fun r hr => hq_deriv r (le_of_lt hr.1)) hq_nonpos
  have hq0 : q t₀ = (enstrophy u t₀) ^ 2 / k := by
    dsimp only [q]; simp
  rw [hq0] at hqT_le
  dsimp only [q] at hqT_le
  rw [integral_enstrophy_sq_ext_eq_9b ht₀ hT] at hqT_le
  have hrem_nn : 0 ≤ ((enstrophy u t₀) ^ 2 / k) * Real.exp (-k * (T - t₀)) :=
    mul_nonneg (div_nonneg (sq_nonneg _) (le_of_lt hk_pos)) (le_of_lt (Real.exp_pos _))
  linarith

-- ============================================================================
-- SECTION 1: GARRY WATERFALL WITNESS STRUCTURE & EXPLICIT BUDGET ACCUMULATORS
-- ============================================================================

/-- Conservative multi-step waterfall certificate produced by Garry (Rust / SMT-LIB2):
    a monotone time grid `0 = t_0 ≤ t_1 ≤ ... ≤ t_N` paired with certified enstrophy
    upper bounds `zCap k ≥ enstrophy u (tGrid k)` satisfying the half-horizon safety
    criterion `2 c_nu_H1 ν (zCap k)² (t_{k+1} - t_k) ≤ 1/2` on every step. -/
structure GarryWaterfallWitness (u : ℝ → R3 → R3) (ν : ℝ) where
  steps : ℕ
  tGrid : ℕ → ℝ
  zCap : ℕ → ℝ
  ht0 : tGrid 0 = 0
  hmono : ∀ k < steps, tGrid k ≤ tGrid (k + 1)
  hzCap_nonneg : ∀ k ≤ steps, 0 ≤ zCap k
  hnode_cap : ∀ k ≤ steps, enstrophy u (tGrid k) ≤ zCap k
  hsafe_step : ∀ k < steps, 2 * c_nu_H1 ν * (zCap k) ^ 2 * (tGrid (k + 1) - tGrid k) ≤ 1 / 2

/-- Certified cumulative critical `L⁴_t Ḣ¹_x` budget across the first `n` steps:
    `∑_{k=0}^{n-1} 2 (zCap k)² (t_{k+1} - t_k)`. -/
def chainBudget (tGrid zCap : ℕ → ℝ) : ℕ → ℝ
  | 0 => 0
  | n + 1 => chainBudget tGrid zCap n + 2 * (zCap n) ^ 2 * (tGrid (n + 1) - tGrid n)

/-- Certified uniform `H¹` enstrophy ceiling across the first `n` steps:
    `max(zCap 0, √2 zCap 0, ..., √2 zCap (n-1))`. -/
noncomputable def chainPeak (zCap : ℕ → ℝ) : ℕ → ℝ
  | 0 => zCap 0
  | n + 1 => max (chainPeak zCap n) (Real.sqrt 2 * zCap n)

lemma GarryWaterfallWitness.tGrid_nonneg {u : ℝ → R3 → R3} {ν : ℝ}
    (W : GarryWaterfallWitness u ν) :
    ∀ n ≤ W.steps, 0 ≤ W.tGrid n := by
  intro n
  induction n with
  | zero =>
    intro _
    rw [W.ht0]
  | succ k ih =>
    intro hk
    have hk_lt : k < W.steps := Nat.lt_of_succ_le hk
    exact le_trans (ih (Nat.le_of_lt hk_lt)) (W.hmono k hk_lt)

lemma chainBudget_nonneg {u : ℝ → R3 → R3} {ν : ℝ} (W : GarryWaterfallWitness u ν) :
    ∀ n ≤ W.steps, 0 ≤ chainBudget W.tGrid W.zCap n := by
  intro n
  induction n with
  | zero =>
    intro _
    simp [chainBudget]
  | succ k ih =>
    intro hk
    have hk_lt : k < W.steps := Nat.lt_of_succ_le hk
    have hprev := ih (Nat.le_of_lt hk_lt)
    have hdt : 0 ≤ W.tGrid (k + 1) - W.tGrid k := sub_nonneg.mpr (W.hmono k hk_lt)
    have hstep : 0 ≤ 2 * (W.zCap k) ^ 2 * (W.tGrid (k + 1) - W.tGrid k) := by positivity
    simp only [chainBudget]
    linarith

lemma chainPeak_nonneg {u : ℝ → R3 → R3} {ν : ℝ} (W : GarryWaterfallWitness u ν) :
    ∀ n ≤ W.steps, 0 ≤ chainPeak W.zCap n := by
  intro n
  induction n with
  | zero =>
    intro _
    exact W.hzCap_nonneg 0 (Nat.zero_le _)
  | succ k ih =>
    intro hk
    exact le_trans (ih (Nat.le_of_lt (Nat.lt_of_succ_le hk))) (le_max_left _ _)

lemma c_nu_mul_chainBudget_le {u : ℝ → R3 → R3} {ν : ℝ} (W : GarryWaterfallWitness u ν) :
    ∀ n ≤ W.steps, c_nu_H1 ν * chainBudget W.tGrid W.zCap n ≤ (n : ℝ) / 2 := by
  intro n
  induction n with
  | zero =>
    intro _
    simp [chainBudget]
  | succ k ih =>
    intro hk
    have hk_lt : k < W.steps := Nat.lt_of_succ_le hk
    have hprev := ih (Nat.le_of_lt hk_lt)
    have hstep := W.hsafe_step k hk_lt
    simp only [chainBudget, Nat.cast_succ]
    have hexp : c_nu_H1 ν * (chainBudget W.tGrid W.zCap k +
        2 * (W.zCap k) ^ 2 * (W.tGrid (k + 1) - W.tGrid k)) =
        c_nu_H1 ν * chainBudget W.tGrid W.zCap k +
        2 * c_nu_H1 ν * (W.zCap k) ^ 2 * (W.tGrid (k + 1) - W.tGrid k) := by ring
    linarith

-- ============================================================================
-- SECTION 2: THEOREM 9B-1 — MULTI-STEP WATERFALL CHAIN INDUCTION
-- ============================================================================

/-- **THEOREM 9B-1 (Unconditional Multi-Step Garry Waterfall Chain on `𝕋³`):**
    For ANY mean-zero classical 3D Navier-Stokes solution `(u, p)` on `𝕋³` and ANY
    certified witness `W : GarryWaterfallWitness u ν` covering `[0, t_N]`:
1. `0 ≤ t_N`,
2. Exact critical `L⁴_t Ḣ¹_x` budget enclosure:
       `∫_0^{t_N} Z(s)² ds ≤ chainBudget W.tGrid W.zCap W.steps`,
3. Pure step-count critical budget ceiling:
       `c_nu_H1 ν * ∫_0^{t_N} Z(s)² ds ≤ W.steps / 2`,
4. Uniform waterfall `H¹` ceiling (no exponential blowup):
       `∀ s ∈ [0, t_N], Z(s) ≤ chainPeak W.zCap W.steps`,
5. Exponential-free waterfall palinstrophy balance (when `palinstrophy3D (u ·)` is continuous):
       `Z(t_N) + (ν/4) ∫_0^{t_N} P(s) ds ≤ W.zCap 0 + c_nu_H1 ν * chainPeak * chainBudget`. -/
theorem garry_multistep_waterfall_chain_torus3D
    {u : ℝ → R3 → R3} {p : ℝ → R3 → ℝ} {ν : ℝ}
    (hns : IsPeriodicClassicalNS3D_C3 u p ν)
    (hmean : ∀ s ≥ 0, ∀ c : Fin 3, torusIntegral (fun x => u s x c) = 0)
    (W : GarryWaterfallWitness u ν) :
    let tN : ℝ := W.tGrid W.steps
    let B : ℝ := chainBudget W.tGrid W.zCap W.steps
    let M_peak : ℝ := chainPeak W.zCap W.steps
    0 ≤ tN ∧
    (∫ s in (0 : ℝ)..tN, (enstrophy u s) ^ 2) ≤ B ∧
    c_nu_H1 ν * (∫ s in (0 : ℝ)..tN, (enstrophy u s) ^ 2) ≤ (W.steps : ℝ) / 2 ∧
    (∀ s ∈ Set.Icc (0 : ℝ) tN, enstrophy u s ≤ M_peak) ∧
    (Continuous (fun s : ℝ => palinstrophy3D (u s)) →
      enstrophy u tN + (ν / 4) * (∫ s in (0 : ℝ)..tN, palinstrophy3D (u s)) ≤
        W.zCap 0 + c_nu_H1 ν * M_peak * B) := by
  intro tN B M_peak
  have hν : 0 < ν := hns.h_nu_pos
  have hc_pos : 0 < c_nu_H1 ν := c_nu_H1_pos hν
  have hchain : ∀ n ≤ W.steps,
      (∫ s in (0 : ℝ)..(W.tGrid n), (enstrophy u s) ^ 2) ≤ chainBudget W.tGrid W.zCap n ∧
      (∀ s ∈ Set.Icc (0 : ℝ) (W.tGrid n), enstrophy u s ≤ chainPeak W.zCap n) := by
    intro n
    induction n with
    | zero =>
      intro _
      constructor
      · rw [W.ht0, intervalIntegral.integral_same]
        simp [chainBudget]
      · intro s hs
        rw [W.ht0] at hs
        have hs0 : s = 0 := le_antisymm hs.2 hs.1
        rw [hs0, ← W.ht0]
        simpa [chainPeak] using W.hnode_cap 0 (Nat.zero_le W.steps)
    | succ k ih =>
      intro hk
      have hk_lt : k < W.steps := Nat.lt_of_succ_le hk
      have hk_le : k ≤ W.steps := Nat.le_of_lt hk_lt
      obtain ⟨ih_int, ih_peak⟩ := ih hk_le
      have htk_nn : 0 ≤ W.tGrid k := W.tGrid_nonneg k hk_le
      have hstep_le : W.tGrid k ≤ W.tGrid (k + 1) := W.hmono k hk_lt
      have hZk_nn : 0 ≤ enstrophy u (W.tGrid k) := enstrophy_nonneg_9b hns htk_nn
      have hZk_le : enstrophy u (W.tGrid k) ≤ W.zCap k := W.hnode_cap k hk_le
      have hZk_sq : (enstrophy u (W.tGrid k)) ^ 2 ≤ (W.zCap k) ^ 2 := by nlinarith
      have hdt : 0 ≤ W.tGrid (k + 1) - W.tGrid k := sub_nonneg.mpr hstep_le
      have hsafe_actual :
          2 * c_nu_H1 ν * (enstrophy u (W.tGrid k)) ^ 2 * (W.tGrid (k + 1) - W.tGrid k) ≤ 1 / 2 := by
        have hfac : 0 ≤ 2 * c_nu_H1 ν * (W.tGrid (k + 1) - W.tGrid k) := by positivity
        have hmul := mul_le_mul_of_nonneg_right hZk_sq hfac
        have hsafe_k := W.hsafe_step k hk_lt
        linarith
      have henc := garry_safe_step_enclosure_torus3D hns hmean htk_nn hstep_le hsafe_actual
      constructor
      · have hadd := integral_enstrophy_sq_add_9b hns le_rfl htk_nn hstep_le
        have hstep_int_le :
            (∫ s in (W.tGrid k)..(W.tGrid (k + 1)), (enstrophy u s) ^ 2) ≤
              2 * (W.zCap k) ^ 2 * (W.tGrid (k + 1) - W.tGrid k) := by
          have hmul := mul_le_mul_of_nonneg_right hZk_sq
            (show 0 ≤ 2 * (W.tGrid (k + 1) - W.tGrid k) by linarith)
          linarith [henc.2.2.1]
        simp only [chainBudget]
        linarith
      · intro s hs
        simp only [chainPeak]
        rcases le_total s (W.tGrid k) with hle | hge
        · exact le_trans (ih_peak s ⟨hs.1, hle⟩) (le_max_left _ _)
        · have h1 := henc.2.1 s ⟨hge, hs.2⟩
          have h2 : Real.sqrt 2 * enstrophy u (W.tGrid k) ≤ Real.sqrt 2 * W.zCap k :=
            mul_le_mul_of_nonneg_left hZk_le (Real.sqrt_nonneg 2)
          exact le_trans (le_trans h1 h2) (le_max_right _ _)
  have htN_nn : 0 ≤ tN := W.tGrid_nonneg W.steps le_rfl
  obtain ⟨hB_int, hM_peak⟩ := hchain W.steps le_rfl
  have hB_steps : c_nu_H1 ν * (∫ s in (0 : ℝ)..tN, (enstrophy u s) ^ 2) ≤ (W.steps : ℝ) / 2 := by
    have hmul := mul_le_mul_of_nonneg_left hB_int (le_of_lt hc_pos)
    have hcb := c_nu_mul_chainBudget_le W W.steps le_rfl
    linarith
  have hpal : Continuous (fun s : ℝ => palinstrophy3D (u s)) →
      enstrophy u tN + (ν / 4) * (∫ s in (0 : ℝ)..tN, palinstrophy3D (u s)) ≤
        W.zCap 0 + c_nu_H1 ν * M_peak * B := by
    intro hP_cont
    have hpal_gen := (critical_prodi_serrin_palinstrophy_bound_torus3D
      hns hmean hP_cont le_rfl htN_nn).1 M_peak hM_peak
    have hZ0_le : enstrophy u 0 ≤ W.zCap 0 := by
      have h0 := W.hnode_cap 0 (Nat.zero_le W.steps)
      rwa [W.ht0] at h0
    have hM_nn : 0 ≤ M_peak := chainPeak_nonneg W W.steps le_rfl
    have hcM_nn : 0 ≤ c_nu_H1 ν * M_peak := mul_nonneg (le_of_lt hc_pos) hM_nn
    have hmul := mul_le_mul_of_nonneg_left hB_int hcM_nn
    linarith
  exact ⟨htN_nn, hB_int, hB_steps, hM_peak, hpal⟩

-- ============================================================================
-- SECTION 3: THEOREM 9B-2 — CERTIFIED WATERFALL-TO-GLOBAL-RIVER CLOSURE
-- ============================================================================

/-- **THEOREM 9B-2 (Certified Garry Waterfall-to-Global-River Master Theorem on `𝕋³`):**
    If a certified multi-step witness `W : GarryWaterfallWitness u ν` reaches the half-critical
    `H¹` basin at its terminal node (`W.zCap W.steps < Z_crit_H1 ν / 2`), then unconditionally
    across the entire global time axis `[0, ∞)`:
1. Permanent `H¹` basin trapping and exponential decay for all `t ≥ t_N`:
       `Z(t) ≤ Z(t_N) * exp(-(3/2) π² ν (t - t_N))`,
2. Global uniform `L∞_t H¹_x` ceiling (exponential-free):
       `∀ T ≥ 0, Z(T) ≤ chainPeak W.zCap W.steps`,
3. Global critical `L⁴_t Ḣ¹_x` norm bound (explicit and numeric river tail):
       `∀ T ≥ 0, ∫_0^T Z(s)² ds ≤ B + (zCap N)² / (3π² ν) < B + 4π⁴ ν³ / 507`,
4. Global `L²_t Ḣ²_x` palinstrophy integral bound AND unconditional finite-time entry into
       Milestone 8A's `H²` threshold `palinstrophy3D (u T_enter) < π⁶ ν² / 27136`. -/
theorem garry_certified_waterfall_to_global_river_torus3D
    {u : ℝ → R3 → R3} {p : ℝ → R3 → ℝ} {ν : ℝ}
    (hns : IsPeriodicClassicalNS3D_C3 u p ν)
    (hmean : ∀ s ≥ 0, ∀ c : Fin 3, torusIntegral (fun x => u s x c) = 0)
    (W : GarryWaterfallWitness u ν)
    (hcapture : W.zCap W.steps < Z_crit_H1 ν / 2) :
    let tN : ℝ := W.tGrid W.steps
    let B : ℝ := chainBudget W.tGrid W.zCap W.steps
    let M_peak : ℝ := chainPeak W.zCap W.steps
    (∀ t ≥ tN, enstrophy u t ≤ enstrophy u tN * Real.exp (-(3 / 2 * Real.pi ^ 2 * ν) * (t - tN))) ∧
    (∀ T ≥ 0, enstrophy u T ≤ M_peak) ∧
    (∀ T ≥ 0, (∫ s in (0 : ℝ)..T, (enstrophy u s) ^ 2) ≤
      B + (W.zCap W.steps) ^ 2 / (3 * Real.pi ^ 2 * ν)) ∧
    (∀ T ≥ 0, (∫ s in (0 : ℝ)..T, (enstrophy u s) ^ 2) ≤
      B + 4 * Real.pi ^ 4 * ν ^ 3 / 507) ∧
    (Continuous (fun s : ℝ => palinstrophy3D (u s)) →
      (∀ T ≥ 0,
        (∫ s in (0 : ℝ)..T, palinstrophy3D (u s)) ≤
          (4 / ν) * (W.zCap 0 + c_nu_H1 ν * M_peak * B) +
          (16 / (3 * ν)) * W.zCap W.steps) ∧
      (∀ Δ : ℝ, 0 < Δ →
        16 * 27136 * W.zCap W.steps / (3 * Real.pi ^ 6 * ν ^ 3) < Δ →
        ∃ T_enter ∈ Set.Icc tN (tN + Δ),
          palinstrophy3D (u T_enter) < Real.pi ^ 6 * ν ^ 2 / 27136)) := by
  intro tN B M_peak
  have hν : 0 < ν := hns.h_nu_pos
  obtain ⟨htN_nn, hB_int, _, hM_peak, hpal_pre⟩ :=
    garry_multistep_waterfall_chain_torus3D hns hmean W
  have htN_le_cap : enstrophy u tN ≤ W.zCap W.steps := W.hnode_cap W.steps le_rfl
  have hZtN_nn : 0 ≤ enstrophy u tN := enstrophy_nonneg_9b hns htN_nn
  have hcap_nn : 0 ≤ W.zCap W.steps := W.hzCap_nonneg W.steps le_rfl
  have htN_half : enstrophy u tN < Z_crit_H1 ν / 2 := lt_of_le_of_lt htN_le_cap hcapture
  have htN_basin : enstrophy u tN < Z_crit_H1 ν := by linarith [Z_crit_H1_pos hν]
  have hdec := unconditional_H1_enstrophy_basin_invariance_and_exp_decay_torus3D
    hns hmean htN_nn htN_basin
  have h_exp : ∀ t ≥ tN,
      enstrophy u t ≤ enstrophy u tN * Real.exp (-(3 / 2 * Real.pi ^ 2 * ν) * (t - tN)) :=
    hdec.2.2.2 (le_of_lt htN_half)
  -- Global uniform L∞_t H¹_x ceiling on [0, ∞)
  have hglob_Z : ∀ T ≥ 0, enstrophy u T ≤ M_peak := by
    intro T hT
    rcases le_total T tN with hle | hge
    · exact hM_peak T ⟨hT, hle⟩
    · exact le_trans (hdec.2.1 T hge) (hM_peak tN ⟨htN_nn, le_rfl⟩)
  -- River tail L⁴_t Ḣ¹_x bound and numeric ceiling
  have htail := river_tail_L4_bound_9b hns hmean htN_nn (le_of_lt htN_half)
  have htail_cap_le :
      (enstrophy u tN) ^ 2 / (3 * Real.pi ^ 2 * ν) ≤
        (W.zCap W.steps) ^ 2 / (3 * Real.pi ^ 2 * ν) :=
    div_le_div_of_nonneg_right (by nlinarith) (by positivity)
  have htail_num :
      (W.zCap W.steps) ^ 2 / (3 * Real.pi ^ 2 * ν) < 4 * Real.pi ^ 4 * ν ^ 3 / 507 := by
    have hsq : (W.zCap W.steps) ^ 2 < (Z_crit_H1 ν / 2) ^ 2 := by
      have hpos : 0 < Z_crit_H1 ν / 2 := half_pos (Z_crit_H1_pos hν)
      nlinarith
    have hdiv : (W.zCap W.steps) ^ 2 / (3 * Real.pi ^ 2 * ν) <
        (Z_crit_H1 ν / 2) ^ 2 / (3 * Real.pi ^ 2 * ν) :=
      div_lt_div_of_pos_right hsq (by positivity)
    have heq : (Z_crit_H1 ν / 2) ^ 2 / (3 * Real.pi ^ 2 * ν) =
        4 * Real.pi ^ 4 * ν ^ 3 / 507 := by
      unfold Z_crit_H1
      have hpi : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
      have hν0 : ν ≠ 0 := ne_of_gt hν
      field_simp
      ring
    linarith
  have hglob_L4 : ∀ T ≥ 0,
      (∫ s in (0 : ℝ)..T, (enstrophy u s) ^ 2) ≤
        B + (W.zCap W.steps) ^ 2 / (3 * Real.pi ^ 2 * ν) := by
    intro T hT
    have htail_nn : 0 ≤ (W.zCap W.steps) ^ 2 / (3 * Real.pi ^ 2 * ν) := by positivity
    rcases le_total T tN with hle | hge
    · have hmono := integral_enstrophy_sq_mono_9b hns le_rfl hT hle
      linarith
    · have hadd := integral_enstrophy_sq_add_9b hns le_rfl htN_nn hge
      have htT := htail T hge
      linarith
  have hglob_L4_num : ∀ T ≥ 0,
      (∫ s in (0 : ℝ)..T, (enstrophy u s) ^ 2) ≤ B + 4 * Real.pi ^ 4 * ν ^ 3 / 507 :=
    fun T hT => le_trans (hglob_L4 T hT) (by linarith)
  -- Global palinstrophy integral & finite-time H² entry
  have hglob_P : Continuous (fun s : ℝ => palinstrophy3D (u s)) →
      (∀ T ≥ 0,
        (∫ s in (0 : ℝ)..T, palinstrophy3D (u s)) ≤
          (4 / ν) * (W.zCap 0 + c_nu_H1 ν * M_peak * B) +
          (16 / (3 * ν)) * W.zCap W.steps) ∧
      (∀ Δ : ℝ, 0 < Δ →
        16 * 27136 * W.zCap W.steps / (3 * Real.pi ^ 6 * ν ^ 3) < Δ →
        ∃ T_enter ∈ Set.Icc tN (tN + Δ),
          palinstrophy3D (u T_enter) < Real.pi ^ 6 * ν ^ 2 / 27136) := by
    intro hP_cont
    have hpal_post := unconditional_H1_basin_palinstrophy_integral_and_H2_entry_torus3D
      hns hmean hP_cont htN_nn (le_of_lt htN_half)
    have hpre_int : (∫ s in (0 : ℝ)..tN, palinstrophy3D (u s)) ≤
        (4 / ν) * (W.zCap 0 + c_nu_H1 ν * M_peak * B) := by
      have h1 : (ν / 4) * (∫ s in (0 : ℝ)..tN, palinstrophy3D (u s)) ≤
          W.zCap 0 + c_nu_H1 ν * M_peak * B := by
        linarith [hpal_pre hP_cont]
      have hmul := mul_le_mul_of_nonneg_left h1 (by positivity : (0 : ℝ) ≤ 4 / ν)
      have hcancel : (4 / ν) * ((ν / 4) * (∫ s in (0 : ℝ)..tN, palinstrophy3D (u s))) =
          ∫ s in (0 : ℝ)..tN, palinstrophy3D (u s) := by
        have hν0 : ν ≠ 0 := ne_of_gt hν
        field_simp
      linarith
    constructor
    · intro T hT
      have hpost_nn : 0 ≤ (16 / (3 * ν)) * W.zCap W.steps := by positivity
      rcases le_total T tN with hle | hge
      · have hadd := intervalIntegral.integral_add_adjacent_intervals
          (hP_cont.intervalIntegrable (μ := volume) 0 T)
          (hP_cont.intervalIntegrable (μ := volume) T tN)
        have hrem_nn : 0 ≤ ∫ s in T..tN, palinstrophy3D (u s) :=
          intervalIntegral.integral_nonneg hle
            (fun s hs => palinstrophy_nonneg_9b hns (le_trans hT hs.1))
        linarith
      · have hadd := intervalIntegral.integral_add_adjacent_intervals
          (hP_cont.intervalIntegrable (μ := volume) 0 tN)
          (hP_cont.intervalIntegrable (μ := volume) tN T)
        have hpost_bal := hpal_post.1 T hge
        have hZT_nn : 0 ≤ enstrophy u T := enstrophy_nonneg_9b hns hT
        have hpost_int : (∫ s in tN..T, palinstrophy3D (u s)) ≤
            (16 / (3 * ν)) * W.zCap W.steps := by
          have h1 : (3 * ν / 16) * (∫ s in tN..T, palinstrophy3D (u s)) ≤ W.zCap W.steps := by
            linarith
          have hmul := mul_le_mul_of_nonneg_left h1 (by positivity : (0 : ℝ) ≤ 16 / (3 * ν))
          have hcancel : (16 / (3 * ν)) * ((3 * ν / 16) * (∫ s in tN..T, palinstrophy3D (u s))) =
              ∫ s in tN..T, palinstrophy3D (u s) := by
            have hν0 : ν ≠ 0 := ne_of_gt hν
            field_simp
          linarith
        linarith
    · intro Δ hΔ hbig
      have hPt_pos : 0 < Real.pi ^ 6 * ν ^ 2 / 27136 := by positivity
      have hreq : 16 * enstrophy u tN / (3 * ν * (Real.pi ^ 6 * ν ^ 2 / 27136)) < Δ := by
        have heq : 16 * enstrophy u tN / (3 * ν * (Real.pi ^ 6 * ν ^ 2 / 27136)) =
            16 * 27136 * enstrophy u tN / (3 * Real.pi ^ 6 * ν ^ 3) := by
          have hpi : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
          have hν0 : ν ≠ 0 := ne_of_gt hν
          field_simp
        have hmono : 16 * 27136 * enstrophy u tN / (3 * Real.pi ^ 6 * ν ^ 3) ≤
            16 * 27136 * W.zCap W.steps / (3 * Real.pi ^ 6 * ν ^ 3) :=
          div_le_div_of_nonneg_right (by linarith) (by positivity)
        linarith
      exact hpal_post.2 (Real.pi ^ 6 * ν ^ 2 / 27136) Δ hPt_pos hΔ hreq
  exact ⟨h_exp, hglob_Z, hglob_L4, hglob_L4_num, hglob_P⟩

-- ============================================================================
-- SECTION 4: THEOREM 9B-3 — NON-VACUITY AUDIT OF THE CERTIFICATE INTERFACE
-- ============================================================================

/-- **THEOREM 9B-3 (Non-Vacuity Audit of `GarryWaterfallWitness`):**
    Any solution starting inside the half-critical `H¹` basin (`enstrophy u 0 < Z_crit_H1 ν / 2`)
    unconditionally admits a certified 0-step witness with zero waterfall budget (`B = 0`)
    and terminal capture `W.zCap 0 < Z_crit_H1 ν / 2`. -/
theorem garry_waterfall_witness_nonvacuous_torus3D
    {u : ℝ → R3 → R3} {p : ℝ → R3 → ℝ} {ν : ℝ}
    (hns : IsPeriodicClassicalNS3D_C3 u p ν)
    (hsmall : enstrophy u 0 < Z_crit_H1 ν / 2) :
    ∃ W : GarryWaterfallWitness u ν,
      W.steps = 0 ∧
      W.zCap W.steps < Z_crit_H1 ν / 2 ∧
      chainBudget W.tGrid W.zCap W.steps = 0 ∧
      chainPeak W.zCap W.steps = enstrophy u 0 := by
  refine ⟨{
    steps := 0
    tGrid := fun _ => 0
    zCap := fun _ => enstrophy u 0
    ht0 := rfl
    hmono := fun k hk => absurd hk (Nat.not_lt_zero k)
    hzCap_nonneg := fun _ _ => enstrophy_nonneg_9b hns le_rfl
    hnode_cap := fun _ _ => le_rfl
    hsafe_step := fun k hk => absurd hk (Nat.not_lt_zero k)
  }, rfl, hsmall, rfl, rfl⟩

-- ============================================================================
-- SECTION 5: AXIOM AUDIT TRAIL (0 sorryAx, 0 custom axioms)
-- ============================================================================

#print axioms garry_multistep_waterfall_chain_torus3D
#print axioms garry_certified_waterfall_to_global_river_torus3D
#print axioms garry_waterfall_witness_nonvacuous_torus3D

end GarryWaterfallCertificate3D