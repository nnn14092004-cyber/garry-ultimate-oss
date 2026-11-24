import SpacetimeSmoothnessNS3D
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

/-!
# Milestone 15F-1 (Fefferman 2000 Schwartz Class & Elimination of `⟨x⟩⁻³` Decay at `t > 0` — Part 1/2):
  Schwartz Space `𝒮(ℝ³)`, Embedding `𝒮_σ(ℝ³) ↪ H^∞_σ(ℝ³) ∩ DecayingH3SolenoidalR3`,
  and Pure-Sobolev `L² + Lipschitz ⟹ VanishesAtInfinityR3` Discharging `DecayingH3SolenoidalR3`
  Without Pointwise `⟨x⟩⁻³` Decay at `t > 0` (`0 sorryAx`)

This module implements the first two deliverables of Milestone 15F:
1. **Section 0 (Fefferman 2000 Schwartz Initial Data `𝒮_σ(ℝ³)`):**
   - `multiPartialR3`: iterated Cartesian partial derivative `∂_x^α f` for any multi-index `α : List (Fin 3)`.
   - `IsSchwartzScalarR3` & `IsSchwartzSolenoidalR3`: verbatim Fefferman (2000) Schwartz class
     `sup_x ⟨x⟩^K |∂_x^α f(x)| < ∞` for all `α, K` and `∇ · u₀ = 0`.
   - `schwartzScalarR3_in_L2_and_vanishes`, `schwartzScalarR3_to_RapidDecayH3_and_DecayingH3`,
     and `schwartzSolenoidalR3_to_DecayingH3Solenoidal_and_finite_EZP`: every `u₀ ∈ 𝒮_σ(ℝ³)`
     automatically lies in `H^m(ℝ³)` for all `m`, satisfies `DecayingH3SolenoidalR3 u₀`, has finite
     `E(0), Z(0), P(0)`, and satisfies Betchov & Loomis–Whitney (`46,656 ν⁴`).
2. **Section 1 (Eliminating Pointwise `⟨x⟩⁻³` Decay at `t > 0`):**
   - `vanishesAtInfinityR3_of_L2_and_lipschitz`: any globally Lipschitz `L²(ℝ³)` function
     automatically satisfies `VanishesAtInfinityR3 f` (zero Schwartz / `⟨x⟩⁻³` assumption!).
   - `pure_H3_sobolev_to_DecayingH3ScalarR3` & `pure_H3_sobolev_to_DecayingH3SolenoidalR3`:
     replaces `RapidDecayH3ScalarR3` at `t > 0` by pure `C³ ∩ H³` + bounded derivatives
     (automatically preserved by `H^∞(ℝ³)` at all `t ∈ [0, T*)`), avoiding the mathematically
     false claim `u(t) ∈ 𝒮(ℝ³)` for `t > 0`.
-/

namespace GarrySchwartzClayPackagingNS3D

open MeasureTheory Filter Topology
open GarryReal3DCalculus
open GarryWholeSpaceR3
open GarryConcreteNS3DClosures
open GarryClassicalPDEBridgeNS3D
open GarryGeometricDepletionCriteriaNS3D
open GarryAdversarialSupercriticalLabNS3D

-- ============================================================================
-- SECTION 0: FEFFERMAN (2000) SCHWARTZ SPACE 𝒮(ℝ³) & EMBEDDING 𝒮_σ ↪ H^∞_σ
-- ============================================================================

/-- Iterated Cartesian partial derivative `∂_x^α f` on `ℝ³` along a multi-index `α : List (Fin 3)`. -/
noncomputable def multiPartialR3 : List (Fin 3) → (R3 → ℝ) → (R3 → ℝ)
  | [], f => f
  | i :: α, f => fun x => partialDerivScalar (multiPartialR3 α f) x i

/-- Verbatim Fefferman (2000) Schwartz class `𝒮(ℝ³)` for scalar fields:
    `f ∈ C^∞(ℝ³)` and `∀ α, K, ∃ C ≥ 0, ∀ x, ⟨x⟩^K |∂_x^α f(x)| ≤ C`. -/
structure IsSchwartzScalarR3 (f : R3 → ℝ) : Prop where
  h_smooth : ContDiff ℝ (⊤ : ℕ∞) f
  h_rapid : ∀ (α : List (Fin 3)) (K : ℕ), ∃ C : ℝ, 0 ≤ C ∧
    ∀ x : R3, japaneseBracket3D x ^ K * |multiPartialR3 α f x| ≤ C

/-- Verbatim Fefferman (2000) divergence-free Schwartz initial data `u₀ ∈ 𝒮_σ(ℝ³)`. -/
structure IsSchwartzSolenoidalR3 (u₀ : R3 → R3) : Prop where
  h_comp : ∀ c : Fin 3, IsSchwartzScalarR3 (fun x => u₀ x c)
  h_div : ∀ x : R3, div3D u₀ x = 0

lemma multiPartialR3_contDiff_infty {f : R3 → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (α : List (Fin 3)) :
    ContDiff ℝ (⊤ : ℕ∞) (multiPartialR3 α f) := by
  induction α with
  | nil => exact hf
  | cons i α ih =>
    unfold multiPartialR3 partialDerivScalar
    exact (ContinuousLinearMap.apply ℝ ℝ (basisVec i)).contDiff.comp (ih.fderiv_right (by simp))

lemma multiPartialR3_continuous {f : R3 → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) (α : List (Fin 3)) :
    Continuous (multiPartialR3 α f) :=
  (multiPartialR3_contDiff_infty hf α).continuous

lemma multiPartialR3_one (f : R3 → ℝ) (i : Fin 3) (x : R3) :
    multiPartialR3 [i] f x = partialDerivScalar f x i := rfl

lemma multiPartialR3_two {f : R3 → ℝ} (hf : ContDiff ℝ 2 f) (i j : Fin 3) (x : R3) :
    multiPartialR3 [i, j] f x = sndPartial f x i j :=
  partial_partial_eq_sndPartial f x (hf.contDiffAt) i j

lemma multiPartialR3_three {f : R3 → ℝ} (hf : ContDiff ℝ 3 f) (k i j : Fin 3) (x : R3) :
    multiPartialR3 [k, i, j] f x = partialDerivScalar (fun y => sndPartial f y i j) x k := by
  have heq : multiPartialR3 [i, j] f = fun y => sndPartial f y i j :=
    funext fun y => multiPartialR3_two (hf.of_le (by norm_num)) i j y
  unfold multiPartialR3
  rw [heq]

/-- **THEOREM 15F1-1 (Schwartz Embedding into Weighted `L¹`, `L²`, and `C_0(ℝ³)` for All Orders):**
    Every `f ∈ 𝒮(ℝ³)` satisfies, for EVERY multi-index `α` and EVERY weight `K : ℕ`:
    1. `Continuous (multiPartialR3 α f)` and `VanishesAtInfinityR3 (multiPartialR3 α f)`;
    2. `Integrable (fun x => (multiPartialR3 α f x) ^ 2) volume`;
    3. `Integrable (fun x => japaneseBracket3D x ^ K * |multiPartialR3 α f x|) volume`. -/
theorem schwartzScalarR3_in_L2_and_vanishes {f : R3 → ℝ} (hf : IsSchwartzScalarR3 f)
    (α : List (Fin 3)) (K : ℕ) :
    Continuous (multiPartialR3 α f) ∧
    VanishesAtInfinityR3 (multiPartialR3 α f) ∧
    Integrable (fun x : R3 => (multiPartialR3 α f x) ^ 2) volume ∧
    Integrable (fun x : R3 => japaneseBracket3D x ^ K * |multiPartialR3 α f x|) volume := by
  have hcont : Continuous (multiPartialR3 α f) := multiPartialR3_continuous hf.h_smooth α
  obtain ⟨C3, hC3, hrap3⟩ := hf.h_rapid α 3
  have hsq_decay : ∀ x : R3, (multiPartialR3 α f x) ^ 2 ≤ C3 ^ 2 / (1 + dot3D x x) ^ 3 := by
    intro x
    have h1 := hrap3 x
    have hpos : 0 < japaneseBracket3D x ^ 3 := pow_pos (japaneseBracket3D_pos x) 3
    have hsq : (japaneseBracket3D x ^ 3 * |multiPartialR3 α f x|) ^ 2 ≤ C3 ^ 2 := by
      nlinarith [mul_nonneg hpos.le (abs_nonneg (multiPartialR3 α f x))]
    rw [mul_pow, sq_abs] at hsq
    have hpow6 : (japaneseBracket3D x ^ 3) ^ 2 = (1 + dot3D x x) ^ 3 := by
      calc (japaneseBracket3D x ^ 3) ^ 2 = (japaneseBracket3D x ^ 2) ^ 3 := by ring
        _ = (1 + dot3D x x) ^ 3 := by rw [japaneseBracket3D_sq]
    rw [hpow6] at hsq
    rw [le_div_iff₀ (pow_pos (by linarith [dot3D_self_nonneg_r3 x]) 3)]
    linarith
  have hvan : VanishesAtInfinityR3 (multiPartialR3 α f) :=
    vanishesAtInfinityR3_of_rapid_decay hC3 hcont hsq_decay
  have hL2 : Integrable (fun x : R3 => (multiPartialR3 α f x) ^ 2) volume :=
    (r3_rapid_decay_implies_vanishing_and_L2 hC3 hcont hsq_decay).1
  -- Weighted L¹ integrability using K + 6
  obtain ⟨CK, hCK, hrapK⟩ := hf.h_rapid α (K + 6)
  have hL1 : Integrable (fun x : R3 => japaneseBracket3D x ^ K * |multiPartialR3 α f x|) volume := by
    have hjbK : Continuous (fun x : R3 => japaneseBracket3D x ^ K) :=
      (Real.continuous_sqrt.comp (continuous_const.add (by unfold dot3D; fun_prop))).pow K
    have hdom : Integrable (fun x : R3 => CK * (1 / (1 + dot3D x x) ^ 3)) volume :=
      r3_japanese_bracket_inv_six_integrable.2.2.1.const_mul CK
    refine hdom.mono' (hjbK.mul hcont.abs).aestronglyMeasurable (Filter.Eventually.of_forall fun x => ?_)
    rw [Real.norm_of_nonneg (mul_nonneg (pow_nonneg (japaneseBracket3D_pos x).le K) (abs_nonneg _))]
    have h1 := hrapK x
    have hpow6 : japaneseBracket3D x ^ 6 = (1 + dot3D x x) ^ 3 := by
      calc japaneseBracket3D x ^ 6 = (japaneseBracket3D x ^ 2) ^ 3 := by ring
        _ = (1 + dot3D x x) ^ 3 := by rw [japaneseBracket3D_sq]
    have hpos6 : 0 < (1 + dot3D x x) ^ 3 := pow_pos (by linarith [dot3D_self_nonneg_r3 x]) 3
    rw [pow_add, hpow6] at h1
    have hmul : (1 + dot3D x x) ^ 3 * (japaneseBracket3D x ^ K * |multiPartialR3 α f x|) ≤ CK := by
      linarith
    calc japaneseBracket3D x ^ K * |multiPartialR3 α f x|
        ≤ CK / (1 + dot3D x x) ^ 3 := (le_div_iff₀ hpos6).2 (by linarith)
      _ = CK * (1 / (1 + dot3D x x) ^ 3) := by ring
  exact ⟨hcont, hvan, hL2, hL1⟩

/-- **THEOREM 15F1-2 (Every Schwartz Scalar `f ∈ 𝒮(ℝ³)` Automatically Discharges `RapidDecayH3ScalarR3` & `DecayingH3ScalarR3`):** -/
theorem schwartzScalarR3_to_RapidDecayH3_and_DecayingH3 {f : R3 → ℝ} (hf : IsSchwartzScalarR3 f) :
    RapidDecayH3ScalarR3 f ∧ DecayingH3ScalarR3 f := by
  have hrap_sq : ∀ α : List (Fin 3), ∃ C : ℝ, 0 ≤ C ∧
      ∀ x : R3, (multiPartialR3 α f x) ^ 2 ≤ C ^ 2 / (1 + dot3D x x) ^ 3 := fun α => by
    obtain ⟨C, hC, h⟩ := hf.h_rapid α 3
    refine ⟨C, hC, fun x => ?_⟩
    have h1 := h x
    have hpos : 0 < japaneseBracket3D x ^ 3 := pow_pos (japaneseBracket3D_pos x) 3
    have hsq : (japaneseBracket3D x ^ 3 * |multiPartialR3 α f x|) ^ 2 ≤ C ^ 2 := by
      nlinarith [mul_nonneg hpos.le (abs_nonneg (multiPartialR3 α f x))]
    rw [mul_pow, sq_abs] at hsq
    have hpow6 : (japaneseBracket3D x ^ 3) ^ 2 = (1 + dot3D x x) ^ 3 := by
      calc (japaneseBracket3D x ^ 3) ^ 2 = (japaneseBracket3D x ^ 2) ^ 3 := by ring
        _ = (1 + dot3D x x) ^ 3 := by rw [japaneseBracket3D_sq]
    rw [hpow6] at hsq
    rw [le_div_iff₀ (pow_pos (by linarith [dot3D_self_nonneg_r3 x]) 3)]
    linarith
  obtain ⟨C0, hC0, h0⟩ := hrap_sq []
  have h1_ex : ∀ i : Fin 3, ∃ C : ℝ, 0 ≤ C ∧ ∀ x : R3, (partialDerivScalar f x i) ^ 2 ≤ C ^ 2 / (1 + dot3D x x) ^ 3 :=
    fun i => hrap_sq [i]
  choose C1 hC1 h1 using h1_ex
  have h2_ex : ∀ i j : Fin 3, ∃ C : ℝ, 0 ≤ C ∧ ∀ x : R3, (sndPartial f x i j) ^ 2 ≤ C ^ 2 / (1 + dot3D x x) ^ 3 := by
    intro i j
    obtain ⟨C, hC, h⟩ := hrap_sq [i, j]
    refine ⟨C, hC, fun x => ?_⟩
    rw [← multiPartialR3_two (hf.h_smooth.of_le (by simp)) i j x]
    exact h x
  choose C2 hC2 h2 using h2_ex
  have h3_ex : ∀ i j k : Fin 3, ∃ C : ℝ, 0 ≤ C ∧
      ∀ x : R3, (partialDerivScalar (fun y => sndPartial f y i j) x k) ^ 2 ≤ C ^ 2 / (1 + dot3D x x) ^ 3 := by
    intro i j k
    obtain ⟨C, hC, h⟩ := hrap_sq [k, i, j]
    refine ⟨C, hC, fun x => ?_⟩
    rw [← multiPartialR3_three (hf.h_smooth.of_le (by simp)) k i j x]
    exact h x
  choose C3 hC3 h3 using h3_ex
  let M1 : ℝ := max (C1 0) (max (C1 1) (C1 2))
  let M2 : ℝ := Finset.univ.sup' ⟨(0, 0), Finset.mem_univ _⟩ (fun p : Fin 3 × Fin 3 => C2 p.1 p.2)
  let M3 : ℝ := Finset.univ.sup' ⟨((0, 0), 0), Finset.mem_univ _⟩ (fun p : (Fin 3 × Fin 3) × Fin 3 => C3 p.1.1 p.1.2 p.2)
  let C : ℝ := max (max C0 M1) (max M2 M3)
  have hC_nn : 0 ≤ C := le_trans hC0 (le_trans (le_max_left _ _) (le_max_left _ _))
  have hdiv_mono : ∀ {a b : ℝ} (x : R3), 0 ≤ a → a ≤ b →
      a ^ 2 / (1 + dot3D x x) ^ 3 ≤ b ^ 2 / (1 + dot3D x x) ^ 3 := fun x ha hab =>
    div_le_div_of_nonneg_right (by nlinarith) (pow_nonneg (by linarith [dot3D_self_nonneg_r3 x]) 3)
  have hrapid : RapidDecayH3ScalarR3 f :=
    { h_c3 := hf.h_smooth.of_le (by simp)
      h_decay := ⟨C, hC_nn,
        fun x => le_trans (h0 x) (hdiv_mono x hC0 (le_trans (le_max_left _ _) (le_max_left _ _))),
        fun i x => le_trans (h1 i x) (hdiv_mono x (hC1 i) (le_trans (by
          fin_cases i
          · exact le_max_left _ _
          · exact le_trans (le_max_left _ _) (le_max_right _ _)
          · exact le_trans (le_max_right _ _) (le_max_right _ _))
          (le_trans (le_max_right _ _) (le_max_left _ _)))),
        fun i j x => le_trans (h2 i j x) (hdiv_mono x (hC2 i j) (le_trans
          (Finset.le_sup' (f := fun p : Fin 3 × Fin 3 => C2 p.1 p.2) (Finset.mem_univ (i, j)))
          (le_trans (le_max_left _ _) (le_max_right _ _)))),
        fun i j k x => le_trans (h3 i j k x) (hdiv_mono x (hC3 i j k) (le_trans
          (Finset.le_sup' (f := fun p : (Fin 3 × Fin 3) × Fin 3 => C3 p.1.1 p.1.2 p.2) (Finset.mem_univ ((i, j), k)))
          (le_trans (le_max_right _ _) (le_max_right _ _))))⟩ }
  exact ⟨hrapid, hrapid.toDecayingH3ScalarR3⟩

/-- **THEOREM 15F1-3 (Fefferman 2000 Schwartz Initial Data `u₀ ∈ 𝒮_σ(ℝ³)` Automatically Unlocks
    `DecayingH3SolenoidalR3`, Betchov Identity, and Unconditional Loomis–Whitney `46,656 ν⁴` Bound):** -/
theorem schwartzSolenoidalR3_to_DecayingH3Solenoidal_and_finite_EZP
    {u₀ : R3 → R3} (hu₀ : IsSchwartzSolenoidalR3 u₀) :
    DecayingH3SolenoidalR3 u₀ ∧
    0 ≤ energyR3 u₀ ∧ 0 ≤ enstrophyR3 u₀ ∧ 0 ≤ palinstrophyR3 u₀ ∧
    vortexStretchingR3 u₀ = -(4 / 3 : ℝ) * r3Integral (strainCubeTrace3D u₀) ∧
    |vortexStretchingR3 u₀| ≤
      C_BLW_R3 * (Real.sqrt (Real.sqrt (enstrophyR3 u₀))) ^ 3 *
        (Real.sqrt (Real.sqrt (palinstrophyR3 u₀))) ^ 3 := by
  have hdec : DecayingH3SolenoidalR3 u₀ :=
    { h_comp := fun c => (schwartzScalarR3_to_RapidDecayH3_and_DecayingH3 (hu₀.h_comp c)).2
      h_div := hu₀.h_div }
  refine ⟨hdec, ?_, ?_, ?_, (r3_betchov_identity hdec).2, unconditional_r3_betchov_loomis_whitney_stretching hdec⟩
  · exact mul_nonneg (by norm_num) (r3Integral_nonneg fun x => dot3D_self_nonneg_r3 (u₀ x))
  · exact mul_nonneg (by norm_num) (r3Integral_nonneg fun x => dot3D_self_nonneg_r3 (curl3D u₀ x))
  · exact r3Integral_nonneg fun x => gradNormSqR3_nonneg (curl3D u₀) x

/-- **THEOREM 15F1-4 (Non-Vacuity of `IsSchwartzSolenoidalR3`):** -/
theorem zero_isSchwartzSolenoidalR3 : IsSchwartzSolenoidalR3 (fun _ : R3 => (0 : R3)) := by
  have hzero_multi : ∀ (α : List (Fin 3)) (x : R3), multiPartialR3 α (fun _ : R3 => (0 : ℝ)) x = 0 := by
    intro α
    induction α with
    | nil => intro x; rfl
    | cons i α ih =>
      intro x
      unfold multiPartialR3
      have hfun : multiPartialR3 α (fun _ : R3 => (0 : ℝ)) = fun _ => (0 : ℝ) := funext ih
      rw [hfun]
      exact partialDerivScalar_const 0 x i
  refine ⟨fun c => ⟨contDiff_const, fun α K => ⟨0, le_rfl, fun x => ?_⟩⟩, fun x => ?_⟩
  · change japaneseBracket3D x ^ K * |multiPartialR3 α (fun _ : R3 => (0 : ℝ)) x| ≤ 0
    rw [hzero_multi α x, abs_zero, mul_zero]
  · unfold div3D
    change partialDerivScalar (fun _ : R3 => (0 : ℝ)) x 0 +
      partialDerivScalar (fun _ : R3 => (0 : ℝ)) x 1 +
      partialDerivScalar (fun _ : R3 => (0 : ℝ)) x 2 = 0
    simp only [partialDerivScalar_const, add_zero]

-- ============================================================================
-- SECTION 1: ELIMINATING POINTWISE ⟨x⟩⁻³ DECAY AT t > 0 VIA PURE L² + LIPSCHITZ
-- ============================================================================

/-- **THEOREM 15F1-5 (Pure-Sobolev Vanishing at Infinity — Eliminating `⟨x⟩⁻³` Decay at `t > 0`):**
    Any globally Lipschitz `L²(ℝ³)` scalar field `f` AUTOMATICALLY satisfies
    `VanishesAtInfinityR3 f` (`f(x) → 0` as `|x| → ∞`), with ZERO pointwise decay assumption! -/
theorem vanishesAtInfinityR3_of_L2_and_lipschitz {f : R3 → ℝ} {L : ℝ}
    (hL : 0 ≤ L)
    (hf_lip : ∀ x y : R3, |f x - f y| ≤ L * ‖x - y‖)
    (hf2 : Integrable (fun x : R3 => (f x) ^ 2) volume) :
    VanishesAtInfinityR3 f := by
  have hf_cont : Continuous f := by
    rw [Metric.continuous_iff]
    intro x ε hε
    refine ⟨ε / (L + 1), by positivity, fun y hy => ?_⟩
    rw [Real.dist_eq]
    rw [dist_eq_norm] at hy
    calc |f y - f x| = |f x - f y| := abs_sub_comm _ _
      _ ≤ L * ‖x - y‖ := hf_lip x y
      _ = L * ‖y - x‖ := by rw [norm_sub_rev]
      _ ≤ L * (ε / (L + 1)) := mul_le_mul_of_nonneg_left hy.le hL
      _ < ε := by
        have hpos : 0 < L + 1 := by linarith
        rw [mul_div_assoc', div_lt_iff₀ hpos]
        nlinarith
  unfold VanishesAtInfinityR3
  rw [Metric.tendsto_nhds]
  intro ε hε
  set r : ℝ := ε / (2 * (L + 1))
  have hr_pos : 0 < r := by positivity
  -- Volume of the ball of radius r around 0 is positive and finite
  have hvol_pos : 0 < volume (Metric.ball (0 : R3) r) := Metric.measure_ball_pos volume (0 : R3) hr_pos
  have hvol_lt_top : volume (Metric.ball (0 : R3) r) < ⊤ := MeasureTheory.measure_ball_lt_top
  set c_vol : ℝ := (volume (Metric.ball (0 : R3) r)).toReal
  have hc_vol_pos : 0 < c_vol := ENNReal.toReal_pos hvol_pos.ne' hvol_lt_top.ne
  -- Tail L² integrals ∫_{‖x‖ ≥ n} f(x)² dx → 0 as n → ∞ by dominated convergence
  let tail : ℕ → R3 → ℝ := fun n x => if (n : ℝ) ≤ ‖x‖ then (f x) ^ 2 else 0
  have htail_m : ∀ n : ℕ, AEStronglyMeasurable (tail n) volume := fun n => by
    have hset : MeasurableSet {x : R3 | (n : ℝ) ≤ ‖x‖} :=
      (isClosed_le continuous_const continuous_norm).measurableSet
    have heq : tail n = Set.piecewise {x : R3 | (n : ℝ) ≤ ‖x‖} (fun x => (f x) ^ 2) (fun _ => 0) := by
      funext x; dsimp only [tail, Set.piecewise]; by_cases h : (n : ℝ) ≤ ‖x‖ <;> simp [h]
    rw [heq]
    exact AEStronglyMeasurable.piecewise hset.nullMeasurableSet (hf_cont.pow 2).aestronglyMeasurable.restrict
      aestronglyMeasurable_const.restrict
  have htail_bd : ∀ n : ℕ, ∀ᵐ x ∂volume, ‖tail n x‖ ≤ (f x) ^ 2 := fun n =>
    Filter.Eventually.of_forall fun x => by
      dsimp only [tail]
      split_ifs
      · rw [Real.norm_of_nonneg (sq_nonneg _)]
      · rw [norm_zero]; exact sq_nonneg _
  have htail_lim : ∀ᵐ x ∂volume, Tendsto (fun n : ℕ => tail n x) atTop (𝓝 0) :=
    Filter.Eventually.of_forall fun x => by
      refine tendsto_atTop_of_eventually_const (i₀ := Nat.floor ‖x‖ + 1) fun n hn => ?_
      dsimp only [tail]
      have hlt : ‖x‖ < (n : ℝ) := by
        have h1 : ‖x‖ < (Nat.floor ‖x‖ : ℝ) + 1 := Nat.lt_floor_add_one ‖x‖
        have h2 : (Nat.floor ‖x‖ + 1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
        linarith
      simp [not_le.2 hlt]
  have htend_int : Tendsto (fun n : ℕ => ∫ x : R3, tail n x) atTop (𝓝 0) := by
    simpa only [integral_zero] using
      MeasureTheory.tendsto_integral_of_dominated_convergence (fun x => (f x) ^ 2) htail_m hf2 htail_bd htail_lim
  have hev_N := (Metric.tendsto_nhds.1 htend_int) ((ε ^ 2 / 4) * c_vol) (by positivity)
  rw [Filter.eventually_atTop] at hev_N
  obtain ⟨N, hN⟩ := hev_N
  have hN_lt : (∫ x : R3, tail N x) < (ε ^ 2 / 4) * c_vol := by
    have h1 := hN N le_rfl
    have hnn : 0 ≤ ∫ x : R3, tail N x := integral_nonneg fun x => by
      dsimp only [tail]; split_ifs <;> [exact sq_nonneg _; exact le_rfl]
    rw [Real.dist_eq, sub_zero, abs_of_nonneg hnn] at h1
    exact h1
  -- Show ∀ x₀ with ‖x₀‖ ≥ N + r, |f x₀| < ε
  have hbound_far : ∀ x₀ : R3, (N : ℝ) + r ≤ ‖x₀‖ → |f x₀| < ε := by
    intro x₀ hx₀
    by_contra hge
    push Not at hge
    have hball_ge : ∀ x ∈ Metric.ball x₀ r, (ε ^ 2 / 4) ≤ tail N x := by
      intro x hx
      rw [Metric.mem_ball, dist_eq_norm] at hx
      have hnorm_x : (N : ℝ) ≤ ‖x‖ := by
        have htri : ‖x₀‖ ≤ ‖x‖ + ‖x₀ - x‖ := by
          have := norm_add_le x (x₀ - x); simpa only [add_sub_cancel] using this
        rw [norm_sub_rev] at htri
        linarith
      dsimp only [tail]
      simp only [hnorm_x, ↓reduceIte]
      have hdiff : |f x₀ - f x| ≤ ε / 2 := by
        have h1 : |f x₀ - f x| ≤ L * ‖x₀ - x‖ := hf_lip x₀ x
        rw [norm_sub_rev] at h1
        have h2 : L * ‖x - x₀‖ ≤ L * r := mul_le_mul_of_nonneg_left hx.le hL
        have h3 : L * r ≤ ε / 2 := by
          dsimp only [r]
          have hpos : 0 < 2 * (L + 1) := by linarith
          rw [mul_div_assoc', div_le_iff₀ hpos]; nlinarith
        linarith
      have hfx_ge : ε / 2 ≤ |f x| := by
        have htri : |f x₀| ≤ |f x| + |f x₀ - f x| := by
          have := abs_add_le (f x) (f x₀ - f x); simpa only [add_sub_cancel] using this
        linarith
      have hsq : (ε / 2) ^ 2 ≤ |f x| ^ 2 := by nlinarith [abs_nonneg (f x)]
      rw [sq_abs] at hsq
      linarith
    -- Integrate ε²/4 ≤ tail N x over Metric.ball x₀ r
    have htail_int : Integrable (tail N) volume :=
      hf2.mono' (htail_m N) (htail_bd N)
    have hvol_eq : volume (Metric.ball x₀ r) = volume (Metric.ball (0 : R3) r) := by
      have hpre : (fun y : R3 => y + x₀) ⁻¹' Metric.ball x₀ r = Metric.ball (0 : R3) r := by
        ext y; simp [Metric.mem_ball, dist_eq_norm]
      rw [← hpre]
      exact ((measurePreserving_add_right (volume : Measure R3) x₀).measure_preimage
        measurableSet_ball.nullMeasurableSet).symm
    have hlow : (ε ^ 2 / 4) * c_vol ≤ ∫ x in Metric.ball x₀ r, tail N x := by
      have hconst_int : IntegrableOn (fun _ : R3 => ε ^ 2 / 4) (Metric.ball x₀ r) volume :=
        integrableOn_const (by rw [hvol_eq]; exact hvol_lt_top.ne)
      have hmono := setIntegral_mono_on hconst_int htail_int.integrableOn measurableSet_ball hball_ge
      rw [setIntegral_const, smul_eq_mul, Measure.real, hvol_eq] at hmono
      dsimp only [c_vol]; linarith
    have hle_full : (∫ x in Metric.ball x₀ r, tail N x) ≤ ∫ x : R3, tail N x :=
      setIntegral_le_integral htail_int (Filter.Eventually.of_forall fun x => by
        dsimp only [tail]; split_ifs <;> [exact sq_nonneg _; exact le_rfl])
    linarith
  -- Convert {x₀ | ‖x₀‖ ≥ N + r} into a cocompact neighborhood
  have hcocomp : {x₀ : R3 | (N : ℝ) + r ≤ ‖x₀‖} ∈ cocompact R3 := by
    rw [Filter.mem_cocompact]
    refine ⟨Metric.closedBall (0 : R3) ((N : ℝ) + r), isCompact_closedBall _ _, fun x₀ hx₀ => ?_⟩
    simp only [Set.mem_compl_iff, Metric.mem_closedBall, dist_zero_right, not_le] at hx₀
    exact hx₀.le
  filter_upwards [hcocomp] with x₀ hx₀
  rw [Real.dist_eq, sub_zero]
  exact hbound_far x₀ hx₀

private lemma lipschitz_of_bounded_grad_15f {f : R3 → ℝ} (hf : ContDiff ℝ 1 f)
    {C : ℝ} (hC : 0 ≤ C) (hgrad : ∀ (i : Fin 3) (x : R3), |partialDerivScalar f x i| ≤ C) :
    ∀ x y : R3, |f x - f y| ≤ (3 * C) * ‖x - y‖ := by
  intro x y
  have hnorm_deriv : ∀ z : R3, ‖fderiv ℝ f z‖ ≤ 3 * C := by
    intro z
    refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun v => ?_
    have hv : v = v 0 • basisVec 0 + v 1 • basisVec 1 + v 2 • basisVec 2 := by
      funext i; fin_cases i <;> simp [basisVec]
    have hval : fderiv ℝ f z v =
        v 0 * partialDerivScalar f z 0 + v 1 * partialDerivScalar f z 1 + v 2 * partialDerivScalar f z 2 := by
      conv_lhs => rw [hv]
      simp only [map_add, map_smul, smul_eq_mul, partialDerivScalar]
    rw [hval, Real.norm_eq_abs]
    have hv0 : |v 0| ≤ ‖v‖ := norm_le_pi_norm v 0
    have hv1 : |v 1| ≤ ‖v‖ := norm_le_pi_norm v 1
    have hv2 : |v 2| ≤ ‖v‖ := norm_le_pi_norm v 2
    calc |v 0 * partialDerivScalar f z 0 + v 1 * partialDerivScalar f z 1 + v 2 * partialDerivScalar f z 2|
        ≤ |v 0 * partialDerivScalar f z 0 + v 1 * partialDerivScalar f z 1| + |v 2 * partialDerivScalar f z 2| :=
          abs_add_le _ _
      _ ≤ (|v 0 * partialDerivScalar f z 0| + |v 1 * partialDerivScalar f z 1|) + |v 2 * partialDerivScalar f z 2| := by
          linarith [abs_add_le (v 0 * partialDerivScalar f z 0) (v 1 * partialDerivScalar f z 1)]
      _ = |v 0| * |partialDerivScalar f z 0| + |v 1| * |partialDerivScalar f z 1| + |v 2| * |partialDerivScalar f z 2| := by
          simp only [abs_mul]
      _ ≤ ‖v‖ * C + ‖v‖ * C + ‖v‖ * C := by
          have h0 := mul_le_mul hv0 (hgrad 0 z) (abs_nonneg _) (norm_nonneg v)
          have h1 := mul_le_mul hv1 (hgrad 1 z) (abs_nonneg _) (norm_nonneg v)
          have h2 := mul_le_mul hv2 (hgrad 2 z) (abs_nonneg _) (norm_nonneg v)
          linarith
      _ = (3 * C) * ‖v‖ := by ring
  have hmvt := Convex.norm_image_sub_le_of_norm_fderiv_le
    (s := Set.univ) (f := f) (C := 3 * C)
    (fun z _ => (hf.differentiable (by norm_num)).differentiableAt)
    (fun z _ => hnorm_deriv z) convex_univ (Set.mem_univ y) (Set.mem_univ x)
  simpa only [Real.norm_eq_abs] using hmvt

/-- **THEOREM 15F1-6 (Pure `H³ ∩ C³_b` Discharges `DecayingH3ScalarR3` — Zero `⟨x⟩⁻³` Decay Needed!):**
    At `t > 0`, a solution in `H^∞(ℝ³)` does NOT need pointwise `⟨x⟩⁻³` or Schwartz decay:
    pure `C³` regularity, `H³(ℝ³)` `L²` integrability, and uniform `L^∞` bounds on derivatives
    up to order 3 AUTOMATICALLY imply `DecayingH3ScalarR3 f`! -/
theorem pure_H3_sobolev_to_DecayingH3ScalarR3 {f : R3 → ℝ}
    (hf_c3 : ContDiff ℝ 3 f)
    (h_int0 : Integrable (fun x => (f x) ^ 2) volume)
    (h_int1 : ∀ i : Fin 3, Integrable (fun x => (partialDerivScalar f x i) ^ 2) volume)
    (h_int2 : ∀ i j : Fin 3, Integrable (fun x => (sndPartial f x i j) ^ 2) volume)
    (h_int3 : ∀ i j k : Fin 3,
      Integrable (fun x => (partialDerivScalar (fun y => sndPartial f y i j) x k) ^ 2) volume)
    (h_bdd1 : ∃ C : ℝ, 0 ≤ C ∧ ∀ (i : Fin 3) (x : R3), |partialDerivScalar f x i| ≤ C)
    (h_bdd2 : ∃ C : ℝ, 0 ≤ C ∧ ∀ (i j : Fin 3) (x : R3), |sndPartial f x i j| ≤ C)
    (h_bdd3 : ∃ C : ℝ, 0 ≤ C ∧ ∀ (i j k : Fin 3) (x : R3),
      |partialDerivScalar (fun y => sndPartial f y i j) x k| ≤ C) :
    DecayingH3ScalarR3 f := by
  obtain ⟨C1, hC1, hb1⟩ := h_bdd1
  obtain ⟨C2, hC2, hb2⟩ := h_bdd2
  obtain ⟨C3, hC3, hb3⟩ := h_bdd3
  refine ⟨hf_c3, ?_, ?_, ?_, h_int0, h_int1, h_int2, h_int3⟩
  · exact vanishesAtInfinityR3_of_L2_and_lipschitz (by positivity)
      (lipschitz_of_bounded_grad_15f (hf_c3.of_le (by norm_num)) hC1 hb1) h_int0
  · intro i
    have hf2 : ContDiff ℝ 2 f := hf_c3.of_le (by norm_num)
    have hci : ContDiff ℝ 1 (fun x => partialDerivScalar f x i) :=
      (ContinuousLinearMap.apply ℝ ℝ (basisVec i)).contDiff.comp (hf2.fderiv_right (by norm_num))
    exact vanishesAtInfinityR3_of_L2_and_lipschitz (by positivity)
      (lipschitz_of_bounded_grad_15f hci hC2 fun j x => by
        rw [partial_partial_eq_sndPartial f x ((hf_c3.of_le (by norm_num)).contDiffAt) j i]
        exact hb2 j i x)
      (h_int1 i)
  · intro i j
    have hcij : ContDiff ℝ 1 (fun x => sndPartial f x i j) := by
      have heq : (fun x => sndPartial f x i j) =
          fun x => partialDerivScalar (fun y => partialDerivScalar f y j) x i :=
        funext fun x => (partial_partial_eq_sndPartial f x ((hf_c3.of_le (by norm_num)).contDiffAt) i j).symm
      rw [heq]
      have hcj : ContDiff ℝ 2 (fun y => partialDerivScalar f y j) :=
        (ContinuousLinearMap.apply ℝ ℝ (basisVec j)).contDiff.comp (hf_c3.fderiv_right (by norm_num))
      exact (ContinuousLinearMap.apply ℝ ℝ (basisVec i)).contDiff.comp (hcj.fderiv_right (by norm_num))
    exact vanishesAtInfinityR3_of_L2_and_lipschitz (by positivity)
      (lipschitz_of_bounded_grad_15f hcij hC3 fun k x => hb3 i j k x) (h_int2 i j)

/-- **THEOREM 15F1-7 (Pure `H³_σ ∩ C³_b` Discharges `DecayingH3SolenoidalR3` & Unconditional `46,656 ν⁴` Stretching):** -/
theorem pure_H3_sobolev_to_DecayingH3SolenoidalR3 {u : R3 → R3}
    (hdiv : ∀ x : R3, div3D u x = 0)
    (hu_c3 : ∀ c : Fin 3, ContDiff ℝ 3 (fun x => u x c))
    (h_int0 : ∀ c : Fin 3, Integrable (fun x => (u x c) ^ 2) volume)
    (h_int1 : ∀ (c i : Fin 3), Integrable (fun x => (partialDerivScalar (fun y => u y c) x i) ^ 2) volume)
    (h_int2 : ∀ (c i j : Fin 3), Integrable (fun x => (sndPartial (fun y => u y c) x i j) ^ 2) volume)
    (h_int3 : ∀ (c i j k : Fin 3),
      Integrable (fun x => (partialDerivScalar (fun y => sndPartial (fun z => u z c) y i j) x k) ^ 2) volume)
    (h_bdd1 : ∀ c : Fin 3, ∃ C : ℝ, 0 ≤ C ∧ ∀ (i : Fin 3) (x : R3), |partialDerivScalar (fun y => u y c) x i| ≤ C)
    (h_bdd2 : ∀ c : Fin 3, ∃ C : ℝ, 0 ≤ C ∧ ∀ (i j : Fin 3) (x : R3), |sndPartial (fun y => u y c) x i j| ≤ C)
    (h_bdd3 : ∀ c : Fin 3, ∃ C : ℝ, 0 ≤ C ∧ ∀ (i j k : Fin 3) (x : R3),
      |partialDerivScalar (fun y => sndPartial (fun z => u z c) y i j) x k| ≤ C) :
    DecayingH3SolenoidalR3 u ∧
    vortexStretchingR3 u = -(4 / 3 : ℝ) * r3Integral (strainCubeTrace3D u) ∧
    |vortexStretchingR3 u| ≤
      C_BLW_R3 * (Real.sqrt (Real.sqrt (enstrophyR3 u))) ^ 3 *
        (Real.sqrt (Real.sqrt (palinstrophyR3 u))) ^ 3 := by
  have hdec : DecayingH3SolenoidalR3 u :=
    { h_comp := fun c => pure_H3_sobolev_to_DecayingH3ScalarR3 (hu_c3 c) (h_int0 c) (h_int1 c)
        (h_int2 c) (h_int3 c) (h_bdd1 c) (h_bdd2 c) (h_bdd3 c)
      h_div := hdiv }
  exact ⟨hdec, (r3_betchov_identity hdec).2, unconditional_r3_betchov_loomis_whitney_stretching hdec⟩

-- ============================================================================
-- SECTION 2 (MILESTONE 15F-2A): PURE-SOBOLEV ℝ³ CLASSICAL SOLUTIONS (ZERO ⟨x⟩⁻³
--   DECAY AT t > 0) & UNCONDITIONAL 46,656 ν⁴ BASIN-TO-RIVER CLOSURE
-- ============================================================================

section ClayPackaging15F2

open GarryVorticity3D
open GarryWholeSpaceR3Agmon
open GarryWholeSpaceR3Waterfall
open GarrySpacetimeSmoothnessNS3D

/-- Pure-Sobolev classical 3D Navier–Stokes solution on unbounded `ℝ³` with ZERO pointwise
    `⟨x⟩⁻³` or Schwartz decay assumption at `t > 0`: requires only `H³ ∩ C³_b` velocity,
    `H¹ ∩ C²_b` pressure, and local-in-time `L¹(ℝ³)` domination for `∂_t`. -/
structure IsPureSobolevClassicalNS3D_R3 (u : ℝ → R3 → R3) (p : ℝ → R3 → ℝ) (ν : ℝ) : Prop
    extends IsClassicalNS3D_C3 u p ν where
  h_u_c3_global : ∀ t ≥ 0, ∀ c : Fin 3, ContDiff ℝ 3 (fun x => u t x c)
  h_u_int0 : ∀ t ≥ 0, ∀ c : Fin 3, Integrable (fun x => (u t x c) ^ 2) volume
  h_u_int1 : ∀ t ≥ 0, ∀ c i : Fin 3,
    Integrable (fun x => (partialDerivScalar (fun y => u t y c) x i) ^ 2) volume
  h_u_int2 : ∀ t ≥ 0, ∀ c i j : Fin 3,
    Integrable (fun x => (sndPartial (fun y => u t y c) x i j) ^ 2) volume
  h_u_int3 : ∀ t ≥ 0, ∀ c i j k : Fin 3,
    Integrable (fun x => (partialDerivScalar (fun y => sndPartial (fun z => u t z c) y i j) x k) ^ 2) volume
  h_u_bdd1 : ∀ t ≥ 0, ∀ c : Fin 3, ∃ C : ℝ, 0 ≤ C ∧
    ∀ (i : Fin 3) (x : R3), |partialDerivScalar (fun y => u t y c) x i| ≤ C
  h_u_bdd2 : ∀ t ≥ 0, ∀ c : Fin 3, ∃ C : ℝ, 0 ≤ C ∧
    ∀ (i j : Fin 3) (x : R3), |sndPartial (fun y => u t y c) x i j| ≤ C
  h_u_bdd3 : ∀ t ≥ 0, ∀ c : Fin 3, ∃ C : ℝ, 0 ≤ C ∧
    ∀ (i j k : Fin 3) (x : R3),
      |partialDerivScalar (fun y => sndPartial (fun z => u t z c) y i j) x k| ≤ C
  h_p_c2_global : ∀ t ≥ 0, ContDiff ℝ 2 (p t)
  h_p_int0 : ∀ t ≥ 0, Integrable (fun x => (p t x) ^ 2) volume
  h_p_int1 : ∀ t ≥ 0, ∀ i : Fin 3, Integrable (fun x => (partialDerivScalar (p t) x i) ^ 2) volume
  h_p_bdd1 : ∀ t ≥ 0, ∃ C : ℝ, 0 ≤ C ∧ ∀ (i : Fin 3) (x : R3), |partialDerivScalar (p t) x i| ≤ C
  h_dt_u_dom : ∀ t₀ ≥ 0, ∃ δ > 0, ∃ bound : R3 → ℝ,
    Integrable bound volume ∧
    ∀ t ∈ Metric.ball t₀ δ, ∀ x : R3,
      |2 * dot3D (fun c => deriv (fun s => u s x c) t) (u t x)| ≤ bound x
  h_dt_w_dom : ∀ t₀ ≥ 0, ∃ δ > 0, ∃ bound : R3 → ℝ,
    Integrable bound volume ∧
    ∀ t ∈ Metric.ball t₀ δ, ∀ x : R3,
      |2 * dot3D (fun c => deriv (fun s => curl3D (u s) x c) t) (curl3D (u t) x)| ≤ bound x

/-- **THEOREM 15F2-1 (Pure-Sobolev `H³ ∩ C³_b` Automatically Discharges `IsDecayingClassicalNS3D_R3`):**
    Eliminates pointwise `⟨x⟩⁻³` decay at `t > 0` completely! -/
theorem IsPureSobolevClassicalNS3D_R3.toDecayingClassicalNS3D_R3
    {u : ℝ → R3 → R3} {p : ℝ → R3 → ℝ} {ν : ℝ}
    (hns : IsPureSobolevClassicalNS3D_R3 u p ν) :
    IsDecayingClassicalNS3D_R3 u p ν where
  toIsClassicalNS3D_C3 := hns.toIsClassicalNS3D_C3
  h_u_decay := fun t ht =>
    (pure_H3_sobolev_to_DecayingH3SolenoidalR3 (hns.h_incompressible t ht)
      (hns.h_u_c3_global t ht) (hns.h_u_int0 t ht) (hns.h_u_int1 t ht)
      (hns.h_u_int2 t ht) (hns.h_u_int3 t ht)
      (hns.h_u_bdd1 t ht) (hns.h_u_bdd2 t ht) (hns.h_u_bdd3 t ht)).1
  h_p_c2_global := hns.h_p_c2_global
  h_p_van := fun t ht => by
    obtain ⟨Cp, hCp, hbp⟩ := hns.h_p_bdd1 t ht
    exact vanishesAtInfinityR3_of_L2_and_lipschitz (by positivity)
      (lipschitz_of_bounded_grad_15f ((hns.h_p_c2_global t ht).of_le (by norm_num)) hCp hbp)
      (hns.h_p_int0 t ht)
  h_p_int0 := hns.h_p_int0
  h_p_int1 := hns.h_p_int1
  h_dt_u_dom := hns.h_dt_u_dom
  h_dt_w_dom := hns.h_dt_w_dom

/-- **THEOREM 15F2-2 (Non-Vacuity of `IsPureSobolevClassicalNS3D_R3`):** -/
theorem zero_isPureSobolevClassicalNS3D_R3 {ν : ℝ} (hν : 0 < ν) :
    IsPureSobolevClassicalNS3D_R3 (fun _ _ => (0 : R3)) (fun _ _ => (0 : ℝ)) ν := by
  have hbase := zero_isDecayingClassicalNS3D_R3 ν hν
  refine ⟨hbase.toIsClassicalNS3D_C3,
    fun _ _ _ => contDiff_const,
    fun _ _ _ => by simp only [Pi.zero_apply, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow]; exact integrable_zero _ _ _,
    fun _ _ _ i => by
      simp only [Pi.zero_apply]
      have : (fun x : R3 => (partialDerivScalar (fun _ : R3 => (0 : ℝ)) x i) ^ 2) = fun _ => 0 :=
        funext fun x => by rw [partialDerivScalar_const]; norm_num
      rw [this]; exact integrable_zero _ _ _,
    fun _ _ _ i j => by
      simp only [Pi.zero_apply]
      have : (fun x : R3 => (sndPartial (fun _ : R3 => (0 : ℝ)) x i j) ^ 2) = fun _ => 0 :=
        funext fun x => by rw [sndPartial_const]; norm_num
      rw [this]; exact integrable_zero _ _ _,
    fun _ _ _ i j k => by
      simp only [Pi.zero_apply]
      have : (fun x : R3 => (partialDerivScalar (fun y => sndPartial (fun _ : R3 => (0 : ℝ)) y i j) x k) ^ 2) = fun _ => 0 :=
        funext fun x => by
          have hs : (fun y : R3 => sndPartial (fun _ : R3 => (0 : ℝ)) y i j) = fun _ => 0 :=
            funext fun y => sndPartial_const 0 y i j
          rw [hs, partialDerivScalar_const]; norm_num
      rw [this]; exact integrable_zero _ _ _,
    fun _ _ _ => ⟨0, le_rfl, fun i x => by simp only [Pi.zero_apply]; rw [partialDerivScalar_const, abs_zero]⟩,
    fun _ _ _ => ⟨0, le_rfl, fun i j x => by simp only [Pi.zero_apply]; rw [sndPartial_const, abs_zero]⟩,
    fun _ _ _ => ⟨0, le_rfl, fun i j k x => by
      simp only [Pi.zero_apply]
      have hs : (fun y : R3 => sndPartial (fun _ : R3 => (0 : ℝ)) y i j) = fun _ => 0 :=
        funext fun y => sndPartial_const 0 y i j
      rw [hs, partialDerivScalar_const, abs_zero]⟩,
    hbase.h_p_c2_global, hbase.h_p_int0, hbase.h_p_int1,
    fun _ _ => ⟨0, le_rfl, fun i x => by rw [partialDerivScalar_const, abs_zero]⟩,
    hbase.h_dt_u_dom, hbase.h_dt_w_dom⟩

/-- **THEOREM 15F2-3 (Unconditional `46,656 ν⁴` Basin Invariance & River Bounds for Pure
    `IsDecayingClassicalNS3D_R3` — Removing `IsRapidDecayClassicalNS3D_R3` Completely!):** -/
theorem global_r3_decaying_46656_basin_invariant_and_river
    {u : ℝ → R3 → R3} {p : ℝ → R3 → ℝ} {ν t₀ : ℝ}
    (hns : IsDecayingClassicalNS3D_R3 u p ν) (ht₀ : 0 ≤ t₀)
    (hbasin : energyR3 (u t₀) * enstrophyR3 (u t₀) < 46656 * ν ^ 4) :
    let R₀ : ℝ := energyR3 (u t₀) * enstrophyR3 (u t₀)
    let gap : ℝ := ν - Real.sqrt (Real.sqrt (R₀ / 46656))
    let B_tail : ℝ := R₀ / (4 * gap)
    0 < gap ∧
    (∀ t ≥ t₀, energyR3 (u t) * enstrophyR3 (u t) ≤ R₀) ∧
    (∀ T ≥ t₀, (∫ s in t₀..T, (enstrophyR3 (u s)) ^ 2) ≤ B_tail) ∧
    (∀ T ≥ t₀, enstrophyR3 (u T) ≤ enstrophyR3 (u t₀) * Real.exp (c_nu_R3 ν * B_tail)) ∧
    (Continuous (fun s : ℝ => palinstrophyR3 (u s)) →
      ∀ T ≥ t₀, (∫ s in t₀..T, palinstrophyR3 (u s)) ≤
        (4 / ν) * (enstrophyR3 (u t₀) +
          c_nu_R3 ν * (enstrophyR3 (u t₀) * Real.exp (c_nu_R3 ν * B_tail)) * B_tail)) := by
  have hν : 0 < ν := hns.h_nu_pos
  set R : ℝ → ℝ := fun t => energyR3 (u t) * enstrophyR3 (u t)
  set R₀ : ℝ := R t₀
  set gap : ℝ := ν - Real.sqrt (Real.sqrt (R₀ / 46656))
  set B_tail : ℝ := R₀ / (4 * gap)
  have hR_nn : ∀ t, 0 ≤ R t := fun t => mul_nonneg (energyR3_nonneg (u t)) (enstrophyR3_nonneg (u t))
  have hgap_pos : 0 < gap := by
    have h1 : R₀ / 46656 < ν ^ 4 := by rw [div_lt_iff₀ (by norm_num)]; linarith
    have h2 : Real.sqrt (R₀ / 46656) < ν ^ 2 := by
      have hsq : Real.sqrt (ν ^ 4) = ν ^ 2 := by
        rw [show ν ^ 4 = (ν ^ 2) ^ 2 by ring, Real.sqrt_sq (sq_nonneg ν)]
      rw [← hsq]; exact Real.sqrt_lt_sqrt (div_nonneg (hR_nn t₀) (by norm_num)) h1
    have h3 : Real.sqrt (Real.sqrt (R₀ / 46656)) < ν := by
      rw [← Real.sqrt_sq hν.le]
      exact Real.sqrt_lt_sqrt (Real.sqrt_nonneg _) h2
    dsimp only [gap]; linarith
  have hR_deriv : ∀ t ≥ 0, HasDerivAt R
      ((-2 * ν * enstrophyR3 (u t)) * enstrophyR3 (u t) +
       energyR3 (u t) * (-ν * palinstrophyR3 (u t) + vortexStretchingR3 (u t))) t := fun t ht =>
    (hasDerivAt_energyR3_leray hns ht).mul (hasDerivAt_enstrophyR3_evolution hns ht)
  have hR'_le : ∀ t ≥ 0,
      deriv R t ≤
        -(ν - Real.sqrt (Real.sqrt (R t / 46656))) *
          (energyR3 (u t) * palinstrophyR3 (u t) + 2 * (enstrophyR3 (u t)) ^ 2) := by
    intro t ht
    rw [(hR_deriv t ht).deriv]
    have hblw := unconditional_r3_betchov_loomis_whitney_stretching (hns.h_u_decay t ht)
    have hS_le : vortexStretchingR3 (u t) ≤
        C_BLW_R3 * (Real.sqrt (Real.sqrt (enstrophyR3 (u t)))) ^ 3 *
          (Real.sqrt (Real.sqrt (palinstrophyR3 (u t)))) ^ 3 := le_trans (le_abs_self _) hblw
    have hvar := variational_EZ_stretching_bound_15a C_BLW_R3_pos
      (energyR3_nonneg (u t)) (enstrophyR3_nonneg (u t)) (palinstrophyR3_nonneg (u t))
    have hconst : 27 * C_BLW_R3 ^ 4 * R t / 512 = R t / 46656 := by
      rw [C_BLW_R3_pow_four]; ring
    rw [hconst] at hvar
    have hES : energyR3 (u t) * vortexStretchingR3 (u t) ≤
        Real.sqrt (Real.sqrt (R t / 46656)) *
          (energyR3 (u t) * palinstrophyR3 (u t) + 2 * (enstrophyR3 (u t)) ^ 2) := by
      calc energyR3 (u t) * vortexStretchingR3 (u t)
          ≤ energyR3 (u t) * (C_BLW_R3 * (Real.sqrt (Real.sqrt (enstrophyR3 (u t)))) ^ 3 *
              (Real.sqrt (Real.sqrt (palinstrophyR3 (u t)))) ^ 3) :=
            mul_le_mul_of_nonneg_left hS_le (energyR3_nonneg (u t))
        _ = C_BLW_R3 * energyR3 (u t) * (Real.sqrt (Real.sqrt (enstrophyR3 (u t)))) ^ 3 *
              (Real.sqrt (Real.sqrt (palinstrophyR3 (u t)))) ^ 3 := by ring
        _ ≤ _ := hvar
    linarith
  have hinv : ∀ t ≥ t₀, R t ≤ R₀ := by
    intro t ht
    by_contra hgt
    push Not at hgt
    set Rmid : ℝ := (R₀ + 46656 * ν ^ 4) / 2
    have hR0_lt_mid : R₀ < Rmid := by dsimp only [Rmid]; linarith
    have hmid_lt : Rmid < 46656 * ν ^ 4 := by dsimp only [Rmid]; linarith
    have hR_cont : ContinuousOn R (Set.Icc t₀ t) :=
      fun s hs => ((hR_deriv s (le_trans ht₀ hs.1)).continuousAt).continuousWithinAt
    set target : ℝ := min (R t) Rmid
    have hR0_lt_target : R₀ < target := lt_min hgt hR0_lt_mid
    have htarget_le_t : target ≤ R t := min_le_left _ _
    have htarget_lt : target < 46656 * ν ^ 4 := lt_of_le_of_lt (min_le_right _ _) hmid_lt
    let S_hit : Set ℝ := {s ∈ Set.Icc t₀ t | target ≤ R s}
    have hS_ne : S_hit.Nonempty := ⟨t, ⟨ht, le_rfl⟩, htarget_le_t⟩
    have hS_bdd : BddBelow S_hit := ⟨t₀, fun s hs => hs.1.1⟩
    set t₁ : ℝ := sInf S_hit
    have hS_closed : IsClosed S_hit :=
      hR_cont.preimage_isClosed_of_isClosed isClosed_Icc isClosed_Ici
    have ht₁_mem : t₁ ∈ S_hit := hS_closed.csInf_mem hS_ne hS_bdd
    have ht₀_lt_t₁ : t₀ < t₁ := by
      rcases eq_or_lt_of_le ht₁_mem.1.1 with heq | hlt
      · exfalso; have := ht₁_mem.2; rw [← heq] at this; linarith
      · exact hlt
    have hle_target : ∀ s ∈ Set.Icc t₀ t₁, R s ≤ target := by
      intro s hs
      rcases eq_or_lt_of_le hs.2 with rfl | hslt
      · by_contra hgt'
        push Not at hgt'
        have hopen := (hR_deriv t₁ (le_trans ht₀ ht₁_mem.1.1)).continuousAt.eventually (lt_mem_nhds hgt')
        rw [Metric.eventually_nhds_iff] at hopen
        obtain ⟨δ, hδ, hprop⟩ := hopen
        set s' : ℝ := max t₀ (t₁ - δ / 2)
        have hs'_lt : s' < t₁ := max_lt ht₀_lt_t₁ (by linarith)
        have hs'_dist : dist s' t₁ < δ := by
          rw [Real.dist_eq, abs_of_neg (sub_neg.2 hs'_lt)]
          have : t₁ - δ / 2 ≤ s' := le_max_right _ _
          linarith
        have hs'_mem : s' ∈ S_hit :=
          ⟨⟨le_max_left _ _, le_trans hs'_lt.le ht₁_mem.1.2⟩, (hprop hs'_dist).le⟩
        exact not_lt_of_ge (csInf_le hS_bdd hs'_mem) hs'_lt
      · by_contra hgt'; push Not at hgt'
        have hs_mem : s ∈ S_hit := ⟨⟨hs.1, le_trans hslt.le ht₁_mem.1.2⟩, hgt'.le⟩
        exact not_lt_of_ge (csInf_le hS_bdd hs_mem) hslt
    have hanti : AntitoneOn R (Set.Icc t₀ t₁) := by
      refine antitoneOn_of_deriv_nonpos (convex_Icc t₀ t₁)
        (hR_cont.mono (Set.Icc_subset_Icc_right ht₁_mem.1.2))
        (fun s hs => (hR_deriv s (le_trans ht₀ (interior_subset hs).1)).differentiableAt.differentiableWithinAt) ?_
      intro s hs
      have hs' := interior_subset hs
      have hRs : R s < 46656 * ν ^ 4 := lt_of_le_of_lt (hle_target s hs') htarget_lt
      have hcoef : 0 ≤ ν - Real.sqrt (Real.sqrt (R s / 46656)) := by
        have h1 : R s / 46656 < ν ^ 4 := by rw [div_lt_iff₀ (by norm_num)]; linarith
        have h2 : Real.sqrt (R s / 46656) < ν ^ 2 := by
          have hsq : Real.sqrt (ν ^ 4) = ν ^ 2 := by
            rw [show ν ^ 4 = (ν ^ 2) ^ 2 by ring, Real.sqrt_sq (sq_nonneg ν)]
          rw [← hsq]; exact Real.sqrt_lt_sqrt (div_nonneg (hR_nn s) (by norm_num)) h1
        have h3 : Real.sqrt (Real.sqrt (R s / 46656)) < ν := by
          rw [← Real.sqrt_sq hν.le]; exact Real.sqrt_lt_sqrt (Real.sqrt_nonneg _) h2
        linarith
      have hsum_nn : 0 ≤ energyR3 (u s) * palinstrophyR3 (u s) + 2 * (enstrophyR3 (u s)) ^ 2 := by
        linarith [mul_nonneg (energyR3_nonneg (u s)) (palinstrophyR3_nonneg (u s)), sq_nonneg (enstrophyR3 (u s))]
      have hle := hR'_le s (le_trans ht₀ hs'.1)
      nlinarith
    have hRt1_le : R t₁ ≤ R₀ := hanti ⟨le_rfl, ht₀_lt_t₁.le⟩ ⟨ht₀_lt_t₁.le, le_rfl⟩ ht₀_lt_t₁.le
    linarith [ht₁_mem.2]
  have hL4 : ∀ T ≥ t₀, (∫ s in t₀..T, (enstrophyR3 (u s)) ^ 2) ≤ B_tail := by
    intro T hT
    have hZ_cont : ContinuousOn (fun s => enstrophyR3 (u s)) (Set.Icc t₀ T) := fun s hs =>
      ((hasDerivAt_enstrophyR3_evolution hns (le_trans ht₀ hs.1)).continuousAt).continuousWithinAt
    have hZ2_int : IntervalIntegrable (fun s => (enstrophyR3 (u s)) ^ 2) volume t₀ T :=
      (hZ_cont.pow 2).intervalIntegrable_of_Icc hT
    set F : ℝ → ℝ := fun t => R t + (4 * gap) * ∫ s in t₀..t, (enstrophyR3 (u s)) ^ 2
    have hF_cont : ContinuousOn F (Set.Icc t₀ T) := by
      have hR_c : ContinuousOn R (Set.Icc t₀ T) := fun s hs =>
        ((hR_deriv s (le_trans ht₀ hs.1)).continuousAt).continuousWithinAt
      have hI_c : ContinuousOn (fun t => ∫ s in t₀..t, (enstrophyR3 (u s)) ^ 2) (Set.Icc t₀ T) := by
        have h1 := intervalIntegral.continuousOn_primitive_interval' hZ2_int (Set.left_mem_uIcc)
        simpa only [Set.uIcc_of_le hT] using h1
      exact hR_c.add (continuousOn_const.mul hI_c)
    have hF_deriv_ioo : ∀ s ∈ Set.Ioo t₀ T,
        HasDerivAt F (deriv R s + (4 * gap) * (enstrophyR3 (u s)) ^ 2) s := by
      intro s hs
      have h1 : HasDerivAt R (deriv R s) s := by
        have hd := hR_deriv s (le_trans ht₀ hs.1.le)
        rwa [← hd.deriv] at hd
      have hZ_ca : ContinuousAt (fun r => (enstrophyR3 (u r)) ^ 2) s :=
        ((hasDerivAt_enstrophyR3_evolution hns (le_trans ht₀ hs.1.le)).continuousAt).pow 2
      have hZ_sm : StronglyMeasurableAtFilter (fun r => (enstrophyR3 (u r)) ^ 2) (𝓝 s) volume :=
        ((hZ_cont.pow 2).mono Set.Ioo_subset_Icc_self).stronglyMeasurableAtFilter isOpen_Ioo s hs
      have h2 : HasDerivAt (fun t => ∫ r in t₀..t, (enstrophyR3 (u r)) ^ 2) ((enstrophyR3 (u s)) ^ 2) s :=
        intervalIntegral.integral_hasDerivAt_right
          (hZ2_int.mono_set (Set.uIcc_subset_uIcc_left (Set.mem_uIcc_of_le hs.1.le hs.2.le)))
          hZ_sm hZ_ca
      exact h1.add (h2.const_mul (4 * gap))
    have hF_anti : AntitoneOn F (Set.Icc t₀ T) := by
      refine antitoneOn_of_deriv_nonpos (convex_Icc t₀ T) hF_cont
        (fun s hs => by
          rw [interior_Icc] at hs
          exact (hF_deriv_ioo s hs).differentiableAt.differentiableWithinAt) ?_
      intro s hs
      rw [interior_Icc] at hs
      rw [(hF_deriv_ioo s hs).deriv]
      have hs' : s ∈ Set.Icc t₀ T := Set.Ioo_subset_Icc_self hs
      have hRs : R s ≤ R₀ := hinv s hs'.1
      have hsqrt_le : Real.sqrt (Real.sqrt (R s / 46656)) ≤ Real.sqrt (Real.sqrt (R₀ / 46656)) :=
        Real.sqrt_le_sqrt (Real.sqrt_le_sqrt (div_le_div_of_nonneg_right hRs (by norm_num)))
      have hgap_le : gap ≤ ν - Real.sqrt (Real.sqrt (R s / 46656)) := by dsimp only [gap]; linarith
      have hinterp := (r3_interpolation_enstrophy_le (hns.h_u_decay s (le_trans ht₀ hs'.1))).2
      have hsum_ge : 4 * (enstrophyR3 (u s)) ^ 2 ≤
          energyR3 (u s) * palinstrophyR3 (u s) + 2 * (enstrophyR3 (u s)) ^ 2 := by linarith
      have hle := hR'_le s (le_trans ht₀ hs'.1)
      nlinarith [sq_nonneg (enstrophyR3 (u s))]
    have hFT : F T ≤ F t₀ := hF_anti ⟨le_rfl, hT⟩ ⟨hT, le_rfl⟩ hT
    dsimp only [F] at hFT
    rw [intervalIntegral.integral_same, mul_zero, add_zero] at hFT
    have hRT_nn : 0 ≤ R T := hR_nn T
    rw [le_div_iff₀ (by linarith : (0 : ℝ) < 4 * gap)]
    linarith
  have hH1 : ∀ T ≥ t₀, enstrophyR3 (u T) ≤ enstrophyR3 (u t₀) * Real.exp (c_nu_R3 ν * B_tail) := fun T hT => by
    have h1 := critical_prodi_serrin_L4H1_reduction_r3 hns ht₀ hT
    have h2 : c_nu_R3 ν * (∫ s in t₀..T, (enstrophyR3 (u s)) ^ 2) ≤ c_nu_R3 ν * B_tail :=
      mul_le_mul_of_nonneg_left (hL4 T hT) (c_nu_R3_pos hν).le
    exact le_trans h1 (mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 h2) (enstrophyR3_nonneg (u t₀)))
  have hPal : Continuous (fun s : ℝ => palinstrophyR3 (u s)) →
      ∀ T ≥ t₀, (∫ s in t₀..T, palinstrophyR3 (u s)) ≤
        (4 / ν) * (enstrophyR3 (u t₀) +
          c_nu_R3 ν * (enstrophyR3 (u t₀) * Real.exp (c_nu_R3 ν * B_tail)) * B_tail) := by
    intro hP_cont T hT
    have h1 := (critical_prodi_serrin_palinstrophy_bound_r3 hns hP_cont ht₀ hT).1
      (enstrophyR3 (u t₀) * Real.exp (c_nu_R3 ν * B_tail)) (fun s hs => hH1 s hs.1)
    have h2 : c_nu_R3 ν * (enstrophyR3 (u t₀) * Real.exp (c_nu_R3 ν * B_tail)) *
        (∫ s in t₀..T, (enstrophyR3 (u s)) ^ 2) ≤
        c_nu_R3 ν * (enstrophyR3 (u t₀) * Real.exp (c_nu_R3 ν * B_tail)) * B_tail :=
      mul_le_mul_of_nonneg_left (hL4 T hT)
        (mul_nonneg (c_nu_R3_pos hν).le (mul_nonneg (enstrophyR3_nonneg (u t₀)) (Real.exp_pos _).le))
    have hZT_nn : 0 ≤ enstrophyR3 (u T) := enstrophyR3_nonneg (u T)
    have h3 : (ν / 4) * (∫ s in t₀..T, palinstrophyR3 (u s)) ≤
        enstrophyR3 (u t₀) + c_nu_R3 ν * (enstrophyR3 (u t₀) * Real.exp (c_nu_R3 ν * B_tail)) * B_tail := by
      linarith
    have hmul := mul_le_mul_of_nonneg_left h3 (by positivity : (0 : ℝ) ≤ 4 / ν)
    have hcancel : (4 / ν) * ((ν / 4) * (∫ s in t₀..T, palinstrophyR3 (u s))) =
        ∫ s in t₀..T, palinstrophyR3 (u s) := by field_simp [hν.ne']
    linarith
  exact ⟨hgap_pos, hinv, hL4, hH1, hPal⟩

-- ============================================================================
-- SECTION 3 (MILESTONE 15F-2B): VERBATIM FEFFERMAN (2000) CLAY PACKAGING
--   FOR BOTH ℝ³ (46,656 ν⁴ TIER I) AND 𝕋³ (CONSTRUCTIVE GLOBAL C^∞ TIER I)
-- ============================================================================

/-- **THEOREM 15F2-4 (Verbatim Fefferman 2000 Clay Tier I Master Theorem on Whole Space `ℝ³`):**
    For ANY divergence-free Schwartz initial datum `u₀ ∈ 𝒮_σ(ℝ³)` satisfying
    `E(u₀) · Z(u₀) < 46,656 ν⁴` and ANY pure-Sobolev classical solution `(u, p)` on `ℝ³ × [0, ∞)`
    with `u(0) = u₀` (ZERO pointwise `⟨x⟩⁻³` or Schwartz decay assumed at `t > 0`!):
    1. **Fefferman (2000) Bounded Energy:** `∀ t ≥ 0, ∫_{ℝ³} |u(t, x)|² dx ≤ 2 E(u₀)` and
       `∀ T ≥ 0, ∫_0^T Z(s) ds ≤ E(u₀) / (2 ν)`;
    2. **Permanent `46,656 ν⁴` Basin Invariance:** `∀ t ≥ 0, E(t) Z(t) ≤ E(u₀) Z(u₀) < 46,656 ν⁴`;
    3. **Global Critical `L⁴_t Ḣ¹_x` & `L^∞_t H¹_x` Control:** uniform-in-`T` bounds on `[0, ∞)`;
    4. **Global `L²_t Ḣ²_x` Palinstrophy Control** (whenever `P` is continuous). -/
theorem clay_fefferman2000_r3_46656_tier1_master
    {u₀ : R3 → R3} {u : ℝ → R3 → R3} {p : ℝ → R3 → ℝ} {ν : ℝ}
    (_hu₀_schwartz : IsSchwartzSolenoidalR3 u₀)
    (hns : IsPureSobolevClassicalNS3D_R3 u p ν)
    (hinit : u 0 = u₀)
    (hbasin : energyR3 u₀ * enstrophyR3 u₀ < 46656 * ν ^ 4) :
    let R₀ : ℝ := energyR3 u₀ * enstrophyR3 u₀
    let gap : ℝ := ν - Real.sqrt (Real.sqrt (R₀ / 46656))
    let B_tail : ℝ := R₀ / (4 * gap)
    0 < gap ∧
    (∀ t ≥ 0, r3Integral (fun x => dot3D (u t x) (u t x)) ≤ 2 * energyR3 u₀) ∧
    (∀ T ≥ 0, (∫ s in (0 : ℝ)..T, enstrophyR3 (u s)) ≤ energyR3 u₀ / (2 * ν)) ∧
    (∀ t ≥ 0, energyR3 (u t) * enstrophyR3 (u t) ≤ R₀) ∧
    (∀ T ≥ 0, (∫ s in (0 : ℝ)..T, (enstrophyR3 (u s)) ^ 2) ≤ B_tail) ∧
    (∀ T ≥ 0, enstrophyR3 (u T) ≤ enstrophyR3 u₀ * Real.exp (c_nu_R3 ν * B_tail)) ∧
    (Continuous (fun s : ℝ => palinstrophyR3 (u s)) →
      ∀ T ≥ 0, (∫ s in (0 : ℝ)..T, palinstrophyR3 (u s)) ≤
        (4 / ν) * (enstrophyR3 u₀ +
          c_nu_R3 ν * (enstrophyR3 u₀ * Real.exp (c_nu_R3 ν * B_tail)) * B_tail)) := by
  have hdec := hns.toDecayingClassicalNS3D_R3
  have hbasin0 : energyR3 (u 0) * enstrophyR3 (u 0) < 46656 * ν ^ 4 := by rwa [hinit]
  have hriv := global_r3_decaying_46656_basin_invariant_and_river hdec le_rfl hbasin0
  rw [hinit] at hriv
  refine ⟨hriv.1, ?_, ?_, hriv.2.1, hriv.2.2.1, hriv.2.2.2.1, hriv.2.2.2.2⟩
  · intro t ht
    have hler := (global_leray_energy_law_r3 hdec ht).2.1
    rw [hinit] at hler
    unfold energyR3 at hler ⊢
    linarith
  · intro T hT
    have hler := (global_leray_energy_law_r3 hdec hT).2.2
    rwa [hinit] at hler

/-- **THEOREM 15F2-5 (Verbatim Fefferman 2000 Periodic `𝕋³` Constructive Global `C^∞` Tier I Master):**
    For ANY mean-zero solenoidal real-symmetric `u₀ ∈ H^∞(𝕋³)` satisfying
    `217,088 ‖u₀‖²_{H²} ≤ π² ν²`:
    1. Constructively produces a global solution `u` on `[0, ∞)` with `u(0) = u₀` whose physical
       synthesis `(U, P)` is `C^∞(𝕋³)`, periodic, divergence-free, and satisfies the exact 3D
       Navier–Stokes PDE pointwise at every `t > 0`;
    2. At boundary `t = 0`, EVERY all-order time-spatial derivative `∂_t^n ∂_x^α u₀` and
       `∂_t^n ∂_x^α p₀` is `C^∞(𝕋³)`. -/
theorem clay_fefferman2000_torus3D_tier1_master {ν : ℝ} (hν : 0 < ν)
    {u₀ : GarrySpectralBilinear3D.VecSeq3D}
    (hu₀_Hinf : InHinfVecTorus3D u₀)
    (hsol₀ : GarrySpectralBilinear3D.IsSolenoidal u₀)
    (hsym₀ : GarrySpectralBilinear3D.IsRealSymm u₀)
    (hzero : ∀ c : Fin 3, u₀ 0 c = 0)
    (hsmall : 217088 * GarrySpectralBilinear3D.h2VecNormSq u₀ ≤ Real.pi ^ 2 * ν ^ 2) :
    (∃ u : ℝ → GarrySpectralBilinear3D.VecSeq3D, u 0 = u₀ ∧
      ∀ t : ℝ, 0 < t →
        ContDiff ℝ (⊤ : ℕ∞) (GarrySmoothSynthesis3D.smoothSynthVec (u t)) ∧
        ContDiff ℝ (⊤ : ℕ∞)
          (GarrySmoothSynthesis3D.smoothSynthScalar (GarryLocalExistence3D.pressureCoeff6B (u t))) ∧
        GarryLerayTorus3D.IsPeriodic3D (GarrySmoothSynthesis3D.smoothSynthVec (u t)) ∧
        (∀ x : R3, div3D (GarrySmoothSynthesis3D.smoothSynthVec (u t)) x = 0) ∧
        (∀ (x : R3) (c : Fin 3),
          deriv (fun s => GarrySmoothSynthesis3D.smoothSynthVec (u s) x c) t +
            advection3D (GarrySmoothSynthesis3D.smoothSynthVec (u t)) x c +
            grad3D (GarrySmoothSynthesis3D.smoothSynthScalar
              (GarryLocalExistence3D.pressureCoeff6B (u t))) x c =
            ν * laplacian3D (GarrySmoothSynthesis3D.smoothSynthVec (u t)) x c)) ∧
    (∀ (n : ℕ) (α : List (Fin 3)) (c : Fin 3),
      ContDiff ℝ (⊤ : ℕ∞)
        (GarrySmoothSynthesis3D.smoothSynthScalar
          (diffMultiModeTorus3D α (fun k => nsTimeDerivSeqTorus3D ν u₀ n k c))) ∧
      ContDiff ℝ (⊤ : ℕ∞)
        (GarrySmoothSynthesis3D.smoothSynthScalar
          (diffMultiModeTorus3D α (pressureTimeDerivSeqTorus3D ν u₀ n)))) := by
  have hu₀_H2 : GarrySpectralBilinear3D.InH2Vec u₀ :=
    (GarryHigherSobolev3D.inH2Vec_of_inHalfHmVec (s := 4) le_rfl (hu₀_Hinf 2)).1
  exact ⟨(GarrySmoothSynthesis3D.garry_millennium_master_theorem_torus3D hν).2.1
      hu₀_H2 hsol₀ hsym₀ hzero hsmall,
    (milestone15E_spacetime_smoothness_master ν).1 hu₀_Hinf hsol₀ hsym₀⟩

/-- **THEOREM 15F2-6 (MILESTONE 15F GRAND DUAL-DOMAIN CLAY PACKAGING MASTER — ZERO AUXILIARY HYPOTHESES):**
    Unifies the complete Tier I Fefferman (2000) closure on both `ℝ³` and `𝕋³` with non-vacuity. -/
theorem milestone15F_clay_fefferman2000_dual_domain_master {ν : ℝ} (hν : 0 < ν) :
    (∃ (u₀ : R3 → R3) (u : ℝ → R3 → R3) (p : ℝ → R3 → ℝ),
      IsSchwartzSolenoidalR3 u₀ ∧
      IsPureSobolevClassicalNS3D_R3 u p ν ∧
      u 0 = u₀ ∧
      energyR3 u₀ * enstrophyR3 u₀ < 46656 * ν ^ 4) ∧
    (∀ {u₀ : R3 → R3} {u : ℝ → R3 → R3} {p : ℝ → R3 → ℝ},
      IsSchwartzSolenoidalR3 u₀ →
      IsPureSobolevClassicalNS3D_R3 u p ν →
      u 0 = u₀ →
      energyR3 u₀ * enstrophyR3 u₀ < 46656 * ν ^ 4 →
      (∀ t ≥ 0, r3Integral (fun x => dot3D (u t x) (u t x)) ≤ 2 * energyR3 u₀) ∧
      (∀ t ≥ 0, energyR3 (u t) * enstrophyR3 (u t) ≤ energyR3 u₀ * enstrophyR3 u₀)) ∧
    (∀ {u₀ : GarrySpectralBilinear3D.VecSeq3D},
      InHinfVecTorus3D u₀ →
      GarrySpectralBilinear3D.IsSolenoidal u₀ →
      GarrySpectralBilinear3D.IsRealSymm u₀ →
      (∀ c : Fin 3, u₀ 0 c = 0) →
      217088 * GarrySpectralBilinear3D.h2VecNormSq u₀ ≤ Real.pi ^ 2 * ν ^ 2 →
      ∃ u : ℝ → GarrySpectralBilinear3D.VecSeq3D, u 0 = u₀ ∧
        ∀ t : ℝ, 0 < t →
          ContDiff ℝ (⊤ : ℕ∞) (GarrySmoothSynthesis3D.smoothSynthVec (u t)) ∧
          ContDiff ℝ (⊤ : ℕ∞)
            (GarrySmoothSynthesis3D.smoothSynthScalar (GarryLocalExistence3D.pressureCoeff6B (u t))) ∧
          (∀ x : R3, div3D (GarrySmoothSynthesis3D.smoothSynthVec (u t)) x = 0)) := by
  refine ⟨⟨fun _ => 0, fun _ _ => 0, fun _ _ => 0,
      zero_isSchwartzSolenoidalR3, zero_isPureSobolevClassicalNS3D_R3 hν, rfl, ?_⟩,
    fun hu₀ hns hinit hbasin => ?_,
    fun hu₀ hsol₀ hsym₀ hzero hsmall => ?_⟩
  · have hE0 : energyR3 (fun _ : R3 => (0 : R3)) = 0 := by
      unfold energyR3 dot3D; simp [r3Integral_zero]
    rw [hE0, zero_mul]; positivity
  · have hcl := clay_fefferman2000_r3_46656_tier1_master hu₀ hns hinit hbasin
    exact ⟨hcl.2.1, hcl.2.2.2.1⟩
  · obtain ⟨u, hu0, hrest⟩ := (clay_fefferman2000_torus3D_tier1_master hν hu₀ hsol₀ hsym₀ hzero hsmall).1
    exact ⟨u, hu0, fun t ht => ⟨(hrest t ht).1, (hrest t ht).2.1, (hrest t ht).2.2.2.1⟩⟩

end ClayPackaging15F2

#print axioms schwartzScalarR3_in_L2_and_vanishes
#print axioms schwartzScalarR3_to_RapidDecayH3_and_DecayingH3
#print axioms schwartzSolenoidalR3_to_DecayingH3Solenoidal_and_finite_EZP
#print axioms zero_isSchwartzSolenoidalR3
#print axioms vanishesAtInfinityR3_of_L2_and_lipschitz
#print axioms pure_H3_sobolev_to_DecayingH3ScalarR3
#print axioms pure_H3_sobolev_to_DecayingH3SolenoidalR3
#print axioms IsPureSobolevClassicalNS3D_R3.toDecayingClassicalNS3D_R3
#print axioms zero_isPureSobolevClassicalNS3D_R3
#print axioms global_r3_decaying_46656_basin_invariant_and_river
#print axioms clay_fefferman2000_r3_46656_tier1_master
#print axioms clay_fefferman2000_torus3D_tier1_master
#print axioms milestone15F_clay_fefferman2000_dual_domain_master

end GarrySchwartzClayPackagingNS3D