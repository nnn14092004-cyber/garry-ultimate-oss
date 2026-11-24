import EnstrophyBasinTorus3D
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

/-!
# Milestone 9A2 (Tier I — 100% Unconditional): Critical Prodi-Serrin L⁴_t Ḣ¹_x Reduction,
  Local Safe Horizon & Waterfall-to-River Global Closure Audit on 𝕋³

Building directly on Milestone 9A1 (`EnstrophyBasinTorus3D.lean`), this module proves
unconditionally (`0 sorryAx`, `0` custom axioms) for periodic mean-zero 3D Navier-Stokes
classical solutions on `𝕋³ = (ℝ/ℤ)³`:

1. **Theorem 9A2-1 (Critical Prodi-Serrin Reduction `Z³ → γ(t) Z`):**
   Sharp exponential enstrophy control via the scale-invariant `L⁴_t Ḣ¹_x` integral
   `∫_{t₀}^T Z(s)² ds`, including the viscous damping term `-2π² ν (T - t₀)` and uniform
   envelope on `[t₀, T]`.
2. **Theorem 9A2-2 (Palinstrophy Integral Control via Critical `L⁴_t Ḣ¹_x` Norm):**
   Unconditional bound on `Z(T) + (ν/4) ∫_{t₀}^T P(s) ds` controlled solely by `Z(t₀)` and
   `∫_{t₀}^T Z(s)² ds`.
3. **Theorem 9A2-3 (Local Safe Horizon — "Never Lose Sight of the Leaf"):**
   Division-free proof (valid for all `Z(t₀) ≥ 0`) of the explicit blow-up barrier
   `Z(t)² ≤ Z(t₀)² / (1 - 2 c_ν Z(t₀)² (t - t₀))` for `t - t₀ < T_local_H1 Z(t₀) ν`, plus the
   certified half-step Garry enclosure (`Z(t) ≤ √2 Z(t₀)` and `c_ν ∫ Z² ≤ 1/2`) for Milestone 9B.
4. **Theorem 9A2-4 (Unified Milestone 9A1 + 9A2 Master & Honest Open-Gap Reduction):**
   Beyond `T_trap_H1 E₀ ν`, the post-trap river `[t*, ∞)` satisfies the unconditional uniform
   tail bound `∫_{t*}^T Z(s)² ds ≤ Z(t*)² / (3π² ν) < 4π⁴ ν³ / 507`. Consequently, all
   global-in-time `L∞_t H¹_x`, `L⁴_t Ḣ¹_x`, and `L²_t Ḣ²_x` norms on `[0, ∞)` reduce
   completely to bounding the single finite waterfall budget `∫_0^{t*} Z(s)² ds` on `[0, T_trap]`.
-/

namespace GarryCriticalProdiSerrin3D

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

-- ============================================================================
-- SECTION 0: EXPLICIT CONSTANTS & CALCULUS HELPERS
-- ============================================================================

/-- Explicit unconditional cubic vortex-stretching coefficient from Milestone 9A1:
    `c_nu_H1 ν = 169 / (8 π⁴ ν³)`. -/
noncomputable def c_nu_H1 (ν : ℝ) : ℝ :=
  169 / (8 * Real.pi ^ 4 * ν ^ 3)

/-- Explicit local safe time horizon ("leaf-tracking barrier") for initial enstrophy `Z₀`
    and viscosity `ν`:
    `T_local_H1 Z₀ ν = 4 π⁴ ν³ / (169 Z₀²) = 1 / (2 c_nu_H1 ν Z₀²)`. -/
noncomputable def T_local_H1 (Z₀ ν : ℝ) : ℝ :=
  4 * Real.pi ^ 4 * ν ^ 3 / (169 * Z₀ ^ 2)

lemma c_nu_H1_pos {ν : ℝ} (hν : 0 < ν) : 0 < c_nu_H1 ν := by
  unfold c_nu_H1; positivity

lemma T_local_H1_pos {Z₀ ν : ℝ} (hZ₀ : 0 < Z₀) (hν : 0 < ν) : 0 < T_local_H1 Z₀ ν := by
  unfold T_local_H1; positivity

lemma two_mul_c_nu_mul_sq_mul_T_local {Z₀ ν : ℝ} (hZ₀ : Z₀ ≠ 0) (hν : ν ≠ 0) :
    2 * c_nu_H1 ν * Z₀ ^ 2 * T_local_H1 Z₀ ν = 1 := by
  unfold c_nu_H1 T_local_H1
  have hpi : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
  field_simp
  ring

lemma T_local_H1_eq_inv {Z₀ ν : ℝ} (hZ₀ : Z₀ ≠ 0) (hν : ν ≠ 0) :
    T_local_H1 Z₀ ν = 1 / (2 * c_nu_H1 ν * Z₀ ^ 2) := by
  unfold c_nu_H1 T_local_H1
  have hpi : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
  field_simp
  ring

private lemma antitone_of_hasDerivAt_nonpos {f f' : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
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

private lemma enstrophy_nonneg_9a2 {u : ℝ → R3 → R3} {p : ℝ → R3 → ℝ} {ν : ℝ}
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

private lemma palinstrophy_nonneg_9a2 {u : ℝ → R3 → R3} {p : ℝ → R3 → ℝ} {ν : ℝ}
    (hns : IsPeriodicClassicalNS3D_C3 u p ν) {t : ℝ} (ht : 0 ≤ t) :
    0 ≤ palinstrophy3D (u t) := by
  have hZ := enstrophy_nonneg_9a2 hns ht
  have hwirt := (sharp_analytical_lemma4_bernstein_poincare_vorticity hns ht).1
  nlinarith [Real.pi_pos]

private lemma deriv_enstrophy_le_cubic {u : ℝ → R3 → R3} {p : ℝ → R3 → ℝ} {ν : ℝ}
    (hns : IsPeriodicClassicalNS3D_C3 u p ν)
    (hmean : ∀ s ≥ 0, ∀ c : Fin 3, torusIntegral (fun x => u s x c) = 0)
    {t : ℝ} (ht : 0 ≤ t) :
    deriv (enstrophy u) t ≤ c_nu_H1 ν * (enstrophy u t) ^ 3 := by
  have hode := (unconditional_enstrophy_ode_torus3D hns hmean ht).1
  have hP := palinstrophy_nonneg_9a2 hns ht
  have hν : 0 < ν := hns.h_nu_pos
  unfold c_nu_H1
  nlinarith

private lemma enstrophy_ext_continuous {u : ℝ → R3 → R3} {p : ℝ → R3 → ℝ} {ν : ℝ}
    (hns : IsPeriodicClassicalNS3D_C3 u p ν) :
    Continuous (fun s : ℝ => enstrophy u (max s 0)) := by
  rw [continuous_iff_continuousAt]
  intro s
  have h1 : ContinuousAt (enstrophy u) (max s (0 : ℝ)) :=
    (hasDerivAt_enstrophy_evolution_3D hns (le_max_right s 0)).1.continuousAt
  have h2 : ContinuousAt (fun r : ℝ => max r (0 : ℝ)) s :=
    (Continuous.max continuous_id continuous_const).continuousAt
  exact ContinuousAt.comp (f := fun r : ℝ => max r (0 : ℝ)) (g := enstrophy u) h1 h2

private lemma integral_enstrophy_sq_ext_eq {u : ℝ → R3 → R3} {a b : ℝ}
    (ha : 0 ≤ a) (hab : a ≤ b) :
    (∫ s in a..b, (enstrophy u (max s 0)) ^ 2) = ∫ s in a..b, (enstrophy u s) ^ 2 := by
  apply intervalIntegral.integral_congr
  intro s hs
  rw [Set.uIcc_of_le hab] at hs
  simp only [max_eq_left (le_trans ha hs.1)]

private lemma hasDerivAt_integral_enstrophy_sq_ext {u : ℝ → R3 → R3} {p : ℝ → R3 → ℝ} {ν : ℝ}
    (hns : IsPeriodicClassicalNS3D_C3 u p ν) (t₀ : ℝ) {r : ℝ} (hr : 0 ≤ r) :
    HasDerivAt (fun q : ℝ => ∫ s in t₀..q, (enstrophy u (max s 0)) ^ 2)
      ((enstrophy u r) ^ 2) r := by
  have hc : Continuous (fun s : ℝ => (enstrophy u (max s 0)) ^ 2) :=
    (enstrophy_ext_continuous hns).pow 2
  have h := intervalIntegral.integral_hasDerivAt_right
    (hc.intervalIntegrable t₀ r)
    (hc.stronglyMeasurableAtFilter volume (nhds r))
    hc.continuousAt
  simpa [max_eq_left hr] using h

private lemma integral_enstrophy_sq_mono {u : ℝ → R3 → R3} {p : ℝ → R3 → ℝ} {ν : ℝ}
    (hns : IsPeriodicClassicalNS3D_C3 u p ν) {a b c : ℝ}
    (ha : 0 ≤ a) (hab : a ≤ b) (hbc : b ≤ c) :
    (∫ s in a..b, (enstrophy u s) ^ 2) ≤ ∫ s in a..c, (enstrophy u s) ^ 2 := by
  have hc : Continuous (fun s : ℝ => (enstrophy u (max s 0)) ^ 2) :=
    (enstrophy_ext_continuous hns).pow 2
  rw [← integral_enstrophy_sq_ext_eq ha hab, ← integral_enstrophy_sq_ext_eq ha (le_trans hab hbc)]
  have hadd := intervalIntegral.integral_add_adjacent_intervals
    (hc.intervalIntegrable (μ := volume) a b) (hc.intervalIntegrable (μ := volume) b c)
  have hnn : 0 ≤ ∫ s in b..c, (enstrophy u (max s 0)) ^ 2 :=
    intervalIntegral.integral_nonneg hbc (fun _ _ => sq_nonneg _)
  linarith

-- ============================================================================
-- SECTION 1: THEOREM 9A2-1 — CRITICAL PRODI-SERRIN REDUCTION (Z³ → γ(t) Z)
-- ============================================================================

/-- **THEOREM 9A2-1 (Unconditional Critical Prodi-Serrin `L⁴_t Ḣ¹_x` Enstrophy Reduction):**
    Lowers the cubic supercritical enstrophy nonlinearity `c_ν Z³` to a linear exponential
    factor governed strictly by the scale-invariant Prodi-Serrin integral `∫_{t₀}^T Z(s)² ds`:
1. Sharp damped form:
       `Z(T) ≤ Z(t₀) * exp(c_nu_H1 ν * ∫_{t₀}^T Z(s)² ds - 2π² ν (T - t₀))`,
2. Pure Prodi-Serrin form:
       `Z(T) ≤ Z(t₀) * exp(c_nu_H1 ν * ∫_{t₀}^T Z(s)² ds)`,
3. Uniform envelope on `[t₀, T]`:
       `∀ s ∈ [t₀, T], Z(s) ≤ Z(t₀) * exp(c_nu_H1 ν * ∫_{t₀}^T Z(r)² dr)`. -/
theorem critical_prodi_serrin_enstrophy_reduction_torus3D
    {u : ℝ → R3 → R3} {p : ℝ → R3 → ℝ} {ν : ℝ}
    (hns : IsPeriodicClassicalNS3D_C3 u p ν)
    (hmean : ∀ s ≥ 0, ∀ c : Fin 3, torusIntegral (fun x => u s x c) = 0)
    {t₀ T : ℝ} (ht₀ : 0 ≤ t₀) (hT : t₀ ≤ T) :
    enstrophy u T ≤
      enstrophy u t₀ *
        Real.exp (c_nu_H1 ν * (∫ s in t₀..T, (enstrophy u s) ^ 2) -
          2 * Real.pi ^ 2 * ν * (T - t₀)) ∧
    enstrophy u T ≤
      enstrophy u t₀ *
        Real.exp (c_nu_H1 ν * (∫ s in t₀..T, (enstrophy u s) ^ 2)) ∧
    (∀ s ∈ Set.Icc t₀ T,
      enstrophy u s ≤
        enstrophy u t₀ *
          Real.exp (c_nu_H1 ν * (∫ r in t₀..T, (enstrophy u r) ^ 2))) := by
  have hν : 0 < ν := hns.h_nu_pos
  have hZ0_nn : 0 ≤ enstrophy u t₀ := enstrophy_nonneg_9a2 hns ht₀
  have hsharp : ∀ t ≥ t₀,
      enstrophy u t ≤
        enstrophy u t₀ *
          Real.exp (c_nu_H1 ν * (∫ s in t₀..t, (enstrophy u s) ^ 2) -
            2 * Real.pi ^ 2 * ν * (t - t₀)) := by
    intro t ht
    let Φ : ℝ → ℝ := fun r =>
      c_nu_H1 ν * (∫ s in t₀..r, (enstrophy u (max s 0)) ^ 2) -
        2 * Real.pi ^ 2 * ν * (r - t₀)
    let Φ' : ℝ → ℝ := fun r => c_nu_H1 ν * (enstrophy u r) ^ 2 - 2 * Real.pi ^ 2 * ν
    let g : ℝ → ℝ := fun r => Real.exp (-Φ r) * enstrophy u r
    let g' : ℝ → ℝ := fun r => Real.exp (-Φ r) * (deriv (enstrophy u) r - Φ' r * enstrophy u r)
    have hg_deriv : ∀ r ≥ t₀, HasDerivAt g (g' r) r := fun r hr => by
      have hI := (hasDerivAt_integral_enstrophy_sq_ext hns t₀ (le_trans ht₀ hr)).const_mul (c_nu_H1 ν)
      have hlin : HasDerivAt (fun q : ℝ => 2 * Real.pi ^ 2 * ν * (q - t₀))
          (2 * Real.pi ^ 2 * ν) r := by
        simpa [mul_one] using ((hasDerivAt_id r).sub_const t₀).const_mul (2 * Real.pi ^ 2 * ν)
      have hΦ : HasDerivAt Φ (Φ' r) r := hI.sub hlin
      have he : HasDerivAt (fun q => Real.exp (-Φ q)) (Real.exp (-Φ r) * (-Φ' r)) r :=
        hΦ.neg.exp
      have hZ : HasDerivAt (enstrophy u) (deriv (enstrophy u) r) r := by
        have hd := hasDerivAt_enstrophy_evolution_3D hns (le_trans ht₀ hr)
        rw [hd.2]; exact hd.1
      have hprod := he.mul hZ
      convert hprod using 1
      dsimp only [g']; ring
    have hg_cont : ContinuousOn g (Set.Icc t₀ t) :=
      fun r hr => (hg_deriv r hr.1).continuousAt.continuousWithinAt
    have hg_nonpos : ∀ r ∈ Set.Ioo t₀ t, g' r ≤ 0 := fun r hr => by
      have hode := (unconditional_enstrophy_ode_torus3D hns hmean (le_trans ht₀ (le_of_lt hr.1))).2.1
      have hdiff : deriv (enstrophy u) r - Φ' r * enstrophy u r ≤ 0 := by
        dsimp only [Φ', c_nu_H1]; linarith
      exact mul_nonpos_of_nonneg_of_nonpos (le_of_lt (Real.exp_pos _)) hdiff
    have hgt_le : g t ≤ g t₀ :=
      antitone_of_hasDerivAt_nonpos ht hg_cont (fun r hr => hg_deriv r (le_of_lt hr.1)) hg_nonpos
    have hg0 : g t₀ = enstrophy u t₀ := by
      dsimp only [g, Φ]
      simp
    rw [hg0] at hgt_le
    dsimp only [g] at hgt_le
    have hmul := mul_le_mul_of_nonneg_right hgt_le (le_of_lt (Real.exp_pos (Φ t)))
    have hcancel : Real.exp (-Φ t) * enstrophy u t * Real.exp (Φ t) = enstrophy u t := by
      calc Real.exp (-Φ t) * enstrophy u t * Real.exp (Φ t)
          = enstrophy u t * (Real.exp (-Φ t) * Real.exp (Φ t)) := by ring
        _ = enstrophy u t * Real.exp (-Φ t + Φ t) := by rw [← Real.exp_add]
        _ = enstrophy u t := by simp
    rw [hcancel] at hmul
    have hΦ_eq : Φ t = c_nu_H1 ν * (∫ s in t₀..t, (enstrophy u s) ^ 2) -
        2 * Real.pi ^ 2 * ν * (t - t₀) := by
      dsimp only [Φ]
      rw [integral_enstrophy_sq_ext_eq ht₀ ht]
    rw [hΦ_eq] at hmul
    exact hmul
  have h1 := hsharp T hT
  have hpure : ∀ t ≥ t₀,
      enstrophy u t ≤
        enstrophy u t₀ * Real.exp (c_nu_H1 ν * (∫ s in t₀..t, (enstrophy u s) ^ 2)) := by
    intro t ht
    have hsub : c_nu_H1 ν * (∫ s in t₀..t, (enstrophy u s) ^ 2) - 2 * Real.pi ^ 2 * ν * (t - t₀) ≤
        c_nu_H1 ν * (∫ s in t₀..t, (enstrophy u s) ^ 2) := by
      have hdamp : 0 ≤ 2 * Real.pi ^ 2 * ν * (t - t₀) := by
        have : 0 ≤ t - t₀ := by linarith
        positivity
      linarith
    exact le_trans (hsharp t ht) (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hsub) hZ0_nn)
  have h2 := hpure T hT
  have h3 : ∀ s ∈ Set.Icc t₀ T,
      enstrophy u s ≤
        enstrophy u t₀ * Real.exp (c_nu_H1 ν * (∫ r in t₀..T, (enstrophy u r) ^ 2)) := by
    intro s hs
    have hmono := integral_enstrophy_sq_mono hns ht₀ hs.1 hs.2
    have hexp : Real.exp (c_nu_H1 ν * (∫ r in t₀..s, (enstrophy u r) ^ 2)) ≤
        Real.exp (c_nu_H1 ν * (∫ r in t₀..T, (enstrophy u r) ^ 2)) :=
      Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hmono (le_of_lt (c_nu_H1_pos hν)))
    exact le_trans (hpure s hs.1) (mul_le_mul_of_nonneg_left hexp hZ0_nn)
  exact ⟨h1, h2, h3⟩

-- ============================================================================
-- SECTION 2: THEOREM 9A2-2 — PALINSTROPHY INTEGRAL CONTROL VIA L⁴_t Ḣ¹_x
-- ============================================================================

/-- **THEOREM 9A2-2 (Unconditional Palinstrophy Integral Control via Critical `L⁴_t Ḣ¹_x` Norm):**
    Combines the Milestone 9A1 differential inequality `dZ/dt ≤ -(ν/4) P + c_ν Z³` with
    Theorem 9A2-1 on `[t₀, T]`:
1. For ANY uniform enstrophy cap `M` on `[t₀, T]`:
       `Z(T) + (ν/4) ∫_{t₀}^T P(s) ds ≤ Z(t₀) + c_nu_H1 ν * M * ∫_{t₀}^T Z(s)² ds`.
2. Self-contained critical Prodi-Serrin palinstrophy bound (no extra `M` hypothesis):
       `Z(T) + (ν/4) ∫_{t₀}^T P(s) ds ≤ Z(t₀) + c_nu_H1 ν * (Z(t₀) * exp(c_nu_H1 ν * I)) * I`,
       where `I = ∫_{t₀}^T Z(s)² ds`. -/
theorem critical_prodi_serrin_palinstrophy_bound_torus3D
    {u : ℝ → R3 → R3} {p : ℝ → R3 → ℝ} {ν : ℝ}
    (hns : IsPeriodicClassicalNS3D_C3 u p ν)
    (hmean : ∀ s ≥ 0, ∀ c : Fin 3, torusIntegral (fun x => u s x c) = 0)
    (hP_cont : Continuous (fun s : ℝ => palinstrophy3D (u s)))
    {t₀ T : ℝ} (ht₀ : 0 ≤ t₀) (hT : t₀ ≤ T) :
    (∀ M : ℝ, (∀ s ∈ Set.Icc t₀ T, enstrophy u s ≤ M) →
      enstrophy u T + (ν / 4) * (∫ s in t₀..T, palinstrophy3D (u s)) ≤
        enstrophy u t₀ + c_nu_H1 ν * M * (∫ s in t₀..T, (enstrophy u s) ^ 2)) ∧
    (let I : ℝ := ∫ s in t₀..T, (enstrophy u s) ^ 2
     enstrophy u T + (ν / 4) * (∫ s in t₀..T, palinstrophy3D (u s)) ≤
       enstrophy u t₀ +
         c_nu_H1 ν * (enstrophy u t₀ * Real.exp (c_nu_H1 ν * I)) * I) := by
  have hν : 0 < ν := hns.h_nu_pos
  have hgen : ∀ M : ℝ, (∀ s ∈ Set.Icc t₀ T, enstrophy u s ≤ M) →
      enstrophy u T + (ν / 4) * (∫ s in t₀..T, palinstrophy3D (u s)) ≤
        enstrophy u t₀ + c_nu_H1 ν * M * (∫ s in t₀..T, (enstrophy u s) ^ 2) := by
    intro M hM
    let h : ℝ → ℝ := fun r =>
      enstrophy u r + (ν / 4) * (∫ s in t₀..r, palinstrophy3D (u s)) -
        c_nu_H1 ν * M * (∫ s in t₀..r, (enstrophy u (max s 0)) ^ 2)
    let h' : ℝ → ℝ := fun r =>
      deriv (enstrophy u) r + (ν / 4) * palinstrophy3D (u r) -
        c_nu_H1 ν * M * (enstrophy u r) ^ 2
    have hh_deriv : ∀ r ≥ t₀, HasDerivAt h (h' r) r := fun r hr => by
      have hZ : HasDerivAt (enstrophy u) (deriv (enstrophy u) r) r := by
        have hd := hasDerivAt_enstrophy_evolution_3D hns (le_trans ht₀ hr)
        rw [hd.2]; exact hd.1
      have hIP : HasDerivAt (fun q => ∫ s in t₀..q, palinstrophy3D (u s))
          (palinstrophy3D (u r)) r :=
        intervalIntegral.integral_hasDerivAt_right
          (hP_cont.intervalIntegrable t₀ r)
          (hP_cont.stronglyMeasurableAtFilter volume (nhds r))
          hP_cont.continuousAt
      have hIZ := hasDerivAt_integral_enstrophy_sq_ext hns t₀ (le_trans ht₀ hr)
      exact (hZ.add (hIP.const_mul (ν / 4))).sub (hIZ.const_mul (c_nu_H1 ν * M))
    have hh_cont : ContinuousOn h (Set.Icc t₀ T) :=
      fun r hr => (hh_deriv r hr.1).continuousAt.continuousWithinAt
    have hh_nonpos : ∀ r ∈ Set.Ioo t₀ T, h' r ≤ 0 := fun r hr => by
      have hode := (unconditional_enstrophy_ode_torus3D hns hmean (le_trans ht₀ (le_of_lt hr.1))).1
      have hZ_le_M : enstrophy u r ≤ M := hM r ⟨le_of_lt hr.1, le_of_lt hr.2⟩
      have hfac_nn : 0 ≤ c_nu_H1 ν * (enstrophy u r) ^ 2 :=
        mul_nonneg (le_of_lt (c_nu_H1_pos hν)) (sq_nonneg _)
      have hcub : c_nu_H1 ν * (enstrophy u r) ^ 3 ≤ c_nu_H1 ν * M * (enstrophy u r) ^ 2 := by
        have := mul_le_mul_of_nonneg_left hZ_le_M hfac_nn
        linarith
      dsimp only [h', c_nu_H1] at hcub ⊢
      linarith
    have hhT_le : h T ≤ h t₀ :=
      antitone_of_hasDerivAt_nonpos hT hh_cont (fun r hr => hh_deriv r (le_of_lt hr.1)) hh_nonpos
    have hh0 : h t₀ = enstrophy u t₀ := by dsimp only [h]; simp
    rw [hh0] at hhT_le
    dsimp only [h] at hhT_le
    rw [integral_enstrophy_sq_ext_eq ht₀ hT] at hhT_le
    linarith
  have hself :
      let I : ℝ := ∫ s in t₀..T, (enstrophy u s) ^ 2
      enstrophy u T + (ν / 4) * (∫ s in t₀..T, palinstrophy3D (u s)) ≤
        enstrophy u t₀ +
          c_nu_H1 ν * (enstrophy u t₀ * Real.exp (c_nu_H1 ν * I)) * I := by
    intro I
    have henv := (critical_prodi_serrin_enstrophy_reduction_torus3D hns hmean ht₀ hT).2.2
    exact hgen (enstrophy u t₀ * Real.exp (c_nu_H1 ν * I)) henv
  exact ⟨hgen, hself⟩

-- ============================================================================
-- SECTION 3: THEOREM 9A2-3 — LOCAL SAFE HORIZON ("LEAF TRACKING") & GARRY STEP
-- ============================================================================

/-- **THEOREM 9A2-3 (Unconditional Local Safe Time Horizon — "Never Lose Sight of the Leaf"):**
    For ANY starting time `t₀ ≥ 0` and ANY `t ≥ t₀` satisfying the explicit blow-up safety
    condition `2 * c_nu_H1 ν * Z(t₀)² * (t - t₀) < 1` (equivalently `t - t₀ < T_local_H1 Z(t₀) ν`
    when `Z(t₀) > 0`), with NO division by `Z(s)` and valid for all `Z(t₀) ≥ 0`:
1. `(enstrophy u t)² * (1 - 2 * c_nu_H1 ν * Z(t₀)² * (t - t₀)) ≤ Z(t₀)²`,
2. `(enstrophy u t)² ≤ Z(t₀)² / (1 - 2 * c_nu_H1 ν * Z(t₀)² * (t - t₀))`,
3. `enstrophy u t ≤ Z(t₀) / √(1 - 2 * c_nu_H1 ν * Z(t₀)² * (t - t₀))`. -/
theorem local_safe_horizon_leaf_tracking_torus3D
    {u : ℝ → R3 → R3} {p : ℝ → R3 → ℝ} {ν : ℝ}
    (hns : IsPeriodicClassicalNS3D_C3 u p ν)
    (hmean : ∀ s ≥ 0, ∀ c : Fin 3, torusIntegral (fun x => u s x c) = 0)
    {t₀ t : ℝ} (ht₀ : 0 ≤ t₀) (ht : t₀ ≤ t)
    (hsafe : 2 * c_nu_H1 ν * (enstrophy u t₀) ^ 2 * (t - t₀) < 1) :
    let D : ℝ := 1 - 2 * c_nu_H1 ν * (enstrophy u t₀) ^ 2 * (t - t₀)
    (enstrophy u t) ^ 2 * D ≤ (enstrophy u t₀) ^ 2 ∧
    (enstrophy u t) ^ 2 ≤ (enstrophy u t₀) ^ 2 / D ∧
    enstrophy u t ≤ enstrophy u t₀ / Real.sqrt D := by
  intro D
  have hν : 0 < ν := hns.h_nu_pos
  have hZ0_nn : 0 ≤ enstrophy u t₀ := enstrophy_nonneg_9a2 hns ht₀
  have hZt_nn : 0 ≤ enstrophy u t := enstrophy_nonneg_9a2 hns (le_trans ht₀ ht)
  have hD_pos : 0 < D := by dsimp only [D]; linarith
  let Z0 : ℝ := enstrophy u t₀
  let cν : ℝ := c_nu_H1 ν
  let a : ℝ → ℝ := fun r => 1 - 2 * cν * Z0 ^ 2 * (r - t₀)
  let w : ℝ → ℝ := fun r => (enstrophy u r) ^ 2 * a r
  let E : ℝ → ℝ := fun r => Real.exp (-(2 * cν * ∫ s in t₀..r, (enstrophy u (max s 0)) ^ 2))
  let G : ℝ → ℝ := fun r => E r * (w r - Z0 ^ 2)
  let G' : ℝ → ℝ := fun r =>
    E r * ((2 * enstrophy u r * deriv (enstrophy u) r * a r -
      2 * cν * Z0 ^ 2 * (enstrophy u r) ^ 2) -
      2 * cν * (enstrophy u r) ^ 2 * (w r - Z0 ^ 2))
  have hG_deriv : ∀ r ≥ t₀, HasDerivAt G (G' r) r := fun r hr => by
    have hZ : HasDerivAt (enstrophy u) (deriv (enstrophy u) r) r := by
      have hd := hasDerivAt_enstrophy_evolution_3D hns (le_trans ht₀ hr)
      rw [hd.2]; exact hd.1
    have hZ2 : HasDerivAt (fun q => (enstrophy u q) ^ 2)
        (2 * enstrophy u r * deriv (enstrophy u) r) r := by
      have hm := hZ.mul hZ
      have hfun : enstrophy u * enstrophy u = fun q => (enstrophy u q) ^ 2 := by
        funext q
        change enstrophy u q * enstrophy u q = (enstrophy u q) ^ 2
        ring
      rw [hfun] at hm
      convert hm using 1
      ring
    have hlin : HasDerivAt (fun q : ℝ => 2 * cν * Z0 ^ 2 * (q - t₀)) (2 * cν * Z0 ^ 2) r := by
      simpa [mul_one] using ((hasDerivAt_id r).sub_const t₀).const_mul (2 * cν * Z0 ^ 2)
    have ha : HasDerivAt a (-(2 * cν * Z0 ^ 2)) r := by
      have hsub := (hasDerivAt_const r (1 : ℝ)).sub hlin
      convert hsub using 1
      ring
    have hw : HasDerivAt w
        (2 * enstrophy u r * deriv (enstrophy u) r * a r -
          2 * cν * Z0 ^ 2 * (enstrophy u r) ^ 2) r := by
      have hm := hZ2.mul ha
      convert hm using 1
      ring
    have hI := hasDerivAt_integral_enstrophy_sq_ext hns t₀ (le_trans ht₀ hr)
    have hE : HasDerivAt E (E r * (-(2 * cν * (enstrophy u r) ^ 2))) r :=
      ((hI.const_mul (2 * cν)).neg).exp
    have hprod := hE.mul (hw.sub_const (Z0 ^ 2))
    convert hprod using 1
    dsimp only [G']; ring
  have hG_cont : ContinuousOn G (Set.Icc t₀ t) :=
    fun r hr => (hG_deriv r hr.1).continuousAt.continuousWithinAt
  have hG_nonpos : ∀ r ∈ Set.Ioo t₀ t, G' r ≤ 0 := fun r hr => by
    have hr_nn : 0 ≤ r := le_trans ht₀ (le_of_lt hr.1)
    have hZr_nn : 0 ≤ enstrophy u r := enstrophy_nonneg_9a2 hns hr_nn
    have hcZ2_nn : 0 ≤ 2 * cν * Z0 ^ 2 := by
      dsimp only [cν]; exact mul_nonneg (mul_nonneg (by norm_num) (le_of_lt (c_nu_H1_pos hν))) (sq_nonneg _)
    have ha_pos : 0 < a r := by
      have hle : 2 * cν * Z0 ^ 2 * (r - t₀) ≤ 2 * cν * Z0 ^ 2 * (t - t₀) :=
        mul_le_mul_of_nonneg_left (by linarith [hr.2]) hcZ2_nn
      dsimp only [a, cν, Z0] at hle ⊢
      linarith
    have hdz : deriv (enstrophy u) r ≤ cν * (enstrophy u r) ^ 3 :=
      deriv_enstrophy_le_cubic hns hmean hr_nn
    have h2Za_nn : 0 ≤ 2 * enstrophy u r * a r :=
      mul_nonneg (mul_nonneg (by norm_num) hZr_nn) (le_of_lt ha_pos)
    have hterm : 2 * enstrophy u r * deriv (enstrophy u) r * a r ≤
        2 * cν * (enstrophy u r) ^ 4 * a r := by
      have := mul_le_mul_of_nonneg_left hdz h2Za_nn
      linarith
    have hbr : (2 * enstrophy u r * deriv (enstrophy u) r * a r -
        2 * cν * Z0 ^ 2 * (enstrophy u r) ^ 2) -
        2 * cν * (enstrophy u r) ^ 2 * (w r - Z0 ^ 2) ≤ 0 := by
      dsimp only [w]; linarith
    exact mul_nonpos_of_nonneg_of_nonpos (le_of_lt (Real.exp_pos _)) hbr
  have hGt_le : G t ≤ G t₀ :=
    antitone_of_hasDerivAt_nonpos ht hG_cont (fun r hr => hG_deriv r (le_of_lt hr.1)) hG_nonpos
  have hG0 : G t₀ = 0 := by
    dsimp only [G, w, a, Z0]
    simp
  rw [hG0] at hGt_le
  have hE_pos : 0 < E t := Real.exp_pos _
  have hw_le : w t - Z0 ^ 2 ≤ 0 := by
    by_contra hpos
    push Not at hpos
    have : 0 < G t := mul_pos hE_pos hpos
    linarith
  have h1 : (enstrophy u t) ^ 2 * D ≤ (enstrophy u t₀) ^ 2 := by
    dsimp only [w, a, cν, Z0] at hw_le
    dsimp only [D]
    linarith
  have h2 : (enstrophy u t) ^ 2 ≤ (enstrophy u t₀) ^ 2 / D :=
    (le_div_iff₀ hD_pos).mpr h1
  have h3 : enstrophy u t ≤ enstrophy u t₀ / Real.sqrt D := by
    have hsqD_pos : 0 < Real.sqrt D := Real.sqrt_pos.mpr hD_pos
    have hR_nn : 0 ≤ enstrophy u t₀ / Real.sqrt D := div_nonneg hZ0_nn (le_of_lt hsqD_pos)
    have hR_sq : (enstrophy u t₀ / Real.sqrt D) ^ 2 = (enstrophy u t₀) ^ 2 / D := by
      rw [div_pow, Real.sq_sqrt (le_of_lt hD_pos)]
    by_contra hgt
    push Not at hgt
    have : (enstrophy u t₀ / Real.sqrt D) ^ 2 < (enstrophy u t) ^ 2 := by nlinarith
    linarith
  exact ⟨h1, h2, h3⟩

/-- **COROLLARY 9A2-3B (Certified Half-Horizon Garry Step Enclosure — Bridge to Milestone 9B):**
    Whenever Garry takes a step `[t₀, T]` satisfying the half-horizon budget
    `2 * c_nu_H1 ν * Z(t₀)² * (T - t₀) ≤ 1/2` (i.e. `Δt ≤ T_local_H1 Z(t₀) ν / 2`):
1. For every `s ∈ [t₀, T]`, `Z(s)² ≤ 2 Z(t₀)²` and `Z(s) ≤ √2 Z(t₀)` (leaf never doubles in `L²`),
2. The single-step critical Prodi-Serrin budget is strictly bounded:
       `∫_{t₀}^T Z(s)² ds ≤ 2 Z(t₀)² (T - t₀)` and `c_nu_H1 ν * ∫_{t₀}^T Z(s)² ds ≤ 1/2`. -/
theorem garry_safe_step_enclosure_torus3D
    {u : ℝ → R3 → R3} {p : ℝ → R3 → ℝ} {ν : ℝ}
    (hns : IsPeriodicClassicalNS3D_C3 u p ν)
    (hmean : ∀ s ≥ 0, ∀ c : Fin 3, torusIntegral (fun x => u s x c) = 0)
    {t₀ T : ℝ} (ht₀ : 0 ≤ t₀) (hT : t₀ ≤ T)
    (hhalf : 2 * c_nu_H1 ν * (enstrophy u t₀) ^ 2 * (T - t₀) ≤ 1 / 2) :
    (∀ s ∈ Set.Icc t₀ T, (enstrophy u s) ^ 2 ≤ 2 * (enstrophy u t₀) ^ 2) ∧
    (∀ s ∈ Set.Icc t₀ T, enstrophy u s ≤ Real.sqrt 2 * enstrophy u t₀) ∧
    (∫ s in t₀..T, (enstrophy u s) ^ 2) ≤ 2 * (enstrophy u t₀) ^ 2 * (T - t₀) ∧
    c_nu_H1 ν * (∫ s in t₀..T, (enstrophy u s) ^ 2) ≤ 1 / 2 := by
  have hν : 0 < ν := hns.h_nu_pos
  have hZ0_nn : 0 ≤ enstrophy u t₀ := enstrophy_nonneg_9a2 hns ht₀
  have hcZ2_nn : 0 ≤ 2 * c_nu_H1 ν * (enstrophy u t₀) ^ 2 :=
    mul_nonneg (mul_nonneg (by norm_num) (le_of_lt (c_nu_H1_pos hν))) (sq_nonneg _)
  have hsq_bnd : ∀ s ∈ Set.Icc t₀ T, (enstrophy u s) ^ 2 ≤ 2 * (enstrophy u t₀) ^ 2 := by
    intro s hs
    have hstep : 2 * c_nu_H1 ν * (enstrophy u t₀) ^ 2 * (s - t₀) ≤ 1 / 2 := by
      have hle := mul_le_mul_of_nonneg_left (show s - t₀ ≤ T - t₀ by linarith [hs.2]) hcZ2_nn
      linarith
    have hloc := (local_safe_horizon_leaf_tracking_torus3D hns hmean ht₀ hs.1 (by linarith)).1
    have hD_ge : 1 / 2 ≤ 1 - 2 * c_nu_H1 ν * (enstrophy u t₀) ^ 2 * (s - t₀) := by linarith
    have hmul := mul_le_mul_of_nonneg_left hD_ge (sq_nonneg (enstrophy u s))
    linarith
  have hlin_bnd : ∀ s ∈ Set.Icc t₀ T, enstrophy u s ≤ Real.sqrt 2 * enstrophy u t₀ := by
    intro s hs
    have hZs_nn : 0 ≤ enstrophy u s := enstrophy_nonneg_9a2 hns (le_trans ht₀ hs.1)
    have hR_nn : 0 ≤ Real.sqrt 2 * enstrophy u t₀ := mul_nonneg (Real.sqrt_nonneg _) hZ0_nn
    have hsq := hsq_bnd s hs
    have hR_sq : (Real.sqrt 2 * enstrophy u t₀) ^ 2 = 2 * (enstrophy u t₀) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt (by norm_num)]
    by_contra hgt
    push Not at hgt
    have : (Real.sqrt 2 * enstrophy u t₀) ^ 2 < (enstrophy u s) ^ 2 := by nlinarith
    linarith
  have hint_bnd : (∫ s in t₀..T, (enstrophy u s) ^ 2) ≤ 2 * (enstrophy u t₀) ^ 2 * (T - t₀) := by
    have hc : Continuous (fun s : ℝ => (enstrophy u (max s 0)) ^ 2) :=
      (enstrophy_ext_continuous hns).pow 2
    rw [← integral_enstrophy_sq_ext_eq ht₀ hT]
    have hconst : (∫ _ in t₀..T, 2 * (enstrophy u t₀) ^ 2) = 2 * (enstrophy u t₀) ^ 2 * (T - t₀) := by
      rw [intervalIntegral.integral_const, smul_eq_mul]; ring
    rw [← hconst]
    apply intervalIntegral.integral_mono_on hT (hc.intervalIntegrable t₀ T)
      (continuous_const.intervalIntegrable t₀ T)
    intro s hs
    rw [max_eq_left (le_trans ht₀ hs.1)]
    exact hsq_bnd s hs
  have hbudget : c_nu_H1 ν * (∫ s in t₀..T, (enstrophy u s) ^ 2) ≤ 1 / 2 := by
    have hmul := mul_le_mul_of_nonneg_left hint_bnd (le_of_lt (c_nu_H1_pos hν))
    linarith
  exact ⟨hsq_bnd, hlin_bnd, hint_bnd, hbudget⟩

-- ============================================================================
-- SECTION 4: THEOREM 9A2-4 — UNIFIED 9A1 + 9A2 MASTER & OPEN-GAP REDUCTION
-- ============================================================================

/-- **THEOREM 9A2-4 (MILESTONE 9A2 MASTER — Unified Waterfall Trap & Global `L⁴_t Ḣ¹_x` Split):**
    Unifies Milestone 9A1 (`unconditional_waterfall_trap_to_exponential_river_torus3D`) and
    Milestone 9A2 for ANY mean-zero 3D Navier-Stokes classical solution `(u, p)` on `𝕋³`
    and ANY horizon `T_end > T_trap_H1 (kineticEnergy u 0) ν`:
    There exists a finite capture time `t* ∈ [0, T_end]` with `Z(t*) < Z_crit_H1 ν / 2` such that:
1. **Unconditional uniform river tail bound** for ALL `T ≥ t*`:
       `∫_{t*}^T Z(s)² ds ≤ Z(t*)² / (3π² ν) < 4π⁴ ν³ / 507`.
2. **Global critical `L⁴_t Ḣ¹_x` reduction** for ALL `T ≥ 0`:
       `∫_0^T Z(s)² ds ≤ (∫_0^{t*} Z(s)² ds) + Z(t*)² / (3π² ν)`.
3. **Global `L∞_t H¹_x` reduction** for ALL `T ≥ 0`:
       `Z(T) ≤ Z(0) * exp(c_nu_H1 ν * ∫_0^{t*} Z(s)² ds)`.
4. **Global `L²_t Ḣ²_x` palinstrophy reduction** (if `palinstrophy3D (u ·)` is continuous)
       for ALL `T ≥ 0`:
       `∫_0^T P(s) ds ≤ (4 / ν) * (Z(0) + c_nu_H1 ν * Z(0) * exp(c_nu_H1 ν * I_pre) * I_pre) + (16 / (3ν)) * Z(t*)`,
       where `I_pre = ∫_0^{t*} Z(s)² ds` is the sole finite waterfall budget remaining on `[0, T_trap]`. -/
theorem milestone9A2_unified_waterfall_prodi_serrin_master_torus3D
    {u : ℝ → R3 → R3} {p : ℝ → R3 → ℝ} {ν T_end : ℝ}
    (hns : IsPeriodicClassicalNS3D_C3 u p ν)
    (hmean : ∀ s ≥ 0, ∀ c : Fin 3, torusIntegral (fun x => u s x c) = 0)
    (hT_trap : T_trap_H1 (kineticEnergy u 0) ν < T_end) :
    ∃ t_star ∈ Set.Icc (0 : ℝ) T_end,
      let I_pre : ℝ := ∫ s in (0 : ℝ)..t_star, (enstrophy u s) ^ 2
      enstrophy u t_star < Z_crit_H1 ν / 2 ∧
      (∀ T ≥ t_star,
        (∫ s in t_star..T, (enstrophy u s) ^ 2) ≤ (enstrophy u t_star) ^ 2 / (3 * Real.pi ^ 2 * ν)) ∧
      (enstrophy u t_star) ^ 2 / (3 * Real.pi ^ 2 * ν) < 4 * Real.pi ^ 4 * ν ^ 3 / 507 ∧
      (∀ T ≥ 0,
        (∫ s in (0 : ℝ)..T, (enstrophy u s) ^ 2) ≤
          I_pre + (enstrophy u t_star) ^ 2 / (3 * Real.pi ^ 2 * ν)) ∧
      (∀ T ≥ 0,
        enstrophy u T ≤ enstrophy u 0 * Real.exp (c_nu_H1 ν * I_pre)) ∧
      (Continuous (fun s : ℝ => palinstrophy3D (u s)) →
        ∀ T ≥ 0,
          (∫ s in (0 : ℝ)..T, palinstrophy3D (u s)) ≤
            (4 / ν) * (enstrophy u 0 +
              c_nu_H1 ν * (enstrophy u 0 * Real.exp (c_nu_H1 ν * I_pre)) * I_pre) +
            (16 / (3 * ν)) * enstrophy u t_star) := by
  have hν : 0 < ν := hns.h_nu_pos
  obtain ⟨t_star, ht_mem, ht_cap, ht_inv, ht_dec, ht_pal⟩ :=
    unconditional_waterfall_trap_to_exponential_river_torus3D hns hmean hT_trap
  have ht_nn : 0 ≤ t_star := ht_mem.1
  have hZt_nn : 0 ≤ enstrophy u t_star := enstrophy_nonneg_9a2 hns ht_nn
  refine ⟨t_star, ht_mem, ?_⟩
  intro I_pre
  -- Part 1: Unconditional tail L⁴_t Ḣ¹_x integral bound on [t*, ∞)
  have htail : ∀ T ≥ t_star,
      (∫ s in t_star..T, (enstrophy u s) ^ 2) ≤
        (enstrophy u t_star) ^ 2 / (3 * Real.pi ^ 2 * ν) := by
    intro T hT
    let k : ℝ := 3 * Real.pi ^ 2 * ν
    have hk_pos : 0 < k := by dsimp only [k]; positivity
    have hk_ne : k ≠ 0 := ne_of_gt hk_pos
    let q : ℝ → ℝ := fun r =>
      (∫ s in t_star..r, (enstrophy u (max s 0)) ^ 2) +
        ((enstrophy u t_star) ^ 2 / k) * Real.exp (-k * (r - t_star))
    let q' : ℝ → ℝ := fun r =>
      (enstrophy u r) ^ 2 - (enstrophy u t_star) ^ 2 * Real.exp (-k * (r - t_star))
    have hq_deriv : ∀ r ≥ t_star, HasDerivAt q (q' r) r := fun r hr => by
      have hI := hasDerivAt_integral_enstrophy_sq_ext hns t_star (le_trans ht_nn hr)
      have hlin : HasDerivAt (fun s : ℝ => -k * (s - t_star)) (-k) r := by
        simpa [mul_one] using ((hasDerivAt_id r).sub_const t_star).const_mul (-k)
      have he : HasDerivAt (fun s : ℝ => Real.exp (-k * (s - t_star)))
          (Real.exp (-k * (r - t_star)) * (-k)) r := hlin.exp
      have hsum := hI.add (he.const_mul ((enstrophy u t_star) ^ 2 / k))
      convert hsum using 1
      dsimp only [q']
      field_simp
      ring
    have hq_cont : ContinuousOn q (Set.Icc t_star T) :=
      fun r hr => (hq_deriv r hr.1).continuousAt.continuousWithinAt
    have hq_nonpos : ∀ r ∈ Set.Ioo t_star T, q' r ≤ 0 := fun r hr => by
      have hr_ge : r ≥ t_star := le_of_lt hr.1
      have hZr_nn : 0 ≤ enstrophy u r := enstrophy_nonneg_9a2 hns (le_trans ht_nn hr_ge)
      have hle := ht_dec r hr_ge
      have hexp_nn : 0 ≤ enstrophy u t_star *
          Real.exp (-(3 / 2 * Real.pi ^ 2 * ν) * (r - t_star)) :=
        mul_nonneg hZt_nn (le_of_lt (Real.exp_pos _))
      have hsq_le : (enstrophy u r) ^ 2 ≤
          (enstrophy u t_star * Real.exp (-(3 / 2 * Real.pi ^ 2 * ν) * (r - t_star))) ^ 2 := by
        nlinarith
      have hexp_sq : (Real.exp (-(3 / 2 * Real.pi ^ 2 * ν) * (r - t_star))) ^ 2 =
          Real.exp (-k * (r - t_star)) := by
        rw [sq, ← Real.exp_add]
        congr 1
        dsimp only [k]
        ring
      rw [mul_pow, hexp_sq] at hsq_le
      dsimp only [q']
      linarith
    have hqT_le : q T ≤ q t_star :=
      antitone_of_hasDerivAt_nonpos hT hq_cont (fun r hr => hq_deriv r (le_of_lt hr.1)) hq_nonpos
    have hq0 : q t_star = (enstrophy u t_star) ^ 2 / k := by
      dsimp only [q]; simp
    rw [hq0] at hqT_le
    dsimp only [q] at hqT_le
    rw [integral_enstrophy_sq_ext_eq ht_nn hT] at hqT_le
    have hrem_nn : 0 ≤ ((enstrophy u t_star) ^ 2 / k) * Real.exp (-k * (T - t_star)) :=
      mul_nonneg (div_nonneg (sq_nonneg _) (le_of_lt hk_pos)) (le_of_lt (Real.exp_pos _))
    linarith
  -- Part 2: Explicit numerical ceiling 4 π⁴ ν³ / 507 on the river tail
  have htail_cap : (enstrophy u t_star) ^ 2 / (3 * Real.pi ^ 2 * ν) <
      4 * Real.pi ^ 4 * ν ^ 3 / 507 := by
    have hsq : (enstrophy u t_star) ^ 2 < (Z_crit_H1 ν / 2) ^ 2 := by
      have hpos : 0 < Z_crit_H1 ν / 2 := half_pos (Z_crit_H1_pos hν)
      nlinarith
    have hdiv : (enstrophy u t_star) ^ 2 / (3 * Real.pi ^ 2 * ν) <
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
  -- Part 3: Global L⁴_t Ḣ¹_x split for all T ≥ 0
  have hglob_L4 : ∀ T ≥ 0,
      (∫ s in (0 : ℝ)..T, (enstrophy u s) ^ 2) ≤
        I_pre + (enstrophy u t_star) ^ 2 / (3 * Real.pi ^ 2 * ν) := by
    intro T hT
    have htail_nn : 0 ≤ (enstrophy u t_star) ^ 2 / (3 * Real.pi ^ 2 * ν) := by positivity
    rcases le_total T t_star with hle | hge
    · have hmono := integral_enstrophy_sq_mono hns le_rfl hT hle
      dsimp only [I_pre]; linarith
    · have hc : Continuous (fun s : ℝ => (enstrophy u (max s 0)) ^ 2) :=
        (enstrophy_ext_continuous hns).pow 2
      have hsplit : (∫ s in (0 : ℝ)..T, (enstrophy u s) ^ 2) =
          I_pre + (∫ s in t_star..T, (enstrophy u s) ^ 2) := by
        dsimp only [I_pre]
        rw [← integral_enstrophy_sq_ext_eq le_rfl hT,
            ← integral_enstrophy_sq_ext_eq le_rfl ht_nn,
            ← integral_enstrophy_sq_ext_eq ht_nn hge]
        exact (intervalIntegral.integral_add_adjacent_intervals
          (hc.intervalIntegrable 0 t_star) (hc.intervalIntegrable t_star T)).symm
      rw [hsplit]
      linarith [htail T hge]
  -- Part 4: Global L∞_t H¹_x bound for all T ≥ 0
  have hpre_env := (critical_prodi_serrin_enstrophy_reduction_torus3D hns hmean le_rfl ht_nn).2.2
  have hglob_Z : ∀ T ≥ 0,
      enstrophy u T ≤ enstrophy u 0 * Real.exp (c_nu_H1 ν * I_pre) := by
    intro T hT
    rcases le_total T t_star with hle | hge
    · exact hpre_env T ⟨hT, hle⟩
    · exact le_trans (ht_inv T hge) (hpre_env t_star ⟨ht_nn, le_rfl⟩)
  -- Part 5: Global L²_t Ḣ²_x palinstrophy split for all T ≥ 0
  have hglob_P : Continuous (fun s : ℝ => palinstrophy3D (u s)) →
      ∀ T ≥ 0,
        (∫ s in (0 : ℝ)..T, palinstrophy3D (u s)) ≤
          (4 / ν) * (enstrophy u 0 +
            c_nu_H1 ν * (enstrophy u 0 * Real.exp (c_nu_H1 ν * I_pre)) * I_pre) +
          (16 / (3 * ν)) * enstrophy u t_star := by
    intro hP_cont T hT
    have hpre_pal := (critical_prodi_serrin_palinstrophy_bound_torus3D hns hmean hP_cont le_rfl ht_nn).2
    have hpre_int : (∫ s in (0 : ℝ)..t_star, palinstrophy3D (u s)) ≤
        (4 / ν) * (enstrophy u 0 +
          c_nu_H1 ν * (enstrophy u 0 * Real.exp (c_nu_H1 ν * I_pre)) * I_pre) := by
      have h1 : (ν / 4) * (∫ s in (0 : ℝ)..t_star, palinstrophy3D (u s)) ≤
          enstrophy u 0 +
            c_nu_H1 ν * (enstrophy u 0 * Real.exp (c_nu_H1 ν * I_pre)) * I_pre := by
        dsimp only [I_pre] at hpre_pal ⊢; linarith
      have hmul := mul_le_mul_of_nonneg_left h1 (by positivity : (0 : ℝ) ≤ 4 / ν)
      have hcancel : (4 / ν) * ((ν / 4) * (∫ s in (0 : ℝ)..t_star, palinstrophy3D (u s))) =
          ∫ s in (0 : ℝ)..t_star, palinstrophy3D (u s) := by
        have hν0 : ν ≠ 0 := ne_of_gt hν
        field_simp
      linarith
    have htail_term_nn : 0 ≤ (16 / (3 * ν)) * enstrophy u t_star := by positivity
    rcases le_total T t_star with hle | hge
    · have hadd := intervalIntegral.integral_add_adjacent_intervals
        (hP_cont.intervalIntegrable (μ := volume) 0 T)
        (hP_cont.intervalIntegrable (μ := volume) T t_star)
      have hrem_nn : 0 ≤ ∫ s in T..t_star, palinstrophy3D (u s) :=
        intervalIntegral.integral_nonneg hle (fun s hs => palinstrophy_nonneg_9a2 hns (le_trans hT hs.1))
      linarith
    · have hadd := intervalIntegral.integral_add_adjacent_intervals
        (hP_cont.intervalIntegrable (μ := volume) 0 t_star)
        (hP_cont.intervalIntegrable (μ := volume) t_star T)
      have hpost_bal := (ht_pal hP_cont).1 T hge
      have hZT_nn : 0 ≤ enstrophy u T := enstrophy_nonneg_9a2 hns hT
      have hpost_int : (∫ s in t_star..T, palinstrophy3D (u s)) ≤
          (16 / (3 * ν)) * enstrophy u t_star := by
        have h1 : (3 * ν / 16) * (∫ s in t_star..T, palinstrophy3D (u s)) ≤ enstrophy u t_star := by
          linarith
        have hmul := mul_le_mul_of_nonneg_left h1 (by positivity : (0 : ℝ) ≤ 16 / (3 * ν))
        have hcancel : (16 / (3 * ν)) * ((3 * ν / 16) * (∫ s in t_star..T, palinstrophy3D (u s))) =
            ∫ s in t_star..T, palinstrophy3D (u s) := by
          have hν0 : ν ≠ 0 := ne_of_gt hν
          field_simp
        linarith
      linarith
  exact ⟨ht_cap, htail, htail_cap, hglob_L4, hglob_Z, hglob_P⟩

-- ============================================================================
-- SECTION 5: AXIOM AUDIT TRAIL (0 sorryAx, 0 custom axioms)
-- ============================================================================

#print axioms critical_prodi_serrin_enstrophy_reduction_torus3D
#print axioms critical_prodi_serrin_palinstrophy_bound_torus3D
#print axioms local_safe_horizon_leaf_tracking_torus3D
#print axioms garry_safe_step_enclosure_torus3D
#print axioms milestone9A2_unified_waterfall_prodi_serrin_master_torus3D

end GarryCriticalProdiSerrin3D