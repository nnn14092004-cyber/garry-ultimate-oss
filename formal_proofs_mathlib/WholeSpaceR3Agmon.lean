import WholeSpaceR3Integral
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

/-!
# Milestone 10A-2 (Hurdle 1 — Tier I, 100% Unconditional): Real-Space 3D Agmon Inequality
  & Unconditional 3D Vortex Stretching Bound on Whole Space `ℝ³` (`0 sorryAx`)

This module proves, directly in Cartesian real space `ℝ³` with zero Fourier inversion,
zero polar coordinates, zero compactness, and zero `Torus3D` imports:

1. Exact 1D & 3D smooth radial kernel integrals for `ρ_a(y) = √(|y|² + a²)`:
   - `∫_{ℝ³} ρ_a(y)^{-4} dy = π² / a`,
   - `∫_{ℝ³} ρ_a(y)^{-6} dy ≤ π² / a³`,
   - `∫_{ℝ³} 3 a² ρ_a(y)^{-5} dy = 4π`.
2. Exact two-kernel smooth Green identity on `ℝ³` via `r3Integral_ibp` for
   `ψ_{ε,R}(y) = ρ_ε(y)^{-1} - ρ_R(y)^{-1} = ∫_ε^R s ρ_s(y)^{-3} ds`.
3. **Theorem 10A2-1 (Whole-Space `ℝ³` Scalar Agmon 3D Inequality):**
   `f(x)² ≤ (1 / 2) * √(∫_{ℝ³} |∇ f|²) * √(∫_{ℝ³} (Δ f)²)`.
4. **Theorem 10A2-2 (Whole-Space `ℝ³` Vector Agmon 3D Inequality):**
   `|u(x)|² ≤ (1 / 2) * √(2 Z_{ℝ³}(u)) * √(P_{ℝ³}(u))`.
5. **Theorem 10A2-3 (Unconditional Whole-Space `ℝ³` Vortex Stretching Bound):**
   `|vortexStretchingR3 u| ≤ C3D_agmon_R3 * Z_{ℝ³}^{3/4} * P_{ℝ³}^{3/4}`,
   with `C3D_agmon_R3 = √(√2)`, `(C3D_agmon_R3)⁴ = 2`, and `c_nu_R3 ν = 1 / (2 ν³)`.
-/

namespace GarryWholeSpaceR3Agmon

open MeasureTheory Filter Topology
open GarryReal3DCalculus
open GarryVorticity3D
open GarryWholeSpaceR3

-- ============================================================================
-- SECTION 0: EXPLICIT WHOLE-SPACE CONSTANTS & SMOOTH RADIAL KERNELS
-- ============================================================================

/-- Explicit unconditional 3D Agmon-IBP vortex stretching constant on `ℝ³`:
    `C3D_agmon_R3 = 2^{1/4} = √(√2)`, satisfying `C3D_agmon_R3⁴ = 2`. -/
noncomputable def C3D_agmon_R3 : ℝ :=
  Real.sqrt (Real.sqrt 2)

/-- Explicit unconditional cubic vortex-stretching coefficient on `ℝ³`:
    `c_nu_R3 ν = C3D_agmon_R3⁴ / (4 ν³) = 1 / (2 ν³)`. -/
noncomputable def c_nu_R3 (ν : ℝ) : ℝ :=
  1 / (2 * ν ^ 3)

lemma C3D_agmon_R3_nonneg : 0 ≤ C3D_agmon_R3 := Real.sqrt_nonneg _

lemma C3D_agmon_R3_pow_two : C3D_agmon_R3 ^ 2 = Real.sqrt 2 :=
  Real.sq_sqrt (Real.sqrt_nonneg 2)

lemma C3D_agmon_R3_pow_four : C3D_agmon_R3 ^ 4 = 2 := by
  calc C3D_agmon_R3 ^ 4 = (C3D_agmon_R3 ^ 2) ^ 2 := by ring
    _ = (Real.sqrt 2) ^ 2 := by rw [C3D_agmon_R3_pow_two]
    _ = 2 := Real.sq_sqrt (by norm_num)

lemma c_nu_R3_pos {ν : ℝ} (hν : 0 < ν) : 0 < c_nu_R3 ν := by
  unfold c_nu_R3; positivity

/-- Smooth regularized Euclidean radius `ρ_a(y) = √(y₀² + y₁² + y₂² + a²)` on `ℝ³`. -/
noncomputable def r3Rho (a : ℝ) (y : R3) : ℝ :=
  Real.sqrt ((y 0) ^ 2 + (y 1) ^ 2 + (y 2) ^ 2 + a ^ 2)

/-- Smooth regularized Newtonian kernel `φ_a(y) = ρ_a(y)⁻¹` on `ℝ³`. -/
noncomputable def r3Phi (a : ℝ) (y : R3) : ℝ :=
  (r3Rho a y)⁻¹

/-- Smooth difference kernel `ψ_{ε,R}(y) = φ_ε(y) - φ_R(y)` on `ℝ³`. -/
noncomputable def r3Psi (ε R : ℝ) (y : R3) : ℝ :=
  r3Phi ε y - r3Phi R y

lemma r3Rho_pos {a : ℝ} (ha : 0 < a) (y : R3) : 0 < r3Rho a y := by
  unfold r3Rho
  exact Real.sqrt_pos.mpr (by positivity)

lemma r3Rho_ge_param {a : ℝ} (ha : 0 < a) (y : R3) : a ≤ r3Rho a y := by
  unfold r3Rho
  have hsq : a ^ 2 ≤ (y 0) ^ 2 + (y 1) ^ 2 + (y 2) ^ 2 + a ^ 2 := by
    have : 0 ≤ (y 0) ^ 2 + (y 1) ^ 2 + (y 2) ^ 2 := by positivity
    linarith
  have hle := Real.sqrt_le_sqrt hsq
  rwa [Real.sqrt_sq (le_of_lt ha)] at hle

lemma r3Rho_sq (a : ℝ) (y : R3) :
    (r3Rho a y) ^ 2 = (y 0) ^ 2 + (y 1) ^ 2 + (y 2) ^ 2 + a ^ 2 := by
  unfold r3Rho
  exact Real.sq_sqrt (by positivity)

lemma r3Rho_continuous (a : ℝ) : Continuous (r3Rho a) := by
  unfold r3Rho
  exact Real.continuous_sqrt.comp
    (((((continuous_apply 0).pow 2).add ((continuous_apply 1).pow 2)).add
      ((continuous_apply 2).pow 2)).add continuous_const)

lemma r3Phi_continuous {a : ℝ} (ha : 0 < a) : Continuous (r3Phi a) :=
  (r3Rho_continuous a).inv₀ (fun y => ne_of_gt (r3Rho_pos ha y))

lemma r3Rho_inv_pow_nonneg {a : ℝ} (ha : 0 < a) (n : ℕ) (y : R3) :
    0 ≤ ((r3Rho a y) ^ n)⁻¹ :=
  inv_nonneg.mpr (pow_nonneg (le_of_lt (r3Rho_pos ha y)) n)

lemma r3_coord_sq_le_rho_sq (a : ℝ) (y : R3) (i : Fin 3) :
    (y i) ^ 2 ≤ (r3Rho a y) ^ 2 := by
  rw [r3Rho_sq]
  fin_cases i
  · change (y 0) ^ 2 ≤ _; nlinarith [sq_nonneg (y 1), sq_nonneg (y 2), sq_nonneg a]
  · change (y 1) ^ 2 ≤ _; nlinarith [sq_nonneg (y 0), sq_nonneg (y 2), sq_nonneg a]
  · change (y 2) ^ 2 ≤ _; nlinarith [sq_nonneg (y 0), sq_nonneg (y 1), sq_nonneg a]

-- ============================================================================
-- SECTION 1: FOUR EXACT 1D ELEMENTARY IMPROPER INTEGRALS ON ℝ
-- ============================================================================

private lemma integral_real_of_hasDerivAt_of_tendsto {F f : ℝ → ℝ} {L_top L_bot : ℝ}
    (hderiv : ∀ t : ℝ, HasDerivAt F (f t) t)
    (hint : Integrable f volume)
    (htop : Tendsto F atTop (𝓝 L_top))
    (hbot : Tendsto F atBot (𝓝 L_bot)) :
    ∫ t : ℝ, f t = L_top - L_bot := by
  have hI : Tendsto (fun R : ℝ => ∫ t in (-R)..R, f t) atTop (𝓝 (∫ t : ℝ, f t)) :=
    MeasureTheory.intervalIntegral_tendsto_integral hint tendsto_neg_atTop_atBot tendsto_id
  have hftc : ∀ R : ℝ, ∫ t in (-R)..R, f t = F R - F (-R) := fun R =>
    intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun t _ => hderiv t) hint.intervalIntegrable
  have hsub : Tendsto (fun R : ℝ => F R - F (-R)) atTop (𝓝 (L_top - L_bot)) :=
    htop.sub (hbot.comp tendsto_neg_atTop_atBot)
  have hI' : Tendsto (fun R : ℝ => F R - F (-R)) atTop (𝓝 (∫ t : ℝ, f t)) := by
    simpa only [hftc] using hI
  exact tendsto_nhds_unique hI' hsub

/-- Integrability of `(t² + a²)⁻¹` on `ℝ` for any `a > 0`. -/
lemma integrable_inv_sq_add_sq {a : ℝ} (ha : 0 < a) :
    Integrable (fun t : ℝ => (t ^ 2 + a ^ 2)⁻¹) volume := by
  let c : ℝ := min 1 (a ^ 2)
  have hc_pos : 0 < c := lt_min zero_lt_one (sq_pos_of_pos ha)
  have hdom : Integrable (fun t : ℝ => c⁻¹ * (1 + t ^ 2)⁻¹) volume :=
    integrable_inv_one_add_sq.const_mul c⁻¹
  have hcont : Continuous (fun t : ℝ => (t ^ 2 + a ^ 2)⁻¹) :=
    ((continuous_id.pow 2).add continuous_const).inv₀
      (fun t => ne_of_gt (add_pos_of_nonneg_of_pos (sq_nonneg t) (sq_pos_of_pos ha)))
  refine hdom.mono' hcont.aestronglyMeasurable (Filter.Eventually.of_forall fun t => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have hle : c * (1 + t ^ 2) ≤ t ^ 2 + a ^ 2 := by
    have h1 : c ≤ 1 := min_le_left 1 (a ^ 2)
    have h2 : c ≤ a ^ 2 := min_le_right 1 (a ^ 2)
    nlinarith [sq_nonneg t]
  have hinv := inv_anti₀ (by positivity : 0 < c * (1 + t ^ 2)) hle
  rwa [mul_inv] at hinv

/-- Exact 1D integral #1: `∫_ℝ (t² + a²)⁻¹ dt = π / a`. -/
lemma integral_inv_sq_add_sq {a : ℝ} (ha : 0 < a) :
    (∫ t : ℝ, (t ^ 2 + a ^ 2)⁻¹) = Real.pi / a := by
  have ha_ne : a ≠ 0 := ne_of_gt ha
  let F : ℝ → ℝ := fun t => a⁻¹ * Real.arctan (t / a)
  have hderiv : ∀ t : ℝ, HasDerivAt F ((t ^ 2 + a ^ 2)⁻¹) t := fun t => by
    have hdiv : HasDerivAt (fun s : ℝ => s / a) (1 / a) t := (hasDerivAt_id t).div_const a
    have harc := (Real.hasDerivAt_arctan (t / a)).comp t hdiv
    have hmul : HasDerivAt F (a⁻¹ * (1 / (1 + (t / a) ^ 2) * (1 / a))) t := harc.const_mul a⁻¹
    have heq : a⁻¹ * (1 / (1 + (t / a) ^ 2) * (1 / a)) = (t ^ 2 + a ^ 2)⁻¹ := by
      have hpos : t ^ 2 + a ^ 2 ≠ 0 := ne_of_gt (add_pos_of_nonneg_of_pos (sq_nonneg t) (sq_pos_of_pos ha))
      have h1 : 1 + (t / a) ^ 2 ≠ 0 := ne_of_gt (add_pos_of_pos_of_nonneg zero_lt_one (sq_nonneg _))
      field_simp; ring
    rwa [heq] at hmul
  have htop : Tendsto F atTop (𝓝 (a⁻¹ * (Real.pi / 2))) :=
    ((Real.tendsto_arctan_atTop.mono_right nhdsWithin_le_nhds).comp
      (Filter.Tendsto.atTop_div_const ha tendsto_id)).const_mul a⁻¹
  have hbot : Tendsto F atBot (𝓝 (a⁻¹ * (-(Real.pi / 2)))) :=
    ((Real.tendsto_arctan_atBot.mono_right nhdsWithin_le_nhds).comp
      (Filter.Tendsto.atBot_div_const ha tendsto_id)).const_mul a⁻¹
  rw [integral_real_of_hasDerivAt_of_tendsto hderiv (integrable_inv_sq_add_sq ha) htop hbot]
  field_simp
  ring

/-- Integrability of `(√(t² + a²))⁻³` on `ℝ` for any `a > 0`. -/
lemma integrable_inv_sqrt_cube {a : ℝ} (ha : 0 < a) :
    Integrable (fun t : ℝ => ((Real.sqrt (t ^ 2 + a ^ 2)) ^ 3)⁻¹) volume := by
  have hdom : Integrable (fun t : ℝ => a⁻¹ * (t ^ 2 + a ^ 2)⁻¹) volume :=
    (integrable_inv_sq_add_sq ha).const_mul a⁻¹
  have hcont : Continuous (fun t : ℝ => ((Real.sqrt (t ^ 2 + a ^ 2)) ^ 3)⁻¹) :=
    ((Real.continuous_sqrt.comp ((continuous_id.pow 2).add continuous_const)).pow 3).inv₀
      (fun t => ne_of_gt (pow_pos (Real.sqrt_pos.mpr
        (add_pos_of_nonneg_of_pos (sq_nonneg t) (sq_pos_of_pos ha))) 3))
  refine hdom.mono' hcont.aestronglyMeasurable (Filter.Eventually.of_forall fun t => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have hsq : (Real.sqrt (t ^ 2 + a ^ 2)) ^ 2 = t ^ 2 + a ^ 2 := Real.sq_sqrt (by positivity)
  have hge : a ≤ Real.sqrt (t ^ 2 + a ^ 2) := by
    have := Real.sqrt_le_sqrt (show a ^ 2 ≤ t ^ 2 + a ^ 2 by nlinarith [sq_nonneg t])
    rwa [Real.sqrt_sq (le_of_lt ha)] at this
  have hcube : a * (t ^ 2 + a ^ 2) ≤ (Real.sqrt (t ^ 2 + a ^ 2)) ^ 3 := by
    calc a * (t ^ 2 + a ^ 2) ≤ Real.sqrt (t ^ 2 + a ^ 2) * (t ^ 2 + a ^ 2) :=
          mul_le_mul_of_nonneg_right hge (by positivity)
      _ = Real.sqrt (t ^ 2 + a ^ 2) * (Real.sqrt (t ^ 2 + a ^ 2)) ^ 2 := by rw [hsq]
      _ = (Real.sqrt (t ^ 2 + a ^ 2)) ^ 3 := by ring
  have hinv := inv_anti₀ (by positivity : 0 < a * (t ^ 2 + a ^ 2)) hcube
  rwa [mul_inv] at hinv

/-- Exact 1D integral #2: `∫_ℝ (√(t² + a²))⁻³ dt = 2 / a²`. -/
lemma integral_inv_sqrt_cube {a : ℝ} (ha : 0 < a) :
    (∫ t : ℝ, ((Real.sqrt (t ^ 2 + a ^ 2)) ^ 3)⁻¹) = 2 / a ^ 2 := by
  have ha_ne : a ≠ 0 := ne_of_gt ha
  let F : ℝ → ℝ := fun t => t / (a ^ 2 * Real.sqrt (t ^ 2 + a ^ 2))
  have hderiv : ∀ t : ℝ, HasDerivAt F (((Real.sqrt (t ^ 2 + a ^ 2)) ^ 3)⁻¹) t := fun t => by
    have hq : HasDerivAt (fun s : ℝ => s ^ 2 + a ^ 2) (2 * t) t := by
      simpa using (hasDerivAt_pow 2 t).add_const (a ^ 2)
    have hsq_pos : 0 < Real.sqrt (t ^ 2 + a ^ 2) := Real.sqrt_pos.mpr (by positivity)
    have hsq_ne : Real.sqrt (t ^ 2 + a ^ 2) ≠ 0 := ne_of_gt hsq_pos
    have hinner_ne : t ^ 2 + a ^ 2 ≠ 0 := by positivity
    have hsqrt : HasDerivAt (fun s : ℝ => Real.sqrt (s ^ 2 + a ^ 2))
        ((2 * t) / (2 * Real.sqrt (t ^ 2 + a ^ 2))) t := hq.sqrt hinner_ne
    have hden : HasDerivAt (fun s : ℝ => a ^ 2 * Real.sqrt (s ^ 2 + a ^ 2))
        (a ^ 2 * ((2 * t) / (2 * Real.sqrt (t ^ 2 + a ^ 2)))) t := hsqrt.const_mul (a ^ 2)
    have hdiv : HasDerivAt F
        ((1 * (a ^ 2 * Real.sqrt (t ^ 2 + a ^ 2)) -
          t * (a ^ 2 * ((2 * t) / (2 * Real.sqrt (t ^ 2 + a ^ 2))))) /
          (a ^ 2 * Real.sqrt (t ^ 2 + a ^ 2)) ^ 2) t :=
      (hasDerivAt_id t).div hden (by positivity)
    have heq : (1 * (a ^ 2 * Real.sqrt (t ^ 2 + a ^ 2)) -
        t * (a ^ 2 * ((2 * t) / (2 * Real.sqrt (t ^ 2 + a ^ 2))))) /
        (a ^ 2 * Real.sqrt (t ^ 2 + a ^ 2)) ^ 2 = ((Real.sqrt (t ^ 2 + a ^ 2)) ^ 3)⁻¹ := by
      set s := Real.sqrt (t ^ 2 + a ^ 2)
      have hs2 : s ^ 2 = t ^ 2 + a ^ 2 := Real.sq_sqrt (by positivity)
      have hnum : 1 * (a ^ 2 * s) - t * (a ^ 2 * ((2 * t) / (2 * s))) = a ^ 4 / s := by
        field_simp
        linarith [hs2]
      rw [hnum]
      field_simp
    rwa [heq] at hdiv
  have htop_lim : Tendsto (fun t : ℝ => (1 : ℝ) / (a ^ 2 * Real.sqrt (1 + (a / t) ^ 2)))
      atTop (𝓝 (1 / a ^ 2)) := by
    have h0 : Tendsto (fun t : ℝ => a / t) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop tendsto_id
    have h1 : Tendsto (fun t : ℝ => 1 + (a / t) ^ 2) atTop (𝓝 1) := by
      simpa using (h0.pow 2).const_add (1 : ℝ)
    have h2 : Tendsto (fun t : ℝ => a ^ 2 * Real.sqrt (1 + (a / t) ^ 2)) atTop (𝓝 (a ^ 2)) := by
      have hs : Tendsto (fun t : ℝ => Real.sqrt (1 + (a / t) ^ 2)) atTop (𝓝 (Real.sqrt 1)) :=
        Real.continuous_sqrt.continuousAt.tendsto.comp h1
      rw [Real.sqrt_one] at hs
      simpa only [mul_one] using hs.const_mul (a ^ 2)
    exact tendsto_const_nhds.div h2 (ne_of_gt (sq_pos_of_pos ha))
  have htop : Tendsto F atTop (𝓝 (1 / a ^ 2)) := by
    refine htop_lim.congr' ?_
    filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with t ht
    have hfac : t ^ 2 + a ^ 2 = t ^ 2 * (1 + (a / t) ^ 2) := by
      have ht0 : t ≠ 0 := ne_of_gt ht; field_simp
    have hsq : Real.sqrt (t ^ 2 + a ^ 2) = t * Real.sqrt (1 + (a / t) ^ 2) := by
      rw [hfac, Real.sqrt_mul (sq_nonneg t), Real.sqrt_sq (le_of_lt ht)]
    dsimp only [F]; rw [hsq]
    have ht0 : t ≠ 0 := ne_of_gt ht
    have h1 : Real.sqrt (1 + (a / t) ^ 2) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (by positivity))
    field_simp
  have hbot_lim : Tendsto (fun t : ℝ => (-1 : ℝ) / (a ^ 2 * Real.sqrt (1 + (a / t) ^ 2)))
      atBot (𝓝 (-(1 / a ^ 2))) := by
    have h0 : Tendsto (fun t : ℝ => a / t) atBot (𝓝 0) :=
      tendsto_const_nhds.div_atBot tendsto_id
    have h1 : Tendsto (fun t : ℝ => 1 + (a / t) ^ 2) atBot (𝓝 1) := by
      simpa using (h0.pow 2).const_add (1 : ℝ)
    have h2 : Tendsto (fun t : ℝ => a ^ 2 * Real.sqrt (1 + (a / t) ^ 2)) atBot (𝓝 (a ^ 2)) := by
      have hs : Tendsto (fun t : ℝ => Real.sqrt (1 + (a / t) ^ 2)) atBot (𝓝 (Real.sqrt 1)) :=
        Real.continuous_sqrt.continuousAt.tendsto.comp h1
      rw [Real.sqrt_one] at hs
      simpa only [mul_one] using hs.const_mul (a ^ 2)
    have hdiv : Tendsto (fun t : ℝ => (-1 : ℝ) / (a ^ 2 * Real.sqrt (1 + (a / t) ^ 2)))
        atBot (𝓝 ((-1 : ℝ) / a ^ 2)) :=
      tendsto_const_nhds.div h2 (ne_of_gt (sq_pos_of_pos ha))
    rwa [neg_div] at hdiv
  have hbot : Tendsto F atBot (𝓝 (-(1 / a ^ 2))) := by
    refine hbot_lim.congr' ?_
    filter_upwards [Filter.eventually_lt_atBot (0 : ℝ)] with t ht
    have hfac : t ^ 2 + a ^ 2 = (-t) ^ 2 * (1 + (a / t) ^ 2) := by
      have ht0 : t ≠ 0 := ne_of_lt ht; field_simp
    have hsq : Real.sqrt (t ^ 2 + a ^ 2) = (-t) * Real.sqrt (1 + (a / t) ^ 2) := by
      rw [hfac, Real.sqrt_mul (sq_nonneg (-t)), Real.sqrt_sq (by linarith)]
    dsimp only [F]; rw [hsq]
    have ht0 : t ≠ 0 := ne_of_lt ht
    have h1 : Real.sqrt (1 + (a / t) ^ 2) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (by positivity))
    field_simp
  rw [integral_real_of_hasDerivAt_of_tendsto hderiv (integrable_inv_sqrt_cube ha) htop hbot]
  ring

/-- Integrability of `((t² + a²)²)⁻¹` on `ℝ` for any `a > 0`. -/
lemma integrable_inv_sq_add_sq_sq {a : ℝ} (ha : 0 < a) :
    Integrable (fun t : ℝ => ((t ^ 2 + a ^ 2) ^ 2)⁻¹) volume := by
  have hdom : Integrable (fun t : ℝ => (a ^ 2)⁻¹ * (t ^ 2 + a ^ 2)⁻¹) volume :=
    (integrable_inv_sq_add_sq ha).const_mul (a ^ 2)⁻¹
  have hcont : Continuous (fun t : ℝ => ((t ^ 2 + a ^ 2) ^ 2)⁻¹) :=
    (((continuous_id.pow 2).add continuous_const).pow 2).inv₀
      (fun t => ne_of_gt (pow_pos (add_pos_of_nonneg_of_pos (sq_nonneg t) (sq_pos_of_pos ha)) 2))
  refine hdom.mono' hcont.aestronglyMeasurable (Filter.Eventually.of_forall fun t => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have hle : a ^ 2 * (t ^ 2 + a ^ 2) ≤ (t ^ 2 + a ^ 2) ^ 2 := by nlinarith [sq_nonneg t]
  have hinv := inv_anti₀ (by positivity : 0 < a ^ 2 * (t ^ 2 + a ^ 2)) hle
  rwa [mul_inv] at hinv

/-- Exact 1D integral #3: `∫_ℝ ((t² + a²)²)⁻¹ dt = π / (2 a³)`. -/
lemma integral_inv_sq_add_sq_sq {a : ℝ} (ha : 0 < a) :
    (∫ t : ℝ, ((t ^ 2 + a ^ 2) ^ 2)⁻¹) = Real.pi / (2 * a ^ 3) := by
  have ha_ne : a ≠ 0 := ne_of_gt ha
  let F : ℝ → ℝ := fun t => t / (2 * a ^ 2 * (t ^ 2 + a ^ 2)) + (1 / (2 * a ^ 3)) * Real.arctan (t / a)
  have hderiv : ∀ t : ℝ, HasDerivAt F (((t ^ 2 + a ^ 2) ^ 2)⁻¹) t := fun t => by
    have hq : HasDerivAt (fun s : ℝ => 2 * a ^ 2 * (s ^ 2 + a ^ 2)) (2 * a ^ 2 * (2 * t)) t := by
      simpa using ((hasDerivAt_pow 2 t).add_const (a ^ 2)).const_mul (2 * a ^ 2)
    have h1 : HasDerivAt (fun s : ℝ => s / (2 * a ^ 2 * (s ^ 2 + a ^ 2)))
        ((1 * (2 * a ^ 2 * (t ^ 2 + a ^ 2)) - t * (2 * a ^ 2 * (2 * t))) /
          (2 * a ^ 2 * (t ^ 2 + a ^ 2)) ^ 2) t :=
      (hasDerivAt_id t).div hq (by positivity)
    have hdiv : HasDerivAt (fun s : ℝ => s / a) (1 / a) t := (hasDerivAt_id t).div_const a
    have h2 : HasDerivAt (fun s : ℝ => (1 / (2 * a ^ 3)) * Real.arctan (s / a))
        ((1 / (2 * a ^ 3)) * (1 / (1 + (t / a) ^ 2) * (1 / a))) t :=
      ((Real.hasDerivAt_arctan (t / a)).comp t hdiv).const_mul (1 / (2 * a ^ 3))
    have hsum : HasDerivAt F
        ((1 * (2 * a ^ 2 * (t ^ 2 + a ^ 2)) - t * (2 * a ^ 2 * (2 * t))) /
          (2 * a ^ 2 * (t ^ 2 + a ^ 2)) ^ 2 +
          (1 / (2 * a ^ 3)) * (1 / (1 + (t / a) ^ 2) * (1 / a))) t := h1.add h2
    have heq : (1 * (2 * a ^ 2 * (t ^ 2 + a ^ 2)) - t * (2 * a ^ 2 * (2 * t))) /
        (2 * a ^ 2 * (t ^ 2 + a ^ 2)) ^ 2 +
        (1 / (2 * a ^ 3)) * (1 / (1 + (t / a) ^ 2) * (1 / a)) = ((t ^ 2 + a ^ 2) ^ 2)⁻¹ := by
      have hpos : t ^ 2 + a ^ 2 ≠ 0 := ne_of_gt (add_pos_of_nonneg_of_pos (sq_nonneg t) (sq_pos_of_pos ha))
      have h1n : 1 + (t / a) ^ 2 ≠ 0 := ne_of_gt (add_pos_of_pos_of_nonneg zero_lt_one (sq_nonneg _))
      field_simp; ring
    rwa [heq] at hsum
  have hterm_top : Tendsto (fun t : ℝ => t / (2 * a ^ 2 * (t ^ 2 + a ^ 2))) atTop (𝓝 0) := by
    have h0 : Tendsto (fun t : ℝ => (1 : ℝ) / t) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop tendsto_id
    have h0a : Tendsto (fun t : ℝ => a / t) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop tendsto_id
    have hden : Tendsto (fun t : ℝ => 2 * a ^ 2 * (1 + (a / t) ^ 2)) atTop (𝓝 (2 * a ^ 2)) := by
      simpa using ((h0a.pow 2).const_add (1 : ℝ)).const_mul (2 * a ^ 2)
    have hlim : Tendsto (fun t : ℝ => ((1 : ℝ) / t) / (2 * a ^ 2 * (1 + (a / t) ^ 2))) atTop (𝓝 0) := by
      have h := h0.div hden (by positivity)
      rwa [zero_div] at h
    refine hlim.congr' ?_
    filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with t ht
    have ht0 : t ≠ 0 := ne_of_gt ht
    have hpos : t ^ 2 + a ^ 2 ≠ 0 := by positivity
    have h1n : 1 + (a / t) ^ 2 ≠ 0 := by positivity
    field_simp
  have hterm_bot : Tendsto (fun t : ℝ => t / (2 * a ^ 2 * (t ^ 2 + a ^ 2))) atBot (𝓝 0) := by
    have h0 : Tendsto (fun t : ℝ => (1 : ℝ) / t) atBot (𝓝 0) :=
      tendsto_const_nhds.div_atBot tendsto_id
    have h0a : Tendsto (fun t : ℝ => a / t) atBot (𝓝 0) :=
      tendsto_const_nhds.div_atBot tendsto_id
    have hden : Tendsto (fun t : ℝ => 2 * a ^ 2 * (1 + (a / t) ^ 2)) atBot (𝓝 (2 * a ^ 2)) := by
      simpa using ((h0a.pow 2).const_add (1 : ℝ)).const_mul (2 * a ^ 2)
    have hlim : Tendsto (fun t : ℝ => ((1 : ℝ) / t) / (2 * a ^ 2 * (1 + (a / t) ^ 2))) atBot (𝓝 0) := by
      have h := h0.div hden (by positivity)
      rwa [zero_div] at h
    refine hlim.congr' ?_
    filter_upwards [Filter.eventually_lt_atBot (0 : ℝ)] with t ht
    have ht0 : t ≠ 0 := ne_of_lt ht
    have hpos : t ^ 2 + a ^ 2 ≠ 0 := by positivity
    have h1n : 1 + (a / t) ^ 2 ≠ 0 := by positivity
    field_simp
  have htop : Tendsto F atTop (𝓝 (0 + (1 / (2 * a ^ 3)) * (Real.pi / 2))) :=
    hterm_top.add (((Real.tendsto_arctan_atTop.mono_right nhdsWithin_le_nhds).comp
      (Filter.Tendsto.atTop_div_const ha tendsto_id)).const_mul (1 / (2 * a ^ 3)))
  have hbot : Tendsto F atBot (𝓝 (0 + (1 / (2 * a ^ 3)) * (-(Real.pi / 2)))) :=
    hterm_bot.add (((Real.tendsto_arctan_atBot.mono_right nhdsWithin_le_nhds).comp
      (Filter.Tendsto.atBot_div_const ha tendsto_id)).const_mul (1 / (2 * a ^ 3)))
  rw [integral_real_of_hasDerivAt_of_tendsto hderiv (integrable_inv_sq_add_sq_sq ha) htop hbot]
  field_simp
  ring

/-- Integrability of `(√(t² + a²))⁻⁵` on `ℝ` for any `a > 0`. -/
lemma integrable_inv_sqrt_pow5 {a : ℝ} (ha : 0 < a) :
    Integrable (fun t : ℝ => ((Real.sqrt (t ^ 2 + a ^ 2)) ^ 5)⁻¹) volume := by
  have hdom : Integrable (fun t : ℝ => (a ^ 3)⁻¹ * (t ^ 2 + a ^ 2)⁻¹) volume :=
    (integrable_inv_sq_add_sq ha).const_mul (a ^ 3)⁻¹
  have hcont : Continuous (fun t : ℝ => ((Real.sqrt (t ^ 2 + a ^ 2)) ^ 5)⁻¹) :=
    ((Real.continuous_sqrt.comp ((continuous_id.pow 2).add continuous_const)).pow 5).inv₀
      (fun t => ne_of_gt (pow_pos (Real.sqrt_pos.mpr
        (add_pos_of_nonneg_of_pos (sq_nonneg t) (sq_pos_of_pos ha))) 5))
  refine hdom.mono' hcont.aestronglyMeasurable (Filter.Eventually.of_forall fun t => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have hsq : (Real.sqrt (t ^ 2 + a ^ 2)) ^ 2 = t ^ 2 + a ^ 2 := Real.sq_sqrt (by positivity)
  have hge : a ≤ Real.sqrt (t ^ 2 + a ^ 2) := by
    have := Real.sqrt_le_sqrt (show a ^ 2 ≤ t ^ 2 + a ^ 2 by nlinarith [sq_nonneg t])
    rwa [Real.sqrt_sq (le_of_lt ha)] at this
  have hge3 : a ^ 3 ≤ (Real.sqrt (t ^ 2 + a ^ 2)) ^ 3 := by
    have h2 : a ^ 2 ≤ (Real.sqrt (t ^ 2 + a ^ 2)) ^ 2 := by nlinarith
    nlinarith
  have hp5 : a ^ 3 * (t ^ 2 + a ^ 2) ≤ (Real.sqrt (t ^ 2 + a ^ 2)) ^ 5 := by
    calc a ^ 3 * (t ^ 2 + a ^ 2) ≤ (Real.sqrt (t ^ 2 + a ^ 2)) ^ 3 * (t ^ 2 + a ^ 2) :=
          mul_le_mul_of_nonneg_right hge3 (by positivity)
      _ = (Real.sqrt (t ^ 2 + a ^ 2)) ^ 3 * (Real.sqrt (t ^ 2 + a ^ 2)) ^ 2 := by rw [hsq]
      _ = (Real.sqrt (t ^ 2 + a ^ 2)) ^ 5 := by ring
  have hinv := inv_anti₀ (by positivity : 0 < a ^ 3 * (t ^ 2 + a ^ 2)) hp5
  rwa [mul_inv] at hinv

/-- Exact 1D integral #4: `∫_ℝ (√(t² + a²))⁻⁵ dt = 4 / (3 a⁴)`. -/
lemma integral_inv_sqrt_pow5 {a : ℝ} (ha : 0 < a) :
    (∫ t : ℝ, ((Real.sqrt (t ^ 2 + a ^ 2)) ^ 5)⁻¹) = 4 / (3 * a ^ 4) := by
  have ha_ne : a ≠ 0 := ne_of_gt ha
  let F : ℝ → ℝ := fun t =>
    t * (2 * t ^ 2 + 3 * a ^ 2) / (3 * a ^ 4 * (Real.sqrt (t ^ 2 + a ^ 2)) ^ 3)
  have hderiv : ∀ t : ℝ, HasDerivAt F (((Real.sqrt (t ^ 2 + a ^ 2)) ^ 5)⁻¹) t := fun t => by
    have hnum : HasDerivAt (fun s : ℝ => s * (2 * s ^ 2 + 3 * a ^ 2))
        (6 * t ^ 2 + 3 * a ^ 2) t := by
      have h1 : HasDerivAt (fun s : ℝ => 2 * s ^ 2 + 3 * a ^ 2) (4 * t) t := by
        have hp : HasDerivAt (fun s : ℝ => 2 * s ^ 2 + 3 * a ^ 2) (2 * ((2 : ℕ) * t ^ (2 - 1))) t :=
          ((hasDerivAt_pow 2 t).const_mul (2 : ℝ)).add_const (3 * a ^ 2)
        have heq1 : (2 : ℝ) * ((2 : ℕ) * t ^ (2 - 1)) = 4 * t := by norm_num; ring
        rwa [heq1] at hp
      have hm : HasDerivAt (fun s : ℝ => s * (2 * s ^ 2 + 3 * a ^ 2))
          (1 * (2 * t ^ 2 + 3 * a ^ 2) + t * (4 * t)) t := (hasDerivAt_id t).mul h1
      have heq2 : 1 * (2 * t ^ 2 + 3 * a ^ 2) + t * (4 * t) = 6 * t ^ 2 + 3 * a ^ 2 := by ring
      rwa [heq2] at hm
    have hq : HasDerivAt (fun s : ℝ => s ^ 2 + a ^ 2) (2 * t) t := by
      simpa using (hasDerivAt_pow 2 t).add_const (a ^ 2)
    have hsq_pos : 0 < Real.sqrt (t ^ 2 + a ^ 2) := Real.sqrt_pos.mpr (by positivity)
    have hsq_ne : Real.sqrt (t ^ 2 + a ^ 2) ≠ 0 := ne_of_gt hsq_pos
    have hsqrt : HasDerivAt (fun s : ℝ => Real.sqrt (s ^ 2 + a ^ 2))
        ((2 * t) / (2 * Real.sqrt (t ^ 2 + a ^ 2))) t := hq.sqrt (by positivity)
    have hcube : HasDerivAt (fun s : ℝ => (Real.sqrt (s ^ 2 + a ^ 2)) ^ 3)
        (3 * (Real.sqrt (t ^ 2 + a ^ 2)) ^ 2 * ((2 * t) / (2 * Real.sqrt (t ^ 2 + a ^ 2)))) t := by
      have h1 : HasDerivAt (fun x : ℝ => x ^ 3) (3 * (Real.sqrt (t ^ 2 + a ^ 2)) ^ 2)
          (Real.sqrt (t ^ 2 + a ^ 2)) := by
        simpa using hasDerivAt_pow 3 (Real.sqrt (t ^ 2 + a ^ 2))
      exact h1.comp t hsqrt
    have hden := hcube.const_mul (3 * a ^ 4)
    have hdiv : HasDerivAt F
        (((6 * t ^ 2 + 3 * a ^ 2) * (3 * a ^ 4 * (Real.sqrt (t ^ 2 + a ^ 2)) ^ 3) -
          t * (2 * t ^ 2 + 3 * a ^ 2) *
            (3 * a ^ 4 * (3 * (Real.sqrt (t ^ 2 + a ^ 2)) ^ 2 * ((2 * t) / (2 * Real.sqrt (t ^ 2 + a ^ 2)))))) /
          (3 * a ^ 4 * (Real.sqrt (t ^ 2 + a ^ 2)) ^ 3) ^ 2) t :=
      hnum.div hden (by positivity)
    have heq : ((6 * t ^ 2 + 3 * a ^ 2) * (3 * a ^ 4 * (Real.sqrt (t ^ 2 + a ^ 2)) ^ 3) -
        t * (2 * t ^ 2 + 3 * a ^ 2) *
          (3 * a ^ 4 * (3 * (Real.sqrt (t ^ 2 + a ^ 2)) ^ 2 * ((2 * t) / (2 * Real.sqrt (t ^ 2 + a ^ 2)))))) /
        (3 * a ^ 4 * (Real.sqrt (t ^ 2 + a ^ 2)) ^ 3) ^ 2 = ((Real.sqrt (t ^ 2 + a ^ 2)) ^ 5)⁻¹ := by
      set s := Real.sqrt (t ^ 2 + a ^ 2)
      have hs2 : s ^ 2 = t ^ 2 + a ^ 2 := Real.sq_sqrt (by positivity)
      have hnum_eq : (6 * t ^ 2 + 3 * a ^ 2) * (3 * a ^ 4 * s ^ 3) -
          t * (2 * t ^ 2 + 3 * a ^ 2) * (3 * a ^ 4 * (3 * s ^ 2 * ((2 * t) / (2 * s)))) =
          9 * a ^ 8 * s := by
        have hsimpl : 3 * s ^ 2 * ((2 * t) / (2 * s)) = 3 * s * t := by field_simp
        rw [hsimpl]
        calc (6 * t ^ 2 + 3 * a ^ 2) * (3 * a ^ 4 * s ^ 3) -
              t * (2 * t ^ 2 + 3 * a ^ 2) * (3 * a ^ 4 * (3 * s * t))
            = 3 * a ^ 4 * s * ((6 * t ^ 2 + 3 * a ^ 2) * s ^ 2 - 3 * t ^ 2 * (2 * t ^ 2 + 3 * a ^ 2)) := by ring
          _ = 3 * a ^ 4 * s * ((6 * t ^ 2 + 3 * a ^ 2) * (t ^ 2 + a ^ 2) - 3 * t ^ 2 * (2 * t ^ 2 + 3 * a ^ 2)) := by rw [hs2]
          _ = 9 * a ^ 8 * s := by ring
      rw [hnum_eq]
      field_simp
      ring
    rwa [heq] at hdiv
  have htop_lim : Tendsto
      (fun t : ℝ => (2 + 3 * (a / t) ^ 2) / (3 * a ^ 4 * (Real.sqrt (1 + (a / t) ^ 2)) ^ 3))
      atTop (𝓝 (2 / (3 * a ^ 4))) := by
    have h0 : Tendsto (fun t : ℝ => a / t) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop tendsto_id
    have hnum : Tendsto (fun t : ℝ => 2 + 3 * (a / t) ^ 2) atTop (𝓝 2) := by
      simpa using ((h0.pow 2).const_mul (3 : ℝ)).const_add (2 : ℝ)
    have h1 : Tendsto (fun t : ℝ => 1 + (a / t) ^ 2) atTop (𝓝 1) := by
      simpa using (h0.pow 2).const_add (1 : ℝ)
    have hden : Tendsto (fun t : ℝ => 3 * a ^ 4 * (Real.sqrt (1 + (a / t) ^ 2)) ^ 3)
        atTop (𝓝 (3 * a ^ 4)) := by
      simpa using ((Real.continuous_sqrt.continuousAt.tendsto.comp h1).pow 3).const_mul (3 * a ^ 4)
    exact hnum.div hden (by positivity)
  have htop : Tendsto F atTop (𝓝 (2 / (3 * a ^ 4))) := by
    refine htop_lim.congr' ?_
    filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with t ht
    have ht0 : t ≠ 0 := ne_of_gt ht
    have hfac : t ^ 2 + a ^ 2 = t ^ 2 * (1 + (a / t) ^ 2) := by field_simp
    have hsq : Real.sqrt (t ^ 2 + a ^ 2) = t * Real.sqrt (1 + (a / t) ^ 2) := by
      rw [hfac, Real.sqrt_mul (sq_nonneg t), Real.sqrt_sq (le_of_lt ht)]
    dsimp only [F]; rw [hsq]
    have h1 : Real.sqrt (1 + (a / t) ^ 2) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (by positivity))
    field_simp
  have hbot_lim : Tendsto
      (fun t : ℝ => -(2 + 3 * (a / t) ^ 2) / (3 * a ^ 4 * (Real.sqrt (1 + (a / t) ^ 2)) ^ 3))
      atBot (𝓝 (-(2 / (3 * a ^ 4)))) := by
    have h0 : Tendsto (fun t : ℝ => a / t) atBot (𝓝 0) :=
      tendsto_const_nhds.div_atBot tendsto_id
    have hnum : Tendsto (fun t : ℝ => -(2 + 3 * (a / t) ^ 2)) atBot (𝓝 (-2)) := by
      simpa using (((h0.pow 2).const_mul (3 : ℝ)).const_add (2 : ℝ)).neg
    have h1 : Tendsto (fun t : ℝ => 1 + (a / t) ^ 2) atBot (𝓝 1) := by
      simpa using (h0.pow 2).const_add (1 : ℝ)
    have hden : Tendsto (fun t : ℝ => 3 * a ^ 4 * (Real.sqrt (1 + (a / t) ^ 2)) ^ 3)
        atBot (𝓝 (3 * a ^ 4)) := by
      simpa using ((Real.continuous_sqrt.continuousAt.tendsto.comp h1).pow 3).const_mul (3 * a ^ 4)
    have hdiv : Tendsto (fun t : ℝ => -(2 + 3 * (a / t) ^ 2) / (3 * a ^ 4 * (Real.sqrt (1 + (a / t) ^ 2)) ^ 3))
        atBot (𝓝 ((-2 : ℝ) / (3 * a ^ 4))) := hnum.div hden (by positivity)
    rwa [neg_div] at hdiv
  have hbot : Tendsto F atBot (𝓝 (-(2 / (3 * a ^ 4)))) := by
    refine hbot_lim.congr' ?_
    filter_upwards [Filter.eventually_lt_atBot (0 : ℝ)] with t ht
    have ht0 : t ≠ 0 := ne_of_lt ht
    have hfac : t ^ 2 + a ^ 2 = (-t) ^ 2 * (1 + (a / t) ^ 2) := by field_simp
    have hsq : Real.sqrt (t ^ 2 + a ^ 2) = (-t) * Real.sqrt (1 + (a / t) ^ 2) := by
      rw [hfac, Real.sqrt_mul (sq_nonneg (-t)), Real.sqrt_sq (by linarith)]
    dsimp only [F]; rw [hsq]
    have h1 : Real.sqrt (1 + (a / t) ^ 2) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (by positivity))
    field_simp
  rw [integral_real_of_hasDerivAt_of_tendsto hderiv (integrable_inv_sqrt_pow5 ha) htop hbot]
  ring

-- ============================================================================
-- SECTION 2: EXACT 3D SMOOTH RADIAL KERNEL INTEGRALS ON ℝ³
-- ============================================================================

private noncomputable def r3ToTriple : R3 ≃ᵐ ℝ × (ℝ × ℝ) :=
  (MeasurableEquiv.piFinSuccAbove (fun _ : Fin 3 => ℝ) 0).trans
    (MeasurableEquiv.prodCongr (MeasurableEquiv.refl ℝ)
      (MeasurableEquiv.piFinTwo (fun _ : Fin 2 => ℝ)))

private lemma measurePreserving_r3ToTriple :
    MeasurePreserving r3ToTriple (volume : Measure R3)
      ((volume : Measure ℝ).prod ((volume : Measure ℝ).prod (volume : Measure ℝ))) := by
  have h1 : MeasurePreserving (MeasurableEquiv.piFinSuccAbove (fun _ : Fin 3 => ℝ) 0)
      (volume : Measure R3) ((volume : Measure ℝ).prod (volume : Measure (Fin 2 → ℝ))) :=
    MeasureTheory.measurePreserving_piFinSuccAbove (fun _ : Fin 3 => (volume : Measure ℝ)) 0
  have h2 : MeasurePreserving (MeasurableEquiv.piFinTwo (fun _ : Fin 2 => ℝ))
      (volume : Measure (Fin 2 → ℝ)) ((volume : Measure ℝ).prod (volume : Measure ℝ)) :=
    MeasureTheory.volume_preserving_piFinTwo (fun _ : Fin 2 => ℝ)
  exact ((MeasurePreserving.id (volume : Measure ℝ)).prod h2).comp h1

private lemma r3ToTriple_symm_sq_sum (x0 x1 x2 : ℝ) :
    (r3ToTriple.symm (x0, (x1, x2)) 0) ^ 2 +
    (r3ToTriple.symm (x0, (x1, x2)) 1) ^ 2 +
    (r3ToTriple.symm (x0, (x1, x2)) 2) ^ 2 = x0 ^ 2 + x1 ^ 2 + x2 ^ 2 := by
  have h0 : r3ToTriple.symm (x0, (x1, x2)) 0 = x0 := by
    change Fin.insertNth (α := fun _ : Fin 3 => ℝ) 0 x0
      ((MeasurableEquiv.piFinTwo (fun _ : Fin 2 => ℝ)).symm (x1, x2)) 0 = x0
    exact Fin.insertNth_apply_same (α := fun _ : Fin 3 => ℝ) 0 x0 _
  have h1 : r3ToTriple.symm (x0, (x1, x2)) 1 = x1 := by
    change Fin.insertNth (α := fun _ : Fin 3 => ℝ) 0 x0
      ((MeasurableEquiv.piFinTwo (fun _ : Fin 2 => ℝ)).symm (x1, x2)) ((0 : Fin 3).succAbove 0) = x1
    rw [Fin.insertNth_apply_succAbove]
    rfl
  have h2 : r3ToTriple.symm (x0, (x1, x2)) 2 = x2 := by
    change Fin.insertNth (α := fun _ : Fin 3 => ℝ) 0 x0
      ((MeasurableEquiv.piFinTwo (fun _ : Fin 2 => ℝ)).symm (x1, x2)) ((0 : Fin 3).succAbove 1) = x2
    rw [Fin.insertNth_apply_succAbove]
    rfl
  rw [h0, h1, h2]

private lemma integrable_and_integral_2d_inv_sqrt_cube {a : ℝ} (ha : 0 < a) :
    Integrable (fun p : ℝ × ℝ => ((Real.sqrt (p.1 ^ 2 + p.2 ^ 2 + a ^ 2)) ^ 3)⁻¹)
      ((volume : Measure ℝ).prod (volume : Measure ℝ)) ∧
    (∫ p : ℝ × ℝ, ((Real.sqrt (p.1 ^ 2 + p.2 ^ 2 + a ^ 2)) ^ 3)⁻¹
      ∂((volume : Measure ℝ).prod (volume : Measure ℝ))) = 2 * Real.pi / a := by
  have hcont : Continuous (fun p : ℝ × ℝ => ((Real.sqrt (p.1 ^ 2 + p.2 ^ 2 + a ^ 2)) ^ 3)⁻¹) :=
    ((Real.continuous_sqrt.comp (((continuous_fst.pow 2).add (continuous_snd.pow 2)).add
      continuous_const)).pow 3).inv₀
      (fun p => ne_of_gt (pow_pos (Real.sqrt_pos.mpr
        (add_pos_of_nonneg_of_pos (add_nonneg (sq_nonneg p.1) (sq_nonneg p.2)) (sq_pos_of_pos ha))) 3))
  have hslice : ∀ y2 : ℝ,
      Integrable (fun y1 : ℝ => ((Real.sqrt (y1 ^ 2 + y2 ^ 2 + a ^ 2)) ^ 3)⁻¹) volume ∧
      (∫ y1 : ℝ, ((Real.sqrt (y1 ^ 2 + y2 ^ 2 + a ^ 2)) ^ 3)⁻¹) = 2 / (y2 ^ 2 + a ^ 2) := by
    intro y2
    let b : ℝ := Real.sqrt (y2 ^ 2 + a ^ 2)
    have hb_pos : 0 < b := Real.sqrt_pos.mpr (by positivity)
    have hb2 : b ^ 2 = y2 ^ 2 + a ^ 2 := Real.sq_sqrt (by positivity)
    have heq : (fun y1 : ℝ => ((Real.sqrt (y1 ^ 2 + y2 ^ 2 + a ^ 2)) ^ 3)⁻¹) =
        fun y1 : ℝ => ((Real.sqrt (y1 ^ 2 + b ^ 2)) ^ 3)⁻¹ := by
      funext y1; congr 3; linarith
    rw [heq]
    exact ⟨integrable_inv_sqrt_cube hb_pos, by rw [integral_inv_sqrt_cube hb_pos, hb2]⟩
  have hint_prod : Integrable (fun p : ℝ × ℝ => ((Real.sqrt (p.1 ^ 2 + p.2 ^ 2 + a ^ 2)) ^ 3)⁻¹)
      ((volume : Measure ℝ).prod (volume : Measure ℝ)) := by
    rw [MeasureTheory.integrable_prod_iff' hcont.aestronglyMeasurable]
    refine ⟨Filter.Eventually.of_forall (fun y2 => (hslice y2).1), ?_⟩
    have hnorm : (fun y2 : ℝ => ∫ y1 : ℝ, ‖((Real.sqrt (y1 ^ 2 + y2 ^ 2 + a ^ 2)) ^ 3)⁻¹‖) =
        fun y2 : ℝ => 2 * (y2 ^ 2 + a ^ 2)⁻¹ := by
      funext y2
      have h1 : (fun y1 : ℝ => ‖((Real.sqrt (y1 ^ 2 + y2 ^ 2 + a ^ 2)) ^ 3)⁻¹‖) =
          fun y1 : ℝ => ((Real.sqrt (y1 ^ 2 + y2 ^ 2 + a ^ 2)) ^ 3)⁻¹ := by
        funext y1; rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      rw [h1, (hslice y2).2, div_eq_mul_inv]
    rw [hnorm]
    exact (integrable_inv_sq_add_sq ha).const_mul 2
  refine ⟨hint_prod, ?_⟩
  rw [MeasureTheory.integral_prod_symm _ hint_prod]
  have houter : (fun y2 : ℝ => ∫ y1 : ℝ, ((Real.sqrt (y1 ^ 2 + y2 ^ 2 + a ^ 2)) ^ 3)⁻¹) =
      fun y2 : ℝ => 2 * (y2 ^ 2 + a ^ 2)⁻¹ := by
    funext y2; rw [(hslice y2).2, div_eq_mul_inv]
  rw [houter, MeasureTheory.integral_const_mul, integral_inv_sq_add_sq ha]
  ring

/-- **Exact 3D Integral #1:** `(r3Rho a y)⁻⁴ = (|y|² + a²)⁻²` is integrable on `ℝ³` with
    exact integral `∫_{ℝ³} (|y|² + a²)⁻² dy = π² / a`. -/
theorem r3Integral_inv_rho_pow4 {a : ℝ} (ha : 0 < a) :
    Integrable (fun y : R3 => ((r3Rho a y) ^ 4)⁻¹) volume ∧
    r3Integral (fun y : R3 => ((r3Rho a y) ^ 4)⁻¹) = Real.pi ^ 2 / a := by
  let g : ℝ × (ℝ × ℝ) → ℝ := fun q => ((q.1 ^ 2 + q.2.1 ^ 2 + q.2.2 ^ 2 + a ^ 2) ^ 2)⁻¹
  have hcomp_eq : (fun q : ℝ × (ℝ × ℝ) => ((r3Rho a (r3ToTriple.symm q)) ^ 4)⁻¹) = g := by
    funext ⟨x0, x1, x2⟩
    dsimp only [g]
    have hr2 := r3Rho_sq a (r3ToTriple.symm (x0, (x1, x2)))
    have hsum := r3ToTriple_symm_sq_sum x0 x1 x2
    have hr4 : (r3Rho a (r3ToTriple.symm (x0, (x1, x2)))) ^ 4 =
        (x0 ^ 2 + x1 ^ 2 + x2 ^ 2 + a ^ 2) ^ 2 := by
      calc (r3Rho a (r3ToTriple.symm (x0, (x1, x2)))) ^ 4
          = ((r3Rho a (r3ToTriple.symm (x0, (x1, x2)))) ^ 2) ^ 2 := by ring
        _ = (x0 ^ 2 + x1 ^ 2 + x2 ^ 2 + a ^ 2) ^ 2 := by rw [hr2, hsum]
    rw [hr4]
  have hcont_g : Continuous g :=
    (((((continuous_fst.pow 2).add ((continuous_fst.comp continuous_snd).pow 2)).add
      ((continuous_snd.comp continuous_snd).pow 2)).add continuous_const).pow 2).inv₀
      (fun q => ne_of_gt (pow_pos (add_pos_of_nonneg_of_pos
        (add_nonneg (add_nonneg (sq_nonneg q.1) (sq_nonneg q.2.1)) (sq_nonneg q.2.2))
        (sq_pos_of_pos ha)) 2))
  have hslice : ∀ p : ℝ × ℝ,
      Integrable (fun x0 : ℝ => g (x0, p)) volume ∧
      (∫ x0 : ℝ, g (x0, p)) = (Real.pi / 2) * ((Real.sqrt (p.1 ^ 2 + p.2 ^ 2 + a ^ 2)) ^ 3)⁻¹ := by
    intro p
    let b : ℝ := Real.sqrt (p.1 ^ 2 + p.2 ^ 2 + a ^ 2)
    have hb_pos : 0 < b := Real.sqrt_pos.mpr (by positivity)
    have hb2 : b ^ 2 = p.1 ^ 2 + p.2 ^ 2 + a ^ 2 := Real.sq_sqrt (by positivity)
    have heq : (fun x0 : ℝ => g (x0, p)) = fun x0 : ℝ => ((x0 ^ 2 + b ^ 2) ^ 2)⁻¹ := by
      funext x0; dsimp only [g]; congr 2; linarith
    rw [heq]
    refine ⟨integrable_inv_sq_add_sq_sq hb_pos, ?_⟩
    rw [integral_inv_sq_add_sq_sq hb_pos]
    dsimp only [b]; ring
  have h2d := integrable_and_integral_2d_inv_sqrt_cube ha
  have hg_int : Integrable g
      ((volume : Measure ℝ).prod ((volume : Measure ℝ).prod (volume : Measure ℝ))) := by
    rw [MeasureTheory.integrable_prod_iff' hcont_g.aestronglyMeasurable]
    refine ⟨Filter.Eventually.of_forall (fun p => (hslice p).1), ?_⟩
    have hnorm : (fun p : ℝ × ℝ => ∫ x0 : ℝ, ‖g (x0, p)‖) =
        fun p : ℝ × ℝ => (Real.pi / 2) * ((Real.sqrt (p.1 ^ 2 + p.2 ^ 2 + a ^ 2)) ^ 3)⁻¹ := by
      funext p
      have h1 : (fun x0 : ℝ => ‖g (x0, p)‖) = fun x0 : ℝ => g (x0, p) := by
        funext x0; dsimp only [g]; rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      rw [h1, (hslice p).2]
    rw [hnorm]
    exact h2d.1.const_mul (Real.pi / 2)
  have hint_r3 : Integrable (fun y : R3 => ((r3Rho a y) ^ 4)⁻¹) volume := by
    have hmp := measurePreserving_r3ToTriple.symm
    rw [← hmp.integrable_comp_emb r3ToTriple.symm.measurableEmbedding]
    change Integrable (fun q : ℝ × (ℝ × ℝ) => ((r3Rho a (r3ToTriple.symm q)) ^ 4)⁻¹) _
    rwa [hcomp_eq]
  refine ⟨hint_r3, ?_⟩
  have hmp_int : ∫ q : ℝ × (ℝ × ℝ), ((r3Rho a (r3ToTriple.symm q)) ^ 4)⁻¹
      ∂((volume : Measure ℝ).prod ((volume : Measure ℝ).prod (volume : Measure ℝ))) =
      r3Integral (fun y : R3 => ((r3Rho a y) ^ 4)⁻¹) :=
    measurePreserving_r3ToTriple.symm.integral_comp' (fun y : R3 => ((r3Rho a y) ^ 4)⁻¹)
  rw [← hmp_int, hcomp_eq, MeasureTheory.integral_prod_symm _ hg_int]
  have houter : (fun p : ℝ × ℝ => ∫ x0 : ℝ, g (x0, p)) =
      fun p : ℝ × ℝ => (Real.pi / 2) * ((Real.sqrt (p.1 ^ 2 + p.2 ^ 2 + a ^ 2)) ^ 3)⁻¹ := by
    funext p; exact (hslice p).2
  rw [houter, MeasureTheory.integral_const_mul, h2d.2]
  ring

/-- **3D Integral Bound #2:** `(r3Rho a y)⁻⁶ = (|y|² + a²)⁻³` is integrable on `ℝ³` with
    `∫_{ℝ³} (|y|² + a²)⁻³ dy ≤ π² / a³`. -/
theorem r3Integral_inv_rho_pow6_le {a : ℝ} (ha : 0 < a) :
    Integrable (fun y : R3 => ((r3Rho a y) ^ 6)⁻¹) volume ∧
    r3Integral (fun y : R3 => ((r3Rho a y) ^ 6)⁻¹) ≤ Real.pi ^ 2 / a ^ 3 := by
  have h4 := r3Integral_inv_rho_pow4 ha
  have hcont : Continuous (fun y : R3 => ((r3Rho a y) ^ 6)⁻¹) :=
    ((r3Rho_continuous a).pow 6).inv₀ (fun y => ne_of_gt (pow_pos (r3Rho_pos ha y) 6))
  have hpt : ∀ y : R3, ((r3Rho a y) ^ 6)⁻¹ ≤ (a ^ 2)⁻¹ * ((r3Rho a y) ^ 4)⁻¹ := fun y => by
    have hge : a ^ 2 ≤ (r3Rho a y) ^ 2 := by
      rw [r3Rho_sq]; nlinarith [sq_nonneg (y 0), sq_nonneg (y 1), sq_nonneg (y 2)]
    have h6 : a ^ 2 * (r3Rho a y) ^ 4 ≤ (r3Rho a y) ^ 6 := by
      have h4p : 0 ≤ (r3Rho a y) ^ 4 := by positivity
      calc a ^ 2 * (r3Rho a y) ^ 4 ≤ (r3Rho a y) ^ 2 * (r3Rho a y) ^ 4 :=
            mul_le_mul_of_nonneg_right hge h4p
        _ = (r3Rho a y) ^ 6 := by ring
    have hinv := inv_anti₀ (mul_pos (sq_pos_of_pos ha) (pow_pos (r3Rho_pos ha y) 4)) h6
    rwa [mul_inv] at hinv
  have hint : Integrable (fun y : R3 => ((r3Rho a y) ^ 6)⁻¹) volume := by
    refine (h4.1.const_mul (a ^ 2)⁻¹).mono' hcont.aestronglyMeasurable
      (Filter.Eventually.of_forall fun y => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact hpt y
  refine ⟨hint, ?_⟩
  have hmono : r3Integral (fun y : R3 => ((r3Rho a y) ^ 6)⁻¹) ≤
      r3Integral (fun y : R3 => (a ^ 2)⁻¹ * ((r3Rho a y) ^ 4)⁻¹) :=
    MeasureTheory.integral_mono hint (h4.1.const_mul (a ^ 2)⁻¹) hpt
  rw [r3Integral_const_mul, h4.2] at hmono
  have heq : (a ^ 2)⁻¹ * (Real.pi ^ 2 / a) = Real.pi ^ 2 / a ^ 3 := by
    have ha0 : a ≠ 0 := ne_of_gt ha; field_simp
  linarith

private lemma integrable_and_integral_2d_inv_sq_sq {a : ℝ} (ha : 0 < a) :
    Integrable (fun p : ℝ × ℝ => ((p.1 ^ 2 + p.2 ^ 2 + a ^ 2) ^ 2)⁻¹)
      ((volume : Measure ℝ).prod (volume : Measure ℝ)) ∧
    (∫ p : ℝ × ℝ, ((p.1 ^ 2 + p.2 ^ 2 + a ^ 2) ^ 2)⁻¹
      ∂((volume : Measure ℝ).prod (volume : Measure ℝ))) = Real.pi / a ^ 2 := by
  have hcont : Continuous (fun p : ℝ × ℝ => ((p.1 ^ 2 + p.2 ^ 2 + a ^ 2) ^ 2)⁻¹) :=
    ((((continuous_fst.pow 2).add (continuous_snd.pow 2)).add continuous_const).pow 2).inv₀
      (fun p => ne_of_gt (pow_pos (add_pos_of_nonneg_of_pos
        (add_nonneg (sq_nonneg p.1) (sq_nonneg p.2)) (sq_pos_of_pos ha)) 2))
  have hslice : ∀ y2 : ℝ,
      Integrable (fun y1 : ℝ => ((y1 ^ 2 + y2 ^ 2 + a ^ 2) ^ 2)⁻¹) volume ∧
      (∫ y1 : ℝ, ((y1 ^ 2 + y2 ^ 2 + a ^ 2) ^ 2)⁻¹) =
        (Real.pi / 2) * ((Real.sqrt (y2 ^ 2 + a ^ 2)) ^ 3)⁻¹ := by
    intro y2
    let b : ℝ := Real.sqrt (y2 ^ 2 + a ^ 2)
    have hb_pos : 0 < b := Real.sqrt_pos.mpr (by positivity)
    have hb2 : b ^ 2 = y2 ^ 2 + a ^ 2 := Real.sq_sqrt (by positivity)
    have heq : (fun y1 : ℝ => ((y1 ^ 2 + y2 ^ 2 + a ^ 2) ^ 2)⁻¹) =
        fun y1 : ℝ => ((y1 ^ 2 + b ^ 2) ^ 2)⁻¹ := by
      funext y1; congr 2; linarith
    rw [heq]
    refine ⟨integrable_inv_sq_add_sq_sq hb_pos, ?_⟩
    rw [integral_inv_sq_add_sq_sq hb_pos]
    dsimp only [b]; ring
  have hint_prod : Integrable (fun p : ℝ × ℝ => ((p.1 ^ 2 + p.2 ^ 2 + a ^ 2) ^ 2)⁻¹)
      ((volume : Measure ℝ).prod (volume : Measure ℝ)) := by
    rw [MeasureTheory.integrable_prod_iff' hcont.aestronglyMeasurable]
    refine ⟨Filter.Eventually.of_forall (fun y2 => (hslice y2).1), ?_⟩
    have hnorm : (fun y2 : ℝ => ∫ y1 : ℝ, ‖((y1 ^ 2 + y2 ^ 2 + a ^ 2) ^ 2)⁻¹‖) =
        fun y2 : ℝ => (Real.pi / 2) * ((Real.sqrt (y2 ^ 2 + a ^ 2)) ^ 3)⁻¹ := by
      funext y2
      have h1 : (fun y1 : ℝ => ‖((y1 ^ 2 + y2 ^ 2 + a ^ 2) ^ 2)⁻¹‖) =
          fun y1 : ℝ => ((y1 ^ 2 + y2 ^ 2 + a ^ 2) ^ 2)⁻¹ := by
        funext y1; rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      rw [h1, (hslice y2).2]
    rw [hnorm]
    exact (integrable_inv_sqrt_cube ha).const_mul (Real.pi / 2)
  refine ⟨hint_prod, ?_⟩
  rw [MeasureTheory.integral_prod_symm _ hint_prod]
  have houter : (fun y2 : ℝ => ∫ y1 : ℝ, ((y1 ^ 2 + y2 ^ 2 + a ^ 2) ^ 2)⁻¹) =
      fun y2 : ℝ => (Real.pi / 2) * ((Real.sqrt (y2 ^ 2 + a ^ 2)) ^ 3)⁻¹ := by
    funext y2; exact (hslice y2).2
  rw [houter, MeasureTheory.integral_const_mul, integral_inv_sqrt_cube ha]
  ring

/-- **Exact 3D Integral #3 (Smooth 3D Poisson Kernel Mass):**
    `3 a² (r3Rho a y)⁻⁵` is integrable on `ℝ³` with exact total mass `4π` for every `a > 0`. -/
theorem r3Integral_poisson_kernel_eq {a : ℝ} (ha : 0 < a) :
    Integrable (fun y : R3 => 3 * a ^ 2 * ((r3Rho a y) ^ 5)⁻¹) volume ∧
    r3Integral (fun y : R3 => 3 * a ^ 2 * ((r3Rho a y) ^ 5)⁻¹) = 4 * Real.pi := by
  let g : ℝ × (ℝ × ℝ) → ℝ := fun q => ((Real.sqrt (q.1 ^ 2 + q.2.1 ^ 2 + q.2.2 ^ 2 + a ^ 2)) ^ 5)⁻¹
  have hcomp_eq : (fun q : ℝ × (ℝ × ℝ) => ((r3Rho a (r3ToTriple.symm q)) ^ 5)⁻¹) = g := by
    funext ⟨x0, x1, x2⟩
    dsimp only [g, r3Rho]
    rw [r3ToTriple_symm_sq_sum]
  have hcont_g : Continuous g :=
    ((Real.continuous_sqrt.comp
      ((((continuous_fst.pow 2).add ((continuous_fst.comp continuous_snd).pow 2)).add
        ((continuous_snd.comp continuous_snd).pow 2)).add continuous_const)).pow 5).inv₀
      (fun q => ne_of_gt (pow_pos (Real.sqrt_pos.mpr (add_pos_of_nonneg_of_pos
        (add_nonneg (add_nonneg (sq_nonneg q.1) (sq_nonneg q.2.1)) (sq_nonneg q.2.2))
        (sq_pos_of_pos ha))) 5))
  have hslice : ∀ p : ℝ × ℝ,
      Integrable (fun x0 : ℝ => g (x0, p)) volume ∧
      (∫ x0 : ℝ, g (x0, p)) = (4 / 3 : ℝ) * ((p.1 ^ 2 + p.2 ^ 2 + a ^ 2) ^ 2)⁻¹ := by
    intro p
    let b : ℝ := Real.sqrt (p.1 ^ 2 + p.2 ^ 2 + a ^ 2)
    have hb_pos : 0 < b := Real.sqrt_pos.mpr (by positivity)
    have hb2 : b ^ 2 = p.1 ^ 2 + p.2 ^ 2 + a ^ 2 := Real.sq_sqrt (by positivity)
    have hb4 : b ^ 4 = (p.1 ^ 2 + p.2 ^ 2 + a ^ 2) ^ 2 := by
      calc b ^ 4 = (b ^ 2) ^ 2 := by ring
        _ = (p.1 ^ 2 + p.2 ^ 2 + a ^ 2) ^ 2 := by rw [hb2]
    have heq : (fun x0 : ℝ => g (x0, p)) = fun x0 : ℝ => ((Real.sqrt (x0 ^ 2 + b ^ 2)) ^ 5)⁻¹ := by
      funext x0; dsimp only [g]
      have harg : x0 ^ 2 + p.1 ^ 2 + p.2 ^ 2 + a ^ 2 = x0 ^ 2 + b ^ 2 := by linarith
      rw [harg]
    rw [heq]
    refine ⟨integrable_inv_sqrt_pow5 hb_pos, ?_⟩
    rw [integral_inv_sqrt_pow5 hb_pos, hb4, div_eq_mul_inv, mul_inv]
    ring
  have h2d := integrable_and_integral_2d_inv_sq_sq ha
  have hg_int : Integrable g
      ((volume : Measure ℝ).prod ((volume : Measure ℝ).prod (volume : Measure ℝ))) := by
    rw [MeasureTheory.integrable_prod_iff' hcont_g.aestronglyMeasurable]
    refine ⟨Filter.Eventually.of_forall (fun p => (hslice p).1), ?_⟩
    have hnorm : (fun p : ℝ × ℝ => ∫ x0 : ℝ, ‖g (x0, p)‖) =
        fun p : ℝ × ℝ => (4 / 3 : ℝ) * ((p.1 ^ 2 + p.2 ^ 2 + a ^ 2) ^ 2)⁻¹ := by
      funext p
      have h1 : (fun x0 : ℝ => ‖g (x0, p)‖) = fun x0 : ℝ => g (x0, p) := by
        funext x0; dsimp only [g]; rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      rw [h1, (hslice p).2]
    rw [hnorm]
    exact h2d.1.const_mul (4 / 3)
  have hint_raw : Integrable (fun y : R3 => ((r3Rho a y) ^ 5)⁻¹) volume := by
    have hmp := measurePreserving_r3ToTriple.symm
    rw [← hmp.integrable_comp_emb r3ToTriple.symm.measurableEmbedding]
    change Integrable (fun q : ℝ × (ℝ × ℝ) => ((r3Rho a (r3ToTriple.symm q)) ^ 5)⁻¹) _
    rwa [hcomp_eq]
  refine ⟨hint_raw.const_mul (3 * a ^ 2), ?_⟩
  rw [r3Integral_const_mul]
  have hmp_int : ∫ q : ℝ × (ℝ × ℝ), ((r3Rho a (r3ToTriple.symm q)) ^ 5)⁻¹
      ∂((volume : Measure ℝ).prod ((volume : Measure ℝ).prod (volume : Measure ℝ))) =
      r3Integral (fun y : R3 => ((r3Rho a y) ^ 5)⁻¹) :=
    measurePreserving_r3ToTriple.symm.integral_comp' (fun y : R3 => ((r3Rho a y) ^ 5)⁻¹)
  rw [← hmp_int, hcomp_eq, MeasureTheory.integral_prod_symm _ hg_int]
  have houter : (fun p : ℝ × ℝ => ∫ x0 : ℝ, g (x0, p)) =
      fun p : ℝ × ℝ => (4 / 3 : ℝ) * ((p.1 ^ 2 + p.2 ^ 2 + a ^ 2) ^ 2)⁻¹ := by
    funext p; exact (hslice p).2
  rw [houter, MeasureTheory.integral_const_mul, h2d.2]
  have ha0 : a ≠ 0 := ne_of_gt ha
  field_simp

  -- ============================================================================
-- SECTION 3: KERNEL DERIVATIVES, L² BOUND ON ψ_{ε,R} & TWO-KERNEL GREEN IDENTITY
-- ============================================================================

private lemma int_add_ag {f g : R3 → ℝ} (hf : Integrable f volume) (hg : Integrable g volume) :
    Integrable (fun x => f x + g x) volume := hf.add hg

private lemma int_const_mul_ag (c : ℝ) {f : R3 → ℝ} (hf : Integrable f volume) :
    Integrable (fun x => c * f x) volume := hf.const_mul c

private lemma curl3D_zero_ag (u : R3 → R3) (x : R3) :
    curl3D u x 0 = partialDerivScalar (fun y => u y 2) x 1 -
      partialDerivScalar (fun y => u y 1) x 2 := rfl

private lemma curl3D_one_ag (u : R3 → R3) (x : R3) :
    curl3D u x 1 = partialDerivScalar (fun y => u y 0) x 2 -
      partialDerivScalar (fun y => u y 2) x 0 := rfl

private lemma curl3D_two_ag (u : R3 → R3) (x : R3) :
    curl3D u x 2 = partialDerivScalar (fun y => u y 1) x 0 -
      partialDerivScalar (fun y => u y 0) x 1 := rfl

private lemma vanishesAtInfinityR3_of_bdd_mul {h f : R3 → ℝ}
    (hbdd : ∃ C : ℝ, 0 ≤ C ∧ ∀ x : R3, |h x| ≤ C)
    (hvan : VanishesAtInfinityR3 f) :
    VanishesAtInfinityR3 (fun x => h x * f x) := by
  obtain ⟨C, hC_nn, hC⟩ := hbdd
  unfold VanishesAtInfinityR3 at *
  rw [Metric.tendsto_nhds] at hvan ⊢
  intro ε hε
  have hε' : 0 < ε / (C + 1) := div_pos hε (by linarith)
  filter_upwards [hvan (ε / (C + 1)) hε'] with x hx
  simp only [Real.dist_eq, sub_zero] at hx ⊢
  rw [abs_mul]
  have h1 : |h x| * |f x| ≤ C * |f x| := mul_le_mul_of_nonneg_right (hC x) (abs_nonneg _)
  have h2 : C * |f x| ≤ C * (ε / (C + 1)) := mul_le_mul_of_nonneg_left (le_of_lt hx) hC_nn
  have h3 : C * (ε / (C + 1)) < ε := by
    have hpos : 0 < C + 1 := by linarith
    calc C * (ε / (C + 1)) = (C / (C + 1)) * ε := by ring
      _ < 1 * ε := mul_lt_mul_of_pos_right ((div_lt_one hpos).mpr (by linarith)) hε
      _ = ε := one_mul ε
  linarith

private lemma contDiff_partial_c2_ag {g : R3 → ℝ} (hg : ContDiff ℝ 3 g) (i : Fin 3) :
    ContDiff ℝ 2 (fun x => partialDerivScalar g x i) := by
  unfold partialDerivScalar
  have hfd : ContDiff ℝ 2 (fderiv ℝ g) := hg.fderiv_right (by norm_cast)
  exact hfd.clm_apply contDiff_const

private lemma contDiff_snd_c1_ag {g : R3 → ℝ} (hg : ContDiff ℝ 3 g) (i j : Fin 3) :
    ContDiff ℝ 1 (fun x => sndPartial g x i j) := by
  have h2 : ContDiff ℝ 2 g := hg.of_le (by exact_mod_cast (show (2 : ℕ) ≤ 3 by decide))
  have heq : (fun x => sndPartial g x i j) =
      fun x => partialDerivScalar (fun y => partialDerivScalar g y j) x i := by
    funext x; exact (partial_partial_eq_sndPartial g x h2.contDiffAt i j).symm
  rw [heq]
  unfold partialDerivScalar
  have h1 : ContDiff ℝ 2 (fun y => partialDerivScalar g y j) := contDiff_partial_c2_ag hg j
  have hfd : ContDiff ℝ 1 (fderiv ℝ (fun y => partialDerivScalar g y j)) :=
    h1.fderiv_right (by norm_cast)
  exact hfd.clm_apply contDiff_const

private lemma norm_sq_le_sum_sq_r3 (y : R3) :
    ‖y‖ ^ 2 ≤ (y 0) ^ 2 + (y 1) ^ 2 + (y 2) ^ 2 := by
  have hsum_nn : 0 ≤ (y 0) ^ 2 + (y 1) ^ 2 + (y 2) ^ 2 := by positivity
  have hle : ‖y‖ ≤ Real.sqrt ((y 0) ^ 2 + (y 1) ^ 2 + (y 2) ^ 2) := by
    rw [pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)]
    intro i
    rw [Real.norm_eq_abs, ← Real.sqrt_sq_eq_abs]
    apply Real.sqrt_le_sqrt
    fin_cases i
    · change (y 0) ^ 2 ≤ _; nlinarith [sq_nonneg (y 1), sq_nonneg (y 2)]
    · change (y 1) ^ 2 ≤ _; nlinarith [sq_nonneg (y 0), sq_nonneg (y 2)]
    · change (y 2) ^ 2 ≤ _; nlinarith [sq_nonneg (y 0), sq_nonneg (y 1)]
  have hsq : ‖y‖ ^ 2 ≤ (Real.sqrt ((y 0) ^ 2 + (y 1) ^ 2 + (y 2) ^ 2)) ^ 2 := by
    nlinarith [norm_nonneg y, Real.sqrt_nonneg ((y 0) ^ 2 + (y 1) ^ 2 + (y 2) ^ 2)]
  rwa [Real.sq_sqrt hsum_nn] at hsq

private noncomputable def r3Proj (j : Fin 3) : R3 →L[ℝ] ℝ :=
  ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 3 => ℝ) j

private noncomputable def r3GradSqCLM (y : R3) : R3 →L[ℝ] ℝ :=
  (2 * y 0) • r3Proj 0 + (2 * y 1) • r3Proj 1 + (2 * y 2) • r3Proj 2

private lemma r3Proj_basisVec_eval (i j : Fin 3) :
    r3Proj j (basisVec i) = if j = i then 1 else 0 := by
  change (Pi.single i (1 : ℝ) : R3) j = if j = i then 1 else 0
  rw [Pi.single_apply]

private lemma hasFDerivAt_comp_real {g : ℝ → ℝ} {f : R3 → ℝ} {g' : ℝ} {f' : R3 →L[ℝ] ℝ} {y : R3}
    (hg : HasDerivAt g g' (f y)) (hf : HasFDerivAt f f' y) :
    HasFDerivAt (fun z => g (f z)) (g' • f') y := by
  have h := hg.hasFDerivAt.comp y hf
  have heq : (ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) g').comp f' = g' • f' := by
    ext v
    simp [mul_comm]
  exact heq ▸ h

private lemma hasFDerivAt_r3Rho {a : ℝ} (ha : 0 < a) (y : R3) :
    HasFDerivAt (r3Rho a) ((2 * r3Rho a y)⁻¹ • r3GradSqCLM y) y := by
  have hp : ∀ j : Fin 3, HasFDerivAt (fun z : R3 => z j) (r3Proj j) y := fun j =>
    (r3Proj j).hasFDerivAt
  have hsq : ∀ j : Fin 3, HasFDerivAt (fun z : R3 => (z j) ^ 2) ((2 * y j) • r3Proj j) y := fun j => by
    have hd : HasDerivAt (fun s : ℝ => s ^ 2) (2 * y j) (y j) := by
      simpa using hasDerivAt_pow 2 (y j)
    exact hasFDerivAt_comp_real hd (hp j)
  have hq01 : HasFDerivAt (fun z : R3 => (z 0) ^ 2 + (z 1) ^ 2)
      ((2 * y 0) • r3Proj 0 + (2 * y 1) • r3Proj 1) y := (hsq 0).add (hsq 1)
  have hq012 : HasFDerivAt (fun z : R3 => (z 0) ^ 2 + (z 1) ^ 2 + (z 2) ^ 2)
      (r3GradSqCLM y) y := hq01.add (hsq 2)
  have hq : HasFDerivAt (fun z : R3 => (z 0) ^ 2 + (z 1) ^ 2 + (z 2) ^ 2 + a ^ 2)
      (r3GradSqCLM y) y := by
    have h1 : HasFDerivAt (fun z : R3 => (z 0) ^ 2 + (z 1) ^ 2 + (z 2) ^ 2 + a ^ 2)
        (r3GradSqCLM y + 0) y := hq012.add (hasFDerivAt_const (𝕜 := ℝ) (a ^ 2) y)
    rwa [add_zero] at h1
  have hq_ne : (y 0) ^ 2 + (y 1) ^ 2 + (y 2) ^ 2 + a ^ 2 ≠ 0 := by positivity
  have hsqrt : HasDerivAt Real.sqrt ((2 * r3Rho a y)⁻¹)
      ((y 0) ^ 2 + (y 1) ^ 2 + (y 2) ^ 2 + a ^ 2) := by
    simpa only [one_div, r3Rho] using Real.hasDerivAt_sqrt hq_ne
  exact hasFDerivAt_comp_real hsqrt hq

/-- First spatial derivatives of the smooth regularized Newtonian kernel `r3Phi a`. -/
lemma r3Phi_differentiable_and_partial {a : ℝ} (ha : 0 < a) :
    Differentiable ℝ (r3Phi a) ∧
    ∀ (y : R3) (i : Fin 3),
      partialDerivScalar (r3Phi a) y i = -y i * ((r3Rho a y) ^ 3)⁻¹ := by
  have hfd : ∀ y : R3,
      HasFDerivAt (r3Phi a) ((-(r3Rho a y ^ 2)⁻¹) • ((2 * r3Rho a y)⁻¹ • r3GradSqCLM y)) y := fun y =>
    hasFDerivAt_comp_real (hasDerivAt_inv (ne_of_gt (r3Rho_pos ha y))) (hasFDerivAt_r3Rho ha y)
  refine ⟨fun y => (hfd y).differentiableAt, fun y i => ?_⟩
  unfold partialDerivScalar
  rw [(hfd y).fderiv]
  simp only [r3GradSqCLM, smul_apply, add_apply, smul_eq_mul, r3Proj_basisVec_eval]
  have hρ_ne : r3Rho a y ≠ 0 := ne_of_gt (r3Rho_pos ha y)
  fin_cases i <;> simp <;> field_simp

/-- Second diagonal spatial derivatives of `r3Phi a` and its exact smooth Laplacian `-3 a² ρ_a⁻⁵`. -/
lemma r3Phi_partial_differentiable_and_laplacian {a : ℝ} (ha : 0 < a) :
    (∀ i : Fin 3, Differentiable ℝ (fun y : R3 => partialDerivScalar (r3Phi a) y i)) ∧
    (∀ (y : R3) (i : Fin 3),
      partialDerivScalar (fun z => partialDerivScalar (r3Phi a) z i) y i =
        -((r3Rho a y) ^ 3)⁻¹ + 3 * (y i) ^ 2 * ((r3Rho a y) ^ 5)⁻¹) ∧
    (∀ y : R3,
      partialDerivScalar (fun z => partialDerivScalar (r3Phi a) z 0) y 0 +
      partialDerivScalar (fun z => partialDerivScalar (r3Phi a) z 1) y 1 +
      partialDerivScalar (fun z => partialDerivScalar (r3Phi a) z 2) y 2 =
        -(3 * a ^ 2 * ((r3Rho a y) ^ 5)⁻¹)) := by
  have hp1 := (r3Phi_differentiable_and_partial ha).2
  have hfd2 : ∀ (i : Fin 3) (y : R3),
      let Lrho : R3 →L[ℝ] ℝ := (2 * r3Rho a y)⁻¹ • r3GradSqCLM y
      HasFDerivAt (fun z : R3 => -z i * ((r3Rho a z) ^ 3)⁻¹)
        ((-y i) • ((-(((r3Rho a y) ^ 3) ^ 2)⁻¹) • ((3 * (r3Rho a y) ^ 2) • Lrho)) +
          (((r3Rho a y) ^ 3)⁻¹) • (-(r3Proj i))) y := by
    intro i y Lrho
    have hneg : HasFDerivAt (fun z : R3 => -z i) (-(r3Proj i)) y := (r3Proj i).hasFDerivAt.neg
    have hrho : HasFDerivAt (r3Rho a) Lrho y := hasFDerivAt_r3Rho ha y
    have hpow3 : HasFDerivAt (fun z : R3 => (r3Rho a z) ^ 3)
        ((3 * (r3Rho a y) ^ 2) • Lrho) y := by
      have hd : HasDerivAt (fun s : ℝ => s ^ 3) (3 * (r3Rho a y) ^ 2) (r3Rho a y) := by
        simpa using hasDerivAt_pow 3 (r3Rho a y)
      exact hasFDerivAt_comp_real hd hrho
    have hinv3 : HasFDerivAt (fun z : R3 => ((r3Rho a z) ^ 3)⁻¹)
        ((-(((r3Rho a y) ^ 3) ^ 2)⁻¹) • ((3 * (r3Rho a y) ^ 2) • Lrho)) y :=
      hasFDerivAt_comp_real (hasDerivAt_inv (ne_of_gt (pow_pos (r3Rho_pos ha y) 3))) hpow3
    exact hneg.mul hinv3
  have heq_f : ∀ i : Fin 3,
      (fun z : R3 => partialDerivScalar (r3Phi a) z i) =
        fun z : R3 => -z i * ((r3Rho a z) ^ 3)⁻¹ := fun i => funext (fun z => hp1 z i)
  have hdiff : ∀ i : Fin 3, Differentiable ℝ (fun y : R3 => partialDerivScalar (r3Phi a) y i) := by
    intro i y
    rw [heq_f i]
    exact (hfd2 i y).differentiableAt
  have hdiag : ∀ (y : R3) (i : Fin 3),
      partialDerivScalar (fun z => partialDerivScalar (r3Phi a) z i) y i =
        -((r3Rho a y) ^ 3)⁻¹ + 3 * (y i) ^ 2 * ((r3Rho a y) ^ 5)⁻¹ := by
    intro y i
    rw [heq_f i]
    unfold partialDerivScalar
    rw [(hfd2 i y).fderiv]
    simp only [r3GradSqCLM, add_apply, smul_apply, neg_apply, smul_eq_mul, r3Proj_basisVec_eval]
    have hρ_ne : r3Rho a y ≠ 0 := ne_of_gt (r3Rho_pos ha y)
    fin_cases i <;> simp <;> field_simp <;> ring
  have hlap : ∀ y : R3,
      partialDerivScalar (fun z => partialDerivScalar (r3Phi a) z 0) y 0 +
      partialDerivScalar (fun z => partialDerivScalar (r3Phi a) z 1) y 1 +
      partialDerivScalar (fun z => partialDerivScalar (r3Phi a) z 2) y 2 =
        -(3 * a ^ 2 * ((r3Rho a y) ^ 5)⁻¹) := by
    intro y
    rw [hdiag y 0, hdiag y 1, hdiag y 2]
    have hρ_ne : r3Rho a y ≠ 0 := ne_of_gt (r3Rho_pos ha y)
    have hρ2 : (r3Rho a y) ^ 2 = (y 0) ^ 2 + (y 1) ^ 2 + (y 2) ^ 2 + a ^ 2 := r3Rho_sq a y
    field_simp
    nlinarith [hρ2]
  exact ⟨hdiff, hdiag, hlap⟩

private lemma intervalIntegral_cauchy_schwarz_const {h : ℝ → ℝ} {a b : ℝ}
    (hab : a ≤ b) (hh : Continuous h) :
    (∫ u in a..b, h u) ^ 2 ≤ (b - a) * ∫ u in a..b, (h u) ^ 2 := by
  rcases eq_or_lt_of_le hab with rfl | hlt
  · simp
  · set I1 := ∫ u in a..b, h u
    set I2 := ∫ u in a..b, (h u) ^ 2
    have hquad : ∀ t : ℝ, 0 ≤ t ^ 2 * (b - a) + 2 * t * I1 + I2 := fun t => by
      have hnn : 0 ≤ ∫ u in a..b, (t + h u) ^ 2 :=
        intervalIntegral.integral_nonneg hab (fun _ _ => sq_nonneg _)
      have hexp : (fun u : ℝ => (t + h u) ^ 2) =
          fun u => t ^ 2 + (2 * t) * h u + (h u) ^ 2 := by funext u; ring
      have hc1 : IntervalIntegrable (fun _ : ℝ => t ^ 2) volume a b :=
        continuous_const.intervalIntegrable a b
      have hc2 : IntervalIntegrable (fun u : ℝ => (2 * t) * h u) volume a b :=
        (continuous_const.mul hh).intervalIntegrable a b
      have hc3 : IntervalIntegrable (fun u : ℝ => (h u) ^ 2) volume a b :=
        (hh.pow 2).intervalIntegrable a b
      have h12 : IntervalIntegrable (fun u : ℝ => t ^ 2 + (2 * t) * h u) volume a b :=
        (continuous_const.add (continuous_const.mul hh)).intervalIntegrable a b
      rw [hexp, intervalIntegral.integral_add h12 hc3,
          intervalIntegral.integral_add hc1 hc2,
          intervalIntegral.integral_const, smul_eq_mul,
          intervalIntegral.integral_const_mul] at hnn
      dsimp only [I1, I2]
      linarith
    have hpos : 0 < b - a := by linarith
    have hne : b - a ≠ 0 := ne_of_gt hpos
    have hq := hquad (-I1 / (b - a))
    have hmul := mul_nonneg (le_of_lt hpos) hq
    have hcalc : (b - a) * ((-I1 / (b - a)) ^ 2 * (b - a) + 2 * (-I1 / (b - a)) * I1 + I2) =
        (b - a) * I2 - I1 ^ 2 := by
      field_simp; ring
    linarith

/-- **Key Real-Space `L²(ℝ³)` Bound on `ψ_{ε,R} = φ_ε - φ_R` (Uniform in `ε`!):**
    Using the smooth substitution `s = u²` and `r3Integral_inv_rho_pow4`:
    `Integrable (r3Psi ε R · ^ 2)` and `∫_{ℝ³} (r3Psi ε R y)² dy ≤ 4 π² R`
    for ALL `0 < ε < R`. -/
theorem r3Integral_psi_sq_le {ε R : ℝ} (hε : 0 < ε) (hεR : ε < R) :
    Integrable (fun y : R3 => (r3Psi ε R y) ^ 2) volume ∧
    r3Integral (fun y : R3 => (r3Psi ε R y) ^ 2) ≤ 4 * Real.pi ^ 2 * R := by
  let a : ℝ := Real.sqrt ε
  let b : ℝ := Real.sqrt R
  have ha_pos : 0 < a := Real.sqrt_pos.mpr hε
  have hb_pos : 0 < b := Real.sqrt_pos.mpr (lt_trans hε hεR)
  have ha2 : a ^ 2 = ε := Real.sq_sqrt (le_of_lt hε)
  have hb2 : b ^ 2 = R := Real.sq_sqrt (le_of_lt (lt_trans hε hεR))
  have hab : a ≤ b := Real.sqrt_le_sqrt (le_of_lt hεR)
  -- Step 1: Pointwise FTC representation ψ_{ε,R}(y) ≤ ∫_a^b 2u / ρ_{u²}(y)² du
  have hpsi_pt : ∀ y : R3,
      (r3Psi ε R y) ^ 2 ≤ (b - a) * ∫ u in a..b, 4 * (max u a) ^ 2 * ((r3Rho ((max u a) ^ 2) y) ^ 4)⁻¹ := by
    intro y
    let F : ℝ → ℝ := fun u => r3Phi (u ^ 2) y
    have hderiv : ∀ u ∈ Set.uIcc a b,
        HasDerivAt F (-(2 * u ^ 3 * ((r3Rho (u ^ 2) y) ^ 3)⁻¹)) u := fun u hu => by
      rw [Set.uIcc_of_le hab] at hu
      have hu_pos : 0 < u := lt_of_lt_of_le ha_pos hu.1
      have hq : HasDerivAt (fun s : ℝ => (y 0) ^ 2 + (y 1) ^ 2 + (y 2) ^ 2 + (s ^ 2) ^ 2)
          (4 * u ^ 3) u := by
        have hq_eq : (fun s : ℝ => (y 0) ^ 2 + (y 1) ^ 2 + (y 2) ^ 2 + (s ^ 2) ^ 2) =
            fun s => (y 0) ^ 2 + (y 1) ^ 2 + (y 2) ^ 2 + s ^ 4 := by funext s; ring
        rw [hq_eq]
        have hd : HasDerivAt (fun s : ℝ => (y 0) ^ 2 + (y 1) ^ 2 + (y 2) ^ 2 + s ^ 4)
            ((4 : ℕ) * u ^ (4 - 1)) u :=
          (hasDerivAt_pow 4 u).const_add ((y 0) ^ 2 + (y 1) ^ 2 + (y 2) ^ 2)
        have hder : ((4 : ℕ) * u ^ (4 - 1)) = 4 * u ^ 3 := by norm_num
        rwa [hder] at hd
      have hρ_pos : 0 < r3Rho (u ^ 2) y := r3Rho_pos (sq_pos_of_pos hu_pos) y
      have hρ_ne : r3Rho (u ^ 2) y ≠ 0 := ne_of_gt hρ_pos
      have hq_ne : (y 0) ^ 2 + (y 1) ^ 2 + (y 2) ^ 2 + (u ^ 2) ^ 2 ≠ 0 := by positivity
      have hrho : HasDerivAt (fun s : ℝ => r3Rho (s ^ 2) y)
          ((4 * u ^ 3) / (2 * r3Rho (u ^ 2) y)) u := by
        unfold r3Rho
        exact hq.sqrt hq_ne
      have hphi : HasDerivAt F
          (-(r3Rho (u ^ 2) y ^ 2)⁻¹ * ((4 * u ^ 3) / (2 * r3Rho (u ^ 2) y))) u :=
        (hasDerivAt_inv hρ_ne).comp u hrho
      have heq_d : -(r3Rho (u ^ 2) y ^ 2)⁻¹ * ((4 * u ^ 3) / (2 * r3Rho (u ^ 2) y)) =
          -(2 * u ^ 3 * ((r3Rho (u ^ 2) y) ^ 3)⁻¹) := by field_simp; ring
      rwa [heq_d] at hphi
    have hcont_d : ContinuousOn (fun u : ℝ => 2 * u ^ 3 * ((r3Rho (u ^ 2) y) ^ 3)⁻¹) (Set.uIcc a b) := by
      rw [Set.uIcc_of_le hab]
      refine ContinuousOn.mul (continuous_const.mul (continuous_id.pow 3)).continuousOn ?_
      refine ContinuousOn.inv₀ ?_ (fun u hu => ne_of_gt (pow_pos (r3Rho_pos (sq_pos_of_pos (lt_of_lt_of_le ha_pos hu.1)) y) 3))
      exact ((Real.continuous_sqrt.comp (continuous_const.add ((continuous_id.pow 2).pow 2))).pow 3).continuousOn
    have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv (hcont_d.neg.intervalIntegrable)
    have hpsi_eq : r3Psi ε R y = ∫ u in a..b, 2 * u ^ 3 * ((r3Rho (u ^ 2) y) ^ 3)⁻¹ := by
      have hneg := intervalIntegral.integral_neg (μ := volume) (a := a) (b := b)
        (f := fun u : ℝ => 2 * u ^ 3 * ((r3Rho (u ^ 2) y) ^ 3)⁻¹)
      have hF : F b - F a = -r3Psi ε R y := by
        dsimp only [F, r3Psi]; rw [ha2, hb2]; ring
      linarith
    have hpsi_nn : 0 ≤ r3Psi ε R y := by
      unfold r3Psi r3Phi
      have hle : r3Rho ε y ≤ r3Rho R y := by
        unfold r3Rho
        exact Real.sqrt_le_sqrt (by nlinarith)
      exact sub_nonneg.mpr (inv_anti₀ (r3Rho_pos hε y) hle)
    let h_dom : ℝ → ℝ := fun u => 2 * max u a * ((r3Rho ((max u a) ^ 2) y) ^ 2)⁻¹
    have hh_cont : Continuous h_dom := by
      dsimp only [h_dom]
      have hma : Continuous (fun u : ℝ => max u a) := continuous_id.max continuous_const
      have hrho_c : Continuous (fun u : ℝ => r3Rho ((max u a) ^ 2) y) :=
        Real.continuous_sqrt.comp (continuous_const.add ((hma.pow 2).pow 2))
      exact (continuous_const.mul hma).mul
        ((hrho_c.pow 2).inv₀ (fun u => ne_of_gt (pow_pos (r3Rho_pos (sq_pos_of_pos (lt_of_lt_of_le ha_pos (le_max_right u a))) y) 2)))
    have hpsi_le : r3Psi ε R y ≤ ∫ u in a..b, h_dom u := by
      rw [hpsi_eq]
      apply intervalIntegral.integral_mono_on hab
        hcont_d.intervalIntegrable
        (hh_cont.intervalIntegrable a b)
      intro u hu
      have hu_pos : 0 < u := lt_of_lt_of_le ha_pos hu.1
      have hmax : max u a = u := max_eq_left hu.1
      dsimp only [h_dom]; rw [hmax]
      have hρ_pos : 0 < r3Rho (u ^ 2) y := r3Rho_pos (sq_pos_of_pos hu_pos) y
      have hu2_le : u ^ 2 ≤ r3Rho (u ^ 2) y := r3Rho_ge_param (sq_pos_of_pos hu_pos) y
      have hρ_ne : r3Rho (u ^ 2) y ≠ 0 := ne_of_gt hρ_pos
      have h1 : 2 * u ^ 3 * ((r3Rho (u ^ 2) y) ^ 3)⁻¹ ≤
          2 * u * r3Rho (u ^ 2) y * ((r3Rho (u ^ 2) y) ^ 3)⁻¹ := by
        have hmul : 2 * u ^ 3 ≤ 2 * u * r3Rho (u ^ 2) y := by nlinarith
        exact mul_le_mul_of_nonneg_right hmul (by positivity)
      have h2 : 2 * u * r3Rho (u ^ 2) y * ((r3Rho (u ^ 2) y) ^ 3)⁻¹ =
          2 * u * ((r3Rho (u ^ 2) y) ^ 2)⁻¹ := by field_simp
      linarith
    have hcs := intervalIntegral_cauchy_schwarz_const hab hh_cont
    have hsq_eq : (fun u : ℝ => (h_dom u) ^ 2) =
        fun u : ℝ => 4 * (max u a) ^ 2 * ((r3Rho ((max u a) ^ 2) y) ^ 4)⁻¹ := by
      funext u; dsimp only [h_dom]; ring
    rw [hsq_eq] at hcs
    have hsq_le : (r3Psi ε R y) ^ 2 ≤ (∫ u in a..b, h_dom u) ^ 2 := by nlinarith
    exact le_trans hsq_le hcs
  -- Step 2: Tonelli/Fubini on (Set.Ioc a b) × ℝ³
  let K : ℝ × R3 → ℝ := fun p => 4 * (max p.1 a) ^ 2 * ((r3Rho ((max p.1 a) ^ 2) p.2) ^ 4)⁻¹
  have hK_cont : Continuous K := by
    dsimp only [K]
    have hma : Continuous (fun p : ℝ × R3 => max p.1 a) := continuous_fst.max continuous_const
    have hrho_c : Continuous (fun p : ℝ × R3 => r3Rho ((max p.1 a) ^ 2) p.2) := by
      unfold r3Rho
      exact Real.continuous_sqrt.comp
        ((((((continuous_apply 0).comp continuous_snd).pow 2).add
          (((continuous_apply 1).comp continuous_snd).pow 2)).add
          (((continuous_apply 2).comp continuous_snd).pow 2)).add ((hma.pow 2).pow 2))
    exact (continuous_const.mul (hma.pow 2)).mul
      ((hrho_c.pow 4).inv₀ (fun p =>
        ne_of_gt (pow_pos (r3Rho_pos (sq_pos_of_pos (lt_of_lt_of_le ha_pos (le_max_right p.1 a))) p.2) 4)))
  let μI : Measure ℝ := volume.restrict (Set.Ioc a b)
  have hK_slice : ∀ u : ℝ,
      Integrable (fun y : R3 => K (u, y)) volume ∧
      (∫ y : R3, K (u, y)) = 4 * Real.pi ^ 2 := fun u => by
    have hmu_pos : 0 < (max u a) ^ 2 := sq_pos_of_pos (lt_of_lt_of_le ha_pos (le_max_right u a))
    have h4 := r3Integral_inv_rho_pow4 hmu_pos
    refine ⟨h4.1.const_mul (4 * (max u a) ^ 2), ?_⟩
    dsimp only [K]
    rw [MeasureTheory.integral_const_mul]
    change 4 * (max u a) ^ 2 * r3Integral (fun y : R3 => ((r3Rho ((max u a) ^ 2) y) ^ 4)⁻¹) = _
    rw [h4.2]
    have hne : (max u a) ^ 2 ≠ 0 := ne_of_gt hmu_pos
    field_simp
  have hK_prod : Integrable K (μI.prod volume) := by
    rw [MeasureTheory.integrable_prod_iff hK_cont.aestronglyMeasurable]
    refine ⟨Filter.Eventually.of_forall (fun u => (hK_slice u).1), ?_⟩
    have hnorm : (fun u : ℝ => ∫ y : R3, ‖K (u, y)‖) = fun _ => 4 * Real.pi ^ 2 := by
      funext u
      have h1 : (fun y : R3 => ‖K (u, y)‖) = fun y : R3 => K (u, y) := by
        funext y; dsimp only [K]
        rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      rw [h1, (hK_slice u).2]
    rw [hnorm]
    exact integrable_const (4 * Real.pi ^ 2)
  have hdom_int : Integrable (fun y : R3 => (b - a) * ∫ u : ℝ, K (u, y) ∂μI) volume :=
    hK_prod.integral_prod_right.const_mul (b - a)
  have hpsi_le_dom : ∀ y : R3, (r3Psi ε R y) ^ 2 ≤ (b - a) * ∫ u : ℝ, K (u, y) ∂μI := fun y => by
    have hrew : (∫ u : ℝ, K (u, y) ∂μI) =
        ∫ u in a..b, 4 * (max u a) ^ 2 * ((r3Rho ((max u a) ^ 2) y) ^ 4)⁻¹ := by
      dsimp only [μI, K]
      rw [intervalIntegral.integral_of_le hab]
    rw [hrew]; exact hpsi_pt y
  have hpsi_cont : Continuous (fun y : R3 => (r3Psi ε R y) ^ 2) :=
    ((r3Phi_continuous hε).sub (r3Phi_continuous (lt_trans hε hεR))).pow 2
  have hpsi_int : Integrable (fun y : R3 => (r3Psi ε R y) ^ 2) volume := by
    refine hdom_int.mono' hpsi_cont.aestronglyMeasurable (Filter.Eventually.of_forall fun y => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact hpsi_le_dom y
  refine ⟨hpsi_int, ?_⟩
  have hmono : r3Integral (fun y : R3 => (r3Psi ε R y) ^ 2) ≤
      r3Integral (fun y : R3 => (b - a) * ∫ u : ℝ, K (u, y) ∂μI) :=
    MeasureTheory.integral_mono hpsi_int hdom_int hpsi_le_dom
  rw [r3Integral_const_mul] at hmono
  have hfub : r3Integral (fun y : R3 => ∫ u : ℝ, K (u, y) ∂μI) = 4 * Real.pi ^ 2 * (b - a) := by
    unfold r3Integral
    rw [← MeasureTheory.integral_prod_symm K hK_prod, MeasureTheory.integral_prod K hK_prod]
    have hinner : (fun u : ℝ => ∫ y : R3, K (u, y)) = fun _ => 4 * Real.pi ^ 2 :=
      funext (fun u => (hK_slice u).2)
    rw [hinner]
    dsimp only [μI]
    rw [← intervalIntegral.integral_of_le hab, intervalIntegral.integral_const, smul_eq_mul]
    ring
  rw [hfub] at hmono
  have hba_sq : (b - a) ^ 2 ≤ R := by
    have h1 : (b - a) ^ 2 ≤ b ^ 2 := by nlinarith
    linarith
  have hpi_nn : 0 ≤ 4 * Real.pi ^ 2 := by positivity
  nlinarith

private lemma r3Phi_partial_sq_integrable {a : ℝ} (ha : 0 < a) (i : Fin 3) :
    Integrable (fun y : R3 => (partialDerivScalar (r3Phi a) y i) ^ 2) volume := by
  have h4 := (r3Integral_inv_rho_pow4 ha).1
  have hcont : Continuous (fun y : R3 => (partialDerivScalar (r3Phi a) y i) ^ 2) :=
    ((r3Phi_partial_differentiable_and_laplacian ha).1 i).continuous.pow 2
  refine h4.mono' hcont.aestronglyMeasurable (Filter.Eventually.of_forall fun y => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), (r3Phi_differentiable_and_partial ha).2 y i]
  have hρ_pos : 0 < r3Rho a y := r3Rho_pos ha y
  have hy_le : (y i) ^ 2 ≤ (r3Rho a y) ^ 2 := r3_coord_sq_le_rho_sq a y i
  have hmul : (y i) ^ 2 * (((r3Rho a y) ^ 3)⁻¹) ^ 2 ≤ (r3Rho a y) ^ 2 * (((r3Rho a y) ^ 3)⁻¹) ^ 2 :=
    mul_le_mul_of_nonneg_right hy_le (sq_nonneg _)
  have heq1 : (-y i * ((r3Rho a y) ^ 3)⁻¹) ^ 2 = (y i) ^ 2 * (((r3Rho a y) ^ 3)⁻¹) ^ 2 := by ring
  have heq2 : (r3Rho a y) ^ 2 * (((r3Rho a y) ^ 3)⁻¹) ^ 2 = ((r3Rho a y) ^ 4)⁻¹ := by
    have hne : r3Rho a y ≠ 0 := ne_of_gt hρ_pos; field_simp
  linarith

/-- **Single-Kernel Green Identity on `ℝ³`:**
    For any `a > 0` and any scalar field `g` in `DecayingH3ScalarR3`,
    `∫_{ℝ³} 3 a² ρ_a(y)⁻⁵ g(y) dy = ∑_{i=0}^2 ∫_{ℝ³} ∂_i φ_a(y) ∂_i g(y) dy`. -/
lemma r3_single_kernel_green_identity {a : ℝ} (ha : 0 < a) {g : R3 → ℝ}
    (hg : DecayingH3ScalarR3 g) :
    r3Integral (fun y => 3 * a ^ 2 * ((r3Rho a y) ^ 5)⁻¹ * g y) =
      r3Integral (fun y => partialDerivScalar (r3Phi a) y 0 * partialDerivScalar g y 0) +
      r3Integral (fun y => partialDerivScalar (r3Phi a) y 1 * partialDerivScalar g y 1) +
      r3Integral (fun y => partialDerivScalar (r3Phi a) y 2 * partialDerivScalar g y 2) := by
  have hφ1 := r3Phi_differentiable_and_partial ha
  have hφ2 := r3Phi_partial_differentiable_and_laplacian ha
  have h6 := r3Integral_inv_rho_pow6_le ha
  have hd_g : Differentiable ℝ g := hg.h_c3.differentiable (by simp)
  have hc_dg : ∀ i : Fin 3, Continuous (fun y => partialDerivScalar g y i) := fun i =>
    (contDiff_partial_c2_ag hg.h_c3 i).continuous
  have hc_φ2 : ∀ i : Fin 3,
      Continuous (fun y => partialDerivScalar (fun z => partialDerivScalar (r3Phi a) z i) y i) := fun i => by
    have heq : (fun y => partialDerivScalar (fun z => partialDerivScalar (r3Phi a) z i) y i) =
        fun y => -((r3Rho a y) ^ 3)⁻¹ + 3 * (y i) ^ 2 * ((r3Rho a y) ^ 5)⁻¹ :=
      funext (fun y => hφ2.2.1 y i)
    rw [heq]
    exact (((r3Rho_continuous a).pow 3).inv₀ (fun y => ne_of_gt (pow_pos (r3Rho_pos ha y) 3))).neg.add
      ((continuous_const.mul ((continuous_apply i).pow 2)).mul
        (((r3Rho_continuous a).pow 5).inv₀ (fun y => ne_of_gt (pow_pos (r3Rho_pos ha y) 5))))
  have hφ2_sq_int : ∀ i : Fin 3,
      Integrable (fun y => (partialDerivScalar (fun z => partialDerivScalar (r3Phi a) z i) y i) ^ 2) volume := by
    intro i
    refine (h6.1.const_mul 16).mono' ((hc_φ2 i).pow 2).aestronglyMeasurable
      (Filter.Eventually.of_forall fun y => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), hφ2.2.1 y i]
    have hρ_pos : 0 < r3Rho a y := r3Rho_pos ha y
    have hy_le : (y i) ^ 2 ≤ (r3Rho a y) ^ 2 := r3_coord_sq_le_rho_sq a y i
    have hρ5_nn : 0 ≤ ((r3Rho a y) ^ 5)⁻¹ := r3Rho_inv_pow_nonneg ha 5 y
    have hρ3_nn : 0 ≤ ((r3Rho a y) ^ 3)⁻¹ := r3Rho_inv_pow_nonneg ha 3 y
    have hterm : 3 * (y i) ^ 2 * ((r3Rho a y) ^ 5)⁻¹ ≤ 3 * ((r3Rho a y) ^ 3)⁻¹ := by
      have h1 : 3 * (y i) ^ 2 * ((r3Rho a y) ^ 5)⁻¹ ≤ 3 * (r3Rho a y) ^ 2 * ((r3Rho a y) ^ 5)⁻¹ :=
        mul_le_mul_of_nonneg_right (by linarith) hρ5_nn
      have h2 : 3 * (r3Rho a y) ^ 2 * ((r3Rho a y) ^ 5)⁻¹ = 3 * ((r3Rho a y) ^ 3)⁻¹ := by
        have hne : r3Rho a y ≠ 0 := ne_of_gt hρ_pos; field_simp
      linarith
    have hlow : -((r3Rho a y) ^ 3)⁻¹ ≤ -((r3Rho a y) ^ 3)⁻¹ + 3 * (y i) ^ 2 * ((r3Rho a y) ^ 5)⁻¹ := by
      have : 0 ≤ 3 * (y i) ^ 2 * ((r3Rho a y) ^ 5)⁻¹ := mul_nonneg (by positivity) hρ5_nn
      linarith
    have hup : -((r3Rho a y) ^ 3)⁻¹ + 3 * (y i) ^ 2 * ((r3Rho a y) ^ 5)⁻¹ ≤ 4 * ((r3Rho a y) ^ 3)⁻¹ := by
      linarith
    have hsq_le : (-((r3Rho a y) ^ 3)⁻¹ + 3 * (y i) ^ 2 * ((r3Rho a y) ^ 5)⁻¹) ^ 2 ≤
        16 * (((r3Rho a y) ^ 3)⁻¹) ^ 2 := by nlinarith
    have hpow6 : (((r3Rho a y) ^ 3)⁻¹) ^ 2 = ((r3Rho a y) ^ 6)⁻¹ := by
      have hne : r3Rho a y ≠ 0 := ne_of_gt hρ_pos; field_simp
    linarith
  have hibp_i : ∀ i : Fin 3,
      r3Integral (fun y => partialDerivScalar (fun z => partialDerivScalar (r3Phi a) z i) y i * g y) =
        -r3Integral (fun y => partialDerivScalar (r3Phi a) y i * partialDerivScalar g y i) := by
    intro i
    have hbdd_i : ∃ C : ℝ, 0 ≤ C ∧ ∀ y : R3, |partialDerivScalar (r3Phi a) y i| ≤ C := by
      refine ⟨(a ^ 2)⁻¹, by positivity, fun y => ?_⟩
      have hρ_pos : 0 < r3Rho a y := r3Rho_pos ha y
      have hρ3_nn : 0 ≤ ((r3Rho a y) ^ 3)⁻¹ := r3Rho_inv_pow_nonneg ha 3 y
      rw [hφ1.2 y i, abs_mul, abs_neg, abs_of_nonneg hρ3_nn]
      have hy_le : |y i| ≤ r3Rho a y := by
        have hsq : (y i) ^ 2 ≤ (r3Rho a y) ^ 2 := r3_coord_sq_le_rho_sq a y i
        nlinarith [abs_nonneg (y i), sq_abs (y i)]
      have ha_le : a ^ 2 ≤ (r3Rho a y) ^ 2 := by
        rw [r3Rho_sq]; nlinarith [sq_nonneg (y 0), sq_nonneg (y 1), sq_nonneg (y 2)]
      have h1 : |y i| * ((r3Rho a y) ^ 3)⁻¹ ≤ r3Rho a y * ((r3Rho a y) ^ 3)⁻¹ :=
        mul_le_mul_of_nonneg_right hy_le hρ3_nn
      have h2 : r3Rho a y * ((r3Rho a y) ^ 3)⁻¹ = ((r3Rho a y) ^ 2)⁻¹ := by
        have hne : r3Rho a y ≠ 0 := ne_of_gt hρ_pos; field_simp
      have h3 : ((r3Rho a y) ^ 2)⁻¹ ≤ (a ^ 2)⁻¹ := inv_anti₀ (sq_pos_of_pos ha) ha_le
      linarith
    have hvan := vanishesAlongAxis_of_vanishesAtInfinityR3
      (vanishesAtInfinityR3_of_bdd_mul hbdd_i hg.h_van0) i
    have h1 := integrable_mul_of_sq (hc_φ2 i) hg.h_c3.continuous (hφ2_sq_int i) hg.h_int0
    have h2 := integrable_mul_of_sq (hφ2.1 i).continuous (hc_dg i) (r3Phi_partial_sq_integrable ha i) (hg.h_int1 i)
    have h := r3Integral_ibp (hφ2.1 i) hd_g hvan h1 h2
    linarith
  have h1_i : ∀ i : Fin 3,
      Integrable (fun y => partialDerivScalar (fun z => partialDerivScalar (r3Phi a) z i) y i * g y) volume :=
    fun i => integrable_mul_of_sq (hc_φ2 i) hg.h_c3.continuous (hφ2_sq_int i) hg.h_int0
  have hsum := r3Integral_add3 (h1_i 0) (h1_i 1) (h1_i 2)
  have hpt : ∀ y : R3,
      partialDerivScalar (fun z => partialDerivScalar (r3Phi a) z 0) y 0 * g y +
      partialDerivScalar (fun z => partialDerivScalar (r3Phi a) z 1) y 1 * g y +
      partialDerivScalar (fun z => partialDerivScalar (r3Phi a) z 2) y 2 * g y =
        -(3 * a ^ 2 * ((r3Rho a y) ^ 5)⁻¹ * g y) := fun y => by
    have hlap := hφ2.2.2 y
    linear_combination g y * hlap
  rw [r3Integral_congr hpt, r3Integral_neg, hibp_i 0, hibp_i 1, hibp_i 2] at hsum
  linarith

/-- **Two-Kernel Smooth Green Identity on `ℝ³`:**
    For any `0 < ε < R` and any `g` in `DecayingH3ScalarR3`,
    `∫_{ℝ³} 3 ε² ρ_ε⁻⁵ g = ∑_i ∫_{ℝ³} ∂_i φ_R ∂_i g - ∫_{ℝ³} ψ_{ε,R} Δ g`. -/
lemma r3_two_kernel_green_identity {ε R : ℝ} (hε : 0 < ε) (hεR : ε < R)
    {g : R3 → ℝ} (hg : DecayingH3ScalarR3 g) :
    r3Integral (fun y => 3 * ε ^ 2 * ((r3Rho ε y) ^ 5)⁻¹ * g y) =
      (r3Integral (fun y => partialDerivScalar (r3Phi R) y 0 * partialDerivScalar g y 0) +
       r3Integral (fun y => partialDerivScalar (r3Phi R) y 1 * partialDerivScalar g y 1) +
       r3Integral (fun y => partialDerivScalar (r3Phi R) y 2 * partialDerivScalar g y 2)) -
      r3Integral (fun y => r3Psi ε R y * laplacianScalar g y) := by
  have hR : 0 < R := lt_trans hε hεR
  have hGε := r3_single_kernel_green_identity hε hg
  have hψ_sq := (r3Integral_psi_sq_le hε hεR).1
  have hψ_cont : Continuous (r3Psi ε R) := (r3Phi_continuous hε).sub (r3Phi_continuous hR)
  have hd_ψ : Differentiable ℝ (r3Psi ε R) :=
    (r3Phi_differentiable_and_partial hε).1.sub (r3Phi_differentiable_and_partial hR).1
  have hψ_bdd : ∃ C : ℝ, 0 ≤ C ∧ ∀ y : R3, |r3Psi ε R y| ≤ C := by
    refine ⟨ε⁻¹ + R⁻¹, by positivity, fun y => ?_⟩
    unfold r3Psi r3Phi
    have h1 : (r3Rho ε y)⁻¹ ≤ ε⁻¹ := inv_anti₀ hε (r3Rho_ge_param hε y)
    have h2 : (r3Rho R y)⁻¹ ≤ R⁻¹ := inv_anti₀ hR (r3Rho_ge_param hR y)
    have h1_nn : 0 ≤ (r3Rho ε y)⁻¹ := inv_nonneg.mpr (le_of_lt (r3Rho_pos hε y))
    have h2_nn : 0 ≤ (r3Rho R y)⁻¹ := inv_nonneg.mpr (le_of_lt (r3Rho_pos hR y))
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  have hd_dg : ∀ i : Fin 3, Differentiable ℝ (fun y => partialDerivScalar g y i) := fun i =>
    (contDiff_partial_c2_ag hg.h_c3 i).differentiable (by simp)
  have hc_snd : ∀ i : Fin 3, Continuous (fun y => sndPartial g y i i) := fun i =>
    (contDiff_snd_c1_ag hg.h_c3 i i).continuous
  have hibp_psi : ∀ i : Fin 3,
      r3Integral (fun y => r3Psi ε R y * sndPartial g y i i) =
        -r3Integral (fun y => partialDerivScalar (r3Phi ε) y i * partialDerivScalar g y i) +
         r3Integral (fun y => partialDerivScalar (r3Phi R) y i * partialDerivScalar g y i) := by
    intro i
    have h2 : ContDiff ℝ 2 g := hg.h_c3.of_le (by exact_mod_cast (show (2 : ℕ) ≤ 3 by decide))
    have hψ_p : (fun y => partialDerivScalar (r3Psi ε R) y i) =
        fun y => partialDerivScalar (r3Phi ε) y i - partialDerivScalar (r3Phi R) y i := by
      funext y
      exact partialDerivScalar_sub ((r3Phi_differentiable_and_partial hε).1 y)
        ((r3Phi_differentiable_and_partial hR).1 y) i
    have h1ε := integrable_mul_of_sq ((r3Phi_partial_differentiable_and_laplacian hε).1 i).continuous
      (hd_dg i).continuous (r3Phi_partial_sq_integrable hε i) (hg.h_int1 i)
    have h1R := integrable_mul_of_sq ((r3Phi_partial_differentiable_and_laplacian hR).1 i).continuous
      (hd_dg i).continuous (r3Phi_partial_sq_integrable hR i) (hg.h_int1 i)
    have h1 : Integrable (fun y => partialDerivScalar (r3Psi ε R) y i * partialDerivScalar g y i) volume := by
      have heq : (fun y => partialDerivScalar (r3Psi ε R) y i * partialDerivScalar g y i) =
          fun y => partialDerivScalar (r3Phi ε) y i * partialDerivScalar g y i -
            partialDerivScalar (r3Phi R) y i * partialDerivScalar g y i := by
        funext y; rw [congrFun hψ_p y]; ring
      rw [heq]; exact h1ε.sub h1R
    have h2_eq : (fun y => r3Psi ε R y * partialDerivScalar (fun z => partialDerivScalar g z i) y i) =
        fun y => r3Psi ε R y * sndPartial g y i i := by
      funext y; rw [partial_partial_eq_sndPartial g y h2.contDiffAt i i]
    have h2_int : Integrable (fun y => r3Psi ε R y * partialDerivScalar (fun z => partialDerivScalar g z i) y i) volume := by
      rw [h2_eq]; exact integrable_mul_of_sq hψ_cont (hc_snd i) hψ_sq (hg.h_int2 i i)
    have hvan := vanishesAlongAxis_of_vanishesAtInfinityR3
      (vanishesAtInfinityR3_of_bdd_mul hψ_bdd (hg.h_van1 i)) i
    have hibp := r3Integral_ibp hd_ψ (hd_dg i) hvan h1 h2_int
    rw [h2_eq] at hibp
    have h1_split : r3Integral (fun y => partialDerivScalar (r3Psi ε R) y i * partialDerivScalar g y i) =
        r3Integral (fun y => partialDerivScalar (r3Phi ε) y i * partialDerivScalar g y i) -
        r3Integral (fun y => partialDerivScalar (r3Phi R) y i * partialDerivScalar g y i) := by
      have heq : (fun y => partialDerivScalar (r3Psi ε R) y i * partialDerivScalar g y i) =
          fun y => partialDerivScalar (r3Phi ε) y i * partialDerivScalar g y i -
            partialDerivScalar (r3Phi R) y i * partialDerivScalar g y i := by
        funext y; rw [congrFun hψ_p y]; ring
      rw [heq, r3Integral_sub h1ε h1R]
    linarith
  have hterm_int : ∀ i : Fin 3, Integrable (fun y => r3Psi ε R y * sndPartial g y i i) volume :=
    fun i => integrable_mul_of_sq hψ_cont (hc_snd i) hψ_sq (hg.h_int2 i i)
  have hlap_eq : r3Integral (fun y => r3Psi ε R y * laplacianScalar g y) =
      r3Integral (fun y => r3Psi ε R y * sndPartial g y 0 0) +
      r3Integral (fun y => r3Psi ε R y * sndPartial g y 1 1) +
      r3Integral (fun y => r3Psi ε R y * sndPartial g y 2 2) := by
    have hpt : ∀ y : R3, r3Psi ε R y * laplacianScalar g y =
        r3Psi ε R y * sndPartial g y 0 0 + r3Psi ε R y * sndPartial g y 1 1 +
        r3Psi ε R y * sndPartial g y 2 2 := fun y => by unfold laplacianScalar; ring
    rw [r3Integral_congr hpt, r3Integral_add3 (hterm_int 0) (hterm_int 1) (hterm_int 2)]
  rw [hlap_eq, hibp_psi 0, hibp_psi 1, hibp_psi 2]
  linarith

-- ============================================================================
-- SECTION 4: THEOREM 10A2-1 — WHOLE-SPACE ℝ³ SCALAR AGMON 3D INEQUALITY
-- ============================================================================

private lemma cauchy_schwarz_3_nonneg_r3 {a0 a1 a2 b0 b1 b2 : ℝ}
    (ha0 : 0 ≤ a0) (ha1 : 0 ≤ a1) (ha2 : 0 ≤ a2)
    (hb0 : 0 ≤ b0) (hb1 : 0 ≤ b1) (hb2 : 0 ≤ b2) :
    Real.sqrt a0 * Real.sqrt b0 + Real.sqrt a1 * Real.sqrt b1 + Real.sqrt a2 * Real.sqrt b2 ≤
      Real.sqrt (a0 + a1 + a2) * Real.sqrt (b0 + b1 + b2) := by
  have hL_nn : 0 ≤ Real.sqrt a0 * Real.sqrt b0 + Real.sqrt a1 * Real.sqrt b1 +
      Real.sqrt a2 * Real.sqrt b2 := by positivity
  have hR_nn : 0 ≤ Real.sqrt (a0 + a1 + a2) * Real.sqrt (b0 + b1 + b2) := by positivity
  have hsq : (Real.sqrt a0 * Real.sqrt b0 + Real.sqrt a1 * Real.sqrt b1 +
      Real.sqrt a2 * Real.sqrt b2) ^ 2 ≤
      (Real.sqrt (a0 + a1 + a2) * Real.sqrt (b0 + b1 + b2)) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (by linarith), Real.sq_sqrt (by linarith)]
    have s0 := Real.sq_sqrt ha0; have s1 := Real.sq_sqrt ha1; have s2 := Real.sq_sqrt ha2
    have t0 := Real.sq_sqrt hb0; have t1 := Real.sq_sqrt hb1; have t2 := Real.sq_sqrt hb2
    nlinarith [sq_nonneg (Real.sqrt a0 * Real.sqrt b1 - Real.sqrt a1 * Real.sqrt b0),
               sq_nonneg (Real.sqrt a0 * Real.sqrt b2 - Real.sqrt a2 * Real.sqrt b0),
               sq_nonneg (Real.sqrt a1 * Real.sqrt b2 - Real.sqrt a2 * Real.sqrt b1)]
  nlinarith

private lemma r3_poisson_avg_error_le {g : R3 → ℝ} (hg : DecayingH3ScalarR3 g)
    {Cg r δ ε : ℝ} (hCg_nn : 0 ≤ Cg) (hCg : ∀ x : R3, |g x| ≤ Cg)
    (hr_pos : 0 < r) (hδ : 0 < δ)
    (hr : ∀ ⦃y : R3⦄, dist y 0 < r → dist (g y) (g 0) < δ / (8 * Real.pi))
    (hε_pos : 0 < ε) (hε_small : ε ≤ δ * r / (12 * Real.pi ^ 2 * (Cg + 1))) :
    |r3Integral (fun y => 3 * ε ^ 2 * ((r3Rho ε y) ^ 5)⁻¹ * g y) - 4 * Real.pi * g 0| ≤ δ := by
  have hPε := r3Integral_poisson_kernel_eq hε_pos
  have h4ε := r3Integral_inv_rho_pow4 hε_pos
  have hdiff_bdd : ∀ y : R3,
      |3 * ε ^ 2 * ((r3Rho ε y) ^ 5)⁻¹ * (g y - g 0)| ≤
        (δ / (8 * Real.pi)) * (3 * ε ^ 2 * ((r3Rho ε y) ^ 5)⁻¹) +
        (6 * Cg * ε ^ 2 / r) * ((r3Rho ε y) ^ 4)⁻¹ := fun y => by
    have hP_nn : 0 ≤ 3 * ε ^ 2 * ((r3Rho ε y) ^ 5)⁻¹ :=
      mul_nonneg (by positivity) (r3Rho_inv_pow_nonneg hε_pos 5 y)
    rw [abs_mul, abs_of_nonneg hP_nn]
    have hg_diff : |g y - g 0| ≤ δ / (8 * Real.pi) + (2 * Cg / r) * r3Rho ε y := by
      by_cases hy : dist y 0 < r
      · have hlt := hr hy
        rw [Real.dist_eq] at hlt
        have : 0 ≤ (2 * Cg / r) * r3Rho ε y :=
          mul_nonneg (by positivity) (le_of_lt (r3Rho_pos hε_pos y))
        linarith
      · push Not at hy
        rw [dist_zero_right] at hy
        have hr_le_ρ : r ≤ r3Rho ε y := by
          have hnorm := norm_sq_le_sum_sq_r3 y
          have hsq : r ^ 2 ≤ (r3Rho ε y) ^ 2 := by
            rw [r3Rho_sq]; nlinarith [sq_nonneg ε]
          nlinarith [r3Rho_pos hε_pos y]
        have h2C : |g y - g 0| ≤ 2 * Cg := by
          calc |g y - g 0| ≤ |g y| + |g 0| := abs_sub (g y) (g 0)
            _ ≤ Cg + Cg := add_le_add (hCg y) (hCg 0)
            _ = 2 * Cg := by ring
        have h1_le : 1 ≤ r3Rho ε y / r := (one_le_div hr_pos).mpr hr_le_ρ
        have hmul : 2 * Cg ≤ (2 * Cg / r) * r3Rho ε y := by
          have := mul_le_mul_of_nonneg_left h1_le (show 0 ≤ 2 * Cg by linarith)
          have heq : 2 * Cg * (r3Rho ε y / r) = (2 * Cg / r) * r3Rho ε y := by ring
          linarith
        have hδ_nn : 0 ≤ δ / (8 * Real.pi) := by positivity
        linarith
    have hmul := mul_le_mul_of_nonneg_left hg_diff hP_nn
    have hsimp : 3 * ε ^ 2 * ((r3Rho ε y) ^ 5)⁻¹ * ((2 * Cg / r) * r3Rho ε y) =
        (6 * Cg * ε ^ 2 / r) * ((r3Rho ε y) ^ 4)⁻¹ := by
      have hne : r3Rho ε y ≠ 0 := ne_of_gt (r3Rho_pos hε_pos y)
      field_simp; ring
    linarith
  have hdom_err : Integrable (fun y : R3 =>
      (δ / (8 * Real.pi)) * (3 * ε ^ 2 * ((r3Rho ε y) ^ 5)⁻¹) +
      (6 * Cg * ε ^ 2 / r) * ((r3Rho ε y) ^ 4)⁻¹) volume :=
    int_add_ag (int_const_mul_ag _ hPε.1) (int_const_mul_ag _ h4ε.1)
  have hdiff_cont : Continuous (fun y : R3 => 3 * ε ^ 2 * ((r3Rho ε y) ^ 5)⁻¹ * (g y - g 0)) :=
    ((continuous_const.mul (((r3Rho_continuous ε).pow 5).inv₀
      (fun y => ne_of_gt (pow_pos (r3Rho_pos hε_pos y) 5))))).mul
      (hg.h_c3.continuous.sub continuous_const)
  have hdiff_int : Integrable (fun y : R3 => 3 * ε ^ 2 * ((r3Rho ε y) ^ 5)⁻¹ * (g y - g 0)) volume :=
    hdom_err.mono' hdiff_cont.aestronglyMeasurable (Filter.Eventually.of_forall fun y => by
      rw [Real.norm_eq_abs]; exact hdiff_bdd y)
  have hPεg_int : Integrable (fun y : R3 => 3 * ε ^ 2 * ((r3Rho ε y) ^ 5)⁻¹ * g y) volume := by
    have hpt : (fun y : R3 => 3 * ε ^ 2 * ((r3Rho ε y) ^ 5)⁻¹ * g y) =
        fun y => 3 * ε ^ 2 * ((r3Rho ε y) ^ 5)⁻¹ * (g y - g 0) +
          g 0 * (3 * ε ^ 2 * ((r3Rho ε y) ^ 5)⁻¹) := by funext y; ring
    rw [hpt]; exact int_add_ag hdiff_int (int_const_mul_ag (g 0) hPε.1)
  have hsplit : r3Integral (fun y => 3 * ε ^ 2 * ((r3Rho ε y) ^ 5)⁻¹ * g y) - 4 * Real.pi * g 0 =
      r3Integral (fun y => 3 * ε ^ 2 * ((r3Rho ε y) ^ 5)⁻¹ * (g y - g 0)) := by
    have hpt : ∀ y : R3, 3 * ε ^ 2 * ((r3Rho ε y) ^ 5)⁻¹ * (g y - g 0) =
        3 * ε ^ 2 * ((r3Rho ε y) ^ 5)⁻¹ * g y - g 0 * (3 * ε ^ 2 * ((r3Rho ε y) ^ 5)⁻¹) := by
      intro y; ring
    rw [r3Integral_congr hpt, r3Integral_sub hPεg_int (int_const_mul_ag (g 0) hPε.1),
        r3Integral_const_mul (g 0), hPε.2]
    ring
  rw [hsplit]
  have hpos_m : r3Integral (fun y => 3 * ε ^ 2 * ((r3Rho ε y) ^ 5)⁻¹ * (g y - g 0)) ≤
      r3Integral (fun y =>
        (δ / (8 * Real.pi)) * (3 * ε ^ 2 * ((r3Rho ε y) ^ 5)⁻¹) +
        (6 * Cg * ε ^ 2 / r) * ((r3Rho ε y) ^ 4)⁻¹) :=
    MeasureTheory.integral_mono hdiff_int hdom_err (fun y => le_trans (le_abs_self _) (hdiff_bdd y))
  have hneg_m : -r3Integral (fun y => 3 * ε ^ 2 * ((r3Rho ε y) ^ 5)⁻¹ * (g y - g 0)) ≤
      r3Integral (fun y =>
        (δ / (8 * Real.pi)) * (3 * ε ^ 2 * ((r3Rho ε y) ^ 5)⁻¹) +
        (6 * Cg * ε ^ 2 / r) * ((r3Rho ε y) ^ 4)⁻¹) := by
    rw [← r3Integral_neg]
    exact MeasureTheory.integral_mono hdiff_int.neg hdom_err
      (fun y => le_trans (neg_le_abs _) (hdiff_bdd y))
  have hdom_val : r3Integral (fun y =>
      (δ / (8 * Real.pi)) * (3 * ε ^ 2 * ((r3Rho ε y) ^ 5)⁻¹) +
      (6 * Cg * ε ^ 2 / r) * ((r3Rho ε y) ^ 4)⁻¹) =
      δ / 2 + 6 * Real.pi ^ 2 * Cg * ε / r := by
    rw [r3Integral_add (int_const_mul_ag _ hPε.1) (int_const_mul_ag _ h4ε.1),
        r3Integral_const_mul (δ / (8 * Real.pi)),
        r3Integral_const_mul (6 * Cg * ε ^ 2 / r), hPε.2, h4ε.2]
    have hpi0 : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
    have hε0 : ε ≠ 0 := ne_of_gt hε_pos
    have hr0 : r ≠ 0 := ne_of_gt hr_pos
    field_simp; ring
  have h2nd : 6 * Real.pi ^ 2 * Cg * ε / r ≤ δ / 2 := by
    have hmul : Cg * ε ≤ (Cg + 1) * (δ * r / (12 * Real.pi ^ 2 * (Cg + 1))) :=
      mul_le_mul (by linarith) hε_small (le_of_lt hε_pos) (by linarith)
    have hfac : 0 ≤ 6 * Real.pi ^ 2 / r := by positivity
    have hstep := mul_le_mul_of_nonneg_left hmul hfac
    have heqL : 6 * Real.pi ^ 2 / r * (Cg * ε) = 6 * Real.pi ^ 2 * Cg * ε / r := by ring
    have heqR : 6 * Real.pi ^ 2 / r * ((Cg + 1) * (δ * r / (12 * Real.pi ^ 2 * (Cg + 1)))) = δ / 2 := by
      have hpi0 : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
      have hr0 : r ≠ 0 := ne_of_gt hr_pos
      have hc0 : Cg + 1 ≠ 0 := by linarith
      field_simp; ring
    linarith
  exact abs_le.mpr ⟨by linarith, by linarith⟩

private lemma r3_green_rhs_bound {g : R3 → ℝ} (hg : DecayingH3ScalarR3 g)
    {ε R : ℝ} (hε : 0 < ε) (hεR : ε < R) :
    let G : ℝ := r3Integral (fun y =>
      (partialDerivScalar g y 0) ^ 2 + (partialDerivScalar g y 1) ^ 2 + (partialDerivScalar g y 2) ^ 2)
    let L : ℝ := r3Integral (fun y => (laplacianScalar g y) ^ 2)
    |r3Integral (fun y => 3 * ε ^ 2 * ((r3Rho ε y) ^ 5)⁻¹ * g y)| ≤
      (Real.pi / Real.sqrt R) * Real.sqrt G + 2 * Real.pi * Real.sqrt R * Real.sqrt L := by
  intro G L
  have hR : 0 < R := lt_trans hε hεR
  have hL_nn : 0 ≤ L := r3Integral_nonneg (fun _ => sq_nonneg _)
  have hc_dg : ∀ i : Fin 3, Continuous (fun y => partialDerivScalar g y i) := fun i =>
    (contDiff_partial_c2_ag hg.h_c3 i).continuous
  have hc_snd : ∀ i : Fin 3, Continuous (fun y => sndPartial g y i i) := fun i =>
    (contDiff_snd_c1_ag hg.h_c3 i i).continuous
  have hc_lap : Continuous (fun y => laplacianScalar g y) := by
    unfold laplacianScalar; exact ((hc_snd 0).add (hc_snd 1)).add (hc_snd 2)
  have hlap_sq_int : Integrable (fun y => (laplacianScalar g y) ^ 2) volume := by
    unfold laplacianScalar
    exact integrable_add_sq_of_sq ((hc_snd 0).add (hc_snd 1)) (hc_snd 2)
      (integrable_add_sq_of_sq (hc_snd 0) (hc_snd 1) (hg.h_int2 0 0) (hg.h_int2 1 1))
      (hg.h_int2 2 2)
  have hgreen := r3_two_kernel_green_identity hε hεR hg
  have h4R := r3Integral_inv_rho_pow4 hR
  let ΦR : Fin 3 → ℝ := fun i => r3Integral (fun y => (partialDerivScalar (r3Phi R) y i) ^ 2)
  let Gi : Fin 3 → ℝ := fun i => r3Integral (fun y => (partialDerivScalar g y i) ^ 2)
  have hterm1_i : ∀ i : Fin 3,
      |r3Integral (fun y => partialDerivScalar (r3Phi R) y i * partialDerivScalar g y i)| ≤
        Real.sqrt (ΦR i) * Real.sqrt (Gi i) := fun i => by
    have hcs := r3_cauchy_schwarz_sq ((r3Phi_partial_differentiable_and_laplacian hR).1 i).continuous
      (hc_dg i) (r3Phi_partial_sq_integrable hR i) (hg.h_int1 i)
    have hR_nn : 0 ≤ Real.sqrt (ΦR i) * Real.sqrt (Gi i) := by positivity
    have hΦ_nn : 0 ≤ ΦR i := r3Integral_nonneg (fun _ => sq_nonneg _)
    have hGi_nn : 0 ≤ Gi i := r3Integral_nonneg (fun _ => sq_nonneg _)
    have hsq : (r3Integral (fun y => partialDerivScalar (r3Phi R) y i * partialDerivScalar g y i)) ^ 2 ≤
        (Real.sqrt (ΦR i) * Real.sqrt (Gi i)) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt hΦ_nn, Real.sq_sqrt hGi_nn]; exact hcs
    nlinarith [sq_abs (r3Integral (fun y => partialDerivScalar (r3Phi R) y i * partialDerivScalar g y i)),
               abs_nonneg (r3Integral (fun y => partialDerivScalar (r3Phi R) y i * partialDerivScalar g y i))]
  have hΦ_sum_le : ΦR 0 + ΦR 1 + ΦR 2 ≤ Real.pi ^ 2 / R := by
    dsimp only [ΦR]
    rw [← r3Integral_add3 (r3Phi_partial_sq_integrable hR 0) (r3Phi_partial_sq_integrable hR 1)
          (r3Phi_partial_sq_integrable hR 2), ← h4R.2]
    apply MeasureTheory.integral_mono
      (int_add_ag (int_add_ag (r3Phi_partial_sq_integrable hR 0) (r3Phi_partial_sq_integrable hR 1))
        (r3Phi_partial_sq_integrable hR 2)) h4R.1
    intro y
    dsimp only
    rw [(r3Phi_differentiable_and_partial hR).2 y 0,
        (r3Phi_differentiable_and_partial hR).2 y 1,
        (r3Phi_differentiable_and_partial hR).2 y 2]
    have hρ_pos : 0 < r3Rho R y := r3Rho_pos hR y
    have hρ_ne : r3Rho R y ≠ 0 := ne_of_gt hρ_pos
    have hsum_le : (y 0) ^ 2 + (y 1) ^ 2 + (y 2) ^ 2 ≤ (r3Rho R y) ^ 2 := by
      rw [r3Rho_sq]; nlinarith [sq_nonneg R]
    have h1 : (-y 0 * ((r3Rho R y) ^ 3)⁻¹) ^ 2 + (-y 1 * ((r3Rho R y) ^ 3)⁻¹) ^ 2 +
        (-y 2 * ((r3Rho R y) ^ 3)⁻¹) ^ 2 =
        ((y 0) ^ 2 + (y 1) ^ 2 + (y 2) ^ 2) * (((r3Rho R y) ^ 3)⁻¹) ^ 2 := by ring
    have h2 : (r3Rho R y) ^ 2 * (((r3Rho R y) ^ 3)⁻¹) ^ 2 = ((r3Rho R y) ^ 4)⁻¹ := by field_simp
    have h3 := mul_le_mul_of_nonneg_right hsum_le (sq_nonneg (((r3Rho R y) ^ 3)⁻¹))
    linarith
  have hG_sum : Gi 0 + Gi 1 + Gi 2 = G := by
    dsimp only [Gi, G]
    rw [← r3Integral_add3 (hg.h_int1 0) (hg.h_int1 1) (hg.h_int1 2)]
  have hterm1 : |r3Integral (fun y => partialDerivScalar (r3Phi R) y 0 * partialDerivScalar g y 0) +
      r3Integral (fun y => partialDerivScalar (r3Phi R) y 1 * partialDerivScalar g y 1) +
      r3Integral (fun y => partialDerivScalar (r3Phi R) y 2 * partialDerivScalar g y 2)| ≤
      (Real.pi / Real.sqrt R) * Real.sqrt G := by
    have hΦ_nn : ∀ i : Fin 3, 0 ≤ ΦR i := fun i => r3Integral_nonneg (fun _ => sq_nonneg _)
    have hGi_nn : ∀ i : Fin 3, 0 ≤ Gi i := fun i => r3Integral_nonneg (fun _ => sq_nonneg _)
    have hcs3 := cauchy_schwarz_3_nonneg_r3
      (hΦ_nn 0) (hΦ_nn 1) (hΦ_nn 2) (hGi_nn 0) (hGi_nn 1) (hGi_nn 2)
    have hsq_le : Real.sqrt (ΦR 0 + ΦR 1 + ΦR 2) ≤ Real.pi / Real.sqrt R := by
      have h1 := Real.sqrt_le_sqrt hΦ_sum_le
      have h2 : Real.sqrt (Real.pi ^ 2 / R) = Real.pi / Real.sqrt R := by
        rw [Real.sqrt_div (sq_nonneg Real.pi), Real.sqrt_sq (le_of_lt Real.pi_pos)]
      linarith
    have htri : |r3Integral (fun y => partialDerivScalar (r3Phi R) y 0 * partialDerivScalar g y 0) +
        r3Integral (fun y => partialDerivScalar (r3Phi R) y 1 * partialDerivScalar g y 1) +
        r3Integral (fun y => partialDerivScalar (r3Phi R) y 2 * partialDerivScalar g y 2)| ≤
        |r3Integral (fun y => partialDerivScalar (r3Phi R) y 0 * partialDerivScalar g y 0)| +
        |r3Integral (fun y => partialDerivScalar (r3Phi R) y 1 * partialDerivScalar g y 1)| +
        |r3Integral (fun y => partialDerivScalar (r3Phi R) y 2 * partialDerivScalar g y 2)| :=
      le_trans (abs_add_le _ _) (add_le_add (abs_add_le _ _) le_rfl)
    have hmul := mul_le_mul_of_nonneg_right hsq_le (Real.sqrt_nonneg G)
    rw [hG_sum] at hcs3
    linarith [hterm1_i 0, hterm1_i 1, hterm1_i 2]
  have hψ := r3Integral_psi_sq_le hε hεR
  have hterm2 : |r3Integral (fun y => r3Psi ε R y * laplacianScalar g y)| ≤
      2 * Real.pi * Real.sqrt R * Real.sqrt L := by
    have hψ_cont : Continuous (r3Psi ε R) := (r3Phi_continuous hε).sub (r3Phi_continuous hR)
    have hcs := r3_cauchy_schwarz_sq hψ_cont hc_lap hψ.1 hlap_sq_int
    have hR_nn : 0 ≤ 2 * Real.pi * Real.sqrt R * Real.sqrt L := by positivity
    have hsq : (r3Integral (fun y => r3Psi ε R y * laplacianScalar g y)) ^ 2 ≤
        (2 * Real.pi * Real.sqrt R * Real.sqrt L) ^ 2 := by
      have h1 : (2 * Real.pi * Real.sqrt R * Real.sqrt L) ^ 2 = (4 * Real.pi ^ 2 * R) * L := by
        rw [mul_pow, mul_pow, mul_pow, Real.sq_sqrt (le_of_lt hR), Real.sq_sqrt hL_nn]; ring
      rw [h1]
      exact le_trans hcs (mul_le_mul_of_nonneg_right hψ.2 hL_nn)
    nlinarith [sq_abs (r3Integral (fun y => r3Psi ε R y * laplacianScalar g y)),
               abs_nonneg (r3Integral (fun y => r3Psi ε R y * laplacianScalar g y))]
  have hgreen_abs : |r3Integral (fun y => 3 * ε ^ 2 * ((r3Rho ε y) ^ 5)⁻¹ * g y)| ≤
      |r3Integral (fun y => partialDerivScalar (r3Phi R) y 0 * partialDerivScalar g y 0) +
       r3Integral (fun y => partialDerivScalar (r3Phi R) y 1 * partialDerivScalar g y 1) +
       r3Integral (fun y => partialDerivScalar (r3Phi R) y 2 * partialDerivScalar g y 2)| +
      |r3Integral (fun y => r3Psi ε R y * laplacianScalar g y)| := by
    rw [hgreen]; exact abs_sub _ _
  linarith

private lemma agmon_3d_r3_scalar_at_zero {g : R3 → ℝ} (hg : DecayingH3ScalarR3 g) :
    (g 0) ^ 2 ≤
      (1 / 2 : ℝ) *
        Real.sqrt (r3Integral (fun y =>
          (partialDerivScalar g y 0) ^ 2 + (partialDerivScalar g y 1) ^ 2 +
          (partialDerivScalar g y 2) ^ 2)) *
        Real.sqrt (r3Integral (fun y => (laplacianScalar g y) ^ 2)) := by
  let G : ℝ := r3Integral (fun y =>
    (partialDerivScalar g y 0) ^ 2 + (partialDerivScalar g y 1) ^ 2 + (partialDerivScalar g y 2) ^ 2)
  let L : ℝ := r3Integral (fun y => (laplacianScalar g y) ^ 2)
  have hG_nn : 0 ≤ G := r3Integral_nonneg (fun _ => by positivity)
  have hL_nn : 0 ≤ L := r3Integral_nonneg (fun _ => sq_nonneg _)
  obtain ⟨Cg, hCg_nn, hCg⟩ := exists_bound_of_vanishesAtInfinityR3 hg.h_c3.continuous hg.h_van0
  have hR_bnd : ∀ R : ℝ, 0 < R →
      4 * |g 0| ≤ Real.sqrt G / Real.sqrt R + 2 * Real.sqrt R * Real.sqrt L := by
    intro R hR
    have h4pi : 4 * Real.pi * |g 0| ≤
        (Real.pi / Real.sqrt R) * Real.sqrt G + 2 * Real.pi * Real.sqrt R * Real.sqrt L := by
      refine le_of_forall_pos_le_add fun δ hδ => ?_
      have hα_pos : 0 < δ / (8 * Real.pi) := by positivity
      obtain ⟨r, hr_pos, hr⟩ := Metric.continuousAt_iff.mp hg.h_c3.continuous.continuousAt
        (δ / (8 * Real.pi)) hα_pos
      let ε : ℝ := min (R / 2) (δ * r / (12 * Real.pi ^ 2 * (Cg + 1)))
      have hε_pos : 0 < ε := lt_min (by positivity) (by positivity)
      have hεR : ε < R := lt_of_le_of_lt (min_le_left _ _) (by linarith)
      have herr := r3_poisson_avg_error_le hg hCg_nn hCg hr_pos hδ hr hε_pos (min_le_right _ _)
      have hgr := r3_green_rhs_bound hg hε_pos hεR
      have h4pi_abs : 4 * Real.pi * |g 0| = |4 * Real.pi * g 0| := by
        rw [abs_mul, abs_of_nonneg (show 0 ≤ 4 * Real.pi by positivity)]
      have htri : |4 * Real.pi * g 0| ≤
          |r3Integral (fun y => 3 * ε ^ 2 * ((r3Rho ε y) ^ 5)⁻¹ * g y)| +
          |r3Integral (fun y => 3 * ε ^ 2 * ((r3Rho ε y) ^ 5)⁻¹ * g y) - 4 * Real.pi * g 0| := by
        set I := r3Integral (fun y => 3 * ε ^ 2 * ((r3Rho ε y) ^ 5)⁻¹ * g y)
        calc |4 * Real.pi * g 0| = |I - (I - 4 * Real.pi * g 0)| := by ring_nf
          _ ≤ |I| + |I - 4 * Real.pi * g 0| := abs_sub _ _
      linarith
    have hpi_pos : 0 < Real.pi := Real.pi_pos
    have hfac : Real.pi / Real.sqrt R * Real.sqrt G = Real.pi * (Real.sqrt G / Real.sqrt R) := by ring
    nlinarith
  by_cases hG0 : G = 0
  · have hg0 : g 0 = 0 := by
      by_contra hne
      have habs : 0 < |g 0| := abs_pos.mpr hne
      let R0 : ℝ := (|g 0| / (Real.sqrt L + 1)) ^ 2
      have hR0_pos : 0 < R0 := sq_pos_of_pos (div_pos habs (by positivity))
      have hsqR0 : Real.sqrt R0 = |g 0| / (Real.sqrt L + 1) :=
        Real.sqrt_sq (le_of_lt (div_pos habs (by positivity)))
      have hb := hR_bnd R0 hR0_pos
      rw [hG0, Real.sqrt_zero, zero_div, zero_add, hsqR0] at hb
      have hlt : 2 * (|g 0| / (Real.sqrt L + 1)) * Real.sqrt L < 2 * |g 0| := by
        have hpos : 0 < Real.sqrt L + 1 := by positivity
        calc 2 * (|g 0| / (Real.sqrt L + 1)) * Real.sqrt L
            = 2 * |g 0| * (Real.sqrt L / (Real.sqrt L + 1)) := by ring
          _ < 2 * |g 0| * 1 := mul_lt_mul_of_pos_left ((div_lt_one hpos).mpr (by linarith)) (by linarith)
          _ = 2 * |g 0| := mul_one _
      linarith
    rw [hg0, zero_pow (by decide)]; positivity
  · by_cases hL0 : L = 0
    · have hg0 : g 0 = 0 := by
        by_contra hne
        have habs : 0 < |g 0| := abs_pos.mpr hne
        let R0 : ℝ := ((Real.sqrt G + 1) / |g 0|) ^ 2
        have hR0_pos : 0 < R0 := sq_pos_of_pos (div_pos (by positivity) habs)
        have hsqR0 : Real.sqrt R0 = (Real.sqrt G + 1) / |g 0| :=
          Real.sqrt_sq (le_of_lt (div_pos (by positivity) habs))
        have hb := hR_bnd R0 hR0_pos
        rw [hL0, Real.sqrt_zero, mul_zero, add_zero, hsqR0] at hb
        have hlt : Real.sqrt G / ((Real.sqrt G + 1) / |g 0|) < |g 0| := by
          have hpos : 0 < Real.sqrt G + 1 := by positivity
          calc Real.sqrt G / ((Real.sqrt G + 1) / |g 0|)
              = |g 0| * (Real.sqrt G / (Real.sqrt G + 1)) := by
                  have hne' : |g 0| ≠ 0 := ne_of_gt habs
                  have hpos' : Real.sqrt G + 1 ≠ 0 := ne_of_gt hpos
                  field_simp
            _ < |g 0| * 1 := mul_lt_mul_of_pos_left ((div_lt_one hpos).mpr (by linarith)) habs
            _ = |g 0| := mul_one _
        linarith
      rw [hg0, zero_pow (by decide)]; positivity
    · have hG_pos : 0 < G := lt_of_le_of_ne hG_nn (Ne.symm hG0)
      have hL_pos : 0 < L := lt_of_le_of_ne hL_nn (Ne.symm hL0)
      let R_opt : ℝ := Real.sqrt G / (2 * Real.sqrt L)
      have hR_pos : 0 < R_opt := by dsimp only [R_opt]; positivity
      have hb := hR_bnd R_opt hR_pos
      have hL_nonneg : 0 ≤ 4 * |g 0| := by positivity
      have hsq : (4 * |g 0|) ^ 2 ≤
          (Real.sqrt G / Real.sqrt R_opt + 2 * Real.sqrt R_opt * Real.sqrt L) ^ 2 := by nlinarith
      have hR_ne : R_opt ≠ 0 := ne_of_gt hR_pos
      have hsqR_ne : Real.sqrt R_opt ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hR_pos)
      have hexp : (Real.sqrt G / Real.sqrt R_opt + 2 * Real.sqrt R_opt * Real.sqrt L) ^ 2 =
          G / R_opt + 4 * Real.sqrt G * Real.sqrt L + 4 * R_opt * L := by
        have h1 : (Real.sqrt G / Real.sqrt R_opt) ^ 2 = G / R_opt := by
          rw [div_pow, Real.sq_sqrt hG_nn, Real.sq_sqrt (le_of_lt hR_pos)]
        have h2 : (2 * Real.sqrt R_opt * Real.sqrt L) ^ 2 = 4 * R_opt * L := by
          rw [mul_pow, mul_pow, Real.sq_sqrt (le_of_lt hR_pos), Real.sq_sqrt hL_nn]; ring
        have h3 : 2 * (Real.sqrt G / Real.sqrt R_opt) * (2 * Real.sqrt R_opt * Real.sqrt L) =
            4 * Real.sqrt G * Real.sqrt L := by field_simp; ring
        have hsq_id : (Real.sqrt G / Real.sqrt R_opt + 2 * Real.sqrt R_opt * Real.sqrt L) ^ 2 =
            (Real.sqrt G / Real.sqrt R_opt) ^ 2 +
            2 * (Real.sqrt G / Real.sqrt R_opt) * (2 * Real.sqrt R_opt * Real.sqrt L) +
            (2 * Real.sqrt R_opt * Real.sqrt L) ^ 2 := by ring
        linarith
      have hterm_opt1 : G / R_opt = 2 * Real.sqrt G * Real.sqrt L := by
        dsimp only [R_opt]
        have hsqG_ne : Real.sqrt G ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hG_pos)
        have hsqL_ne : Real.sqrt L ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hL_pos)
        have hG2 : (Real.sqrt G) ^ 2 = G := Real.sq_sqrt hG_nn
        field_simp; nlinarith [hG2]
      have hterm_opt2 : 4 * R_opt * L = 2 * Real.sqrt G * Real.sqrt L := by
        dsimp only [R_opt]
        have hsqL_ne : Real.sqrt L ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hL_pos)
        have hL2 : (Real.sqrt L) ^ 2 = L := Real.sq_sqrt hL_nn
        field_simp; nlinarith [hL2]
      rw [hexp, hterm_opt1, hterm_opt2] at hsq
      have habs_sq : (4 * |g 0|) ^ 2 = 16 * (g 0) ^ 2 := by rw [mul_pow, sq_abs]; ring
      linarith

private lemma tendsto_add_left_cocompact (x₀ : R3) :
    Tendsto (fun y : R3 => x₀ + y) (cocompact R3) (cocompact R3) := by
  rw [Filter.hasBasis_cocompact.tendsto_right_iff]
  intro K hK
  obtain ⟨C, hC⟩ := hK.isBounded.subset_closedBall (0 : R3)
  rw [Filter.hasBasis_cocompact.eventually_iff]
  refine ⟨Metric.closedBall (0 : R3) (C + ‖x₀‖), isCompact_closedBall 0 (C + ‖x₀‖), fun y hy hmem => ?_⟩
  have h1 : ‖x₀ + y‖ ≤ C := by simpa [dist_zero_right] using hC hmem
  have h2 : C + ‖x₀‖ < ‖y‖ := by
    by_contra hle; push Not at hle
    exact hy (by simpa [Metric.mem_closedBall, dist_zero_right] using hle)
  have htri : ‖y‖ ≤ ‖x₀ + y‖ + ‖x₀‖ := by
    simpa [add_sub_cancel_left] using norm_sub_le (x₀ + y) x₀
  linarith

private lemma fderiv_translate_left {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (h : R3 → E) (x₀ y : R3) :
    fderiv ℝ (fun z : R3 => h (x₀ + z)) y = fderiv ℝ h (x₀ + y) := by
  by_cases hd : DifferentiableAt ℝ h (x₀ + y)
  · have htr : HasFDerivAt (fun z : R3 => x₀ + z) (ContinuousLinearMap.id ℝ R3) y := by
      have h1 : HasFDerivAt (fun z : R3 => x₀ + z) (0 + ContinuousLinearMap.id ℝ R3) y :=
        (hasFDerivAt_const (𝕜 := ℝ) x₀ y).add (hasFDerivAt_id (𝕜 := ℝ) y)
      rwa [zero_add] at h1
    have hcomp : HasFDerivAt (fun z : R3 => h (x₀ + z))
        ((fderiv ℝ h (x₀ + y)).comp (ContinuousLinearMap.id ℝ R3)) y :=
      hd.hasFDerivAt.comp y htr
    rw [ContinuousLinearMap.comp_id] at hcomp
    exact hcomp.fderiv
  · have hnd : ¬DifferentiableAt ℝ (fun z : R3 => h (x₀ + z)) y := by
      intro hd'
      have htr_inv : HasFDerivAt (fun w : R3 => -x₀ + w) (ContinuousLinearMap.id ℝ R3) (x₀ + y) := by
        have h1 : HasFDerivAt (fun w : R3 => -x₀ + w) (0 + ContinuousLinearMap.id ℝ R3) (x₀ + y) :=
          (hasFDerivAt_const (𝕜 := ℝ) (-x₀) (x₀ + y)).add (hasFDerivAt_id (𝕜 := ℝ) (x₀ + y))
        rwa [zero_add] at h1
      have hy_eq : -x₀ + (x₀ + y) = y := neg_add_cancel_left x₀ y
      have hd'_at : DifferentiableAt ℝ (fun z : R3 => h (x₀ + z)) (-x₀ + (x₀ + y)) := by
        rwa [hy_eq]
      have hcomp : DifferentiableAt ℝ (fun w : R3 => h (x₀ + (-x₀ + w))) (x₀ + y) :=
        DifferentiableAt.comp (g := fun z : R3 => h (x₀ + z)) (f := fun w : R3 => -x₀ + w)
          (x₀ + y) hd'_at htr_inv.differentiableAt
      have heq : (fun w : R3 => h (x₀ + (-x₀ + w))) = h := by
        funext w; rw [add_neg_cancel_left]
      rw [heq] at hcomp
      exact hd hcomp
    rw [fderiv_zero_of_not_differentiableAt hd, fderiv_zero_of_not_differentiableAt hnd]

private lemma decayingH3ScalarR3_translate {f : R3 → ℝ} (hf : DecayingH3ScalarR3 f) (x₀ : R3) :
    DecayingH3ScalarR3 (fun y : R3 => f (x₀ + y)) := by
  have hp1 : ∀ (y : R3) (i : Fin 3),
      partialDerivScalar (fun z => f (x₀ + z)) y i = partialDerivScalar f (x₀ + y) i := fun y i => by
    unfold partialDerivScalar; rw [fderiv_translate_left]
  have hp2 : ∀ (y : R3) (i j : Fin 3),
      sndPartial (fun z => f (x₀ + z)) y i j = sndPartial f (x₀ + y) i j := fun y i j => by
    unfold sndPartial
    have hfd : fderiv ℝ (fun z => f (x₀ + z)) = fun z => fderiv ℝ f (x₀ + z) :=
      funext (fun z => fderiv_translate_left f x₀ z)
    rw [hfd, fderiv_translate_left]
  have hp3 : ∀ (y : R3) (i j k : Fin 3),
      partialDerivScalar (fun z => sndPartial (fun w => f (x₀ + w)) z i j) y k =
        partialDerivScalar (fun z => sndPartial f z i j) (x₀ + y) k := fun y i j k => by
    have hfun : (fun z => sndPartial (fun w => f (x₀ + w)) z i j) =
        fun z => sndPartial f (x₀ + z) i j := funext (fun z => hp2 z i j)
    rw [hfun]
    unfold partialDerivScalar
    exact congrArg (fun L => L (basisVec k)) (fderiv_translate_left (fun z => sndPartial f z i j) x₀ y)
  exact {
    h_c3 := hf.h_c3.comp (contDiff_const.add contDiff_id)
    h_van0 := hf.h_van0.comp (tendsto_add_left_cocompact x₀)
    h_van1 := fun i => by
      have h : (fun y => partialDerivScalar (fun z => f (x₀ + z)) y i) =
          fun y => partialDerivScalar f (x₀ + y) i := funext (fun y => hp1 y i)
      rw [h]; exact (hf.h_van1 i).comp (tendsto_add_left_cocompact x₀)
    h_van2 := fun i j => by
      have h : (fun y => sndPartial (fun z => f (x₀ + z)) y i j) =
          fun y => sndPartial f (x₀ + y) i j := funext (fun y => hp2 y i j)
      rw [h]; exact (hf.h_van2 i j).comp (tendsto_add_left_cocompact x₀)
    h_int0 := hf.h_int0.comp_add_left x₀
    h_int1 := fun i => by
      have h : (fun y => (partialDerivScalar (fun z => f (x₀ + z)) y i) ^ 2) =
          fun y => (partialDerivScalar f (x₀ + y) i) ^ 2 := funext (fun y => by rw [hp1 y i])
      rw [h]; exact (hf.h_int1 i).comp_add_left x₀
    h_int2 := fun i j => by
      have h : (fun y => (sndPartial (fun z => f (x₀ + z)) y i j) ^ 2) =
          fun y => (sndPartial f (x₀ + y) i j) ^ 2 := funext (fun y => by rw [hp2 y i j])
      rw [h]; exact (hf.h_int2 i j).comp_add_left x₀
    h_int3 := fun i j k => by
      have h : (fun y => (partialDerivScalar (fun z => sndPartial (fun w => f (x₀ + w)) z i j) y k) ^ 2) =
          fun y => (partialDerivScalar (fun z => sndPartial f z i j) (x₀ + y) k) ^ 2 :=
        funext (fun y => by rw [hp3 y i j k])
      rw [h]; exact (hf.h_int3 i j k).comp_add_left x₀
  }

/-- **THEOREM 10A2-1 (Unconditional Whole-Space `ℝ³` Scalar Agmon 3D Inequality):**
    For EVERY scalar field `f` in `DecayingH3ScalarR3` and EVERY `x : R3`,
    `f(x)² ≤ (1 / 2) * √(∫_{ℝ³} |∇ f|² dy) * √(∫_{ℝ³} (Δ f)² dy)`. -/
theorem agmon_3d_r3_scalar {f : R3 → ℝ} (hf : DecayingH3ScalarR3 f) (x : R3) :
    (f x) ^ 2 ≤
      (1 / 2 : ℝ) *
        Real.sqrt (r3Integral (fun y =>
          (partialDerivScalar f y 0) ^ 2 + (partialDerivScalar f y 1) ^ 2 +
          (partialDerivScalar f y 2) ^ 2)) *
        Real.sqrt (r3Integral (fun y => (laplacianScalar f y) ^ 2)) := by
  have htr := agmon_3d_r3_scalar_at_zero (decayingH3ScalarR3_translate hf x)
  have h0 : (fun y : R3 => f (x + y)) 0 = f x := by simp
  have hp1 : ∀ (y : R3) (i : Fin 3),
      partialDerivScalar (fun z => f (x + z)) y i = partialDerivScalar f (x + y) i := fun y i => by
    unfold partialDerivScalar; rw [fderiv_translate_left]
  have hp2 : ∀ (y : R3) (i j : Fin 3),
      sndPartial (fun z => f (x + z)) y i j = sndPartial f (x + y) i j := fun y i j => by
    unfold sndPartial
    have hfd : fderiv ℝ (fun z => f (x + z)) = fun z => fderiv ℝ f (x + z) :=
      funext (fun z => fderiv_translate_left f x z)
    rw [hfd, fderiv_translate_left]
  have hG_eq : r3Integral (fun y =>
      (partialDerivScalar (fun z => f (x + z)) y 0) ^ 2 +
      (partialDerivScalar (fun z => f (x + z)) y 1) ^ 2 +
      (partialDerivScalar (fun z => f (x + z)) y 2) ^ 2) =
      r3Integral (fun y =>
        (partialDerivScalar f y 0) ^ 2 + (partialDerivScalar f y 1) ^ 2 +
        (partialDerivScalar f y 2) ^ 2) := by
    have hpt : (fun y =>
        (partialDerivScalar (fun z => f (x + z)) y 0) ^ 2 +
        (partialDerivScalar (fun z => f (x + z)) y 1) ^ 2 +
        (partialDerivScalar (fun z => f (x + z)) y 2) ^ 2) =
        fun y => (partialDerivScalar f (x + y) 0) ^ 2 +
          (partialDerivScalar f (x + y) 1) ^ 2 + (partialDerivScalar f (x + y) 2) ^ 2 :=
      funext (fun y => by rw [hp1 y 0, hp1 y 1, hp1 y 2])
    rw [hpt]
    exact MeasureTheory.integral_add_left_eq_self
      (fun y => (partialDerivScalar f y 0) ^ 2 + (partialDerivScalar f y 1) ^ 2 +
        (partialDerivScalar f y 2) ^ 2) x
  have hL_eq : r3Integral (fun y => (laplacianScalar (fun z => f (x + z)) y) ^ 2) =
      r3Integral (fun y => (laplacianScalar f y) ^ 2) := by
    have hpt : (fun y => (laplacianScalar (fun z => f (x + z)) y) ^ 2) =
        fun y => (laplacianScalar f (x + y)) ^ 2 :=
      funext (fun y => by unfold laplacianScalar; rw [hp2 y 0 0, hp2 y 1 1, hp2 y 2 2])
    rw [hpt]
    exact MeasureTheory.integral_add_left_eq_self (fun y => (laplacianScalar f y) ^ 2) x
  rw [add_zero, hG_eq, hL_eq] at htr
  exact htr

-- ============================================================================
-- SECTION 5: VECTOR AGMON 3D & UNCONDITIONAL VORTEX STRETCHING BOUND ON ℝ³
-- ============================================================================

/-- **THEOREM 10A2-2 (Unconditional Whole-Space `ℝ³` Vector Agmon 3D Inequality):**
    For EVERY `u` in `DecayingH3SolenoidalR3` and EVERY `x : R3`,
    `|u(x)|² ≤ (1 / 2) * √(2 Z_{ℝ³}(u)) * √(P_{ℝ³}(u))`. -/
theorem agmon_3d_r3_ns_velocity {u : R3 → R3} (hu : DecayingH3SolenoidalR3 u) (x : R3) :
    dot3D (u x) (u x) ≤
      (1 / 2 : ℝ) *
        Real.sqrt (r3Integral (fun y => dot3D (curl3D u y) (curl3D u y))) *
        Real.sqrt (palinstrophyR3 u) := by
  let G : Fin 3 → ℝ := fun c =>
    r3Integral (fun y =>
      (partialDerivScalar (fun z => u z c) y 0) ^ 2 +
      (partialDerivScalar (fun z => u z c) y 1) ^ 2 +
      (partialDerivScalar (fun z => u z c) y 2) ^ 2)
  let L : Fin 3 → ℝ := fun c =>
    r3Integral (fun y => (laplacianScalar (fun z => u z c) y) ^ 2)
  have hG_nn : ∀ c : Fin 3, 0 ≤ G c := fun c => r3Integral_nonneg (fun _ => by positivity)
  have hL_nn : ∀ c : Fin 3, 0 ≤ L c := fun c => r3Integral_nonneg (fun _ => sq_nonneg _)
  have hag : ∀ c : Fin 3, (u x c) ^ 2 ≤ (1 / 2 : ℝ) * Real.sqrt (G c) * Real.sqrt (L c) :=
    fun c => agmon_3d_r3_scalar (hu.h_comp c) x
  have hG_sum : G 0 + G 1 + G 2 = r3Integral (fun y => dot3D (curl3D u y) (curl3D u y)) := by
    rw [r3_enstrophy_eq_half_gradNormSq hu]
    dsimp only [G]
    rw [← r3Integral_add3
          (int_add_ag (int_add_ag ((hu.h_comp 0).h_int1 0) ((hu.h_comp 0).h_int1 1)) ((hu.h_comp 0).h_int1 2))
          (int_add_ag (int_add_ag ((hu.h_comp 1).h_int1 0) ((hu.h_comp 1).h_int1 1)) ((hu.h_comp 1).h_int1 2))
          (int_add_ag (int_add_ag ((hu.h_comp 2).h_int1 0) ((hu.h_comp 2).h_int1 1)) ((hu.h_comp 2).h_int1 2))]
    apply r3Integral_congr
    intro y; unfold gradNormSqR3; ring
  have hl_int : ∀ c : Fin 3, Integrable (fun y => (laplacianScalar (fun z => u z c) y) ^ 2) volume := by
    intro c
    have hc_s : ∀ i : Fin 3, Continuous (fun y => sndPartial (fun z => u z c) y i i) := fun i =>
      (contDiff_snd_c1_ag (hu.h_comp c).h_c3 i i).continuous
    unfold laplacianScalar
    exact integrable_add_sq_of_sq ((hc_s 0).add (hc_s 1)) (hc_s 2)
      (integrable_add_sq_of_sq (hc_s 0) (hc_s 1) ((hu.h_comp c).h_int2 0 0) ((hu.h_comp c).h_int2 1 1))
      ((hu.h_comp c).h_int2 2 2)
  have hL_sum : L 0 + L 1 + L 2 = palinstrophyR3 u := by
    rw [r3_palinstrophy_eq_laplacianNormSq hu]
    dsimp only [L]
    rw [← r3Integral_add3 (hl_int 0) (hl_int 1) (hl_int 2)]
    apply r3Integral_congr
    intro y; unfold dot3D laplacian3D; ring
  have hcs := cauchy_schwarz_3_nonneg_r3 (hG_nn 0) (hG_nn 1) (hG_nn 2) (hL_nn 0) (hL_nn 1) (hL_nn 2)
  rw [hG_sum, hL_sum] at hcs
  have hdot_sq : dot3D (u x) (u x) = (u x 0) ^ 2 + (u x 1) ^ 2 + (u x 2) ^ 2 := by
    unfold dot3D; ring
  rw [hdot_sq]
  linarith [hag 0, hag 1, hag 2]

private lemma pointwise_stretch_sq_le_r3 (u ω : R3)
    (dw00 dw01 dw02 dw10 dw11 dw12 dw20 dw21 dw22 : ℝ) :
    (u 0 * (ω 0 * dw00 + ω 1 * dw01 + ω 2 * dw02) +
     u 1 * (ω 0 * dw10 + ω 1 * dw11 + ω 2 * dw12) +
     u 2 * (ω 0 * dw20 + ω 1 * dw21 + ω 2 * dw22)) ^ 2 ≤
      dot3D u u * dot3D ω ω *
        (dw00 ^ 2 + dw01 ^ 2 + dw02 ^ 2 +
         dw10 ^ 2 + dw11 ^ 2 + dw12 ^ 2 +
         dw20 ^ 2 + dw21 ^ 2 + dw22 ^ 2) := by
  let b0 := ω 0 * dw00 + ω 1 * dw01 + ω 2 * dw02
  let b1 := ω 0 * dw10 + ω 1 * dw11 + ω 2 * dw12
  let b2 := ω 0 * dw20 + ω 1 * dw21 + ω 2 * dw22
  have hcs_u : (u 0 * b0 + u 1 * b1 + u 2 * b2) ^ 2 ≤
      dot3D u u * (b0 ^ 2 + b1 ^ 2 + b2 ^ 2) := by
    unfold dot3D
    nlinarith [sq_nonneg (u 0 * b1 - u 1 * b0),
               sq_nonneg (u 0 * b2 - u 2 * b0),
               sq_nonneg (u 1 * b2 - u 2 * b1)]
  have hb0 : b0 ^ 2 ≤ dot3D ω ω * (dw00 ^ 2 + dw01 ^ 2 + dw02 ^ 2) := by
    unfold dot3D; dsimp only [b0]
    nlinarith [sq_nonneg (ω 0 * dw01 - ω 1 * dw00),
               sq_nonneg (ω 0 * dw02 - ω 2 * dw00),
               sq_nonneg (ω 1 * dw02 - ω 2 * dw01)]
  have hb1 : b1 ^ 2 ≤ dot3D ω ω * (dw10 ^ 2 + dw11 ^ 2 + dw12 ^ 2) := by
    unfold dot3D; dsimp only [b1]
    nlinarith [sq_nonneg (ω 0 * dw11 - ω 1 * dw10),
               sq_nonneg (ω 0 * dw12 - ω 2 * dw10),
               sq_nonneg (ω 1 * dw12 - ω 2 * dw11)]
  have hb2 : b2 ^ 2 ≤ dot3D ω ω * (dw20 ^ 2 + dw21 ^ 2 + dw22 ^ 2) := by
    unfold dot3D; dsimp only [b2]
    nlinarith [sq_nonneg (ω 0 * dw21 - ω 1 * dw20),
               sq_nonneg (ω 0 * dw22 - ω 2 * dw20),
               sq_nonneg (ω 1 * dw22 - ω 2 * dw21)]
  have hu_nn : 0 ≤ dot3D u u := dot3D_self_nonneg_r3 u
  have hsum : b0 ^ 2 + b1 ^ 2 + b2 ^ 2 ≤
      dot3D ω ω * (dw00 ^ 2 + dw01 ^ 2 + dw02 ^ 2 +
        dw10 ^ 2 + dw11 ^ 2 + dw12 ^ 2 + dw20 ^ 2 + dw21 ^ 2 + dw22 ^ 2) := by linarith
  have hmul := mul_le_mul_of_nonneg_left hsum hu_nn
  linarith

/-- **THEOREM 10A2-3 (Unconditional Whole-Space `ℝ³` 3D Vortex Stretching Bound):**
    For EVERY `u` in `DecayingH3SolenoidalR3`, with ZERO extra hypotheses, ZERO compactness,
    and ZERO mean-zero requirement:
    `|vortexStretchingR3 u| ≤ C3D_agmon_R3 * Z_{ℝ³}^{3/4} * P_{ℝ³}^{3/4}`,
    where `C3D_agmon_R3 = 2^{1/4}` (`C3D_agmon_R3⁴ = 2`). -/
theorem unconditional_vortexStretching_le_agmon_r3 {u : R3 → R3} (hu : DecayingH3SolenoidalR3 u) :
    let Z : ℝ := enstrophyR3 u
    let P : ℝ := palinstrophyR3 u
    |vortexStretchingR3 u| ≤
      C3D_agmon_R3 * (Real.sqrt (Real.sqrt Z)) ^ 3 * (Real.sqrt (Real.sqrt P)) ^ 3 := by
  intro Z P
  have hu_c2 : ∀ c : Fin 3, ContDiff ℝ 2 (fun x => u x c) := fun c =>
    (hu.h_comp c).h_c3.of_le (by exact_mod_cast (show (2 : ℕ) ≤ 3 by decide))
  have hc_du : ∀ c i : Fin 3, Continuous (fun x => partialDerivScalar (fun y => u y c) x i) := fun c i =>
    (contDiff_partial_c2_ag (hu.h_comp c).h_c3 i).continuous
  have hc_snd : ∀ c i j : Fin 3, Continuous (fun x => sndPartial (fun y => u y c) x i j) := fun c i j =>
    (contDiff_snd_c1_ag (hu.h_comp c).h_c3 i j).continuous
  have hw_cont : ∀ c : Fin 3, Continuous (fun x => curl3D u x c) := fun c => by
    fin_cases c
    · change Continuous (fun x => curl3D u x 0)
      have h : (fun x => curl3D u x 0) = fun x =>
          partialDerivScalar (fun y => u y 2) x 1 - partialDerivScalar (fun y => u y 1) x 2 :=
        funext (curl3D_zero_ag u)
      rw [h]; exact (hc_du 2 1).sub (hc_du 1 2)
    · change Continuous (fun x => curl3D u x 1)
      have h : (fun x => curl3D u x 1) = fun x =>
          partialDerivScalar (fun y => u y 0) x 2 - partialDerivScalar (fun y => u y 2) x 0 :=
        funext (curl3D_one_ag u)
      rw [h]; exact (hc_du 0 2).sub (hc_du 2 0)
    · change Continuous (fun x => curl3D u x 2)
      have h : (fun x => curl3D u x 2) = fun x =>
          partialDerivScalar (fun y => u y 1) x 0 - partialDerivScalar (fun y => u y 0) x 1 :=
        funext (curl3D_two_ag u)
      rw [h]; exact (hc_du 1 0).sub (hc_du 0 1)
  have hw_int0 : ∀ c : Fin 3, Integrable (fun x => (curl3D u x c) ^ 2) volume := fun c => by
    fin_cases c
    · change Integrable (fun x => (curl3D u x 0) ^ 2) volume
      have h : (fun x => (curl3D u x 0) ^ 2) = fun x =>
          (partialDerivScalar (fun y => u y 2) x 1 - partialDerivScalar (fun y => u y 1) x 2) ^ 2 :=
        funext (fun x => by rw [curl3D_zero_ag])
      rw [h]; exact integrable_sub_sq_of_sq (hc_du 2 1) (hc_du 1 2) ((hu.h_comp 2).h_int1 1) ((hu.h_comp 1).h_int1 2)
    · change Integrable (fun x => (curl3D u x 1) ^ 2) volume
      have h : (fun x => (curl3D u x 1) ^ 2) = fun x =>
          (partialDerivScalar (fun y => u y 0) x 2 - partialDerivScalar (fun y => u y 2) x 0) ^ 2 :=
        funext (fun x => by rw [curl3D_one_ag])
      rw [h]; exact integrable_sub_sq_of_sq (hc_du 0 2) (hc_du 2 0) ((hu.h_comp 0).h_int1 2) ((hu.h_comp 2).h_int1 0)
    · change Integrable (fun x => (curl3D u x 2) ^ 2) volume
      have h : (fun x => (curl3D u x 2) ^ 2) = fun x =>
          (partialDerivScalar (fun y => u y 1) x 0 - partialDerivScalar (fun y => u y 0) x 1) ^ 2 :=
        funext (fun x => by rw [curl3D_two_ag])
      rw [h]; exact integrable_sub_sq_of_sq (hc_du 1 0) (hc_du 0 1) ((hu.h_comp 1).h_int1 0) ((hu.h_comp 0).h_int1 1)
  have hdw_eq : ∀ c i : Fin 3,
      (fun x => partialDerivScalar (fun y => curl3D u y c) x i) =
        match c with
        | 0 => fun x => sndPartial (fun y => u y 2) x i 1 - sndPartial (fun y => u y 1) x i 2
        | 1 => fun x => sndPartial (fun y => u y 0) x i 2 - sndPartial (fun y => u y 2) x i 0
        | 2 => fun x => sndPartial (fun y => u y 1) x i 0 - sndPartial (fun y => u y 0) x i 1 := by
    intro c i; funext x
    have hd_du : ∀ a b : Fin 3, DifferentiableAt ℝ (fun y => partialDerivScalar (fun z => u z a) y b) x :=
      fun a b => (contDiff_partial_c2_ag (hu.h_comp a).h_c3 b).differentiable (by simp) x
    fin_cases c
    · change partialDerivScalar (fun y => curl3D u y 0) x i = _
      have h0 : (fun y => curl3D u y 0) = fun y =>
          partialDerivScalar (fun z => u z 2) y 1 - partialDerivScalar (fun z => u z 1) y 2 :=
        funext (curl3D_zero_ag u)
      rw [h0, partialDerivScalar_sub (hd_du 2 1) (hd_du 1 2) i,
          partial_partial_eq_sndPartial (fun z => u z 2) x (hu_c2 2).contDiffAt i 1,
          partial_partial_eq_sndPartial (fun z => u z 1) x (hu_c2 1).contDiffAt i 2]
    · change partialDerivScalar (fun y => curl3D u y 1) x i = _
      have h1 : (fun y => curl3D u y 1) = fun y =>
          partialDerivScalar (fun z => u z 0) y 2 - partialDerivScalar (fun z => u z 2) y 0 :=
        funext (curl3D_one_ag u)
      rw [h1, partialDerivScalar_sub (hd_du 0 2) (hd_du 2 0) i,
          partial_partial_eq_sndPartial (fun z => u z 0) x (hu_c2 0).contDiffAt i 2,
          partial_partial_eq_sndPartial (fun z => u z 2) x (hu_c2 2).contDiffAt i 0]
    · change partialDerivScalar (fun y => curl3D u y 2) x i = _
      have h2 : (fun y => curl3D u y 2) = fun y =>
          partialDerivScalar (fun z => u z 1) y 0 - partialDerivScalar (fun z => u z 0) y 1 :=
        funext (curl3D_two_ag u)
      rw [h2, partialDerivScalar_sub (hd_du 1 0) (hd_du 0 1) i,
          partial_partial_eq_sndPartial (fun z => u z 1) x (hu_c2 1).contDiffAt i 0,
          partial_partial_eq_sndPartial (fun z => u z 0) x (hu_c2 0).contDiffAt i 1]
  have hdw_cont : ∀ c i : Fin 3, Continuous (fun x => partialDerivScalar (fun y => curl3D u y c) x i) := by
    intro c i; rw [hdw_eq c i]
    fin_cases c
    · exact (hc_snd 2 i 1).sub (hc_snd 1 i 2)
    · exact (hc_snd 0 i 2).sub (hc_snd 2 i 0)
    · exact (hc_snd 1 i 0).sub (hc_snd 0 i 1)
  have hdw_int : ∀ c i : Fin 3,
      Integrable (fun x => (partialDerivScalar (fun y => curl3D u y c) x i) ^ 2) volume := by
    intro c i
    have h : (fun x => (partialDerivScalar (fun y => curl3D u y c) x i) ^ 2) =
        fun x => ((fun z => partialDerivScalar (fun y => curl3D u y c) z i) x) ^ 2 := rfl
    rw [h, hdw_eq c i]
    fin_cases c
    · exact integrable_sub_sq_of_sq (hc_snd 2 i 1) (hc_snd 1 i 2) ((hu.h_comp 2).h_int2 i 1) ((hu.h_comp 1).h_int2 i 2)
    · exact integrable_sub_sq_of_sq (hc_snd 0 i 2) (hc_snd 2 i 0) ((hu.h_comp 0).h_int2 i 2) ((hu.h_comp 2).h_int2 i 0)
    · exact integrable_sub_sq_of_sq (hc_snd 1 i 0) (hc_snd 0 i 1) ((hu.h_comp 1).h_int2 i 0) ((hu.h_comp 0).h_int2 i 1)
  have hint_w2 : Integrable (fun x => dot3D (curl3D u x) (curl3D u x)) volume := by
    have hpt : (fun x => dot3D (curl3D u x) (curl3D u x)) =
        fun x => (curl3D u x 0) ^ 2 + (curl3D u x 1) ^ 2 + (curl3D u x 2) ^ 2 := by
      funext x; unfold dot3D; ring
    rw [hpt]; exact int_add_ag (int_add_ag (hw_int0 0) (hw_int0 1)) (hw_int0 2)
  have hint_gw : Integrable (gradNormSqR3 (curl3D u)) volume := by
    unfold gradNormSqR3
    exact int_add_ag (int_add_ag (int_add_ag (int_add_ag (int_add_ag (int_add_ag (int_add_ag (int_add_ag
      (hdw_int 0 0) (hdw_int 0 1)) (hdw_int 0 2)) (hdw_int 1 0)) (hdw_int 1 1)) (hdw_int 1 2))
      (hdw_int 2 0)) (hdw_int 2 1)) (hdw_int 2 2)
  have hu_bdd : ∀ c : Fin 3, ∃ C : ℝ, 0 ≤ C ∧ ∀ x : R3, |u x c| ≤ C := fun c =>
    exists_bound_of_vanishesAtInfinityR3 (hu.h_comp c).h_c3.continuous (hu.h_comp c).h_van0
  have hint_ibp : Integrable (fun x => dot3D (u x) (directionalAdvection3D (curl3D u) (curl3D u) x)) volume := by
    have ht : ∀ c i : Fin 3,
        Integrable (fun x => u x c * (curl3D u x i * partialDerivScalar (fun y => curl3D u y c) x i)) volume :=
      fun c i => integrable_bdd_mul_mul_of_sq (hu.h_comp c).h_c3.continuous (hw_cont i)
        (hdw_cont c i) (hu_bdd c) (hw_int0 i) (hdw_int c i)
    have hpt : (fun x => dot3D (u x) (directionalAdvection3D (curl3D u) (curl3D u) x)) =
        fun x =>
          (u x 0 * (curl3D u x 0 * partialDerivScalar (fun y => curl3D u y 0) x 0) +
           u x 0 * (curl3D u x 1 * partialDerivScalar (fun y => curl3D u y 0) x 1) +
           u x 0 * (curl3D u x 2 * partialDerivScalar (fun y => curl3D u y 0) x 2)) +
          (u x 1 * (curl3D u x 0 * partialDerivScalar (fun y => curl3D u y 1) x 0) +
           u x 1 * (curl3D u x 1 * partialDerivScalar (fun y => curl3D u y 1) x 1) +
           u x 1 * (curl3D u x 2 * partialDerivScalar (fun y => curl3D u y 1) x 2)) +
          (u x 2 * (curl3D u x 0 * partialDerivScalar (fun y => curl3D u y 2) x 0) +
           u x 2 * (curl3D u x 1 * partialDerivScalar (fun y => curl3D u y 2) x 1) +
           u x 2 * (curl3D u x 2 * partialDerivScalar (fun y => curl3D u y 2) x 2)) := by
      funext x; unfold dot3D directionalAdvection3D; ring
    rw [hpt]
    exact int_add_ag
      (int_add_ag (int_add_ag (int_add_ag (ht 0 0) (ht 0 1)) (ht 0 2))
        (int_add_ag (int_add_ag (ht 1 0) (ht 1 1)) (ht 1 2)))
      (int_add_ag (int_add_ag (ht 2 0) (ht 2 1)) (ht 2 2))
  have h2Z_nn : 0 ≤ r3Integral (fun x => dot3D (curl3D u x) (curl3D u x)) :=
    r3Integral_nonneg (fun x => dot3D_self_nonneg_r3 _)
  have hZ_nn : 0 ≤ Z := by dsimp only [Z, enstrophyR3]; linarith
  have hP_nn : 0 ≤ P := r3Integral_nonneg (fun x => gradNormSqR3_nonneg _ _)
  let M : ℝ := (1 / 2 : ℝ) *
      Real.sqrt (r3Integral (fun x => dot3D (curl3D u x) (curl3D u x))) * Real.sqrt P
  have hM_nn : 0 ≤ M := by dsimp only [M]; positivity
  have hpt_sq : ∀ x : R3,
      (dot3D (u x) (directionalAdvection3D (curl3D u) (curl3D u) x)) ^ 2 ≤
        M * dot3D (curl3D u x) (curl3D u x) * gradNormSqR3 (curl3D u) x := fun x => by
    have h1 := pointwise_stretch_sq_le_r3 (u x) (curl3D u x)
      (partialDerivScalar (fun y => curl3D u y 0) x 0)
      (partialDerivScalar (fun y => curl3D u y 0) x 1)
      (partialDerivScalar (fun y => curl3D u y 0) x 2)
      (partialDerivScalar (fun y => curl3D u y 1) x 0)
      (partialDerivScalar (fun y => curl3D u y 1) x 1)
      (partialDerivScalar (fun y => curl3D u y 1) x 2)
      (partialDerivScalar (fun y => curl3D u y 2) x 0)
      (partialDerivScalar (fun y => curl3D u y 2) x 1)
      (partialDerivScalar (fun y => curl3D u y 2) x 2)
    have h2 : dot3D (u x) (u x) ≤ M := agmon_3d_r3_ns_velocity hu x
    have hwg_nn : 0 ≤ dot3D (curl3D u x) (curl3D u x) * gradNormSqR3 (curl3D u) x :=
      mul_nonneg (dot3D_self_nonneg_r3 _) (gradNormSqR3_nonneg _ _)
    have hmul := mul_le_mul_of_nonneg_right h2 hwg_nn
    change (u x 0 * (curl3D u x 0 * partialDerivScalar (fun y => curl3D u y 0) x 0 +
      curl3D u x 1 * partialDerivScalar (fun y => curl3D u y 0) x 1 +
      curl3D u x 2 * partialDerivScalar (fun y => curl3D u y 0) x 2) +
      u x 1 * (curl3D u x 0 * partialDerivScalar (fun y => curl3D u y 1) x 0 +
      curl3D u x 1 * partialDerivScalar (fun y => curl3D u y 1) x 1 +
      curl3D u x 2 * partialDerivScalar (fun y => curl3D u y 1) x 2) +
      u x 2 * (curl3D u x 0 * partialDerivScalar (fun y => curl3D u y 2) x 0 +
      curl3D u x 1 * partialDerivScalar (fun y => curl3D u y 2) x 1 +
      curl3D u x 2 * partialDerivScalar (fun y => curl3D u y 2) x 2)) ^ 2 ≤ _
    rw [← mul_assoc, ← mul_assoc] at hmul
    unfold gradNormSqR3 at hmul ⊢
    linarith
  by_cases hM0 : M = 0
  · have hzero : ∀ x : R3, dot3D (u x) (directionalAdvection3D (curl3D u) (curl3D u) x) = 0 := by
      intro x
      have hsq := hpt_sq x; rw [hM0] at hsq
      nlinarith [sq_nonneg (dot3D (u x) (directionalAdvection3D (curl3D u) (curl3D u) x))]
    rw [r3_vortexStretching_eq_neg_ibp hu, r3Integral_congr hzero, r3Integral_zero, neg_zero, abs_zero]
    exact mul_nonneg (mul_nonneg C3D_agmon_R3_nonneg (by positivity)) (by positivity)
  · have hM_pos : 0 < M := lt_of_le_of_ne hM_nn (Ne.symm hM0)
    have hZ_pos : 0 < Z := by
      by_contra hle; push Not at hle
      have hZ0 : Z = 0 := le_antisymm hle hZ_nn
      have h2Z0 : r3Integral (fun x => dot3D (curl3D u x) (curl3D u x)) = 0 := by
        dsimp only [Z, enstrophyR3] at hZ0; linarith
      have : M = 0 := by dsimp only [M]; rw [h2Z0, Real.sqrt_zero]; ring
      exact hM0 this
    have hP_pos : 0 < P := by
      by_contra hle; push Not at hle
      have hP0 : P = 0 := le_antisymm hle hP_nn
      have : M = 0 := by dsimp only [M]; rw [hP0, Real.sqrt_zero]; ring
      exact hM0 this
    let α : ℝ := Real.sqrt (M * P / (2 * Z))
    have hα_pos : 0 < α := Real.sqrt_pos.mpr (by positivity)
    have hpt_amgm : ∀ x : R3,
        dot3D (u x) (directionalAdvection3D (curl3D u) (curl3D u) x) ≤
          (α / 2) * dot3D (curl3D u x) (curl3D u x) + (M / (2 * α)) * gradNormSqR3 (curl3D u) x ∧
        -(dot3D (u x) (directionalAdvection3D (curl3D u) (curl3D u) x)) ≤
          (α / 2) * dot3D (curl3D u x) (curl3D u x) + (M / (2 * α)) * gradNormSqR3 (curl3D u) x := by
      intro x
      set S := dot3D (u x) (directionalAdvection3D (curl3D u) (curl3D u) x)
      set W := dot3D (curl3D u x) (curl3D u x)
      set Gx := gradNormSqR3 (curl3D u) x
      have hW : 0 ≤ W := dot3D_self_nonneg_r3 _
      have hGx : 0 ≤ Gx := gradNormSqR3_nonneg _ _
      have hR_nn : 0 ≤ (α / 2) * W + (M / (2 * α)) * Gx := by positivity
      have hdiff : ((α / 2) * W + (M / (2 * α)) * Gx) ^ 2 - M * W * Gx =
          ((α / 2) * W - (M / (2 * α)) * Gx) ^ 2 := by
        have hα0 : α ≠ 0 := ne_of_gt hα_pos; field_simp; ring
      have hsq_le : S ^ 2 ≤ ((α / 2) * W + (M / (2 * α)) * Gx) ^ 2 := by
        have h1 := hpt_sq x
        nlinarith [sq_nonneg ((α / 2) * W - (M / (2 * α)) * Gx)]
      constructor <;> nlinarith
    have hint_rhs_fn : Integrable (fun x =>
        (α / 2) * dot3D (curl3D u x) (curl3D u x) + (M / (2 * α)) * gradNormSqR3 (curl3D u) x) volume :=
      int_add_ag (int_const_mul_ag (α / 2) hint_w2) (int_const_mul_ag (M / (2 * α)) hint_gw)
    have hint_rhs_eq : r3Integral (fun x =>
        (α / 2) * dot3D (curl3D u x) (curl3D u x) + (M / (2 * α)) * gradNormSqR3 (curl3D u) x) =
        α * Z + (M / (2 * α)) * P := by
      rw [r3Integral_add (int_const_mul_ag (α / 2) hint_w2) (int_const_mul_ag (M / (2 * α)) hint_gw),
          r3Integral_const_mul, r3Integral_const_mul]
      dsimp only [Z, P, enstrophyR3, palinstrophyR3]; ring
    have hpos_le : r3Integral (fun x => dot3D (u x) (directionalAdvection3D (curl3D u) (curl3D u) x)) ≤
        α * Z + (M / (2 * α)) * P := by
      rw [← hint_rhs_eq]
      exact MeasureTheory.integral_mono hint_ibp hint_rhs_fn (fun x => (hpt_amgm x).1)
    have hneg_le : -r3Integral (fun x => dot3D (u x) (directionalAdvection3D (curl3D u) (curl3D u) x)) ≤
        α * Z + (M / (2 * α)) * P := by
      rw [← r3Integral_neg, ← hint_rhs_eq]
      exact MeasureTheory.integral_mono hint_ibp.neg hint_rhs_fn (fun x => (hpt_amgm x).2)
    have habs_le : |vortexStretchingR3 u| ≤ α * Z + (M / (2 * α)) * P := by
      rw [r3_vortexStretching_eq_neg_ibp hu, abs_neg, abs_le]
      exact ⟨by linarith, hpos_le⟩
    have h_eq : α * Z + (M / (2 * α)) * P =
        C3D_agmon_R3 * (Real.sqrt (Real.sqrt Z)) ^ 3 * (Real.sqrt (Real.sqrt P)) ^ 3 := by
      have hL_nn : 0 ≤ α * Z + (M / (2 * α)) * P := by positivity
      have hR_nn : 0 ≤ C3D_agmon_R3 * (Real.sqrt (Real.sqrt Z)) ^ 3 * (Real.sqrt (Real.sqrt P)) ^ 3 :=
        mul_nonneg (mul_nonneg C3D_agmon_R3_nonneg (by positivity)) (by positivity)
      have hsq_eq : (α * Z + (M / (2 * α)) * P) ^ 2 =
          (C3D_agmon_R3 * (Real.sqrt (Real.sqrt Z)) ^ 3 * (Real.sqrt (Real.sqrt P)) ^ 3) ^ 2 := by
        have hα2 : α ^ 2 = M * P / (2 * Z) := Real.sq_sqrt (by positivity)
        have hα0 : α ≠ 0 := ne_of_gt hα_pos
        have hZ0 : Z ≠ 0 := ne_of_gt hZ_pos
        have hL2 : (α * Z + (M / (2 * α)) * P) ^ 2 = 2 * M * Z * P := by
          have hexp : (α * Z + (M / (2 * α)) * P) ^ 2 =
              α ^ 2 * Z ^ 2 + M * P * Z + M ^ 2 * P ^ 2 / (4 * α ^ 2) := by field_simp; ring
          rw [hexp, hα2]; field_simp; ring
        have hZ32 : ((Real.sqrt (Real.sqrt Z)) ^ 3) ^ 2 = Z * Real.sqrt Z := by
          calc ((Real.sqrt (Real.sqrt Z)) ^ 3) ^ 2 = ((Real.sqrt (Real.sqrt Z)) ^ 2) ^ 3 := by ring
            _ = (Real.sqrt Z) ^ 3 := by rw [Real.sq_sqrt (Real.sqrt_nonneg _)]
            _ = (Real.sqrt Z) ^ 2 * Real.sqrt Z := by ring
            _ = Z * Real.sqrt Z := by rw [Real.sq_sqrt hZ_nn]
        have hP32 : ((Real.sqrt (Real.sqrt P)) ^ 3) ^ 2 = P * Real.sqrt P := by
          calc ((Real.sqrt (Real.sqrt P)) ^ 3) ^ 2 = ((Real.sqrt (Real.sqrt P)) ^ 2) ^ 3 := by ring
            _ = (Real.sqrt P) ^ 3 := by rw [Real.sq_sqrt (Real.sqrt_nonneg _)]
            _ = (Real.sqrt P) ^ 2 * Real.sqrt P := by ring
            _ = P * Real.sqrt P := by rw [Real.sq_sqrt hP_nn]
        have h2Z_eq : r3Integral (fun x => dot3D (curl3D u x) (curl3D u x)) = 2 * Z := by
          dsimp only [Z, enstrophyR3]; ring
        have hsq2Z : Real.sqrt (2 * Z) = Real.sqrt 2 * Real.sqrt Z := Real.sqrt_mul (by norm_num) Z
        rw [hL2]
        calc 2 * M * Z * P
            = 2 * ((1 / 2 : ℝ) * (Real.sqrt 2 * Real.sqrt Z) * Real.sqrt P) * Z * P := by
                dsimp only [M]; rw [h2Z_eq, hsq2Z]
          _ = Real.sqrt 2 * (Z * Real.sqrt Z) * (P * Real.sqrt P) := by ring
          _ = C3D_agmon_R3 ^ 2 * ((Real.sqrt (Real.sqrt Z)) ^ 3) ^ 2 *
                ((Real.sqrt (Real.sqrt P)) ^ 3) ^ 2 := by
                rw [C3D_agmon_R3_pow_two, hZ32, hP32]
          _ = (C3D_agmon_R3 * (Real.sqrt (Real.sqrt Z)) ^ 3 * (Real.sqrt (Real.sqrt P)) ^ 3) ^ 2 := by
                ring
      nlinarith
    linarith

/-- **COROLLARY 10A2-4 (Unconditional Young Absorption on Whole Space `ℝ³` — Bridge to 10B):**
    For EVERY `u` in `DecayingH3SolenoidalR3` and EVERY viscosity `ν > 0`:
    `|vortexStretchingR3 u| ≤ (3 * ν / 4) * palinstrophyR3 u + c_nu_R3 ν * (enstrophyR3 u)³`,
    where `c_nu_R3 ν = 1 / (2 ν³)`. -/
theorem unconditional_r3_stretching_young_absorption
    {u : R3 → R3} (hu : DecayingH3SolenoidalR3 u) {ν : ℝ} (hν : 0 < ν) :
    |vortexStretchingR3 u| ≤
      (3 * ν / 4) * palinstrophyR3 u + c_nu_R3 ν * (enstrophyR3 u) ^ 3 := by
  set Z := enstrophyR3 u
  set P := palinstrophyR3 u
  have hZ_nn : 0 ≤ Z := by
    dsimp only [Z, enstrophyR3]; linarith [r3Integral_nonneg (fun x => dot3D_self_nonneg_r3 (curl3D u x))]
  have hP_nn : 0 ≤ P := r3Integral_nonneg (fun x => gradNormSqR3_nonneg (curl3D u) x)
  have hstr := unconditional_vortexStretching_le_agmon_r3 hu
  let A : ℝ := Real.sqrt (Real.sqrt (ν * P))
  let B : ℝ := Real.sqrt (Real.sqrt (4 * c_nu_R3 ν * Z ^ 3))
  have hA_nn : 0 ≤ A := Real.sqrt_nonneg _
  have hB_nn : 0 ≤ B := Real.sqrt_nonneg _
  have hA4 : A ^ 4 = ν * P := by
    dsimp only [A]
    calc (Real.sqrt (Real.sqrt (ν * P))) ^ 4 = ((Real.sqrt (Real.sqrt (ν * P))) ^ 2) ^ 2 := by ring
      _ = (Real.sqrt (ν * P)) ^ 2 := by rw [Real.sq_sqrt (Real.sqrt_nonneg _)]
      _ = ν * P := Real.sq_sqrt (by positivity)
  have hB4 : B ^ 4 = 4 * c_nu_R3 ν * Z ^ 3 := by
    dsimp only [B]
    have hc_pos : 0 < c_nu_R3 ν := c_nu_R3_pos hν
    calc (Real.sqrt (Real.sqrt (4 * c_nu_R3 ν * Z ^ 3))) ^ 4
        = ((Real.sqrt (Real.sqrt (4 * c_nu_R3 ν * Z ^ 3))) ^ 2) ^ 2 := by ring
      _ = (Real.sqrt (4 * c_nu_R3 ν * Z ^ 3)) ^ 2 := by rw [Real.sq_sqrt (Real.sqrt_nonneg _)]
      _ = 4 * c_nu_R3 ν * Z ^ 3 := Real.sq_sqrt (by positivity)
  have hamgm : A ^ 3 * B ≤ (3 / 4 : ℝ) * A ^ 4 + (1 / 4 : ℝ) * B ^ 4 := by
    have hdiff : 3 * A ^ 4 + B ^ 4 - 4 * A ^ 3 * B = (A - B) ^ 2 * (3 * A ^ 2 + 2 * A * B + B ^ 2) := by
      ring
    have hnn : 0 ≤ (A - B) ^ 2 * (3 * A ^ 2 + 2 * A * B + B ^ 2) :=
      mul_nonneg (sq_nonneg _) (by positivity)
    linarith
  have hprod_eq : C3D_agmon_R3 * (Real.sqrt (Real.sqrt Z)) ^ 3 * (Real.sqrt (Real.sqrt P)) ^ 3 =
      A ^ 3 * B := by
    have hL_nn : 0 ≤ C3D_agmon_R3 * (Real.sqrt (Real.sqrt Z)) ^ 3 * (Real.sqrt (Real.sqrt P)) ^ 3 :=
      mul_nonneg (mul_nonneg C3D_agmon_R3_nonneg (by positivity)) (by positivity)
    have hR_nn : 0 ≤ A ^ 3 * B := by positivity
    have h4eq : (C3D_agmon_R3 * (Real.sqrt (Real.sqrt Z)) ^ 3 * (Real.sqrt (Real.sqrt P)) ^ 3) ^ 4 =
        (A ^ 3 * B) ^ 4 := by
      have hZ4 : ((Real.sqrt (Real.sqrt Z)) ^ 3) ^ 4 = Z ^ 3 := by
        calc ((Real.sqrt (Real.sqrt Z)) ^ 3) ^ 4 = (((Real.sqrt (Real.sqrt Z)) ^ 2) ^ 2) ^ 3 := by ring
          _ = ((Real.sqrt Z) ^ 2) ^ 3 := by rw [Real.sq_sqrt (Real.sqrt_nonneg _)]
          _ = Z ^ 3 := by rw [Real.sq_sqrt hZ_nn]
      have hP4 : ((Real.sqrt (Real.sqrt P)) ^ 3) ^ 4 = P ^ 3 := by
        calc ((Real.sqrt (Real.sqrt P)) ^ 3) ^ 4 = (((Real.sqrt (Real.sqrt P)) ^ 2) ^ 2) ^ 3 := by ring
          _ = ((Real.sqrt P) ^ 2) ^ 3 := by rw [Real.sq_sqrt (Real.sqrt_nonneg _)]
          _ = P ^ 3 := by rw [Real.sq_sqrt hP_nn]
      calc (C3D_agmon_R3 * (Real.sqrt (Real.sqrt Z)) ^ 3 * (Real.sqrt (Real.sqrt P)) ^ 3) ^ 4
          = C3D_agmon_R3 ^ 4 * ((Real.sqrt (Real.sqrt Z)) ^ 3) ^ 4 * ((Real.sqrt (Real.sqrt P)) ^ 3) ^ 4 := by
              ring
        _ = 2 * Z ^ 3 * P ^ 3 := by rw [C3D_agmon_R3_pow_four, hZ4, hP4]
        _ = (ν * P) ^ 3 * (4 * c_nu_R3 ν * Z ^ 3) := by
              unfold c_nu_R3
              have hν0 : ν ≠ 0 := ne_of_gt hν
              field_simp; ring
        _ = (A ^ 4) ^ 3 * B ^ 4 := by rw [hA4, hB4]
        _ = (A ^ 3 * B) ^ 4 := by ring
    set X := C3D_agmon_R3 * (Real.sqrt (Real.sqrt Z)) ^ 3 * (Real.sqrt (Real.sqrt P)) ^ 3
    set Y := A ^ 3 * B
    have h2eq : X ^ 2 = Y ^ 2 := by
      have hfac : (X ^ 2 - Y ^ 2) * (X ^ 2 + Y ^ 2) = X ^ 4 - Y ^ 4 := by ring
      have hL2_nn : 0 ≤ X ^ 2 := sq_nonneg _
      have hR2_nn : 0 ≤ Y ^ 2 := sq_nonneg _
      nlinarith
    have hfac2 : (X - Y) * (X + Y) = X ^ 2 - Y ^ 2 := by ring
    nlinarith
  rw [hA4, hB4] at hamgm
  linarith

-- ============================================================================
-- SECTION 6: AXIOM AUDIT TRAIL (0 sorryAx, 0 custom axioms)
-- ============================================================================

#print axioms r3Integral_inv_rho_pow4
#print axioms r3Integral_inv_rho_pow6_le
#print axioms r3Integral_poisson_kernel_eq
#print axioms r3Integral_psi_sq_le
#print axioms agmon_3d_r3_scalar
#print axioms agmon_3d_r3_ns_velocity
#print axioms unconditional_vortexStretching_le_agmon_r3
#print axioms unconditional_r3_stretching_young_absorption

end GarryWholeSpaceR3Agmon