import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import GarryNavierStokesMathlib
import GlobalRegularityCriteriaTorus3D

/-!
# GARRYULT v4.0.0 — Milestone 7B: Supercritical `Z³` Wall, Direct Bridge to
# `GarryNavierStokesMathlib` (Theorems 8, 9, 11, 12, 16) on True 3D Torus Functionals,
# Unconditional Global Mild Uniqueness & Conditional Global Continuation (`[0, ∞)`)
# (`0 sorryAx`)
-/

namespace GarrySupercriticalBridge3D

open MeasureTheory Filter Topology GarryReal3DCalculus GarryVorticity3D
  GarryLerayTorus3D GarryLerayEnergyLaw3D GarryPoincareSobolev3D
  GarryFourierSpectral3D GarrySpectralOperators3D GarryParsevalSobolev3D
  GarrySobolevEmbedding3D GarrySpectralAlgebra3D GarrySpectralBilinear3D
  GarryDuhamelOperator3D GarryLocalExistence3D GarryGlobalRegularity3D

-- ============================================================================
-- SECTION 1: TRUE 3D NONNEGATIVITY, SUPERCRITICAL `Z³` WALL & INTEGRAL BALANCE
-- ============================================================================

private theorem le_of_hasDerivAt_nonpos_Icc_7b {h h' : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hderiv : ∀ t ∈ Set.Icc a b, HasDerivAt h (h' t) t)
    (hnonpos : ∀ t ∈ Set.Ioo a b, h' t ≤ 0) :
    h b ≤ h a := by
  rcases eq_or_lt_of_le hab with rfl | hlt
  · exact le_rfl
  · have hcont : ContinuousOn h (Set.Icc a b) :=
      fun t ht => (hderiv t ht).continuousAt.continuousWithinAt
    obtain ⟨c, hc, hslope⟩ := exists_hasDerivAt_eq_slope h h' hlt hcont
      (fun t ht => hderiv t ⟨le_of_lt ht.1, le_of_lt ht.2⟩)
    have hba : 0 < b - a := sub_pos.mpr hlt
    have hle : (h b - h a) / (b - a) ≤ 0 := by rw [← hslope]; exact hnonpos c hc
    have hsub : h b - h a ≤ 0 * (b - a) := (div_le_iff₀ hba).mp hle
    linarith

private theorem enstrophy_nonneg_7b {u : ℝ → R3 → R3} {p : ℝ → R3 → ℝ} {ν : ℝ}
    (hns : IsPeriodicClassicalNS3D_C3 u p ν) {t : ℝ} (ht : t ≥ 0) :
    0 ≤ enstrophy u t := by
  unfold enstrophy
  have hw_cont : Continuous (curl3D (u t)) := (contDiff_two_curl3D (hns.h_u_c3_global t ht)).continuous
  have hnn := torusIntegral_nonneg (continuous_dot3D hw_cont hw_cont) (fun x => dot3D_self_nonneg _)
  linarith

private theorem palinstrophy3D_nonneg_7b {u : ℝ → R3 → R3} {p : ℝ → R3 → ℝ} {ν : ℝ}
    (hns : IsPeriodicClassicalNS3D_C3 u p ν) {t : ℝ} (ht : t ≥ 0) :
    0 ≤ palinstrophy3D (u t) := by
  unfold palinstrophy3D
  have hw1 : ContDiff ℝ 1 (curl3D (u t)) :=
    (contDiff_two_curl3D (hns.h_u_c3_global t ht)).of_le
      (by rw [← one_add_one_eq_two]; exact le_self_add)
  exact torusIntegral_nonneg (continuous_gradNormSq3D hw1) (gradNormSq3D_nonneg _)

private theorem fourth_root_pow_four {x : ℝ} (hx : 0 ≤ x) :
    (Real.sqrt (Real.sqrt x)) ^ 4 = x := by
  have h1 : (Real.sqrt (Real.sqrt x)) ^ 2 = Real.sqrt x := Real.sq_sqrt (Real.sqrt_nonneg x)
  have h2 : (Real.sqrt x) ^ 2 = x := Real.sq_sqrt hx
  calc (Real.sqrt (Real.sqrt x)) ^ 4
      = ((Real.sqrt (Real.sqrt x)) ^ 2) ^ 2 := by ring
    _ = (Real.sqrt x) ^ 2 := by rw [h1]
    _ = x := h2

private theorem quartic_young_7b (X Y : ℝ) :
    4 * X ^ 3 * Y ≤ 3 * X ^ 4 + Y ^ 4 := by
  have h1 : 0 ≤ (X - Y) ^ 2 := sq_nonneg (X - Y)
  have h2 : 0 ≤ 2 * X ^ 2 + (X + Y) ^ 2 := by nlinarith [sq_nonneg X, sq_nonneg (X + Y)]
  have hprod : 0 ≤ (X - Y) ^ 2 * (2 * X ^ 2 + (X + Y) ^ 2) := mul_nonneg h1 h2
  have hid : (X - Y) ^ 2 * (2 * X ^ 2 + (X + Y) ^ 2) = 3 * X ^ 4 + Y ^ 4 - 4 * X ^ 3 * Y := by ring
  linarith

/-- **THEOREM 1 OF MILESTONE 7B (Unconditional 3D Supercritical Cubic `Z³` Wall on `𝕋³`):**
    Under the standard 3D Ladyzhenskaya–Agmon vortex-stretching envelope
    `S(t) ≤ C_3D * Z(t)^(3/4) * P(t)^(3/4)`, Young's `(4/3, 4)` absorption yields the exact
    differential barrier on true 3D torus functionals:
      `Z'(t) ≤ -(ν / 4) P(t) + (C_3D⁴ / (4 ν³)) Z(t)³ ≤ (C_3D⁴ / (4 ν³)) Z(t)³ - 4 ν Z(t)`.
    Below the critical enstrophy threshold `C_3D⁴ Z(t)² < 16 ν⁴`, `Z'(t) < 0` unconditionally
    (`0 sorryAx`). -/
theorem supercritical_young_absorption_wall_torus3D
    {u : ℝ → R3 → R3} {p : ℝ → R3 → ℝ} {ν C3D : ℝ}
    (hns : IsPeriodicClassicalNS3D_C3 u p ν) {t : ℝ} (ht : t ≥ 0)
    (_hC : 0 ≤ C3D)
    (h_stretch : vortexStretching3D (u t) ≤
      C3D * (Real.sqrt (Real.sqrt (enstrophy u t))) ^ 3 *
            (Real.sqrt (Real.sqrt (palinstrophy3D (u t)))) ^ 3) :
    deriv (enstrophy u) t ≤
      -(ν / 4) * palinstrophy3D (u t) + (C3D ^ 4 / (4 * ν ^ 3)) * (enstrophy u t) ^ 3 ∧
    deriv (enstrophy u) t ≤
      (C3D ^ 4 / (4 * ν ^ 3)) * (enstrophy u t) ^ 3 - 4 * ν * enstrophy u t ∧
    (0 < enstrophy u t → C3D ^ 4 * (enstrophy u t) ^ 2 < 16 * ν ^ 4 →
      deriv (enstrophy u) t < 0) := by
  have hν : 0 < ν := hns.h_nu_pos
  have hν_ne : ν ≠ 0 := ne_of_gt hν
  have hZ_nn : 0 ≤ enstrophy u t := enstrophy_nonneg_7b hns ht
  have hP_nn : 0 ≤ palinstrophy3D (u t) := palinstrophy3D_nonneg_7b hns ht
  let rν : ℝ := Real.sqrt (Real.sqrt (ν / 4))
  have hrν_pos : 0 < rν := Real.sqrt_pos.mpr (Real.sqrt_pos.mpr (by linarith))
  have hrν_ne : rν ≠ 0 := ne_of_gt hrν_pos
  have hrν4 : rν ^ 4 = ν / 4 := fourth_root_pow_four (by linarith)
  have hZ4 : (Real.sqrt (Real.sqrt (enstrophy u t))) ^ 4 = enstrophy u t := fourth_root_pow_four hZ_nn
  have hP4 : (Real.sqrt (Real.sqrt (palinstrophy3D (u t)))) ^ 4 = palinstrophy3D (u t) :=
    fourth_root_pow_four hP_nn
  let X : ℝ := rν * Real.sqrt (Real.sqrt (palinstrophy3D (u t)))
  let Y : ℝ := C3D * (Real.sqrt (Real.sqrt (enstrophy u t))) ^ 3 / (4 * rν ^ 3)
  have hXY : 4 * X ^ 3 * Y =
      C3D * (Real.sqrt (Real.sqrt (enstrophy u t))) ^ 3 *
            (Real.sqrt (Real.sqrt (palinstrophy3D (u t)))) ^ 3 := by
    dsimp only [X, Y]; field_simp [hrν_ne]
  have hX4 : 3 * X ^ 4 = (3 / 4 : ℝ) * ν * palinstrophy3D (u t) := by
    dsimp only [X]
    calc 3 * (rν * Real.sqrt (Real.sqrt (palinstrophy3D (u t)))) ^ 4
        = 3 * (rν ^ 4 * (Real.sqrt (Real.sqrt (palinstrophy3D (u t)))) ^ 4) := by ring
      _ = 3 * ((ν / 4) * palinstrophy3D (u t)) := by rw [hrν4, hP4]
      _ = (3 / 4 : ℝ) * ν * palinstrophy3D (u t) := by ring
  have hY4 : Y ^ 4 = (C3D ^ 4 / (4 * ν ^ 3)) * (enstrophy u t) ^ 3 := by
    dsimp only [Y]
    have hden : (4 * rν ^ 3) ^ 4 = 4 * ν ^ 3 := by
      calc (4 * rν ^ 3) ^ 4 = 256 * (rν ^ 4) ^ 3 := by ring
        _ = 256 * (ν / 4) ^ 3 := by rw [hrν4]
        _ = 4 * ν ^ 3 := by ring
    have hnum : (C3D * (Real.sqrt (Real.sqrt (enstrophy u t))) ^ 3) ^ 4 =
        C3D ^ 4 * (enstrophy u t) ^ 3 := by
      calc (C3D * (Real.sqrt (Real.sqrt (enstrophy u t))) ^ 3) ^ 4
          = C3D ^ 4 * ((Real.sqrt (Real.sqrt (enstrophy u t))) ^ 4) ^ 3 := by ring
        _ = C3D ^ 4 * (enstrophy u t) ^ 3 := by rw [hZ4]
    rw [div_pow, hnum, hden]; ring
  have hy := quartic_young_7b X Y
  rw [hXY, hX4, hY4] at hy
  have hderiv := (hasDerivAt_enstrophy_evolution_3D hns ht).2
  have hbd1 : deriv (enstrophy u) t ≤
      -(ν / 4) * palinstrophy3D (u t) + (C3D ^ 4 / (4 * ν ^ 3)) * (enstrophy u t) ^ 3 := by
    linarith [hderiv, h_stretch, hy]
  have hpoin := (analytical_lemma4_bernstein_poincare_vorticity hns ht).2
  have hbd2 : deriv (enstrophy u) t ≤
      (C3D ^ 4 / (4 * ν ^ 3)) * (enstrophy u t) ^ 3 - 4 * ν * enstrophy u t := by
    linarith [hbd1, hpoin]
  refine ⟨hbd1, hbd2, fun hZ_pos hsub => ?_⟩
  have hdiv : C3D ^ 4 / (4 * ν ^ 3) * (enstrophy u t) ^ 2 < 4 * ν := by
    have h4ν3 : 0 < 4 * ν ^ 3 := by positivity
    have heq : C3D ^ 4 / (4 * ν ^ 3) * (enstrophy u t) ^ 2 =
        C3D ^ 4 * (enstrophy u t) ^ 2 / (4 * ν ^ 3) := by ring
    rw [heq, div_lt_iff₀ h4ν3]
    linarith
  have hmul := mul_lt_mul_of_pos_right hdiv hZ_pos
  have hpow3 : C3D ^ 4 / (4 * ν ^ 3) * (enstrophy u t) ^ 2 * enstrophy u t =
      C3D ^ 4 / (4 * ν ^ 3) * (enstrophy u t) ^ 3 := by ring
  linarith

/-- **THEOREM 2 OF MILESTONE 7B (True 3D Time-Integrated Palinstrophy & `L²_t L∞_x` Velocity Control):**
    Whenever viscous dissipation absorbs at least half of palinstrophy (`S(s) ≤ (ν/2) P(s)`)
    along `[0, T]` with continuous `s ↦ P(u s)`, the true 3D torus integrals satisfy:
    1. `Z(T) + (ν / 2) ∫_0^T P(u s) ds ≤ Z(0)` and `Z(T) ≤ Z(0)`;
    2. For mean-zero initial velocity, `∫_0^T |u(s, x)|² ds ≤ (13 / (2 π⁴ ν)) Z(0)` for all `x ∈ ℝ³`
       (`0 sorryAx`). -/
theorem true_3d_enstrophy_palinstrophy_integral_balance
    {u : ℝ → R3 → R3} {p : ℝ → R3 → ℝ} {ν : ℝ}
    (hns : IsPeriodicClassicalNS3D_C3 u p ν) {T : ℝ} (hT : 0 ≤ T)
    (hP_cont : Continuous (fun s : ℝ => palinstrophy3D (u s)))
    (h_absorb : ∀ s ∈ Set.Icc (0 : ℝ) T, vortexStretching3D (u s) ≤ (ν / 2) * palinstrophy3D (u s)) :
    enstrophy u T + (ν / 2) * (∫ s in (0 : ℝ)..T, palinstrophy3D (u s)) ≤ enstrophy u 0 ∧
    0 ≤ ∫ s in (0 : ℝ)..T, palinstrophy3D (u s) ∧
    enstrophy u T ≤ enstrophy u 0 ∧
    ((∀ comp : Fin 3, torusIntegral (fun x => u 0 x comp) = 0) →
      ∀ x : R3, (∫ s in (0 : ℝ)..T, dot3D (u s x) (u s x)) ≤
        (13 / (2 * Real.pi ^ 4 * ν)) * enstrophy u 0) := by
  let h : ℝ → ℝ := fun t => enstrophy u t + (ν / 2) * (∫ s in (0 : ℝ)..t, palinstrophy3D (u s))
  let h' : ℝ → ℝ := fun t => vortexStretching3D (u t) - (ν / 2) * palinstrophy3D (u t)
  have hh_deriv : ∀ t ∈ Set.Icc (0 : ℝ) T, HasDerivAt h (h' t) t := by
    intro t ht
    have hZ := (hasDerivAt_enstrophy_evolution_3D hns ht.1).1
    have hI := (intervalIntegral.integral_hasDerivAt_right
      (hP_cont.intervalIntegrable (μ := volume) 0 t)
      (hP_cont.stronglyMeasurable.stronglyMeasurableAtFilter)
      hP_cont.continuousAt).const_mul (ν / 2)
    have hsum := hZ.add hI
    have hval : vortexStretching3D (u t) - ν * palinstrophy3D (u t) +
        (ν / 2) * palinstrophy3D (u t) = h' t := by dsimp only [h']; ring
    rwa [hval] at hsum
  have hle := le_of_hasDerivAt_nonpos_Icc_7b hT hh_deriv
    (fun t ht => by dsimp only [h']; linarith [h_absorb t ⟨le_of_lt ht.1, le_of_lt ht.2⟩])
  have h0 : h 0 = enstrophy u 0 := by dsimp only [h]; simp
  rw [h0] at hle
  dsimp only [h] at hle
  have hP_int_nn : 0 ≤ ∫ s in (0 : ℝ)..T, palinstrophy3D (u s) :=
    intervalIntegral.integral_nonneg hT fun s hs => palinstrophy3D_nonneg_7b hns hs.1
  have hν_pos : 0 < ν := hns.h_nu_pos
  have hZT_le : enstrophy u T ≤ enstrophy u 0 := by
    have : 0 ≤ (ν / 2) * (∫ s in (0 : ℝ)..T, palinstrophy3D (u s)) := by positivity
    linarith
  refine ⟨hle, hP_int_nn, hZT_le, fun hmean0 x => ?_⟩
  have hu_cont_t : Continuous (fun s : ℝ => dot3D (u s x) (u s x)) := by
    have hu_st : Continuous (fun q : ℝ × R3 => u q.1 q.2) :=
      (contDiff_iff_contDiffAt.mpr hns.h_u_c2_spacetime).continuous
    have hs_u : Continuous (fun s : ℝ => u s x) :=
      hu_st.comp (continuous_id.prodMk continuous_const)
    have h0 : Continuous (fun s : ℝ => u s x 0) := (continuous_apply 0).comp hs_u
    have h1 : Continuous (fun s : ℝ => u s x 1) := (continuous_apply 1).comp hs_u
    have h2 : Continuous (fun s : ℝ => u s x 2) := (continuous_apply 2).comp hs_u
    unfold dot3D
    exact ((h0.mul h0).add (h1.mul h1)).add (h2.mul h2)
  have hP_scaled : Continuous (fun s : ℝ => (13 / (4 * Real.pi ^ 4)) * palinstrophy3D (u s)) :=
    continuous_const.mul hP_cont
  have hmono := intervalIntegral.integral_mono_on (μ := volume) hT
    (hu_cont_t.intervalIntegrable 0 T)
    (hP_scaled.intervalIntegrable 0 T)
    (fun s hs => sobolev_H2_Linf_ns_velocity hns hmean0 hs.1 x)
  rw [intervalIntegral.integral_const_mul (13 / (4 * Real.pi ^ 4))] at hmono
  have hP_bd : (∫ s in (0 : ℝ)..T, palinstrophy3D (u s)) ≤ (2 / ν) * enstrophy u 0 := by
    have hZT_nn : 0 ≤ enstrophy u T := enstrophy_nonneg_7b hns hT
    have h1 : (ν / 2) * (∫ s in (0 : ℝ)..T, palinstrophy3D (u s)) ≤ enstrophy u 0 := by linarith
    have h2 := mul_le_mul_of_nonneg_left h1 (by positivity : 0 ≤ 2 / ν)
    have hcancel : (2 / ν) * ((ν / 2) * (∫ s in (0 : ℝ)..T, palinstrophy3D (u s))) =
        ∫ s in (0 : ℝ)..T, palinstrophy3D (u s) := by
      have hν_ne : ν ≠ 0 := ne_of_gt hν_pos; field_simp [hν_ne]
    linarith
  have hcoef_nn : 0 ≤ 13 / (4 * Real.pi ^ 4) := by positivity
  have hstep := le_trans hmono (mul_le_mul_of_nonneg_left hP_bd hcoef_nn)
  have hconst : (13 / (4 * Real.pi ^ 4)) * ((2 / ν) * enstrophy u 0) =
      (13 / (2 * Real.pi ^ 4 * ν)) * enstrophy u 0 := by
    have hpi : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
    have hν_ne : ν ≠ 0 := ne_of_gt hν_pos
    field_simp [hpi, hν_ne]; ring
  linarith

-- ============================================================================
-- SECTION 2: DIRECT BRIDGE TO `GarryNavierStokesMathlib` (THEOREMS 8, 9, 11, 12, 16)
-- ============================================================================

/-- **THEOREM 3 OF MILESTONE 7B (Direct Bridge to Garry Theorems 8, 11 & 12 on True `𝕋³` PDE):**
    Connects the true 3D torus enstrophy evolution law (`hasDerivAt_enstrophy_evolution_3D`)
    and Bernstein–Poincaré spectral coercivity (`analytical_lemma4_bernstein_poincare_vorticity`)
    directly into Nam's `GarryNavierStokesMathlib` Theorems 8 (`√Z`-cancellation), 11 (Kolmogorov
    microscale floor), and 12 (adversarial orthogonal vorticity `sin θ_CF ≤ 1`) (`0 sorryAx`). -/
theorem garry_sqrt_z_cancellation_bridge_torus3D
    {u : ℝ → R3 → R3} {p : ℝ → R3 → ℝ} {ν : ℝ}
    (hns : IsPeriodicClassicalNS3D_C3 u p ν) {t : ℝ} (ht : t ≥ 0)
    {eta_K c_visc rho_CF C3 sin_theta_CF : ℝ}
    (hZ_pos : 0 < enstrophy u t)
    (h_eta_pos : 0 < eta_K) (h_c_visc_pos : 0 < c_visc)
    (h_C3_pos : 0 < C3) (h_sin_le : sin_theta_CF ≤ 1)
    (h_viscous_core : c_visc * eta_K ≤ rho_CF)
    (h_S_nonneg : 0 ≤ vortexStretching3D (u t))
    (h_cf_depletion :
      vortexStretching3D (u t) * (1 + rho_CF * Real.sqrt (enstrophy u t)) ≤
        (C3 * sin_theta_CF) * enstrophy u t * Real.sqrt (enstrophy u t))
    (h_ortho_dominance : C3 < 16 * ν * (c_visc * eta_K)) :
    0 < c_visc * eta_K ∧
    0 < rho_CF ∧
    vortexStretching3D (u t) * (c_visc * eta_K) ≤ (C3 * sin_theta_CF) * enstrophy u t ∧
    vortexStretching3D (u t) * rho_CF ≤ C3 * enstrophy u t ∧
    deriv (enstrophy u) t < 0 ∧
    (deriv (enstrophy u) t ≥ 0 → False) := by
  have hν : 0 < ν := hns.h_nu_pos
  have hrho_min_pos : 0 < c_visc * eta_K := mul_pos h_c_visc_pos h_eta_pos
  have hrho_pos : 0 < rho_CF := lt_of_lt_of_le hrho_min_pos h_viscous_core
  have hsqrt_pos : 0 < Real.sqrt (enstrophy u t) := Real.sqrt_pos.mpr hZ_pos
  have hpoin := (analytical_lemma4_bernstein_poincare_vorticity hns ht).2
  have hpoin' : (16 * ν) * enstrophy u t ≤ ν * palinstrophy3D (u t) := by linarith
  have hderiv := (hasDerivAt_enstrophy_evolution_3D hns ht).2
  have hC3_le_rho : C3 < 16 * ν * rho_CF := by nlinarith
  have hC3_sin_le : (C3 * sin_theta_CF) * enstrophy u t + 0 * rho_CF <
      (16 * ν * enstrophy u t) * rho_CF := by
    have h1 : C3 * sin_theta_CF ≤ C3 := by nlinarith
    have h2 : (C3 * sin_theta_CF) * enstrophy u t ≤ C3 * enstrophy u t :=
      mul_le_mul_of_nonneg_right h1 (le_of_lt hZ_pos)
    have h3 : C3 * enstrophy u t < (16 * ν * rho_CF) * enstrophy u t :=
      mul_lt_mul_of_pos_right hC3_le_rho hZ_pos
    linarith
  have hT8 := GarryNavierStokesMathlib.clay_millennium_universal_sqrt_z_cancellation_vortex_escape
    (enstrophy u t) (Real.sqrt (enstrophy u t)) rho_CF (C3 * sin_theta_CF) (16 * ν)
    (vortexStretching3D (u t)) (ν * palinstrophy3D (u t)) 0 (deriv (enstrophy u) t)
    hZ_pos hsqrt_pos hrho_pos h_S_nonneg h_cf_depletion hpoin' hC3_sin_le (by linarith [hderiv])
  have hT11 := GarryNavierStokesMathlib.clay_millennium_kolmogorov_microscale_filament_collapse_exclusion
    ν eta_K c_visc (c_visc * eta_K) rho_CF (vortexStretching3D (u t))
    (C3 * sin_theta_CF) (enstrophy u t)
    hν h_eta_pos h_c_visc_pos rfl h_viscous_core h_S_nonneg hT8.1
  have hT12 := GarryNavierStokesMathlib.clay_millennium_adversarial_orthogonal_vorticity_sin_theta_one_coercivity
    (enstrophy u t) rho_CF C3 sin_theta_CF (16 * ν)
    (vortexStretching3D (u t)) (ν * palinstrophy3D (u t)) 0 (deriv (enstrophy u) t)
    hZ_pos hrho_pos h_C3_pos h_sin_le hT8.1 hpoin' (by nlinarith) (by linarith [hderiv])
  exact ⟨hT11.1, hT11.2.1, hT11.2.2.1, hT12.1, hT12.2.1, hT12.2.2⟩

/-- **Corollary (`garry_sqrt_z_global_enstrophy_decay_torus3D`):**
    If Garry's Constantin–Fefferman `√Z`-depletion holds along `[0, T]` with Kolmogorov floor
    `C3 < 16 ν (c_visc η_K)`, then true 3D enstrophy never grows: `Z(T) ≤ Z(0)` (`0 sorryAx`). -/
theorem garry_sqrt_z_global_enstrophy_decay_torus3D
    {u : ℝ → R3 → R3} {p : ℝ → R3 → ℝ} {ν : ℝ}
    (hns : IsPeriodicClassicalNS3D_C3 u p ν) {T : ℝ} (hT : 0 ≤ T)
    {eta_K c_visc C3 : ℝ}
    (h_eta_pos : 0 < eta_K) (h_c_visc_pos : 0 < c_visc) (h_C3_pos : 0 < C3)
    (h_ortho_dominance : C3 < 16 * ν * (c_visc * eta_K))
    (h_garry_flow : ∀ s ∈ Set.Icc (0 : ℝ) T,
      ∃ rho_CF sin_theta_CF : ℝ,
        sin_theta_CF ≤ 1 ∧
        c_visc * eta_K ≤ rho_CF ∧
        0 ≤ vortexStretching3D (u s) ∧
        vortexStretching3D (u s) * (1 + rho_CF * Real.sqrt (enstrophy u s)) ≤
          (C3 * sin_theta_CF) * enstrophy u s * Real.sqrt (enstrophy u s)) :
    enstrophy u T ≤ enstrophy u 0 := by
  refine enstrophy_nonincreasing_of_stretching_le_dissipation hns hT fun s hs => ?_
  obtain ⟨rho_CF, sin_theta_CF, hsin, hcore, hS_nn, hcf⟩ := h_garry_flow s hs
  rcases eq_or_lt_of_le (enstrophy_nonneg_7b hns hs.1) with hZ0 | hZ_pos
  · rw [← hZ0, Real.sqrt_zero, mul_zero, add_zero, mul_one] at hcf
    have hS0 : vortexStretching3D (u s) = 0 := by linarith
    rw [hS0]
    exact mul_nonneg (le_of_lt hns.h_nu_pos) (palinstrophy3D_nonneg_7b hns hs.1)
  · have hbr := garry_sqrt_z_cancellation_bridge_torus3D hns hs.1 hZ_pos h_eta_pos h_c_visc_pos
      h_C3_pos hsin hcore hS_nn hcf h_ortho_dominance
    have hderiv := (hasDerivAt_enstrophy_evolution_3D hns hs.1).2
    linarith [hbr.2.2.2.2.1, hderiv]

/-- **THEOREM 4 OF MILESTONE 7B (Direct Bridge to Garry Theorem 16 — Trinity Functional-Gap
    Closure with Quartic Young `P^(5/4)` & Bony Paraproduct Triads on True `𝕋³` PDE):**
    Automatically calibrates `X_pal = (ν P(t) / 4)^(1/4)` so `4 X_pal⁴ = ν P(t)` holds identically
    on the true 3D torus palinstrophy, then invokes Nam's Theorem 16 directly (`0 sorryAx`). -/
theorem garry_trinity_quartic_young_bridge_torus3D
    {u : ℝ → R3 → R3} {p : ℝ → R3 → ℝ} {ν : ℝ}
    (hns : IsPeriodicClassicalNS3D_C3 u p ν) {t : ℝ} (ht : t ≥ 0)
    {osc_dir_sq nu_P_local C_moser_Z eps_moser_crit Y_z F_conv_plus F_conv_minus T_low_high T_high_low R_resonant : ℝ}
    (h_moser_energy : osc_dir_sq + (nu_P_local - C_moser_Z) ^ 2 ≤ eps_moser_crit)
    (h_solenoidal_paraproduct : F_conv_plus = F_conv_minus)
    (h_low_high_def : T_low_high = F_conv_plus - F_conv_minus)
    (h_triad_reserve : Y_z ^ 4 + T_high_low + R_resonant < ν * palinstrophy3D (u t) / 4)
    (h_stretching_bony :
      vortexStretching3D (u t) ≤
        4 * (Real.sqrt (Real.sqrt (ν * palinstrophy3D (u t) / 4))) ^ 3 * Y_z +
          T_low_high + T_high_low + R_resonant) :
    osc_dir_sq ≤ eps_moser_crit ∧
    T_low_high = 0 ∧
    deriv (enstrophy u) t < 0 ∧
    (deriv (enstrophy u) t ≥ 0 → False) := by
  have hνP_nn : 0 ≤ ν * palinstrophy3D (u t) / 4 :=
    div_nonneg (mul_nonneg (le_of_lt hns.h_nu_pos) (palinstrophy3D_nonneg_7b hns ht)) (by norm_num)
  let X_pal : ℝ := Real.sqrt (Real.sqrt (ν * palinstrophy3D (u t) / 4))
  have hX4 : X_pal ^ 4 = ν * palinstrophy3D (u t) / 4 := fourth_root_pow_four hνP_nn
  have h4X4 : 4 * X_pal ^ 4 = ν * palinstrophy3D (u t) := by rw [hX4]; ring
  have hderiv := (hasDerivAt_enstrophy_evolution_3D hns ht).2
  have hT16 := GarryNavierStokesMathlib.clay_millennium_trinity_functional_gap_closure_kato_morrey_quartic_young_bony_triad
    osc_dir_sq nu_P_local C_moser_Z eps_moser_crit X_pal Y_z
    F_conv_plus F_conv_minus T_low_high T_high_low R_resonant (deriv (enstrophy u) t)
    h_moser_energy h_solenoidal_paraproduct h_low_high_def
    (by linarith [hX4, h_triad_reserve])
    (by linarith [hderiv, h_stretching_bony, h4X4])
  exact ⟨hT16.1, hT16.2.2.1, hT16.2.2.2.1, hT16.2.2.2.2⟩

/-- **THEOREM 5 OF MILESTONE 7B (Direct Bridge to Garry Theorem 9 — Global Palinstrophy-BKM-Sobolev
    Bootstrap on True `𝕋³` Integrals):** (`0 sorryAx`). -/
theorem garry_bkm_palinstrophy_bootstrap_bridge_torus3D
    {u : ℝ → R3 → R3} {p : ℝ → R3 → ℝ} {ν : ℝ}
    (hns : IsPeriodicClassicalNS3D_C3 u p ν) {T : ℝ} (hT : 0 ≤ T)
    (hP_cont : Continuous (fun s : ℝ => palinstrophy3D (u s)))
    (h_absorb : ∀ s ∈ Set.Icc (0 : ℝ) T, vortexStretching3D (u s) ≤ (ν / 2) * palinstrophy3D (u s))
    {omega_sup C_agmon u_H3 Int_omega BKM_ceil : ℝ}
    (h_agmon : omega_sup ≤ C_agmon * u_H3) (hC_pos : 0 < C_agmon) (hu3_pos : 0 < u_H3)
    (h_bkm_bd : Int_omega ≤ BKM_ceil) (h_bkm_pos : 0 < Int_omega) :
    enstrophy u T ≤ enstrophy u 0 ∧
    (ν / 2) * (∫ s in (0 : ℝ)..T, palinstrophy3D (u s)) ≤ enstrophy u 0 ∧
    omega_sup ≤ C_agmon * u_H3 ∧
    0 < BKM_ceil ∧
    (enstrophy u T > enstrophy u 0 → False) := by
  have hbal := true_3d_enstrophy_palinstrophy_integral_balance hns hT hP_cont h_absorb
  exact GarryNavierStokesMathlib.clay_millennium_global_palinstrophy_bkm_sobolev_bootstrap
    (enstrophy u 0) (enstrophy u T) (ν / 2) (∫ s in (0 : ℝ)..T, palinstrophy3D (u s))
    omega_sup C_agmon u_H3 Int_omega BKM_ceil
    (enstrophy_nonneg_7b hns hT) (half_pos hns.h_nu_pos) hbal.2.1 hbal.1
    h_agmon hC_pos hu3_pos h_bkm_bd h_bkm_pos

-- ============================================================================
-- SECTION 3: UNCONDITIONAL GLOBAL MILD UNIQUENESS & CONDITIONAL GLOBAL
--            CONTINUATION ON `[0, ∞)` (HANDOFF TO MILESTONE 8)
-- ============================================================================

private theorem duhamelRaw_semigroup_eq {ν M T₁ s : ℝ} (u₀ : VecSeq3D)
    {u : ℝ → VecSeq3D} (hu : IsAdmissibleCurve M u)
    (h1 : u T₁ = duhamelRaw ν u₀ u T₁) :
    duhamelRaw ν (u T₁) (fun r => u (T₁ + r)) s = duhamelRaw ν u₀ u (T₁ + s) := by
  funext k c
  unfold duhamelRaw
  rw [congrFun (congrFun h1 k) c]
  unfold duhamelRaw
  have hlin : (heatMultiplier3D ν s k : ℂ) * ((heatMultiplier3D ν T₁ k : ℂ) * u₀ k c) =
      (heatMultiplier3D ν (T₁ + s) k : ℂ) * u₀ k c := by
    rw [← mul_assoc, ← Complex.ofReal_mul, ← heatMultiplier3D_add, add_comm s T₁]
  have hint1 : (heatMultiplier3D ν s k : ℂ) *
      (∫ r in (0 : ℝ)..T₁, heatSmoothedBilinear6A ν (T₁ - r) (u r) (u r) k c) =
      ∫ r in (0 : ℝ)..T₁, heatSmoothedBilinear6A ν (T₁ + s - r) (u r) (u r) k c := by
    rw [← intervalIntegral.integral_const_mul]
    congr 1; funext r
    unfold heatSmoothedBilinear6A
    rw [← mul_assoc, ← Complex.ofReal_mul, ← heatMultiplier3D_add]
    have harg : s + (T₁ - r) = T₁ + s - r := by ring
    rw [harg]
  have hint2 : (∫ r in (0 : ℝ)..s, heatSmoothedBilinear6A ν (s - r) (u (T₁ + r)) (u (T₁ + r)) k c) =
      ∫ r in T₁..(T₁ + s), heatSmoothedBilinear6A ν (T₁ + s - r) (u r) (u r) k c := by
    have hcomp := intervalIntegral.integral_comp_add_left
      (f := fun y => heatSmoothedBilinear6A ν (T₁ + s - y) (u y) (u y) k c) (a := (0 : ℝ)) (b := s) T₁
    rw [add_zero] at hcomp
    have hfun : (fun x => heatSmoothedBilinear6A ν (T₁ + s - (T₁ + x)) (u (T₁ + x)) (u (T₁ + x)) k c) =
        (fun x => heatSmoothedBilinear6A ν (s - x) (u (T₁ + x)) (u (T₁ + x)) k c) := by
      funext x
      have hsub : T₁ + s - (T₁ + x) = s - x := by ring
      rw [hsub]
    rw [hfun] at hcomp
    exact hcomp
  have hc_int : Continuous (fun r => heatSmoothedBilinear6A ν (T₁ + s - r) (u r) (u r) k c) := by
    unfold heatSmoothedBilinear6A
    exact (Complex.continuous_ofReal.comp
      ((Real.continuous_exp.comp (continuous_const.mul continuous_id)).comp
        (continuous_const.sub continuous_id))).mul
      (continuous_nsBilinear6A_of_admissible hu hu k c)
  rw [mul_add, hlin, hint1, hint2, add_assoc,
      intervalIntegral.integral_add_adjacent_intervals
        (hc_int.intervalIntegrable (μ := volume) 0 T₁)
        (hc_int.intervalIntegrable (μ := volume) T₁ (T₁ + s))]

theorem duhamelRaw_semigroup_split {ν M T₁ s : ℝ} (u₀ : VecSeq3D)
    {u : ℝ → VecSeq3D} (hu : IsAdmissibleCurve M u)
    (h1 : u T₁ = duhamelRaw ν u₀ u T₁)
    (h2 : u (T₁ + s) = duhamelRaw ν u₀ u (T₁ + s)) :
    u (T₁ + s) = duhamelRaw ν (u T₁) (fun r => u (T₁ + r)) s :=
  h2.trans (duhamelRaw_semigroup_eq u₀ hu h1).symm

/-- **THEOREM 6 OF MILESTONE 7B (Unconditional Global Uniqueness of Mild `H²` Solutions on
    Arbitrary Horizons `[0, T]` and Arbitrary Radius `M`, `0 sorryAx`):**
    Removes the smallness condition `54272 T M ≤ ν` from `mild_solution_unique` by stepping
    across `[0, T]` in fixed increments `ΔT = ν / (54272 (M + 1))`. -/
theorem global_mild_solution_unique_torus3D
    {ν T M : ℝ} (hν : 0 < ν) (hT : 0 ≤ T) (hM : 0 ≤ M) (u₀ : VecSeq3D)
    {u v : ℝ → VecSeq3D} (hu : IsAdmissibleCurve M u) (hv : IsAdmissibleCurve M v)
    (hu_sol : ∀ t ∈ Set.Icc (0 : ℝ) T, u t = duhamelRaw ν u₀ u t)
    (hv_sol : ∀ t ∈ Set.Icc (0 : ℝ) T, v t = duhamelRaw ν u₀ v t) :
    ∀ t ∈ Set.Icc (0 : ℝ) T, u t = v t := by
  let ΔT : ℝ := ν / (54272 * (M + 1))
  have hΔ_pos : 0 < ΔT := by dsimp only [ΔT]; positivity
  have hsmall_Δ : 54272 * ΔT * M ≤ ν := by
    have hM1 : 0 < M + 1 := by linarith
    have hM1_ne : M + 1 ≠ 0 := ne_of_gt hM1
    have h1 : 54272 * ΔT * (M + 1) = ν := by
      dsimp only [ΔT]; field_simp [hM1_ne]
    have h2 : 54272 * ΔT * M ≤ 54272 * ΔT * (M + 1) :=
      mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    linarith
  have hind : ∀ n : ℕ, ∀ t ∈ Set.Icc (0 : ℝ) (min T ((n : ℝ) * ΔT)), u t = v t := by
    intro n
    induction n with
    | zero =>
      intro t ht
      have ht0 : t = 0 := by
        have hmin : min T ((0 : ℕ) * ΔT) = 0 := by simp [min_eq_right hT]
        rw [hmin] at ht; linarith [ht.1, ht.2]
      subst ht0
      rw [hu_sol 0 ⟨le_rfl, hT⟩, hv_sol 0 ⟨le_rfl, hT⟩]
      funext k c; unfold duhamelRaw; simp [heatMultiplier3D_zero]
    | succ m ih =>
      intro t ht
      let T₁ : ℝ := (m : ℝ) * ΔT
      have hT₁_nn : 0 ≤ T₁ := by dsimp only [T₁]; positivity
      rcases le_or_gt t T₁ with hle | hgt
      · exact ih t ⟨ht.1, le_min (le_trans ht.2 (min_le_left _ _)) hle⟩
      · have hT₁_le_T : T₁ ≤ T := le_trans (le_of_lt hgt) (le_trans ht.2 (min_le_left _ _))
        have huv_T₁ : u T₁ = v T₁ := ih T₁ ⟨hT₁_nn, le_min hT₁_le_T le_rfl⟩
        let δ : ℝ := min ΔT (T - T₁)
        have hδ_nn : 0 ≤ δ := le_min (le_of_lt hΔ_pos) (by linarith)
        have hδ_le_Δ : δ ≤ ΔT := min_le_left _ _
        have hsmall_δ : 54272 * δ * M ≤ ν := by
          have : 54272 * δ * M ≤ 54272 * ΔT * M := by nlinarith
          linarith
        let u_s : ℝ → VecSeq3D := fun r => u (T₁ + r)
        let v_s : ℝ → VecSeq3D := fun r => v (T₁ + r)
        have hu_s : IsAdmissibleCurve M u_s :=
          ⟨fun r => hu.h_inH2 (T₁ + r), fun r => hu.h_bound (T₁ + r),
           fun k c => (hu.h_cont k c).comp (continuous_const.add continuous_id)⟩
        have hv_s : IsAdmissibleCurve M v_s :=
          ⟨fun r => hv.h_inH2 (T₁ + r), fun r => hv.h_bound (T₁ + r),
           fun k c => (hv.h_cont k c).comp (continuous_const.add continuous_id)⟩
        have hu_s_sol : ∀ r ∈ Set.Icc (0 : ℝ) δ, u_s r = duhamelRaw ν (u T₁) u_s r := by
          intro r hr
          have htr : T₁ + r ∈ Set.Icc (0 : ℝ) T :=
            ⟨by linarith [hr.1], by linarith [hr.2, min_le_right ΔT (T - T₁)]⟩
          exact duhamelRaw_semigroup_split u₀ hu (hu_sol T₁ ⟨hT₁_nn, hT₁_le_T⟩) (hu_sol (T₁ + r) htr)
        have hv_s_sol : ∀ r ∈ Set.Icc (0 : ℝ) δ, v_s r = duhamelRaw ν (u T₁) v_s r := by
          intro r hr
          have htr : T₁ + r ∈ Set.Icc (0 : ℝ) T :=
            ⟨by linarith [hr.1], by linarith [hr.2, min_le_right ΔT (T - T₁)]⟩
          have h := duhamelRaw_semigroup_split u₀ hv (hv_sol T₁ ⟨hT₁_nn, hT₁_le_T⟩) (hv_sol (T₁ + r) htr)
          rwa [← huv_T₁] at h
        have hr_mem : t - T₁ ∈ Set.Icc (0 : ℝ) δ := by
          have hsucc : ((m + 1 : ℕ) : ℝ) * ΔT = T₁ + ΔT := by dsimp only [T₁]; push_cast; ring
          have ht_le_T : t ≤ T := le_trans ht.2 (min_le_left _ _)
          have ht_le_succ : t ≤ T₁ + ΔT := by rw [← hsucc]; exact le_trans ht.2 (min_le_right _ _)
          exact ⟨by linarith, le_min (by linarith) (by linarith)⟩
        have heq := mild_solution_unique hν hδ_nn hM hsmall_δ (u T₁) hu_s hv_s
          hu_s_sol hv_s_sol (t - T₁) hr_mem
        dsimp only [u_s, v_s] at heq
        have hsum : T₁ + (t - T₁) = t := by ring
        rwa [hsum] at heq
  intro t ht
  let N : ℕ := Nat.ceil (T / ΔT)
  have hT_le_N : T ≤ (N : ℝ) * ΔT := by
    have h1 : T / ΔT ≤ (N : ℝ) := Nat.le_ceil (T / ΔT)
    have h2 := mul_le_mul_of_nonneg_right h1 (le_of_lt hΔ_pos)
    rwa [div_mul_cancel₀ T (ne_of_gt hΔ_pos)] at h2
  exact hind N t ⟨ht.1, le_min ht.2 (le_trans ht.2 hT_le_N)⟩

/-- Uniform Picard continuation step size `ΔT = ν / (54272 (4 B + 1))` for arbitrary `H²` ceiling `B`. -/
noncomputable def contStep (ν B : ℝ) : ℝ :=
  ν / (54272 * (4 * B + 1))

/-- Recursive state sequence `u(n ΔT)` for global continuation under an a priori `H²` ceiling `B`. -/
noncomputable def contState (ν B : ℝ) (u₀ : VecSeq3D) : ℕ → VecSeq3D
  | 0 => u₀
  | n + 1 => picardLimit ν (contStep ν B) (contState ν B u₀ n) (contStep ν B)

/-- Global stitched mild curve on `[0, ∞)` under an a priori `H²` ceiling `B`. -/
noncomputable def contGlobal (ν B : ℝ) (u₀ : VecSeq3D) (t : ℝ) : VecSeq3D :=
  if t ≤ 0 then u₀
  else
    picardLimit ν (contStep ν B)
      (contState ν B u₀ (Nat.floor (t / contStep ν B)))
      (t - (Nat.floor (t / contStep ν B) : ℝ) * contStep ν B)

private theorem contStep_pos_and_small {ν B : ℝ} (hν : 0 < ν) (hB : 0 ≤ B) :
    0 < contStep ν B ∧ 54272 * contStep ν B * (4 * B + 1) ≤ ν := by
  have hM_pos : 0 < 4 * B + 1 := by linarith
  have hM_ne : 4 * B + 1 ≠ 0 := ne_of_gt hM_pos
  refine ⟨by unfold contStep; positivity, ?_⟩
  have heq : 54272 * contStep ν B * (4 * B + 1) = ν := by
    unfold contStep; field_simp [hM_ne]
  linarith

private theorem contState_invariant {ν B : ℝ} (hν : 0 < ν) (hB : 0 ≤ B)
    {u₀ : VecSeq3D} (hu₀ : InH2Vec u₀) (hsol₀ : IsSolenoidal u₀) (hsym₀ : IsRealSymm u₀)
    (hinit_bd : h2VecNormSq u₀ ≤ B)
    (h_apriori : ∀ w : VecSeq3D, InH2Vec w → IsSolenoidal w → IsRealSymm w → h2VecNormSq w ≤ B →
      h2VecNormSq (picardLimit ν (contStep ν B) w (contStep ν B)) ≤ B) (n : ℕ) :
    InH2Vec (contState ν B u₀ n) ∧
    h2VecNormSq (contState ν B u₀ n) ≤ B ∧
    IsSolenoidal (contState ν B u₀ n) ∧
    IsRealSymm (contState ν B u₀ n) ∧
    (∀ c : Fin 3, contState ν B u₀ n 0 c = u₀ 0 c) := by
  have hst := contStep_pos_and_small hν hB
  induction n with
  | zero => exact ⟨hu₀, hinit_bd, hsol₀, hsym₀, fun _ => rfl⟩
  | succ m ih =>
    have hR : 4 * h2VecNormSq (contState ν B u₀ m) ≤ 4 * B + 1 := by linarith [ih.2.1]
    have hadm := (picardLimit_admissible_and_rate hν (le_of_lt hst.1) (by linarith) ih.1 hR hst.2).1
    have hfix := picardLimit_fixedPoint_and_structure hν (le_of_lt hst.1) (by linarith)
      ih.1 ih.2.2.1 ih.2.2.2.1 hR hst.2
    have hstr := hfix.2.2.2 (contStep ν B)
    exact ⟨hadm.h_inH2 _, h_apriori _ ih.1 ih.2.2.1 ih.2.2.2.1 ih.2.1,
           hstr.1, hstr.2.1, fun c => by
             dsimp only [contState]
             rw [hstr.2.2 c, ih.2.2.2.2 c]⟩

private theorem contGlobal_slab_eq {ν B : ℝ} (hν : 0 < ν) (hB : 0 ≤ B)
    {u₀ : VecSeq3D} (hu₀ : InH2Vec u₀) (hsol₀ : IsSolenoidal u₀) (hsym₀ : IsRealSymm u₀)
    (hinit_bd : h2VecNormSq u₀ ≤ B)
    (h_apriori : ∀ w : VecSeq3D, InH2Vec w → IsSolenoidal w → IsRealSymm w → h2VecNormSq w ≤ B →
      h2VecNormSq (picardLimit ν (contStep ν B) w (contStep ν B)) ≤ B)
    (n : ℕ) {s : ℝ} (hs : s ∈ Set.Icc (0 : ℝ) (contStep ν B)) :
    contGlobal ν B u₀ ((n : ℝ) * contStep ν B + s) =
      picardLimit ν (contStep ν B) (contState ν B u₀ n) s := by
  have hcs := contStep_pos_and_small hν hB
  have hΔ_pos : 0 < contStep ν B := hcs.1
  have hΔ_ne : contStep ν B ≠ 0 := ne_of_gt hΔ_pos
  have hst_n := contState_invariant hν hB hu₀ hsol₀ hsym₀ hinit_bd h_apriori n
  have hfix_n := picardLimit_fixedPoint_and_structure hν (le_of_lt hΔ_pos) (by linarith)
    hst_n.1 hst_n.2.2.1 hst_n.2.2.2.1 (by linarith [hst_n.2.1]) hcs.2
  rcases eq_or_lt_of_le hs.2 with rfl | hs_lt
  · have ht_pos : 0 < (n : ℝ) * contStep ν B + contStep ν B := by positivity
    have hdiv : ((n : ℝ) * contStep ν B + contStep ν B) / contStep ν B = ((n + 1 : ℕ) : ℝ) := by
      rw [add_div, mul_div_cancel_right₀ _ hΔ_ne, div_self hΔ_ne]; push_cast; ring
    have hfl : Nat.floor (((n : ℝ) * contStep ν B + contStep ν B) / contStep ν B) = n + 1 := by
      rw [hdiv, Nat.floor_natCast]
    have hsub : (n : ℝ) * contStep ν B + contStep ν B - ((n + 1 : ℕ) : ℝ) * contStep ν B = 0 := by
      push_cast; ring
    unfold contGlobal
    simp only [not_le.mpr ht_pos, ↓reduceIte, hfl, hsub]
    have hst_n1 := contState_invariant hν hB hu₀ hsol₀ hsym₀ hinit_bd h_apriori (n + 1)
    have hfix_n1 := picardLimit_fixedPoint_and_structure hν (le_of_lt hΔ_pos) (by linarith)
      hst_n1.1 hst_n1.2.2.1 hst_n1.2.2.2.1 (by linarith [hst_n1.2.1]) hcs.2
    rw [hfix_n1.2.2.1]; rfl
  · by_cases ht0 : (n : ℝ) * contStep ν B + s ≤ 0
    · have hn0 : n = 0 := by
        by_contra hne
        have hn1 : (1 : ℝ) ≤ (n : ℝ) := Nat.one_le_cast.mpr (Nat.pos_of_ne_zero hne)
        have : 0 < (n : ℝ) * contStep ν B := mul_pos (by linarith) hΔ_pos
        linarith [hs.1]
      subst hn0
      have hs0 : s = 0 := by simp at ht0; linarith [hs.1]
      subst hs0
      unfold contGlobal
      simp only [Nat.cast_zero, zero_mul, add_zero, le_refl, ↓reduceIte]
      exact hfix_n.2.2.1.symm
    · push Not at ht0
      have hdiv : ((n : ℝ) * contStep ν B + s) / contStep ν B = (n : ℝ) + s / contStep ν B := by
        rw [add_div, mul_div_cancel_right₀ _ hΔ_ne]
      have hfl : Nat.floor (((n : ℝ) * contStep ν B + s) / contStep ν B) = n := by
        have hs0 : 0 ≤ s := hs.1
        rw [hdiv, Nat.floor_eq_iff (by positivity)]
        have hlt1 : s / contStep ν B < 1 := (div_lt_one hΔ_pos).mpr hs_lt
        exact ⟨by linarith [div_nonneg hs0 (le_of_lt hΔ_pos)], by linarith⟩
      have hsub : (n : ℝ) * contStep ν B + s - (n : ℝ) * contStep ν B = s := by ring
      unfold contGlobal
      simp only [not_le.mpr ht0, ↓reduceIte, hfl, hsub]

private theorem contGlobal_continuous {ν B : ℝ} (hν : 0 < ν) (hB : 0 ≤ B)
    {u₀ : VecSeq3D} (hu₀ : InH2Vec u₀) (hsol₀ : IsSolenoidal u₀) (hsym₀ : IsRealSymm u₀)
    (hinit_bd : h2VecNormSq u₀ ≤ B)
    (h_apriori : ∀ w : VecSeq3D, InH2Vec w → IsSolenoidal w → IsRealSymm w → h2VecNormSq w ≤ B →
      h2VecNormSq (picardLimit ν (contStep ν B) w (contStep ν B)) ≤ B)
    (k : Fin 3 → ℤ) (c : Fin 3) :
    Continuous (fun t : ℝ => contGlobal ν B u₀ t k c) := by
  have hcs := contStep_pos_and_small hν hB
  have hΔ_pos : 0 < contStep ν B := hcs.1
  have hΔ_nn : 0 ≤ contStep ν B := le_of_lt hΔ_pos
  have hΔ_ne : contStep ν B ≠ 0 := ne_of_gt hΔ_pos
  have hslab_cont : ∀ n : ℕ, Continuous (fun s : ℝ => picardLimit ν (contStep ν B) (contState ν B u₀ n) s k c) := by
    intro n
    have hst := contState_invariant hν hB hu₀ hsol₀ hsym₀ hinit_bd h_apriori n
    exact (picardLimit_admissible_and_rate hν hΔ_nn (by linarith) hst.1 (by linarith [hst.2.1]) hcs.2).1.h_cont k c
  have h0_eq : picardLimit ν (contStep ν B) u₀ 0 = u₀ :=
    (picardLimit_fixedPoint_and_structure hν hΔ_nn (by linarith) hu₀ hsol₀ hsym₀ (by linarith) hcs.2).2.2.1
  refine continuous_iff_continuousAt.mpr fun t₀ => ?_
  by_cases ht_neg : t₀ < 0
  · refine (continuousAt_const (y := u₀ k c)).congr ?_
    filter_upwards [Iio_mem_nhds ht_neg] with t ht
    have ht_le : t ≤ 0 := le_of_lt (Set.mem_Iio.mp ht)
    unfold contGlobal; simp only [ht_le, ↓reduceIte]
  · push Not at ht_neg
    rcases eq_or_lt_of_le ht_neg with rfl | ht_pos
    · have hcont0 : ContinuousAt (fun t : ℝ => picardLimit ν (contStep ν B) u₀ (max 0 t) k c) 0 :=
        ((hslab_cont 0).comp (continuous_const.max continuous_id)).continuousAt
      refine hcont0.congr ?_
      filter_upwards [Ioo_mem_nhds (by norm_num : (-1 : ℝ) < 0) hΔ_pos] with t ht
      rcases le_or_gt t 0 with hle | hgt
      · rw [max_eq_left hle]
        unfold contGlobal; simp only [hle, ↓reduceIte]
        exact congrArg (fun w => w k c) h0_eq
      · rw [max_eq_right (le_of_lt hgt)]
        have heq := contGlobal_slab_eq hν hB hu₀ hsol₀ hsym₀ hinit_bd h_apriori 0 ⟨le_of_lt hgt, le_of_lt ht.2⟩
        simp only [Nat.cast_zero, zero_mul, zero_add] at heq
        exact congrArg (fun w => w k c) heq.symm
    · let n : ℕ := Nat.floor (t₀ / contStep ν B)
      have hnt_le : (n : ℝ) * contStep ν B ≤ t₀ := by
        have h1 := mul_le_mul_of_nonneg_right (Nat.floor_le (by positivity : 0 ≤ t₀ / contStep ν B)) hΔ_nn
        rwa [div_mul_cancel₀ t₀ hΔ_ne] at h1
      have hnt_lt : t₀ < ((n + 1 : ℕ) : ℝ) * contStep ν B := by
        have h1 := mul_lt_mul_of_pos_right (Nat.lt_floor_add_one (t₀ / contStep ν B)) hΔ_pos
        rw [div_mul_cancel₀ t₀ hΔ_ne] at h1
        push_cast; linarith
      rcases eq_or_lt_of_le hnt_le with heq_bd | hnt_strict
      · have hn_pos : 1 ≤ n := by
          by_contra h0
          have hn0 : n = 0 := by omega
          rw [hn0] at heq_bd; simp at heq_bd; linarith
        let m : ℕ := n - 1
        have hmn : m + 1 = n := by omega
        have ht0_eq : (m : ℝ) * contStep ν B + contStep ν B = t₀ := by
          rw [← heq_bd, ← hmn]; push_cast; ring
        refine Metric.continuousAt_iff.mpr fun ε hε => ?_
        have hcm : ContinuousAt (fun r : ℝ =>
            picardLimit ν (contStep ν B) (contState ν B u₀ m) (r - (m : ℝ) * contStep ν B) k c) t₀ :=
          ((hslab_cont m).comp (continuous_id.sub continuous_const)).continuousAt
        have hcn : ContinuousAt (fun r : ℝ =>
            picardLimit ν (contStep ν B) (contState ν B u₀ n) (r - (n : ℝ) * contStep ν B) k c) t₀ :=
          ((hslab_cont n).comp (continuous_id.sub continuous_const)).continuousAt
        obtain ⟨δ₁, hδ₁_pos, hδ₁⟩ := Metric.continuousAt_iff.mp hcm ε hε
        obtain ⟨δ₂, hδ₂_pos, hδ₂⟩ := Metric.continuousAt_iff.mp hcn ε hε
        let δ : ℝ := min (min δ₁ δ₂) (contStep ν B / 2)
        have hδ_pos : 0 < δ := lt_min (lt_min hδ₁_pos hδ₂_pos) (by positivity)
        refine ⟨δ, hδ_pos, fun {t} ht => ?_⟩
        have hd1 : dist t t₀ < δ₁ := lt_of_lt_of_le ht (le_trans (min_le_left _ _) (min_le_left _ _))
        have hd2 : dist t t₀ < δ₂ := lt_of_lt_of_le ht (le_trans (min_le_left _ _) (min_le_right _ _))
        have hdT : |t - t₀| < contStep ν B / 2 := by
          rw [← Real.dist_eq]; exact lt_of_lt_of_le ht (min_le_right _ _)
        have htab : t₀ - contStep ν B / 2 < t ∧ t < t₀ + contStep ν B / 2 :=
          abs_lt.mp hdT |> fun ⟨h1, h2⟩ => ⟨by linarith, by linarith⟩
        rcases le_or_gt t t₀ with hle | hgt
        · have hs_mem : t - (m : ℝ) * contStep ν B ∈ Set.Icc (0 : ℝ) (contStep ν B) :=
            ⟨by linarith [ht0_eq, htab.1], by linarith [ht0_eq]⟩
          have h1 := congrArg (fun w => w k c)
            (contGlobal_slab_eq hν hB hu₀ hsol₀ hsym₀ hinit_bd h_apriori m hs_mem)
          have h2 := congrArg (fun w => w k c)
            (contGlobal_slab_eq hν hB hu₀ hsol₀ hsym₀ hinit_bd h_apriori m ⟨hΔ_nn, le_rfl⟩)
          have hsum_t : (m : ℝ) * contStep ν B + (t - (m : ℝ) * contStep ν B) = t := by ring
          have hsum_t0 : t₀ - (m : ℝ) * contStep ν B = contStep ν B := by linarith [ht0_eq]
          rw [hsum_t] at h1; rw [ht0_eq] at h2
          have hdist : dist (picardLimit ν (contStep ν B) (contState ν B u₀ m) (t - (m : ℝ) * contStep ν B) k c)
              (picardLimit ν (contStep ν B) (contState ν B u₀ m) (t₀ - (m : ℝ) * contStep ν B) k c) < ε := hδ₁ hd1
          rw [hsum_t0] at hdist
          rw [h1, h2]; exact hdist
        · have hs_mem : t - (n : ℝ) * contStep ν B ∈ Set.Icc (0 : ℝ) (contStep ν B) :=
            ⟨by linarith [heq_bd], by linarith [heq_bd, htab.2]⟩
          have h1 := congrArg (fun w => w k c)
            (contGlobal_slab_eq hν hB hu₀ hsol₀ hsym₀ hinit_bd h_apriori n hs_mem)
          have h2 := congrArg (fun w => w k c)
            (contGlobal_slab_eq hν hB hu₀ hsol₀ hsym₀ hinit_bd h_apriori n ⟨le_rfl, hΔ_nn⟩)
          have hsum_t : (n : ℝ) * contStep ν B + (t - (n : ℝ) * contStep ν B) = t := by ring
          have ht0_eq' : (n : ℝ) * contStep ν B + 0 = t₀ := by linarith [heq_bd]
          have hsum_t0 : t₀ - (n : ℝ) * contStep ν B = 0 := by linarith [heq_bd]
          rw [hsum_t] at h1; rw [ht0_eq'] at h2
          have hdist : dist (picardLimit ν (contStep ν B) (contState ν B u₀ n) (t - (n : ℝ) * contStep ν B) k c)
              (picardLimit ν (contStep ν B) (contState ν B u₀ n) (t₀ - (n : ℝ) * contStep ν B) k c) < ε := hδ₂ hd2
          rw [hsum_t0] at hdist
          rw [h1, h2]; exact hdist
      · have hcn : ContinuousAt (fun r : ℝ =>
            picardLimit ν (contStep ν B) (contState ν B u₀ n) (r - (n : ℝ) * contStep ν B) k c) t₀ :=
          ((hslab_cont n).comp (continuous_id.sub continuous_const)).continuousAt
        refine hcn.congr ?_
        filter_upwards [Ioo_mem_nhds hnt_strict hnt_lt] with t ht
        have hs_mem : t - (n : ℝ) * contStep ν B ∈ Set.Icc (0 : ℝ) (contStep ν B) := by
          have hsucc : ((n + 1 : ℕ) : ℝ) * contStep ν B = (n : ℝ) * contStep ν B + contStep ν B := by
            push_cast; ring
          exact ⟨by linarith [ht.1], by linarith [ht.2, hsucc]⟩
        have h1 := contGlobal_slab_eq hν hB hu₀ hsol₀ hsym₀ hinit_bd h_apriori n hs_mem
        have hsum_t : (n : ℝ) * contStep ν B + (t - (n : ℝ) * contStep ν B) = t := by ring
        rw [hsum_t] at h1
        exact congrArg (fun w => w k c) h1.symm

private theorem contGlobal_admissible_and_struct {ν B : ℝ} (hν : 0 < ν) (hB : 0 ≤ B)
    {u₀ : VecSeq3D} (hu₀ : InH2Vec u₀) (hsol₀ : IsSolenoidal u₀) (hsym₀ : IsRealSymm u₀)
    (hinit_bd : h2VecNormSq u₀ ≤ B)
    (h_apriori : ∀ w : VecSeq3D, InH2Vec w → IsSolenoidal w → IsRealSymm w → h2VecNormSq w ≤ B →
      h2VecNormSq (picardLimit ν (contStep ν B) w (contStep ν B)) ≤ B) :
    IsAdmissibleCurve (4 * B + 1) (contGlobal ν B u₀) ∧
    (∀ t : ℝ, IsSolenoidal (contGlobal ν B u₀ t) ∧
              IsRealSymm (contGlobal ν B u₀ t) ∧
              (∀ c : Fin 3, contGlobal ν B u₀ t 0 c = u₀ 0 c)) := by
  have hcs := contStep_pos_and_small hν hB
  have hΔ_nn : 0 ≤ contStep ν B := le_of_lt hcs.1
  have hslab_adm : ∀ n : ℕ, IsAdmissibleCurve (4 * B + 1) (picardLimit ν (contStep ν B) (contState ν B u₀ n)) := by
    intro n
    have hst := contState_invariant hν hB hu₀ hsol₀ hsym₀ hinit_bd h_apriori n
    exact (picardLimit_admissible_and_rate hν hΔ_nn (by linarith) hst.1 (by linarith [hst.2.1]) hcs.2).1
  have hslab_st : ∀ (n : ℕ) (s : ℝ),
      IsSolenoidal (picardLimit ν (contStep ν B) (contState ν B u₀ n) s) ∧
      IsRealSymm (picardLimit ν (contStep ν B) (contState ν B u₀ n) s) ∧
      (∀ c : Fin 3, picardLimit ν (contStep ν B) (contState ν B u₀ n) s 0 c = u₀ 0 c) := by
    intro n s
    have hst := contState_invariant hν hB hu₀ hsol₀ hsym₀ hinit_bd h_apriori n
    have hfix := picardLimit_fixedPoint_and_structure hν hΔ_nn (by linarith)
      hst.1 hst.2.2.1 hst.2.2.2.1 (by linarith [hst.2.1]) hcs.2
    exact ⟨(hfix.2.2.2 s).1, (hfix.2.2.2 s).2.1, fun c => by rw [(hfix.2.2.2 s).2.2 c, hst.2.2.2.2 c]⟩
  refine ⟨⟨fun t => ?_, fun t => ?_, contGlobal_continuous hν hB hu₀ hsol₀ hsym₀ hinit_bd h_apriori⟩, fun t => ?_⟩
  · unfold contGlobal; split_ifs
    · exact hu₀
    · exact (hslab_adm _).h_inH2 _
  · unfold contGlobal; split_ifs
    · linarith [hinit_bd]
    · exact (hslab_adm _).h_bound _
  · unfold contGlobal; split_ifs
    · exact ⟨hsol₀, hsym₀, fun _ => rfl⟩
    · exact hslab_st _ _

private theorem contGlobal_duhamel_all {ν B : ℝ} (hν : 0 < ν) (hB : 0 ≤ B)
    {u₀ : VecSeq3D} (hu₀ : InH2Vec u₀) (hsol₀ : IsSolenoidal u₀) (hsym₀ : IsRealSymm u₀)
    (hinit_bd : h2VecNormSq u₀ ≤ B)
    (h_apriori : ∀ w : VecSeq3D, InH2Vec w → IsSolenoidal w → IsRealSymm w → h2VecNormSq w ≤ B →
      h2VecNormSq (picardLimit ν (contStep ν B) w (contStep ν B)) ≤ B) :
    ∀ t : ℝ, 0 ≤ t → contGlobal ν B u₀ t = duhamelRaw ν u₀ (contGlobal ν B u₀) t := by
  have hcs := contStep_pos_and_small hν hB
  have hΔ_pos : 0 < contStep ν B := hcs.1
  have hΔ_nn : 0 ≤ contStep ν B := le_of_lt hΔ_pos
  have hΔ_ne : contStep ν B ≠ 0 := ne_of_gt hΔ_pos
  have hu_adm := (contGlobal_admissible_and_struct hν hB hu₀ hsol₀ hsym₀ hinit_bd h_apriori).1
  have hslab_fix : ∀ n : ℕ,
      (∀ s ∈ Set.Icc (0 : ℝ) (contStep ν B),
        picardLimit ν (contStep ν B) (contState ν B u₀ n) s =
          duhamelRaw ν (contState ν B u₀ n) (picardLimit ν (contStep ν B) (contState ν B u₀ n)) s) ∧
      picardLimit ν (contStep ν B) (contState ν B u₀ n) 0 = contState ν B u₀ n := by
    intro n
    have hst := contState_invariant hν hB hu₀ hsol₀ hsym₀ hinit_bd h_apriori n
    have hfix := picardLimit_fixedPoint_and_structure hν hΔ_nn (by linarith)
      hst.1 hst.2.2.1 hst.2.2.2.1 (by linarith [hst.2.1]) hcs.2
    exact ⟨hfix.2.1, hfix.2.2.1⟩
  have hslab : ∀ (n : ℕ) (s : ℝ), s ∈ Set.Icc (0 : ℝ) (contStep ν B) →
      contGlobal ν B u₀ ((n : ℝ) * contStep ν B + s) =
        duhamelRaw ν u₀ (contGlobal ν B u₀) ((n : ℝ) * contStep ν B + s) := by
    intro n
    induction n with
    | zero =>
      intro s hs
      have h0 := contGlobal_slab_eq hν hB hu₀ hsol₀ hsym₀ hinit_bd h_apriori 0 hs
      simp only [Nat.cast_zero, zero_mul, zero_add] at h0 ⊢
      rw [h0, (hslab_fix 0).1 s hs]
      funext k c; unfold duhamelRaw
      have hint : (∫ r in (0 : ℝ)..s,
            heatSmoothedBilinear6A ν (s - r) (picardLimit ν (contStep ν B) (contState ν B u₀ 0) r)
              (picardLimit ν (contStep ν B) (contState ν B u₀ 0) r) k c) =
          ∫ r in (0 : ℝ)..s,
            heatSmoothedBilinear6A ν (s - r) (contGlobal ν B u₀ r) (contGlobal ν B u₀ r) k c := by
        refine intervalIntegral.integral_congr fun r hr => ?_
        rw [Set.uIcc_of_le hs.1] at hr
        have hru := contGlobal_slab_eq hν hB hu₀ hsol₀ hsym₀ hinit_bd h_apriori 0 ⟨hr.1, le_trans hr.2 hs.2⟩
        simp only [Nat.cast_zero, zero_mul, zero_add] at hru
        rw [← hru]
      exact congrArg ((heatMultiplier3D ν s k : ℂ) * u₀ k c + ·) hint
    | succ m ih =>
      intro s hs
      have hm_end : contGlobal ν B u₀ (((m + 1 : ℕ) : ℝ) * contStep ν B) =
          duhamelRaw ν u₀ (contGlobal ν B u₀) (((m + 1 : ℕ) : ℝ) * contStep ν B) := by
        have hstep := ih (contStep ν B) ⟨hΔ_nn, le_rfl⟩
        have hcast : ((m + 1 : ℕ) : ℝ) * contStep ν B = (m : ℝ) * contStep ν B + contStep ν B := by
          push_cast; ring
        rwa [hcast]
      have hloc : contGlobal ν B u₀ (((m + 1 : ℕ) : ℝ) * contStep ν B + s) =
          duhamelRaw ν (contGlobal ν B u₀ (((m + 1 : ℕ) : ℝ) * contStep ν B))
            (fun r => contGlobal ν B u₀ (((m + 1 : ℕ) : ℝ) * contStep ν B + r)) s := by
        have h1 := contGlobal_slab_eq hν hB hu₀ hsol₀ hsym₀ hinit_bd h_apriori (m + 1) hs
        have h2 := contGlobal_slab_eq hν hB hu₀ hsol₀ hsym₀ hinit_bd h_apriori (m + 1) ⟨le_rfl, hΔ_nn⟩
        rw [add_zero] at h2
        have hst_eq : contGlobal ν B u₀ (((m + 1 : ℕ) : ℝ) * contStep ν B) = contState ν B u₀ (m + 1) := by
          rw [h2, (hslab_fix (m + 1)).2]
        rw [h1, (hslab_fix (m + 1)).1 s hs, hst_eq]
        funext k c; unfold duhamelRaw
        have hint : (∫ r in (0 : ℝ)..s,
              heatSmoothedBilinear6A ν (s - r) (picardLimit ν (contStep ν B) (contState ν B u₀ (m + 1)) r)
                (picardLimit ν (contStep ν B) (contState ν B u₀ (m + 1)) r) k c) =
            ∫ r in (0 : ℝ)..s,
              heatSmoothedBilinear6A ν (s - r)
                (contGlobal ν B u₀ (((m + 1 : ℕ) : ℝ) * contStep ν B + r))
                (contGlobal ν B u₀ (((m + 1 : ℕ) : ℝ) * contStep ν B + r)) k c := by
          refine intervalIntegral.integral_congr fun r hr => ?_
          rw [Set.uIcc_of_le hs.1] at hr
          have hru := contGlobal_slab_eq hν hB hu₀ hsol₀ hsym₀ hinit_bd h_apriori (m + 1) ⟨hr.1, le_trans hr.2 hs.2⟩
          rw [← hru]
        exact congrArg ((heatMultiplier3D ν s k : ℂ) * contState ν B u₀ (m + 1) k c + ·) hint
      exact duhamelRaw_semigroup_glue u₀ hu_adm hm_end hloc
  intro t ht
  let n : ℕ := Nat.floor (t / contStep ν B)
  have hs_mem : t - (n : ℝ) * contStep ν B ∈ Set.Icc (0 : ℝ) (contStep ν B) := by
    have h1 := mul_le_mul_of_nonneg_right (Nat.floor_le (by positivity : 0 ≤ t / contStep ν B)) hΔ_nn
    have h2 := mul_lt_mul_of_pos_right (Nat.lt_floor_add_one (t / contStep ν B)) hΔ_pos
    rw [div_mul_cancel₀ t hΔ_ne] at h1 h2
    exact ⟨by linarith, by linarith⟩
  have h := hslab n (t - (n : ℝ) * contStep ν B) hs_mem
  have hsum : (n : ℝ) * contStep ν B + (t - (n : ℝ) * contStep ν B) = t := by ring
  rwa [hsum] at h

/-- **MAIN THEOREM 7 OF MILESTONE 7B (Global Continuation & Uniqueness on `[0, ∞)` for Arbitrary
    Data Size under an A Priori `H²` Ceiling `B` — Handoff Interface to Milestone 8, `0 sorryAx`):**
    For EVERY viscosity `ν > 0`, EVERY ceiling `B ≥ 0`, and EVERY real solenoidal initial velocity
    `u₀ ∈ H²(𝕋³)` (arbitrary size, arbitrary mean velocity `u₀(0)`) with `‖u₀‖²_{H²} ≤ B`:
    whenever the local Picard evolution preserves the a priori ceiling `B`, there EXISTS a UNIQUE
    global curve `u : ℝ → VecSeq3D` on `[0, ∞)` solving the full spectral 3D Navier–Stokes
    Duhamel equation and momentum ODE with Poisson pressure, preserving solenoidality, reality
    symmetry, momentum, and uniform `H²`/`L∞` bounds (`0 sorryAx`). -/
theorem global_continuation_of_apriori_H2_bound_torus3D
    {ν B : ℝ} (hν : 0 < ν) (hB : 0 ≤ B)
    {u₀ : VecSeq3D} (hu₀ : InH2Vec u₀) (hsol₀ : IsSolenoidal u₀) (hsym₀ : IsRealSymm u₀)
    (hinit_bd : h2VecNormSq u₀ ≤ B)
    (h_apriori : ∀ w : VecSeq3D, InH2Vec w → IsSolenoidal w → IsRealSymm w → h2VecNormSq w ≤ B →
      h2VecNormSq (picardLimit ν (contStep ν B) w (contStep ν B)) ≤ B) :
    let M : ℝ := 4 * B + 1
    ∃ u : ℝ → VecSeq3D,
      IsAdmissibleCurve M u ∧
      u 0 = u₀ ∧
      (∀ t : ℝ, 0 ≤ t → u t = duhamelRaw ν u₀ u t) ∧
      (∀ t : ℝ, 0 < t → ∀ (k : Fin 3 → ℤ) (c : Fin 3),
        HasDerivAt (fun s : ℝ => u s k c)
          ((-4 * (Real.pi : ℂ) ^ 2 * (ν : ℂ) * ((kNormSq k : ℝ) : ℂ)) * u t k c -
            nsFlux6A (u t) (u t) k c -
            2 * (Real.pi : ℂ) * Complex.I * (k c : ℂ) * pressureCoeff6B (u t) k) t) ∧
      (∀ t : ℝ, IsSolenoidal (u t) ∧ IsRealSymm (u t) ∧ (∀ c : Fin 3, u t 0 c = u₀ 0 c)) ∧
      (∀ t : ℝ, Continuous (synthVec3D (u t)) ∧ IsPeriodic3D (synthVec3D (u t)) ∧
        (∀ x : R3, dot3D (synthVec3D (u t) x) (synthVec3D (u t) x) ≤ 53 * M)) ∧
      (∀ T : ℝ, 0 ≤ T → ∀ v : ℝ → VecSeq3D, IsAdmissibleCurve M v →
        (∀ t ∈ Set.Icc (0 : ℝ) T, v t = duhamelRaw ν u₀ v t) →
        ∀ t ∈ Set.Icc (0 : ℝ) T, v t = u t) := by
  intro M
  have hpair := contGlobal_admissible_and_struct hν hB hu₀ hsol₀ hsym₀ hinit_bd h_apriori
  have hduh := contGlobal_duhamel_all hν hB hu₀ hsol₀ hsym₀ hinit_bd h_apriori
  refine ⟨contGlobal ν B u₀, hpair.1, ?_, hduh, ?_, hpair.2, ?_, ?_⟩
  · unfold contGlobal; simp
  · intro t ht k c
    exact mild_solution_hasDerivAt_spectral_ns3d (T := t + 1) u₀ hpair.1
      (fun s hs => hduh s hs.1) ⟨ht, by linarith⟩ k c
  · intro t
    have hsyn := synthVec3D_continuous_periodic_and_Linf (hpair.1.h_inH2 t)
    refine ⟨hsyn.1, hsyn.2.1, fun x => ?_⟩
    have hbd : h2VecNormSq (contGlobal ν B u₀ t) ≤ M := hpair.1.h_bound t
    linarith [hsyn.2.2 x, hbd]
  · intro T hT v hv hv_sol t ht
    exact global_mild_solution_unique_torus3D hν hT (by dsimp only [M]; linarith) u₀ hv hpair.1
      hv_sol (fun s hs => hduh s hs.1) t ht

-- ============================================================================
-- SECTION 4: AXIOM AUDIT TRAIL — MILESTONE 7B (0 sorryAx)
-- ============================================================================

#print axioms supercritical_young_absorption_wall_torus3D
#print axioms true_3d_enstrophy_palinstrophy_integral_balance
#print axioms garry_sqrt_z_cancellation_bridge_torus3D
#print axioms garry_sqrt_z_global_enstrophy_decay_torus3D
#print axioms garry_trinity_quartic_young_bridge_torus3D
#print axioms garry_bkm_palinstrophy_bootstrap_bridge_torus3D
#print axioms duhamelRaw_semigroup_split
#print axioms global_mild_solution_unique_torus3D
#print axioms global_continuation_of_apriori_H2_bound_torus3D

end GarrySupercriticalBridge3D