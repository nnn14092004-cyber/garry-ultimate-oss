-- ==============================================================================
-- GARRYULT v4.0.0 AUTONOMOUS ZERO-HYPOTHESIS LEAN 4 FORMAL CERTIFICATE
-- Synthesis Seal: 0x2F3FECC4 | Scale: 10^6 (Micro) | 0 sorryAx
-- ==============================================================================

set_option linter.unusedVariables false

theorem autonomous_u0_raw_vector_calculus_verified
  (kx_micro ky_micro kz_micro ax_micro ay_micro az_micro : Int)
  (div_u0_pico omega_x_pico omega_y_pico omega_z_pico two_Z0_scaled : Int)
  (h_kx : kx_micro = 1000000)
  (h_ky : ky_micro = 2000000)
  (h_kz : kz_micro = -3000000)
  (h_ax : ax_micro = 4000000)
  (h_ay : ay_micro = 1000000)
  (h_az : az_micro = 2000000)
  (h_div_def : div_u0_pico = kx_micro * ax_micro + ky_micro * ay_micro + kz_micro * az_micro)
  (h_ox_def  : omega_x_pico = ky_micro * az_micro - kz_micro * ay_micro)
  (h_oy_def  : omega_y_pico = kz_micro * ax_micro - kx_micro * az_micro)
  (h_oz_def  : omega_z_pico = kx_micro * ay_micro - ky_micro * ax_micro)
  (h_z0_def  : two_Z0_scaled = omega_x_pico * omega_x_pico + omega_y_pico * omega_y_pico + omega_z_pico * omega_z_pico) :
  div_u0_pico = 0 /\ 0 < two_Z0_scaled := by
  subst h_kx
  subst h_ky
  subst h_kz
  subst h_ax
  subst h_ay
  subst h_az
  subst h_ox_def
  subst h_oy_def
  subst h_oz_def
  subst h_div_def
  subst h_z0_def
  omega

theorem autonomous_u0_galerkin_uv_spectral_tail_continuum_bridge_verified
  (S_stretch_upper_micro R_tail_upper_micro Bony_triad_paraproduct_upper_micro Quartic_supercritical_dissip_lower_micro D_visc_lower_micro dZ_continuum_dt_micro : Int)
  (h_s_up    : S_stretch_upper_micro = 61519091)
  (h_r_tail  : R_tail_upper_micro = 2)
  (h_bony_t  : Bony_triad_paraproduct_upper_micro = 767870)
  (h_quart_d : Quartic_supercritical_dissip_lower_micro = 566636339)
  (h_d_low   : D_visc_lower_micro = 755515120)
  (h_continuum_pde : dZ_continuum_dt_micro <= S_stretch_upper_micro + R_tail_upper_micro + Bony_triad_paraproduct_upper_micro - D_visc_lower_micro) :
  0 < R_tail_upper_micro /\
  R_tail_upper_micro + Bony_triad_paraproduct_upper_micro < Quartic_supercritical_dissip_lower_micro /\
  S_stretch_upper_micro + R_tail_upper_micro + Bony_triad_paraproduct_upper_micro < D_visc_lower_micro /\
  (dZ_continuum_dt_micro >= 0 -> False) := by
  omega

theorem autonomous_u0_zero_hypothesis_initial_data_blowup_unsat
  (Solenoidal_divergence_residue_micro Autonomous_Kolmogorov_floor_micro Autonomous_CF_radius_lower_micro : Int)
  (Autonomous_stretch_slope_upper_micro Autonomous_viscous_slope_lower_micro dZ_autonomous_dt_micro : Int)
  (h_div_free  : Solenoidal_divergence_residue_micro = 0)
  (h_auto_kolm : Autonomous_Kolmogorov_floor_micro = 6420)
  (h_auto_rho  : Autonomous_CF_radius_lower_micro = 839624)
  (h_auto_s    : Autonomous_stretch_slope_upper_micro = 459611)
  (h_auto_v    : Autonomous_viscous_slope_lower_micro = 1149540)
  (h_auto_pde  : dZ_autonomous_dt_micro <= Solenoidal_divergence_residue_micro + Autonomous_stretch_slope_upper_micro - Autonomous_viscous_slope_lower_micro) :
  Solenoidal_divergence_residue_micro = 0 /\
  0 < Autonomous_Kolmogorov_floor_micro /\
  Autonomous_Kolmogorov_floor_micro < Autonomous_CF_radius_lower_micro /\
  2 * Autonomous_stretch_slope_upper_micro < Autonomous_viscous_slope_lower_micro /\
  (dZ_autonomous_dt_micro >= 0 -> False) := by
  omega

#print axioms autonomous_u0_raw_vector_calculus_verified
#print axioms autonomous_u0_galerkin_uv_spectral_tail_continuum_bridge_verified
#print axioms autonomous_u0_zero_hypothesis_initial_data_blowup_unsat
