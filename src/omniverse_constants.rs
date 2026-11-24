//! Compile-time physical constants and 10-manifold hydrodynamic parameter lookup table (LUT)
//! for 3D incompressible Navier-Stokes enstrophy, BKM, Serrin, and CKN regularity benchmarks.

pub const KOLMOGOROV_FIVE_THIRDS_EXP: f64 = 1.666_666_666_67;
pub const KOLMOGOROV_CONSTANT_CK: f64 = 1.50;
pub const SERRIN_CRITICAL_INDEX: f64 = 1.000_000;
pub const SOBOLEV_3D_CRITICAL_EXP: f64 = 6.0;
pub const LADYSHENSKAYA_CONST_C3: f64 = 0.385_900;
pub const FINE_STRUCTURE_ALPHA: f64 = 0.007_297_352_569_3;
pub const PLANCK_REDUCED_EV_S: f64 = 6.582_119_569e-16;
pub const BOLTZMANN_K_J_K: f64 = 1.380_649e-23;

#[derive(Debug, Clone, Copy, PartialEq)]
pub struct OmniverseFlowManifoldSpec {
    pub code: &'static str,
    pub name: &'static str,
    pub kinematic_viscosity_nu: f64,
    pub characteristic_velocity_u0: f64,
    pub integral_length_l0: f64,
    pub initial_enstrophy_z0: f64,
    pub helicity_coherence_cos: f64,
    pub dyadic_shell_cutoff_j: u32,
    pub serrin_exponent_p: f64,
    pub serrin_exponent_q: f64,
    pub pubcf_alignment_radius_rho: f64,
    pub waterfall_drop_head_m: f64,
    pub tailwater_river_depth_m: f64,
    pub omniverse_coupling_gamma: f64,
}

pub const OMNIVERSE_MANIFOLD_CATALOG: [OmniverseFlowManifoldSpec; 10] = [
    OmniverseFlowManifoldSpec {
        code: "omniverse_10pillar_unifier",
        name: "Garry 10-Pillar Omniverse Unified Millennium Navier-Stokes R^3 Manifold (L1->L2 Waterfall-to-River Attractor)",
        kinematic_viscosity_nu: 0.0010,
        characteristic_velocity_u0: 12.50,
        integral_length_l0: 2.40,
        initial_enstrophy_z0: 185.0,
        helicity_coherence_cos: 0.885,
        dyadic_shell_cutoff_j: 18,
        serrin_exponent_p: 4.0,
        serrin_exponent_q: 6.0,
        pubcf_alignment_radius_rho: 0.65,
        waterfall_drop_head_m: 45.0,
        tailwater_river_depth_m: 6.80,
        omniverse_coupling_gamma: 1.618,
    },
    OmniverseFlowManifoldSpec {
        code: "prandtl_navier_river",
        name: "Waterfall Plunge-Pool Vortex Trapping to Laminar Tailwater River Transition (L1->L2 Hydraulic Dissipation)",
        kinematic_viscosity_nu: 0.0012,
        characteristic_velocity_u0: 18.00,
        integral_length_l0: 3.20,
        initial_enstrophy_z0: 320.0,
        helicity_coherence_cos: 0.910,
        dyadic_shell_cutoff_j: 20,
        serrin_exponent_p: 5.0,
        serrin_exponent_q: 5.0,
        pubcf_alignment_radius_rho: 0.78,
        waterfall_drop_head_m: 85.0,
        tailwater_river_depth_m: 11.50,
        omniverse_coupling_gamma: 1.850,
    },
    OmniverseFlowManifoldSpec {
        code: "taylor_green_vortex",
        name: "3D Periodic Torus T^3 Taylor-Green Vortex Stretching & Enstrophy Peak Cascade",
        kinematic_viscosity_nu: 0.0015,
        characteristic_velocity_u0: 8.50,
        integral_length_l0: 1.60,
        initial_enstrophy_z0: 140.0,
        helicity_coherence_cos: 0.820,
        dyadic_shell_cutoff_j: 16,
        serrin_exponent_p: 4.0,
        serrin_exponent_q: 6.0,
        pubcf_alignment_radius_rho: 0.55,
        waterfall_drop_head_m: 24.0,
        tailwater_river_depth_m: 4.20,
        omniverse_coupling_gamma: 1.250,
    },
    OmniverseFlowManifoldSpec {
        code: "beltrami_helical_flow",
        name: "Arnold-Beltrami-Childress (ABC) Force-Free Helical Eigen-Vortex (curl u = lambda u, Lamb Vector u x omega = 0)",
        kinematic_viscosity_nu: 0.0008,
        characteristic_velocity_u0: 15.00,
        integral_length_l0: 2.00,
        initial_enstrophy_z0: 210.0,
        helicity_coherence_cos: 0.965,
        dyadic_shell_cutoff_j: 19,
        serrin_exponent_p: 6.0,
        serrin_exponent_q: 4.5,
        pubcf_alignment_radius_rho: 0.92,
        waterfall_drop_head_m: 38.0,
        tailwater_river_depth_m: 7.40,
        omniverse_coupling_gamma: 1.720,
    },
    OmniverseFlowManifoldSpec {
        code: "kolmogorov_k41_cascade",
        name: "Kolmogorov K41 Inertial Subrange k^(-5/3) Littlewood-Paley Dyadic Shell & Kraichnan Viscous Cutoff",
        kinematic_viscosity_nu: 0.0005,
        characteristic_velocity_u0: 22.00,
        integral_length_l0: 4.00,
        initial_enstrophy_z0: 480.0,
        helicity_coherence_cos: 0.845,
        dyadic_shell_cutoff_j: 22,
        serrin_exponent_p: 3.0,
        serrin_exponent_q: 9.0,
        pubcf_alignment_radius_rho: 0.62,
        waterfall_drop_head_m: 110.0,
        tailwater_river_depth_m: 14.00,
        omniverse_coupling_gamma: 1.940,
    },
    OmniverseFlowManifoldSpec {
        code: "leray_hopf_plunge_pool",
        name: "Jean Leray & Eberhard Hopf Weak-to-Strong Solution Regularization & Energy Inequality Manifold",
        kinematic_viscosity_nu: 0.0020,
        characteristic_velocity_u0: 9.80,
        integral_length_l0: 1.80,
        initial_enstrophy_z0: 165.0,
        helicity_coherence_cos: 0.875,
        dyadic_shell_cutoff_j: 15,
        serrin_exponent_p: 4.0,
        serrin_exponent_q: 6.0,
        pubcf_alignment_radius_rho: 0.70,
        waterfall_drop_head_m: 32.0,
        tailwater_river_depth_m: 5.60,
        omniverse_coupling_gamma: 1.420,
    },
    OmniverseFlowManifoldSpec {
        code: "beale_kato_majda_bkm",
        name: "Beale-Kato-Majda (BKM) L1-Time L_infty-Vorticity Continuation & Calderón-Zygmund Singular Integral Manifold",
        kinematic_viscosity_nu: 0.0009,
        characteristic_velocity_u0: 16.40,
        integral_length_l0: 2.20,
        initial_enstrophy_z0: 275.0,
        helicity_coherence_cos: 0.905,
        dyadic_shell_cutoff_j: 19,
        serrin_exponent_p: 8.0,
        serrin_exponent_q: 4.0,
        pubcf_alignment_radius_rho: 0.76,
        waterfall_drop_head_m: 64.0,
        tailwater_river_depth_m: 8.90,
        omniverse_coupling_gamma: 1.680,
    },
    OmniverseFlowManifoldSpec {
        code: "ladyzhenskaya_prodi_serrin",
        name: "Ladyzhenskaya-Prodi-Serrin L_t^p L_x^q (2/p + 3/q = 1) Scale-Invariant Critical Sobolev Manifold",
        kinematic_viscosity_nu: 0.0011,
        characteristic_velocity_u0: 14.20,
        integral_length_l0: 2.50,
        initial_enstrophy_z0: 230.0,
        helicity_coherence_cos: 0.890,
        dyadic_shell_cutoff_j: 17,
        serrin_exponent_p: 5.0,
        serrin_exponent_q: 5.0,
        pubcf_alignment_radius_rho: 0.72,
        waterfall_drop_head_m: 52.0,
        tailwater_river_depth_m: 7.80,
        omniverse_coupling_gamma: 1.560,
    },
    OmniverseFlowManifoldSpec {
        code: "constantin_fefferman_align",
        name: "Constantin-Fefferman Vorticity Direction Lipschitz Alignment & Geometric Nonlinearity Depletion Manifold",
        kinematic_viscosity_nu: 0.0007,
        characteristic_velocity_u0: 19.50,
        integral_length_l0: 2.80,
        initial_enstrophy_z0: 360.0,
        helicity_coherence_cos: 0.945,
        dyadic_shell_cutoff_j: 21,
        serrin_exponent_p: 6.0,
        serrin_exponent_q: 4.5,
        pubcf_alignment_radius_rho: 0.88,
        waterfall_drop_head_m: 76.0,
        tailwater_river_depth_m: 10.40,
        omniverse_coupling_gamma: 1.810,
    },
    OmniverseFlowManifoldSpec {
        code: "caffarelli_kohn_nirenberg",
        name: "Caffarelli-Kohn-Nirenberg (CKN) Parabolic Hausdorff Measure H^1(S)=0 & Scheffer-May Singularity Exclusion",
        kinematic_viscosity_nu: 0.0006,
        characteristic_velocity_u0: 21.00,
        integral_length_l0: 3.00,
        initial_enstrophy_z0: 410.0,
        helicity_coherence_cos: 0.930,
        dyadic_shell_cutoff_j: 21,
        serrin_exponent_p: 4.0,
        serrin_exponent_q: 6.0,
        pubcf_alignment_radius_rho: 0.84,
        waterfall_drop_head_m: 95.0,
        tailwater_river_depth_m: 12.60,
        omniverse_coupling_gamma: 1.910,
    },
];

// =============================================================================
// MILESTONE 9 - 15G FORMAL LEAN 4 CONSTANTS (0 sorryAx, 1-to-1 Synchronized)
// =============================================================================

/// R^3 Betchov-Loomis-Whitney invariant basin constant: R_crit = 46,656 * nu^4
pub const BLW_R_CRIT_NUMER_R3: i128 = 46_656;
/// R^3 sharp Riccati cubic constant denominator: c_BLW(nu) = 1 / (23,328 * nu^3)
pub const BLW_C_SHARP_DENOM_R3: i128 = 23_328;
/// R^3 sharp singularity horizon divisor: T_sep = T_trap / 186,624
pub const BLW_T_SEP_DIVISOR_R3: i128 = 186_624;
/// Exact fourth power of C_BLW_R3: (C_BLW_R3)^4 = 8 / 19,683
pub const BLW_CONST_POW4_NUMER_R3: i128 = 8;
pub const BLW_CONST_POW4_DENOM_R3: i128 = 19_683;

/// Exact Betchov biaxiality profile at theta = 1/2: betchovProfile(1/2) = 11 / 16
pub const BETCHOV_PROFILE_HALF_NUMER: i128 = 11;
pub const BETCHOV_PROFILE_HALF_DENOM: i128 = 16;
/// Lower bound on amplified basin at theta = 1/2: > 208,000 * nu^4
pub const BETCHOV_HALF_BASIN_FLOOR_R3: i128 = 208_000;

/// Riccati safe-step inequality 2 * (1 / (23328 * nu^3)) * z_k^2 * dt_k <= 1 / 2
/// <=> (BLW_SAFE_STEP_LHS_MULT) * z_k^2 * dt_k <= BLW_C_SHARP_DENOM_R3 * nu^3
pub const BLW_SAFE_STEP_FACTOR_NUM: i128 = 2;
pub const BLW_SAFE_STEP_RHS_DENOM: i128 = 2;
pub const BLW_SAFE_STEP_LHS_MULT: i128 = BLW_SAFE_STEP_FACTOR_NUM * BLW_SAFE_STEP_RHS_DENOM;

/// T^3 Milestone 9 exact constants: c_nu = 169 / (8 * pi^4 * nu^3), Z_crit = 4 * pi^3 * nu^2 / 13
pub const TORUS3D_C_NU_NUMER: i128 = 169;
pub const TORUS3D_C_NU_DENOM: i128 = 8;
pub const TORUS3D_Z_CRIT_NUMER: i128 = 4;
pub const TORUS3D_Z_CRIT_DENOM: i128 = 13;
pub const TORUS3D_H2_SMALL_DATA_COEFF: i128 = 217_088;
pub const TORUS3D_PALINSTROPHY_ENTRY_DENOM: i128 = 27_136;

/// Static stack capacities for BLW deterministic witness verification & certificate emitter
pub const BLW_MAX_WATERFALL_NODES: usize = 16;
pub const BLW_EMIT_BUFFER_BYTES: usize = 32_768;
pub const BLW_PLOT_WIDTH: usize = 73;
pub const BLW_PLOT_HEIGHT: usize = 21;

fn has_exact_manifold_token(lower_query: &str, token: &str) -> bool {
    lower_query
        .split(|c: char| !c.is_ascii_alphanumeric() && c != '_')
        .any(|t| t == token)
}

pub fn lookup_omniverse_manifold(query: &str) -> OmniverseFlowManifoldSpec {
    let low = query.to_lowercase();

    // Pass 1: Exact primary manifold code match takes absolute priority over 3D wireframe keywords
    let mut c_idx = 0usize;
    while c_idx < OMNIVERSE_MANIFOLD_CATALOG.len() {
        match has_exact_manifold_token(&low, OMNIVERSE_MANIFOLD_CATALOG[c_idx].code) {
            true => return OMNIVERSE_MANIFOLD_CATALOG[c_idx],
            false => c_idx += 1,
        }
    }

    // Pass 2: Secondary domain keyword fallback
    let is_ckn = has_exact_manifold_token(&low, "caffarelli")
        || has_exact_manifold_token(&low, "nirenberg")
        || has_exact_manifold_token(&low, "hausdorff")
        || has_exact_manifold_token(&low, "ckn");
    let is_cf = has_exact_manifold_token(&low, "constantin")
        || has_exact_manifold_token(&low, "fefferman")
        || has_exact_manifold_token(&low, "vorticity_direction");
    let is_serrin = has_exact_manifold_token(&low, "ladyzhenskaya")
        || has_exact_manifold_token(&low, "prodi")
        || has_exact_manifold_token(&low, "serrin");
    let is_bkm = has_exact_manifold_token(&low, "beale")
        || has_exact_manifold_token(&low, "kato")
        || has_exact_manifold_token(&low, "majda")
        || has_exact_manifold_token(&low, "bkm");
    let is_leray = has_exact_manifold_token(&low, "leray")
        || has_exact_manifold_token(&low, "hopf");
    let is_k41 = has_exact_manifold_token(&low, "kolmogorov")
        || has_exact_manifold_token(&low, "k41")
        || has_exact_manifold_token(&low, "littlewood_paley");
    let is_beltrami = has_exact_manifold_token(&low, "beltrami")
        || has_exact_manifold_token(&low, "helicity")
        || has_exact_manifold_token(&low, "lamb_vector");
    let is_tg = has_exact_manifold_token(&low, "taylor_green")
        || has_exact_manifold_token(&low, "torus");
    let is_river = has_exact_manifold_token(&low, "waterfall")
        || has_exact_manifold_token(&low, "plunge_pool")
        || has_exact_manifold_token(&low, "tailwater")
        || has_exact_manifold_token(&low, "hydraulic_jump");

    match (
        is_ckn, is_cf, is_serrin, is_bkm, is_leray, is_k41, is_beltrami, is_tg, is_river,
    ) {
        (true, _, _, _, _, _, _, _, _) => OMNIVERSE_MANIFOLD_CATALOG[9],
        (false, true, _, _, _, _, _, _, _) => OMNIVERSE_MANIFOLD_CATALOG[8],
        (false, false, true, _, _, _, _, _, _) => OMNIVERSE_MANIFOLD_CATALOG[7],
        (false, false, false, true, _, _, _, _, _) => OMNIVERSE_MANIFOLD_CATALOG[6],
        (false, false, false, false, true, _, _, _, _) => OMNIVERSE_MANIFOLD_CATALOG[5],
        (false, false, false, false, false, true, _, _, _) => OMNIVERSE_MANIFOLD_CATALOG[4],
        (false, false, false, false, false, false, true, _, _) => OMNIVERSE_MANIFOLD_CATALOG[3],
        (false, false, false, false, false, false, false, true, _) => OMNIVERSE_MANIFOLD_CATALOG[2],
        (false, false, false, false, false, false, false, false, true) => {
            OMNIVERSE_MANIFOLD_CATALOG[1]
        }
        _ => OMNIVERSE_MANIFOLD_CATALOG[0],
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_omniverse_manifold_token_lookup() {
        let omni = lookup_omniverse_manifold(
            "Evaluate navier_stokes_regularity on omniverse_10pillar_unifier with nu_visc = 0.001",
        );
        assert_eq!(omni.code, "omniverse_10pillar_unifier");

        let riv = lookup_omniverse_manifold(
            "Evaluate waterfall_vortex_dissipation on prandtl_navier_river with z0_enstrophy = 320.0",
        );
        assert_eq!(riv.code, "prandtl_navier_river");

        let bkm = lookup_omniverse_manifold(
            "Evaluate bkm_continuation on beale_kato_majda_bkm with u0_vel = 16.4",
        );
        assert_eq!(bkm.code, "beale_kato_majda_bkm");
    }
}