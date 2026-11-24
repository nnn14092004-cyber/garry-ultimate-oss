//! Fixed-stack 3D wireframe geometry builder and depth-shaded ASCII rasterizer for
//! Taylor-Green vortex meshes, Arnold-Beltrami-Childress helical filaments,
//! Kolmogorov cascade polytopes, plunge-pool-to-tailwater flow domains,
//! and Milestone 15G BLW waterfall / biaxial strain spectrum projections.

pub const MAX_CANVAS_WIDTH: usize = 80;
pub const MAX_CANVAS_HEIGHT: usize = 24;
pub const MAX_WIREFRAME_EDGES: usize = 64;
pub const MAX_BRESENHAM_STEPS: usize = 512;

#[derive(Debug, Clone, Copy, PartialEq)]
pub struct Point3D {
    pub x: f64,
    pub y: f64,
    pub z: f64,
}

impl Point3D {
    pub const fn new(x: f64, y: f64, z: f64) -> Self {
        Self { x, y, z }
    }
}

#[derive(Debug, Clone, Copy, PartialEq)]
pub struct Point2D {
    pub x: f64,
    pub y: f64,
}

impl Point2D {
    pub const fn new(x: f64, y: f64) -> Self {
        Self { x, y }
    }
}

#[derive(Debug, Clone, Copy, PartialEq)]
pub struct Line3D {
    pub start: Point3D,
    pub end: Point3D,
}

impl Line3D {
    pub const fn new(start: Point3D, end: Point3D) -> Self {
        Self { start, end }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SpatialTopologyKind {
    UnitCube,
    Tetrahedron,
    SquarePyramid,
    Octahedron,
    VectorAndLine3D,
    AsymmetricPolytope,
    SpiderwebGeodesicMesh,
    BlwWaterfallBasin3D,
    BiaxialStrainSpectrum3D,
}

impl Default for SpatialTopologyKind {
    fn default() -> Self {
        Self::UnitCube
    }
}

impl SpatialTopologyKind {
    pub const fn omniverse_model_label(&self) -> &'static str {
        match self {
            Self::UnitCube => {
                "3D Periodic Torus T^3 Fourier-Galerkin Lattice & Littlewood-Paley Dyadic Shell Box (12-Edge Unit)"
            }
            Self::Tetrahedron => {
                "3D Constantin-Fefferman Vorticity Direction Alignment Simplex & Helicity Tetrahedron"
            }
            Self::SquarePyramid => {
                "3D Kolmogorov K41 Inertial Energy Cascade Pyramid & Enstrophy Dissipation Funnel"
            }
            Self::Octahedron => {
                "3D Garry 10-Pillar Omniverse Dual-Cone & Caffarelli-Kohn-Nirenberg Parabolic Octahedron"
            }
            Self::VectorAndLine3D => {
                "3D Arnold-Beltrami-Childress (ABC) Helical Vortex Filament & Biot-Savart Streamline Triad"
            }
            Self::AsymmetricPolytope => {
                "3D Waterfall Plunge-Pool Vortex Trapping to Laminar Tailwater River Manifold (L1->L2)"
            }
            Self::SpiderwebGeodesicMesh => {
                "3D Taylor-Green Solenoidal Vortex Tube Mesh & Beale-Kato-Majda Iso-Vorticity Cage"
            }
            Self::BlwWaterfallBasin3D => {
                "3D M15G Three-Phase BLW Waterfall Cascade -> Singularity Cage (T_trap/186,624) -> 46,656 nu^4 Basin -> O(1/t) River"
            }
            Self::BiaxialStrainSpectrum3D => {
                "3D M14-M15G Trace-Free Strain Spectrum (lambda_1+lambda_2+lambda_3=0): Biaxial Sheet Cone (lambda_2>0) vs Tube Closure (lambda_2<=0)"
            }
        }
    }
}

fn has_exact_spatial_token(lower_text: &str, target: &str) -> bool {
    lower_text
        .split(|c: char| !c.is_ascii_alphanumeric() && c != '_')
        .any(|tok| tok == target)
}

impl SpatialTopologyKind {
    pub fn from_query(text: &str) -> Self {
        let lower = text.to_lowercase();
        let is_blw_3phase = has_exact_spatial_token(&lower, "blw_waterfall")
            || has_exact_spatial_token(&lower, "m15g_waterfall")
            || has_exact_spatial_token(&lower, "basin_46656");
        let is_biaxial = has_exact_spatial_token(&lower, "biaxial_sheet")
            || has_exact_spatial_token(&lower, "strain_spectrum")
            || has_exact_spatial_token(&lower, "lambda2_cone");

        match (is_blw_3phase, is_biaxial) {
            (true, _) => return Self::BlwWaterfallBasin3D,
            (false, true) => return Self::BiaxialStrainSpectrum3D,
            (false, false) => {}
        }

        let is_web = has_exact_spatial_token(&lower, "spiderweb")
            || has_exact_spatial_token(&lower, "taylor_green_mesh")
            || has_exact_spatial_token(&lower, "vortex_mesh")
            || has_exact_spatial_token(&lower, "bkm_cage")
            || has_exact_spatial_token(&lower, "iso_vorticity")
            || has_exact_spatial_token(&lower, "mesh");
        let is_vec = has_exact_spatial_token(&lower, "vector_line")
            || has_exact_spatial_token(&lower, "line3d")
            || has_exact_spatial_token(&lower, "vortex_filament")
            || has_exact_spatial_token(&lower, "beltrami_helix")
            || has_exact_spatial_token(&lower, "biot_savart")
            || has_exact_spatial_token(&lower, "helicity_triad");
        let is_asym = has_exact_spatial_token(&lower, "asymmetric")
            || has_exact_spatial_token(&lower, "waterfall_river")
            || has_exact_spatial_token(&lower, "plunge_pool")
            || has_exact_spatial_token(&lower, "hydraulic_jump")
            || has_exact_spatial_token(&lower, "tailwater_basin")
            || has_exact_spatial_token(&lower, "oblique");
        let is_tetra = has_exact_spatial_token(&lower, "tetrahedron")
            || has_exact_spatial_token(&lower, "vorticity_simplex")
            || has_exact_spatial_token(&lower, "cf_simplex")
            || has_exact_spatial_token(&lower, "simplex");
        let is_pyra = has_exact_spatial_token(&lower, "pyramid")
            || has_exact_spatial_token(&lower, "kolmogorov_pyramid")
            || has_exact_spatial_token(&lower, "cascade_pyramid")
            || has_exact_spatial_token(&lower, "enstrophy_funnel");
        let is_octa = has_exact_spatial_token(&lower, "octahedron")
            || has_exact_spatial_token(&lower, "omniverse_octahedron")
            || has_exact_spatial_token(&lower, "ckn_octahedron")
            || has_exact_spatial_token(&lower, "sobolev_octahedron");
        let is_cube = has_exact_spatial_token(&lower, "cube")
            || has_exact_spatial_token(&lower, "torus_lattice")
            || has_exact_spatial_token(&lower, "dyadic_box")
            || has_exact_spatial_token(&lower, "fourier_box");

        match (is_web, is_vec, is_asym, is_tetra, is_pyra, is_octa, is_cube) {
            (true, _, _, _, _, _, _) => Self::SpiderwebGeodesicMesh,
            (false, true, _, _, _, _, _) => Self::VectorAndLine3D,
            (false, false, true, _, _, _, _) => Self::AsymmetricPolytope,
            (false, false, false, true, _, _, _) => Self::Tetrahedron,
            (false, false, false, false, true, _, _) => Self::SquarePyramid,
            (false, false, false, false, false, true, _) => Self::Octahedron,
            (false, false, false, false, false, false, true) => Self::UnitCube,
            _ => Self::UnitCube,
        }
    }
}

pub struct SpatialWireframeBuilder;

impl SpatialWireframeBuilder {
    pub const DUMMY_LINE: Line3D =
        Line3D::new(Point3D::new(0.0, 0.0, 0.0), Point3D::new(0.0, 0.0, 0.0));

    pub fn build_topology(kind: SpatialTopologyKind) -> ([Line3D; MAX_WIREFRAME_EDGES], usize) {
        match kind {
            SpatialTopologyKind::UnitCube => Self::build_unit_cube(),
            SpatialTopologyKind::Tetrahedron => Self::build_tetrahedron(),
            SpatialTopologyKind::SquarePyramid => Self::build_square_pyramid(),
            SpatialTopologyKind::Octahedron => Self::build_octahedron(),
            SpatialTopologyKind::VectorAndLine3D => Self::build_vector_and_line_3d(),
            SpatialTopologyKind::AsymmetricPolytope => Self::build_asymmetric_polytope(),
            SpatialTopologyKind::SpiderwebGeodesicMesh => Self::build_spiderweb_mesh(),
            SpatialTopologyKind::BlwWaterfallBasin3D => Self::build_blw_waterfall_basin_3d(),
            SpatialTopologyKind::BiaxialStrainSpectrum3D => Self::build_biaxial_strain_spectrum_3d(),
        }
    }

    pub fn build_unit_cube() -> ([Line3D; MAX_WIREFRAME_EDGES], usize) {
        let mut edges = [Self::DUMMY_LINE; MAX_WIREFRAME_EDGES];
        let cube = [
            Line3D::new(Point3D::new(-1.0, -1.0, -1.0), Point3D::new(1.0, -1.0, -1.0)),
            Line3D::new(Point3D::new(1.0, -1.0, -1.0), Point3D::new(1.0, 1.0, -1.0)),
            Line3D::new(Point3D::new(1.0, 1.0, -1.0), Point3D::new(-1.0, 1.0, -1.0)),
            Line3D::new(Point3D::new(-1.0, 1.0, -1.0), Point3D::new(-1.0, -1.0, -1.0)),
            Line3D::new(Point3D::new(-1.0, -1.0, 1.0), Point3D::new(1.0, -1.0, 1.0)),
            Line3D::new(Point3D::new(1.0, -1.0, 1.0), Point3D::new(1.0, 1.0, 1.0)),
            Line3D::new(Point3D::new(1.0, 1.0, 1.0), Point3D::new(-1.0, 1.0, 1.0)),
            Line3D::new(Point3D::new(-1.0, 1.0, 1.0), Point3D::new(-1.0, -1.0, 1.0)),
            Line3D::new(Point3D::new(-1.0, -1.0, -1.0), Point3D::new(-1.0, -1.0, 1.0)),
            Line3D::new(Point3D::new(1.0, -1.0, -1.0), Point3D::new(1.0, -1.0, 1.0)),
            Line3D::new(Point3D::new(1.0, 1.0, -1.0), Point3D::new(1.0, 1.0, 1.0)),
            Line3D::new(Point3D::new(-1.0, 1.0, -1.0), Point3D::new(-1.0, 1.0, 1.0)),
        ];
        let mut i = 0usize;
        while i < 12 {
            edges[i] = cube[i];
            i += 1;
        }
        (edges, 12)
    }

    pub fn build_tetrahedron() -> ([Line3D; MAX_WIREFRAME_EDGES], usize) {
        let mut edges = [Self::DUMMY_LINE; MAX_WIREFRAME_EDGES];
        let v0 = Point3D::new(0.0, 1.35, 0.0);
        let v1 = Point3D::new(-1.25, -0.9, 1.05);
        let v2 = Point3D::new(1.25, -0.9, 1.05);
        let v3 = Point3D::new(0.0, -0.9, -1.35);

        edges[0] = Line3D::new(v0, v1);
        edges[1] = Line3D::new(v0, v2);
        edges[2] = Line3D::new(v0, v3);
        edges[3] = Line3D::new(v1, v2);
        edges[4] = Line3D::new(v2, v3);
        edges[5] = Line3D::new(v3, v1);
        (edges, 6)
    }

    pub fn build_square_pyramid() -> ([Line3D; MAX_WIREFRAME_EDGES], usize) {
        let mut edges = [Self::DUMMY_LINE; MAX_WIREFRAME_EDGES];
        let apex = Point3D::new(0.0, 1.55, 0.0);
        let b0 = Point3D::new(-1.2, -1.0, -1.2);
        let b1 = Point3D::new(1.2, -1.0, -1.2);
        let b2 = Point3D::new(1.2, -1.0, 1.2);
        let b3 = Point3D::new(-1.2, -1.0, 1.2);

        edges[0] = Line3D::new(b0, b1);
        edges[1] = Line3D::new(b1, b2);
        edges[2] = Line3D::new(b2, b3);
        edges[3] = Line3D::new(b3, b0);
        edges[4] = Line3D::new(apex, b0);
        edges[5] = Line3D::new(apex, b1);
        edges[6] = Line3D::new(apex, b2);
        edges[7] = Line3D::new(apex, b3);
        (edges, 8)
    }

    pub fn build_octahedron() -> ([Line3D; MAX_WIREFRAME_EDGES], usize) {
        let mut edges = [Self::DUMMY_LINE; MAX_WIREFRAME_EDGES];
        let top = Point3D::new(0.0, 1.55, 0.0);
        let bot = Point3D::new(0.0, -1.55, 0.0);
        let m0 = Point3D::new(-1.35, 0.0, 0.0);
        let m1 = Point3D::new(0.0, 0.0, 1.35);
        let m2 = Point3D::new(1.35, 0.0, 0.0);
        let m3 = Point3D::new(0.0, 0.0, -1.35);

        edges[0] = Line3D::new(m0, m1);
        edges[1] = Line3D::new(m1, m2);
        edges[2] = Line3D::new(m2, m3);
        edges[3] = Line3D::new(m3, m0);
        edges[4] = Line3D::new(top, m0);
        edges[5] = Line3D::new(top, m1);
        edges[6] = Line3D::new(top, m2);
        edges[7] = Line3D::new(top, m3);
        edges[8] = Line3D::new(bot, m0);
        edges[9] = Line3D::new(bot, m1);
        edges[10] = Line3D::new(bot, m2);
        edges[11] = Line3D::new(bot, m3);
        (edges, 12)
    }

    /// 3D Arnold-Beltrami-Childress (ABC) Helical Vortex Filament & Biot-Savart Streamline Triad (15 edges).
    pub fn build_vector_and_line_3d() -> ([Line3D; MAX_WIREFRAME_EDGES], usize) {
        let mut edges = [Self::DUMMY_LINE; MAX_WIREFRAME_EDGES];
        let core = Point3D::new(0.0, 0.0, 0.0);

        edges[0] = Line3D::new(Point3D::new(-1.65, 0.0, 0.0), core);
        edges[1] = Line3D::new(core, Point3D::new(1.65, 0.0, 0.0));

        let f1 = Point3D::new(1.20, 1.35, 0.85);
        let f2 = Point3D::new(0.85, 1.45, -1.05);
        let f3 = Point3D::new(1.40, 0.90, -0.35);
        let f4 = Point3D::new(-1.20, -1.35, -0.85);
        let f5 = Point3D::new(-0.85, -1.45, 1.05);
        let f6 = Point3D::new(-1.40, -0.90, 0.35);
        edges[2] = Line3D::new(core, f1);
        edges[3] = Line3D::new(core, f2);
        edges[4] = Line3D::new(core, f3);
        edges[5] = Line3D::new(core, f4);
        edges[6] = Line3D::new(core, f5);
        edges[7] = Line3D::new(core, f6);

        edges[8] = Line3D::new(f1, f2);
        edges[9] = Line3D::new(f2, f3);
        edges[10] = Line3D::new(f3, f1);
        edges[11] = Line3D::new(f4, f5);
        edges[12] = Line3D::new(f5, f6);
        edges[13] = Line3D::new(f6, f4);
        edges[14] = Line3D::new(Point3D::new(0.0, -1.55, 0.0), Point3D::new(0.0, 1.55, 0.0));

        (edges, 15)
    }

    /// 3D Waterfall Plunge-Pool Vortex Trapping to Laminar Tailwater River Manifold (14 edges).
    pub fn build_asymmetric_polytope() -> ([Line3D; MAX_WIREFRAME_EDGES], usize) {
        let mut edges = [Self::DUMMY_LINE; MAX_WIREFRAME_EDGES];
        let plunge_pool_throat = Point3D::new(0.0, 0.0, 0.0);

        let w_crest = Point3D::new(-1.60, 0.0, 0.0);
        let w_top = Point3D::new(-0.95, 1.15, 0.45);
        let w_bot = Point3D::new(-0.95, -1.15, -0.45);
        let w_front = Point3D::new(-0.95, -0.35, 1.15);

        let r_outflow = Point3D::new(1.55, 0.0, 0.0);
        let r_top = Point3D::new(0.85, 0.85, -0.35);
        let r_bot = Point3D::new(0.85, -0.85, 0.35);

        edges[0] = Line3D::new(w_crest, w_top);
        edges[1] = Line3D::new(w_crest, w_bot);
        edges[2] = Line3D::new(w_crest, w_front);
        edges[3] = Line3D::new(w_top, w_front);
        edges[4] = Line3D::new(w_front, w_bot);
        edges[5] = Line3D::new(w_top, plunge_pool_throat);
        edges[6] = Line3D::new(w_bot, plunge_pool_throat);
        edges[7] = Line3D::new(w_front, plunge_pool_throat);

        edges[8] = Line3D::new(plunge_pool_throat, r_top);
        edges[9] = Line3D::new(plunge_pool_throat, r_bot);
        edges[10] = Line3D::new(r_top, r_outflow);
        edges[11] = Line3D::new(r_bot, r_outflow);
        edges[12] = Line3D::new(r_top, r_bot);
        edges[13] = Line3D::new(w_crest, r_outflow);

        (edges, 14)
    }

    pub fn build_spiderweb_mesh() -> ([Line3D; MAX_WIREFRAME_EDGES], usize) {
        let mut edges = [Self::DUMMY_LINE; MAX_WIREFRAME_EDGES];
        let mut count = 0usize;
        let dirs: [(f64, f64); 8] = [
            (1.0, 0.0),
            (0.70710678, 0.70710678),
            (0.0, 1.0),
            (-0.70710678, 0.70710678),
            (-1.0, 0.0),
            (-0.70710678, -0.70710678),
            (0.0, -1.0),
            (0.70710678, -0.70710678),
        ];
        let vortex_eye = Point3D::new(0.0, 0.45, 0.0);
        let mut s = 0usize;
        while s < 8 {
            let (dx, dz) = dirs[s];
            edges[count] = Line3D::new(vortex_eye, Point3D::new(dx * 1.5, -0.45, dz * 1.5));
            count += 1;
            s += 1;
        }
        let radii: [(f64, f64); 3] = [(0.55, 0.18), (1.05, -0.12), (1.5, -0.45)];
        let mut r_idx = 0usize;
        while r_idx < 3 {
            let (rad, y_lvl) = radii[r_idx];
            let mut k = 0usize;
            while k < 8 {
                let next_k = (k + 1) % 8;
                edges[count] = Line3D::new(
                    Point3D::new(dirs[k].0 * rad, y_lvl, dirs[k].1 * rad),
                    Point3D::new(dirs[next_k].0 * rad, y_lvl, dirs[next_k].1 * rad),
                );
                count += 1;
                k += 1;
            }
            r_idx += 1;
        }
        (edges, count)
    }

    /// M15G 3-Phase Closure Geometry (22 edges):
    /// Left: Supercritical Waterfall Crest + Riccati Safe-Step Gates [0, t_N]
    /// Center: Singularity Cage T_sep = T_trap/186,624 & 46,656 nu^4 Basin Throat
    /// Right: Global Dissipative River Outflow Channel [t_N, infinity)
    pub fn build_blw_waterfall_basin_3d() -> ([Line3D; MAX_WIREFRAME_EDGES], usize) {
        let mut edges = [Self::DUMMY_LINE; MAX_WIREFRAME_EDGES];

        let c0 = Point3D::new(-1.65, 1.35, -0.55);
        let c1 = Point3D::new(-1.65, 1.35, 0.55);
        let c2 = Point3D::new(-1.65, 0.55, 0.55);
        let c3 = Point3D::new(-1.65, 0.55, -0.55);

        let g0 = Point3D::new(-0.85, 0.75, -0.45);
        let g1 = Point3D::new(-0.85, 0.75, 0.45);
        let g2 = Point3D::new(-0.85, -0.05, 0.45);
        let g3 = Point3D::new(-0.85, -0.05, -0.45);

        let b0 = Point3D::new(0.0, 0.22, -0.22);
        let b1 = Point3D::new(0.0, 0.22, 0.22);
        let b2 = Point3D::new(0.0, -0.22, 0.22);
        let b3 = Point3D::new(0.0, -0.22, -0.22);

        let r0 = Point3D::new(1.65, -0.15, -0.45);
        let r1 = Point3D::new(1.65, -0.15, 0.45);
        let r2 = Point3D::new(1.65, -0.65, 0.45);
        let r3 = Point3D::new(1.65, -0.65, -0.45);

        edges[0] = Line3D::new(c0, c1);
        edges[1] = Line3D::new(c1, c2);
        edges[2] = Line3D::new(c2, c3);
        edges[3] = Line3D::new(c3, c0);
        edges[4] = Line3D::new(c0, g0);
        edges[5] = Line3D::new(c1, g1);
        edges[6] = Line3D::new(c2, g2);
        edges[7] = Line3D::new(c3, g3);
        edges[8] = Line3D::new(g0, b0);
        edges[9] = Line3D::new(g1, b1);
        edges[10] = Line3D::new(g2, b2);
        edges[11] = Line3D::new(g3, b3);
        edges[12] = Line3D::new(b0, b1);
        edges[13] = Line3D::new(b1, b2);
        edges[14] = Line3D::new(b2, b3);
        edges[15] = Line3D::new(b3, b0);
        edges[16] = Line3D::new(b0, r0);
        edges[17] = Line3D::new(b1, r1);
        edges[18] = Line3D::new(b2, r2);
        edges[19] = Line3D::new(b3, r3);
        edges[20] = Line3D::new(r0, r1);
        edges[21] = Line3D::new(r2, r3);

        (edges, 22)
    }

    /// M14A/M15C/M15G Trace-Free Strain Spectrum Geometry (20 edges):
    /// Separates the Biaxial Sheet Blow-Up Cone (lambda_2 > 0, upper half)
    /// from the Unconditional Tube Closure Half-Space (lambda_2 <= 0, lower half).
    pub fn build_biaxial_strain_spectrum_3d() -> ([Line3D; MAX_WIREFRAME_EDGES], usize) {
        let mut edges = [Self::DUMMY_LINE; MAX_WIREFRAME_EDGES];
        let origin = Point3D::new(0.0, 0.0, 0.0);

        let p0 = Point3D::new(1.30, 0.0, 0.0);
        let p1 = Point3D::new(0.65, 0.0, 1.1258);
        let p2 = Point3D::new(-0.65, 0.0, 1.1258);
        let p3 = Point3D::new(-1.30, 0.0, 0.0);
        let p4 = Point3D::new(-0.65, 0.0, -1.1258);
        let p5 = Point3D::new(0.65, 0.0, -1.1258);

        let apex_biaxial = Point3D::new(0.0, 1.45, 0.0);
        let apex_tube = Point3D::new(0.0, -1.45, 0.0);

        edges[0] = Line3D::new(p0, p1);
        edges[1] = Line3D::new(p1, p2);
        edges[2] = Line3D::new(p2, p3);
        edges[3] = Line3D::new(p3, p4);
        edges[4] = Line3D::new(p4, p5);
        edges[5] = Line3D::new(p5, p0);

        edges[6] = Line3D::new(apex_biaxial, p0);
        edges[7] = Line3D::new(apex_biaxial, p1);
        edges[8] = Line3D::new(apex_biaxial, p2);
        edges[9] = Line3D::new(apex_biaxial, p3);
        edges[10] = Line3D::new(apex_biaxial, p4);
        edges[11] = Line3D::new(apex_biaxial, p5);

        edges[12] = Line3D::new(apex_tube, p0);
        edges[13] = Line3D::new(apex_tube, p1);
        edges[14] = Line3D::new(apex_tube, p2);
        edges[15] = Line3D::new(apex_tube, p3);
        edges[16] = Line3D::new(apex_tube, p4);
        edges[17] = Line3D::new(apex_tube, p5);

        edges[18] = Line3D::new(origin, apex_biaxial);
        edges[19] = Line3D::new(origin, apex_tube);

        (edges, 20)
    }
}

pub fn project_3d_to_2d_with_depth(
    p: Point3D,
    yaw_deg: f64,
    pitch_deg: f64,
    distance: f64,
) -> (Point2D, f64) {
    let yaw_rad = yaw_deg.to_radians();
    let pitch_rad = pitch_deg.to_radians();

    let cos_y = yaw_rad.cos();
    let sin_y = yaw_rad.sin();
    let cos_p = pitch_rad.cos();
    let sin_p = pitch_rad.sin();

    let x1 = p.x * cos_y + p.z * sin_y;
    let y1 = p.y;
    let z1 = -p.x * sin_y + p.z * cos_y;

    let x2 = x1;
    let y2 = y1 * cos_p - z1 * sin_p;
    let z2 = y1 * sin_p + z1 * cos_p;

    let dist = match distance <= 0.0 {
        true => 1.0,
        false => distance,
    };
    let denom = z2 + dist;
    let factor = match denom.abs() < 1e-4 {
        true => dist / 1e-4,
        false => dist / denom,
    };

    (
        Point2D {
            x: x2 * factor,
            y: y2 * factor,
        },
        z2,
    )
}

pub fn project_3d_to_2d(p: Point3D, yaw_deg: f64, pitch_deg: f64, distance: f64) -> Point2D {
    project_3d_to_2d_with_depth(p, yaw_deg, pitch_deg, distance).0
}

pub struct AsciiCanvas {
    pub width: usize,
    pub height: usize,
    buffer: [[char; MAX_CANVAS_WIDTH]; MAX_CANVAS_HEIGHT],
}

impl AsciiCanvas {
    pub fn new(width: usize, height: usize) -> Self {
        let w = width.clamp(1, MAX_CANVAS_WIDTH);
        let h = height.clamp(1, MAX_CANVAS_HEIGHT);
        Self {
            width: w,
            height: h,
            buffer: [[' '; MAX_CANVAS_WIDTH]; MAX_CANVAS_HEIGHT],
        }
    }

    pub fn set_pixel(&mut self, x: i32, y: i32, ch: char) {
        let in_bounds = x >= 0 && x < (self.width as i32) && y >= 0 && y < (self.height as i32);
        match in_bounds {
            true => {
                let existing = self.buffer[y as usize][x as usize];
                let should_write = match existing {
                    'O' => false,
                    '#' => ch == 'O' || ch == '#',
                    '+' => ch == 'O' || ch == '#' || ch == '+',
                    _ => true,
                };
                match should_write {
                    true => self.buffer[y as usize][x as usize] = ch,
                    false => {}
                }
            }
            false => {}
        }
    }

    pub fn draw_line(&mut self, mut x0: i32, mut y0: i32, x1: i32, y1: i32, ch: char) {
        let dx = (x1 - x0).abs();
        let sx = match x0 < x1 {
            true => 1,
            false => -1,
        };
        let dy = -(y1 - y0).abs();
        let sy = match y0 < y1 {
            true => 1,
            false => -1,
        };
        let mut err = dx + dy;
        let mut step_budget = MAX_BRESENHAM_STEPS;

        while step_budget > 0 {
            step_budget -= 1;
            self.set_pixel(x0, y0, ch);
            match x0 == x1 && y0 == y1 {
                true => break,
                false => {}
            }
            let e2 = 2 * err;
            match e2 >= dy {
                true => {
                    err += dy;
                    x0 += sx;
                }
                false => {}
            }
            match e2 <= dx {
                true => {
                    err += dx;
                    y0 += sy;
                }
                false => {}
            }
        }
    }

    /// Zero-heap stack rasterizer writing directly into any `core::fmt::Write` target.
    pub fn render_topology_3d_to_writer<W: core::fmt::Write>(
        &mut self,
        kind: SpatialTopologyKind,
        yaw: f64,
        pitch: f64,
        out: &mut W,
    ) {
        let mut cr = 0usize;
        while cr < self.height {
            let mut cc = 0usize;
            while cc < self.width {
                self.buffer[cr][cc] = ' ';
                cc += 1;
            }
            cr += 1;
        }

        let (edges, count) = SpatialWireframeBuilder::build_topology(kind);
        let mut projected = [(
            Point2D::new(0.0, 0.0),
            Point2D::new(0.0, 0.0),
            0.0f64,
        ); MAX_WIREFRAME_EDGES];
        let mut min_x = f64::MAX;
        let mut max_x = f64::MIN;
        let mut min_y = f64::MAX;
        let mut max_y = f64::MIN;

        let mut i = 0usize;
        while i < count {
            let (p1, z1) = project_3d_to_2d_with_depth(edges[i].start, yaw, pitch, 6.8);
            let (p2, z2) = project_3d_to_2d_with_depth(edges[i].end, yaw, pitch, 6.8);
            min_x = min_x.min(p1.x).min(p2.x);
            max_x = max_x.max(p1.x).max(p2.x);
            min_y = min_y.min(p1.y).min(p2.y);
            max_y = max_y.max(p1.y).max(p2.y);
            projected[i] = (p1, p2, 0.5 * (z1 + z2));
            i += 1;
        }

        let span_x = (max_x - min_x).max(1e-4);
        let span_y = (max_y - min_y).max(1e-4);
        let target_w = (self.width.saturating_sub(4)).max(1) as f64;
        let target_h = (self.height.saturating_sub(4)).max(1) as f64;

        let mut k = 0usize;
        while k < count {
            let (p1, p2, z_mean) = projected[k];
            let x0 = 2 + (((p1.x - min_x) / span_x) * target_w).round() as i32;
            let y0 = 2 + (((max_y - p1.y) / span_y) * target_h).round() as i32;
            let x1 = 2 + (((p2.x - min_x) / span_x) * target_w).round() as i32;
            let y1 = 2 + (((max_y - p2.y) / span_y) * target_h).round() as i32;

            let stroke_ch = match z_mean < -0.15 {
                true => '#',
                false => match z_mean <= 0.25 {
                    true => '+',
                    false => '.',
                },
            };
            self.draw_line(x0, y0, x1, y1, stroke_ch);
            self.set_pixel(x0, y0, 'O');
            self.set_pixel(x1, y1, 'O');
            k += 1;
        }

        let mut r = 0usize;
        while r < self.height {
            let mut c = 0usize;
            while c < self.width {
                let _ = out.write_char(self.buffer[r][c]);
                c += 1;
            }
            let _ = out.write_char('\n');
            r += 1;
        }
    }

    pub fn render_topology_3d(&mut self, kind: SpatialTopologyKind, yaw: f64, pitch: f64) -> String {
        let mut out = String::with_capacity((self.width + 1) * self.height);
        self.render_topology_3d_to_writer(kind, yaw, pitch, &mut out);
        out
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_all_nine_3d_omniverse_and_m15g_wireframe_topologies_are_distinct() {
        let (_, c_cube) = SpatialWireframeBuilder::build_topology(SpatialTopologyKind::UnitCube);
        let (_, c_tetra) =
            SpatialWireframeBuilder::build_topology(SpatialTopologyKind::Tetrahedron);
        let (_, c_pyra) =
            SpatialWireframeBuilder::build_topology(SpatialTopologyKind::SquarePyramid);
        let (_, c_octa) = SpatialWireframeBuilder::build_topology(SpatialTopologyKind::Octahedron);
        let (_, c_vec) =
            SpatialWireframeBuilder::build_topology(SpatialTopologyKind::VectorAndLine3D);
        let (_, c_asym) =
            SpatialWireframeBuilder::build_topology(SpatialTopologyKind::AsymmetricPolytope);
        let (_, c_web) =
            SpatialWireframeBuilder::build_topology(SpatialTopologyKind::SpiderwebGeodesicMesh);
        let (_, c_blw) =
            SpatialWireframeBuilder::build_topology(SpatialTopologyKind::BlwWaterfallBasin3D);
        let (_, c_biax) =
            SpatialWireframeBuilder::build_topology(SpatialTopologyKind::BiaxialStrainSpectrum3D);

        assert_eq!(
            (c_cube, c_tetra, c_pyra, c_octa, c_vec, c_asym, c_web, c_blw, c_biax),
            (12, 6, 8, 12, 15, 14, 32, 22, 20)
        );
        assert_eq!(
            SpatialTopologyKind::from_query("waterfall_river wireframe"),
            SpatialTopologyKind::AsymmetricPolytope
        );
        assert_eq!(
            SpatialTopologyKind::from_query("taylor_green_mesh wireframe"),
            SpatialTopologyKind::SpiderwebGeodesicMesh
        );
        assert_eq!(
            SpatialTopologyKind::from_query("blw_waterfall wireframe"),
            SpatialTopologyKind::BlwWaterfallBasin3D
        );
        assert_eq!(
            SpatialTopologyKind::from_query("biaxial_sheet wireframe"),
            SpatialTopologyKind::BiaxialStrainSpectrum3D
        );
    }
}