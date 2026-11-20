import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Tactic.Ring
import GarryNavierStokesMathlib

/-!
# GARRYULT v4.0.0 — Milestone 1: Real 3D Vector Calculus & Classical 3D Navier-Stokes PDE
Formalizes true spatial Fréchet differential operators (`grad3D`, `div3D`, `curl3D`,
`laplacian3D`, `advection3D`) on `ℝ³ = Fin 3 → ℝ`, proves unconditional `C²` vector
calculus identities (`∇ × (∇p) = 0`, `∇ · (∇ × u) = 0`), verifies the exact 3D solenoidal
plane wave `u₀(x) = a * sin(k · x)`, and defines the classical 3D incompressible
Navier-Stokes PDE (`IsClassicalNS3D`) with a non-vacuity witness (`0 sorryAx`).
-/

namespace GarryReal3DCalculus

abbrev R3 := Fin 3 → ℝ

def vec3 (vx vy vz : ℝ) : R3 := fun i =>
  match i with
  | ⟨0, _⟩ => vx
  | ⟨1, _⟩ => vy
  | ⟨2, _⟩ => vz

noncomputable def basisVec (i : Fin 3) : R3 := Pi.single i 1

noncomputable def dot3D (k x : R3) : ℝ :=
  k 0 * x 0 + k 1 * x 1 + k 2 * x 2

noncomputable def cross3D (k a : R3) : R3 :=
  vec3 (k 1 * a 2 - k 2 * a 1) (k 2 * a 0 - k 0 * a 2) (k 0 * a 1 - k 1 * a 0)

-- ============================================================================
-- SECTION 1: TRUE 3D FRÉCHET DIFFERENTIAL OPERATORS ON ℝ³
-- ============================================================================

noncomputable def partialDerivScalar (f : R3 → ℝ) (x : R3) (i : Fin 3) : ℝ :=
  fderiv ℝ f x (basisVec i)

noncomputable def sndPartial (p : R3 → ℝ) (x : R3) (i j : Fin 3) : ℝ :=
  fderiv ℝ (fderiv ℝ p) x (basisVec i) (basisVec j)

noncomputable def grad3D (p : R3 → ℝ) (x : R3) : R3 :=
  fun i => partialDerivScalar p x i

noncomputable def div3D (u : R3 → R3) (x : R3) : ℝ :=
  partialDerivScalar (fun y => u y 0) x 0 +
  partialDerivScalar (fun y => u y 1) x 1 +
  partialDerivScalar (fun y => u y 2) x 2

noncomputable def curl3D (u : R3 → R3) (x : R3) : R3 :=
  vec3
    (partialDerivScalar (fun y => u y 2) x 1 - partialDerivScalar (fun y => u y 1) x 2)
    (partialDerivScalar (fun y => u y 0) x 2 - partialDerivScalar (fun y => u y 2) x 0)
    (partialDerivScalar (fun y => u y 1) x 0 - partialDerivScalar (fun y => u y 0) x 1)

noncomputable def laplacianScalar (f : R3 → ℝ) (x : R3) : ℝ :=
  sndPartial f x 0 0 + sndPartial f x 1 1 + sndPartial f x 2 2

noncomputable def laplacian3D (u : R3 → R3) (x : R3) : R3 :=
  fun comp => laplacianScalar (fun y => u y comp) x

noncomputable def advection3D (u : R3 → R3) (x : R3) : R3 :=
  fun comp =>
    u x 0 * partialDerivScalar (fun y => u y comp) x 0 +
    u x 1 * partialDerivScalar (fun y => u y comp) x 1 +
    u x 2 * partialDerivScalar (fun y => u y comp) x 2

-- ============================================================================
-- SECTION 2: UNCONDITIONAL C² VECTOR CALCULUS IDENTITIES (0 sorryAx)
-- ============================================================================

theorem sndPartial_symm_of_contDiffAt
    (p : R3 → ℝ) (x : R3) (hp : ContDiffAt ℝ 2 p x) (i j : Fin 3) :
    sndPartial p x i j = sndPartial p x j i := by
  have hsymm := hp.isSymmSndFDerivAt (by simp)
  exact hsymm.eq (basisVec i) (basisVec j)

theorem hasFDerivAt_partialDerivScalar
    (f : R3 → ℝ) (x : R3) (hf : ContDiffAt ℝ 2 f x) (j : Fin 3) :
    HasFDerivAt (fun y => partialDerivScalar f y j)
      ((ContinuousLinearMap.apply ℝ ℝ (basisVec j)).comp (fderiv ℝ (fderiv ℝ f) x)) x := by
  have h1 : ContDiffAt ℝ 1 (fderiv ℝ f) x := hf.fderiv_right (by simp [one_add_one_eq_two])
  have hdiff : DifferentiableAt ℝ (fderiv ℝ f) x := h1.differentiableAt (by simp)
  exact (ContinuousLinearMap.apply ℝ ℝ (basisVec j)).hasFDerivAt.comp x hdiff.hasFDerivAt

theorem partial_partial_eq_sndPartial
    (f : R3 → ℝ) (x : R3) (hf : ContDiffAt ℝ 2 f x) (i j : Fin 3) :
    partialDerivScalar (fun y => partialDerivScalar f y j) x i = sndPartial f x i j := by
  have h := (hasFDerivAt_partialDerivScalar f x hf j).fderiv
  change fderiv ℝ (fun y => partialDerivScalar f y j) x (basisVec i) = sndPartial f x i j
  rw [h]
  rfl

theorem partialDerivScalar_sub_of_hasFDerivAt
    {g₁ g₂ : R3 → ℝ} {L₁ L₂ : R3 →L[ℝ] ℝ} {x : R3}
    (h₁ : HasFDerivAt g₁ L₁ x) (h₂ : HasFDerivAt g₂ L₂ x) (i : Fin 3) :
    partialDerivScalar (fun y => g₁ y - g₂ y) x i = L₁ (basisVec i) - L₂ (basisVec i) := by
  have hsub : HasFDerivAt (fun y => g₁ y - g₂ y) (L₁ - L₂) x := h₁.sub h₂
  unfold partialDerivScalar
  rw [hsub.fderiv]
  rfl

noncomputable def realPressureHessianJet
    (p : R3 → ℝ) (x : R3) (hp : ContDiffAt ℝ 2 p x) :
    GarryNavierStokesMathlib.C2PressureHessianJet where
  dxx := sndPartial p x 0 0
  dyy := sndPartial p x 1 1
  dzz := sndPartial p x 2 2
  dxy := sndPartial p x 0 1
  dyx := sndPartial p x 1 0
  dyz := sndPartial p x 1 2
  dzy := sndPartial p x 2 1
  dzx := sndPartial p x 2 0
  dxz := sndPartial p x 0 2
  schwarz_xy := sndPartial_symm_of_contDiffAt p x hp 0 1
  schwarz_yz := sndPartial_symm_of_contDiffAt p x hp 1 2
  schwarz_zx := sndPartial_symm_of_contDiffAt p x hp 2 0

/-- Bridge to Garry's `lemma2_hodge_helmholtz_curl_grad_pressure_zero` from real `C²` pressure. -/
theorem real_c2_pressure_curl_grad_zero
    (p : R3 → ℝ) (x : R3) (hp : ContDiffAt ℝ 2 p x) :
    GarryNavierStokesMathlib.curlOfGradPressure (realPressureHessianJet p x hp) = ⟨0, 0, 0⟩ :=
  GarryNavierStokesMathlib.lemma2_hodge_helmholtz_curl_grad_pressure_zero
    (realPressureHessianJet p x hp)

/-- **Identity 1 (`∇ × (∇p) = 0`):** Direct proof on `curl3D` and `grad3D` for any `C²` scalar field `p`. -/
theorem curl3D_grad3D_eq_zero
    (p : R3 → ℝ) (x : R3) (hp : ContDiffAt ℝ 2 p x) :
    curl3D (grad3D p) x = vec3 0 0 0 := by
  funext i
  match i with
  | ⟨0, _⟩ =>
    change partialDerivScalar (fun y => partialDerivScalar p y 2) x 1 -
           partialDerivScalar (fun y => partialDerivScalar p y 1) x 2 = 0
    rw [partial_partial_eq_sndPartial p x hp 1 2, partial_partial_eq_sndPartial p x hp 2 1,
        sndPartial_symm_of_contDiffAt p x hp 1 2, sub_self]
  | ⟨1, _⟩ =>
    change partialDerivScalar (fun y => partialDerivScalar p y 0) x 2 -
           partialDerivScalar (fun y => partialDerivScalar p y 2) x 0 = 0
    rw [partial_partial_eq_sndPartial p x hp 2 0, partial_partial_eq_sndPartial p x hp 0 2,
        sndPartial_symm_of_contDiffAt p x hp 2 0, sub_self]
  | ⟨2, _⟩ =>
    change partialDerivScalar (fun y => partialDerivScalar p y 1) x 0 -
           partialDerivScalar (fun y => partialDerivScalar p y 0) x 1 = 0
    rw [partial_partial_eq_sndPartial p x hp 0 1, partial_partial_eq_sndPartial p x hp 1 0,
        sndPartial_symm_of_contDiffAt p x hp 0 1, sub_self]

/-- **Identity 2 (`∇ · (∇ × u) = 0`):** Unconditional proof for any `C²` 3D vector field `u : ℝ³ → ℝ³`. -/
theorem div3D_curl3D_eq_zero
    (u : R3 → R3) (x : R3) (hu : ContDiffAt ℝ 2 u x) :
    div3D (curl3D u) x = 0 := by
  have hu0 : ContDiffAt ℝ 2 (fun y => u y 0) x := contDiffAt_pi.mp hu 0
  have hu1 : ContDiffAt ℝ 2 (fun y => u y 1) x := contDiffAt_pi.mp hu 1
  have hu2 : ContDiffAt ℝ 2 (fun y => u y 2) x := contDiffAt_pi.mp hu 2
  have hd0 : partialDerivScalar (fun y => curl3D u y 0) x 0 =
      sndPartial (fun y => u y 2) x 0 1 - sndPartial (fun y => u y 1) x 0 2 := by
    exact partialDerivScalar_sub_of_hasFDerivAt
      (hasFDerivAt_partialDerivScalar (fun y => u y 2) x hu2 1)
      (hasFDerivAt_partialDerivScalar (fun y => u y 1) x hu1 2) 0
  have hd1 : partialDerivScalar (fun y => curl3D u y 1) x 1 =
      sndPartial (fun y => u y 0) x 1 2 - sndPartial (fun y => u y 2) x 1 0 := by
    exact partialDerivScalar_sub_of_hasFDerivAt
      (hasFDerivAt_partialDerivScalar (fun y => u y 0) x hu0 2)
      (hasFDerivAt_partialDerivScalar (fun y => u y 2) x hu2 0) 1
  have hd2 : partialDerivScalar (fun y => curl3D u y 2) x 2 =
      sndPartial (fun y => u y 1) x 2 0 - sndPartial (fun y => u y 0) x 2 1 := by
    exact partialDerivScalar_sub_of_hasFDerivAt
      (hasFDerivAt_partialDerivScalar (fun y => u y 1) x hu1 0)
      (hasFDerivAt_partialDerivScalar (fun y => u y 0) x hu0 1) 2
  unfold div3D
  rw [hd0, hd1, hd2]
  rw [sndPartial_symm_of_contDiffAt (fun y => u y 2) x hu2 1 0,
      sndPartial_symm_of_contDiffAt (fun y => u y 1) x hu1 2 0,
      sndPartial_symm_of_contDiffAt (fun y => u y 0) x hu0 2 1]
  ring

-- ============================================================================
-- SECTION 3: EXACT 3D SOLENOIDAL PLANE WAVE `u₀(x) = a * sin(k · x)`
-- ============================================================================

noncomputable def dotLinear (k : R3) : R3 →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap
    { toFun := dot3D k
      map_add' := fun x y => by simp [dot3D]; ring
      map_smul' := fun c x => by simp [dot3D]; ring }

theorem dotLinear_basisVec (k : R3) (j : Fin 3) :
    dotLinear k (basisVec j) = k j := by
  match j with
  | ⟨0, _⟩ => simp [dotLinear, dot3D, basisVec]
  | ⟨1, _⟩ => simp [dotLinear, dot3D, basisVec]
  | ⟨2, _⟩ => simp [dotLinear, dot3D, basisVec]

noncomputable def planeWave3D (k a : R3) (x : R3) : R3 :=
  fun comp => a comp * Real.sin (dot3D k x)

theorem hasFDerivAt_planeWave_comp (k a : R3) (comp : Fin 3) (x : R3) :
    HasFDerivAt (fun y => planeWave3D k a y comp)
      (a comp • (Real.cos (dot3D k x) • dotLinear k)) x := by
  have h1 : HasFDerivAt (dot3D k) (dotLinear k) x := (dotLinear k).hasFDerivAt
  have h2 : HasFDerivAt (fun y => Real.sin (dot3D k y))
      (Real.cos (dot3D k x) • dotLinear k) x :=
    (Real.hasDerivAt_sin (dot3D k x)).comp_hasFDerivAt x h1
  exact h2.const_mul (a comp)

theorem partialDerivScalar_planeWave3D (k a : R3) (comp j : Fin 3) (x : R3) :
    partialDerivScalar (fun y => planeWave3D k a y comp) x j =
      a comp * k j * Real.cos (dot3D k x) := by
  unfold partialDerivScalar
  rw [(hasFDerivAt_planeWave_comp k a comp x).fderiv]
  simp [dotLinear_basisVec]
  ring

/-- Exact divergence of the 3D plane wave `u₀(x) = a * sin(k · x)` at every `x ∈ ℝ³`. -/
theorem planeWave3D_div_eq (k a x : R3) :
    div3D (planeWave3D k a) x = dot3D k a * Real.cos (dot3D k x) := by
  unfold div3D
  rw [partialDerivScalar_planeWave3D, partialDerivScalar_planeWave3D,
      partialDerivScalar_planeWave3D]
  have hka : dot3D k a = k 0 * a 0 + k 1 * a 1 + k 2 * a 2 := rfl
  rw [hka]
  ring

/-- Solenoidal theorem: `k · a = 0` implies `div(u₀)(x) = 0` identically for all `x ∈ ℝ³`. -/
theorem planeWave3D_div_eq_zero_of_ortho (k a : R3) (h_ortho : dot3D k a = 0) (x : R3) :
    div3D (planeWave3D k a) x = 0 := by
  rw [planeWave3D_div_eq, h_ortho, zero_mul]

/-- Exact curl (vorticity) of the 3D plane wave `u₀(x) = a * sin(k · x)` at every `x ∈ ℝ³`. -/
theorem planeWave3D_curl_eq (k a x : R3) :
    curl3D (planeWave3D k a) x = fun i => cross3D k a i * Real.cos (dot3D k x) := by
  funext i
  match i with
  | ⟨0, _⟩ =>
    change partialDerivScalar (fun y => planeWave3D k a y 2) x 1 -
           partialDerivScalar (fun y => planeWave3D k a y 1) x 2 =
           (k 1 * a 2 - k 2 * a 1) * Real.cos (dot3D k x)
    rw [partialDerivScalar_planeWave3D, partialDerivScalar_planeWave3D]
    ring
  | ⟨1, _⟩ =>
    change partialDerivScalar (fun y => planeWave3D k a y 0) x 2 -
           partialDerivScalar (fun y => planeWave3D k a y 2) x 0 =
           (k 2 * a 0 - k 0 * a 2) * Real.cos (dot3D k x)
    rw [partialDerivScalar_planeWave3D, partialDerivScalar_planeWave3D]
    ring
  | ⟨2, _⟩ =>
    change partialDerivScalar (fun y => planeWave3D k a y 1) x 0 -
           partialDerivScalar (fun y => planeWave3D k a y 0) x 1 =
           (k 0 * a 1 - k 1 * a 0) * Real.cos (dot3D k x)
    rw [partialDerivScalar_planeWave3D, partialDerivScalar_planeWave3D]
    ring

-- ============================================================================
-- SECTION 4: CLASSICAL 3D INCOMPRESSIBLE NAVIER-STOKES PDE DEFINITION
-- ============================================================================

/-- Classical 3D incompressible Navier-Stokes system on `ℝ³ × [0, ∞)` (zero external forcing),
    stated directly with Mathlib4 time derivatives (`deriv`) and spatial Fréchet derivatives. -/
structure IsClassicalNS3D (u : ℝ → R3 → R3) (p : ℝ → R3 → ℝ) (ν : ℝ) : Prop where
  h_nu_pos : 0 < ν
  h_u_smooth : ∀ t ≥ 0, ∀ x : R3, ContDiffAt ℝ 2 (u t) x
  h_p_smooth : ∀ t ≥ 0, ∀ x : R3, ContDiffAt ℝ 2 (p t) x
  h_incompressible : ∀ t ≥ 0, ∀ x : R3, div3D (u t) x = 0
  h_momentum : ∀ t ≥ 0, ∀ x : R3, ∀ comp : Fin 3,
    deriv (fun s => u s x comp) t + advection3D (u t) x comp + grad3D (p t) x comp =
      ν * laplacian3D (u t) x comp

theorem partialDerivScalar_const (c : ℝ) (x : R3) (i : Fin 3) :
    partialDerivScalar (fun _ : R3 => c) x i = 0 := by
  simp [partialDerivScalar]

theorem sndPartial_const (c : ℝ) (x : R3) (i j : Fin 3) :
    sndPartial (fun _ : R3 => c) x i j = 0 := by
  have h0 : fderiv ℝ (fun _ : R3 => c) = fun _ => 0 := by
    funext y
    exact fderiv_const_apply c
  simp [sndPartial, h0]

/-- Non-vacuity witness: any steady uniform velocity `u(t,x) = c` with constant pressure `p₀`
    satisfies `IsClassicalNS3D` for every `ν > 0`. -/
theorem steadyUniformFlow_isClassicalNS3D (c : R3) (p₀ ν : ℝ) (hν : 0 < ν) :
    IsClassicalNS3D (fun _ _ => c) (fun _ _ => p₀) ν where
  h_nu_pos := hν
  h_u_smooth := fun _ _ _ => contDiffAt_const
  h_p_smooth := fun _ _ _ => contDiffAt_const
  h_incompressible := fun _ _ x => by
    simp [div3D, partialDerivScalar_const]
  h_momentum := fun t _ x comp => by
    simp [deriv_const, advection3D, grad3D, laplacian3D, laplacianScalar,
          partialDerivScalar_const, sndPartial_const]

-- ============================================================================
-- SECTION 5: AXIOM AUDIT TRAIL (0 sorryAx)
-- ============================================================================

#print axioms real_c2_pressure_curl_grad_zero
#print axioms curl3D_grad3D_eq_zero
#print axioms div3D_curl3D_eq_zero
#print axioms planeWave3D_div_eq_zero_of_ortho
#print axioms planeWave3D_curl_eq
#print axioms steadyUniformFlow_isClassicalNS3D

end GarryReal3DCalculus