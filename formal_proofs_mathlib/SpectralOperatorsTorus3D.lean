import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import FourierSpectralTorus3D

/-!
# GARRYULT v4.0.0 — Milestone 5A: 3D Spectral Fluid Operators on `𝕋³`
Formalizes directly from `IsPeriodicClassicalNS3D_C3` and Milestone 4B's 3D Fourier
coefficients (`0 sorryAx`):
1. Exact 3D Spectral Biot–Savart Law: `ω̂(k) = 2πi (k × û(k))`,
   `û(k) = (i / (2π|k|²)) (k × ω̂(k))`, and `|ω̂(k)|² = 4π²|k|² |û(k)|²`.
2. 3D Leray–Helmholtz Projector `ℙ_k`: idempotence, solenoidality, annihilation of
   `∇p`, and exact Hermitian Pythagoras decomposition `|ℙ_k v|² + |(I - ℙ_k)v|² = |v|²`.
3. Exact 3D Pressure Poisson Equation & Modewise Calderón–Zygmund Gradient Bound:
   `p̂(k) = (i / (2π|k|²)) (k · ((u·∇)u)^∧(k))`, `|(∇p)^∧(k)|² ≤ |((u·∇)u)^∧(k)|²`.
4. Pressure-Eliminated Spectral 3D Navier–Stokes PDE:
   `(∂_t u)^∧(k) + ℙ_k(((u·∇)u)^∧(k)) + 4π² ν |k|² û(k) = 0`.
-/

namespace GarrySpectralOperators3D

open MeasureTheory Filter Topology GarryReal3DCalculus GarryVorticity3D
  GarryLerayTorus3D GarryLerayEnergyLaw3D GarryPoincareSobolev3D GarryFourierSpectral3D

private lemma two_add_one_eq_three5 {α : Type*} [AddMonoidWithOne α] :
    (2 : α) + 1 = 3 := by
  rw [← Nat.cast_ofNat (n := 2), ← Nat.cast_one, ← Nat.cast_add]
  exact Nat.cast_ofNat

private lemma contDiff_two_of_three5 {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {f : E → F} (hf : ContDiff ℝ 3 f) :
    ContDiff ℝ 2 f :=
  hf.of_le (by rw [← two_add_one_eq_three5]; exact le_self_add)

private lemma contDiff_one_of_two5 {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {f : E → F} (hf : ContDiff ℝ 2 f) :
    ContDiff ℝ 1 f :=
  hf.of_le (by rw [← one_add_one_eq_two]; exact le_self_add)

-- ============================================================================
-- SECTION 1: COMPLEX 3D VECTOR ALGEBRA & VECTOR FOURIER COEFFICIENTS ON `𝕋³`
-- ============================================================================

/-- Complex 3D vector space `ℂ³`. -/
abbrev C3 := Fin 3 → ℂ

/-- Real squared Euclidean norm of a wavevector `k ∈ ℤ³`: `|k|² = k₀² + k₁² + k₂²`. -/
def kNormSq (k : Fin 3 → ℤ) : ℝ :=
  (k 0 : ℝ) ^ 2 + (k 1 : ℝ) ^ 2 + (k 2 : ℝ) ^ 2

/-- Complex cast of `|k|²`. -/
def kNormSqC (k : Fin 3 → ℤ) : ℂ :=
  (k 0 : ℂ) ^ 2 + (k 1 : ℂ) ^ 2 + (k 2 : ℂ) ^ 2

theorem kNormSqC_eq_ofReal (k : Fin 3 → ℤ) : kNormSqC k = ((kNormSq k : ℝ) : ℂ) := by
  unfold kNormSqC kNormSq
  push_cast
  ring

theorem kNormSq_pos_of_ne_zero {k : Fin 3 → ℤ} (hk : k ≠ 0) : 0 < kNormSq k := by
  unfold kNormSq
  have h0 : 0 ≤ (k 0 : ℝ) ^ 2 := sq_nonneg _
  have h1 : 0 ≤ (k 1 : ℝ) ^ 2 := sq_nonneg _
  have h2 : 0 ≤ (k 2 : ℝ) ^ 2 := sq_nonneg _
  by_contra hle
  push Not at hle
  have e0 : (k 0 : ℝ) = 0 := sq_eq_zero_iff.mp (by linarith)
  have e1 : (k 1 : ℝ) = 0 := sq_eq_zero_iff.mp (by linarith)
  have e2 : (k 2 : ℝ) = 0 := sq_eq_zero_iff.mp (by linarith)
  apply hk
  funext i
  fin_cases i
  · exact Int.cast_eq_zero.mp e0
  · exact Int.cast_eq_zero.mp e1
  · exact Int.cast_eq_zero.mp e2

theorem kNormSqC_ne_zero {k : Fin 3 → ℤ} (hk : k ≠ 0) : kNormSqC k ≠ 0 := by
  rw [kNormSqC_eq_ofReal]
  exact Complex.ofReal_ne_zero.mpr (ne_of_gt (kNormSq_pos_of_ne_zero hk))

/-- Complex wavevector `k ∈ ℂ³`. -/
def kVecC (k : Fin 3 → ℤ) : C3 := fun i => (k i : ℂ)

/-- Complex bilinear dot product `a · b = a₀b₀ + a₁b₁ + a₂b₂`. -/
def dotC3 (a b : C3) : ℂ :=
  a 0 * b 0 + a 1 * b 1 + a 2 * b 2

/-- Complex 3D cross product `a × b`. -/
def crossC3 (a b : C3) : C3
  | ⟨0, _⟩ => a 1 * b 2 - a 2 * b 1
  | ⟨1, _⟩ => a 2 * b 0 - a 0 * b 2
  | ⟨2, _⟩ => a 0 * b 1 - a 1 * b 0

/-- Squared Hermitian Euclidean norm `|v|² = ‖v₀‖² + ‖v₁‖² + ‖v₂‖²` on `ℂ³`. -/
noncomputable def normSqC3 (v : C3) : ℝ :=
  ‖v 0‖ ^ 2 + ‖v 1‖ ^ 2 + ‖v 2‖ ^ 2

theorem normSqC3_nonneg (v : C3) : 0 ≤ normSqC3 v := by
  unfold normSqC3
  have h0 : 0 ≤ ‖v 0‖ ^ 2 := sq_nonneg _
  have h1 : 0 ≤ ‖v 1‖ ^ 2 := sq_nonneg _
  have h2 : 0 ≤ ‖v 2‖ ^ 2 := sq_nonneg _
  linarith

private theorem complex_norm_sq_eq_mul_conj (z : ℂ) :
    ((‖z‖ : ℂ) ^ 2) = z * starRingEnd ℂ z := by
  have h : ((‖z‖ ^ 2 : ℝ) : ℂ) = z * starRingEnd ℂ z := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  simpa using h

theorem normSqC3_ofReal (v : C3) :
    ((normSqC3 v : ℝ) : ℂ) =
      v 0 * starRingEnd ℂ (v 0) + v 1 * starRingEnd ℂ (v 1) + v 2 * starRingEnd ℂ (v 2) := by
  unfold normSqC3
  push_cast
  rw [complex_norm_sq_eq_mul_conj (v 0),
      complex_norm_sq_eq_mul_conj (v 1),
      complex_norm_sq_eq_mul_conj (v 2)]

/-- Vector-valued 3D Fourier coefficient `û(k) ∈ ℂ³`. -/
noncomputable def fourierCoeff3DVec (u : R3 → R3) (k : Fin 3 → ℤ) : C3 :=
  fun comp => fourierCoeff3D (fun x => u x comp) k

theorem fourierCoeff3D_const_mul {f : R3 → ℝ} (c : ℝ) (k : Fin 3 → ℤ) :
    fourierCoeff3D (fun x => c * f x) k = (c : ℂ) * fourierCoeff3D f k := by
  unfold fourierCoeff3D
  have h1 : ∀ x y : ℝ,
      (∫ z in (0 : ℝ)..1, fourierChar1D (k 0) x * fourierChar1D (k 1) y * fourierChar1D (k 2) z *
        ((c * f (vec3 x y z) : ℝ) : ℂ)) =
      (c : ℂ) * ∫ z in (0 : ℝ)..1, fourierChar1D (k 0) x * fourierChar1D (k 1) y *
        fourierChar1D (k 2) z * (f (vec3 x y z) : ℂ) := by
    intro x y
    have hpt : (fun z => fourierChar1D (k 0) x * fourierChar1D (k 1) y * fourierChar1D (k 2) z *
        ((c * f (vec3 x y z) : ℝ) : ℂ)) =
        (fun z => (c : ℂ) * (fourierChar1D (k 0) x * fourierChar1D (k 1) y *
          fourierChar1D (k 2) z * (f (vec3 x y z) : ℂ))) := by
      funext z; push_cast; ring
    rw [hpt, intervalIntegral.integral_const_mul]
  simp_rw [h1, intervalIntegral.integral_const_mul]

theorem fourierCoeff3D_sub {f g : R3 → ℝ} (hf : Continuous f) (hg : Continuous g) (k : Fin 3 → ℤ) :
    fourierCoeff3D (fun x => f x - g x) k = fourierCoeff3D f k - fourierCoeff3D g k := by
  have hpt : (fun x => f x - g x) = (fun x => f x + (-1 : ℝ) * g x) := by funext x; ring
  have hmg : Continuous (fun x => (-1 : ℝ) * g x) := continuous_const.mul hg
  rw [hpt, fourierCoeff3D_add hf hmg k, fourierCoeff3D_const_mul (-1 : ℝ) k]
  push_cast
  ring

-- ============================================================================
-- SECTION 2: 3D SPECTRAL BIOT–SAVART LAW (`û(k) = (i / (2π|k|²)) (k × ω̂(k))`)
-- ============================================================================

/-- **Spectral Curl Formula (`ω̂(k) = 2πi (k × û(k))`):**
    For any `C¹` periodic vector field `u` on `𝕋³`, every component of the Fourier
    transform of `ω = ∇ × u` satisfies `ω̂(k)_c = 2πi (k × û(k))_c` (`0 sorryAx`). -/
theorem fourierCoeff3DVec_curl3D
    {u : R3 → R3} (hu : ContDiff ℝ 1 u) (hpu : IsPeriodic3D u) (k : Fin 3 → ℤ) (comp : Fin 3) :
    fourierCoeff3DVec (curl3D u) k comp =
      (2 * (Real.pi : ℂ) * Complex.I) * crossC3 (kVecC k) (fourierCoeff3DVec u k) comp := by
  have hu0 : ContDiff ℝ 1 (fun y => u y 0) := contDiff_pi.mp hu 0
  have hu1 : ContDiff ℝ 1 (fun y => u y 1) := contDiff_pi.mp hu 1
  have hu2 : ContDiff ℝ 1 (fun y => u y 2) := contDiff_pi.mp hu 2
  have hpu0 : IsPeriodic3D (fun y => u y 0) := fun x i => congrArg (fun v => v 0) (hpu x i)
  have hpu1 : IsPeriodic3D (fun y => u y 1) := fun x i => congrArg (fun v => v 1) (hpu x i)
  have hpu2 : IsPeriodic3D (fun y => u y 2) := fun x i => congrArg (fun v => v 2) (hpu x i)
  unfold fourierCoeff3DVec
  match comp with
  | ⟨0, _⟩ =>
    change fourierCoeff3D (fun x => partialDerivScalar (fun y => u y 2) x 1 -
        partialDerivScalar (fun y => u y 1) x 2) k = _
    rw [fourierCoeff3D_sub (continuous_partialDerivScalar_of_contDiff hu2 1)
          (continuous_partialDerivScalar_of_contDiff hu1 2) k,
        fourierCoeff3D_partialDeriv hu2 hpu2 k 1,
        fourierCoeff3D_partialDeriv hu1 hpu1 k 2]
    unfold crossC3 kVecC; ring
  | ⟨1, _⟩ =>
    change fourierCoeff3D (fun x => partialDerivScalar (fun y => u y 0) x 2 -
        partialDerivScalar (fun y => u y 2) x 0) k = _
    rw [fourierCoeff3D_sub (continuous_partialDerivScalar_of_contDiff hu0 2)
          (continuous_partialDerivScalar_of_contDiff hu2 0) k,
        fourierCoeff3D_partialDeriv hu0 hpu0 k 2,
        fourierCoeff3D_partialDeriv hu2 hpu2 k 0]
    unfold crossC3 kVecC; ring
  | ⟨2, _⟩ =>
    change fourierCoeff3D (fun x => partialDerivScalar (fun y => u y 1) x 0 -
        partialDerivScalar (fun y => u y 0) x 1) k = _
    rw [fourierCoeff3D_sub (continuous_partialDerivScalar_of_contDiff hu1 0)
          (continuous_partialDerivScalar_of_contDiff hu0 1) k,
        fourierCoeff3D_partialDeriv hu1 hpu1 k 0,
        fourierCoeff3D_partialDeriv hu0 hpu0 k 1]
    unfold crossC3 kVecC; ring

/-- **MAIN THEOREM 1 OF MILESTONE 5A (Exact 3D Spectral Biot–Savart Inversion & Norm Law):**
    For any `C¹` periodic divergence-free velocity field `u` (`∇ · u = 0`) and every
    nonzero wavevector `k ≠ 0`:
    1. Exact Biot–Savart inversion:
       `û(k) = (i / (2π |k|²)) * (k × ω̂(k))`.
    2. Exact spectral enstrophy–velocity norm law:
       `|ω̂(k)|² = 4π² |k|² |û(k)|²` (`0 sorryAx`). -/
theorem biot_savart_3d_spectral
    {u : R3 → R3} (hu : ContDiff ℝ 1 u) (hpu : IsPeriodic3D u)
    (hdiv : ∀ x : R3, div3D u x = 0) {k : Fin 3 → ℤ} (hk : k ≠ 0) :
    (∀ comp : Fin 3,
      fourierCoeff3DVec u k comp =
        (Complex.I / (2 * (Real.pi : ℂ) * kNormSqC k)) *
          crossC3 (kVecC k) (fourierCoeff3DVec (curl3D u) k) comp) ∧
    normSqC3 (fourierCoeff3DVec (curl3D u) k) =
      4 * Real.pi ^ 2 * kNormSq k * normSqC3 (fourierCoeff3DVec u k) := by
  have hortho : dotC3 (kVecC k) (fourierCoeff3DVec u k) = 0 :=
    fourierCoeff3D_solenoidal_ortho hu hpu hdiv k
  have hw0 := fourierCoeff3DVec_curl3D hu hpu k 0
  have hw1 := fourierCoeff3DVec_curl3D hu hpu k 1
  have hw2 := fourierCoeff3DVec_curl3D hu hpu k 2
  have hk2_ne : kNormSqC k ≠ 0 := kNormSqC_ne_zero hk
  have hpi_ne : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hden_ne : 2 * (Real.pi : ℂ) * kNormSqC k ≠ 0 :=
    mul_ne_zero (mul_ne_zero (by norm_num) hpi_ne) hk2_ne
  constructor
  · intro comp
    have hbac : crossC3 (kVecC k) (fourierCoeff3DVec (curl3D u) k) comp =
        (-2 * (Real.pi : ℂ) * Complex.I * kNormSqC k) * fourierCoeff3DVec u k comp := by
      unfold dotC3 kVecC at hortho
      unfold crossC3 kVecC at hw0 hw1 hw2
      unfold crossC3 kVecC kNormSqC
      dsimp only at hw0 hw1 hw2
      fin_cases comp
      · change (k 1 : ℂ) * fourierCoeff3DVec (curl3D u) k 2 -
            (k 2 : ℂ) * fourierCoeff3DVec (curl3D u) k 1 =
            (-2 * (Real.pi : ℂ) * Complex.I * ((k 0 : ℂ) ^ 2 + (k 1 : ℂ) ^ 2 + (k 2 : ℂ) ^ 2)) *
              fourierCoeff3DVec u k 0
        rw [hw1, hw2]
        linear_combination (2 * (Real.pi : ℂ) * Complex.I * (k 0 : ℂ)) * hortho
      · change (k 2 : ℂ) * fourierCoeff3DVec (curl3D u) k 0 -
            (k 0 : ℂ) * fourierCoeff3DVec (curl3D u) k 2 =
            (-2 * (Real.pi : ℂ) * Complex.I * ((k 0 : ℂ) ^ 2 + (k 1 : ℂ) ^ 2 + (k 2 : ℂ) ^ 2)) *
              fourierCoeff3DVec u k 1
        rw [hw0, hw2]
        linear_combination (2 * (Real.pi : ℂ) * Complex.I * (k 1 : ℂ)) * hortho
      · change (k 0 : ℂ) * fourierCoeff3DVec (curl3D u) k 1 -
            (k 1 : ℂ) * fourierCoeff3DVec (curl3D u) k 0 =
            (-2 * (Real.pi : ℂ) * Complex.I * ((k 0 : ℂ) ^ 2 + (k 1 : ℂ) ^ 2 + (k 2 : ℂ) ^ 2)) *
              fourierCoeff3DVec u k 2
        rw [hw0, hw1]
        linear_combination (2 * (Real.pi : ℂ) * Complex.I * (k 2 : ℂ)) * hortho
    rw [hbac]
    have hcancel : (Complex.I / (2 * (Real.pi : ℂ) * kNormSqC k)) *
        (-2 * (Real.pi : ℂ) * Complex.I * kNormSqC k) = 1 := by
      field_simp [hden_ne]
      rw [Complex.I_sq]; ring
    calc fourierCoeff3DVec u k comp
        = 1 * fourierCoeff3DVec u k comp := (one_mul _).symm
      _ = ((Complex.I / (2 * (Real.pi : ℂ) * kNormSqC k)) *
            (-2 * (Real.pi : ℂ) * Complex.I * kNormSqC k)) * fourierCoeff3DVec u k comp := by
          rw [hcancel]
      _ = (Complex.I / (2 * (Real.pi : ℂ) * kNormSqC k)) *
            ((-2 * (Real.pi : ℂ) * Complex.I * kNormSqC k) * fourierCoeff3DVec u k comp) := by
          ring
  · apply Complex.ofReal_injective
    rw [normSqC3_ofReal]
    push_cast
    rw [normSqC3_ofReal, ← kNormSqC_eq_ofReal]
    have hconj_k : ∀ i : Fin 3, starRingEnd ℂ (k i : ℂ) = (k i : ℂ) := fun i => by
      rw [← Complex.ofReal_intCast, Complex.conj_ofReal]
    have hconj_pi : starRingEnd ℂ (Real.pi : ℂ) = (Real.pi : ℂ) := Complex.conj_ofReal _
    have hconj_I : starRingEnd ℂ Complex.I = -Complex.I := Complex.conj_I
    have hortho_conj :
        (k 0 : ℂ) * starRingEnd ℂ (fourierCoeff3DVec u k 0) +
        (k 1 : ℂ) * starRingEnd ℂ (fourierCoeff3DVec u k 1) +
        (k 2 : ℂ) * starRingEnd ℂ (fourierCoeff3DVec u k 2) = 0 := by
      have hc := congrArg (starRingEnd ℂ) hortho
      unfold dotC3 kVecC at hc
      simp only [map_add, map_mul, map_zero, hconj_k] at hc
      exact hc
    rw [hw0, hw1, hw2]
    unfold crossC3 kVecC kNormSqC
    dsimp only
    simp only [map_sub, map_mul, map_ofNat, hconj_k, hconj_pi, hconj_I]
    have hI_neg : (2 * (Real.pi : ℂ) * Complex.I) * (2 * (Real.pi : ℂ) * -Complex.I) =
        4 * (Real.pi : ℂ) ^ 2 := by
      calc (2 * (Real.pi : ℂ) * Complex.I) * (2 * (Real.pi : ℂ) * -Complex.I)
          = -4 * (Real.pi : ℂ) ^ 2 * Complex.I ^ 2 := by ring
        _ = -4 * (Real.pi : ℂ) ^ 2 * (-1) := by rw [Complex.I_sq]
        _ = 4 * (Real.pi : ℂ) ^ 2 := by ring
    have hlhs_simp :
        2 * (Real.pi : ℂ) * Complex.I *
            ((k 1 : ℂ) * fourierCoeff3DVec u k 2 - (k 2 : ℂ) * fourierCoeff3DVec u k 1) *
          (2 * (Real.pi : ℂ) * -Complex.I *
            ((k 1 : ℂ) * starRingEnd ℂ (fourierCoeff3DVec u k 2) -
             (k 2 : ℂ) * starRingEnd ℂ (fourierCoeff3DVec u k 1))) +
        2 * (Real.pi : ℂ) * Complex.I *
            ((k 2 : ℂ) * fourierCoeff3DVec u k 0 - (k 0 : ℂ) * fourierCoeff3DVec u k 2) *
          (2 * (Real.pi : ℂ) * -Complex.I *
            ((k 2 : ℂ) * starRingEnd ℂ (fourierCoeff3DVec u k 0) -
             (k 0 : ℂ) * starRingEnd ℂ (fourierCoeff3DVec u k 2))) +
        2 * (Real.pi : ℂ) * Complex.I *
            ((k 0 : ℂ) * fourierCoeff3DVec u k 1 - (k 1 : ℂ) * fourierCoeff3DVec u k 0) *
          (2 * (Real.pi : ℂ) * -Complex.I *
            ((k 0 : ℂ) * starRingEnd ℂ (fourierCoeff3DVec u k 1) -
             (k 1 : ℂ) * starRingEnd ℂ (fourierCoeff3DVec u k 0))) =
        4 * (Real.pi : ℂ) ^ 2 *
          (((k 1 : ℂ) * fourierCoeff3DVec u k 2 - (k 2 : ℂ) * fourierCoeff3DVec u k 1) *
             ((k 1 : ℂ) * starRingEnd ℂ (fourierCoeff3DVec u k 2) -
              (k 2 : ℂ) * starRingEnd ℂ (fourierCoeff3DVec u k 1)) +
           ((k 2 : ℂ) * fourierCoeff3DVec u k 0 - (k 0 : ℂ) * fourierCoeff3DVec u k 2) *
             ((k 2 : ℂ) * starRingEnd ℂ (fourierCoeff3DVec u k 0) -
              (k 0 : ℂ) * starRingEnd ℂ (fourierCoeff3DVec u k 2)) +
           ((k 0 : ℂ) * fourierCoeff3DVec u k 1 - (k 1 : ℂ) * fourierCoeff3DVec u k 0) *
             ((k 0 : ℂ) * starRingEnd ℂ (fourierCoeff3DVec u k 1) -
              (k 1 : ℂ) * starRingEnd ℂ (fourierCoeff3DVec u k 0))) := by
      have hfac : ∀ a b : ℂ, (2 * (Real.pi : ℂ) * Complex.I * a) * (2 * (Real.pi : ℂ) * -Complex.I * b) =
          ((2 * (Real.pi : ℂ) * Complex.I) * (2 * (Real.pi : ℂ) * -Complex.I)) * (a * b) :=
        fun a b => by ring
      rw [hfac, hfac, hfac, hI_neg]; ring
    rw [hlhs_simp]
    unfold dotC3 kVecC at hortho
    have hprod_zero :
        ((k 0 : ℂ) * fourierCoeff3DVec u k 0 + (k 1 : ℂ) * fourierCoeff3DVec u k 1 +
          (k 2 : ℂ) * fourierCoeff3DVec u k 2) *
        ((k 0 : ℂ) * starRingEnd ℂ (fourierCoeff3DVec u k 0) +
         (k 1 : ℂ) * starRingEnd ℂ (fourierCoeff3DVec u k 1) +
         (k 2 : ℂ) * starRingEnd ℂ (fourierCoeff3DVec u k 2)) = 0 := by
      rw [hortho, zero_mul]
    linear_combination -(4 * (Real.pi : ℂ) ^ 2) * hprod_zero

-- ============================================================================
-- SECTION 3: 3D LERAY–HELMHOLTZ SPECTRAL PROJECTOR `ℙ_k` & PYTHAGORAS LAW
-- ============================================================================

/-- 3D spectral Leray–Helmholtz projection onto divergence-free modes:
    `ℙ_k(v) = v - ((k · v) / |k|²) k` for `k ≠ 0`, and `ℙ_0(v) = v`. -/
noncomputable def lerayProj3D (k : Fin 3 → ℤ) (v : C3) : C3 :=
  if k = 0 then v
  else fun comp => v comp - (dotC3 (kVecC k) v / kNormSqC k) * (k comp : ℂ)

/-- Complementary gradient (irrotational) projection `(I - ℙ_k)(v) = ((k · v) / |k|²) k`. -/
noncomputable def gradProj3D (k : Fin 3 → ℤ) (v : C3) : C3 :=
  if k = 0 then 0
  else fun comp => (dotC3 (kVecC k) v / kNormSqC k) * (k comp : ℂ)

theorem lerayProj3D_add_gradProj3D (k : Fin 3 → ℤ) (v : C3) (comp : Fin 3) :
    lerayProj3D k v comp + gradProj3D k v comp = v comp := by
  unfold lerayProj3D gradProj3D
  split_ifs
  · simp
  · ring

theorem lerayProj3D_solenoidal (k : Fin 3 → ℤ) (v : C3) :
    dotC3 (kVecC k) (lerayProj3D k v) = 0 := by
  unfold lerayProj3D
  by_cases hk : k = 0
  · subst hk; unfold dotC3 kVecC; simp
  · simp only [hk, ↓reduceIte]
    have hk2 : kNormSqC k ≠ 0 := kNormSqC_ne_zero hk
    unfold kNormSqC at hk2
    unfold dotC3 kVecC kNormSqC
    field_simp [hk2]
    ring

theorem lerayProj3D_eq_self_of_solenoidal {k : Fin 3 → ℤ} {v : C3}
    (h : dotC3 (kVecC k) v = 0) (comp : Fin 3) :
    lerayProj3D k v comp = v comp := by
  unfold lerayProj3D
  split_ifs
  · rfl
  · dsimp only
    rw [h, zero_div, zero_mul, sub_zero]

theorem lerayProj3D_idem (k : Fin 3 → ℤ) (v : C3) (comp : Fin 3) :
    lerayProj3D k (lerayProj3D k v) comp = lerayProj3D k v comp :=
  lerayProj3D_eq_self_of_solenoidal (lerayProj3D_solenoidal k v) comp

theorem lerayProj3D_add (k : Fin 3 → ℤ) (v w : C3) (comp : Fin 3) :
    lerayProj3D k (fun c => v c + w c) comp = lerayProj3D k v comp + lerayProj3D k w comp := by
  unfold lerayProj3D
  by_cases hk : k = 0
  · simp [hk]
  · simp only [hk, ↓reduceIte]
    have hdot : dotC3 (kVecC k) (fun c => v c + w c) = dotC3 (kVecC k) v + dotC3 (kVecC k) w := by
      unfold dotC3; ring
    rw [hdot]; ring

theorem lerayProj3D_smul (k : Fin 3 → ℤ) (α : ℂ) (v : C3) (comp : Fin 3) :
    lerayProj3D k (fun c => α * v c) comp = α * lerayProj3D k v comp := by
  unfold lerayProj3D
  by_cases hk : k = 0
  · simp [hk]
  · simp only [hk, ↓reduceIte]
    have hdot : dotC3 (kVecC k) (fun c => α * v c) = α * dotC3 (kVecC k) v := by
      unfold dotC3; ring
    rw [hdot]; ring

/-- **Spectral Annihilation of Pressure Gradient (`ℙ_k((∇p)^∧(k)) = 0`):**
    For any `C¹` periodic scalar pressure field `p` on `𝕋³` and every `k ∈ ℤ³`:
      `lerayProj3D k (fourierCoeff3DVec (grad3D p) k) = 0` (`0 sorryAx`). -/
theorem lerayProj3D_grad3D_eq_zero
    {p : R3 → ℝ} (hp : ContDiff ℝ 1 p) (hpp : IsPeriodic3D p) (k : Fin 3 → ℤ) (comp : Fin 3) :
    lerayProj3D k (fourierCoeff3DVec (grad3D p) k) comp = 0 := by
  have hgp : ∀ i : Fin 3, fourierCoeff3DVec (grad3D p) k i =
      (2 * (Real.pi : ℂ) * Complex.I * (k i : ℂ)) * fourierCoeff3D p k := fun i =>
    fourierCoeff3D_partialDeriv hp hpp k i
  unfold lerayProj3D
  by_cases hk : k = 0
  · subst hk
    simp [hgp comp]
  · simp only [hk, ↓reduceIte]
    have hk2 : kNormSqC k ≠ 0 := kNormSqC_ne_zero hk
    rw [hgp comp]
    have hdot : dotC3 (kVecC k) (fourierCoeff3DVec (grad3D p) k) =
        (2 * (Real.pi : ℂ) * Complex.I * kNormSqC k) * fourierCoeff3D p k := by
      unfold dotC3 kVecC kNormSqC
      rw [hgp 0, hgp 1, hgp 2]
      ring
    rw [hdot]
    field_simp [hk2]
    ring

/-- **Exact Hermitian Pythagoras Decomposition for `ℙ_k`:**
    `|ℙ_k(v)|² + |(I - ℙ_k)(v)|² = |v|²` for every `k ∈ ℤ³` and `v ∈ ℂ³` (`0 sorryAx`). -/
theorem lerayProj3D_pythagoras (k : Fin 3 → ℤ) (v : C3) :
    normSqC3 (lerayProj3D k v) + normSqC3 (gradProj3D k v) = normSqC3 v := by
  apply Complex.ofReal_injective
  push_cast
  rw [normSqC3_ofReal, normSqC3_ofReal, normSqC3_ofReal]
  have hsplit : ∀ i : Fin 3, v i = lerayProj3D k v i + gradProj3D k v i := fun i =>
    (lerayProj3D_add_gradProj3D k v i).symm
  have hconj_k : ∀ i : Fin 3, starRingEnd ℂ (k i : ℂ) = (k i : ℂ) := fun i => by
    rw [← Complex.ofReal_intCast, Complex.conj_ofReal]
  have hcross_zero :
      lerayProj3D k v 0 * starRingEnd ℂ (gradProj3D k v 0) +
      lerayProj3D k v 1 * starRingEnd ℂ (gradProj3D k v 1) +
      lerayProj3D k v 2 * starRingEnd ℂ (gradProj3D k v 2) = 0 := by
    by_cases hk : k = 0
    · unfold gradProj3D; simp [hk]
    · have hsol := lerayProj3D_solenoidal k v
      unfold gradProj3D
      simp only [hk, ↓reduceIte]
      simp only [map_mul, hconj_k]
      unfold dotC3 kVecC at hsol
      linear_combination starRingEnd ℂ (dotC3 (kVecC k) v / kNormSqC k) * hsol
  have hcross_conj_zero :
      gradProj3D k v 0 * starRingEnd ℂ (lerayProj3D k v 0) +
      gradProj3D k v 1 * starRingEnd ℂ (lerayProj3D k v 1) +
      gradProj3D k v 2 * starRingEnd ℂ (lerayProj3D k v 2) = 0 := by
    have hc := congrArg (starRingEnd ℂ) hcross_zero
    simp only [map_add, map_mul, starRingEnd_self_apply, map_zero] at hc
    linear_combination hc
  rw [hsplit 0, hsplit 1, hsplit 2]
  simp only [map_add]
  linear_combination -(hcross_zero + hcross_conj_zero)

-- ============================================================================
-- SECTION 4: SPECTRAL PRESSURE POISSON, CALDERÓN–ZYGMUND BOUND & PROJECTED NS3D
-- ============================================================================

/-- Spectral momentum PDE identity for every component `comp` and wavevector `k ∈ ℤ³`. -/
theorem navier_stokes_3d_momentum_spectral
    {u : ℝ → R3 → R3} {p : ℝ → R3 → ℝ} {ν : ℝ}
    (hns : IsPeriodicClassicalNS3D_C3 u p ν) {t : ℝ} (ht : t ≥ 0)
    (k : Fin 3 → ℤ) (comp : Fin 3) :
    fourierCoeff3DVec (fun x c => deriv (fun s => u s x c) t) k comp +
      fourierCoeff3DVec (advection3D (u t)) k comp +
      fourierCoeff3DVec (grad3D (p t)) k comp =
      (-4 * (Real.pi : ℂ) ^ 2 * (ν : ℂ) * kNormSqC k) * fourierCoeff3DVec (u t) k comp := by
  have hu2 : ContDiff ℝ 2 (u t) := contDiff_two_of_three5 (hns.h_u_c3_global t ht)
  have hu1 : ContDiff ℝ 1 (u t) := contDiff_one_of_two5 hu2
  have hp1 : ContDiff ℝ 1 (p t) := contDiff_one_of_two5 (hns.h_p_c2_global t ht)
  have huc2 : ContDiff ℝ 2 (fun y => u t y comp) := contDiff_pi.mp hu2 comp
  have hpuc : IsPeriodic3D (fun y => u t y comp) :=
    fun x i => congrArg (fun v => v comp) (hns.h_u_periodic t ht x i)
  have h_ut_cont : Continuous (fun x => deriv (fun s => u s x comp) t) := by
    have hFc : ∀ q : ℝ × R3, ContDiffAt ℝ 2 (fun r : ℝ × R3 => u r.1 r.2 comp) q :=
      fun q => contDiffAt_pi.mp (hns.h_u_c2_spacetime q) comp
    have hfun : (fun x => deriv (fun s => u s x comp) t) =
        (fun x => fderiv ℝ (fun r : ℝ × R3 => u r.1 r.2 comp) (t, x) ((1 : ℝ), (0 : R3))) := by
      funext x; exact timeDeriv_eq_fderiv_prod (fun r => u r.1 r.2 comp) hFc t x
    rw [hfun]
    have hcd1 : ContDiff ℝ 1 (fderiv ℝ (fun r : ℝ × R3 => u r.1 r.2 comp)) :=
      (contDiff_iff_contDiffAt.mpr hFc).fderiv_right (by simp [one_add_one_eq_two])
    exact ((ContinuousLinearMap.apply ℝ ℝ ((1 : ℝ), (0 : R3))).continuous.comp hcd1.continuous).comp
      (continuous_const.prodMk continuous_id)
  have h_adv_cont : Continuous (fun x => advection3D (u t) x comp) :=
    (continuous_apply comp).comp (continuous_advection3D hu1)
  have h_gp_cont : Continuous (fun x => grad3D (p t) x comp) :=
    (continuous_apply comp).comp (continuous_grad3D hp1)
  have h_eq_fun : (fun x => deriv (fun s => u s x comp) t + advection3D (u t) x comp +
        grad3D (p t) x comp) =
      (fun x => ν * laplacianScalar (fun y => u t y comp) x) := by
    funext x
    exact hns.h_momentum t ht x comp
  have h_fc := congrArg (fun f => fourierCoeff3D f k) h_eq_fun
  have h_add1 : Continuous (fun x => deriv (fun s => u s x comp) t + advection3D (u t) x comp) :=
    h_ut_cont.add h_adv_cont
  rw [fourierCoeff3D_add h_add1 h_gp_cont k,
      fourierCoeff3D_add h_ut_cont h_adv_cont k,
      fourierCoeff3D_const_mul ν k,
      fourierCoeff3D_laplacianScalar huc2 hpuc k] at h_fc
  unfold fourierCoeff3DVec kNormSqC
  linear_combination h_fc

/-- Time-derivative velocity field `∂_t u(t, ·)` is solenoidal in Fourier space:
    `k · (∂_t u)^∧(k) = 0`. -/
theorem fourierCoeff3D_timeDeriv_solenoidal
    {u : ℝ → R3 → R3} {p : ℝ → R3 → ℝ} {ν : ℝ}
    (hns : IsPeriodicClassicalNS3D_C3 u p ν) {t : ℝ} (ht : t ≥ 0) (k : Fin 3 → ℤ) :
    dotC3 (kVecC k) (fourierCoeff3DVec (fun x c => deriv (fun s => u s x c) t) k) = 0 := by
  -- Use `u(s, ·)` divergence-free for all `s ≥ 0` ⇒ `div(∂_t u) = ∂_t(div u) = 0` via `partial_timeDeriv_comm`
  have h_ut_c1 : ContDiff ℝ 1 (fun x c => deriv (fun s => u s x c) t) := by
    refine contDiff_pi.mpr fun comp => ?_
    have hFc : ∀ q : ℝ × R3, ContDiffAt ℝ 2 (fun r : ℝ × R3 => u r.1 r.2 comp) q :=
      fun q => contDiffAt_pi.mp (hns.h_u_c2_spacetime q) comp
    have hfun : (fun x => deriv (fun s => u s x comp) t) =
        (fun x => fderiv ℝ (fun r : ℝ × R3 => u r.1 r.2 comp) (t, x) ((1 : ℝ), (0 : R3))) := by
      funext x; exact timeDeriv_eq_fderiv_prod (fun r => u r.1 r.2 comp) hFc t x
    rw [hfun]
    have hcd1 : ContDiff ℝ 1 (fderiv ℝ (fun r : ℝ × R3 => u r.1 r.2 comp)) :=
      (contDiff_iff_contDiffAt.mpr hFc).fderiv_right (by simp [one_add_one_eq_two])
    exact ((ContinuousLinearMap.apply ℝ ℝ ((1 : ℝ), (0 : R3))).contDiff.comp hcd1).comp
      (contDiff_const.prodMk contDiff_id)
  have h_ut_per : IsPeriodic3D (fun x c => deriv (fun s => u s x c) t) := by
    intro x i
    funext c
    -- Show `u s (x + e_i) c = u s x c` on `[t, ∞)` or directly via `HasDerivAt`
    -- Since periodicity holds for all `s ≥ 0`, for `t > 0` it holds on a neighborhood of `t`,
    -- and at `t = 0` we get it by continuity of `s ↦ ∂_t u(s, x)` from `s > 0`.
    have hFc : ∀ q : ℝ × R3, ContDiffAt ℝ 2 (fun r : ℝ × R3 => u r.1 r.2 c) q :=
      fun q => contDiffAt_pi.mp (hns.h_u_c2_spacetime q) c
    have h_pos : ∀ s : ℝ, 0 < s → deriv (fun r => u r (x + basisVec i) c) s =
        deriv (fun r => u r x c) s := by
      intro s hs
      have hev : (fun r => u r (x + basisVec i) c) =ᶠ[𝓝 s] (fun r => u r x c) := by
        filter_upwards [Ioi_mem_nhds hs] with r hr
        exact congrArg (fun v => v c) (hns.h_u_periodic r (le_of_lt hr) x i)
      exact hev.deriv_eq
    have hcont_l : Continuous (fun s => deriv (fun r => u r (x + basisVec i) c) s) := by
      have hfun : (fun s => deriv (fun r => u r (x + basisVec i) c) s) =
          (fun s => fderiv ℝ (fun q : ℝ × R3 => u q.1 q.2 c) (s, x + basisVec i) ((1 : ℝ), (0 : R3))) := by
        funext s; exact timeDeriv_eq_fderiv_prod (fun q => u q.1 q.2 c) hFc s (x + basisVec i)
      rw [hfun]
      have hcd1 : ContDiff ℝ 1 (fderiv ℝ (fun q : ℝ × R3 => u q.1 q.2 c)) :=
        (contDiff_iff_contDiffAt.mpr hFc).fderiv_right (by simp [one_add_one_eq_two])
      exact ((ContinuousLinearMap.apply ℝ ℝ ((1 : ℝ), (0 : R3))).continuous.comp hcd1.continuous).comp
        (continuous_id.prodMk continuous_const)
    have hcont_r : Continuous (fun s => deriv (fun r => u r x c) s) := by
      have hfun : (fun s => deriv (fun r => u r x c) s) =
          (fun s => fderiv ℝ (fun q : ℝ × R3 => u q.1 q.2 c) (s, x) ((1 : ℝ), (0 : R3))) := by
        funext s; exact timeDeriv_eq_fderiv_prod (fun q => u q.1 q.2 c) hFc s x
      rw [hfun]
      have hcd1 : ContDiff ℝ 1 (fderiv ℝ (fun q : ℝ × R3 => u q.1 q.2 c)) :=
        (contDiff_iff_contDiffAt.mpr hFc).fderiv_right (by simp [one_add_one_eq_two])
      exact ((ContinuousLinearMap.apply ℝ ℝ ((1 : ℝ), (0 : R3))).continuous.comp hcd1.continuous).comp
        (continuous_id.prodMk continuous_const)
    rcases eq_or_lt_of_le ht with rfl | ht_pos
    · have h_tend_l : Tendsto (fun s => deriv (fun r => u r (x + basisVec i) c) s) (𝓝[>] 0)
          (𝓝 (deriv (fun r => u r (x + basisVec i) c) 0)) :=
        hcont_l.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
      have h_tend_r : Tendsto (fun s => deriv (fun r => u r x c) s) (𝓝[>] 0)
          (𝓝 (deriv (fun r => u r x c) 0)) :=
        hcont_r.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
      have h_tend_l' : Tendsto (fun s => deriv (fun r => u r (x + basisVec i) c) s) (𝓝[>] 0)
          (𝓝 (deriv (fun r => u r x c) 0)) :=
        h_tend_r.congr' (by filter_upwards [self_mem_nhdsWithin] with s hs; exact (h_pos s hs).symm)
      exact tendsto_nhds_unique h_tend_l h_tend_l'
    · exact h_pos t ht_pos
  have h_ut_div : ∀ x : R3, div3D (fun y c => deriv (fun s => u s y c) t) x = 0 := by
    intro x
    have hF : ∀ c : Fin 3, ∀ q : ℝ × R3, ContDiffAt ℝ 2 (fun r : ℝ × R3 => u r.1 r.2 c) q :=
      fun c q => contDiffAt_pi.mp (hns.h_u_c2_spacetime q) c
    have h_div_pos : ∀ s : ℝ, 0 < s → div3D (fun y c => deriv (fun r => u r y c) s) x = 0 := by
      intro s hs
      unfold div3D
      rw [partial_timeDeriv_comm (fun r => u r.1 r.2 0) (hF 0) s x 0,
          partial_timeDeriv_comm (fun r => u r.1 r.2 1) (hF 1) s x 1,
          partial_timeDeriv_comm (fun r => u r.1 r.2 2) (hF 2) s x 2]
      have hd0 := hasDerivAt_spacePartial_time (fun r => u r.1 r.2 0) (hF 0) s x 0
      have hd1 := hasDerivAt_spacePartial_time (fun r => u r.1 r.2 1) (hF 1) s x 1
      have hd2 := hasDerivAt_spacePartial_time (fun r => u r.1 r.2 2) (hF 2) s x 2
      have hsum : HasDerivAt
          (fun r => partialDerivScalar (fun y => u r y 0) x 0 +
                    partialDerivScalar (fun y => u r y 1) x 1 +
                    partialDerivScalar (fun y => u r y 2) x 2)
          (((fderiv ℝ (fderiv ℝ fun r : ℝ × R3 => u r.1 r.2 0) (s, x)) (1, 0)) (0, basisVec 0) +
           ((fderiv ℝ (fderiv ℝ fun r : ℝ × R3 => u r.1 r.2 1) (s, x)) (1, 0)) (0, basisVec 1) +
           ((fderiv ℝ (fderiv ℝ fun r : ℝ × R3 => u r.1 r.2 2) (s, x)) (1, 0)) (0, basisVec 2)) s :=
        (hd0.add hd1).add hd2
      have hev : (fun r => partialDerivScalar (fun y => u r y 0) x 0 +
          partialDerivScalar (fun y => u r y 1) x 1 +
          partialDerivScalar (fun y => u r y 2) x 2) =ᶠ[𝓝 s] (fun _ => (0 : ℝ)) := by
        filter_upwards [Ioi_mem_nhds hs] with r hr
        exact hns.h_incompressible r (le_of_lt hr) x
      have hzero_d : deriv (fun r => partialDerivScalar (fun y => u r y 0) x 0 +
          partialDerivScalar (fun y => u r y 1) x 1 +
          partialDerivScalar (fun y => u r y 2) x 2) s = 0 := by
        rw [hev.deriv_eq, deriv_const]
      rw [hd0.deriv, hd1.deriv, hd2.deriv]
      linarith [hsum.deriv, hzero_d]
    rcases eq_or_lt_of_le ht with rfl | ht_pos
    · have hcont_div : Continuous (fun s => div3D (fun y c => deriv (fun r => u r y c) s) x) := by
        have h_term : ∀ c : Fin 3, Continuous (fun s =>
            partialDerivScalar (fun y => deriv (fun r => u r y c) s) x c) := by
          intro c
          have hfun : (fun s => partialDerivScalar (fun y => deriv (fun r => u r y c) s) x c) =
              (fun s => fderiv ℝ (fderiv ℝ (fun q : ℝ × R3 => u q.1 q.2 c)) (s, x)
                ((1 : ℝ), (0 : R3)) ((0 : ℝ), basisVec c)) := by
            funext s
            rw [partial_timeDeriv_comm (fun q => u q.1 q.2 c) (hF c) s x c]
            exact (hasDerivAt_spacePartial_time (fun q => u q.1 q.2 c) (hF c) s x c).deriv
          rw [hfun]
          have hcd2 : ContDiff ℝ 2 (fun q : ℝ × R3 => u q.1 q.2 c) := contDiff_iff_contDiffAt.mpr (hF c)
          have hcd1 : ContDiff ℝ 1 (fderiv ℝ (fun q : ℝ × R3 => u q.1 q.2 c)) :=
            hcd2.fderiv_right (by simp [one_add_one_eq_two])
          have hcd0 : ContDiff ℝ 0 (fderiv ℝ (fderiv ℝ (fun q : ℝ × R3 => u q.1 q.2 c))) :=
            hcd1.fderiv_right (by simp)
          have h1 : Continuous (fun q : ℝ × R3 =>
              fderiv ℝ (fderiv ℝ (fun r : ℝ × R3 => u r.1 r.2 c)) q ((1 : ℝ), (0 : R3))) :=
            (ContinuousLinearMap.apply ℝ ((ℝ × R3) →L[ℝ] ℝ) ((1 : ℝ), (0 : R3))).continuous.comp
              hcd0.continuous
          have h2 : Continuous (fun q : ℝ × R3 =>
              fderiv ℝ (fderiv ℝ (fun r : ℝ × R3 => u r.1 r.2 c)) q ((1 : ℝ), (0 : R3))
                ((0 : ℝ), basisVec c)) :=
            (ContinuousLinearMap.apply ℝ ℝ ((0 : ℝ), basisVec c)).continuous.comp h1
          exact h2.comp (continuous_id.prodMk continuous_const)
        unfold div3D
        exact ((h_term 0).add (h_term 1)).add (h_term 2)
      have ht1 : Tendsto (fun s => div3D (fun y c => deriv (fun r => u r y c) s) x) (𝓝[>] 0)
          (𝓝 (div3D (fun y c => deriv (fun r => u r y c) 0) x)) :=
        hcont_div.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
      have ht2 : Tendsto (fun s => div3D (fun y c => deriv (fun r => u r y c) s) x) (𝓝[>] 0) (𝓝 0) :=
        tendsto_const_nhds.congr' (by filter_upwards [self_mem_nhdsWithin] with s hs; exact (h_div_pos s hs).symm)
      exact tendsto_nhds_unique ht1 ht2
    · exact h_div_pos t ht_pos
  exact fourierCoeff3D_solenoidal_ortho h_ut_c1 h_ut_per h_ut_div k

/-- **MAIN THEOREM 2 OF MILESTONE 5A (Exact 3D Spectral Pressure Poisson Equation &
    Modewise Calderón–Zygmund Gradient Bound):**
    For EVERY periodic classical 3D Navier-Stokes solution `(u, p)` and EVERY `k ≠ 0`:
    1. Spectral Pressure Poisson: `fourierCoeff3D (Δp) k = -2πi (k · ((u·∇)u)^∧(k))`.
    2. Exact Spectral Pressure Recovery:
       `p̂(k) = (i / (2π |k|²)) * (k · ((u·∇)u)^∧(k))`.
    3. Exact Hodge–Helmholtz Gradient Projection Identity:
       `(∇p)^∧(k) = -(I - ℙ_k)(((u·∇)u)^∧(k))`.
    4. Exact Modewise Calderón–Zygmund Bound:
       `|(∇p)^∧(k)|² ≤ |((u·∇)u)^∧(k)|²` (`0 sorryAx`). -/
theorem pressure_poisson_and_calderon_zygmund_spectral
    {u : ℝ → R3 → R3} {p : ℝ → R3 → ℝ} {ν : ℝ}
    (hns : IsPeriodicClassicalNS3D_C3 u p ν) {t : ℝ} (ht : t ≥ 0)
    {k : Fin 3 → ℤ} (hk : k ≠ 0) :
    fourierCoeff3D (laplacianScalar (p t)) k =
      (-2 * (Real.pi : ℂ) * Complex.I) * dotC3 (kVecC k) (fourierCoeff3DVec (advection3D (u t)) k) ∧
    fourierCoeff3D (p t) k =
      (Complex.I / (2 * (Real.pi : ℂ) * kNormSqC k)) *
        dotC3 (kVecC k) (fourierCoeff3DVec (advection3D (u t)) k) ∧
    (∀ comp : Fin 3,
      fourierCoeff3DVec (grad3D (p t)) k comp =
        -gradProj3D k (fourierCoeff3DVec (advection3D (u t)) k) comp) ∧
    normSqC3 (fourierCoeff3DVec (grad3D (p t)) k) ≤
      normSqC3 (fourierCoeff3DVec (advection3D (u t)) k) := by
  have hu1 : ContDiff ℝ 1 (u t) := contDiff_one_of_two5 (contDiff_two_of_three5 (hns.h_u_c3_global t ht))
  have hp2 : ContDiff ℝ 2 (p t) := hns.h_p_c2_global t ht
  have hp1 : ContDiff ℝ 1 (p t) := contDiff_one_of_two5 hp2
  have hpp : IsPeriodic3D (p t) := hns.h_p_periodic t ht
  have hm0 := navier_stokes_3d_momentum_spectral hns ht k 0
  have hm1 := navier_stokes_3d_momentum_spectral hns ht k 1
  have hm2 := navier_stokes_3d_momentum_spectral hns ht k 2
  have h_ut_sol := fourierCoeff3D_timeDeriv_solenoidal hns ht k
  have h_u_sol : dotC3 (kVecC k) (fourierCoeff3DVec (u t) k) = 0 :=
    fourierCoeff3D_solenoidal_ortho hu1 (hns.h_u_periodic t ht) (hns.h_incompressible t ht) k
  -- Dot the spectral momentum equation with `k`
  have hk_dot_gp : dotC3 (kVecC k) (fourierCoeff3DVec (grad3D (p t)) k) =
      -dotC3 (kVecC k) (fourierCoeff3DVec (advection3D (u t)) k) := by
    unfold dotC3 kVecC at h_ut_sol h_u_sol ⊢
    linear_combination
      (k 0 : ℂ) * hm0 + (k 1 : ℂ) * hm1 + (k 2 : ℂ) * hm2
      - h_ut_sol
      + (-4 * (Real.pi : ℂ) ^ 2 * (ν : ℂ) * kNormSqC k) * h_u_sol
  have hgp_comp : ∀ i : Fin 3, fourierCoeff3DVec (grad3D (p t)) k i =
      (2 * (Real.pi : ℂ) * Complex.I * (k i : ℂ)) * fourierCoeff3D (p t) k := fun i =>
    fourierCoeff3D_partialDeriv hp1 hpp k i
  have hk_dot_gp_eq : dotC3 (kVecC k) (fourierCoeff3DVec (grad3D (p t)) k) =
      (2 * (Real.pi : ℂ) * Complex.I * kNormSqC k) * fourierCoeff3D (p t) k := by
    unfold dotC3 kVecC kNormSqC
    rw [hgp_comp 0, hgp_comp 1, hgp_comp 2]; ring
  have hpi_ne : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hk2_ne : kNormSqC k ≠ 0 := kNormSqC_ne_zero hk
  have hden_ne : 2 * (Real.pi : ℂ) * kNormSqC k ≠ 0 :=
    mul_ne_zero (mul_ne_zero (by norm_num) hpi_ne) hk2_ne
  -- 1. Pressure Poisson: `Δp^∧(k) = -2πi (k · adv^∧(k))`
  have h_poisson : fourierCoeff3D (laplacianScalar (p t)) k =
      (-2 * (Real.pi : ℂ) * Complex.I) * dotC3 (kVecC k) (fourierCoeff3DVec (advection3D (u t)) k) := by
    rw [fourierCoeff3D_laplacianScalar hp2 hpp k]
    have hstep : (-4 * (Real.pi : ℂ) ^ 2 * kNormSqC k) * fourierCoeff3D (p t) k =
        (2 * (Real.pi : ℂ) * Complex.I) *
          ((2 * (Real.pi : ℂ) * Complex.I * kNormSqC k) * fourierCoeff3D (p t) k) := by
      calc (-4 * (Real.pi : ℂ) ^ 2 * kNormSqC k) * fourierCoeff3D (p t) k
          = (4 * (Real.pi : ℂ) ^ 2 * (-1) * kNormSqC k) * fourierCoeff3D (p t) k := by ring
        _ = (4 * (Real.pi : ℂ) ^ 2 * Complex.I ^ 2 * kNormSqC k) * fourierCoeff3D (p t) k := by
            rw [Complex.I_sq]
        _ = (2 * (Real.pi : ℂ) * Complex.I) *
              ((2 * (Real.pi : ℂ) * Complex.I * kNormSqC k) * fourierCoeff3D (p t) k) := by ring
    change (-4 * (Real.pi : ℂ) ^ 2 * kNormSqC k) * fourierCoeff3D (p t) k = _
    rw [hstep, ← hk_dot_gp_eq, hk_dot_gp]
    ring
  -- 2. Exact pressure recovery `p̂(k)`
  have h_p_hat : fourierCoeff3D (p t) k =
      (Complex.I / (2 * (Real.pi : ℂ) * kNormSqC k)) *
        dotC3 (kVecC k) (fourierCoeff3DVec (advection3D (u t)) k) := by
    have hmul : (2 * (Real.pi : ℂ) * Complex.I * kNormSqC k) * fourierCoeff3D (p t) k =
        -dotC3 (kVecC k) (fourierCoeff3DVec (advection3D (u t)) k) := by
      rw [← hk_dot_gp_eq, hk_dot_gp]
    have hfull_ne : 2 * (Real.pi : ℂ) * Complex.I * kNormSqC k ≠ 0 :=
      mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) hpi_ne) Complex.I_ne_zero) hk2_ne
    apply mul_left_cancel₀ hfull_ne
    rw [hmul]
    field_simp [hden_ne]
    rw [Complex.I_sq]; ring
  -- 3. Gradient projection identity `(∇p)^∧(k) = -(I - ℙ_k)(adv^∧(k))`
  have h_gp_proj : ∀ comp : Fin 3,
      fourierCoeff3DVec (grad3D (p t)) k comp =
        -gradProj3D k (fourierCoeff3DVec (advection3D (u t)) k) comp := by
    intro comp
    rw [hgp_comp comp, h_p_hat]
    unfold gradProj3D
    simp only [hk, ↓reduceIte]
    field_simp [hden_ne, hk2_ne]
    rw [Complex.I_sq]; ring
  -- 4. Calderón–Zygmund modewise bound `|(∇p)^∧(k)|² ≤ |adv^∧(k)|²`
  have h_cz : normSqC3 (fourierCoeff3DVec (grad3D (p t)) k) ≤
      normSqC3 (fourierCoeff3DVec (advection3D (u t)) k) := by
    have hnorm_eq : normSqC3 (fourierCoeff3DVec (grad3D (p t)) k) =
        normSqC3 (gradProj3D k (fourierCoeff3DVec (advection3D (u t)) k)) := by
      unfold normSqC3
      rw [h_gp_proj 0, h_gp_proj 1, h_gp_proj 2, norm_neg, norm_neg, norm_neg]
    have hpyth := lerayProj3D_pythagoras k (fourierCoeff3DVec (advection3D (u t)) k)
    have hnn := normSqC3_nonneg (lerayProj3D k (fourierCoeff3DVec (advection3D (u t)) k))
    linarith
  exact ⟨h_poisson, h_p_hat, h_gp_proj, h_cz⟩

/-- **MAIN THEOREM 3 OF MILESTONE 5A (Pressure-Eliminated Leray-Projected Spectral 3D Navier–Stokes):**
    Applying `ℙ_k` to the spectral momentum equation eliminates the pressure gradient identically
    for EVERY `k ∈ ℤ³` and `comp ∈ {0, 1, 2}`:
      `(∂_t u)^∧(k) + ℙ_k(((u·∇)u)^∧(k)) + 4π² ν |k|² û(k) = 0` (`0 sorryAx`). -/
theorem navier_stokes_3d_leray_projected_spectral
    {u : ℝ → R3 → R3} {p : ℝ → R3 → ℝ} {ν : ℝ}
    (hns : IsPeriodicClassicalNS3D_C3 u p ν) {t : ℝ} (ht : t ≥ 0)
    (k : Fin 3 → ℤ) (comp : Fin 3) :
    fourierCoeff3DVec (fun x c => deriv (fun s => u s x c) t) k comp +
      lerayProj3D k (fourierCoeff3DVec (advection3D (u t)) k) comp +
      (4 * (Real.pi : ℂ) ^ 2 * (ν : ℂ) * kNormSqC k) * fourierCoeff3DVec (u t) k comp = 0 := by
  have hu1 : ContDiff ℝ 1 (u t) := contDiff_one_of_two5 (contDiff_two_of_three5 (hns.h_u_c3_global t ht))
  have hp1 : ContDiff ℝ 1 (p t) := contDiff_one_of_two5 (hns.h_p_c2_global t ht)
  have h_ut_sol := fourierCoeff3D_timeDeriv_solenoidal hns ht k
  have h_u_sol : dotC3 (kVecC k) (fourierCoeff3DVec (u t) k) = 0 :=
    fourierCoeff3D_solenoidal_ortho hu1 (hns.h_u_periodic t ht) (hns.h_incompressible t ht) k
  have h_vec_eq :
      (fun c => fourierCoeff3DVec (fun x j => deriv (fun s => u s x j) t) k c +
        fourierCoeff3DVec (advection3D (u t)) k c +
        fourierCoeff3DVec (grad3D (p t)) k c) =
      (fun c => (-4 * (Real.pi : ℂ) ^ 2 * (ν : ℂ) * kNormSqC k) * fourierCoeff3DVec (u t) k c) := by
    funext c; exact navier_stokes_3d_momentum_spectral hns ht k c
  have hproj := congrArg (fun v => lerayProj3D k v comp) h_vec_eq
  rw [lerayProj3D_add k (fun c => fourierCoeff3DVec (fun x j => deriv (fun s => u s x j) t) k c +
        fourierCoeff3DVec (advection3D (u t)) k c) (fourierCoeff3DVec (grad3D (p t)) k) comp,
      lerayProj3D_add k (fourierCoeff3DVec (fun x j => deriv (fun s => u s x j) t) k)
        (fourierCoeff3DVec (advection3D (u t)) k) comp,
      lerayProj3D_smul k (-4 * (Real.pi : ℂ) ^ 2 * (ν : ℂ) * kNormSqC k)
        (fourierCoeff3DVec (u t) k) comp,
      lerayProj3D_eq_self_of_solenoidal h_ut_sol comp,
      lerayProj3D_eq_self_of_solenoidal h_u_sol comp,
      lerayProj3D_grad3D_eq_zero hp1 (hns.h_p_periodic t ht) k comp,
      add_zero] at hproj
  linear_combination hproj

-- ============================================================================
-- SECTION 5: AXIOM AUDIT TRAIL (0 sorryAx)
-- ============================================================================

#print axioms fourierCoeff3DVec_curl3D
#print axioms biot_savart_3d_spectral
#print axioms lerayProj3D_solenoidal
#print axioms lerayProj3D_idem
#print axioms lerayProj3D_grad3D_eq_zero
#print axioms lerayProj3D_pythagoras
#print axioms navier_stokes_3d_momentum_spectral
#print axioms fourierCoeff3D_timeDeriv_solenoidal
#print axioms pressure_poisson_and_calderon_zygmund_spectral
#print axioms navier_stokes_3d_leray_projected_spectral

end GarrySpectralOperators3D