import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Abel
import SpectralAlgebraTorus3D

/-!
# GARRYULT v4.0.0 — Milestone 6A (Stage 2): Solenoidal Vector `H²(𝕋³; ℝ³)`,
# Spectral Leray–Helmholtz Projector `ℙ_k`, Heat-Smoothed Navier–Stokes Bilinear
# Operator (`C = 848/(ντ)`, Quadratic Lipschitz `1696/(ντ)`) & Reverse Spectral
# Synthesis `H²(𝕋³) ↪ C⁰(𝕋³)` (`0 sorryAx`)
-/

namespace GarrySpectralBilinear3D

open MeasureTheory Filter Topology GarryReal3DCalculus GarryVorticity3D
  GarryLerayTorus3D GarryLerayEnergyLaw3D GarryPoincareSobolev3D
  GarryFourierSpectral3D GarrySpectralOperators3D GarryParsevalSobolev3D
  GarrySobolevEmbedding3D GarrySpectralAlgebra3D

-- ============================================================================
-- SECTION 1: VECTOR `H²(𝕋³; ℝ³)` SPACE, REAL SYMMETRY & SOLENOIDALITY
-- ============================================================================

/-- Complex 3D Fourier vector sequence `k ↦ û(k) ∈ ℂ³`. -/
abbrev VecSeq3D := (Fin 3 → ℤ) → (Fin 3 → ℂ)

/-- Squared Euclidean norm on `ℂ³`. -/
noncomputable def vecNormSqC (v : Fin 3 → ℂ) : ℝ :=
  ‖v 0‖ ^ 2 + ‖v 1‖ ^ 2 + ‖v 2‖ ^ 2

/-- Membership in vector `H²(𝕋³; ℂ³)`. -/
def InH2Vec (u : VecSeq3D) : Prop :=
  ∀ c : Fin 3, InH2Seq (fun k => u k c)

/-- Squared vector `H²(𝕋³)` norm `∑_{c=0}^2 ∑' k, (1 + |k|⁴) ‖û_c(k)‖²`. -/
noncomputable def h2VecNormSq (u : VecSeq3D) : ℝ :=
  h2NormSq (fun k => u k 0) + h2NormSq (fun k => u k 1) + h2NormSq (fun k => u k 2)

/-- Reality (Hermitian) symmetry `conj(û(k)) = û(-k)`. -/
def IsRealSymm (u : VecSeq3D) : Prop :=
  ∀ (k : Fin 3 → ℤ) (c : Fin 3), starRingEnd ℂ (u k c) = u (-k) c

/-- Spectral divergence-free condition `k · û(k) = 0`. -/
def IsSolenoidal (u : VecSeq3D) : Prop :=
  ∀ k : Fin 3 → ℤ,
    (k 0 : ℂ) * u k 0 + (k 1 : ℂ) * u k 1 + (k 2 : ℂ) * u k 2 = 0

private theorem kNormSq_neg_6a2 (k : Fin 3 → ℤ) : kNormSq (-k) = kNormSq k := by
  unfold kNormSq
  simp only [Pi.neg_apply, Int.cast_neg, neg_sq]

private theorem heatMultiplier3D_neg (ν τ : ℝ) (k : Fin 3 → ℤ) :
    heatMultiplier3D ν τ (-k) = heatMultiplier3D ν τ k := by
  unfold heatMultiplier3D
  rw [kNormSq_neg_6a2]

theorem vecNormSqC_nonneg (v : Fin 3 → ℂ) : 0 ≤ vecNormSqC v := by
  unfold vecNormSqC; positivity

theorem h2VecNormSq_nonneg (u : VecSeq3D) : 0 ≤ h2VecNormSq u := by
  unfold h2VecNormSq
  linarith [h2NormSq_nonneg (fun k => u k 0),
            h2NormSq_nonneg (fun k => u k 1),
            h2NormSq_nonneg (fun k => u k 2)]

theorem hasSum_h2VecNormSq {u : VecSeq3D} (hu : InH2Vec u) :
    HasSum (fun k : Fin 3 → ℤ => h2Weight k * vecNormSqC (u k)) (h2VecNormSq u) := by
  have hsum := (((hu 0).hasSum).add ((hu 1).hasSum)).add ((hu 2).hasSum)
  have heq : (fun k : Fin 3 → ℤ =>
      h2Weight k * ‖u k 0‖ ^ 2 + h2Weight k * ‖u k 1‖ ^ 2 + h2Weight k * ‖u k 2‖ ^ 2) =
      (fun k => h2Weight k * vecNormSqC (u k)) := by
    funext k; unfold vecNormSqC; ring
  rwa [heq] at hsum

theorem inH2Vec_add {u v : VecSeq3D} (hu : InH2Vec u) (hv : InH2Vec v) :
    InH2Vec (fun k c => u k c + v k c) ∧
    h2VecNormSq (fun k c => u k c + v k c) ≤ 2 * h2VecNormSq u + 2 * h2VecNormSq v := by
  have h0 := inH2Seq_add (hu 0) (hv 0)
  have h1 := inH2Seq_add (hu 1) (hv 1)
  have h2 := inH2Seq_add (hu 2) (hv 2)
  refine ⟨fun c => ?_, ?_⟩
  · fin_cases c
    · exact h0.1
    · exact h1.1
    · exact h2.1
  · unfold h2VecNormSq
    linarith [h0.2, h1.2, h2.2]

theorem inH2Vec_sub {u v : VecSeq3D} (hu : InH2Vec u) (hv : InH2Vec v) :
    InH2Vec (fun k c => u k c - v k c) ∧
    h2VecNormSq (fun k c => u k c - v k c) ≤ 2 * h2VecNormSq u + 2 * h2VecNormSq v := by
  have h0 := inH2Seq_sub (hu 0) (hv 0)
  have h1 := inH2Seq_sub (hu 1) (hv 1)
  have h2 := inH2Seq_sub (hu 2) (hv 2)
  refine ⟨fun c => ?_, ?_⟩
  · fin_cases c
    · exact h0.1
    · exact h1.1
    · exact h2.1
  · unfold h2VecNormSq
    linarith [h0.2, h1.2, h2.2]

-- ============================================================================
-- SECTION 2: SPECTRAL LERAY–HELMHOLTZ PROJECTOR `ℙ_k`
-- ============================================================================

/-- Spectral Leray–Helmholtz orthogonal projection onto `{v ∈ ℂ³ : k · v = 0}`. -/
noncomputable def lerayProj6A (k : Fin 3 → ℤ) (v : Fin 3 → ℂ) : Fin 3 → ℂ :=
  if k = 0 then v
  else fun c =>
    v c - (((k 0 : ℂ) * v 0 + (k 1 : ℂ) * v 1 + (k 2 : ℂ) * v 2) /
      ((kNormSq k : ℝ) : ℂ)) * (k c : ℂ)

/-- **THEOREM 1 OF MILESTONE 6A-2:** `k · ℙ_k v = 0` for every mode `k ∈ ℤ³` (`0 sorryAx`). -/
theorem lerayProj6A_solenoidal (k : Fin 3 → ℤ) (v : Fin 3 → ℂ) :
    (k 0 : ℂ) * lerayProj6A k v 0 + (k 1 : ℂ) * lerayProj6A k v 1 +
      (k 2 : ℂ) * lerayProj6A k v 2 = 0 := by
  unfold lerayProj6A
  by_cases hk : k = 0
  · subst hk; simp
  · simp only [hk, ↓reduceIte]
    have hd_pos : 0 < kNormSq k := kNormSq_pos_of_ne_zero hk
    have hd_ne : ((kNormSq k : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hd_pos)
    have hksum : (k 0 : ℂ) ^ 2 + (k 1 : ℂ) ^ 2 + (k 2 : ℂ) ^ 2 = ((kNormSq k : ℝ) : ℂ) := by
      unfold kNormSq; push_cast; ring
    have hlin : (k 0 : ℂ) * (v 0 - ((k 0 : ℂ) * v 0 + (k 1 : ℂ) * v 1 + (k 2 : ℂ) * v 2) /
          ((kNormSq k : ℝ) : ℂ) * (k 0 : ℂ)) +
        (k 1 : ℂ) * (v 1 - ((k 0 : ℂ) * v 0 + (k 1 : ℂ) * v 1 + (k 2 : ℂ) * v 2) /
          ((kNormSq k : ℝ) : ℂ) * (k 1 : ℂ)) +
        (k 2 : ℂ) * (v 2 - ((k 0 : ℂ) * v 0 + (k 1 : ℂ) * v 1 + (k 2 : ℂ) * v 2) /
          ((kNormSq k : ℝ) : ℂ) * (k 2 : ℂ)) =
        ((k 0 : ℂ) * v 0 + (k 1 : ℂ) * v 1 + (k 2 : ℂ) * v 2) *
          (1 - ((k 0 : ℂ) ^ 2 + (k 1 : ℂ) ^ 2 + (k 2 : ℂ) ^ 2) / ((kNormSq k : ℝ) : ℂ)) := by
      ring
    rw [hlin, hksum, div_self hd_ne, sub_self, mul_zero]

/-- **THEOREM 2 OF MILESTONE 6A-2:** Orthogonal contraction `‖ℙ_k v‖² ≤ ‖v‖²` (`0 sorryAx`). -/
theorem lerayProj6A_normSq_le (k : Fin 3 → ℤ) (v : Fin 3 → ℂ) :
    vecNormSqC (lerayProj6A k v) ≤ vecNormSqC v := by
  unfold lerayProj6A
  by_cases hk : k = 0
  · simp [hk]
  · simp only [hk, ↓reduceIte]
    let d : ℝ := kNormSq k
    have hd_pos : 0 < d := kNormSq_pos_of_ne_zero hk
    have hd_ne : ((d : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hd_pos)
    let s : ℂ := (k 0 : ℂ) * v 0 + (k 1 : ℂ) * v 1 + (k 2 : ℂ) * v 2
    let α : ℂ := s / (d : ℂ)
    have hαd : α * (d : ℂ) = s := div_mul_cancel₀ s hd_ne
    have hre : α.re * d = s.re := by
      simpa [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im] using congrArg Complex.re hαd
    have him : α.im * d = s.im := by
      simpa [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im] using congrArg Complex.im hαd
    have hk_re : ∀ c : Fin 3, ((k c : ℂ)).re = (k c : ℝ) := fun c => by
      rw [← Complex.ofReal_intCast, Complex.ofReal_re]
    have hk_im : ∀ c : Fin 3, ((k c : ℂ)).im = 0 := fun c => by
      rw [← Complex.ofReal_intCast, Complex.ofReal_im]
    have hs_re : s.re = (k 0 : ℝ) * (v 0).re + (k 1 : ℝ) * (v 1).re + (k 2 : ℝ) * (v 2).re := by
      dsimp only [s]
      simp only [Complex.add_re, Complex.mul_re, hk_re, hk_im, zero_mul, sub_zero]
    have hs_im : s.im = (k 0 : ℝ) * (v 0).im + (k 1 : ℝ) * (v 1).im + (k 2 : ℝ) * (v 2).im := by
      dsimp only [s]
      simp only [Complex.add_im, Complex.mul_im, hk_re, hk_im, zero_mul, add_zero]
    have hcomp : ∀ c : Fin 3, ‖v c - α * (k c : ℂ)‖ ^ 2 =
        ((v c).re - α.re * (k c : ℝ)) ^ 2 + ((v c).im - α.im * (k c : ℝ)) ^ 2 := fun c => by
      rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
      simp only [Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im,
        hk_re, hk_im, mul_zero, sub_zero]
      ring
    have hvcomp : ∀ c : Fin 3, ‖v c‖ ^ 2 = (v c).re ^ 2 + (v c).im ^ 2 := fun c => by
      rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]; ring
    have hd_def : d = (k 0 : ℝ) ^ 2 + (k 1 : ℝ) ^ 2 + (k 2 : ℝ) ^ 2 := rfl
    change vecNormSqC (fun c => v c - α * (k c : ℂ)) ≤ vecNormSqC v
    unfold vecNormSqC
    rw [hcomp 0, hcomp 1, hcomp 2, hvcomp 0, hvcomp 1, hvcomp 2]
    have hdiff :
        (((v 0).re - α.re * (k 0 : ℝ)) ^ 2 + ((v 0).im - α.im * (k 0 : ℝ)) ^ 2) +
        (((v 1).re - α.re * (k 1 : ℝ)) ^ 2 + ((v 1).im - α.im * (k 1 : ℝ)) ^ 2) +
        (((v 2).re - α.re * (k 2 : ℝ)) ^ 2 + ((v 2).im - α.im * (k 2 : ℝ)) ^ 2) =
        (((v 0).re ^ 2 + (v 0).im ^ 2) + ((v 1).re ^ 2 + (v 1).im ^ 2) +
         ((v 2).re ^ 2 + (v 2).im ^ 2)) - (α.re ^ 2 + α.im ^ 2) * d := by
      have h1 :
          (((v 0).re - α.re * (k 0 : ℝ)) ^ 2 + ((v 0).im - α.im * (k 0 : ℝ)) ^ 2) +
          (((v 1).re - α.re * (k 1 : ℝ)) ^ 2 + ((v 1).im - α.im * (k 1 : ℝ)) ^ 2) +
          (((v 2).re - α.re * (k 2 : ℝ)) ^ 2 + ((v 2).im - α.im * (k 2 : ℝ)) ^ 2) =
          (((v 0).re ^ 2 + (v 0).im ^ 2) + ((v 1).re ^ 2 + (v 1).im ^ 2) +
           ((v 2).re ^ 2 + (v 2).im ^ 2)) -
          2 * α.re * ((k 0 : ℝ) * (v 0).re + (k 1 : ℝ) * (v 1).re + (k 2 : ℝ) * (v 2).re) -
          2 * α.im * ((k 0 : ℝ) * (v 0).im + (k 1 : ℝ) * (v 1).im + (k 2 : ℝ) * (v 2).im) +
          (α.re ^ 2 + α.im ^ 2) * ((k 0 : ℝ) ^ 2 + (k 1 : ℝ) ^ 2 + (k 2 : ℝ) ^ 2) := by
        ring
      rw [h1, ← hs_re, ← hs_im, ← hd_def, ← hre, ← him]
      ring
    rw [hdiff]
    have hnn : 0 ≤ (α.re ^ 2 + α.im ^ 2) * d := mul_nonneg (by positivity) (le_of_lt hd_pos)
    linarith

theorem lerayProj6A_conj (k : Fin 3 → ℤ) (v : Fin 3 → ℂ) (c : Fin 3) :
    starRingEnd ℂ (lerayProj6A k v c) = lerayProj6A (-k) (fun j => starRingEnd ℂ (v j)) c := by
  unfold lerayProj6A
  by_cases hk : k = 0
  · subst hk; simp
  · have hnk : -k ≠ 0 := neg_ne_zero.mpr hk
    simp only [hk, hnk, ↓reduceIte, Pi.neg_apply, kNormSq_neg_6a2]
    have hint : ∀ n : ℤ, starRingEnd ℂ (n : ℂ) = (n : ℂ) := fun n => by
      rw [← Complex.ofReal_intCast, Complex.conj_ofReal]
    simp only [map_sub, map_mul, map_div₀, map_add, Complex.conj_ofReal, hint, Int.cast_neg]
    ring

theorem lerayProj6A_add (k : Fin 3 → ℤ) (v w : Fin 3 → ℂ) (c : Fin 3) :
    lerayProj6A k (fun j => v j + w j) c = lerayProj6A k v c + lerayProj6A k w c := by
  unfold lerayProj6A
  by_cases hk : k = 0
  · simp [hk]
  · simp only [hk, ↓reduceIte]; ring

theorem lerayProj6A_sub (k : Fin 3 → ℤ) (v w : Fin 3 → ℂ) (c : Fin 3) :
    lerayProj6A k (fun j => v j - w j) c = lerayProj6A k v c - lerayProj6A k w c := by
  unfold lerayProj6A
  by_cases hk : k = 0
  · simp [hk]
  · simp only [hk, ↓reduceIte]; ring

-- ============================================================================
-- SECTION 3: HEAT-SMOOTHED NAVIER–STOKES BILINEAR OPERATOR & LIPSCHITZ BOUND
-- ============================================================================

/-- Unprojected divergence-form nonlinear flux `F(u, v)_k(c) = 2π i ∑_{j=0}^2 k_j (u_j * v_c)(k)`. -/
noncomputable def nsFlux6A (u v : VecSeq3D) (k : Fin 3 → ℤ) (c : Fin 3) : ℂ :=
  2 * (Real.pi : ℂ) * Complex.I *
    ((k 0 : ℂ) * conv3D (fun m => u m 0) (fun m => v m c) k +
     (k 1 : ℂ) * conv3D (fun m => u m 1) (fun m => v m c) k +
     (k 2 : ℂ) * conv3D (fun m => u m 2) (fun m => v m c) k)

/-- Projected Navier–Stokes bilinear term `B(u, v)_k = -ℙ_k (∇ · (u ⊗ v))_k`. -/
noncomputable def nsBilinear6A (u v : VecSeq3D) (k : Fin 3 → ℤ) : Fin 3 → ℂ :=
  fun c => -lerayProj6A k (nsFlux6A u v k) c

/-- Heat-smoothed bilinear operator `S_τ(u, v)_k = e^{-4π²ν|k|²τ} B(u, v)_k`. -/
noncomputable def heatSmoothedBilinear6A (ν τ : ℝ) (u v : VecSeq3D) (k : Fin 3 → ℤ) : Fin 3 → ℂ :=
  fun c => (heatMultiplier3D ν τ k : ℂ) * nsBilinear6A u v k c

theorem nsBilinear6A_zero (u v : VecSeq3D) (c : Fin 3) :
    nsBilinear6A u v 0 c = 0 := by
  unfold nsBilinear6A lerayProj6A nsFlux6A; simp

theorem heatSmoothedBilinear6A_zero (ν τ : ℝ) (u v : VecSeq3D) (c : Fin 3) :
    heatSmoothedBilinear6A ν τ u v 0 c = 0 := by
  unfold heatSmoothedBilinear6A
  rw [nsBilinear6A_zero, mul_zero]

theorem nsBilinear6A_solenoidal (u v : VecSeq3D) :
    IsSolenoidal (nsBilinear6A u v) := by
  intro k
  unfold nsBilinear6A
  have h := lerayProj6A_solenoidal k (nsFlux6A u v k)
  have heq : (k 0 : ℂ) * -lerayProj6A k (nsFlux6A u v k) 0 +
      (k 1 : ℂ) * -lerayProj6A k (nsFlux6A u v k) 1 +
      (k 2 : ℂ) * -lerayProj6A k (nsFlux6A u v k) 2 =
      -((k 0 : ℂ) * lerayProj6A k (nsFlux6A u v k) 0 +
        (k 1 : ℂ) * lerayProj6A k (nsFlux6A u v k) 1 +
        (k 2 : ℂ) * lerayProj6A k (nsFlux6A u v k) 2) := by ring
  rw [heq, h, neg_zero]

theorem heatSmoothedBilinear6A_solenoidal (ν τ : ℝ) (u v : VecSeq3D) :
    IsSolenoidal (heatSmoothedBilinear6A ν τ u v) := by
  intro k
  unfold heatSmoothedBilinear6A
  have h := nsBilinear6A_solenoidal u v k
  have heq : (k 0 : ℂ) * ((heatMultiplier3D ν τ k : ℂ) * nsBilinear6A u v k 0) +
      (k 1 : ℂ) * ((heatMultiplier3D ν τ k : ℂ) * nsBilinear6A u v k 1) +
      (k 2 : ℂ) * ((heatMultiplier3D ν τ k : ℂ) * nsBilinear6A u v k 2) =
      (heatMultiplier3D ν τ k : ℂ) *
        ((k 0 : ℂ) * nsBilinear6A u v k 0 + (k 1 : ℂ) * nsBilinear6A u v k 1 +
         (k 2 : ℂ) * nsBilinear6A u v k 2) := by ring
  rw [heq, h, mul_zero]

private theorem conv3D_conj_of_realSymm {a b : (Fin 3 → ℤ) → ℂ}
    (ha : InH2Seq a) (hb : InH2Seq b)
    (hsa : ∀ k, starRingEnd ℂ (a k) = a (-k))
    (hsb : ∀ k, starRingEnd ℂ (b k) = b (-k)) (k : Fin 3 → ℤ) :
    starRingEnd ℂ (conv3D a b k) = conv3D a b (-k) := by
  unfold conv3D
  have hsumm := conv3D_summable ha hb k
  have hconj : starRingEnd ℂ (∑' j : Fin 3 → ℤ, a j * b (k - j)) =
      ∑' j : Fin 3 → ℤ, starRingEnd ℂ (a j * b (k - j)) :=
    (Complex.conjCLE.toContinuousLinearMap.hasSum hsumm.hasSum).tsum_eq.symm
  have hreidx : (∑' j : Fin 3 → ℤ, a (-j) * b (-k - (-j))) =
      ∑' j : Fin 3 → ℤ, a j * b (-k - j) :=
    Equiv.tsum_eq (Equiv.neg (Fin 3 → ℤ)) (fun j => a j * b (-k - j))
  rw [hconj, ← hreidx]
  refine tsum_congr fun j => ?_
  rw [map_mul, hsa j, hsb (k - j)]
  have hsub : -(k - j) = -k - (-j) := by abel
  rw [hsub]

/-- **THEOREM 3 OF MILESTONE 6A-2:** `heatSmoothedBilinear6A` preserves reality symmetry (`0 sorryAx`). -/
theorem heatSmoothedBilinear6A_realSymm (ν τ : ℝ) {u v : VecSeq3D}
    (hu : InH2Vec u) (hv : InH2Vec v)
    (hsu : IsRealSymm u) (hsv : IsRealSymm v) :
    IsRealSymm (heatSmoothedBilinear6A ν τ u v) := by
  have hflux : ∀ (k : Fin 3 → ℤ) (c : Fin 3),
      starRingEnd ℂ (nsFlux6A u v k c) = nsFlux6A u v (-k) c := by
    intro k c
    unfold nsFlux6A
    have hint : ∀ n : ℤ, starRingEnd ℂ (n : ℂ) = (n : ℂ) := fun n => by
      rw [← Complex.ofReal_intCast, Complex.conj_ofReal]
    simp only [map_mul, map_add, map_ofNat, Complex.conj_ofReal, Complex.conj_I, hint,
      Pi.neg_apply, Int.cast_neg]
    rw [conv3D_conj_of_realSymm (hu 0) (hv c) (fun m => hsu m 0) (fun m => hsv m c) k,
        conv3D_conj_of_realSymm (hu 1) (hv c) (fun m => hsu m 1) (fun m => hsv m c) k,
        conv3D_conj_of_realSymm (hu 2) (hv c) (fun m => hsu m 2) (fun m => hsv m c) k]
    ring
  intro k c
  unfold heatSmoothedBilinear6A nsBilinear6A
  rw [map_mul, Complex.conj_ofReal, heatMultiplier3D_neg, map_neg, lerayProj6A_conj]
  have hf_eq : (fun j => starRingEnd ℂ (nsFlux6A u v k j)) = nsFlux6A u v (-k) :=
    funext fun j => hflux k j
  rw [hf_eq]

private theorem norm_linear_comb_sq_le (k : Fin 3 → ℤ) (z : Fin 3 → ℂ) :
    ‖(k 0 : ℂ) * z 0 + (k 1 : ℂ) * z 1 + (k 2 : ℂ) * z 2‖ ^ 2 ≤
      kNormSq k * (‖z 0‖ ^ 2 + ‖z 1‖ ^ 2 + ‖z 2‖ ^ 2) := by
  have hk : ∀ i : Fin 3, ‖(k i : ℂ)‖ = |(k i : ℝ)| := fun i => by
    rw [← Complex.ofReal_intCast, Complex.norm_real, Real.norm_eq_abs]
  have htri : ‖(k 0 : ℂ) * z 0 + (k 1 : ℂ) * z 1 + (k 2 : ℂ) * z 2‖ ≤
      |(k 0 : ℝ)| * ‖z 0‖ + |(k 1 : ℝ)| * ‖z 1‖ + |(k 2 : ℝ)| * ‖z 2‖ := by
    calc ‖(k 0 : ℂ) * z 0 + (k 1 : ℂ) * z 1 + (k 2 : ℂ) * z 2‖
        ≤ ‖(k 0 : ℂ) * z 0 + (k 1 : ℂ) * z 1‖ + ‖(k 2 : ℂ) * z 2‖ := norm_add_le _ _
      _ ≤ ‖(k 0 : ℂ) * z 0‖ + ‖(k 1 : ℂ) * z 1‖ + ‖(k 2 : ℂ) * z 2‖ :=
          add_le_add (norm_add_le _ _) le_rfl
      _ = |(k 0 : ℝ)| * ‖z 0‖ + |(k 1 : ℝ)| * ‖z 1‖ + |(k 2 : ℝ)| * ‖z 2‖ := by
          rw [norm_mul, norm_mul, norm_mul, hk 0, hk 1, hk 2]
  have hnn : 0 ≤ ‖(k 0 : ℂ) * z 0 + (k 1 : ℂ) * z 1 + (k 2 : ℂ) * z 2‖ := norm_nonneg _
  have hsq : ‖(k 0 : ℂ) * z 0 + (k 1 : ℂ) * z 1 + (k 2 : ℂ) * z 2‖ ^ 2 ≤
      (|(k 0 : ℝ)| * ‖z 0‖ + |(k 1 : ℝ)| * ‖z 1‖ + |(k 2 : ℝ)| * ‖z 2‖) ^ 2 := by nlinarith
  have hcs : (|(k 0 : ℝ)| * ‖z 0‖ + |(k 1 : ℝ)| * ‖z 1‖ + |(k 2 : ℝ)| * ‖z 2‖) ^ 2 ≤
      ((k 0 : ℝ) ^ 2 + (k 1 : ℝ) ^ 2 + (k 2 : ℝ) ^ 2) * (‖z 0‖ ^ 2 + ‖z 1‖ ^ 2 + ‖z 2‖ ^ 2) := by
    have h0 : |(k 0 : ℝ)| ^ 2 = (k 0 : ℝ) ^ 2 := sq_abs _
    have h1 : |(k 1 : ℝ)| ^ 2 = (k 1 : ℝ) ^ 2 := sq_abs _
    have h2 : |(k 2 : ℝ)| ^ 2 = (k 2 : ℝ) ^ 2 := sq_abs _
    nlinarith [sq_nonneg (|(k 0 : ℝ)| * ‖z 1‖ - |(k 1 : ℝ)| * ‖z 0‖),
               sq_nonneg (|(k 0 : ℝ)| * ‖z 2‖ - |(k 2 : ℝ)| * ‖z 0‖),
               sq_nonneg (|(k 1 : ℝ)| * ‖z 2‖ - |(k 2 : ℝ)| * ‖z 1‖), h0, h1, h2]
  unfold kNormSq
  exact le_trans hsq hcs

private theorem nsBilinear6A_normSq_le (u v : VecSeq3D) (k : Fin 3 → ℤ) :
    vecNormSqC (nsBilinear6A u v k) ≤
      4 * Real.pi ^ 2 * kNormSq k *
        ((‖conv3D (fun m => u m 0) (fun m => v m 0) k‖ ^ 2 +
          ‖conv3D (fun m => u m 1) (fun m => v m 0) k‖ ^ 2 +
          ‖conv3D (fun m => u m 2) (fun m => v m 0) k‖ ^ 2) +
         (‖conv3D (fun m => u m 0) (fun m => v m 1) k‖ ^ 2 +
          ‖conv3D (fun m => u m 1) (fun m => v m 1) k‖ ^ 2 +
          ‖conv3D (fun m => u m 2) (fun m => v m 1) k‖ ^ 2) +
         (‖conv3D (fun m => u m 0) (fun m => v m 2) k‖ ^ 2 +
          ‖conv3D (fun m => u m 1) (fun m => v m 2) k‖ ^ 2 +
          ‖conv3D (fun m => u m 2) (fun m => v m 2) k‖ ^ 2)) := by
  have hneg : vecNormSqC (nsBilinear6A u v k) = vecNormSqC (lerayProj6A k (nsFlux6A u v k)) := by
    unfold vecNormSqC nsBilinear6A
    simp only [norm_neg]
  rw [hneg]
  have hproj := lerayProj6A_normSq_le k (nsFlux6A u v k)
  have h2pi : ‖(2 : ℂ) * (Real.pi : ℂ) * Complex.I‖ ^ 2 = 4 * Real.pi ^ 2 := by
    have h2 : ‖(2 : ℂ)‖ = 2 := by norm_num
    rw [norm_mul, norm_mul, Complex.norm_I, mul_one, h2,
        Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
    ring
  have hflux_c : ∀ c : Fin 3, ‖nsFlux6A u v k c‖ ^ 2 ≤
      4 * Real.pi ^ 2 * kNormSq k *
        (‖conv3D (fun m => u m 0) (fun m => v m c) k‖ ^ 2 +
         ‖conv3D (fun m => u m 1) (fun m => v m c) k‖ ^ 2 +
         ‖conv3D (fun m => u m 2) (fun m => v m c) k‖ ^ 2) := by
    intro c
    unfold nsFlux6A
    rw [norm_mul, mul_pow, h2pi]
    have hcs := norm_linear_comb_sq_le k (fun j => conv3D (fun m => u m j) (fun m => v m c) k)
    have hpi_nn : 0 ≤ 4 * Real.pi ^ 2 := by positivity
    nlinarith
  unfold vecNormSqC at hproj ⊢
  rw [mul_add, mul_add]
  linarith [hproj, hflux_c 0, hflux_c 1, hflux_c 2]

/-- **MAIN THEOREM 4 OF MILESTONE 6A-2 (Heat-Smoothed Bilinear `H²` Estimate):**
    For all `ν > 0, τ > 0` and `u, v ∈ H²(𝕋³; ℂ³)`:
    `‖e^{ντΔ} B(u, v)‖²_{H²} ≤ (848 / (ν τ)) * ‖u‖²_{H²} * ‖v‖²_{H²}` (`0 sorryAx`). -/
theorem heatSmoothedBilinear6A_inH2_and_bound
    {ν τ : ℝ} (hν : 0 < ν) (hτ : 0 < τ) {u v : VecSeq3D} (hu : InH2Vec u) (hv : InH2Vec v) :
    InH2Vec (heatSmoothedBilinear6A ν τ u v) ∧
    h2VecNormSq (heatSmoothedBilinear6A ν τ u v) ≤
      (848 / (ν * τ)) * h2VecNormSq u * h2VecNormSq v := by
  let C : Fin 3 → Fin 3 → (Fin 3 → ℤ) → ℂ := fun j c => conv3D (fun m => u m j) (fun m => v m c)
  have hC : ∀ j c : Fin 3, InH2Seq (C j c) ∧
      h2NormSq (C j c) ≤ 1696 * h2NormSq (fun m => u m j) * h2NormSq (fun m => v m c) :=
    fun j c => conv3D_inH2_and_norm_le (hu j) (hv c)
  let term : Fin 3 → Fin 3 → (Fin 3 → ℤ) → ℝ := fun j c k => h2Weight k * ‖C j c k‖ ^ 2
  let sum9 : (Fin 3 → ℤ) → ℝ := fun k =>
    (term 0 0 k + term 1 0 k + term 2 0 k) +
    (term 0 1 k + term 1 1 k + term 2 1 k) +
    (term 0 2 k + term 1 2 k + term 2 2 k)
  have hsum9_has : HasSum sum9
      ((h2NormSq (C 0 0) + h2NormSq (C 1 0) + h2NormSq (C 2 0)) +
       (h2NormSq (C 0 1) + h2NormSq (C 1 1) + h2NormSq (C 2 1)) +
       (h2NormSq (C 0 2) + h2NormSq (C 1 2) + h2NormSq (C 2 2))) :=
    ((((((hC 0 0).1.hasSum.add (hC 1 0).1.hasSum).add (hC 2 0).1.hasSum).add
      (((hC 0 1).1.hasSum.add (hC 1 1).1.hasSum).add (hC 2 1).1.hasSum)).add
      (((hC 0 2).1.hasSum.add (hC 1 2).1.hasSum).add (hC 2 2).1.hasSum)))
  have hdom_has : HasSum (fun k => (1 / (2 * ν * τ)) * sum9 k)
      ((1 / (2 * ν * τ)) *
        ((h2NormSq (C 0 0) + h2NormSq (C 1 0) + h2NormSq (C 2 0)) +
         (h2NormSq (C 0 1) + h2NormSq (C 1 1) + h2NormSq (C 2 1)) +
         (h2NormSq (C 0 2) + h2NormSq (C 1 2) + h2NormSq (C 2 2)))) :=
    hsum9_has.mul_left (1 / (2 * ν * τ))
  have hpt_vec : ∀ k : Fin 3 → ℤ,
      h2Weight k * vecNormSqC (heatSmoothedBilinear6A ν τ u v k) ≤
        (1 / (2 * ν * τ)) * sum9 k := by
    intro k
    have hmul_eq : vecNormSqC (heatSmoothedBilinear6A ν τ u v k) =
        (heatMultiplier3D ν τ k) ^ 2 * vecNormSqC (nsBilinear6A u v k) := by
      unfold vecNormSqC heatSmoothedBilinear6A
      simp only [norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs]
      ring
    have hsm := heatMultiplier3D_smoothing_H1 hν hτ k
    have hbi := nsBilinear6A_normSq_le u v k
    have hw_nn : 0 ≤ h2Weight k := le_of_lt (h2Weight_pos k)
    have hsumC_nn : 0 ≤
        ((‖C 0 0 k‖ ^ 2 + ‖C 1 0 k‖ ^ 2 + ‖C 2 0 k‖ ^ 2) +
         (‖C 0 1 k‖ ^ 2 + ‖C 1 1 k‖ ^ 2 + ‖C 2 1 k‖ ^ 2) +
         (‖C 0 2 k‖ ^ 2 + ‖C 1 2 k‖ ^ 2 + ‖C 2 2 k‖ ^ 2)) := by positivity
    have h1 : (heatMultiplier3D ν τ k) ^ 2 * vecNormSqC (nsBilinear6A u v k) ≤
        (4 * Real.pi ^ 2 * kNormSq k * (heatMultiplier3D ν τ k) ^ 2) *
          ((‖C 0 0 k‖ ^ 2 + ‖C 1 0 k‖ ^ 2 + ‖C 2 0 k‖ ^ 2) +
           (‖C 0 1 k‖ ^ 2 + ‖C 1 1 k‖ ^ 2 + ‖C 2 1 k‖ ^ 2) +
           (‖C 0 2 k‖ ^ 2 + ‖C 1 2 k‖ ^ 2 + ‖C 2 2 k‖ ^ 2)) := by
      have hsq_nn : 0 ≤ (heatMultiplier3D ν τ k) ^ 2 := sq_nonneg _
      have h2 := mul_le_mul_of_nonneg_left hbi hsq_nn
      dsimp only [C]
      linarith
    have h2 : (4 * Real.pi ^ 2 * kNormSq k * (heatMultiplier3D ν τ k) ^ 2) *
        ((‖C 0 0 k‖ ^ 2 + ‖C 1 0 k‖ ^ 2 + ‖C 2 0 k‖ ^ 2) +
         (‖C 0 1 k‖ ^ 2 + ‖C 1 1 k‖ ^ 2 + ‖C 2 1 k‖ ^ 2) +
         (‖C 0 2 k‖ ^ 2 + ‖C 1 2 k‖ ^ 2 + ‖C 2 2 k‖ ^ 2)) ≤
        (1 / (2 * ν * τ)) *
          ((‖C 0 0 k‖ ^ 2 + ‖C 1 0 k‖ ^ 2 + ‖C 2 0 k‖ ^ 2) +
           (‖C 0 1 k‖ ^ 2 + ‖C 1 1 k‖ ^ 2 + ‖C 2 1 k‖ ^ 2) +
           (‖C 0 2 k‖ ^ 2 + ‖C 1 2 k‖ ^ 2 + ‖C 2 2 k‖ ^ 2)) :=
      mul_le_mul_of_nonneg_right hsm hsumC_nn
    have h3 : h2Weight k * vecNormSqC (heatSmoothedBilinear6A ν τ u v k) ≤
        h2Weight k * ((1 / (2 * ν * τ)) *
          ((‖C 0 0 k‖ ^ 2 + ‖C 1 0 k‖ ^ 2 + ‖C 2 0 k‖ ^ 2) +
           (‖C 0 1 k‖ ^ 2 + ‖C 1 1 k‖ ^ 2 + ‖C 2 1 k‖ ^ 2) +
           (‖C 0 2 k‖ ^ 2 + ‖C 1 2 k‖ ^ 2 + ‖C 2 2 k‖ ^ 2))) := by
      rw [hmul_eq]; exact mul_le_mul_of_nonneg_left (le_trans h1 h2) hw_nn
    have hfac : h2Weight k * ((1 / (2 * ν * τ)) *
        ((‖C 0 0 k‖ ^ 2 + ‖C 1 0 k‖ ^ 2 + ‖C 2 0 k‖ ^ 2) +
         (‖C 0 1 k‖ ^ 2 + ‖C 1 1 k‖ ^ 2 + ‖C 2 1 k‖ ^ 2) +
         (‖C 0 2 k‖ ^ 2 + ‖C 1 2 k‖ ^ 2 + ‖C 2 2 k‖ ^ 2))) =
        (1 / (2 * ν * τ)) * sum9 k := by
      dsimp only [sum9, term]; ring
    linarith
  have hS_inH2 : InH2Vec (heatSmoothedBilinear6A ν τ u v) := by
    intro c
    refine Summable.of_nonneg_of_le
      (fun k => mul_nonneg (le_of_lt (h2Weight_pos k)) (sq_nonneg _))
      (fun k => ?_) hdom_has.summable
    have hcle : ‖heatSmoothedBilinear6A ν τ u v k c‖ ^ 2 ≤
        vecNormSqC (heatSmoothedBilinear6A ν τ u v k) := by
      unfold vecNormSqC
      fin_cases c
      · change ‖heatSmoothedBilinear6A ν τ u v k 0‖ ^ 2 ≤ _
        linarith [sq_nonneg ‖heatSmoothedBilinear6A ν τ u v k 1‖,
                  sq_nonneg ‖heatSmoothedBilinear6A ν τ u v k 2‖]
      · change ‖heatSmoothedBilinear6A ν τ u v k 1‖ ^ 2 ≤ _
        linarith [sq_nonneg ‖heatSmoothedBilinear6A ν τ u v k 0‖,
                  sq_nonneg ‖heatSmoothedBilinear6A ν τ u v k 2‖]
      · change ‖heatSmoothedBilinear6A ν τ u v k 2‖ ^ 2 ≤ _
        linarith [sq_nonneg ‖heatSmoothedBilinear6A ν τ u v k 0‖,
                  sq_nonneg ‖heatSmoothedBilinear6A ν τ u v k 1‖]
    exact le_trans (mul_le_mul_of_nonneg_left hcle (le_of_lt (h2Weight_pos k))) (hpt_vec k)
  have htsum_bd := hasSum_le hpt_vec (hasSum_h2VecNormSq hS_inH2) hdom_has
  have hsum9_bd :
      ((h2NormSq (C 0 0) + h2NormSq (C 1 0) + h2NormSq (C 2 0)) +
       (h2NormSq (C 0 1) + h2NormSq (C 1 1) + h2NormSq (C 2 1)) +
       (h2NormSq (C 0 2) + h2NormSq (C 1 2) + h2NormSq (C 2 2))) ≤
      1696 * h2VecNormSq u * h2VecNormSq v := by
    have hfac : 1696 * h2VecNormSq u * h2VecNormSq v =
        (1696 * h2NormSq (fun m => u m 0) * h2NormSq (fun m => v m 0) +
         1696 * h2NormSq (fun m => u m 1) * h2NormSq (fun m => v m 0) +
         1696 * h2NormSq (fun m => u m 2) * h2NormSq (fun m => v m 0)) +
        (1696 * h2NormSq (fun m => u m 0) * h2NormSq (fun m => v m 1) +
         1696 * h2NormSq (fun m => u m 1) * h2NormSq (fun m => v m 1) +
         1696 * h2NormSq (fun m => u m 2) * h2NormSq (fun m => v m 1)) +
        (1696 * h2NormSq (fun m => u m 0) * h2NormSq (fun m => v m 2) +
         1696 * h2NormSq (fun m => u m 1) * h2NormSq (fun m => v m 2) +
         1696 * h2NormSq (fun m => u m 2) * h2NormSq (fun m => v m 2)) := by
      unfold h2VecNormSq; ring
    rw [hfac]
    linarith [(hC 0 0).2, (hC 1 0).2, (hC 2 0).2,
              (hC 0 1).2, (hC 1 1).2, (hC 2 1).2,
              (hC 0 2).2, (hC 1 2).2, (hC 2 2).2]
  have hcoef_nn : 0 ≤ 1 / (2 * ν * τ) := by positivity
  have hbd2 := le_trans htsum_bd (mul_le_mul_of_nonneg_left hsum9_bd hcoef_nn)
  have hconst : (1 / (2 * ν * τ)) * (1696 * h2VecNormSq u * h2VecNormSq v) =
      (848 / (ν * τ)) * h2VecNormSq u * h2VecNormSq v := by
    have hν_ne : ν ≠ 0 := ne_of_gt hν
    have hτ_ne : τ ≠ 0 := ne_of_gt hτ
    field_simp [hν_ne, hτ_ne]; ring
  exact ⟨hS_inH2, by linarith⟩

theorem nsBilinear6A_self_sub_eq {u v : VecSeq3D} (hu : InH2Vec u) (hv : InH2Vec v)
    (k : Fin 3 → ℤ) (c : Fin 3) :
    nsBilinear6A u u k c - nsBilinear6A v v k c =
      nsBilinear6A (fun m j => u m j - v m j) u k c +
      nsBilinear6A v (fun m j => u m j - v m j) k c := by
  have hflux : ∀ d : Fin 3,
      nsFlux6A u u k d - nsFlux6A v v k d =
        nsFlux6A (fun m j => u m j - v m j) u k d +
        nsFlux6A v (fun m j => u m j - v m j) k d := by
    intro d
    unfold nsFlux6A
    rw [conv3D_sub_left (hu 0) (hv 0) (hu d) k,
        conv3D_sub_left (hu 1) (hv 1) (hu d) k,
        conv3D_sub_left (hu 2) (hv 2) (hu d) k,
        conv3D_sub_right (hv 0) (hu d) (hv d) k,
        conv3D_sub_right (hv 1) (hu d) (hv d) k,
        conv3D_sub_right (hv 2) (hu d) (hv d) k]
    ring
  unfold nsBilinear6A
  have h1 : lerayProj6A k (nsFlux6A u u k) c - lerayProj6A k (nsFlux6A v v k) c =
      lerayProj6A k (fun d => nsFlux6A u u k d - nsFlux6A v v k d) c :=
    (lerayProj6A_sub k (nsFlux6A u u k) (nsFlux6A v v k) c).symm
  have h2 : (fun d => nsFlux6A u u k d - nsFlux6A v v k d) =
      (fun d => nsFlux6A (fun m j => u m j - v m j) u k d +
                nsFlux6A v (fun m j => u m j - v m j) k d) := funext hflux
  rw [h2, lerayProj6A_add] at h1
  linear_combination -h1

/-- **MAIN THEOREM 5 OF MILESTONE 6A-2 (Quadratic Lipschitz Estimate for `e^{ντΔ} B(u, u)`):**
    `‖S_τ(u, u) - S_τ(v, v)‖²_{H²} ≤ (1696 / (ν τ)) * (‖u‖²_{H²} + ‖v‖²_{H²}) * ‖u - v‖²_{H²}` (`0 sorryAx`). -/
theorem heatSmoothedBilinear6A_self_sub_lipschitz
    {ν τ : ℝ} (hν : 0 < ν) (hτ : 0 < τ) {u v : VecSeq3D} (hu : InH2Vec u) (hv : InH2Vec v) :
    InH2Vec (fun k c => heatSmoothedBilinear6A ν τ u u k c - heatSmoothedBilinear6A ν τ v v k c) ∧
    h2VecNormSq (fun k c => heatSmoothedBilinear6A ν τ u u k c - heatSmoothedBilinear6A ν τ v v k c) ≤
      (1696 / (ν * τ)) * (h2VecNormSq u + h2VecNormSq v) *
        h2VecNormSq (fun k c => u k c - v k c) := by
  have hdiff := (inH2Vec_sub hu hv).1
  have hL := heatSmoothedBilinear6A_inH2_and_bound hν hτ hdiff hu
  have hR := heatSmoothedBilinear6A_inH2_and_bound hν hτ hv hdiff
  have hsplit :
      (fun k c => heatSmoothedBilinear6A ν τ u u k c - heatSmoothedBilinear6A ν τ v v k c) =
      (fun k c => heatSmoothedBilinear6A ν τ (fun m j => u m j - v m j) u k c +
                  heatSmoothedBilinear6A ν τ v (fun m j => u m j - v m j) k c) := by
    funext k c
    unfold heatSmoothedBilinear6A
    rw [← mul_sub, nsBilinear6A_self_sub_eq hu hv k c, mul_add]
  have hadd := inH2Vec_add hL.1 hR.1
  rw [← hsplit] at hadd
  refine ⟨hadd.1, ?_⟩
  have hconst : 2 * ((848 / (ν * τ)) * h2VecNormSq (fun k c => u k c - v k c) * h2VecNormSq u) +
      2 * ((848 / (ν * τ)) * h2VecNormSq v * h2VecNormSq (fun k c => u k c - v k c)) =
      (1696 / (ν * τ)) * (h2VecNormSq u + h2VecNormSq v) *
        h2VecNormSq (fun k c => u k c - v k c) := by ring
  linarith [hadd.2, hL.2, hR.2]

-- ============================================================================
-- SECTION 4: REVERSE SPECTRAL SYNTHESIS `H²(𝕋³) ↪ C⁰(𝕋³)` & `L∞` BOUND
-- ============================================================================

private theorem norm_fourierChar1D_6a2 (n : ℤ) (t : ℝ) : ‖fourierChar1D n t‖ = 1 := by
  unfold fourierChar1D
  have h : -2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) * (t : ℂ) =
      ((-2 * Real.pi * (n : ℝ) * t : ℝ) : ℂ) * Complex.I := by push_cast; ring
  rw [h, Complex.norm_exp_ofReal_mul_I]

private theorem fourierChar1D_periodic_6a2 (n : ℤ) (t : ℝ) :
    fourierChar1D n (t + 1) = fourierChar1D n t := by
  unfold fourierChar1D
  have hadd : -2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) * ((t + 1 : ℝ) : ℂ) =
      (-2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) * (t : ℂ)) +
      ((-n : ℤ) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by push_cast; ring
  rw [hadd, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]

/-- Reverse Fourier synthesis of a scalar sequence `a ∈ H²(𝕋³)` as a real field on `ℝ³`. -/
noncomputable def synthScalar3D (a : (Fin 3 → ℤ) → ℂ) (x : R3) : ℝ :=
  (∑' k : Fin 3 → ℤ, a k *
    starRingEnd ℂ (fourierChar1D (k 0) (x 0) * fourierChar1D (k 1) (x 1) *
      fourierChar1D (k 2) (x 2))).re

/-- Reverse Fourier synthesis of a vector sequence `u ∈ H²(𝕋³; ℂ³)` as a 3D real vector field. -/
noncomputable def synthVec3D (u : VecSeq3D) (x : R3) : R3 :=
  fun c => synthScalar3D (fun k => u k c) x

/-- **THEOREM 6 OF MILESTONE 6A-2 (Reverse Spectral Synthesis `H²(𝕋³) ↪ C⁰(𝕋³)` — Scalar):**
    Every `a ∈ H²(𝕋³)` synthesizes a continuous `ℤ³`-periodic function satisfying
    `(synthScalar3D a x)² ≤ 53 * ‖a‖²_{H²}` for every `x ∈ ℝ³` (`0 sorryAx`). -/
theorem synthScalar3D_continuous_periodic_and_Linf {a : (Fin 3 → ℤ) → ℂ} (ha : InH2Seq a) :
    Continuous (synthScalar3D a) ∧
    IsPeriodic3D (synthScalar3D a) ∧
    (∀ x : R3, (synthScalar3D a x) ^ 2 ≤ 53 * h2NormSq a) := by
  have hl1 := h2Seq_l1_embedding ha
  let e_pos : (Fin 3 → ℤ) → R3 → ℂ := fun m x =>
    starRingEnd ℂ (fourierChar1D (m 0) (x 0) * fourierChar1D (m 1) (x 1) *
      fourierChar1D (m 2) (x 2))
  have he_norm : ∀ m x, ‖e_pos m x‖ = 1 := fun m x => by
    dsimp only [e_pos]
    rw [Complex.norm_conj, norm_mul, norm_mul, norm_fourierChar1D_6a2,
        norm_fourierChar1D_6a2, norm_fourierChar1D_6a2, mul_one, mul_one]
  have he_cont : ∀ m, Continuous (e_pos m) := fun m => by
    have hc1 : ∀ (n : ℤ) (i : Fin 3), Continuous (fun x : R3 => fourierChar1D n (x i)) := fun n i =>
      (Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal)).comp
        (continuous_apply i)
    exact Complex.continuous_conj.comp (((hc1 (m 0) 0).mul (hc1 (m 1) 1)).mul (hc1 (m 2) 2))
  have hS_cont : Continuous (fun x => ∑' m : Fin 3 → ℤ, a m * e_pos m x) :=
    continuous_tsum (fun m => continuous_const.mul (he_cont m)) hl1.1 fun m x => by
      rw [norm_mul, he_norm, mul_one]
  refine ⟨Complex.continuous_re.comp hS_cont, ?_, ?_⟩
  · intro x i
    have h1 : ∀ m : Fin 3 → ℤ, e_pos m (x + basisVec i) = e_pos m x := by
      intro m; dsimp only [e_pos]
      have hb0 : (x + basisVec 0) 0 = x 0 + 1 ∧ (x + basisVec 0) 1 = x 1 ∧
          (x + basisVec 0) 2 = x 2 := by simp [basisVec]
      have hb1 : (x + basisVec 1) 0 = x 0 ∧ (x + basisVec 1) 1 = x 1 + 1 ∧
          (x + basisVec 1) 2 = x 2 := by simp [basisVec]
      have hb2 : (x + basisVec 2) 0 = x 0 ∧ (x + basisVec 2) 1 = x 1 ∧
          (x + basisVec 2) 2 = x 2 + 1 := by simp [basisVec]
      fin_cases i
      · change starRingEnd ℂ (fourierChar1D (m 0) ((x + basisVec 0) 0) *
            fourierChar1D (m 1) ((x + basisVec 0) 1) * fourierChar1D (m 2) ((x + basisVec 0) 2)) = _
        rw [hb0.1, hb0.2.1, hb0.2.2, fourierChar1D_periodic_6a2]
      · change starRingEnd ℂ (fourierChar1D (m 0) ((x + basisVec 1) 0) *
            fourierChar1D (m 1) ((x + basisVec 1) 1) * fourierChar1D (m 2) ((x + basisVec 1) 2)) = _
        rw [hb1.1, hb1.2.1, hb1.2.2, fourierChar1D_periodic_6a2]
      · change starRingEnd ℂ (fourierChar1D (m 0) ((x + basisVec 2) 0) *
            fourierChar1D (m 1) ((x + basisVec 2) 1) * fourierChar1D (m 2) ((x + basisVec 2) 2)) = _
        rw [hb2.1, hb2.2.1, hb2.2.2, fourierChar1D_periodic_6a2]
    change (∑' m : Fin 3 → ℤ, a m * e_pos m (x + basisVec i)).re =
      (∑' m : Fin 3 → ℤ, a m * e_pos m x).re
    simp_rw [h1]
  · intro x
    let Sx : ℂ := ∑' m : Fin 3 → ℤ, a m * e_pos m x
    have hre_sq : (Sx.re) ^ 2 ≤ ‖Sx‖ ^ 2 := by
      rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
      nlinarith [sq_nonneg Sx.im]
    have hsumm_x : Summable (fun m : Fin 3 → ℤ => ‖a m * e_pos m x‖) := by
      simpa only [norm_mul, he_norm, mul_one] using hl1.1
    have hnorm_le : ‖Sx‖ ≤ ∑' m : Fin 3 → ℤ, ‖a m‖ := by
      have h := norm_tsum_le_tsum_norm hsumm_x
      have heq : (fun m : Fin 3 → ℤ => ‖a m * e_pos m x‖) = (fun m => ‖a m‖) := by
        funext m; rw [norm_mul, he_norm, mul_one]
      rwa [heq] at h
    have hnorm_nn : 0 ≤ ‖Sx‖ := norm_nonneg _
    have hsq_le : ‖Sx‖ ^ 2 ≤ (∑' m : Fin 3 → ℤ, ‖a m‖) ^ 2 := by nlinarith
    exact le_trans hre_sq (le_trans hsq_le hl1.2)

/-- **THEOREM 7 OF MILESTONE 6A-2 (Reverse Spectral Synthesis `H²(𝕋³; ℂ³) ↪ C⁰(𝕋³; ℝ³)` — Vector):**
    Every `u ∈ H²(𝕋³; ℂ³)` synthesizes a continuous `ℤ³`-periodic 3D velocity field satisfying
    `|synthVec3D u x|² ≤ 53 * ‖u‖²_{H²}` (`0 sorryAx`). -/
theorem synthVec3D_continuous_periodic_and_Linf {u : VecSeq3D} (hu : InH2Vec u) :
    Continuous (synthVec3D u) ∧
    IsPeriodic3D (synthVec3D u) ∧
    (∀ x : R3, dot3D (synthVec3D u x) (synthVec3D u x) ≤ 53 * h2VecNormSq u) := by
  have h0 := synthScalar3D_continuous_periodic_and_Linf (hu 0)
  have h1 := synthScalar3D_continuous_periodic_and_Linf (hu 1)
  have h2 := synthScalar3D_continuous_periodic_and_Linf (hu 2)
  refine ⟨continuous_pi fun c => ?_, ?_, ?_⟩
  · fin_cases c
    · exact h0.1
    · exact h1.1
    · exact h2.1
  · intro x i
    funext c
    fin_cases c
    · exact h0.2.1 x i
    · exact h1.2.1 x i
    · exact h2.2.1 x i
  · intro x
    unfold dot3D synthVec3D h2VecNormSq
    nlinarith [h0.2.2 x, h1.2.2 x, h2.2.2 x]

-- ============================================================================
-- SECTION 5: AXIOM AUDIT TRAIL — MILESTONE 6A STAGE 2 (0 sorryAx)
-- ============================================================================

#print axioms lerayProj6A_solenoidal
#print axioms lerayProj6A_normSq_le
#print axioms heatSmoothedBilinear6A_solenoidal
#print axioms heatSmoothedBilinear6A_realSymm
#print axioms heatSmoothedBilinear6A_inH2_and_bound
#print axioms heatSmoothedBilinear6A_self_sub_lipschitz
#print axioms synthScalar3D_continuous_periodic_and_Linf
#print axioms synthVec3D_continuous_periodic_and_Linf

end GarrySpectralBilinear3D