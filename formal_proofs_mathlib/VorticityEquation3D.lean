import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Tactic.Ring
import Real3DVectorCalculus

/-!
# GARRYULT v4.0.0 — Milestone 2: Exact 3D Vorticity Equation from Classical Navier-Stokes PDE
Derives the full 3D incompressible vorticity transport & vortex-stretching equation
  `∂_t ω + (u · ∇)ω - (ω · ∇)u = ν Δω`  (with `ω = ∇ × u` and `∇ · ω = 0`)
directly from `IsClassicalNS3D` using Mathlib4 `fderiv`, `deriv`, and Schwarz symmetry
with zero algebraic shortcuts (`0 sorryAx`).
-/

namespace GarryVorticity3D

open GarryReal3DCalculus

-- ============================================================================
-- SECTION 1: BASIC CALCULUS & LINEARITY HELPERS FOR `partialDerivScalar`
-- ============================================================================

private lemma two_add_one_eq_three {α : Type*} [AddMonoidWithOne α] :
    (2 : α) + 1 = 3 := by
  rw [← Nat.cast_ofNat (n := 2), ← Nat.cast_one, ← Nat.cast_add]
  exact Nat.cast_ofNat

private lemma contDiffAt_two_of_three {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {f : E → F} {x : E}
    (hf : ContDiffAt ℝ 3 f x) : ContDiffAt ℝ 2 f x :=
  hf.of_le (by rw [← two_add_one_eq_three]; exact le_self_add)

private lemma differentiableAt_of_contDiffAt_two {E F : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] {f : E → F} {x : E}
    (hf : ContDiffAt ℝ 2 f x) : DifferentiableAt ℝ f x := by
  have h1 : ContDiffAt ℝ 1 f x := hf.of_le (by rw [← one_add_one_eq_two]; exact le_self_add)
  exact h1.differentiableAt (by simp)

theorem contDiffAt_two_partialDerivScalar
    (f : R3 → ℝ) (x : R3) (hf : ContDiffAt ℝ 3 f x) (j : Fin 3) :
    ContDiffAt ℝ 2 (fun y => partialDerivScalar f y j) x := by
  have h1 : ContDiffAt ℝ 2 (fderiv ℝ f) x := hf.fderiv_right (le_of_eq two_add_one_eq_three)
  exact ((ContinuousLinearMap.apply ℝ ℝ (basisVec j)).contDiff.contDiffAt).comp x h1

theorem partialDerivScalar_add
    {g₁ g₂ : R3 → ℝ} {x : R3}
    (h₁ : DifferentiableAt ℝ g₁ x) (h₂ : DifferentiableAt ℝ g₂ x) (i : Fin 3) :
    partialDerivScalar (fun y => g₁ y + g₂ y) x i =
      partialDerivScalar g₁ x i + partialDerivScalar g₂ x i := by
  have hadd : HasFDerivAt (fun y => g₁ y + g₂ y) (fderiv ℝ g₁ x + fderiv ℝ g₂ x) x :=
    h₁.hasFDerivAt.add h₂.hasFDerivAt
  unfold partialDerivScalar
  rw [hadd.fderiv]
  rfl

theorem partialDerivScalar_add3
    {g₁ g₂ g₃ : R3 → ℝ} {x : R3}
    (h₁ : DifferentiableAt ℝ g₁ x) (h₂ : DifferentiableAt ℝ g₂ x) (h₃ : DifferentiableAt ℝ g₃ x)
    (i : Fin 3) :
    partialDerivScalar (fun y => g₁ y + g₂ y + g₃ y) x i =
      partialDerivScalar g₁ x i + partialDerivScalar g₂ x i + partialDerivScalar g₃ x i := by
  have h12 : DifferentiableAt ℝ (fun y => g₁ y + g₂ y) x := h₁.add h₂
  rw [partialDerivScalar_add h12 h₃ i, partialDerivScalar_add h₁ h₂ i]

theorem partialDerivScalar_sub
    {g₁ g₂ : R3 → ℝ} {x : R3}
    (h₁ : DifferentiableAt ℝ g₁ x) (h₂ : DifferentiableAt ℝ g₂ x) (i : Fin 3) :
    partialDerivScalar (fun y => g₁ y - g₂ y) x i =
      partialDerivScalar g₁ x i - partialDerivScalar g₂ x i := by
  have hsub : HasFDerivAt (fun y => g₁ y - g₂ y) (fderiv ℝ g₁ x - fderiv ℝ g₂ x) x :=
    h₁.hasFDerivAt.sub h₂.hasFDerivAt
  unfold partialDerivScalar
  rw [hsub.fderiv]
  rfl

theorem partialDerivScalar_const_mul
    {g : R3 → ℝ} {x : R3} (c : ℝ)
    (hg : DifferentiableAt ℝ g x) (i : Fin 3) :
    partialDerivScalar (fun y => c * g y) x i = c * partialDerivScalar g x i := by
  have hcm : HasFDerivAt (fun y => c * g y) (c • fderiv ℝ g x) x :=
    hg.hasFDerivAt.const_mul c
  unfold partialDerivScalar
  rw [hcm.fderiv]
  rfl

theorem partialDerivScalar_mul
    {g₁ g₂ : R3 → ℝ} {x : R3}
    (h₁ : DifferentiableAt ℝ g₁ x) (h₂ : DifferentiableAt ℝ g₂ x) (i : Fin 3) :
    partialDerivScalar (fun y => g₁ y * g₂ y) x i =
      g₁ x * partialDerivScalar g₂ x i + partialDerivScalar g₁ x i * g₂ x := by
  have hmul : HasFDerivAt (fun y => g₁ y * g₂ y)
      (g₁ x • fderiv ℝ g₂ x + g₂ x • fderiv ℝ g₁ x) x :=
    h₁.hasFDerivAt.mul h₂.hasFDerivAt
  unfold partialDerivScalar
  rw [hmul.fderiv]
  simp [smul_eq_mul]
  ring

theorem deriv_sub_of_hasDerivAt {f g : ℝ → ℝ} {f' g' t : ℝ}
    (hf : HasDerivAt f f' t) (hg : HasDerivAt g g' t) :
    deriv (fun s => f s - g s) t = f' - g' := by
  have h : HasDerivAt (fun s => f s - g s) (f' - g') t := hf.sub hg
  exact h.deriv

theorem curl3D_add {f g : R3 → R3} {x : R3}
    (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) (comp : Fin 3) :
    curl3D (fun y c => f y c + g y c) x comp = curl3D f x comp + curl3D g x comp := by
  have hf0 : DifferentiableAt ℝ (fun y => f y 0) x := differentiableAt_pi.mp hf 0
  have hf1 : DifferentiableAt ℝ (fun y => f y 1) x := differentiableAt_pi.mp hf 1
  have hf2 : DifferentiableAt ℝ (fun y => f y 2) x := differentiableAt_pi.mp hf 2
  have hg0 : DifferentiableAt ℝ (fun y => g y 0) x := differentiableAt_pi.mp hg 0
  have hg1 : DifferentiableAt ℝ (fun y => g y 1) x := differentiableAt_pi.mp hg 1
  have hg2 : DifferentiableAt ℝ (fun y => g y 2) x := differentiableAt_pi.mp hg 2
  match comp with
  | ⟨0, _⟩ =>
    change partialDerivScalar (fun y => f y 2 + g y 2) x 1 -
           partialDerivScalar (fun y => f y 1 + g y 1) x 2 =
           (partialDerivScalar (fun y => f y 2) x 1 - partialDerivScalar (fun y => f y 1) x 2) +
           (partialDerivScalar (fun y => g y 2) x 1 - partialDerivScalar (fun y => g y 1) x 2)
    rw [partialDerivScalar_add hf2 hg2 1, partialDerivScalar_add hf1 hg1 2]
    ring
  | ⟨1, _⟩ =>
    change partialDerivScalar (fun y => f y 0 + g y 0) x 2 -
           partialDerivScalar (fun y => f y 2 + g y 2) x 0 =
           (partialDerivScalar (fun y => f y 0) x 2 - partialDerivScalar (fun y => f y 2) x 0) +
           (partialDerivScalar (fun y => g y 0) x 2 - partialDerivScalar (fun y => g y 2) x 0)
    rw [partialDerivScalar_add hf0 hg0 2, partialDerivScalar_add hf2 hg2 0]
    ring
  | ⟨2, _⟩ =>
    change partialDerivScalar (fun y => f y 1 + g y 1) x 0 -
           partialDerivScalar (fun y => f y 0 + g y 0) x 1 =
           (partialDerivScalar (fun y => f y 1) x 0 - partialDerivScalar (fun y => f y 0) x 1) +
           (partialDerivScalar (fun y => g y 1) x 0 - partialDerivScalar (fun y => g y 0) x 1)
    rw [partialDerivScalar_add hf1 hg1 0, partialDerivScalar_add hf0 hg0 1]
    ring

theorem curl3D_const_mul {f : R3 → R3} {x : R3} (c : ℝ)
    (hf : DifferentiableAt ℝ f x) (comp : Fin 3) :
    curl3D (fun y k => c * f y k) x comp = c * curl3D f x comp := by
  have hf0 : DifferentiableAt ℝ (fun y => f y 0) x := differentiableAt_pi.mp hf 0
  have hf1 : DifferentiableAt ℝ (fun y => f y 1) x := differentiableAt_pi.mp hf 1
  have hf2 : DifferentiableAt ℝ (fun y => f y 2) x := differentiableAt_pi.mp hf 2
  match comp with
  | ⟨0, _⟩ =>
    change partialDerivScalar (fun y => c * f y 2) x 1 -
           partialDerivScalar (fun y => c * f y 1) x 2 =
           c * (partialDerivScalar (fun y => f y 2) x 1 - partialDerivScalar (fun y => f y 1) x 2)
    rw [partialDerivScalar_const_mul c hf2 1, partialDerivScalar_const_mul c hf1 2]
    ring
  | ⟨1, _⟩ =>
    change partialDerivScalar (fun y => c * f y 0) x 2 -
           partialDerivScalar (fun y => c * f y 2) x 0 =
           c * (partialDerivScalar (fun y => f y 0) x 2 - partialDerivScalar (fun y => f y 2) x 0)
    rw [partialDerivScalar_const_mul c hf0 2, partialDerivScalar_const_mul c hf2 0]
    ring
  | ⟨2, _⟩ =>
    change partialDerivScalar (fun y => c * f y 1) x 0 -
           partialDerivScalar (fun y => c * f y 0) x 1 =
           c * (partialDerivScalar (fun y => f y 1) x 0 - partialDerivScalar (fun y => f y 0) x 1)
    rw [partialDerivScalar_const_mul c hf1 0, partialDerivScalar_const_mul c hf0 1]
    ring

-- ============================================================================
-- SECTION 2: PILLAR 1 — SPACE-TIME COMMUTATIVITY `∇ × (∂_t u) = ∂_t (∇ × u)`
-- ============================================================================

theorem timeDeriv_eq_fderiv_prod
    (F : ℝ × R3 → ℝ) (hF : ∀ q : ℝ × R3, ContDiffAt ℝ 2 F q) (t : ℝ) (y : R3) :
    deriv (fun s => F (s, y)) t = fderiv ℝ F (t, y) ((1 : ℝ), (0 : R3)) := by
  have hdiff : DifferentiableAt ℝ F (t, y) := differentiableAt_of_contDiffAt_two (hF (t, y))
  have hembed : HasDerivAt (fun s : ℝ => (s, y)) ((1 : ℝ), (0 : R3)) t :=
    (hasDerivAt_id t).prodMk (hasDerivAt_const t y)
  exact (hdiff.hasFDerivAt.comp_hasDerivAt t hembed).deriv

theorem spacePartial_eq_fderiv_prod
    (F : ℝ × R3 → ℝ) (hF : ∀ q : ℝ × R3, ContDiffAt ℝ 2 F q) (s : ℝ) (x : R3) (i : Fin 3) :
    partialDerivScalar (fun y => F (s, y)) x i = fderiv ℝ F (s, x) ((0 : ℝ), basisVec i) := by
  have hdiff : DifferentiableAt ℝ F (s, x) := differentiableAt_of_contDiffAt_two (hF (s, x))
  have hembed : HasFDerivAt (fun y : R3 => (s, y))
      ((0 : R3 →L[ℝ] ℝ).prod (ContinuousLinearMap.id ℝ R3)) x :=
    (hasFDerivAt_const s x).prodMk (hasFDerivAt_id x)
  have hcomp : HasFDerivAt (fun y : R3 => F (s, y))
      ((fderiv ℝ F (s, x)).comp ((0 : R3 →L[ℝ] ℝ).prod (ContinuousLinearMap.id ℝ R3))) x :=
    hdiff.hasFDerivAt.comp x hembed
  unfold partialDerivScalar
  rw [hcomp.fderiv]
  rfl

theorem hasFDerivAt_timeDeriv_space
    (F : ℝ × R3 → ℝ) (hF : ∀ q : ℝ × R3, ContDiffAt ℝ 2 F q) (t : ℝ) (x : R3) :
    HasFDerivAt (fun y => deriv (fun s => F (s, y)) t)
      ((ContinuousLinearMap.apply ℝ ℝ ((1 : ℝ), (0 : R3))).comp
        ((fderiv ℝ (fderiv ℝ F) (t, x)).comp
          ((0 : R3 →L[ℝ] ℝ).prod (ContinuousLinearMap.id ℝ R3)))) x := by
  have hfun : (fun y => deriv (fun s => F (s, y)) t) =
      (fun y => fderiv ℝ F (t, y) ((1 : ℝ), (0 : R3))) := by
    funext y
    exact timeDeriv_eq_fderiv_prod F hF t y
  rw [hfun]
  have h1 : ContDiffAt ℝ 1 (fderiv ℝ F) (t, x) :=
    (hF (t, x)).fderiv_right (by simp [one_add_one_eq_two])
  have hdiff : DifferentiableAt ℝ (fderiv ℝ F) (t, x) := h1.differentiableAt (by simp)
  have hembed : HasFDerivAt (fun y : R3 => (t, y))
      ((0 : R3 →L[ℝ] ℝ).prod (ContinuousLinearMap.id ℝ R3)) x :=
    (hasFDerivAt_const t x).prodMk (hasFDerivAt_id x)
  exact (ContinuousLinearMap.apply ℝ ℝ ((1 : ℝ), (0 : R3))).hasFDerivAt.comp x
    (hdiff.hasFDerivAt.comp x hembed)

theorem hasDerivAt_spacePartial_time
    (F : ℝ × R3 → ℝ) (hF : ∀ q : ℝ × R3, ContDiffAt ℝ 2 F q) (t : ℝ) (x : R3) (i : Fin 3) :
    HasDerivAt (fun s => partialDerivScalar (fun y => F (s, y)) x i)
      (fderiv ℝ (fderiv ℝ F) (t, x) ((1 : ℝ), (0 : R3)) ((0 : ℝ), basisVec i)) t := by
  have hfun : (fun s => partialDerivScalar (fun y => F (s, y)) x i) =
      (fun s => fderiv ℝ F (s, x) ((0 : ℝ), basisVec i)) := by
    funext s
    exact spacePartial_eq_fderiv_prod F hF s x i
  rw [hfun]
  have h1 : ContDiffAt ℝ 1 (fderiv ℝ F) (t, x) :=
    (hF (t, x)).fderiv_right (by simp [one_add_one_eq_two])
  have hdiff : DifferentiableAt ℝ (fderiv ℝ F) (t, x) := h1.differentiableAt (by simp)
  have hembed : HasDerivAt (fun s : ℝ => (s, x)) ((1 : ℝ), (0 : R3)) t :=
    (hasDerivAt_id t).prodMk (hasDerivAt_const t x)
  exact (ContinuousLinearMap.apply ℝ ℝ ((0 : ℝ), basisVec i)).hasFDerivAt.comp_hasDerivAt t
    (hdiff.hasFDerivAt.comp_hasDerivAt t hembed)

theorem partial_timeDeriv_comm
    (F : ℝ × R3 → ℝ) (hF : ∀ q : ℝ × R3, ContDiffAt ℝ 2 F q) (t : ℝ) (x : R3) (i : Fin 3) :
    partialDerivScalar (fun y => deriv (fun s => F (s, y)) t) x i =
      deriv (fun s => partialDerivScalar (fun y => F (s, y)) x i) t := by
  have h_lhs : partialDerivScalar (fun y => deriv (fun s => F (s, y)) t) x i =
      fderiv ℝ (fderiv ℝ F) (t, x) ((0 : ℝ), basisVec i) ((1 : ℝ), (0 : R3)) := by
    unfold partialDerivScalar
    rw [(hasFDerivAt_timeDeriv_space F hF t x).fderiv]
    rfl
  have h_rhs : deriv (fun s => partialDerivScalar (fun y => F (s, y)) x i) t =
      fderiv ℝ (fderiv ℝ F) (t, x) ((1 : ℝ), (0 : R3)) ((0 : ℝ), basisVec i) :=
    (hasDerivAt_spacePartial_time F hF t x i).deriv
  have hsymm := (hF (t, x)).isSymmSndFDerivAt (by simp)
  rw [h_lhs, h_rhs]
  exact hsymm.eq ((0 : ℝ), basisVec i) ((1 : ℝ), (0 : R3))

/-- **Pillar 1 (`∇ × (∂_t u) = ∂_t (∇ × u)`):** Proved unconditionally from space-time `C²` Schwarz symmetry. -/
theorem curl3D_timeDeriv_eq_timeDeriv_curl3D
    (u : ℝ → R3 → R3)
    (hu_st : ∀ q : ℝ × R3, ContDiffAt ℝ 2 (fun p : ℝ × R3 => u p.1 p.2) q)
    (t : ℝ) (x : R3) (comp : Fin 3) :
    curl3D (fun y c => deriv (fun s => u s y c) t) x comp =
      deriv (fun s => curl3D (u s) x comp) t := by
  have hF0 : ∀ q : ℝ × R3, ContDiffAt ℝ 2 (fun p : ℝ × R3 => u p.1 p.2 0) q :=
    fun q => contDiffAt_pi.mp (hu_st q) 0
  have hF1 : ∀ q : ℝ × R3, ContDiffAt ℝ 2 (fun p : ℝ × R3 => u p.1 p.2 1) q :=
    fun q => contDiffAt_pi.mp (hu_st q) 1
  have hF2 : ∀ q : ℝ × R3, ContDiffAt ℝ 2 (fun p : ℝ × R3 => u p.1 p.2 2) q :=
    fun q => contDiffAt_pi.mp (hu_st q) 2
  match comp with
  | ⟨0, _⟩ =>
    change partialDerivScalar (fun y => deriv (fun s => u s y 2) t) x 1 -
           partialDerivScalar (fun y => deriv (fun s => u s y 1) t) x 2 =
           deriv (fun s => partialDerivScalar (fun y => u s y 2) x 1 -
                           partialDerivScalar (fun y => u s y 1) x 2) t
    have h2 : HasDerivAt (fun s => partialDerivScalar (fun y => u s y 2) x 1) _ t :=
      hasDerivAt_spacePartial_time (fun p => u p.1 p.2 2) hF2 t x 1
    have h1 : HasDerivAt (fun s => partialDerivScalar (fun y => u s y 1) x 2) _ t :=
      hasDerivAt_spacePartial_time (fun p => u p.1 p.2 1) hF1 t x 2
    rw [partial_timeDeriv_comm (fun p => u p.1 p.2 2) hF2 t x 1,
        partial_timeDeriv_comm (fun p => u p.1 p.2 1) hF1 t x 2]
    dsimp only
    rw [h2.deriv, h1.deriv, deriv_sub_of_hasDerivAt h2 h1]
  | ⟨1, _⟩ =>
    change partialDerivScalar (fun y => deriv (fun s => u s y 0) t) x 2 -
           partialDerivScalar (fun y => deriv (fun s => u s y 2) t) x 0 =
           deriv (fun s => partialDerivScalar (fun y => u s y 0) x 2 -
                           partialDerivScalar (fun y => u s y 2) x 0) t
    have h0 : HasDerivAt (fun s => partialDerivScalar (fun y => u s y 0) x 2) _ t :=
      hasDerivAt_spacePartial_time (fun p => u p.1 p.2 0) hF0 t x 2
    have h2 : HasDerivAt (fun s => partialDerivScalar (fun y => u s y 2) x 0) _ t :=
      hasDerivAt_spacePartial_time (fun p => u p.1 p.2 2) hF2 t x 0
    rw [partial_timeDeriv_comm (fun p => u p.1 p.2 0) hF0 t x 2,
        partial_timeDeriv_comm (fun p => u p.1 p.2 2) hF2 t x 0]
    dsimp only
    rw [h0.deriv, h2.deriv, deriv_sub_of_hasDerivAt h0 h2]
  | ⟨2, _⟩ =>
    change partialDerivScalar (fun y => deriv (fun s => u s y 1) t) x 0 -
           partialDerivScalar (fun y => deriv (fun s => u s y 0) t) x 1 =
           deriv (fun s => partialDerivScalar (fun y => u s y 1) x 0 -
                           partialDerivScalar (fun y => u s y 0) x 1) t
    have h1 : HasDerivAt (fun s => partialDerivScalar (fun y => u s y 1) x 0) _ t :=
      hasDerivAt_spacePartial_time (fun p => u p.1 p.2 1) hF1 t x 0
    have h0 : HasDerivAt (fun s => partialDerivScalar (fun y => u s y 0) x 1) _ t :=
      hasDerivAt_spacePartial_time (fun p => u p.1 p.2 0) hF0 t x 1
    rw [partial_timeDeriv_comm (fun p => u p.1 p.2 1) hF1 t x 0,
        partial_timeDeriv_comm (fun p => u p.1 p.2 0) hF0 t x 1]
    dsimp only
    rw [h1.deriv, h0.deriv, deriv_sub_of_hasDerivAt h1 h0]

-- ============================================================================
-- SECTION 3: PILLAR 2 — NONLINEAR ADVECTION CURL & VORTEX STRETCHING IDENTITY
-- ============================================================================

/-- General directional derivative operator `(v · ∇)w` in ℝ³.
    Note: `(u · ∇)ω` is vorticity advection; `(ω · ∇)u` is 3D vortex stretching. -/
noncomputable def directionalAdvection3D (v w : R3 → R3) (x : R3) : R3 :=
  fun comp =>
    v x 0 * partialDerivScalar (fun y => w y comp) x 0 +
    v x 1 * partialDerivScalar (fun y => w y comp) x 1 +
    v x 2 * partialDerivScalar (fun y => w y comp) x 2

theorem differentiableAt_advection3D
    (u : R3 → R3) (x : R3) (hu : ContDiffAt ℝ 2 u x) :
    DifferentiableAt ℝ (advection3D u) x := by
  refine differentiableAt_pi.mpr fun comp => ?_
  have huc : ContDiffAt ℝ 2 (fun y => u y comp) x := contDiffAt_pi.mp hu comp
  have hu0 : DifferentiableAt ℝ (fun y => u y 0) x :=
    differentiableAt_of_contDiffAt_two (contDiffAt_pi.mp hu 0)
  have hu1 : DifferentiableAt ℝ (fun y => u y 1) x :=
    differentiableAt_of_contDiffAt_two (contDiffAt_pi.mp hu 1)
  have hu2 : DifferentiableAt ℝ (fun y => u y 2) x :=
    differentiableAt_of_contDiffAt_two (contDiffAt_pi.mp hu 2)
  have hd0 := (hasFDerivAt_partialDerivScalar (fun y => u y comp) x huc 0).differentiableAt
  have hd1 := (hasFDerivAt_partialDerivScalar (fun y => u y comp) x huc 1).differentiableAt
  have hd2 := (hasFDerivAt_partialDerivScalar (fun y => u y comp) x huc 2).differentiableAt
  exact ((hu0.mul hd0).add (hu1.mul hd1)).add (hu2.mul hd2)

theorem partialDerivScalar_advection3D
    (u : R3 → R3) (x : R3) (hu : ContDiffAt ℝ 2 u x) (comp i : Fin 3) :
    partialDerivScalar (fun y => advection3D u y comp) x i =
      (u x 0 * sndPartial (fun y => u y comp) x i 0 +
       partialDerivScalar (fun y => u y 0) x i * partialDerivScalar (fun y => u y comp) x 0) +
      (u x 1 * sndPartial (fun y => u y comp) x i 1 +
       partialDerivScalar (fun y => u y 1) x i * partialDerivScalar (fun y => u y comp) x 1) +
      (u x 2 * sndPartial (fun y => u y comp) x i 2 +
       partialDerivScalar (fun y => u y 2) x i * partialDerivScalar (fun y => u y comp) x 2) := by
  have huc : ContDiffAt ℝ 2 (fun y => u y comp) x := contDiffAt_pi.mp hu comp
  have hu0 : DifferentiableAt ℝ (fun y => u y 0) x :=
    differentiableAt_of_contDiffAt_two (contDiffAt_pi.mp hu 0)
  have hu1 : DifferentiableAt ℝ (fun y => u y 1) x :=
    differentiableAt_of_contDiffAt_two (contDiffAt_pi.mp hu 1)
  have hu2 : DifferentiableAt ℝ (fun y => u y 2) x :=
    differentiableAt_of_contDiffAt_two (contDiffAt_pi.mp hu 2)
  have hd0 := (hasFDerivAt_partialDerivScalar (fun y => u y comp) x huc 0).differentiableAt
  have hd1 := (hasFDerivAt_partialDerivScalar (fun y => u y comp) x huc 1).differentiableAt
  have hd2 := (hasFDerivAt_partialDerivScalar (fun y => u y comp) x huc 2).differentiableAt
  have hm0 : DifferentiableAt ℝ (fun y => u y 0 * partialDerivScalar (fun z => u z comp) y 0) x :=
    hu0.mul hd0
  have hm1 : DifferentiableAt ℝ (fun y => u y 1 * partialDerivScalar (fun z => u z comp) y 1) x :=
    hu1.mul hd1
  have hm2 : DifferentiableAt ℝ (fun y => u y 2 * partialDerivScalar (fun z => u z comp) y 2) x :=
    hu2.mul hd2
  unfold advection3D
  rw [partialDerivScalar_add3 hm0 hm1 hm2 i,
      partialDerivScalar_mul hu0 hd0 i,
      partialDerivScalar_mul hu1 hd1 i,
      partialDerivScalar_mul hu2 hd2 i,
      partial_partial_eq_sndPartial (fun y => u y comp) x huc i 0,
      partial_partial_eq_sndPartial (fun y => u y comp) x huc i 1,
      partial_partial_eq_sndPartial (fun y => u y comp) x huc i 2]

/-- **Pillar 2 (Exact 3D Vortex-Stretching Vector Identity):**
    For any `C²` vector field `u : ℝ³ → ℝ³` with vorticity `ω = ∇ × u`,
    `∇ × ((u · ∇)u) = (u · ∇)ω - (ω · ∇)u + (∇ · u) ω` identically at every `x ∈ ℝ³`. -/
theorem curl3D_advection3D
    (u : R3 → R3) (x : R3) (hu : ContDiffAt ℝ 2 u x) (comp : Fin 3) :
    curl3D (advection3D u) x comp =
      directionalAdvection3D u (curl3D u) x comp -
      directionalAdvection3D (curl3D u) u x comp +
      div3D u x * curl3D u x comp := by
  have hu0 : ContDiffAt ℝ 2 (fun y => u y 0) x := contDiffAt_pi.mp hu 0
  have hu1 : ContDiffAt ℝ 2 (fun y => u y 1) x := contDiffAt_pi.mp hu 1
  have hu2 : ContDiffAt ℝ 2 (fun y => u y 2) x := contDiffAt_pi.mp hu 2
  match comp with
  | ⟨0, _⟩ =>
    have hw0 : ∀ m : Fin 3, partialDerivScalar (fun y => curl3D u y 0) x m =
        sndPartial (fun y => u y 2) x m 1 - sndPartial (fun y => u y 1) x m 2 := fun m =>
      partialDerivScalar_sub_of_hasFDerivAt
        (hasFDerivAt_partialDerivScalar (fun y => u y 2) x hu2 1)
        (hasFDerivAt_partialDerivScalar (fun y => u y 1) x hu1 2) m
    change partialDerivScalar (fun y => advection3D u y 2) x 1 -
           partialDerivScalar (fun y => advection3D u y 1) x 2 =
           directionalAdvection3D u (curl3D u) x 0 -
           directionalAdvection3D (curl3D u) u x 0 +
           div3D u x * curl3D u x 0
    rw [partialDerivScalar_advection3D u x hu 2 1,
        partialDerivScalar_advection3D u x hu 1 2]
    unfold directionalAdvection3D div3D
    rw [hw0 0, hw0 1, hw0 2]
    change _ = _ -
      ((partialDerivScalar (fun y => u y 2) x 1 - partialDerivScalar (fun y => u y 1) x 2) *
         partialDerivScalar (fun y => u y 0) x 0 +
       (partialDerivScalar (fun y => u y 0) x 2 - partialDerivScalar (fun y => u y 2) x 0) *
         partialDerivScalar (fun y => u y 0) x 1 +
       (partialDerivScalar (fun y => u y 1) x 0 - partialDerivScalar (fun y => u y 0) x 1) *
         partialDerivScalar (fun y => u y 0) x 2) +
      (partialDerivScalar (fun y => u y 0) x 0 + partialDerivScalar (fun y => u y 1) x 1 +
       partialDerivScalar (fun y => u y 2) x 2) *
      (partialDerivScalar (fun y => u y 2) x 1 - partialDerivScalar (fun y => u y 1) x 2)
    rw [sndPartial_symm_of_contDiffAt (fun y => u y 2) x hu2 1 0,
        sndPartial_symm_of_contDiffAt (fun y => u y 2) x hu2 1 2,
        sndPartial_symm_of_contDiffAt (fun y => u y 1) x hu1 2 0,
        sndPartial_symm_of_contDiffAt (fun y => u y 1) x hu1 2 1]
    ring
  | ⟨1, _⟩ =>
    have hw1 : ∀ m : Fin 3, partialDerivScalar (fun y => curl3D u y 1) x m =
        sndPartial (fun y => u y 0) x m 2 - sndPartial (fun y => u y 2) x m 0 := fun m =>
      partialDerivScalar_sub_of_hasFDerivAt
        (hasFDerivAt_partialDerivScalar (fun y => u y 0) x hu0 2)
        (hasFDerivAt_partialDerivScalar (fun y => u y 2) x hu2 0) m
    change partialDerivScalar (fun y => advection3D u y 0) x 2 -
           partialDerivScalar (fun y => advection3D u y 2) x 0 =
           directionalAdvection3D u (curl3D u) x 1 -
           directionalAdvection3D (curl3D u) u x 1 +
           div3D u x * curl3D u x 1
    rw [partialDerivScalar_advection3D u x hu 0 2,
        partialDerivScalar_advection3D u x hu 2 0]
    unfold directionalAdvection3D div3D
    rw [hw1 0, hw1 1, hw1 2]
    change _ = _ -
      ((partialDerivScalar (fun y => u y 2) x 1 - partialDerivScalar (fun y => u y 1) x 2) *
         partialDerivScalar (fun y => u y 1) x 0 +
       (partialDerivScalar (fun y => u y 0) x 2 - partialDerivScalar (fun y => u y 2) x 0) *
         partialDerivScalar (fun y => u y 1) x 1 +
       (partialDerivScalar (fun y => u y 1) x 0 - partialDerivScalar (fun y => u y 0) x 1) *
         partialDerivScalar (fun y => u y 1) x 2) +
      (partialDerivScalar (fun y => u y 0) x 0 + partialDerivScalar (fun y => u y 1) x 1 +
       partialDerivScalar (fun y => u y 2) x 2) *
      (partialDerivScalar (fun y => u y 0) x 2 - partialDerivScalar (fun y => u y 2) x 0)
    rw [sndPartial_symm_of_contDiffAt (fun y => u y 0) x hu0 2 0,
        sndPartial_symm_of_contDiffAt (fun y => u y 0) x hu0 2 1,
        sndPartial_symm_of_contDiffAt (fun y => u y 2) x hu2 0 1,
        sndPartial_symm_of_contDiffAt (fun y => u y 2) x hu2 0 2]
    ring
  | ⟨2, _⟩ =>
    have hw2 : ∀ m : Fin 3, partialDerivScalar (fun y => curl3D u y 2) x m =
        sndPartial (fun y => u y 1) x m 0 - sndPartial (fun y => u y 0) x m 1 := fun m =>
      partialDerivScalar_sub_of_hasFDerivAt
        (hasFDerivAt_partialDerivScalar (fun y => u y 1) x hu1 0)
        (hasFDerivAt_partialDerivScalar (fun y => u y 0) x hu0 1) m
    change partialDerivScalar (fun y => advection3D u y 1) x 0 -
           partialDerivScalar (fun y => advection3D u y 0) x 1 =
           directionalAdvection3D u (curl3D u) x 2 -
           directionalAdvection3D (curl3D u) u x 2 +
           div3D u x * curl3D u x 2
    rw [partialDerivScalar_advection3D u x hu 1 0,
        partialDerivScalar_advection3D u x hu 0 1]
    unfold directionalAdvection3D div3D
    rw [hw2 0, hw2 1, hw2 2]
    change _ = _ -
      ((partialDerivScalar (fun y => u y 2) x 1 - partialDerivScalar (fun y => u y 1) x 2) *
         partialDerivScalar (fun y => u y 2) x 0 +
       (partialDerivScalar (fun y => u y 0) x 2 - partialDerivScalar (fun y => u y 2) x 0) *
         partialDerivScalar (fun y => u y 2) x 1 +
       (partialDerivScalar (fun y => u y 1) x 0 - partialDerivScalar (fun y => u y 0) x 1) *
         partialDerivScalar (fun y => u y 2) x 2) +
      (partialDerivScalar (fun y => u y 0) x 0 + partialDerivScalar (fun y => u y 1) x 1 +
       partialDerivScalar (fun y => u y 2) x 2) *
      (partialDerivScalar (fun y => u y 1) x 0 - partialDerivScalar (fun y => u y 0) x 1)
    rw [sndPartial_symm_of_contDiffAt (fun y => u y 1) x hu1 0 1,
        sndPartial_symm_of_contDiffAt (fun y => u y 1) x hu1 0 2,
        sndPartial_symm_of_contDiffAt (fun y => u y 0) x hu0 1 0,
        sndPartial_symm_of_contDiffAt (fun y => u y 0) x hu0 1 2]
    ring

-- ============================================================================
-- SECTION 4: PILLAR 3 — COMMUTATIVITY OF `curl3D` AND `laplacian3D` (`C³`)
-- ============================================================================

theorem sndPartial_sub
    (g₁ g₂ : R3 → ℝ) (hg₁ : ∀ y : R3, ContDiffAt ℝ 2 g₁ y) (hg₂ : ∀ y : R3, ContDiffAt ℝ 2 g₂ y)
    (x : R3) (i j : Fin 3) :
    sndPartial (fun y => g₁ y - g₂ y) x i j = sndPartial g₁ x i j - sndPartial g₂ x i j := by
  have hsub_c2 : ContDiffAt ℝ 2 (fun y => g₁ y - g₂ y) x := (hg₁ x).sub (hg₂ x)
  rw [← partial_partial_eq_sndPartial (fun y => g₁ y - g₂ y) x hsub_c2 i j]
  have hinner : (fun y => partialDerivScalar (fun z => g₁ z - g₂ z) y j) =
      (fun y => partialDerivScalar g₁ y j - partialDerivScalar g₂ y j) := by
    funext y
    exact partialDerivScalar_sub
      (differentiableAt_of_contDiffAt_two (hg₁ y))
      (differentiableAt_of_contDiffAt_two (hg₂ y)) j
  rw [hinner,
      partialDerivScalar_sub
        (hasFDerivAt_partialDerivScalar g₁ x (hg₁ x) j).differentiableAt
        (hasFDerivAt_partialDerivScalar g₂ x (hg₂ x) j).differentiableAt i,
      partial_partial_eq_sndPartial g₁ x (hg₁ x) i j,
      partial_partial_eq_sndPartial g₂ x (hg₂ x) i j]

theorem laplacianScalar_sub
    (g₁ g₂ : R3 → ℝ) (hg₁ : ∀ y : R3, ContDiffAt ℝ 2 g₁ y) (hg₂ : ∀ y : R3, ContDiffAt ℝ 2 g₂ y)
    (x : R3) :
    laplacianScalar (fun y => g₁ y - g₂ y) x = laplacianScalar g₁ x - laplacianScalar g₂ x := by
  unfold laplacianScalar
  rw [sndPartial_sub g₁ g₂ hg₁ hg₂ x 0 0,
      sndPartial_sub g₁ g₂ hg₁ hg₂ x 1 1,
      sndPartial_sub g₁ g₂ hg₁ hg₂ x 2 2]
  ring

theorem partial_sndPartial_diag_comm
    (f : R3 → ℝ) (hf : ∀ y : R3, ContDiffAt ℝ 3 f y) (x : R3) (i m : Fin 3) :
    partialDerivScalar (fun y => sndPartial f y m m) x i =
      sndPartial (fun y => partialDerivScalar f y i) x m m := by
  have h_eq1 : (fun y => sndPartial f y m m) =
      (fun y => partialDerivScalar (fun z => partialDerivScalar f z m) y m) := by
    funext y
    exact (partial_partial_eq_sndPartial f y (contDiffAt_two_of_three (hf y)) m m).symm
  have hgm : ContDiffAt ℝ 2 (fun z => partialDerivScalar f z m) x :=
    contDiffAt_two_partialDerivScalar f x (hf x) m
  have hgi : ContDiffAt ℝ 2 (fun z => partialDerivScalar f z i) x :=
    contDiffAt_two_partialDerivScalar f x (hf x) i
  have h_eq2 : (fun y => partialDerivScalar (fun z => partialDerivScalar f z m) y i) =
      (fun y => partialDerivScalar (fun z => partialDerivScalar f z i) y m) := by
    funext y
    have hf2 : ContDiffAt ℝ 2 f y := contDiffAt_two_of_three (hf y)
    rw [partial_partial_eq_sndPartial f y hf2 i m,
        partial_partial_eq_sndPartial f y hf2 m i,
        sndPartial_symm_of_contDiffAt f y hf2 i m]
  rw [h_eq1,
      partial_partial_eq_sndPartial (fun z => partialDerivScalar f z m) x hgm i m,
      sndPartial_symm_of_contDiffAt (fun z => partialDerivScalar f z m) x hgm i m,
      ← partial_partial_eq_sndPartial (fun z => partialDerivScalar f z m) x hgm m i,
      h_eq2,
      partial_partial_eq_sndPartial (fun z => partialDerivScalar f z i) x hgi m m]

theorem differentiableAt_sndPartial_diag
    (f : R3 → ℝ) (hf : ∀ y : R3, ContDiffAt ℝ 3 f y) (x : R3) (m : Fin 3) :
    DifferentiableAt ℝ (fun y => sndPartial f y m m) x := by
  have h_eq : (fun y => sndPartial f y m m) =
      (fun y => partialDerivScalar (fun z => partialDerivScalar f z m) y m) := by
    funext y
    exact (partial_partial_eq_sndPartial f y (contDiffAt_two_of_three (hf y)) m m).symm
  rw [h_eq]
  exact (hasFDerivAt_partialDerivScalar (fun z => partialDerivScalar f z m) x
    (contDiffAt_two_partialDerivScalar f x (hf x) m) m).differentiableAt

theorem differentiableAt_laplacian3D
    (u : R3 → R3) (hu : ∀ y : R3, ContDiffAt ℝ 3 u y) (x : R3) :
    DifferentiableAt ℝ (laplacian3D u) x := by
  refine differentiableAt_pi.mpr fun comp => ?_
  have huc : ∀ y : R3, ContDiffAt ℝ 3 (fun z => u z comp) y :=
    fun y => contDiffAt_pi.mp (hu y) comp
  exact ((differentiableAt_sndPartial_diag (fun z => u z comp) huc x 0).add
         (differentiableAt_sndPartial_diag (fun z => u z comp) huc x 1)).add
        (differentiableAt_sndPartial_diag (fun z => u z comp) huc x 2)

theorem partial_laplacianScalar_comm
    (f : R3 → ℝ) (hf : ∀ y : R3, ContDiffAt ℝ 3 f y) (x : R3) (i : Fin 3) :
    partialDerivScalar (fun y => laplacianScalar f y) x i =
      laplacianScalar (fun y => partialDerivScalar f y i) x := by
  have hd0 := differentiableAt_sndPartial_diag f hf x 0
  have hd1 := differentiableAt_sndPartial_diag f hf x 1
  have hd2 := differentiableAt_sndPartial_diag f hf x 2
  unfold laplacianScalar
  rw [partialDerivScalar_add3 hd0 hd1 hd2 i,
      partial_sndPartial_diag_comm f hf x i 0,
      partial_sndPartial_diag_comm f hf x i 1,
      partial_sndPartial_diag_comm f hf x i 2]

/-- **Pillar 3 (`∇ × (Δu) = Δ(∇ × u)`):** Proved unconditionally for any `C³` 3D vector field `u`. -/
theorem curl3D_laplacian3D
    (u : R3 → R3) (hu : ∀ y : R3, ContDiffAt ℝ 3 u y) (x : R3) (comp : Fin 3) :
    curl3D (laplacian3D u) x comp = laplacian3D (curl3D u) x comp := by
  have hu0 : ∀ y, ContDiffAt ℝ 3 (fun z => u z 0) y := fun y => contDiffAt_pi.mp (hu y) 0
  have hu1 : ∀ y, ContDiffAt ℝ 3 (fun z => u z 1) y := fun y => contDiffAt_pi.mp (hu y) 1
  have hu2 : ∀ y, ContDiffAt ℝ 3 (fun z => u z 2) y := fun y => contDiffAt_pi.mp (hu y) 2
  match comp with
  | ⟨0, _⟩ =>
    change partialDerivScalar (fun y => laplacianScalar (fun z => u z 2) y) x 1 -
           partialDerivScalar (fun y => laplacianScalar (fun z => u z 1) y) x 2 =
           laplacianScalar (fun y => partialDerivScalar (fun z => u z 2) y 1 -
                                     partialDerivScalar (fun z => u z 1) y 2) x
    rw [partial_laplacianScalar_comm (fun z => u z 2) hu2 x 1,
        partial_laplacianScalar_comm (fun z => u z 1) hu1 x 2,
        laplacianScalar_sub
          (fun y => partialDerivScalar (fun z => u z 2) y 1)
          (fun y => partialDerivScalar (fun z => u z 1) y 2)
          (fun y => contDiffAt_two_partialDerivScalar (fun z => u z 2) y (hu2 y) 1)
          (fun y => contDiffAt_two_partialDerivScalar (fun z => u z 1) y (hu1 y) 2) x]
  | ⟨1, _⟩ =>
    change partialDerivScalar (fun y => laplacianScalar (fun z => u z 0) y) x 2 -
           partialDerivScalar (fun y => laplacianScalar (fun z => u z 2) y) x 0 =
           laplacianScalar (fun y => partialDerivScalar (fun z => u z 0) y 2 -
                                     partialDerivScalar (fun z => u z 2) y 0) x
    rw [partial_laplacianScalar_comm (fun z => u z 0) hu0 x 2,
        partial_laplacianScalar_comm (fun z => u z 2) hu2 x 0,
        laplacianScalar_sub
          (fun y => partialDerivScalar (fun z => u z 0) y 2)
          (fun y => partialDerivScalar (fun z => u z 2) y 0)
          (fun y => contDiffAt_two_partialDerivScalar (fun z => u z 0) y (hu0 y) 2)
          (fun y => contDiffAt_two_partialDerivScalar (fun z => u z 2) y (hu2 y) 0) x]
  | ⟨2, _⟩ =>
    change partialDerivScalar (fun y => laplacianScalar (fun z => u z 1) y) x 0 -
           partialDerivScalar (fun y => laplacianScalar (fun z => u z 0) y) x 1 =
           laplacianScalar (fun y => partialDerivScalar (fun z => u z 1) y 0 -
                                     partialDerivScalar (fun z => u z 0) y 1) x
    rw [partial_laplacianScalar_comm (fun z => u z 1) hu1 x 0,
        partial_laplacianScalar_comm (fun z => u z 0) hu0 x 1,
        laplacianScalar_sub
          (fun y => partialDerivScalar (fun z => u z 1) y 0)
          (fun y => partialDerivScalar (fun z => u z 0) y 1)
          (fun y => contDiffAt_two_partialDerivScalar (fun z => u z 1) y (hu1 y) 0)
          (fun y => contDiffAt_two_partialDerivScalar (fun z => u z 0) y (hu0 y) 1) x]

-- ============================================================================
-- SECTION 5: CLASSICAL C³ NAVIER-STOKES & THE 3D VORTICITY EQUATION THEOREM
-- ============================================================================

/-- Classical `C³` spatial / `C²` space-time incompressible 3D Navier-Stokes solution,
    extending Milestone 1's `IsClassicalNS3D` with the exact regularity required to take
    the spatial curl of the momentum PDE. -/
structure IsClassicalNS3D_C3 (u : ℝ → R3 → R3) (p : ℝ → R3 → ℝ) (ν : ℝ) : Prop
    extends IsClassicalNS3D u p ν where
  h_u_c3_space : ∀ t ≥ 0, ∀ x : R3, ContDiffAt ℝ 3 (u t) x
  h_u_c2_spacetime : ∀ q : ℝ × R3, ContDiffAt ℝ 2 (fun r : ℝ × R3 => u r.1 r.2) q

/-- Non-vacuity witness for `IsClassicalNS3D_C3`: any steady uniform flow satisfies it. -/
theorem steadyUniformFlow_isClassicalNS3D_C3 (c : R3) (p₀ ν : ℝ) (hν : 0 < ν) :
    IsClassicalNS3D_C3 (fun _ _ => c) (fun _ _ => p₀) ν where
  toIsClassicalNS3D := steadyUniformFlow_isClassicalNS3D c p₀ ν hν
  h_u_c3_space := fun _ _ _ => contDiffAt_const
  h_u_c2_spacetime := fun _ => contDiffAt_const

/-- Vorticity field `ω(t, x) = ∇ × u(t, x)` is automatically divergence-free (`∇ · ω = 0`). -/
theorem vorticity_is_solenoidal
    {u : ℝ → R3 → R3} {p : ℝ → R3 → ℝ} {ν : ℝ}
    (hns : IsClassicalNS3D u p ν) {t : ℝ} (ht : t ≥ 0) (x : R3) :
    div3D (curl3D (u t)) x = 0 :=
  div3D_curl3D_eq_zero (u t) x (hns.h_u_smooth t ht x)

/-- **MAIN THEOREM OF MILESTONE 2 (3D Incompressible Navier-Stokes Vorticity Equation):**
    For any classical solution `(u, p)` of `IsClassicalNS3D_C3 u p ν` with vorticity
    `ω(t, x) = curl3D (u t) x`, the pressure gradient annihilates identically (`∇ × ∇p = 0`)
    and `ω` obeys the exact 3D vorticity transport and vortex-stretching PDE:
      `∂_t ω + (u · ∇)ω - (ω · ∇)u = ν Δω`
    at every `t ≥ 0`, `x ∈ ℝ³`, and coordinate component `comp ∈ {0, 1, 2}` (`0 sorryAx`). -/
theorem navier_stokes_3d_vorticity_equation
    {u : ℝ → R3 → R3} {p : ℝ → R3 → ℝ} {ν : ℝ}
    (hns : IsClassicalNS3D_C3 u p ν) {t : ℝ} (ht : t ≥ 0) (x : R3) (comp : Fin 3) :
    deriv (fun s => curl3D (u s) x comp) t +
      directionalAdvection3D (u t) (curl3D (u t)) x comp -
      directionalAdvection3D (curl3D (u t)) (u t) x comp =
      ν * laplacian3D (curl3D (u t)) x comp := by
  let ut_field : R3 → R3 := fun y c => deriv (fun s => u s y c) t
  let adv_field : R3 → R3 := advection3D (u t)
  let gp_field : R3 → R3 := grad3D (p t)
  let lap_field : R3 → R3 := laplacian3D (u t)
  have h_ut_diff : DifferentiableAt ℝ ut_field x := by
    refine differentiableAt_pi.mpr fun c => ?_
    have hFc : ∀ q : ℝ × R3, ContDiffAt ℝ 2 (fun r : ℝ × R3 => u r.1 r.2 c) q :=
      fun q => contDiffAt_pi.mp (hns.h_u_c2_spacetime q) c
    exact (hasFDerivAt_timeDeriv_space (fun r => u r.1 r.2 c) hFc t x).differentiableAt
  have h_adv_diff : DifferentiableAt ℝ adv_field x :=
    differentiableAt_advection3D (u t) x (hns.h_u_smooth t ht x)
  have h_gp_diff : DifferentiableAt ℝ gp_field x := by
    refine differentiableAt_pi.mpr fun c => ?_
    exact (hasFDerivAt_partialDerivScalar (p t) x (hns.h_p_smooth t ht x) c).differentiableAt
  have h_lap_diff : DifferentiableAt ℝ lap_field x :=
    differentiableAt_laplacian3D (u t) (hns.h_u_c3_space t ht) x
  have h_mom_fun :
      (fun y c => (ut_field y c + adv_field y c) + gp_field y c) =
      (fun y c => ν * lap_field y c) := by
    funext y c
    exact hns.h_momentum t ht y c
  have h_curl_eq :
      curl3D (fun y c => (ut_field y c + adv_field y c) + gp_field y c) x comp =
      curl3D (fun y c => ν * lap_field y c) x comp :=
    congrArg (fun f => curl3D f x comp) h_mom_fun
  have h_ut_adv_diff : DifferentiableAt ℝ (fun y c => ut_field y c + adv_field y c) x :=
    h_ut_diff.add h_adv_diff
  rw [curl3D_add h_ut_adv_diff h_gp_diff comp,
      curl3D_add h_ut_diff h_adv_diff comp,
      curl3D_const_mul ν h_lap_diff comp] at h_curl_eq
  have h_p_zero : curl3D gp_field x comp = 0 := by
    have hp0 := curl3D_grad3D_eq_zero (p t) x (hns.h_p_smooth t ht x)
    have hcomp : curl3D gp_field x comp = vec3 0 0 0 comp := congrArg (fun v => v comp) hp0
    rw [hcomp]
    match comp with
    | ⟨0, _⟩ => rfl
    | ⟨1, _⟩ => rfl
    | ⟨2, _⟩ => rfl
  have h_time : curl3D ut_field x comp = deriv (fun s => curl3D (u s) x comp) t :=
    curl3D_timeDeriv_eq_timeDeriv_curl3D u hns.h_u_c2_spacetime t x comp
  have h_adv : curl3D adv_field x comp =
      directionalAdvection3D (u t) (curl3D (u t)) x comp -
      directionalAdvection3D (curl3D (u t)) (u t) x comp := by
    rw [curl3D_advection3D (u t) x (hns.h_u_smooth t ht x) comp,
        hns.h_incompressible t ht x, zero_mul, add_zero]
  have h_lap : curl3D lap_field x comp = laplacian3D (curl3D (u t)) x comp :=
    curl3D_laplacian3D (u t) (hns.h_u_c3_space t ht) x comp
  rw [h_time, h_adv, h_p_zero, add_zero, h_lap] at h_curl_eq
  linarith [h_curl_eq]

-- ============================================================================
-- SECTION 6: AXIOM AUDIT TRAIL (0 sorryAx)
-- ============================================================================

#print axioms curl3D_timeDeriv_eq_timeDeriv_curl3D
#print axioms curl3D_advection3D
#print axioms curl3D_laplacian3D
#print axioms vorticity_is_solenoidal
#print axioms steadyUniformFlow_isClassicalNS3D_C3
#print axioms navier_stokes_3d_vorticity_equation

end GarryVorticity3D