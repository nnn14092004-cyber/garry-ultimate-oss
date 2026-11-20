import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import VorticityEquation3D

/-!
# GARRYULT v4.0.0 — Milestone 3: Measure-Theoretic Leray Energy & 3D Enstrophy Evolution on `𝕋³`
Formalizes the true 3D Lebesgue integral over the periodic unit torus `𝕋³ = [0, 1]³` using
Mathlib4 `MeasureTheory` + Fubini + Fundamental Theorem of Calculus, proving with `0 sorryAx`:
1. 3D Periodic Divergence Theorem (`∫_{𝕋³} div F = 0`) and Integration by Parts.
2. Real Analytical Lemma 1 (Gauss-Leray): `∫_{𝕋³} ⟨(v · ∇)w, w⟩ = 0` for `div v = 0`.
3. Pressure work cancellation (`∫_{𝕋³} ⟨∇p, u⟩ = 0`) and viscous Laplacian dissipation
   (`∫_{𝕋³} ⟨Δw, w⟩ = -∫_{𝕋³} |∇w|² ≤ 0`).
4. Classical Leray Energy Identity (`∫_{𝕋³} ⟨∂_t u, u⟩ = -ν ∫_{𝕋³} |∇u|² ≤ 0`).
5. Exact 3D Enstrophy Evolution Identity derived from Milestone 2's vorticity PDE:
   `∫_{𝕋³} ⟨∂_t ω, ω⟩ = ∫_{𝕋³} ⟨(ω · ∇)u, ω⟩ - ν ∫_{𝕋³} |∇ω|²`.
-/

namespace GarryLerayTorus3D

open MeasureTheory GarryReal3DCalculus GarryVorticity3D

-- ============================================================================
-- SECTION 1: 3D TORUS INTEGRAL `𝕋³ = [0, 1]³` & PERIODICITY STRUCTURE
-- ============================================================================

/-- 1-periodicity along all three spatial coordinate axes of `ℝ³`. -/
def IsPeriodic3D {α : Type*} (f : R3 → α) : Prop :=
  ∀ (x : R3) (i : Fin 3), f (x + basisVec i) = f x

/-- True 3D Lebesgue integral over the unit torus `𝕋³ = [0, 1]³` via iterated interval integrals. -/
noncomputable def torusIntegral (f : R3 → ℝ) : ℝ :=
  ∫ x in (0 : ℝ)..1, ∫ y in (0 : ℝ)..1, ∫ z in (0 : ℝ)..1, f (vec3 x y z)

/-- Pointwise Frobenius norm squared of the 3×3 spatial Jacobian `|∇w(x)|²`. -/
noncomputable def gradNormSq3D (w : R3 → R3) (x : R3) : ℝ :=
  (partialDerivScalar (fun y => w y 0) x 0) ^ 2 +
  (partialDerivScalar (fun y => w y 0) x 1) ^ 2 +
  (partialDerivScalar (fun y => w y 0) x 2) ^ 2 +
  (partialDerivScalar (fun y => w y 1) x 0) ^ 2 +
  (partialDerivScalar (fun y => w y 1) x 1) ^ 2 +
  (partialDerivScalar (fun y => w y 1) x 2) ^ 2 +
  (partialDerivScalar (fun y => w y 2) x 0) ^ 2 +
  (partialDerivScalar (fun y => w y 2) x 1) ^ 2 +
  (partialDerivScalar (fun y => w y 2) x 2) ^ 2

theorem gradNormSq3D_nonneg (w : R3 → R3) (x : R3) : 0 ≤ gradNormSq3D w x := by
  unfold gradNormSq3D
  have h00 : 0 ≤ (partialDerivScalar (fun y => w y 0) x 0) ^ 2 := sq_nonneg _
  have h01 : 0 ≤ (partialDerivScalar (fun y => w y 0) x 1) ^ 2 := sq_nonneg _
  have h02 : 0 ≤ (partialDerivScalar (fun y => w y 0) x 2) ^ 2 := sq_nonneg _
  have h10 : 0 ≤ (partialDerivScalar (fun y => w y 1) x 0) ^ 2 := sq_nonneg _
  have h11 : 0 ≤ (partialDerivScalar (fun y => w y 1) x 1) ^ 2 := sq_nonneg _
  have h12 : 0 ≤ (partialDerivScalar (fun y => w y 1) x 2) ^ 2 := sq_nonneg _
  have h20 : 0 ≤ (partialDerivScalar (fun y => w y 2) x 0) ^ 2 := sq_nonneg _
  have h21 : 0 ≤ (partialDerivScalar (fun y => w y 2) x 1) ^ 2 := sq_nonneg _
  have h22 : 0 ≤ (partialDerivScalar (fun y => w y 2) x 2) ^ 2 := sq_nonneg _
  linarith

private lemma two_add_one_eq_three' {α : Type*} [AddMonoidWithOne α] :
    (2 : α) + 1 = 3 := by
  rw [← Nat.cast_ofNat (n := 2), ← Nat.cast_one, ← Nat.cast_add]
  exact Nat.cast_ofNat

private lemma contDiff_one_of_two {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {f : E → F} (hf : ContDiff ℝ 2 f) :
    ContDiff ℝ 1 f :=
  hf.of_le (by rw [← one_add_one_eq_two]; exact le_self_add)

private lemma contDiff_two_of_three {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {f : E → F} (hf : ContDiff ℝ 3 f) :
    ContDiff ℝ 2 f :=
  hf.of_le (by rw [← two_add_one_eq_three']; exact le_self_add)

private lemma differentiable_of_contDiff_one {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {f : E → F} (hf : ContDiff ℝ 1 f) :
    Differentiable ℝ f :=
  hf.differentiable (by simp)

theorem continuous_partialDerivScalar_of_contDiff
    {f : R3 → ℝ} (hf : ContDiff ℝ 1 f) (j : Fin 3) :
    Continuous (fun x => partialDerivScalar f x j) := by
  have h0 : ContDiff ℝ 0 (fderiv ℝ f) := hf.fderiv_right (by simp)
  exact (ContinuousLinearMap.apply ℝ ℝ (basisVec j)).continuous.comp h0.continuous

theorem contDiff_one_partialDerivScalar
    {f : R3 → ℝ} (hf : ContDiff ℝ 2 f) (j : Fin 3) :
    ContDiff ℝ 1 (fun x => partialDerivScalar f x j) := by
  have h1 : ContDiff ℝ 1 (fderiv ℝ f) := hf.fderiv_right (by simp [one_add_one_eq_two])
  exact (ContinuousLinearMap.apply ℝ ℝ (basisVec j)).contDiff.comp h1

theorem contDiff_two_partialDerivScalar
    {f : R3 → ℝ} (hf : ContDiff ℝ 3 f) (j : Fin 3) :
    ContDiff ℝ 2 (fun x => partialDerivScalar f x j) := by
  have h2 : ContDiff ℝ 2 (fderiv ℝ f) := hf.fderiv_right (le_of_eq two_add_one_eq_three')
  exact (ContinuousLinearMap.apply ℝ ℝ (basisVec j)).contDiff.comp h2

theorem continuous_sndPartial_of_contDiff
    {f : R3 → ℝ} (hf : ContDiff ℝ 2 f) (i j : Fin 3) :
    Continuous (fun x => sndPartial f x i j) := by
  have h_eq : (fun x => sndPartial f x i j) =
      (fun x => partialDerivScalar (fun y => partialDerivScalar f y j) x i) := by
    funext x
    exact (partial_partial_eq_sndPartial f x hf.contDiffAt i j).symm
  rw [h_eq]
  exact continuous_partialDerivScalar_of_contDiff (contDiff_one_partialDerivScalar hf j) i

theorem contDiff_two_curl3D {u : R3 → R3} (hu : ContDiff ℝ 3 u) :
    ContDiff ℝ 2 (curl3D u) := by
  have hu0 : ContDiff ℝ 3 (fun y => u y 0) := contDiff_pi.mp hu 0
  have hu1 : ContDiff ℝ 3 (fun y => u y 1) := contDiff_pi.mp hu 1
  have hu2 : ContDiff ℝ 3 (fun y => u y 2) := contDiff_pi.mp hu 2
  refine contDiff_pi.mpr fun comp => ?_
  match comp with
  | ⟨0, _⟩ =>
    exact (contDiff_two_partialDerivScalar hu2 1).sub (contDiff_two_partialDerivScalar hu1 2)
  | ⟨1, _⟩ =>
    exact (contDiff_two_partialDerivScalar hu0 2).sub (contDiff_two_partialDerivScalar hu2 0)
  | ⟨2, _⟩ =>
    exact (contDiff_two_partialDerivScalar hu1 0).sub (contDiff_two_partialDerivScalar hu0 1)

theorem continuous_dot3D {v w : R3 → R3} (hv : Continuous v) (hw : Continuous w) :
    Continuous (fun x => dot3D (v x) (w x)) := by
  unfold dot3D
  have hv0 : Continuous (fun x => v x 0) := (continuous_apply 0).comp hv
  have hv1 : Continuous (fun x => v x 1) := (continuous_apply 1).comp hv
  have hv2 : Continuous (fun x => v x 2) := (continuous_apply 2).comp hv
  have hw0 : Continuous (fun x => w x 0) := (continuous_apply 0).comp hw
  have hw1 : Continuous (fun x => w x 1) := (continuous_apply 1).comp hw
  have hw2 : Continuous (fun x => w x 2) := (continuous_apply 2).comp hw
  exact ((hv0.mul hw0).add (hv1.mul hw1)).add (hv2.mul hw2)

theorem continuous_grad3D {p : R3 → ℝ} (hp : ContDiff ℝ 1 p) : Continuous (grad3D p) :=
  continuous_pi fun i => continuous_partialDerivScalar_of_contDiff hp i

theorem continuous_directionalAdvection3D
    {v w : R3 → R3} (hv : Continuous v) (hw : ContDiff ℝ 1 w) :
    Continuous (directionalAdvection3D v w) := by
  refine continuous_pi fun comp => ?_
  have hwc : ContDiff ℝ 1 (fun y => w y comp) := contDiff_pi.mp hw comp
  have hv0 : Continuous (fun x => v x 0) := (continuous_apply 0).comp hv
  have hv1 : Continuous (fun x => v x 1) := (continuous_apply 1).comp hv
  have hv2 : Continuous (fun x => v x 2) := (continuous_apply 2).comp hv
  exact ((hv0.mul (continuous_partialDerivScalar_of_contDiff hwc 0)).add
         (hv1.mul (continuous_partialDerivScalar_of_contDiff hwc 1))).add
        (hv2.mul (continuous_partialDerivScalar_of_contDiff hwc 2))

theorem continuous_advection3D {u : R3 → R3} (hu : ContDiff ℝ 1 u) :
    Continuous (advection3D u) :=
  continuous_directionalAdvection3D hu.continuous hu

theorem continuous_laplacian3D {w : R3 → R3} (hw : ContDiff ℝ 2 w) :
    Continuous (laplacian3D w) := by
  refine continuous_pi fun comp => ?_
  have hwc : ContDiff ℝ 2 (fun y => w y comp) := contDiff_pi.mp hw comp
  exact ((continuous_sndPartial_of_contDiff hwc 0 0).add
         (continuous_sndPartial_of_contDiff hwc 1 1)).add
        (continuous_sndPartial_of_contDiff hwc 2 2)

theorem continuous_gradNormSq3D {w : R3 → R3} (hw : ContDiff ℝ 1 w) :
    Continuous (gradNormSq3D w) := by
  have hw0 : ContDiff ℝ 1 (fun y => w y 0) := contDiff_pi.mp hw 0
  have hw1 : ContDiff ℝ 1 (fun y => w y 1) := contDiff_pi.mp hw 1
  have hw2 : ContDiff ℝ 1 (fun y => w y 2) := contDiff_pi.mp hw 2
  unfold gradNormSq3D
  exact ((((((((continuous_partialDerivScalar_of_contDiff hw0 0).pow 2).add
    ((continuous_partialDerivScalar_of_contDiff hw0 1).pow 2)).add
    ((continuous_partialDerivScalar_of_contDiff hw0 2).pow 2)).add
    ((continuous_partialDerivScalar_of_contDiff hw1 0).pow 2)).add
    ((continuous_partialDerivScalar_of_contDiff hw1 1).pow 2)).add
    ((continuous_partialDerivScalar_of_contDiff hw1 2).pow 2)).add
    ((continuous_partialDerivScalar_of_contDiff hw2 0).pow 2)).add
    ((continuous_partialDerivScalar_of_contDiff hw2 1).pow 2) |>.add
    ((continuous_partialDerivScalar_of_contDiff hw2 2).pow 2)

-- Periodicity closure lemmas

theorem IsPeriodic3D.comp {α β : Type*} {f : R3 → α} (hf : IsPeriodic3D f) (g : α → β) :
    IsPeriodic3D (fun x => g (f x)) := fun x i => congrArg g (hf x i)

theorem IsPeriodic3D.mul {f g : R3 → ℝ} (hf : IsPeriodic3D f) (hg : IsPeriodic3D g) :
    IsPeriodic3D (fun x => f x * g x) := fun x i => by
  dsimp only
  rw [hf x i, hg x i]

theorem IsPeriodic3D.sub {f g : R3 → ℝ} (hf : IsPeriodic3D f) (hg : IsPeriodic3D g) :
    IsPeriodic3D (fun x => f x - g x) := fun x i => by
  dsimp only
  rw [hf x i, hg x i]

theorem IsPeriodic3D.partialDeriv
    {f : R3 → ℝ} (hper : IsPeriodic3D f) (hf : Differentiable ℝ f) (j : Fin 3) :
    IsPeriodic3D (fun x => partialDerivScalar f x j) := by
  intro x i
  have hshift : (fun y : R3 => f (y + basisVec i)) = f := by
    funext y
    exact hper y i
  have htr : HasFDerivAt (fun y : R3 => y + basisVec i) (ContinuousLinearMap.id ℝ R3) x :=
    (hasFDerivAt_id x).add_const (basisVec i)
  have hcomp : HasFDerivAt (fun y : R3 => f (y + basisVec i))
      ((fderiv ℝ f (x + basisVec i)).comp (ContinuousLinearMap.id ℝ R3)) x :=
    (hf (x + basisVec i)).hasFDerivAt.comp x htr
  rw [hshift] at hcomp
  have hfderiv_eq : fderiv ℝ f x = fderiv ℝ f (x + basisVec i) := by
    simpa using hcomp.fderiv
  change fderiv ℝ f (x + basisVec i) (basisVec j) = fderiv ℝ f x (basisVec j)
  rw [← hfderiv_eq]

theorem IsPeriodic3D.curl3D
    {u : R3 → R3} (hper : IsPeriodic3D u) (hu : Differentiable ℝ u) :
    IsPeriodic3D (curl3D u) := by
  have hp0 : IsPeriodic3D (fun y => u y 0) := fun x i => congrArg (fun v => v 0) (hper x i)
  have hp1 : IsPeriodic3D (fun y => u y 1) := fun x i => congrArg (fun v => v 1) (hper x i)
  have hp2 : IsPeriodic3D (fun y => u y 2) := fun x i => congrArg (fun v => v 2) (hper x i)
  have hd0 : Differentiable ℝ (fun y => u y 0) := fun x => differentiableAt_pi.mp (hu x) 0
  have hd1 : Differentiable ℝ (fun y => u y 1) := fun x => differentiableAt_pi.mp (hu x) 1
  have hd2 : Differentiable ℝ (fun y => u y 2) := fun x => differentiableAt_pi.mp (hu x) 2
  intro x i
  funext comp
  match comp with
  | ⟨0, _⟩ =>
    have e1 : partialDerivScalar (fun y => u y 2) (x + basisVec i) 1 =
        partialDerivScalar (fun y => u y 2) x 1 := IsPeriodic3D.partialDeriv hp2 hd2 1 x i
    have e2 : partialDerivScalar (fun y => u y 1) (x + basisVec i) 2 =
        partialDerivScalar (fun y => u y 1) x 2 := IsPeriodic3D.partialDeriv hp1 hd1 2 x i
    change partialDerivScalar (fun y => u y 2) (x + basisVec i) 1 -
           partialDerivScalar (fun y => u y 1) (x + basisVec i) 2 =
           partialDerivScalar (fun y => u y 2) x 1 -
           partialDerivScalar (fun y => u y 1) x 2
    rw [e1, e2]
  | ⟨1, _⟩ =>
    have e1 : partialDerivScalar (fun y => u y 0) (x + basisVec i) 2 =
        partialDerivScalar (fun y => u y 0) x 2 := IsPeriodic3D.partialDeriv hp0 hd0 2 x i
    have e2 : partialDerivScalar (fun y => u y 2) (x + basisVec i) 0 =
        partialDerivScalar (fun y => u y 2) x 0 := IsPeriodic3D.partialDeriv hp2 hd2 0 x i
    change partialDerivScalar (fun y => u y 0) (x + basisVec i) 2 -
           partialDerivScalar (fun y => u y 2) (x + basisVec i) 0 =
           partialDerivScalar (fun y => u y 0) x 2 -
           partialDerivScalar (fun y => u y 2) x 0
    rw [e1, e2]
  | ⟨2, _⟩ =>
    have e1 : partialDerivScalar (fun y => u y 1) (x + basisVec i) 0 =
        partialDerivScalar (fun y => u y 1) x 0 := IsPeriodic3D.partialDeriv hp1 hd1 0 x i
    have e2 : partialDerivScalar (fun y => u y 0) (x + basisVec i) 1 =
        partialDerivScalar (fun y => u y 0) x 1 := IsPeriodic3D.partialDeriv hp0 hd0 1 x i
    change partialDerivScalar (fun y => u y 1) (x + basisVec i) 0 -
           partialDerivScalar (fun y => u y 0) (x + basisVec i) 1 =
           partialDerivScalar (fun y => u y 1) x 0 -
           partialDerivScalar (fun y => u y 0) x 1
    rw [e1, e2]

-- ============================================================================
-- SECTION 2: MEASURE-THEORETIC PRODUCT REPRESENTATION & LINEARITY OF `torusIntegral`
-- ============================================================================

private noncomputable abbrev unitMeas : Measure ℝ := volume.restrict (Set.Icc (0 : ℝ) 1)

private theorem continuous_vec3_triple :
    Continuous (fun q : ℝ × (ℝ × ℝ) => vec3 q.1 q.2.1 q.2.2) := by
  refine continuous_pi fun i => ?_
  match i with
  | ⟨0, _⟩ => exact continuous_fst
  | ⟨1, _⟩ => exact continuous_fst.comp continuous_snd
  | ⟨2, _⟩ => exact continuous_snd.comp continuous_snd

private theorem continuous_vec3_yz (x : ℝ) :
    Continuous (fun p : ℝ × ℝ => vec3 x p.1 p.2) := by
  refine continuous_pi fun i => ?_
  match i with
  | ⟨0, _⟩ => exact continuous_const
  | ⟨1, _⟩ => exact continuous_fst
  | ⟨2, _⟩ => exact continuous_snd

private theorem intervalIntegral_eq_unitMeas (h : ℝ → ℝ) :
    ∫ t in (0 : ℝ)..1, h t = ∫ t, h t ∂unitMeas := by
  rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1),
      ← MeasureTheory.integral_Icc_eq_integral_Ioc]

private theorem integrable_unitMeas_prod2 {g : ℝ × ℝ → ℝ} (hg : Continuous g) :
    Integrable g (unitMeas.prod unitMeas) := by
  have hprod : unitMeas.prod unitMeas =
      (volume : Measure (ℝ × ℝ)).restrict (Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1) := by
    rw [Measure.prod_restrict]
    rfl
  rw [hprod]
  exact hg.continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)

private theorem integrable_unitMeas_prod3 {g : R3 → ℝ} (hg : Continuous g) :
    Integrable (fun q : ℝ × (ℝ × ℝ) => g (vec3 q.1 q.2.1 q.2.2))
      (unitMeas.prod (unitMeas.prod unitMeas)) := by
  have hprod : unitMeas.prod (unitMeas.prod unitMeas) =
      (volume : Measure (ℝ × (ℝ × ℝ))).restrict
        (Set.Icc (0 : ℝ) 1 ×ˢ (Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1)) := by
    rw [Measure.prod_restrict, Measure.prod_restrict]
    rfl
  rw [hprod]
  exact (hg.comp continuous_vec3_triple).continuousOn.integrableOn_compact
    (isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc))

private theorem torusIntegral_eq_prod3 {g : R3 → ℝ} (hg : Continuous g) :
    torusIntegral g =
      ∫ q : ℝ × (ℝ × ℝ), g (vec3 q.1 q.2.1 q.2.2) ∂(unitMeas.prod (unitMeas.prod unitMeas)) := by
  unfold torusIntegral
  simp_rw [intervalIntegral_eq_unitMeas]
  have h_inner : ∀ x : ℝ,
      (∫ y, (∫ z, g (vec3 x y z) ∂unitMeas) ∂unitMeas) =
      ∫ p : ℝ × ℝ, g (vec3 x p.1 p.2) ∂(unitMeas.prod unitMeas) := fun x => by
    exact (MeasureTheory.integral_prod (fun p : ℝ × ℝ => g (vec3 x p.1 p.2))
      (integrable_unitMeas_prod2 (hg.comp (continuous_vec3_yz x)))).symm
  simp_rw [h_inner]
  exact (MeasureTheory.integral_prod (fun q : ℝ × (ℝ × ℝ) => g (vec3 q.1 q.2.1 q.2.2))
    (integrable_unitMeas_prod3 hg)).symm

theorem torusIntegral_add {f g : R3 → ℝ} (hf : Continuous f) (hg : Continuous g) :
    torusIntegral (fun x => f x + g x) = torusIntegral f + torusIntegral g := by
  have hfg : Continuous (fun x => f x + g x) := hf.add hg
  rw [torusIntegral_eq_prod3 hfg, torusIntegral_eq_prod3 hf, torusIntegral_eq_prod3 hg]
  exact MeasureTheory.integral_add (integrable_unitMeas_prod3 hf) (integrable_unitMeas_prod3 hg)

theorem torusIntegral_add3 {f g h : R3 → ℝ}
    (hf : Continuous f) (hg : Continuous g) (hh : Continuous h) :
    torusIntegral (fun x => f x + g x + h x) =
      torusIntegral f + torusIntegral g + torusIntegral h := by
  have hfg : Continuous (fun x => f x + g x) := hf.add hg
  rw [torusIntegral_add hfg hh, torusIntegral_add hf hg]

theorem torusIntegral_sub {f g : R3 → ℝ} (hf : Continuous f) (hg : Continuous g) :
    torusIntegral (fun x => f x - g x) = torusIntegral f - torusIntegral g := by
  have hfg : Continuous (fun x => f x - g x) := hf.sub hg
  rw [torusIntegral_eq_prod3 hfg, torusIntegral_eq_prod3 hf, torusIntegral_eq_prod3 hg]
  exact MeasureTheory.integral_sub (integrable_unitMeas_prod3 hf) (integrable_unitMeas_prod3 hg)

theorem torusIntegral_const_mul {f : R3 → ℝ} (c : ℝ) (hf : Continuous f) :
    torusIntegral (fun x => c * f x) = c * torusIntegral f := by
  have hcf : Continuous (fun x => c * f x) := continuous_const.mul hf
  rw [torusIntegral_eq_prod3 hcf, torusIntegral_eq_prod3 hf]
  exact MeasureTheory.integral_const_mul c _

theorem torusIntegral_neg {f : R3 → ℝ} (hf : Continuous f) :
    torusIntegral (fun x => -f x) = -torusIntegral f := by
  have h := torusIntegral_const_mul (-1) hf
  simpa using h

theorem torusIntegral_nonneg {f : R3 → ℝ} (hf : Continuous f) (hnn : ∀ x : R3, 0 ≤ f x) :
    0 ≤ torusIntegral f := by
  rw [torusIntegral_eq_prod3 hf]
  exact MeasureTheory.integral_nonneg (fun q => hnn (vec3 q.1 q.2.1 q.2.2))

theorem torusIntegral_congr {f g : R3 → ℝ} (h : ∀ x : R3, f x = g x) :
    torusIntegral f = torusIntegral g := by
  have hfun : f = g := funext h
  rw [hfun]

-- ============================================================================
-- SECTION 3: 3D PERIODIC FTC, FUBINI, DIVERGENCE THEOREM & INTEGRATION BY PARTS
-- ============================================================================

private theorem vec3_one_zero_eq_add_basis0 (y z : ℝ) :
    vec3 1 y z = vec3 0 y z + basisVec 0 := by
  funext i; match i with | ⟨0, _⟩ => simp [vec3, basisVec] | ⟨1, _⟩ => simp [vec3, basisVec] | ⟨2, _⟩ => simp [vec3, basisVec]

private theorem vec3_one_zero_eq_add_basis1 (x z : ℝ) :
    vec3 x 1 z = vec3 x 0 z + basisVec 1 := by
  funext i; match i with | ⟨0, _⟩ => simp [vec3, basisVec] | ⟨1, _⟩ => simp [vec3, basisVec] | ⟨2, _⟩ => simp [vec3, basisVec]

private theorem vec3_one_zero_eq_add_basis2 (x y : ℝ) :
    vec3 x y 1 = vec3 x y 0 + basisVec 2 := by
  funext i; match i with | ⟨0, _⟩ => simp [vec3, basisVec] | ⟨1, _⟩ => simp [vec3, basisVec] | ⟨2, _⟩ => simp [vec3, basisVec]

private theorem hasDerivAt_vec3_x (y z t : ℝ) :
    HasDerivAt (fun s => vec3 s y z) (basisVec 0) t := by
  refine hasDerivAt_pi.mpr fun k => ?_
  match k with
  | ⟨0, _⟩ =>
    change HasDerivAt (fun s : ℝ => s) 1 t
    exact hasDerivAt_id t
  | ⟨1, _⟩ =>
    change HasDerivAt (fun _ : ℝ => y) 0 t
    exact hasDerivAt_const t y
  | ⟨2, _⟩ =>
    change HasDerivAt (fun _ : ℝ => z) 0 t
    exact hasDerivAt_const t z

private theorem hasDerivAt_vec3_y (x z t : ℝ) :
    HasDerivAt (fun s => vec3 x s z) (basisVec 1) t := by
  refine hasDerivAt_pi.mpr fun k => ?_
  match k with
  | ⟨0, _⟩ =>
    change HasDerivAt (fun _ : ℝ => x) 0 t
    exact hasDerivAt_const t x
  | ⟨1, _⟩ =>
    change HasDerivAt (fun s : ℝ => s) 1 t
    exact hasDerivAt_id t
  | ⟨2, _⟩ =>
    change HasDerivAt (fun _ : ℝ => z) 0 t
    exact hasDerivAt_const t z

private theorem hasDerivAt_vec3_z (x y t : ℝ) :
    HasDerivAt (fun s => vec3 x y s) (basisVec 2) t := by
  refine hasDerivAt_pi.mpr fun k => ?_
  match k with
  | ⟨0, _⟩ =>
    change HasDerivAt (fun _ : ℝ => x) 0 t
    exact hasDerivAt_const t x
  | ⟨1, _⟩ =>
    change HasDerivAt (fun _ : ℝ => y) 0 t
    exact hasDerivAt_const t y
  | ⟨2, _⟩ =>
    change HasDerivAt (fun s : ℝ => s) 1 t
    exact hasDerivAt_id t

private theorem intervalIntegral_swap_unit {g : ℝ → ℝ → ℝ}
    (hg : Continuous (fun p : ℝ × ℝ => g p.1 p.2)) :
    (∫ a in (0 : ℝ)..1, ∫ b in (0 : ℝ)..1, g a b) =
    ∫ b in (0 : ℝ)..1, ∫ a in (0 : ℝ)..1, g a b := by
  simp_rw [intervalIntegral_eq_unitMeas]
  exact MeasureTheory.integral_integral_swap (integrable_unitMeas_prod2 hg)

/-- **3D Periodic FTC + Fubini Theorem:** For any `C¹` periodic scalar field `f` on `𝕋³`,
    the integral of every spatial partial derivative `∂_i f` over `𝕋³` vanishes identically. -/
theorem torusIntegral_partialDeriv_eq_zero
    {f : R3 → ℝ} (hf : ContDiff ℝ 1 f) (hper : IsPeriodic3D f) (i : Fin 3) :
    torusIntegral (fun x => partialDerivScalar f x i) = 0 := by
  have hdiff : Differentiable ℝ f := differentiable_of_contDiff_one hf
  fin_cases i
  · have hcont : Continuous (fun x => partialDerivScalar f x 0) :=
      continuous_partialDerivScalar_of_contDiff hf 0
    have hswap : torusIntegral (fun x => partialDerivScalar f x 0) =
        ∫ p : ℝ × ℝ, (∫ x, partialDerivScalar f (vec3 x p.1 p.2) 0 ∂unitMeas) ∂(unitMeas.prod unitMeas) := by
      rw [torusIntegral_eq_prod3 hcont,
          MeasureTheory.integral_prod (fun q : ℝ × (ℝ × ℝ) => partialDerivScalar f (vec3 q.1 q.2.1 q.2.2) 0)
            (integrable_unitMeas_prod3 hcont)]
      exact MeasureTheory.integral_integral_swap (integrable_unitMeas_prod3 hcont)
    change torusIntegral (fun x => partialDerivScalar f x 0) = 0
    rw [hswap]
    have hinner : ∀ p : ℝ × ℝ, ∫ x, partialDerivScalar f (vec3 x p.1 p.2) 0 ∂unitMeas = 0 := by
      intro p
      rw [← intervalIntegral_eq_unitMeas]
      have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt
        (a := (0 : ℝ)) (b := 1)
        (f := fun s => f (vec3 s p.1 p.2))
        (f' := fun s => partialDerivScalar f (vec3 s p.1 p.2) 0)
        (fun s _ => (hdiff (vec3 s p.1 p.2)).hasFDerivAt.comp_hasDerivAt s (hasDerivAt_vec3_x p.1 p.2 s))
        ((hcont.comp (continuous_pi fun k => match k with
          | ⟨0, _⟩ => continuous_id
          | ⟨1, _⟩ => continuous_const
          | ⟨2, _⟩ => continuous_const)).intervalIntegrable 0 1)
      rw [hftc, vec3_one_zero_eq_add_basis0, hper (vec3 0 p.1 p.2) 0, sub_self]
    simp [hinner]
  · have hcont : Continuous (fun x => partialDerivScalar f x 1) :=
      continuous_partialDerivScalar_of_contDiff hf 1
    unfold torusIntegral
    have hmid : ∀ x : ℝ,
        (∫ y in (0 : ℝ)..1, ∫ z in (0 : ℝ)..1, partialDerivScalar f (vec3 x y z) 1) = 0 := by
      intro x
      have hcyz : Continuous (fun p : ℝ × ℝ => partialDerivScalar f (vec3 x p.1 p.2) 1) :=
        hcont.comp (continuous_vec3_yz x)
      rw [intervalIntegral_swap_unit hcyz]
      have hinner : ∀ z : ℝ, ∫ y in (0 : ℝ)..1, partialDerivScalar f (vec3 x y z) 1 = 0 := by
        intro z
        have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt
          (a := (0 : ℝ)) (b := 1)
          (f := fun s => f (vec3 x s z))
          (f' := fun s => partialDerivScalar f (vec3 x s z) 1)
          (fun s _ => (hdiff (vec3 x s z)).hasFDerivAt.comp_hasDerivAt s (hasDerivAt_vec3_y x z s))
          ((hcont.comp (continuous_pi fun k => match k with
            | ⟨0, _⟩ => continuous_const
            | ⟨1, _⟩ => continuous_id
            | ⟨2, _⟩ => continuous_const)).intervalIntegrable 0 1)
        rw [hftc, vec3_one_zero_eq_add_basis1, hper (vec3 x 0 z) 1, sub_self]
      simp [hinner]
    simp [hmid]
  · have hcont : Continuous (fun x => partialDerivScalar f x 2) :=
      continuous_partialDerivScalar_of_contDiff hf 2
    unfold torusIntegral
    have hinner : ∀ x y : ℝ, ∫ z in (0 : ℝ)..1, partialDerivScalar f (vec3 x y z) 2 = 0 := by
      intro x y
      have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt
        (a := (0 : ℝ)) (b := 1)
        (f := fun s => f (vec3 x y s))
        (f' := fun s => partialDerivScalar f (vec3 x y s) 2)
        (fun s _ => (hdiff (vec3 x y s)).hasFDerivAt.comp_hasDerivAt s (hasDerivAt_vec3_z x y s))
        ((hcont.comp (continuous_pi fun k => match k with
          | ⟨0, _⟩ => continuous_const
          | ⟨1, _⟩ => continuous_const
          | ⟨2, _⟩ => continuous_id)).intervalIntegrable 0 1)
      rw [hftc, vec3_one_zero_eq_add_basis2, hper (vec3 x y 0) 2, sub_self]
    simp [hinner]

/-- **3D Periodic Divergence Theorem:** `∫_{𝕋³} div(F) = 0` for any `C¹` periodic vector field `F`. -/
theorem torusIntegral_div3D_eq_zero
    {F : R3 → R3} (hF : ContDiff ℝ 1 F) (hpF : IsPeriodic3D F) :
    torusIntegral (div3D F) = 0 := by
  have hF0 : ContDiff ℝ 1 (fun y => F y 0) := contDiff_pi.mp hF 0
  have hF1 : ContDiff ℝ 1 (fun y => F y 1) := contDiff_pi.mp hF 1
  have hF2 : ContDiff ℝ 1 (fun y => F y 2) := contDiff_pi.mp hF 2
  have hp0 : IsPeriodic3D (fun y => F y 0) := fun x i => congrArg (fun v => v 0) (hpF x i)
  have hp1 : IsPeriodic3D (fun y => F y 1) := fun x i => congrArg (fun v => v 1) (hpF x i)
  have hp2 : IsPeriodic3D (fun y => F y 2) := fun x i => congrArg (fun v => v 2) (hpF x i)
  have hc0 := continuous_partialDerivScalar_of_contDiff hF0 0
  have hc1 := continuous_partialDerivScalar_of_contDiff hF1 1
  have hc2 := continuous_partialDerivScalar_of_contDiff hF2 2
  unfold div3D
  rw [torusIntegral_add3 hc0 hc1 hc2,
      torusIntegral_partialDeriv_eq_zero hF0 hp0 0,
      torusIntegral_partialDeriv_eq_zero hF1 hp1 1,
      torusIntegral_partialDeriv_eq_zero hF2 hp2 2]
  ring

/-- **3D Periodic Integration by Parts:** `∫_{𝕋³} f ∂_i g = -∫_{𝕋³} (∂_i f) g`. -/
theorem torusIntegral_ibp
    {f g : R3 → ℝ} (hf : ContDiff ℝ 1 f) (hg : ContDiff ℝ 1 g)
    (hpf : IsPeriodic3D f) (hpg : IsPeriodic3D g) (i : Fin 3) :
    torusIntegral (fun x => f x * partialDerivScalar g x i) =
      -torusIntegral (fun x => partialDerivScalar f x i * g x) := by
  have hprod_zero := torusIntegral_partialDeriv_eq_zero (hf.mul hg) (hpf.mul hpg) i
  have hrule : ∀ x : R3,
      partialDerivScalar (fun y => f y * g y) x i =
        f x * partialDerivScalar g x i + partialDerivScalar f x i * g x := fun x =>
    partialDerivScalar_mul (differentiable_of_contDiff_one hf x)
      (differentiable_of_contDiff_one hg x) i
  have hc1 : Continuous (fun x => f x * partialDerivScalar g x i) :=
    hf.continuous.mul (continuous_partialDerivScalar_of_contDiff hg i)
  have hc2 : Continuous (fun x => partialDerivScalar f x i * g x) :=
    (continuous_partialDerivScalar_of_contDiff hf i).mul hg.continuous
  rw [torusIntegral_congr hrule, torusIntegral_add hc1 hc2] at hprod_zero
  linarith

-- ============================================================================
-- SECTION 4: ANALYTICAL LEMMA 1 (GAUSS-LERAY), PRESSURE & LAPLACIAN DISSIPATION
-- ============================================================================

/-- **Real Analytical Lemma 1 (Gauss-Leray Solenoidal Transport Cancellation on `𝕋³`):**
    For any `C¹` periodic vector fields `v, w : ℝ³ → ℝ³` with `div(v) = 0`,
    `∫_{𝕋³} ⟨(v · ∇)w, w⟩ dx = 0`.
    Covers BOTH velocity convection (`v = u, w = u`) and vorticity transport (`v = u, w = ω`). -/
theorem gauss_leray_transport_zero
    {v w : R3 → R3} (hv : ContDiff ℝ 1 v) (hw : ContDiff ℝ 1 w)
    (hpv : IsPeriodic3D v) (hpw : IsPeriodic3D w)
    (hdiv : ∀ x : R3, div3D v x = 0) :
    torusIntegral (fun x => dot3D (directionalAdvection3D v w x) (w x)) = 0 := by
  have hcomp_zero : ∀ comp : Fin 3,
      torusIntegral (fun x => directionalAdvection3D v w x comp * w x comp) = 0 := by
    intro comp
    let F : R3 → R3 := fun y i => v y i * (w y comp * w y comp)
    have hwc : ContDiff ℝ 1 (fun y => w y comp) := contDiff_pi.mp hw comp
    have hF_c1 : ContDiff ℝ 1 F := by
      refine contDiff_pi.mpr fun i => (contDiff_pi.mp hv i).mul (hwc.mul hwc)
    have hF_per : IsPeriodic3D F := by
      intro x i
      funext j
      change v (x + basisVec i) j * (w (x + basisVec i) comp * w (x + basisVec i) comp) =
             v x j * (w x comp * w x comp)
      rw [hpv x i, hpw x i]
    have hdivF_zero : torusIntegral (div3D F) = 0 := torusIntegral_div3D_eq_zero hF_c1 hF_per
    have hpt : ∀ x : R3,
        directionalAdvection3D v w x comp * w x comp = (1 / 2 : ℝ) * div3D F x := by
      intro x
      have hd_v : ∀ i : Fin 3, DifferentiableAt ℝ (fun y => v y i) x :=
        fun i => differentiable_of_contDiff_one (contDiff_pi.mp hv i) x
      have hd_wc : DifferentiableAt ℝ (fun y => w y comp) x :=
        differentiable_of_contDiff_one hwc x
      have hd_sq : DifferentiableAt ℝ (fun y => w y comp * w y comp) x := hd_wc.mul hd_wc
      have h_term : ∀ i : Fin 3,
          partialDerivScalar (fun y => F y i) x i =
            v x i * (2 * partialDerivScalar (fun y => w y comp) x i * w x comp) +
            partialDerivScalar (fun y => v y i) x i * (w x comp * w x comp) := fun i => by
        change partialDerivScalar (fun y => v y i * (w y comp * w y comp)) x i = _
        rw [partialDerivScalar_mul (hd_v i) hd_sq i, partialDerivScalar_mul hd_wc hd_wc i]
        ring
      have hdiv_eq : div3D F x =
          2 * (directionalAdvection3D v w x comp * w x comp) +
          div3D v x * (w x comp * w x comp) := by
        unfold div3D directionalAdvection3D
        rw [h_term 0, h_term 1, h_term 2]
        ring
      rw [hdiv_eq, hdiv x]
      ring
    have hdivF_cont : Continuous (div3D F) := by
      unfold div3D
      exact ((continuous_partialDerivScalar_of_contDiff (contDiff_pi.mp hF_c1 0) 0).add
             (continuous_partialDerivScalar_of_contDiff (contDiff_pi.mp hF_c1 1) 1)).add
            (continuous_partialDerivScalar_of_contDiff (contDiff_pi.mp hF_c1 2) 2)
    rw [torusIntegral_congr hpt, torusIntegral_const_mul (1 / 2 : ℝ) hdivF_cont, hdivF_zero, mul_zero]
  have hc_adv := continuous_directionalAdvection3D hv.continuous hw
  have hc0 : Continuous (fun x => directionalAdvection3D v w x 0 * w x 0) :=
    ((continuous_apply 0).comp hc_adv).mul ((continuous_apply 0).comp hw.continuous)
  have hc1 : Continuous (fun x => directionalAdvection3D v w x 1 * w x 1) :=
    ((continuous_apply 1).comp hc_adv).mul ((continuous_apply 1).comp hw.continuous)
  have hc2 : Continuous (fun x => directionalAdvection3D v w x 2 * w x 2) :=
    ((continuous_apply 2).comp hc_adv).mul ((continuous_apply 2).comp hw.continuous)
  unfold dot3D
  rw [torusIntegral_add3 hc0 hc1 hc2,
      hcomp_zero 0, hcomp_zero 1, hcomp_zero 2]
  ring

/-- **Pressure Work Cancellation on `𝕋³`:** `∫_{𝕋³} ⟨∇p, u⟩ dx = 0` for solenoidal periodic `u`. -/
theorem torusIntegral_grad_dot_solenoidal_zero
    {p : R3 → ℝ} {u : R3 → R3}
    (hp : ContDiff ℝ 1 p) (hu : ContDiff ℝ 1 u)
    (hpp : IsPeriodic3D p) (hpu : IsPeriodic3D u)
    (hdiv : ∀ x : R3, div3D u x = 0) :
    torusIntegral (fun x => dot3D (grad3D p x) (u x)) = 0 := by
  have hu0 : ContDiff ℝ 1 (fun y => u y 0) := contDiff_pi.mp hu 0
  have hu1 : ContDiff ℝ 1 (fun y => u y 1) := contDiff_pi.mp hu 1
  have hu2 : ContDiff ℝ 1 (fun y => u y 2) := contDiff_pi.mp hu 2
  have hpu0 : IsPeriodic3D (fun y => u y 0) := fun x i => congrArg (fun v => v 0) (hpu x i)
  have hpu1 : IsPeriodic3D (fun y => u y 1) := fun x i => congrArg (fun v => v 1) (hpu x i)
  have hpu2 : IsPeriodic3D (fun y => u y 2) := fun x i => congrArg (fun v => v 2) (hpu x i)
  have h_ibp0 : torusIntegral (fun x => partialDerivScalar p x 0 * u x 0) =
      -torusIntegral (fun x => p x * partialDerivScalar (fun y => u y 0) x 0) := by
    have h := torusIntegral_ibp hp hu0 hpp hpu0 0
    linarith
  have h_ibp1 : torusIntegral (fun x => partialDerivScalar p x 1 * u x 1) =
      -torusIntegral (fun x => p x * partialDerivScalar (fun y => u y 1) x 1) := by
    have h := torusIntegral_ibp hp hu1 hpp hpu1 1
    linarith
  have h_ibp2 : torusIntegral (fun x => partialDerivScalar p x 2 * u x 2) =
      -torusIntegral (fun x => p x * partialDerivScalar (fun y => u y 2) x 2) := by
    have h := torusIntegral_ibp hp hu2 hpp hpu2 2
    linarith
  have hc0 : Continuous (fun x => partialDerivScalar p x 0 * u x 0) :=
    (continuous_partialDerivScalar_of_contDiff hp 0).mul hu0.continuous
  have hc1 : Continuous (fun x => partialDerivScalar p x 1 * u x 1) :=
    (continuous_partialDerivScalar_of_contDiff hp 1).mul hu1.continuous
  have hc2 : Continuous (fun x => partialDerivScalar p x 2 * u x 2) :=
    (continuous_partialDerivScalar_of_contDiff hp 2).mul hu2.continuous
  have hr0 : Continuous (fun x => p x * partialDerivScalar (fun y => u y 0) x 0) :=
    hp.continuous.mul (continuous_partialDerivScalar_of_contDiff hu0 0)
  have hr1 : Continuous (fun x => p x * partialDerivScalar (fun y => u y 1) x 1) :=
    hp.continuous.mul (continuous_partialDerivScalar_of_contDiff hu1 1)
  have hr2 : Continuous (fun x => p x * partialDerivScalar (fun y => u y 2) x 2) :=
    hp.continuous.mul (continuous_partialDerivScalar_of_contDiff hu2 2)
  have hsum_zero :
      torusIntegral (fun x => p x * partialDerivScalar (fun y => u y 0) x 0) +
      torusIntegral (fun x => p x * partialDerivScalar (fun y => u y 1) x 1) +
      torusIntegral (fun x => p x * partialDerivScalar (fun y => u y 2) x 2) = 0 := by
    rw [← torusIntegral_add3 hr0 hr1 hr2]
    have hpt : ∀ x : R3,
        p x * partialDerivScalar (fun y => u y 0) x 0 +
        p x * partialDerivScalar (fun y => u y 1) x 1 +
        p x * partialDerivScalar (fun y => u y 2) x 2 = 0 := by
      intro x
      have hd := hdiv x
      unfold div3D at hd
      calc p x * partialDerivScalar (fun y => u y 0) x 0 +
           p x * partialDerivScalar (fun y => u y 1) x 1 +
           p x * partialDerivScalar (fun y => u y 2) x 2
          = p x * (partialDerivScalar (fun y => u y 0) x 0 +
                   partialDerivScalar (fun y => u y 1) x 1 +
                   partialDerivScalar (fun y => u y 2) x 2) := by ring
        _ = p x * 0 := by rw [hd]
        _ = 0 := mul_zero _
    rw [torusIntegral_congr hpt]
    unfold torusIntegral
    simp
  unfold dot3D grad3D
  rw [torusIntegral_add3 hc0 hc1 hc2,
      h_ibp0, h_ibp1, h_ibp2]
  linarith

/-- **Viscous Laplacian Dissipation Identity on `𝕋³`:**
    For any `C²` periodic vector field `w`, `∫_{𝕋³} ⟨Δw, w⟩ dx = -∫_{𝕋³} |∇w|² dx ≤ 0`. -/
theorem torusIntegral_laplacian_dot_self
    {w : R3 → R3} (hw : ContDiff ℝ 2 w) (hpw : IsPeriodic3D w) :
    torusIntegral (fun x => dot3D (laplacian3D w x) (w x)) =
      -torusIntegral (gradNormSq3D w) := by
  have h_scalar : ∀ (f : R3 → ℝ), ContDiff ℝ 2 f → IsPeriodic3D f →
      torusIntegral (fun x => laplacianScalar f x * f x) =
      -torusIntegral (fun x =>
        (partialDerivScalar f x 0) ^ 2 +
        (partialDerivScalar f x 1) ^ 2 +
        (partialDerivScalar f x 2) ^ 2) := by
    intro f hf hpf
    have hf1 : ContDiff ℝ 1 f := contDiff_one_of_two hf
    have h_axis : ∀ i : Fin 3,
        torusIntegral (fun x => sndPartial f x i i * f x) =
        -torusIntegral (fun x => (partialDerivScalar f x i) ^ 2) := by
      intro i
      have hgi : ContDiff ℝ 1 (fun y => partialDerivScalar f y i) :=
        contDiff_one_partialDerivScalar hf i
      have hpgi : IsPeriodic3D (fun y => partialDerivScalar f y i) :=
        IsPeriodic3D.partialDeriv hpf (differentiable_of_contDiff_one hf1) i
      have hibp := torusIntegral_ibp hf1 hgi hpf hpgi i
      have hlhs : ∀ x : R3, sndPartial f x i i * f x =
          f x * partialDerivScalar (fun y => partialDerivScalar f y i) x i := fun x => by
        rw [partial_partial_eq_sndPartial f x hf.contDiffAt i i]
        ring
      have hrhs : ∀ x : R3, partialDerivScalar f x i * partialDerivScalar f x i =
          (partialDerivScalar f x i) ^ 2 := fun x => (sq _).symm
      rw [torusIntegral_congr hlhs, hibp, torusIntegral_congr hrhs]
    have hpt_l : ∀ x : R3, laplacianScalar f x * f x =
        sndPartial f x 0 0 * f x + sndPartial f x 1 1 * f x + sndPartial f x 2 2 * f x := fun x => by
      unfold laplacianScalar; ring
    have hc0 : Continuous (fun x => sndPartial f x 0 0 * f x) :=
      (continuous_sndPartial_of_contDiff hf 0 0).mul hf.continuous
    have hc1 : Continuous (fun x => sndPartial f x 1 1 * f x) :=
      (continuous_sndPartial_of_contDiff hf 1 1).mul hf.continuous
    have hc2 : Continuous (fun x => sndPartial f x 2 2 * f x) :=
      (continuous_sndPartial_of_contDiff hf 2 2).mul hf.continuous
    have hq0 : Continuous (fun x => (partialDerivScalar f x 0) ^ 2) :=
      (continuous_partialDerivScalar_of_contDiff hf1 0).pow 2
    have hq1 : Continuous (fun x => (partialDerivScalar f x 1) ^ 2) :=
      (continuous_partialDerivScalar_of_contDiff hf1 1).pow 2
    have hq2 : Continuous (fun x => (partialDerivScalar f x 2) ^ 2) :=
      (continuous_partialDerivScalar_of_contDiff hf1 2).pow 2
    rw [torusIntegral_congr hpt_l,
        torusIntegral_add3 hc0 hc1 hc2,
        h_axis 0, h_axis 1, h_axis 2,
        torusIntegral_add3 hq0 hq1 hq2]
    ring
  have hw0 : ContDiff ℝ 2 (fun y => w y 0) := contDiff_pi.mp hw 0
  have hw1 : ContDiff ℝ 2 (fun y => w y 1) := contDiff_pi.mp hw 1
  have hw2 : ContDiff ℝ 2 (fun y => w y 2) := contDiff_pi.mp hw 2
  have hpw0 : IsPeriodic3D (fun y => w y 0) := fun x i => congrArg (fun v => v 0) (hpw x i)
  have hpw1 : IsPeriodic3D (fun y => w y 1) := fun x i => congrArg (fun v => v 1) (hpw x i)
  have hpw2 : IsPeriodic3D (fun y => w y 2) := fun x i => congrArg (fun v => v 2) (hpw x i)
  have hcl := continuous_laplacian3D hw
  have hl0 : Continuous (fun x => laplacian3D w x 0 * w x 0) :=
    ((continuous_apply 0).comp hcl).mul hw0.continuous
  have hl1 : Continuous (fun x => laplacian3D w x 1 * w x 1) :=
    ((continuous_apply 1).comp hcl).mul hw1.continuous
  have hl2 : Continuous (fun x => laplacian3D w x 2 * w x 2) :=
    ((continuous_apply 2).comp hcl).mul hw2.continuous
  have hq : ∀ (f : R3 → ℝ), ContDiff ℝ 2 f → Continuous (fun x =>
      (partialDerivScalar f x 0) ^ 2 + (partialDerivScalar f x 1) ^ 2 + (partialDerivScalar f x 2) ^ 2) :=
    fun f hf =>
      (((continuous_partialDerivScalar_of_contDiff (contDiff_one_of_two hf) 0).pow 2).add
       ((continuous_partialDerivScalar_of_contDiff (contDiff_one_of_two hf) 1).pow 2)).add
      ((continuous_partialDerivScalar_of_contDiff (contDiff_one_of_two hf) 2).pow 2)
  have hgrad_split : torusIntegral (gradNormSq3D w) =
      torusIntegral (fun x => (partialDerivScalar (fun y => w y 0) x 0) ^ 2 +
        (partialDerivScalar (fun y => w y 0) x 1) ^ 2 +
        (partialDerivScalar (fun y => w y 0) x 2) ^ 2) +
      torusIntegral (fun x => (partialDerivScalar (fun y => w y 1) x 0) ^ 2 +
        (partialDerivScalar (fun y => w y 1) x 1) ^ 2 +
        (partialDerivScalar (fun y => w y 1) x 2) ^ 2) +
      torusIntegral (fun x => (partialDerivScalar (fun y => w y 2) x 0) ^ 2 +
        (partialDerivScalar (fun y => w y 2) x 1) ^ 2 +
        (partialDerivScalar (fun y => w y 2) x 2) ^ 2) := by
    have hpt : ∀ x : R3, gradNormSq3D w x =
        ((partialDerivScalar (fun y => w y 0) x 0) ^ 2 +
         (partialDerivScalar (fun y => w y 0) x 1) ^ 2 +
         (partialDerivScalar (fun y => w y 0) x 2) ^ 2) +
        ((partialDerivScalar (fun y => w y 1) x 0) ^ 2 +
         (partialDerivScalar (fun y => w y 1) x 1) ^ 2 +
         (partialDerivScalar (fun y => w y 1) x 2) ^ 2) +
        ((partialDerivScalar (fun y => w y 2) x 0) ^ 2 +
         (partialDerivScalar (fun y => w y 2) x 1) ^ 2 +
         (partialDerivScalar (fun y => w y 2) x 2) ^ 2) := fun x => by
      unfold gradNormSq3D; ring
    rw [torusIntegral_congr hpt, torusIntegral_add3 (hq _ hw0) (hq _ hw1) (hq _ hw2)]
  unfold dot3D
  rw [torusIntegral_add3 hl0 hl1 hl2]
  dsimp only [laplacian3D]
  rw [h_scalar (fun y => w y 0) hw0 hpw0,
      h_scalar (fun y => w y 1) hw1 hpw1,
      h_scalar (fun y => w y 2) hw2 hpw2,
      hgrad_split]
  ring

-- ============================================================================
-- SECTION 5: PERIODIC CLASSICAL NS3D — LERAY ENERGY & 3D ENSTROPHY IDENTITIES
-- ============================================================================

/-- Periodic classical `C³` 3D incompressible Navier-Stokes solution on `𝕋³ × [0, ∞)`,
    extending Milestone 2's `IsClassicalNS3D_C3` with spatial periodicity and global `C³`/`C²` regularity. -/
structure IsPeriodicClassicalNS3D_C3 (u : ℝ → R3 → R3) (p : ℝ → R3 → ℝ) (ν : ℝ) : Prop
    extends IsClassicalNS3D_C3 u p ν where
  h_u_c3_global : ∀ t ≥ 0, ContDiff ℝ 3 (u t)
  h_p_c2_global : ∀ t ≥ 0, ContDiff ℝ 2 (p t)
  h_u_periodic : ∀ t ≥ 0, IsPeriodic3D (u t)
  h_p_periodic : ∀ t ≥ 0, IsPeriodic3D (p t)

/-- Non-vacuity witness: steady uniform flow satisfies `IsPeriodicClassicalNS3D_C3`. -/
theorem steadyUniformFlow_isPeriodicClassicalNS3D_C3 (c : R3) (p₀ ν : ℝ) (hν : 0 < ν) :
    IsPeriodicClassicalNS3D_C3 (fun _ _ => c) (fun _ _ => p₀) ν where
  toIsClassicalNS3D_C3 := steadyUniformFlow_isClassicalNS3D_C3 c p₀ ν hν
  h_u_c3_global := fun _ _ => contDiff_const
  h_p_c2_global := fun _ _ => contDiff_const
  h_u_periodic := fun _ _ _ _ => rfl
  h_p_periodic := fun _ _ _ _ => rfl

/-- **MAIN THEOREM 1 OF MILESTONE 3 (Classical Leray Energy Dissipation Identity on `𝕋³`):**
    For any periodic classical 3D Navier-Stokes solution `(u, p)`,
      `∫_{𝕋³} ⟨∂_t u(t, x), u(t, x)⟩ dx = -ν ∫_{𝕋³} |∇u(t, x)|² dx ≤ 0`
    proved directly from the PDE with zero external inequalities (`0 sorryAx`). -/
theorem leray_energy_identity_torus3D
    {u : ℝ → R3 → R3} {p : ℝ → R3 → ℝ} {ν : ℝ}
    (hns : IsPeriodicClassicalNS3D_C3 u p ν) {t : ℝ} (ht : t ≥ 0) :
    torusIntegral (fun x => dot3D (fun c => deriv (fun s => u s x c) t) (u t x)) =
      -ν * torusIntegral (gradNormSq3D (u t)) ∧
    torusIntegral (fun x => dot3D (fun c => deriv (fun s => u s x c) t) (u t x)) ≤ 0 := by
  have hu2 : ContDiff ℝ 2 (u t) := contDiff_two_of_three (hns.h_u_c3_global t ht)
  have hu1 : ContDiff ℝ 1 (u t) := contDiff_one_of_two hu2
  have hp1 : ContDiff ℝ 1 (p t) := contDiff_one_of_two (hns.h_p_c2_global t ht)
  have hpu : IsPeriodic3D (u t) := hns.h_u_periodic t ht
  have hpp : IsPeriodic3D (p t) := hns.h_p_periodic t ht
  have hpt : ∀ x : R3,
      dot3D (fun c => deriv (fun s => u s x c) t) (u t x) =
      ν * dot3D (laplacian3D (u t) x) (u t x) -
      dot3D (advection3D (u t) x) (u t x) -
      dot3D (grad3D (p t) x) (u t x) := by
    intro x
    have h0 := hns.h_momentum t ht x 0
    have h1 := hns.h_momentum t ht x 1
    have h2 := hns.h_momentum t ht x 2
    unfold dot3D
    have e0 : deriv (fun s => u s x 0) t * u t x 0 =
        (ν * laplacian3D (u t) x 0 - advection3D (u t) x 0 - grad3D (p t) x 0) * u t x 0 := by
      congr 1; linarith
    have e1 : deriv (fun s => u s x 1) t * u t x 1 =
        (ν * laplacian3D (u t) x 1 - advection3D (u t) x 1 - grad3D (p t) x 1) * u t x 1 := by
      congr 1; linarith
    have e2 : deriv (fun s => u s x 2) t * u t x 2 =
        (ν * laplacian3D (u t) x 2 - advection3D (u t) x 2 - grad3D (p t) x 2) * u t x 2 := by
      congr 1; linarith
    rw [e0, e1, e2]
    ring
  have hc_lap : Continuous (fun x => dot3D (laplacian3D (u t) x) (u t x)) :=
    continuous_dot3D (continuous_laplacian3D hu2) hu2.continuous
  have hc_nu_lap : Continuous (fun x => ν * dot3D (laplacian3D (u t) x) (u t x)) :=
    continuous_const.mul hc_lap
  have hc_adv : Continuous (fun x => dot3D (advection3D (u t) x) (u t x)) :=
    continuous_dot3D (continuous_advection3D hu1) hu1.continuous
  have hc_sub1 : Continuous (fun x =>
      ν * dot3D (laplacian3D (u t) x) (u t x) - dot3D (advection3D (u t) x) (u t x)) :=
    hc_nu_lap.sub hc_adv
  have hc_gp : Continuous (fun x => dot3D (grad3D (p t) x) (u t x)) :=
    continuous_dot3D (continuous_grad3D hp1) hu1.continuous
  have h_adv_zero : torusIntegral (fun x => dot3D (advection3D (u t) x) (u t x)) = 0 :=
    gauss_leray_transport_zero hu1 hu1 hpu hpu (hns.h_incompressible t ht)
  have h_gp_zero : torusIntegral (fun x => dot3D (grad3D (p t) x) (u t x)) = 0 :=
    torusIntegral_grad_dot_solenoidal_zero hp1 hu1 hpp hpu (hns.h_incompressible t ht)
  have h_lap_eq : torusIntegral (fun x => dot3D (laplacian3D (u t) x) (u t x)) =
      -torusIntegral (gradNormSq3D (u t)) :=
    torusIntegral_laplacian_dot_self hu2 hpu
  have h_eq : torusIntegral (fun x => dot3D (fun c => deriv (fun s => u s x c) t) (u t x)) =
      -ν * torusIntegral (gradNormSq3D (u t)) := by
    rw [torusIntegral_congr hpt,
        torusIntegral_sub hc_sub1 hc_gp,
        torusIntegral_sub hc_nu_lap hc_adv,
        torusIntegral_const_mul ν hc_lap,
        h_lap_eq, h_adv_zero, h_gp_zero]
    ring
  have h_grad_nn : 0 ≤ torusIntegral (gradNormSq3D (u t)) :=
    torusIntegral_nonneg (continuous_gradNormSq3D hu1) (gradNormSq3D_nonneg (u t))
  have h_le : -ν * torusIntegral (gradNormSq3D (u t)) ≤ 0 := by
    nlinarith [hns.h_nu_pos, h_grad_nn]
  exact ⟨h_eq, h_eq ▸ h_le⟩

/-- **MAIN THEOREM 2 OF MILESTONE 3 (Exact 3D Enstrophy Evolution Identity on `𝕋³`):**
    Derived directly from Milestone 2's `navier_stokes_3d_vorticity_equation`:
    for vorticity `ω(t, x) = curl3D (u t) x`, the true enstrophy production rate satisfies
      `∫_{𝕋³} ⟨∂_t ω, ω⟩ dx = ∫_{𝕋³} ⟨(ω · ∇)u, ω⟩ dx - ν ∫_{𝕋³} |∇ω|² dx`
    where the first RHS term is the true 3D vortex stretching `S_stretch` and the second is
    the true viscous palinstrophy dissipation `D_visc` (`0 sorryAx`). -/
theorem enstrophy_evolution_identity_torus3D
    {u : ℝ → R3 → R3} {p : ℝ → R3 → ℝ} {ν : ℝ}
    (hns : IsPeriodicClassicalNS3D_C3 u p ν) {t : ℝ} (ht : t ≥ 0) :
    torusIntegral (fun x => dot3D (fun c => deriv (fun s => curl3D (u s) x c) t) (curl3D (u t) x)) =
      torusIntegral (fun x => dot3D (directionalAdvection3D (curl3D (u t)) (u t) x) (curl3D (u t) x)) -
      ν * torusIntegral (gradNormSq3D (curl3D (u t))) := by
  have hu3 : ContDiff ℝ 3 (u t) := hns.h_u_c3_global t ht
  have hu2 : ContDiff ℝ 2 (u t) := contDiff_two_of_three hu3
  have hu1 : ContDiff ℝ 1 (u t) := contDiff_one_of_two hu2
  have hw2 : ContDiff ℝ 2 (curl3D (u t)) := contDiff_two_curl3D hu3
  have hw1 : ContDiff ℝ 1 (curl3D (u t)) := contDiff_one_of_two hw2
  have hpu : IsPeriodic3D (u t) := hns.h_u_periodic t ht
  have hpw : IsPeriodic3D (curl3D (u t)) := hpu.curl3D (differentiable_of_contDiff_one hu1)
  have hpt : ∀ x : R3,
      dot3D (fun c => deriv (fun s => curl3D (u s) x c) t) (curl3D (u t) x) =
      dot3D (directionalAdvection3D (curl3D (u t)) (u t) x) (curl3D (u t) x) +
      ν * dot3D (laplacian3D (curl3D (u t)) x) (curl3D (u t) x) -
      dot3D (directionalAdvection3D (u t) (curl3D (u t)) x) (curl3D (u t) x) := by
    intro x
    have hv0 := navier_stokes_3d_vorticity_equation hns.toIsClassicalNS3D_C3 ht x 0
    have hv1 := navier_stokes_3d_vorticity_equation hns.toIsClassicalNS3D_C3 ht x 1
    have hv2 := navier_stokes_3d_vorticity_equation hns.toIsClassicalNS3D_C3 ht x 2
    unfold dot3D
    have e0 : deriv (fun s => curl3D (u s) x 0) t * curl3D (u t) x 0 =
        (directionalAdvection3D (curl3D (u t)) (u t) x 0 +
         ν * laplacian3D (curl3D (u t)) x 0 -
         directionalAdvection3D (u t) (curl3D (u t)) x 0) * curl3D (u t) x 0 := by
      congr 1; linarith
    have e1 : deriv (fun s => curl3D (u s) x 1) t * curl3D (u t) x 1 =
        (directionalAdvection3D (curl3D (u t)) (u t) x 1 +
         ν * laplacian3D (curl3D (u t)) x 1 -
         directionalAdvection3D (u t) (curl3D (u t)) x 1) * curl3D (u t) x 1 := by
      congr 1; linarith
    have e2 : deriv (fun s => curl3D (u s) x 2) t * curl3D (u t) x 2 =
        (directionalAdvection3D (curl3D (u t)) (u t) x 2 +
         ν * laplacian3D (curl3D (u t)) x 2 -
         directionalAdvection3D (u t) (curl3D (u t)) x 2) * curl3D (u t) x 2 := by
      congr 1; linarith
    rw [e0, e1, e2]
    ring
  have hc_str : Continuous (fun x =>
      dot3D (directionalAdvection3D (curl3D (u t)) (u t) x) (curl3D (u t) x)) :=
    continuous_dot3D (continuous_directionalAdvection3D hw1.continuous hu1) hw1.continuous
  have hc_lap : Continuous (fun x =>
      dot3D (laplacian3D (curl3D (u t)) x) (curl3D (u t) x)) :=
    continuous_dot3D (continuous_laplacian3D hw2) hw2.continuous
  have hc_tr : Continuous (fun x =>
      dot3D (directionalAdvection3D (u t) (curl3D (u t)) x) (curl3D (u t) x)) :=
    continuous_dot3D (continuous_directionalAdvection3D hu1.continuous hw1) hw1.continuous
  have h_tr_zero : torusIntegral (fun x =>
      dot3D (directionalAdvection3D (u t) (curl3D (u t)) x) (curl3D (u t) x)) = 0 :=
    gauss_leray_transport_zero hu1 hw1 hpu hpw (hns.h_incompressible t ht)
  have h_lap_eq : torusIntegral (fun x =>
      dot3D (laplacian3D (curl3D (u t)) x) (curl3D (u t) x)) =
      -torusIntegral (gradNormSq3D (curl3D (u t))) :=
    torusIntegral_laplacian_dot_self hw2 hpw
  have hc_nu_lap : Continuous (fun x => ν * dot3D (laplacian3D (curl3D (u t)) x) (curl3D (u t) x)) :=
    continuous_const.mul hc_lap
  have hc_add1 : Continuous (fun x =>
      dot3D (directionalAdvection3D (curl3D (u t)) (u t) x) (curl3D (u t) x) +
      ν * dot3D (laplacian3D (curl3D (u t)) x) (curl3D (u t) x)) :=
    hc_str.add hc_nu_lap
  rw [torusIntegral_congr hpt,
      torusIntegral_sub hc_add1 hc_tr,
      torusIntegral_add hc_str hc_nu_lap,
      torusIntegral_const_mul ν hc_lap,
      h_lap_eq, h_tr_zero]
  ring

-- ============================================================================
-- SECTION 6: AXIOM AUDIT TRAIL (0 sorryAx)
-- ============================================================================

#print axioms torusIntegral_div3D_eq_zero
#print axioms torusIntegral_ibp
#print axioms gauss_leray_transport_zero
#print axioms torusIntegral_grad_dot_solenoidal_zero
#print axioms torusIntegral_laplacian_dot_self
#print axioms steadyUniformFlow_isPeriodicClassicalNS3D_C3
#print axioms leray_energy_identity_torus3D
#print axioms enstrophy_evolution_identity_torus3D

end GarryLerayTorus3D