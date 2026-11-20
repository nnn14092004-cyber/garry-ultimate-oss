import Mathlib.Analysis.Fourier.AddCircleMulti
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import SpectralOperatorsTorus3D

/-!
# GARRYULT v4.0.0 — Milestone 5B: Full 3D Parseval Identity on `𝕋³`, Global `L²(𝕋³)`
# Calderón–Zygmund Pressure Bound, Isotropic 3D Spherical-Shell Bernstein Inequality,
# Periodic Sobolev Spaces `Hˢ(𝕋³)` & Spectral `L²–H¹–H²` Interpolation (`2 Z² ≤ E · P`)
-/

namespace GarryParsevalSobolev3D

open MeasureTheory Filter Topology UnitAddTorus GarryReal3DCalculus GarryVorticity3D
  GarryLerayTorus3D GarryLerayEnergyLaw3D GarryPoincareSobolev3D
  GarryFourierSpectral3D GarrySpectralOperators3D

private lemma two_add_one_eq_three5b {α : Type*} [AddMonoidWithOne α] :
    (2 : α) + 1 = 3 := by
  rw [← Nat.cast_ofNat (n := 2), ← Nat.cast_one, ← Nat.cast_add]
  exact Nat.cast_ofNat

private lemma contDiff_two_of_three5b {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {f : E → F} (hf : ContDiff ℝ 3 f) :
    ContDiff ℝ 2 f :=
  hf.of_le (by rw [← two_add_one_eq_three5b]; exact le_self_add)

private lemma contDiff_one_of_two5b {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {f : E → F} (hf : ContDiff ℝ 2 f) :
    ContDiff ℝ 1 f :=
  hf.of_le (by rw [← one_add_one_eq_two]; exact le_self_add)

-- ============================================================================
-- SECTION 1: MEASURE-PRESERVING BRIDGE `UnitAddTorus (Fin 3) ↔ (0, 1]³`
-- ============================================================================

/-- Unit cube `(0, 1]³` inside `R3 = Fin 3 → ℝ`. -/
private def unitCubePi : Set R3 := {x : R3 | ∀ i : Fin 3, x i ∈ Set.Ioc (0 : ℝ) 1}

private noncomputable abbrev uMeas1b : Measure ℝ := volume.restrict (Set.Ioc (0 : ℝ) 1)
private noncomputable abbrev uMeas2b : Measure (ℝ × ℝ) := uMeas1b.prod uMeas1b
private noncomputable abbrev uMeas3b : Measure (ℝ × (ℝ × ℝ)) := uMeas1b.prod uMeas2b
private abbrev uSquareIoc : Set (ℝ × ℝ) := Set.Ioc (0 : ℝ) 1 ×ˢ Set.Ioc (0 : ℝ) 1
private abbrev uCubeIoc : Set (ℝ × (ℝ × ℝ)) := Set.Ioc (0 : ℝ) 1 ×ˢ uSquareIoc

private theorem uMeas2b_eq_restrict : uMeas2b = (volume : Measure (ℝ × ℝ)).restrict uSquareIoc := by
  unfold uMeas2b uMeas1b uSquareIoc
  rw [Measure.prod_restrict]
  rfl

private theorem uMeas3b_eq_restrict :
    uMeas3b = (volume : Measure (ℝ × (ℝ × ℝ))).restrict uCubeIoc := by
  unfold uMeas3b uMeas2b uMeas1b uCubeIoc uSquareIoc
  rw [Measure.prod_restrict, Measure.prod_restrict]
  rfl

/-- Canonical measurable equivalence `(Fin 3 → ℝ) ≃ᵐ ℝ × (ℝ × ℝ)`. -/
private def r3ToProdEquiv : R3 ≃ᵐ ℝ × (ℝ × ℝ) :=
  (MeasurableEquiv.piFinSuccAbove (fun _ : Fin 3 => ℝ) 0).trans
    (MeasurableEquiv.prodCongr (MeasurableEquiv.refl ℝ)
      ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin 2 => ℝ) 0).trans
        (MeasurableEquiv.prodCongr (MeasurableEquiv.refl ℝ)
          (MeasurableEquiv.funUnique (Fin 1) ℝ))))

private theorem r3ToProdEquiv_apply (x : R3) :
    r3ToProdEquiv x = (x 0, (x 1, x 2)) := rfl

private theorem r3ToProdEquiv_symm_apply (q : ℝ × (ℝ × ℝ)) :
    r3ToProdEquiv.symm q = vec3 q.1 q.2.1 q.2.2 := by
  funext i
  fin_cases i <;> rfl

private theorem measurePreserving_r3ToProd :
    MeasurePreserving r3ToProdEquiv (volume : Measure R3) (volume : Measure (ℝ × (ℝ × ℝ))) := by
  have h1 : MeasurePreserving (MeasurableEquiv.piFinSuccAbove (fun _ : Fin 3 => ℝ) 0)
      (volume : Measure R3) (volume : Measure (ℝ × (Fin 2 → ℝ))) :=
    MeasureTheory.volume_preserving_piFinSuccAbove (fun _ : Fin 3 => ℝ) 0
  have h2 : MeasurePreserving (MeasurableEquiv.piFinSuccAbove (fun _ : Fin 2 => ℝ) 0)
      (volume : Measure (Fin 2 → ℝ)) (volume : Measure (ℝ × (Fin 1 → ℝ))) :=
    MeasureTheory.volume_preserving_piFinSuccAbove (fun _ : Fin 2 => ℝ) 0
  have h3 : MeasurePreserving (MeasurableEquiv.funUnique (Fin 1) ℝ)
      (volume : Measure (Fin 1 → ℝ)) (volume : Measure ℝ) :=
    MeasureTheory.volume_preserving_funUnique (Fin 1) ℝ
  have h23 : MeasurePreserving
      ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin 2 => ℝ) 0).trans
        (MeasurableEquiv.prodCongr (MeasurableEquiv.refl ℝ)
          (MeasurableEquiv.funUnique (Fin 1) ℝ)))
      (volume : Measure (Fin 2 → ℝ)) (volume : Measure (ℝ × ℝ)) :=
    ((MeasurePreserving.id (volume : Measure ℝ)).prod h3).comp h2
  exact ((MeasurePreserving.id (volume : Measure ℝ)).prod h23).comp h1

private theorem r3ToProd_preimage_uCubeIoc :
    r3ToProdEquiv ⁻¹' uCubeIoc = unitCubePi := by
  ext x
  simp only [Set.mem_preimage, uCubeIoc, uSquareIoc, unitCubePi, Set.mem_prod,
    Set.mem_ofPred_eq, r3ToProdEquiv_apply]
  constructor
  · intro ⟨h0, h1, h2⟩ i
    fin_cases i
    · exact h0
    · exact h1
    · exact h2
  · intro h
    exact ⟨h 0, h 1, h 2⟩

private theorem integral_unitCubePi_eq_iterated {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {g : R3 → E} (hg : Continuous g) :
    (∫ x in unitCubePi, g x) =
      ∫ x in (0 : ℝ)..1, ∫ y in (0 : ℝ)..1, ∫ z in (0 : ℝ)..1, g (vec3 x y z) := by
  have hmp_restrict : MeasurePreserving r3ToProdEquiv
      ((volume : Measure R3).restrict unitCubePi) uMeas3b := by
    rw [uMeas3b_eq_restrict, ← r3ToProd_preimage_uCubeIoc]
    exact measurePreserving_r3ToProd.restrict_preimage
      (measurableSet_Ioc.prod (measurableSet_Ioc.prod measurableSet_Ioc))
  have h_eq1 : (∫ x in unitCubePi, g x) =
      ∫ q : ℝ × (ℝ × ℝ), g (vec3 q.1 q.2.1 q.2.2) ∂uMeas3b := by
    have hcomp := hmp_restrict.symm.integral_comp' (g := g)
    have hfun : (fun q : ℝ × (ℝ × ℝ) => g (r3ToProdEquiv.symm q)) =
        (fun q : ℝ × (ℝ × ℝ) => g (vec3 q.1 q.2.1 q.2.2)) := by
      funext q; rw [r3ToProdEquiv_symm_apply]
    rw [← hcomp, hfun]
  have hcont_xyz : Continuous (fun q : ℝ × (ℝ × ℝ) => vec3 q.1 q.2.1 q.2.2) :=
    continuous_pi fun i => match i with
      | ⟨0, _⟩ => continuous_fst | ⟨1, _⟩ => continuous_fst.comp continuous_snd
      | ⟨2, _⟩ => continuous_snd.comp continuous_snd
  have hcIcc : IsCompact (Set.Icc (0 : ℝ) 1) := isCompact_Icc
  have hint3 : Integrable (fun q : ℝ × (ℝ × ℝ) => g (vec3 q.1 q.2.1 q.2.2)) uMeas3b := by
    rw [uMeas3b_eq_restrict]
    refine ((hg.comp hcont_xyz).continuousOn.integrableOn_compact
      (hcIcc.prod (hcIcc.prod hcIcc))).mono_set ?_
    exact Set.prod_mono Set.Ioc_subset_Icc_self
      (Set.prod_mono Set.Ioc_subset_Icc_self Set.Ioc_subset_Icc_self)
  have h_prod : (∫ q : ℝ × (ℝ × ℝ), g (vec3 q.1 q.2.1 q.2.2) ∂uMeas3b) =
      ∫ x, (∫ p : ℝ × ℝ, g (vec3 x p.1 p.2) ∂uMeas2b) ∂uMeas1b :=
    MeasureTheory.integral_prod (fun q : ℝ × (ℝ × ℝ) => g (vec3 q.1 q.2.1 q.2.2)) hint3
  have h_inner : ∀ x : ℝ,
      (∫ p : ℝ × ℝ, g (vec3 x p.1 p.2) ∂uMeas2b) =
        ∫ y, (∫ z, g (vec3 x y z) ∂uMeas1b) ∂uMeas1b := by
    intro x
    have hcont_yz : Continuous (fun p : ℝ × ℝ => vec3 x p.1 p.2) :=
      continuous_pi fun i => match i with
        | ⟨0, _⟩ => continuous_const | ⟨1, _⟩ => continuous_fst | ⟨2, _⟩ => continuous_snd
    have hint2 : Integrable (fun p : ℝ × ℝ => g (vec3 x p.1 p.2)) uMeas2b := by
      rw [uMeas2b_eq_restrict]
      refine ((hg.comp hcont_yz).continuousOn.integrableOn_compact
        (hcIcc.prod hcIcc)).mono_set ?_
      exact Set.prod_mono Set.Ioc_subset_Icc_self Set.Ioc_subset_Icc_self
    exact MeasureTheory.integral_prod (fun p : ℝ × ℝ => g (vec3 x p.1 p.2)) hint2
  rw [h_eq1, h_prod]
  simp_rw [h_inner]
  have h1 : ∀ h : ℝ → E, (∫ t, h t ∂uMeas1b) = ∫ t in (0 : ℝ)..1, h t := fun h =>
    (intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)).symm
  simp_rw [h1]

/-- Integer-lattice translation invariance of `IsPeriodic3D` functions. -/
private theorem isPeriodic3D_shift_int {f : R3 → ℝ} (hpf : IsPeriodic3D f) :
    ∀ (x : R3) (m : Fin 3 → ℤ), f (fun i => x i + (m i : ℝ)) = f x := by
  have h_nat : ∀ (n : ℕ) (x : R3) (i : Fin 3),
      f (fun j => if j = i then x j + (n : ℝ) else x j) = f x := by
    intro n
    induction n with
    | zero =>
      intro x i
      have heq : (fun j => if j = i then x j + ((0 : ℕ) : ℝ) else x j) = x := by
        funext j; split_ifs <;> simp
      rw [heq]
    | succ k ih =>
      intro x i
      have hstep : (fun j => if j = i then x j + ((k + 1 : ℕ) : ℝ) else x j) =
          (fun j => if j = i then x j + (k : ℝ) else x j) + basisVec i := by
        funext j
        unfold basisVec
        by_cases hj : j = i
        · subst hj; simp [Nat.cast_add]; ring
        · simp [hj]
      rw [hstep, hpf _ i, ih]
  have h_one : ∀ (x : R3) (i : Fin 3) (n : ℤ),
      f (fun j => if j = i then x j + (n : ℝ) else x j) = f x := by
    intro x i n
    cases n with
    | ofNat k =>
      simpa using h_nat k x i
    | negSucc k =>
      let y : R3 := fun j => if j = i then x j + ((Int.negSucc k : ℤ) : ℝ) else x j
      have hy : (fun j => if j = i then y j + ((k + 1 : ℕ) : ℝ) else y j) = x := by
        funext j
        dsimp only [y]
        by_cases hj : j = i
        · subst hj
          simp only [↓reduceIte, Int.cast_negSucc, Nat.cast_add, Nat.cast_one]
          ring
        · simp [hj]
      have h := h_nat (k + 1) y i
      rw [hy] at h
      exact h.symm
  intro x m
  let x1 : R3 := fun j => if j = 0 then x j + (m 0 : ℝ) else x j
  let x2 : R3 := fun j => if j = 1 then x1 j + (m 1 : ℝ) else x1 j
  let x3 : R3 := fun j => if j = 2 then x2 j + (m 2 : ℝ) else x2 j
  have h_eq : (fun i => x i + (m i : ℝ)) = x3 := by
    funext i
    fin_cases i <;> simp [x3, x2, x1]
  rw [h_eq, h_one x2 2 (m 2), h_one x1 1 (m 1), h_one x 0 (m 0)]

/-- Canonical projection `R3 → UnitAddTorus (Fin 3)` is an open surjective continuous map,
    hence a topological quotient map. -/
private theorem isQuotientMap_r3ToTorus :
    Topology.IsQuotientMap (fun x : R3 => (fun i : Fin 3 => (x i : AddCircle (1 : ℝ)))) := by
  let q1 : ℝ → AddCircle (1 : ℝ) := QuotientAddGroup.mk
  have hopen1 : IsOpenMap q1 := QuotientAddGroup.isOpenMap_coe
  have hcont1 : Continuous q1 := continuous_quotient_mk'
  have hsurj1 : Function.Surjective q1 := QuotientAddGroup.mk_surjective
  have hopen : IsOpenMap (fun x : R3 => (fun i : Fin 3 => q1 (x i))) := by
    intro U hU
    rw [isOpen_pi_iff]
    intro y hy
    rcases hy with ⟨x, hxU, rfl⟩
    rw [isOpen_pi_iff] at hU
    obtain ⟨I, V, hV, hVU⟩ := hU x hxU
    refine ⟨I, fun i => q1 '' V i, fun i hi => ⟨hopen1 (V i) (hV i hi).1, ⟨x i, (hV i hi).2, rfl⟩⟩, ?_⟩
    intro z hz
    have hchoice : ∀ i : Fin 3, ∃ r : ℝ, q1 r = z i ∧ (i ∈ I → r ∈ V i) := by
      intro i
      by_cases hi : i ∈ I
      · obtain ⟨r, hrV, hrz⟩ := hz i hi
        exact ⟨r, hrz, fun _ => hrV⟩
      · obtain ⟨r, hrz⟩ := hsurj1 (z i)
        exact ⟨r, hrz, fun h => absurd h hi⟩
    choose r hr_eq hrV using hchoice
    refine ⟨r, hVU fun i hi => hrV i hi, funext hr_eq⟩
  have hcont : Continuous (fun x : R3 => (fun i : Fin 3 => q1 (x i))) :=
    continuous_pi fun i => hcont1.comp (continuous_apply i)
  have hsurj : Function.Surjective (fun x : R3 => (fun i : Fin 3 => q1 (x i))) := by
    intro y
    choose r hr using fun i => hsurj1 (y i)
    exact ⟨r, funext hr⟩
  exact hopen.isQuotientMap hcont hsurj

/-- Choose a real representative in `R3` for each point of `UnitAddTorus (Fin 3)`. -/
private noncomputable def torusRep (t : UnitAddTorus (Fin 3)) : R3 :=
  fun i => Classical.choose (QuotientAddGroup.mk_surjective (t i))

private theorem torusRep_spec (t : UnitAddTorus (Fin 3)) (i : Fin 3) :
    ((torusRep t i : ℝ) : AddCircle (1 : ℝ)) = t i :=
  Classical.choose_spec (QuotientAddGroup.mk_surjective (t i))

private theorem torusRep_of_coe_shift (x : R3) :
    ∃ m : Fin 3 → ℤ, torusRep (fun i => (x i : AddCircle (1 : ℝ))) = fun i => x i + (m i : ℝ) := by
  have hdiff : ∀ i : Fin 3, ∃ m : ℤ,
      torusRep (fun j => (x j : AddCircle (1 : ℝ))) i = x i + (m : ℝ) := by
    intro i
    have heq : ((torusRep (fun j => (x j : AddCircle (1 : ℝ))) i : ℝ) : AddCircle (1 : ℝ)) =
        ((x i : ℝ) : AddCircle (1 : ℝ)) :=
      torusRep_spec (fun j => (x j : AddCircle (1 : ℝ))) i
    rw [QuotientAddGroup.eq] at heq
    obtain ⟨m, hm⟩ := AddSubgroup.mem_zmultiples_iff.mp heq
    refine ⟨-m, ?_⟩
    simp only [zsmul_eq_mul, mul_one, Int.cast_neg] at hm ⊢
    linarith
  choose m hm using hdiff
  exact ⟨m, funext hm⟩

/-- Canonical lift of a continuous periodic real function `f : R3 → ℝ` to `C(UnitAddTorus (Fin 3), ℂ)`. -/
private noncomputable def liftPeriodicToTorus {f : R3 → ℝ} (hf : Continuous f) (hpf : IsPeriodic3D f) :
    C(UnitAddTorus (Fin 3), ℂ) where
  toFun := fun t => (f (torusRep t) : ℂ)
  continuous_toFun := by
    rw [isQuotientMap_r3ToTorus.continuous_iff]
    have hcomp : (fun t : UnitAddTorus (Fin 3) => (f (torusRep t) : ℂ)) ∘
        (fun x : R3 => (fun i : Fin 3 => (x i : AddCircle (1 : ℝ)))) =
        (fun x : R3 => (f x : ℂ)) := by
      funext x
      dsimp only [Function.comp_apply]
      obtain ⟨m, hm⟩ := torusRep_of_coe_shift x
      rw [hm, isPeriodic3D_shift_int hpf x m]
    rw [hcomp]
    exact Complex.continuous_ofReal.comp hf

private theorem liftPeriodicToTorus_apply {f : R3 → ℝ} (hf : Continuous f) (hpf : IsPeriodic3D f)
    (x : R3) :
    liftPeriodicToTorus hf hpf (fun i => (x i : AddCircle (1 : ℝ))) = (f x : ℂ) := by
  dsimp only [liftPeriodicToTorus, ContinuousMap.coe_mk]
  obtain ⟨m, hm⟩ := torusRep_of_coe_shift x
  rw [hm, isPeriodic3D_shift_int hpf x m]

private theorem mFourier_neg_eq_fourierChar1D (k : Fin 3 → ℤ) (x : R3) :
    mFourier (-k) (fun i => (x i : AddCircle (1 : ℝ))) =
      fourierChar1D (k 0) (x 0) * fourierChar1D (k 1) (x 1) * fourierChar1D (k 2) (x 2) := by
  rw [mFourier, ContinuousMap.coe_mk, Fin.prod_univ_three]
  have h1 : ∀ (n : ℤ) (t : ℝ), fourier (T := (1 : ℝ)) (-n) (t : AddCircle (1 : ℝ)) = fourierChar1D n t := by
    intro n t
    rw [fourier_coe_apply]
    unfold fourierChar1D
    congr 1
    push_cast
    ring
  simp only [Pi.neg_apply, h1]

private theorem mFourierCoeff_lift_eq_fourierCoeff3D
    {f : R3 → ℝ} (hf : Continuous f) (hpf : IsPeriodic3D f) (k : Fin 3 → ℤ) :
    mFourierCoeff (liftPeriodicToTorus hf hpf) k = fourierCoeff3D f k := by
  rw [mFourierCoeff_eq_integral _ k (0 : R3)]
  have hset : {x : R3 | ∀ i, x i ∈ Set.Ioc ((0 : R3) i) ((0 : R3) i + 1)} = unitCubePi := by
    ext x; simp [unitCubePi]
  rw [hset]
  have hpt : (fun x : R3 => mFourier (-k) (fun i => (x i : AddCircle (1 : ℝ))) •
      liftPeriodicToTorus hf hpf (fun i => (x i : AddCircle (1 : ℝ)))) =
      (fun x : R3 => fourierChar1D (k 0) (x 0) * fourierChar1D (k 1) (x 1) *
        fourierChar1D (k 2) (x 2) * (f x : ℂ)) := by
    funext x
    rw [smul_eq_mul, mFourier_neg_eq_fourierChar1D, liftPeriodicToTorus_apply]
  rw [hpt]
  have hcont : Continuous (fun x : R3 =>
      fourierChar1D (k 0) (x 0) * fourierChar1D (k 1) (x 1) * fourierChar1D (k 2) (x 2) * (f x : ℂ)) := by
    have hc1 : ∀ (n : ℤ) (i : Fin 3), Continuous (fun x : R3 => fourierChar1D n (x i)) := fun n i =>
      (Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal)).comp
        (continuous_apply i)
    exact (((hc1 (k 0) 0).mul (hc1 (k 1) 1)).mul (hc1 (k 2) 2)).mul
      (Complex.continuous_ofReal.comp hf)
  rw [integral_unitCubePi_eq_iterated hcont]
  unfold fourierCoeff3D
  rfl

-- ============================================================================
-- SECTION 2: FULL 3D PARSEVAL IDENTITIES (SCALAR & VECTOR) ON `𝕋³`
-- ============================================================================

section TorusParseval

noncomputable local instance (priority := high) : MeasureSpace UnitAddCircle :=
  ⟨AddCircle.haarAddCircle⟩
local instance (priority := high) : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance (priority := high) : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

private theorem hasSum_sq_mFourierCoeff_cont {d : Type*} [Fintype d]
    (F : C(UnitAddTorus d, ℂ)) :
    HasSum (fun k : d → ℤ => ‖mFourierCoeff F k‖ ^ 2)
      (∫ t : UnitAddTorus d, ‖F t‖ ^ 2) := by
  have hparse := hasSum_sq_mFourierCoeff (F.toLp 2 volume ℂ)
  have h_coeff : (fun k : d → ℤ => ‖mFourierCoeff (F.toLp 2 volume ℂ) k‖ ^ 2) =
      (fun k : d → ℤ => ‖mFourierCoeff F k‖ ^ 2) := by
    funext k; rw [mFourierCoeff_toLp]
  have h_rhs : (∫ t : UnitAddTorus d, ‖(F.toLp 2 volume ℂ) t‖ ^ 2) =
      ∫ t : UnitAddTorus d, ‖F t‖ ^ 2 := by
    refine integral_congr_ae ?_
    filter_upwards [F.coeFn_toAEEqFun volume] with t ht
    have ht' : (F.toLp 2 volume ℂ) t = F t := ht
    rw [ht']
  rw [h_coeff, h_rhs] at hparse
  exact hparse

/-- **MAIN THEOREM 1 OF MILESTONE 5B (Full 3D Scalar Parseval Identity on `𝕋³`):**
    For any continuous `ℤ³`-periodic scalar field `f : R3 → ℝ`:
      `∑' k : ℤ³, ‖fourierCoeff3D f k‖² = ∫_{𝕋³} f(x)² dx` (`0 sorryAx`). -/
theorem hasSum_sq_fourierCoeff3D
    {f : R3 → ℝ} (hf : Continuous f) (hpf : IsPeriodic3D f) :
    HasSum (fun k : Fin 3 → ℤ => ‖fourierCoeff3D f k‖ ^ 2)
      (torusIntegral (fun x => (f x) ^ 2)) := by
  let F : C(UnitAddTorus (Fin 3), ℂ) := liftPeriodicToTorus hf hpf
  have hparse := hasSum_sq_mFourierCoeff_cont F
  have h_coeff : (fun k : Fin 3 → ℤ => ‖mFourierCoeff F k‖ ^ 2) =
      (fun k : Fin 3 → ℤ => ‖fourierCoeff3D f k‖ ^ 2) := by
    funext k
    rw [mFourierCoeff_lift_eq_fourierCoeff3D hf hpf k]
  have h_rhs : (∫ t : UnitAddTorus (Fin 3), ‖F t‖ ^ 2) =
      torusIntegral (fun x => (f x) ^ 2) := by
    rw [integral_preimage (fun t => ‖F t‖ ^ 2) (0 : R3)]
    have hset : {x : R3 | ∀ i, x i ∈ Set.Ioc ((0 : R3) i) ((0 : R3) i + 1)} = unitCubePi := by
      ext x; simp [unitCubePi]
    rw [hset]
    have hpt : (fun x : R3 => ‖F (fun i => (x i : AddCircle (1 : ℝ)))‖ ^ 2) =
        (fun x : R3 => (f x) ^ 2) := by
      funext x
      dsimp only [F]
      rw [liftPeriodicToTorus_apply, Complex.norm_real, Real.norm_eq_abs, sq_abs]
    have hf2 : Continuous (fun x : R3 => (f x) ^ 2) := hf.pow 2
    rw [hpt, integral_unitCubePi_eq_iterated hf2]
    rfl
  rw [h_coeff, h_rhs] at hparse
  exact hparse

end TorusParseval

/-- **Full 3D Vector Parseval Identity on `𝕋³`:**
    For any continuous `ℤ³`-periodic vector field `u : R3 → R3`:
      `∑' k : ℤ³, |û(k)|² = ∫_{𝕋³} |u(x)|² dx` (`0 sorryAx`). -/
theorem hasSum_sq_fourierCoeff3DVec
    {u : R3 → R3} (hu : Continuous u) (hpu : IsPeriodic3D u) :
    HasSum (fun k : Fin 3 → ℤ => normSqC3 (fourierCoeff3DVec u k))
      (torusIntegral (fun x => dot3D (u x) (u x))) := by
  have hu0 : Continuous (fun x => u x 0) := (continuous_apply 0).comp hu
  have hu1 : Continuous (fun x => u x 1) := (continuous_apply 1).comp hu
  have hu2 : Continuous (fun x => u x 2) := (continuous_apply 2).comp hu
  have hpu0 : IsPeriodic3D (fun x => u x 0) := fun x i => congrArg (fun v => v 0) (hpu x i)
  have hpu1 : IsPeriodic3D (fun x => u x 1) := fun x i => congrArg (fun v => v 1) (hpu x i)
  have hpu2 : IsPeriodic3D (fun x => u x 2) := fun x i => congrArg (fun v => v 2) (hpu x i)
  have h0 := hasSum_sq_fourierCoeff3D hu0 hpu0
  have h1 := hasSum_sq_fourierCoeff3D hu1 hpu1
  have h2 := hasSum_sq_fourierCoeff3D hu2 hpu2
  have hsum := (h0.add h1).add h2
  have hdot : torusIntegral (fun x => (u x 0) ^ 2) + torusIntegral (fun x => (u x 1) ^ 2) +
      torusIntegral (fun x => (u x 2) ^ 2) = torusIntegral (fun x => dot3D (u x) (u x)) := by
    have hpt : ∀ x : R3, dot3D (u x) (u x) = (u x 0) ^ 2 + (u x 1) ^ 2 + (u x 2) ^ 2 := fun x => by
      unfold dot3D; ring
    have hc0 : Continuous (fun x => (u x 0) ^ 2) := hu0.pow 2
    have hc1 : Continuous (fun x => (u x 1) ^ 2) := hu1.pow 2
    have hc2 : Continuous (fun x => (u x 2) ^ 2) := hu2.pow 2
    rw [torusIntegral_congr hpt, torusIntegral_add3 hc0 hc1 hc2]
  rw [hdot] at hsum
  exact hsum

-- ============================================================================
-- SECTION 3: ISOTROPIC 3D SPHERICAL-SHELL BERNSTEIN & SOBOLEV `H¹ / H²` NORMS
-- ============================================================================

/-- **Spectral `Ḣ¹(𝕋³)` Gradient Norm Identity (Scalar):**
    `∑' k : ℤ³, 4π² |k|² ‖f̂(k)‖² = ∫_{𝕋³} |∇f(x)|² dx` (`0 sorryAx`). -/
theorem hasSum_gradNormSq_scalar
    {f : R3 → ℝ} (hf : ContDiff ℝ 1 f) (hpf : IsPeriodic3D f) :
    HasSum (fun k : Fin 3 → ℤ => 4 * Real.pi ^ 2 * kNormSq k * ‖fourierCoeff3D f k‖ ^ 2)
      (torusIntegral (fun x =>
        (partialDerivScalar f x 0) ^ 2 +
        (partialDerivScalar f x 1) ^ 2 +
        (partialDerivScalar f x 2) ^ 2)) := by
  have hdiff : Differentiable ℝ f := hf.differentiable (by simp)
  have hc0 := continuous_partialDerivScalar_of_contDiff hf 0
  have hc1 := continuous_partialDerivScalar_of_contDiff hf 1
  have hc2 := continuous_partialDerivScalar_of_contDiff hf 2
  have hp0 := IsPeriodic3D.partialDeriv hpf hdiff 0
  have hp1 := IsPeriodic3D.partialDeriv hpf hdiff 1
  have hp2 := IsPeriodic3D.partialDeriv hpf hdiff 2
  have hsum := ((hasSum_sq_fourierCoeff3D hc0 hp0).add (hasSum_sq_fourierCoeff3D hc1 hp1)).add
    (hasSum_sq_fourierCoeff3D hc2 hp2)
  have hterm : ∀ k : Fin 3 → ℤ,
      ‖fourierCoeff3D (fun x => partialDerivScalar f x 0) k‖ ^ 2 +
      ‖fourierCoeff3D (fun x => partialDerivScalar f x 1) k‖ ^ 2 +
      ‖fourierCoeff3D (fun x => partialDerivScalar f x 2) k‖ ^ 2 =
      4 * Real.pi ^ 2 * kNormSq k * ‖fourierCoeff3D f k‖ ^ 2 := by
    intro k
    have hnorm_axis : ∀ j : Fin 3,
        ‖fourierCoeff3D (fun x => partialDerivScalar f x j) k‖ ^ 2 =
          4 * Real.pi ^ 2 * (k j : ℝ) ^ 2 * ‖fourierCoeff3D f k‖ ^ 2 := by
      intro j
      rw [fourierCoeff3D_partialDeriv hf hpf k j, norm_mul, mul_pow]
      have hfac : ‖2 * (Real.pi : ℂ) * Complex.I * (k j : ℂ)‖ ^ 2 = 4 * Real.pi ^ 2 * (k j : ℝ) ^ 2 := by
        rw [norm_mul, norm_mul, norm_mul, Complex.norm_I, mul_one]
        have h1 : ‖(2 : ℂ)‖ = 2 := by norm_num
        have h2 : ‖(Real.pi : ℂ)‖ = Real.pi := by
          rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
        have h3 : ‖(k j : ℂ)‖ = |(k j : ℝ)| := by
          rw [← Complex.ofReal_intCast, Complex.norm_real, Real.norm_eq_abs]
        rw [h1, h2, h3, mul_pow, mul_pow, sq_abs]; ring
      rw [hfac]
    rw [hnorm_axis 0, hnorm_axis 1, hnorm_axis 2]
    unfold kNormSq; ring
  have hfun : (fun k => ‖fourierCoeff3D (fun x => partialDerivScalar f x 0) k‖ ^ 2 +
      ‖fourierCoeff3D (fun x => partialDerivScalar f x 1) k‖ ^ 2 +
      ‖fourierCoeff3D (fun x => partialDerivScalar f x 2) k‖ ^ 2) =
      (fun k => 4 * Real.pi ^ 2 * kNormSq k * ‖fourierCoeff3D f k‖ ^ 2) := funext hterm
  have hc0_sq : Continuous (fun x => (partialDerivScalar f x 0) ^ 2) := hc0.pow 2
  have hc1_sq : Continuous (fun x => (partialDerivScalar f x 1) ^ 2) := hc1.pow 2
  have hc2_sq : Continuous (fun x => (partialDerivScalar f x 2) ^ 2) := hc2.pow 2
  rw [hfun, ← torusIntegral_add3 hc0_sq hc1_sq hc2_sq] at hsum
  exact hsum

/-- **MAIN THEOREM 2 OF MILESTONE 5B (Isotropic 3D Spherical-Shell Bernstein Inequality):**
    If all Fourier modes inside the 3D ball `|k|² < R²` vanish (`fourierCoeff3D f k = 0`), then
      `4π² R² ∫_{𝕋³} f(x)² dx ≤ ∫_{𝕋³} |∇f(x)|² dx` (`0 sorryAx`). -/
theorem isotropic_bernstein_3d_torus
    {f : R3 → ℝ} {R : ℝ} (hf : ContDiff ℝ 1 f) (hpf : IsPeriodic3D f)
    (h_ball_zero : ∀ k : Fin 3 → ℤ, kNormSq k < R ^ 2 → fourierCoeff3D f k = 0) :
    4 * Real.pi ^ 2 * R ^ 2 * torusIntegral (fun x => (f x) ^ 2) ≤
      torusIntegral (fun x =>
        (partialDerivScalar f x 0) ^ 2 +
        (partialDerivScalar f x 1) ^ 2 +
        (partialDerivScalar f x 2) ^ 2) := by
  have h1 := (hasSum_sq_fourierCoeff3D hf.continuous hpf).mul_left (4 * Real.pi ^ 2 * R ^ 2)
  have h2 := hasSum_gradNormSq_scalar hf hpf
  refine hasSum_le (fun k => ?_) h1 h2
  by_cases hlt : kNormSq k < R ^ 2
  · rw [h_ball_zero k hlt, norm_zero, zero_pow (by norm_num : 2 ≠ 0), mul_zero]
    have hk_nn : 0 ≤ kNormSq k := by unfold kNormSq; positivity
    positivity
  · push Not at hlt
    have hfac : 0 ≤ 4 * Real.pi ^ 2 * ‖fourierCoeff3D f k‖ ^ 2 := by positivity
    nlinarith

/-- **Spectral `Ḣ¹(𝕋³)` Gradient Norm Identity (Vector):**
    `∑' k : ℤ³, 4π² |k|² |û(k)|² = ∫_{𝕋³} |∇u(x)|² dx` (`0 sorryAx`). -/
theorem hasSum_gradNormSq_vec
    {u : R3 → R3} (hu : ContDiff ℝ 1 u) (hpu : IsPeriodic3D u) :
    HasSum (fun k : Fin 3 → ℤ => 4 * Real.pi ^ 2 * kNormSq k * normSqC3 (fourierCoeff3DVec u k))
      (torusIntegral (gradNormSq3D u)) := by
  have hu0 : ContDiff ℝ 1 (fun y => u y 0) := contDiff_pi.mp hu 0
  have hu1 : ContDiff ℝ 1 (fun y => u y 1) := contDiff_pi.mp hu 1
  have hu2 : ContDiff ℝ 1 (fun y => u y 2) := contDiff_pi.mp hu 2
  have hpu0 : IsPeriodic3D (fun y => u y 0) := fun x i => congrArg (fun v => v 0) (hpu x i)
  have hpu1 : IsPeriodic3D (fun y => u y 1) := fun x i => congrArg (fun v => v 1) (hpu x i)
  have hpu2 : IsPeriodic3D (fun y => u y 2) := fun x i => congrArg (fun v => v 2) (hpu x i)
  have hsum := ((hasSum_gradNormSq_scalar hu0 hpu0).add (hasSum_gradNormSq_scalar hu1 hpu1)).add
    (hasSum_gradNormSq_scalar hu2 hpu2)
  have hfun : (fun k => 4 * Real.pi ^ 2 * kNormSq k * ‖fourierCoeff3D (fun y => u y 0) k‖ ^ 2 +
      4 * Real.pi ^ 2 * kNormSq k * ‖fourierCoeff3D (fun y => u y 1) k‖ ^ 2 +
      4 * Real.pi ^ 2 * kNormSq k * ‖fourierCoeff3D (fun y => u y 2) k‖ ^ 2) =
      (fun k => 4 * Real.pi ^ 2 * kNormSq k * normSqC3 (fourierCoeff3DVec u k)) := by
    funext k; unfold normSqC3 fourierCoeff3DVec; ring
  have hq : ∀ (f : R3 → ℝ), ContDiff ℝ 1 f → Continuous (fun x =>
      (partialDerivScalar f x 0) ^ 2 + (partialDerivScalar f x 1) ^ 2 + (partialDerivScalar f x 2) ^ 2) :=
    fun f hf =>
      (((continuous_partialDerivScalar_of_contDiff hf 0).pow 2).add
       ((continuous_partialDerivScalar_of_contDiff hf 1).pow 2)).add
      ((continuous_partialDerivScalar_of_contDiff hf 2).pow 2)
  have hgrad : torusIntegral (fun x => (partialDerivScalar (fun y => u y 0) x 0) ^ 2 +
        (partialDerivScalar (fun y => u y 0) x 1) ^ 2 + (partialDerivScalar (fun y => u y 0) x 2) ^ 2) +
      torusIntegral (fun x => (partialDerivScalar (fun y => u y 1) x 0) ^ 2 +
        (partialDerivScalar (fun y => u y 1) x 1) ^ 2 + (partialDerivScalar (fun y => u y 1) x 2) ^ 2) +
      torusIntegral (fun x => (partialDerivScalar (fun y => u y 2) x 0) ^ 2 +
        (partialDerivScalar (fun y => u y 2) x 1) ^ 2 + (partialDerivScalar (fun y => u y 2) x 2) ^ 2) =
      torusIntegral (gradNormSq3D u) := by
    have hpt : ∀ x : R3, gradNormSq3D u x =
        ((partialDerivScalar (fun y => u y 0) x 0) ^ 2 +
         (partialDerivScalar (fun y => u y 0) x 1) ^ 2 + (partialDerivScalar (fun y => u y 0) x 2) ^ 2) +
        ((partialDerivScalar (fun y => u y 1) x 0) ^ 2 +
         (partialDerivScalar (fun y => u y 1) x 1) ^ 2 + (partialDerivScalar (fun y => u y 1) x 2) ^ 2) +
        ((partialDerivScalar (fun y => u y 2) x 0) ^ 2 +
         (partialDerivScalar (fun y => u y 2) x 1) ^ 2 + (partialDerivScalar (fun y => u y 2) x 2) ^ 2) :=
      fun x => by unfold gradNormSq3D; ring
    rw [torusIntegral_congr hpt, torusIntegral_add3 (hq _ hu0) (hq _ hu1) (hq _ hu2)]
  rw [hfun, hgrad] at hsum
  exact hsum

private theorem isPeriodic3D_laplacianScalar {f : R3 → ℝ} (hf : ContDiff ℝ 2 f) (hpf : IsPeriodic3D f) :
    IsPeriodic3D (laplacianScalar f) := by
  have hf1 : ContDiff ℝ 1 f := contDiff_one_of_two5b hf
  have haxis : ∀ (j : Fin 3) (x : R3) (i : Fin 3),
      sndPartial f (x + basisVec i) j j = sndPartial f x j j := by
    intro j x i
    have hgj : ContDiff ℝ 1 (fun y => partialDerivScalar f y j) := contDiff_one_partialDerivScalar hf j
    have hpgj : IsPeriodic3D (fun y => partialDerivScalar f y j) :=
      IsPeriodic3D.partialDeriv hpf (hf1.differentiable (by simp)) j
    have hpjj := IsPeriodic3D.partialDeriv hpgj (hgj.differentiable (by simp)) j x i
    dsimp only at hpjj
    rw [← partial_partial_eq_sndPartial f (x + basisVec i) hf.contDiffAt j j,
        ← partial_partial_eq_sndPartial f x hf.contDiffAt j j]
    exact hpjj
  intro x i
  unfold laplacianScalar
  rw [haxis 0 x i, haxis 1 x i, haxis 2 x i]

private theorem isPeriodic3D_laplacian3D {u : R3 → R3} (hu : ContDiff ℝ 2 u) (hpu : IsPeriodic3D u) :
    IsPeriodic3D (laplacian3D u) := by
  intro x i; funext c
  exact isPeriodic3D_laplacianScalar (contDiff_pi.mp hu c)
    (fun y j => congrArg (fun v => v c) (hpu y j)) x i

private theorem isPeriodic3D_grad3D {p : R3 → ℝ} (hp : ContDiff ℝ 1 p) (hpp : IsPeriodic3D p) :
    IsPeriodic3D (grad3D p) := by
  intro x i; funext c
  exact IsPeriodic3D.partialDeriv hpp (hp.differentiable (by simp)) c x i

private theorem isPeriodic3D_advection3D {u : R3 → R3} (hu : ContDiff ℝ 1 u) (hpu : IsPeriodic3D u) :
    IsPeriodic3D (advection3D u) := by
  intro x i; funext c
  have huc : ContDiff ℝ 1 (fun y => u y c) := contDiff_pi.mp hu c
  have hpuc : IsPeriodic3D (fun y => u y c) := fun y j => congrArg (fun v => v c) (hpu y j)
  have hdu : Differentiable ℝ (fun y => u y c) := huc.differentiable (by simp)
  have hp0 : partialDerivScalar (fun y => u y c) (x + basisVec i) 0 =
      partialDerivScalar (fun y => u y c) x 0 := IsPeriodic3D.partialDeriv hpuc hdu 0 x i
  have hp1 : partialDerivScalar (fun y => u y c) (x + basisVec i) 1 =
      partialDerivScalar (fun y => u y c) x 1 := IsPeriodic3D.partialDeriv hpuc hdu 1 x i
  have hp2 : partialDerivScalar (fun y => u y c) (x + basisVec i) 2 =
      partialDerivScalar (fun y => u y c) x 2 := IsPeriodic3D.partialDeriv hpuc hdu 2 x i
  unfold advection3D
  rw [hpu x i, hp0, hp1, hp2]

/-- **Spectral `Ḣ²(𝕋³)` Laplacian Norm Identity (Vector):**
    `∑' k : ℤ³, 16π⁴ |k|⁴ |û(k)|² = ∫_{𝕋³} |Δu(x)|² dx` (`0 sorryAx`). -/
theorem hasSum_laplacianNormSq_vec
    {u : R3 → R3} (hu : ContDiff ℝ 2 u) (hpu : IsPeriodic3D u) :
    HasSum (fun k : Fin 3 → ℤ => 16 * Real.pi ^ 4 * (kNormSq k) ^ 2 * normSqC3 (fourierCoeff3DVec u k))
      (torusIntegral (fun x => dot3D (laplacian3D u x) (laplacian3D u x))) := by
  have hu0 : ContDiff ℝ 2 (fun y => u y 0) := contDiff_pi.mp hu 0
  have hu1 : ContDiff ℝ 2 (fun y => u y 1) := contDiff_pi.mp hu 1
  have hu2 : ContDiff ℝ 2 (fun y => u y 2) := contDiff_pi.mp hu 2
  have hpu0 : IsPeriodic3D (fun y => u y 0) := fun x i => congrArg (fun v => v 0) (hpu x i)
  have hpu1 : IsPeriodic3D (fun y => u y 1) := fun x i => congrArg (fun v => v 1) (hpu x i)
  have hpu2 : IsPeriodic3D (fun y => u y 2) := fun x i => congrArg (fun v => v 2) (hpu x i)
  have hparse := hasSum_sq_fourierCoeff3DVec (continuous_laplacian3D hu) (isPeriodic3D_laplacian3D hu hpu)
  have hfun : (fun k => normSqC3 (fourierCoeff3DVec (laplacian3D u) k)) =
      (fun k => 16 * Real.pi ^ 4 * (kNormSq k) ^ 2 * normSqC3 (fourierCoeff3DVec u k)) := by
    funext k
    have hnorm_lap : ‖(-4 : ℂ) * (Real.pi : ℂ) ^ 2 *
        ((k 0 : ℂ) ^ 2 + (k 1 : ℂ) ^ 2 + (k 2 : ℂ) ^ 2)‖ ^ 2 =
        16 * Real.pi ^ 4 * (kNormSq k) ^ 2 := by
      have hk_eq : (-4 : ℂ) * (Real.pi : ℂ) ^ 2 *
          ((k 0 : ℂ) ^ 2 + (k 1 : ℂ) ^ 2 + (k 2 : ℂ) ^ 2) =
          ((-4 * Real.pi ^ 2 * kNormSq k : ℝ) : ℂ) := by
        unfold kNormSq; push_cast; ring
      rw [hk_eq, Complex.norm_real, Real.norm_eq_abs, sq_abs]
      ring
    have hcomp : ∀ (f : R3 → ℝ), ContDiff ℝ 2 f → IsPeriodic3D f →
        ‖fourierCoeff3D (laplacianScalar f) k‖ ^ 2 =
          16 * Real.pi ^ 4 * (kNormSq k) ^ 2 * ‖fourierCoeff3D f k‖ ^ 2 := fun f hf hpf => by
      rw [fourierCoeff3D_laplacianScalar hf hpf k, norm_mul, mul_pow, hnorm_lap]
    unfold normSqC3 fourierCoeff3DVec laplacian3D
    rw [hcomp _ hu0 hpu0, hcomp _ hu1 hpu1, hcomp _ hu2 hpu2]
    ring
  rw [hfun] at hparse
  exact hparse

/-- **Exact Palinstrophy–Laplacian Identity on `𝕋³` (`P = ∫ |∇ω|² = ∫ |Δu|²`):**
    For any `C³` periodic solenoidal velocity field `u`:
      `palinstrophy3D u = ∫_{𝕋³} |Δu(x)|² dx` (`0 sorryAx`). -/
theorem palinstrophy_eq_laplacianNormSq
    {u : R3 → R3} (hu : ContDiff ℝ 3 u) (hpu : IsPeriodic3D u)
    (hdiv : ∀ x : R3, div3D u x = 0) :
    palinstrophy3D u = torusIntegral (fun x => dot3D (laplacian3D u x) (laplacian3D u x)) := by
  have hu2 : ContDiff ℝ 2 u := contDiff_two_of_three5b hu
  have hu1 : ContDiff ℝ 1 u := contDiff_one_of_two5b hu2
  have hw1 : ContDiff ℝ 1 (curl3D u) := contDiff_one_of_two5b (contDiff_two_curl3D hu)
  have hpw : IsPeriodic3D (curl3D u) := hpu.curl3D (hu1.differentiable (by simp))
  have hP := hasSum_gradNormSq_vec hw1 hpw
  have hL := hasSum_laplacianNormSq_vec hu2 hpu
  have h_term : ∀ k : Fin 3 → ℤ,
      4 * Real.pi ^ 2 * kNormSq k * normSqC3 (fourierCoeff3DVec (curl3D u) k) =
      16 * Real.pi ^ 4 * (kNormSq k) ^ 2 * normSqC3 (fourierCoeff3DVec u k) := by
    intro k
    by_cases hk : k = 0
    · subst hk; unfold kNormSq; simp
    · have hbs := (biot_savart_3d_spectral hu1 hpu hdiv hk).2
      rw [hbs]; ring
  have hfun : (fun k => 4 * Real.pi ^ 2 * kNormSq k * normSqC3 (fourierCoeff3DVec (curl3D u) k)) =
      (fun k => 16 * Real.pi ^ 4 * (kNormSq k) ^ 2 * normSqC3 (fourierCoeff3DVec u k)) :=
    funext h_term
  rw [hfun] at hP
  exact hP.unique hL

-- ============================================================================
-- SECTION 4: GLOBAL `L²(𝕋³)` CALDERÓN–ZYGMUND BOUND & `L²–H¹–H²` INTERPOLATION
-- ============================================================================

/-- **MAIN THEOREM 3 OF MILESTONE 5B (Global Unconditional `L²(𝕋³)` Calderón–Zygmund
    Pressure Gradient Bound):**
    For EVERY periodic classical 3D Navier-Stokes solution `(u, p)` and EVERY `t ≥ 0`:
      `∫_{𝕋³} |∇p(t, x)|² dx ≤ ∫_{𝕋³} |(u·∇)u(t, x)|² dx` (`0 sorryAx`). -/
theorem global_calderon_zygmund_pressure_L2_torus3D
    {u : ℝ → R3 → R3} {p : ℝ → R3 → ℝ} {ν : ℝ}
    (hns : IsPeriodicClassicalNS3D_C3 u p ν) {t : ℝ} (ht : t ≥ 0) :
    torusIntegral (fun x => dot3D (grad3D (p t) x) (grad3D (p t) x)) ≤
      torusIntegral (fun x => dot3D (advection3D (u t) x) (advection3D (u t) x)) := by
  have hu2 : ContDiff ℝ 2 (u t) := contDiff_two_of_three5b (hns.h_u_c3_global t ht)
  have hu1 : ContDiff ℝ 1 (u t) := contDiff_one_of_two5b hu2
  have hp1 : ContDiff ℝ 1 (p t) := contDiff_one_of_two5b (hns.h_p_c2_global t ht)
  have hpu : IsPeriodic3D (u t) := hns.h_u_periodic t ht
  have hpp : IsPeriodic3D (p t) := hns.h_p_periodic t ht
  have hsum_gp := hasSum_sq_fourierCoeff3DVec (continuous_grad3D hp1) (isPeriodic3D_grad3D hp1 hpp)
  have hsum_adv := hasSum_sq_fourierCoeff3DVec (continuous_advection3D hu1) (isPeriodic3D_advection3D hu1 hpu)
  refine hasSum_le (fun k => ?_) hsum_gp hsum_adv
  by_cases hk : k = 0
  · subst hk
    have h0 : ∀ c : Fin 3, fourierCoeff3DVec (grad3D (p t)) 0 c = 0 := fun c => by
      have h := fourierCoeff3D_partialDeriv hp1 hpp 0 c
      simpa [fourierCoeff3DVec, grad3D] using h
    have hnorm0 : normSqC3 (fourierCoeff3DVec (grad3D (p t)) 0) = 0 := by
      unfold normSqC3; rw [h0 0, h0 1, h0 2]; simp
    rw [hnorm0]
    exact normSqC3_nonneg _
  · exact (pressure_poisson_and_calderon_zygmund_spectral hns ht hk).2.2.2

/-- **MAIN THEOREM 4 OF MILESTONE 5B (Periodic Sobolev `L²–H¹–H²` Interpolation Inequality):**
    For any `C²` periodic vector field `u : R3 → R3`:
      `(∫_{𝕋³} |∇u|² dx)² ≤ (∫_{𝕋³} |u|² dx) · (∫_{𝕋³} |Δu|² dx)` (`0 sorryAx`). -/
theorem sobolev_interp_L2_H1_H2_torus3D
    {u : R3 → R3} (hu : ContDiff ℝ 2 u) (hpu : IsPeriodic3D u) :
    (torusIntegral (gradNormSq3D u)) ^ 2 ≤
      torusIntegral (fun x => dot3D (u x) (u x)) *
      torusIntegral (fun x => dot3D (laplacian3D u x) (laplacian3D u x)) := by
  have hu1 : ContDiff ℝ 1 u := contDiff_one_of_two5b hu
  let E2 : ℝ := torusIntegral (fun x => dot3D (u x) (u x))
  let G2 : ℝ := torusIntegral (gradNormSq3D u)
  let L2 : ℝ := torusIntegral (fun x => dot3D (laplacian3D u x) (laplacian3D u x))
  have hE := hasSum_sq_fourierCoeff3DVec hu.continuous hpu
  have hG := hasSum_gradNormSq_vec hu1 hpu
  have hL := hasSum_laplacianNormSq_vec hu hpu
  have hquad : ∀ r : ℝ, 0 ≤ r ^ 2 * E2 - 2 * r * G2 + L2 := by
    intro r
    have hcomb := ((hE.mul_left (r ^ 2)).sub (hG.mul_left (2 * r))).add hL
    have hnn : ∀ k : Fin 3 → ℤ,
        0 ≤ r ^ 2 * normSqC3 (fourierCoeff3DVec u k) -
          2 * r * (4 * Real.pi ^ 2 * kNormSq k * normSqC3 (fourierCoeff3DVec u k)) +
          16 * Real.pi ^ 4 * (kNormSq k) ^ 2 * normSqC3 (fourierCoeff3DVec u k) := by
      intro k
      have hfac : r ^ 2 * normSqC3 (fourierCoeff3DVec u k) -
          2 * r * (4 * Real.pi ^ 2 * kNormSq k * normSqC3 (fourierCoeff3DVec u k)) +
          16 * Real.pi ^ 4 * (kNormSq k) ^ 2 * normSqC3 (fourierCoeff3DVec u k) =
          (r - 4 * Real.pi ^ 2 * kNormSq k) ^ 2 * normSqC3 (fourierCoeff3DVec u k) := by ring
      rw [hfac]
      exact mul_nonneg (sq_nonneg _) (normSqC3_nonneg _)
    exact hasSum_le hnn hasSum_zero hcomb
  have hE_nn : 0 ≤ E2 := torusIntegral_nonneg (continuous_dot3D hu.continuous hu.continuous)
    (fun x => by
      unfold dot3D
      have h0 : 0 ≤ u x 0 * u x 0 := mul_self_nonneg _
      have h1 : 0 ≤ u x 1 * u x 1 := mul_self_nonneg _
      have h2 : 0 ≤ u x 2 * u x 2 := mul_self_nonneg _
      linarith)
  change G2 ^ 2 ≤ E2 * L2
  rcases eq_or_lt_of_le hE_nn with hE0 | hE_pos
  · have hG0 : G2 = 0 := by
      by_contra hne
      have h1 := hquad ((L2 + 1) / (2 * G2))
      have h2G : 2 * G2 ≠ 0 := mul_ne_zero (by norm_num) hne
      rw [← hE0, mul_zero, zero_sub] at h1
      have hcalc : 2 * ((L2 + 1) / (2 * G2)) * G2 = L2 + 1 := by
        field_simp [h2G]
      linarith
    rw [hG0, ← hE0]; norm_num
  · have hq := hquad (G2 / E2)
    have hmul : 0 ≤ ((G2 / E2) ^ 2 * E2 - 2 * (G2 / E2) * G2 + L2) * E2 :=
      mul_nonneg hq (le_of_lt hE_pos)
    have hE_ne : E2 ≠ 0 := ne_of_gt hE_pos
    have halg : ((G2 / E2) ^ 2 * E2 - 2 * (G2 / E2) * G2 + L2) * E2 = E2 * L2 - G2 ^ 2 := by
      field_simp [hE_ne]; ring
    linarith

/-- **Navier–Stokes Enstrophy–Energy–Palinstrophy Interpolation (`2 Z(t)² ≤ E(t) · P(t)`):**
    Unconditional interpolation bound for EVERY periodic classical 3D Navier–Stokes solution:
      `2 * (enstrophy u t)² ≤ kineticEnergy u t * palinstrophy3D (u t)` (`0 sorryAx`). -/
theorem enstrophy_sq_le_energy_mul_palinstrophy
    {u : ℝ → R3 → R3} {p : ℝ → R3 → ℝ} {ν : ℝ}
    (hns : IsPeriodicClassicalNS3D_C3 u p ν) {t : ℝ} (ht : t ≥ 0) :
    2 * (enstrophy u t) ^ 2 ≤ kineticEnergy u t * palinstrophy3D (u t) := by
  have hu3 : ContDiff ℝ 3 (u t) := hns.h_u_c3_global t ht
  have hu2 : ContDiff ℝ 2 (u t) := contDiff_two_of_three5b hu3
  have hpu : IsPeriodic3D (u t) := hns.h_u_periodic t ht
  have hdiv : ∀ x : R3, div3D (u t) x = 0 := hns.h_incompressible t ht
  have h_interp := sobolev_interp_L2_H1_H2_torus3D hu2 hpu
  have hZ : torusIntegral (gradNormSq3D (u t)) = 2 * enstrophy u t := by
    have h := enstrophy_eq_half_gradNormSq hu2 hpu hdiv
    unfold enstrophy; linarith
  have hP := palinstrophy_eq_laplacianNormSq hu3 hpu hdiv
  have hE : torusIntegral (fun x => dot3D (u t x) (u t x)) = 2 * kineticEnergy u t := by
    unfold kineticEnergy; ring
  rw [hZ, hE, ← hP] at h_interp
  nlinarith

-- ============================================================================
-- SECTION 5: AXIOM AUDIT TRAIL (0 sorryAx)
-- ============================================================================

#print axioms hasSum_sq_fourierCoeff3D
#print axioms hasSum_sq_fourierCoeff3DVec
#print axioms hasSum_gradNormSq_scalar
#print axioms isotropic_bernstein_3d_torus
#print axioms hasSum_gradNormSq_vec
#print axioms hasSum_laplacianNormSq_vec
#print axioms palinstrophy_eq_laplacianNormSq
#print axioms global_calderon_zygmund_pressure_L2_torus3D
#print axioms sobolev_interp_L2_H1_H2_torus3D
#print axioms enstrophy_sq_le_energy_mul_palinstrophy

end GarryParsevalSobolev3D