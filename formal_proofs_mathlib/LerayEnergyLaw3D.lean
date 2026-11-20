import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import LerayEnergyTorus3D

/-!
# GARRYULT v4.0.0 — Milestone 3B: Leibniz Rule, Global Leray Energy Balance (`E(T) ≤ E(0)`)
# & Exact Time-Differentiated Enstrophy Law (`Z'(t) = S_stretch(t) - ν P(t)`) on `𝕋³`
Closes the measure-theoretic energy & enstrophy layer by pulling `d/dt` outside the 3D
Lebesgue torus integral via dominated differentiation (`ParametricIntegral`), proving
directly from `IsPeriodicClassicalNS3D_C3` with zero additional hypotheses (`0 sorryAx`):
1. `E'(t) = -ν ∫_{𝕋³} |∇u(t, x)|² dx` for all `t ≥ 0`.
2. `E(T) + ν ∫_0^T ∫_{𝕋³} |∇u(s, x)|² dx ds = E(0)` and `0 ≤ E(T) ≤ E(0)` for all `T ≥ 0`.
3. `Z'(t) = S_stretch(t) - ν P(t)` for all `t ≥ 0`.
4. Conditional enstrophy monotonicity: `S_stretch ≤ ν P` on `[0, T]` implies `Z(T) ≤ Z(0)`.
-/

namespace GarryLerayEnergyLaw3D

open MeasureTheory Filter Topology GarryReal3DCalculus GarryVorticity3D GarryLerayTorus3D

-- ============================================================================
-- SECTION 1: TRUE ENERGY, ENSTROPHY, STRETCHING & PALINSTROPHY FUNCTIONALS
-- ============================================================================

/-- True `L²` kinetic energy on `𝕋³`: `E(t) = ½ ∫_{𝕋³} |u(t, x)|² dx`. -/
noncomputable def kineticEnergy (u : ℝ → R3 → R3) (t : ℝ) : ℝ :=
  (1 / 2 : ℝ) * torusIntegral (fun x => dot3D (u t x) (u t x))

/-- True `H¹` enstrophy on `𝕋³`: `Z(t) = ½ ∫_{𝕋³} |ω(t, x)|² dx` with `ω = ∇ × u`. -/
noncomputable def enstrophy (u : ℝ → R3 → R3) (t : ℝ) : ℝ :=
  (1 / 2 : ℝ) * torusIntegral (fun x => dot3D (curl3D (u t) x) (curl3D (u t) x))

/-- True 3D nonlinear vortex stretching integral `S_stretch = ∫_{𝕋³} ⟨(ω · ∇)u, ω⟩ dx`. -/
noncomputable def vortexStretching3D (u : R3 → R3) : ℝ :=
  torusIntegral (fun x => dot3D (directionalAdvection3D (curl3D u) u x) (curl3D u x))

/-- True 3D palinstrophy integral `P = ∫_{𝕋³} |∇ω|² dx`. -/
noncomputable def palinstrophy3D (u : R3 → R3) : ℝ :=
  torusIntegral (gradNormSq3D (curl3D u))

theorem dot3D_self_nonneg (v : R3) : 0 ≤ dot3D v v := by
  unfold dot3D
  have h0 : 0 ≤ v 0 * v 0 := mul_self_nonneg (v 0)
  have h1 : 0 ≤ v 1 * v 1 := mul_self_nonneg (v 1)
  have h2 : 0 ≤ v 2 * v 2 := mul_self_nonneg (v 2)
  linarith

-- ============================================================================
-- SECTION 2: LOCAL PRODUCT MEASURE ON `[0, 1]³` & 3D LEIBNIZ RULE
-- ============================================================================

private noncomputable abbrev unitCube : Set (ℝ × (ℝ × ℝ)) :=
  Set.Icc (0 : ℝ) 1 ×ˢ (Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1)

private noncomputable abbrev unitMeas : Measure ℝ := volume.restrict (Set.Icc (0 : ℝ) 1)

private noncomputable abbrev unitMeas3 : Measure (ℝ × (ℝ × ℝ)) :=
  unitMeas.prod (unitMeas.prod unitMeas)

private theorem isCompact_unitCube : IsCompact unitCube :=
  isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc)

private theorem measurableSet_unitCube : MeasurableSet unitCube :=
  measurableSet_Icc.prod (measurableSet_Icc.prod measurableSet_Icc)

private theorem unitMeas3_eq_restrict :
    unitMeas3 = (volume : Measure (ℝ × (ℝ × ℝ))).restrict unitCube := by
  unfold unitMeas3 unitMeas unitCube
  rw [Measure.prod_restrict, Measure.prod_restrict]
  rfl

private theorem isFiniteMeasure_unitMeas3 : IsFiniteMeasure unitMeas3 :=
  ⟨by rw [unitMeas3_eq_restrict, Measure.restrict_apply_univ]; exact isCompact_unitCube.measure_lt_top⟩

private theorem ae_mem_unitCube : ∀ᵐ q ∂unitMeas3, q ∈ unitCube := by
  rw [unitMeas3_eq_restrict]
  exact ae_restrict_mem measurableSet_unitCube

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

private theorem integrable_unitMeas3_of_continuous {g : R3 → ℝ} (hg : Continuous g) :
    Integrable (fun q : ℝ × (ℝ × ℝ) => g (vec3 q.1 q.2.1 q.2.2)) unitMeas3 := by
  rw [unitMeas3_eq_restrict]
  exact (hg.comp continuous_vec3_triple).continuousOn.integrableOn_compact isCompact_unitCube

private theorem torusIntegral_eq_unitMeas3 {g : R3 → ℝ} (hg : Continuous g) :
    torusIntegral g = ∫ q : ℝ × (ℝ × ℝ), g (vec3 q.1 q.2.1 q.2.2) ∂unitMeas3 := by
  unfold torusIntegral
  simp_rw [intervalIntegral_eq_unitMeas]
  have h_inner : ∀ x : ℝ,
      (∫ y, (∫ z, g (vec3 x y z) ∂unitMeas) ∂unitMeas) =
      ∫ p : ℝ × ℝ, g (vec3 x p.1 p.2) ∂(unitMeas.prod unitMeas) := fun x =>
    (MeasureTheory.integral_prod (fun p : ℝ × ℝ => g (vec3 x p.1 p.2))
      (integrable_unitMeas_prod2 (hg.comp (continuous_vec3_yz x)))).symm
  simp_rw [h_inner]
  exact (MeasureTheory.integral_prod (fun q : ℝ × (ℝ × ℝ) => g (vec3 q.1 q.2.1 q.2.2))
    (integrable_unitMeas3_of_continuous hg)).symm

/-- **3D Torus Leibniz Rule:** Differentiation under the 3D Lebesgue integral over `𝕋³ = [0, 1]³`
    for jointly continuous `F` and `∂_t F`. -/
theorem hasDerivAt_torusIntegral_of_continuous
    {F F' : ℝ → R3 → ℝ}
    (hF_cont : Continuous (fun p : ℝ × R3 => F p.1 p.2))
    (hF'_cont : Continuous (fun p : ℝ × R3 => F' p.1 p.2))
    (h_diff : ∀ (t : ℝ) (x : R3), HasDerivAt (fun s => F s x) (F' t x) t)
    (t₀ : ℝ) :
    HasDerivAt (fun t => torusIntegral (F t)) (torusIntegral (F' t₀)) t₀ := by
  have : IsFiniteMeasure unitMeas3 := isFiniteMeasure_unitMeas3
  have hF_slice : ∀ t : ℝ, Continuous (F t) :=
    fun t => hF_cont.comp (continuous_const.prodMk continuous_id)
  have hF'_slice : ∀ t : ℝ, Continuous (F' t) :=
    fun t => hF'_cont.comp (continuous_const.prodMk continuous_id)
  have hG_eq : (fun t => torusIntegral (F t)) =
      (fun t => ∫ q : ℝ × (ℝ × ℝ), F t (vec3 q.1 q.2.1 q.2.2) ∂unitMeas3) := by
    funext t
    exact torusIntegral_eq_unitMeas3 (hF_slice t)
  rw [hG_eq, torusIntegral_eq_unitMeas3 (hF'_slice t₀)]
  let s : Set ℝ := Set.Icc (t₀ - 1) (t₀ + 1)
  have hs : s ∈ 𝓝 t₀ := Icc_mem_nhds (by linarith) (by linarith)
  have hK : IsCompact (s ×ˢ unitCube) := isCompact_Icc.prod isCompact_unitCube
  have hF'_prod_cont : Continuous (fun r : ℝ × (ℝ × (ℝ × ℝ)) => F' r.1 (vec3 r.2.1 r.2.2.1 r.2.2.2)) :=
    hF'_cont.comp (continuous_fst.prodMk (continuous_vec3_triple.comp continuous_snd))
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hF'_prod_cont.continuousOn
  have h_meas : ∀ᶠ t in 𝓝 t₀,
      AEStronglyMeasurable (fun q : ℝ × (ℝ × ℝ) => F t (vec3 q.1 q.2.1 q.2.2)) unitMeas3 :=
    Eventually.of_forall fun t => ((hF_slice t).comp continuous_vec3_triple).aestronglyMeasurable
  have h_int : Integrable (fun q : ℝ × (ℝ × ℝ) => F t₀ (vec3 q.1 q.2.1 q.2.2)) unitMeas3 :=
    integrable_unitMeas3_of_continuous (hF_slice t₀)
  have h_meas' : AEStronglyMeasurable (fun q : ℝ × (ℝ × ℝ) => F' t₀ (vec3 q.1 q.2.1 q.2.2)) unitMeas3 :=
    ((hF'_slice t₀).comp continuous_vec3_triple).aestronglyMeasurable
  have h_bound : ∀ᵐ q ∂unitMeas3, ∀ t ∈ s, ‖F' t (vec3 q.1 q.2.1 q.2.2)‖ ≤ C := by
    filter_upwards [ae_mem_unitCube] with q hq t ht
    exact hC (t, q) ⟨ht, hq⟩
  have h_bound_int : Integrable (fun _ : ℝ × (ℝ × ℝ) => C) unitMeas3 := integrable_const C
  have h_diff_ae : ∀ᵐ q ∂unitMeas3, ∀ t ∈ s,
      HasDerivAt (fun r => F r (vec3 q.1 q.2.1 q.2.2)) (F' t (vec3 q.1 q.2.1 q.2.2)) t :=
    Eventually.of_forall fun q t _ => h_diff t (vec3 q.1 q.2.1 q.2.2)
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le hs h_meas h_int h_meas'
    h_bound h_bound_int h_diff_ae).2

/-- Joint continuity of `G(t, x)` implies continuity of `t ↦ torusIntegral (G t)`. -/
theorem continuous_torusIntegral_of_joint_continuous
    {G : ℝ → R3 → ℝ} (hG_cont : Continuous (fun p : ℝ × R3 => G p.1 p.2)) :
    Continuous (fun t => torusIntegral (G t)) := by
  have : IsFiniteMeasure unitMeas3 := isFiniteMeasure_unitMeas3
  have hG_slice : ∀ t : ℝ, Continuous (G t) :=
    fun t => hG_cont.comp (continuous_const.prodMk continuous_id)
  have h_eq : (fun t => torusIntegral (G t)) =
      (fun t => ∫ q : ℝ × (ℝ × ℝ), G t (vec3 q.1 q.2.1 q.2.2) ∂unitMeas3) := by
    funext t
    exact torusIntegral_eq_unitMeas3 (hG_slice t)
  rw [h_eq]
  refine continuous_iff_continuousAt.mpr fun t₀ => ?_
  let s : Set ℝ := Set.Icc (t₀ - 1) (t₀ + 1)
  have hs : s ∈ 𝓝 t₀ := Icc_mem_nhds (by linarith) (by linarith)
  have hK : IsCompact (s ×ˢ unitCube) := isCompact_Icc.prod isCompact_unitCube
  have hG_prod_cont : Continuous (fun r : ℝ × (ℝ × (ℝ × ℝ)) => G r.1 (vec3 r.2.1 r.2.2.1 r.2.2.2)) :=
    hG_cont.comp (continuous_fst.prodMk (continuous_vec3_triple.comp continuous_snd))
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hG_prod_cont.continuousOn
  have h_meas : ∀ᶠ t in 𝓝 t₀,
      AEStronglyMeasurable (fun q : ℝ × (ℝ × ℝ) => G t (vec3 q.1 q.2.1 q.2.2)) unitMeas3 :=
    Eventually.of_forall fun t => ((hG_slice t).comp continuous_vec3_triple).aestronglyMeasurable
  have h_bound : ∀ᶠ t in 𝓝 t₀, ∀ᵐ q ∂unitMeas3, ‖G t (vec3 q.1 q.2.1 q.2.2)‖ ≤ C := by
    filter_upwards [hs] with t ht
    filter_upwards [ae_mem_unitCube] with q hq
    exact hC (t, q) ⟨ht, hq⟩
  have h_cont_ae : ∀ᵐ q ∂unitMeas3, ContinuousAt (fun t => G t (vec3 q.1 q.2.1 q.2.2)) t₀ :=
    Eventually.of_forall fun q =>
      (hG_cont.comp (continuous_id.prodMk continuous_const)).continuousAt
  exact continuousAt_of_dominated h_meas h_bound (integrable_const C) h_cont_ae

-- ============================================================================
-- SECTION 3: JOINT SPACE-TIME REGULARITY & POINTWISE `d/dt (½ |w|²) = ⟨∂_t w, w⟩`
-- ============================================================================

theorem hasDerivAt_half_dot3D_self
    {w : ℝ → R3} {w' : R3} {t : ℝ}
    (h0 : HasDerivAt (fun s => w s 0) (w' 0) t)
    (h1 : HasDerivAt (fun s => w s 1) (w' 1) t)
    (h2 : HasDerivAt (fun s => w s 2) (w' 2) t) :
    HasDerivAt (fun s => (1 / 2 : ℝ) * dot3D (w s) (w s)) (dot3D w' (w t)) t := by
  have hsq0 : HasDerivAt (fun s => w s 0 * w s 0) (w' 0 * w t 0 + w t 0 * w' 0) t := h0.mul h0
  have hsq1 : HasDerivAt (fun s => w s 1 * w s 1) (w' 1 * w t 1 + w t 1 * w' 1) t := h1.mul h1
  have hsq2 : HasDerivAt (fun s => w s 2 * w s 2) (w' 2 * w t 2 + w t 2 * w' 2) t := h2.mul h2
  have hsum : HasDerivAt (fun s => dot3D (w s) (w s))
      ((w' 0 * w t 0 + w t 0 * w' 0) + (w' 1 * w t 1 + w t 1 * w' 1) +
       (w' 2 * w t 2 + w t 2 * w' 2)) t :=
    (hsq0.add hsq1).add hsq2
  have hhalf := hsum.const_mul (1 / 2 : ℝ)
  have heq : (1 / 2 : ℝ) *
      ((w' 0 * w t 0 + w t 0 * w' 0) + (w' 1 * w t 1 + w t 1 * w' 1) +
       (w' 2 * w t 2 + w t 2 * w' 2)) = dot3D w' (w t) := by
    unfold dot3D
    ring
  rw [heq] at hhalf
  exact hhalf

private theorem continuous_fderiv_spacetime_comp
    {u : ℝ → R3 → R3}
    (hu_st : ∀ q : ℝ × R3, ContDiffAt ℝ 2 (fun p : ℝ × R3 => u p.1 p.2) q)
    (c : Fin 3) :
    Continuous (fderiv ℝ (fun p : ℝ × R3 => u p.1 p.2 c)) := by
  have hFc : ContDiff ℝ 2 (fun p : ℝ × R3 => u p.1 p.2 c) :=
    contDiff_iff_contDiffAt.mpr fun q => contDiffAt_pi.mp (hu_st q) c
  have h1 : ContDiff ℝ 1 (fderiv ℝ (fun p : ℝ × R3 => u p.1 p.2 c)) :=
    hFc.fderiv_right (by simp [one_add_one_eq_two])
  exact h1.continuous

private theorem continuous_sndFDeriv_spacetime_comp
    {u : ℝ → R3 → R3}
    (hu_st : ∀ q : ℝ × R3, ContDiffAt ℝ 2 (fun p : ℝ × R3 => u p.1 p.2) q)
    (c : Fin 3) :
    Continuous (fderiv ℝ (fderiv ℝ (fun p : ℝ × R3 => u p.1 p.2 c))) := by
  have hFc : ContDiff ℝ 2 (fun p : ℝ × R3 => u p.1 p.2 c) :=
    contDiff_iff_contDiffAt.mpr fun q => contDiffAt_pi.mp (hu_st q) c
  have h1 : ContDiff ℝ 1 (fderiv ℝ (fun p : ℝ × R3 => u p.1 p.2 c)) :=
    hFc.fderiv_right (by simp [one_add_one_eq_two])
  have h0 : ContDiff ℝ 0 (fderiv ℝ (fderiv ℝ (fun p : ℝ × R3 => u p.1 p.2 c))) :=
    h1.fderiv_right (by simp)
  exact h0.continuous

private theorem continuous_joint_timeDeriv_comp
    {u : ℝ → R3 → R3}
    (hu_st : ∀ q : ℝ × R3, ContDiffAt ℝ 2 (fun p : ℝ × R3 => u p.1 p.2) q)
    (c : Fin 3) :
    Continuous (fun p : ℝ × R3 => deriv (fun s => u s p.2 c) p.1) := by
  have hFc : ∀ q : ℝ × R3, ContDiffAt ℝ 2 (fun p : ℝ × R3 => u p.1 p.2 c) q :=
    fun q => contDiffAt_pi.mp (hu_st q) c
  have hfun : (fun p : ℝ × R3 => deriv (fun s => u s p.2 c) p.1) =
      (fun p : ℝ × R3 => fderiv ℝ (fun q : ℝ × R3 => u q.1 q.2 c) p ((1 : ℝ), (0 : R3))) := by
    funext p
    exact timeDeriv_eq_fderiv_prod (fun q => u q.1 q.2 c) hFc p.1 p.2
  rw [hfun]
  exact (ContinuousLinearMap.apply ℝ ℝ ((1 : ℝ), (0 : R3))).continuous.comp
    (continuous_fderiv_spacetime_comp hu_st c)

private theorem continuous_joint_spacePartial_comp
    {u : ℝ → R3 → R3}
    (hu_st : ∀ q : ℝ × R3, ContDiffAt ℝ 2 (fun p : ℝ × R3 => u p.1 p.2) q)
    (c i : Fin 3) :
    Continuous (fun p : ℝ × R3 => partialDerivScalar (fun y => u p.1 y c) p.2 i) := by
  have hFc : ∀ q : ℝ × R3, ContDiffAt ℝ 2 (fun p : ℝ × R3 => u p.1 p.2 c) q :=
    fun q => contDiffAt_pi.mp (hu_st q) c
  have hfun : (fun p : ℝ × R3 => partialDerivScalar (fun y => u p.1 y c) p.2 i) =
      (fun p : ℝ × R3 => fderiv ℝ (fun q : ℝ × R3 => u q.1 q.2 c) p ((0 : ℝ), basisVec i)) := by
    funext p
    exact spacePartial_eq_fderiv_prod (fun q => u q.1 q.2 c) hFc p.1 p.2 i
  rw [hfun]
  exact (ContinuousLinearMap.apply ℝ ℝ ((0 : ℝ), basisVec i)).continuous.comp
    (continuous_fderiv_spacetime_comp hu_st c)

private theorem continuous_joint_timeDeriv_spacePartial_comp
    {u : ℝ → R3 → R3}
    (hu_st : ∀ q : ℝ × R3, ContDiffAt ℝ 2 (fun p : ℝ × R3 => u p.1 p.2) q)
    (c i : Fin 3) :
    Continuous (fun p : ℝ × R3 =>
      fderiv ℝ (fderiv ℝ (fun q : ℝ × R3 => u q.1 q.2 c)) p ((1 : ℝ), (0 : R3)) ((0 : ℝ), basisVec i)) := by
  have h1 : Continuous (fun p : ℝ × R3 =>
      fderiv ℝ (fderiv ℝ (fun q : ℝ × R3 => u q.1 q.2 c)) p ((1 : ℝ), (0 : R3))) :=
    (ContinuousLinearMap.apply ℝ ((ℝ × R3) →L[ℝ] ℝ) ((1 : ℝ), (0 : R3))).continuous.comp
      (continuous_sndFDeriv_spacetime_comp hu_st c)
  exact (ContinuousLinearMap.apply ℝ ℝ ((0 : ℝ), basisVec i)).continuous.comp h1

private theorem hasDerivAt_u_comp
    {u : ℝ → R3 → R3}
    (hu_st : ∀ q : ℝ × R3, ContDiffAt ℝ 2 (fun p : ℝ × R3 => u p.1 p.2) q)
    (t : ℝ) (x : R3) (c : Fin 3) :
    HasDerivAt (fun s => u s x c) (deriv (fun s => u s x c) t) t := by
  have hFc : ∀ q : ℝ × R3, ContDiffAt ℝ 2 (fun p : ℝ × R3 => u p.1 p.2 c) q :=
    fun q => contDiffAt_pi.mp (hu_st q) c
  have h1 : ContDiffAt ℝ 1 (fun p : ℝ × R3 => u p.1 p.2 c) (t, x) :=
    (hFc (t, x)).of_le (by rw [← one_add_one_eq_two]; exact le_self_add)
  have hdiff : DifferentiableAt ℝ (fun p : ℝ × R3 => u p.1 p.2 c) (t, x) :=
    h1.differentiableAt (by simp)
  have hembed : HasDerivAt (fun s : ℝ => (s, x)) ((1 : ℝ), (0 : R3)) t :=
    (hasDerivAt_id t).prodMk (hasDerivAt_const t x)
  have hd := hdiff.hasFDerivAt.comp_hasDerivAt t hembed
  rw [← timeDeriv_eq_fderiv_prod (fun p => u p.1 p.2 c) hFc t x] at hd
  exact hd

private theorem hasDerivAt_curl3D_comp
    {u : ℝ → R3 → R3}
    (hu_st : ∀ q : ℝ × R3, ContDiffAt ℝ 2 (fun p : ℝ × R3 => u p.1 p.2) q)
    (t : ℝ) (x : R3) (comp : Fin 3) :
    HasDerivAt (fun s => curl3D (u s) x comp) (deriv (fun s => curl3D (u s) x comp) t) t := by
  have hF0 : ∀ q : ℝ × R3, ContDiffAt ℝ 2 (fun p : ℝ × R3 => u p.1 p.2 0) q :=
    fun q => contDiffAt_pi.mp (hu_st q) 0
  have hF1 : ∀ q : ℝ × R3, ContDiffAt ℝ 2 (fun p : ℝ × R3 => u p.1 p.2 1) q :=
    fun q => contDiffAt_pi.mp (hu_st q) 1
  have hF2 : ∀ q : ℝ × R3, ContDiffAt ℝ 2 (fun p : ℝ × R3 => u p.1 p.2 2) q :=
    fun q => contDiffAt_pi.mp (hu_st q) 2
  match comp with
  | ⟨0, _⟩ =>
    have h2 : HasDerivAt (fun s => partialDerivScalar (fun y => u s y 2) x 1) _ t :=
      hasDerivAt_spacePartial_time (fun p => u p.1 p.2 2) hF2 t x 1
    have h1 : HasDerivAt (fun s => partialDerivScalar (fun y => u s y 1) x 2) _ t :=
      hasDerivAt_spacePartial_time (fun p => u p.1 p.2 1) hF1 t x 2
    have hsub : HasDerivAt (fun s => partialDerivScalar (fun y => u s y 2) x 1 -
        partialDerivScalar (fun y => u s y 1) x 2) _ t := h2.sub h1
    change HasDerivAt
      (fun s => partialDerivScalar (fun y => u s y 2) x 1 -
                partialDerivScalar (fun y => u s y 1) x 2)
      (deriv (fun s => partialDerivScalar (fun y => u s y 2) x 1 -
                       partialDerivScalar (fun y => u s y 1) x 2) t) t
    rw [hsub.deriv]
    exact hsub
  | ⟨1, _⟩ =>
    have h0 : HasDerivAt (fun s => partialDerivScalar (fun y => u s y 0) x 2) _ t :=
      hasDerivAt_spacePartial_time (fun p => u p.1 p.2 0) hF0 t x 2
    have h2 : HasDerivAt (fun s => partialDerivScalar (fun y => u s y 2) x 0) _ t :=
      hasDerivAt_spacePartial_time (fun p => u p.1 p.2 2) hF2 t x 0
    have hsub : HasDerivAt (fun s => partialDerivScalar (fun y => u s y 0) x 2 -
        partialDerivScalar (fun y => u s y 2) x 0) _ t := h0.sub h2
    change HasDerivAt
      (fun s => partialDerivScalar (fun y => u s y 0) x 2 -
                partialDerivScalar (fun y => u s y 2) x 0)
      (deriv (fun s => partialDerivScalar (fun y => u s y 0) x 2 -
                       partialDerivScalar (fun y => u s y 2) x 0) t) t
    rw [hsub.deriv]
    exact hsub
  | ⟨2, _⟩ =>
    have h1 : HasDerivAt (fun s => partialDerivScalar (fun y => u s y 1) x 0) _ t :=
      hasDerivAt_spacePartial_time (fun p => u p.1 p.2 1) hF1 t x 0
    have h0 : HasDerivAt (fun s => partialDerivScalar (fun y => u s y 0) x 1) _ t :=
      hasDerivAt_spacePartial_time (fun p => u p.1 p.2 0) hF0 t x 1
    have hsub : HasDerivAt (fun s => partialDerivScalar (fun y => u s y 1) x 0 -
        partialDerivScalar (fun y => u s y 0) x 1) _ t := h1.sub h0
    change HasDerivAt
      (fun s => partialDerivScalar (fun y => u s y 1) x 0 -
                partialDerivScalar (fun y => u s y 0) x 1)
      (deriv (fun s => partialDerivScalar (fun y => u s y 1) x 0 -
                       partialDerivScalar (fun y => u s y 0) x 1) t) t
    rw [hsub.deriv]
    exact hsub

private theorem continuous_joint_timeDeriv_curl3D_comp
    {u : ℝ → R3 → R3}
    (hu_st : ∀ q : ℝ × R3, ContDiffAt ℝ 2 (fun p : ℝ × R3 => u p.1 p.2) q)
    (comp : Fin 3) :
    Continuous (fun p : ℝ × R3 => deriv (fun s => curl3D (u s) p.2 comp) p.1) := by
  have hF0 : ∀ q : ℝ × R3, ContDiffAt ℝ 2 (fun p : ℝ × R3 => u p.1 p.2 0) q :=
    fun q => contDiffAt_pi.mp (hu_st q) 0
  have hF1 : ∀ q : ℝ × R3, ContDiffAt ℝ 2 (fun p : ℝ × R3 => u p.1 p.2 1) q :=
    fun q => contDiffAt_pi.mp (hu_st q) 1
  have hF2 : ∀ q : ℝ × R3, ContDiffAt ℝ 2 (fun p : ℝ × R3 => u p.1 p.2 2) q :=
    fun q => contDiffAt_pi.mp (hu_st q) 2
  match comp with
  | ⟨0, _⟩ =>
    have hfun : (fun p : ℝ × R3 => deriv (fun s => curl3D (u s) p.2 0) p.1) =
        (fun p : ℝ × R3 =>
          fderiv ℝ (fderiv ℝ (fun q : ℝ × R3 => u q.1 q.2 2)) p ((1 : ℝ), (0 : R3)) ((0 : ℝ), basisVec 1) -
          fderiv ℝ (fderiv ℝ (fun q : ℝ × R3 => u q.1 q.2 1)) p ((1 : ℝ), (0 : R3)) ((0 : ℝ), basisVec 2)) := by
      funext p
      have h2 := hasDerivAt_spacePartial_time (fun q => u q.1 q.2 2) hF2 p.1 p.2 1
      have h1 := hasDerivAt_spacePartial_time (fun q => u q.1 q.2 1) hF1 p.1 p.2 2
      exact deriv_sub_of_hasDerivAt h2 h1
    change Continuous (fun p : ℝ × R3 => deriv (fun s => curl3D (u s) p.2 0) p.1)
    rw [hfun]
    exact (continuous_joint_timeDeriv_spacePartial_comp hu_st 2 1).sub
          (continuous_joint_timeDeriv_spacePartial_comp hu_st 1 2)
  | ⟨1, _⟩ =>
    have hfun : (fun p : ℝ × R3 => deriv (fun s => curl3D (u s) p.2 1) p.1) =
        (fun p : ℝ × R3 =>
          fderiv ℝ (fderiv ℝ (fun q : ℝ × R3 => u q.1 q.2 0)) p ((1 : ℝ), (0 : R3)) ((0 : ℝ), basisVec 2) -
          fderiv ℝ (fderiv ℝ (fun q : ℝ × R3 => u q.1 q.2 2)) p ((1 : ℝ), (0 : R3)) ((0 : ℝ), basisVec 0)) := by
      funext p
      have h0 := hasDerivAt_spacePartial_time (fun q => u q.1 q.2 0) hF0 p.1 p.2 2
      have h2 := hasDerivAt_spacePartial_time (fun q => u q.1 q.2 2) hF2 p.1 p.2 0
      exact deriv_sub_of_hasDerivAt h0 h2
    change Continuous (fun p : ℝ × R3 => deriv (fun s => curl3D (u s) p.2 1) p.1)
    rw [hfun]
    exact (continuous_joint_timeDeriv_spacePartial_comp hu_st 0 2).sub
          (continuous_joint_timeDeriv_spacePartial_comp hu_st 2 0)
  | ⟨2, _⟩ =>
    have hfun : (fun p : ℝ × R3 => deriv (fun s => curl3D (u s) p.2 2) p.1) =
        (fun p : ℝ × R3 =>
          fderiv ℝ (fderiv ℝ (fun q : ℝ × R3 => u q.1 q.2 1)) p ((1 : ℝ), (0 : R3)) ((0 : ℝ), basisVec 0) -
          fderiv ℝ (fderiv ℝ (fun q : ℝ × R3 => u q.1 q.2 0)) p ((1 : ℝ), (0 : R3)) ((0 : ℝ), basisVec 1)) := by
      funext p
      have h1 := hasDerivAt_spacePartial_time (fun q => u q.1 q.2 1) hF1 p.1 p.2 0
      have h0 := hasDerivAt_spacePartial_time (fun q => u q.1 q.2 0) hF0 p.1 p.2 1
      exact deriv_sub_of_hasDerivAt h1 h0
    change Continuous (fun p : ℝ × R3 => deriv (fun s => curl3D (u s) p.2 2) p.1)
    rw [hfun]
    exact (continuous_joint_timeDeriv_spacePartial_comp hu_st 1 0).sub
          (continuous_joint_timeDeriv_spacePartial_comp hu_st 0 1)

-- ============================================================================
-- SECTION 4: MAIN THEOREMS OF MILESTONE 3B (0 sorryAx)
-- ============================================================================

/-- **MAIN THEOREM 1 OF MILESTONE 3B (Differential Leray Energy Law on `𝕋³`):**
    For any periodic classical 3D Navier-Stokes solution `(u, p)` and any `t ≥ 0`:
      `d/dt E(t) = -ν ∫_{𝕋³} |∇u(t, x)|² dx` (`0 sorryAx`). -/
theorem hasDerivAt_kineticEnergy_leray
    {u : ℝ → R3 → R3} {p : ℝ → R3 → ℝ} {ν : ℝ}
    (hns : IsPeriodicClassicalNS3D_C3 u p ν) {t : ℝ} (ht : t ≥ 0) :
    HasDerivAt (kineticEnergy u) (-ν * torusIntegral (gradNormSq3D (u t))) t ∧
    deriv (kineticEnergy u) t = -ν * torusIntegral (gradNormSq3D (u t)) := by
  have hu_cont : Continuous (fun q : ℝ × R3 => u q.1 q.2) :=
    (contDiff_iff_contDiffAt.mpr hns.h_u_c2_spacetime).continuous
  have hu0 : Continuous (fun q : ℝ × R3 => u q.1 q.2 0) := (continuous_apply 0).comp hu_cont
  have hu1 : Continuous (fun q : ℝ × R3 => u q.1 q.2 1) := (continuous_apply 1).comp hu_cont
  have hu2 : Continuous (fun q : ℝ × R3 => u q.1 q.2 2) := (continuous_apply 2).comp hu_cont
  have hF_cont : Continuous (fun q : ℝ × R3 => (1 / 2 : ℝ) * dot3D (u q.1 q.2) (u q.1 q.2)) := by
    unfold dot3D
    exact continuous_const.mul (((hu0.mul hu0).add (hu1.mul hu1)).add (hu2.mul hu2))
  have hut0 := continuous_joint_timeDeriv_comp hns.h_u_c2_spacetime 0
  have hut1 := continuous_joint_timeDeriv_comp hns.h_u_c2_spacetime 1
  have hut2 := continuous_joint_timeDeriv_comp hns.h_u_c2_spacetime 2
  have hF'_cont : Continuous (fun q : ℝ × R3 =>
      dot3D (fun c => deriv (fun s => u s q.2 c) q.1) (u q.1 q.2)) := by
    unfold dot3D
    exact ((hut0.mul hu0).add (hut1.mul hu1)).add (hut2.mul hu2)
  have h_leibniz := hasDerivAt_torusIntegral_of_continuous
    (F := fun s x => (1 / 2 : ℝ) * dot3D (u s x) (u s x))
    (F' := fun s x => dot3D (fun c => deriv (fun r => u r x c) s) (u s x))
    hF_cont hF'_cont
    (fun s x => hasDerivAt_half_dot3D_self
      (w := fun r => u r x)
      (w' := fun c => deriv (fun r => u r x c) s)
      (hasDerivAt_u_comp hns.h_u_c2_spacetime s x 0)
      (hasDerivAt_u_comp hns.h_u_c2_spacetime s x 1)
      (hasDerivAt_u_comp hns.h_u_c2_spacetime s x 2)) t
  have hE_eq : kineticEnergy u =
      (fun s => torusIntegral (fun x => (1 / 2 : ℝ) * dot3D (u s x) (u s x))) := by
    funext s
    unfold kineticEnergy
    have hc : Continuous (fun x => dot3D (u s x) (u s x)) := by
      have hs_cont : Continuous (u s) := hu_cont.comp (continuous_const.prodMk continuous_id)
      exact continuous_dot3D hs_cont hs_cont
    exact (torusIntegral_const_mul (1 / 2 : ℝ) hc).symm
  rw [← hE_eq, (leray_energy_identity_torus3D hns ht).1] at h_leibniz
  exact ⟨h_leibniz, h_leibniz.deriv⟩

private lemma two_add_one_eq_three'' {α : Type*} [AddMonoidWithOne α] :
    (2 : α) + 1 = 3 := by
  rw [← Nat.cast_ofNat (n := 2), ← Nat.cast_one, ← Nat.cast_add]
  exact Nat.cast_ofNat

private lemma contDiff_one_of_three {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {f : E → F} (hf : ContDiff ℝ 3 f) :
    ContDiff ℝ 1 f := by
  have hf2 : ContDiff ℝ 2 f := hf.of_le (by rw [← two_add_one_eq_three'']; exact le_self_add)
  exact hf2.of_le (by rw [← one_add_one_eq_two]; exact le_self_add)

/-- **MAIN THEOREM 2 OF MILESTONE 3B (Global Leray Energy Balance & Uniform Bound `E(T) ≤ E(0)`):**
    Time-integrating the differential Leray energy law over `[0, T]` proves for every `T ≥ 0`:
    1. Exact energy balance: `E(T) + ν ∫_0^T ∫_{𝕋³} |∇u(s, x)|² dx ds = E(0)`.
    2. Global uniform energy bound (Clay requirement): `0 ≤ E(T) ≤ E(0)`.
    3. Global cumulative dissipation bound: `ν ∫_0^T ∫_{𝕋³} |∇u(s, x)|² dx ds ≤ E(0)`. -/
theorem global_leray_energy_balance_and_bound
    {u : ℝ → R3 → R3} {p : ℝ → R3 → ℝ} {ν : ℝ}
    (hns : IsPeriodicClassicalNS3D_C3 u p ν) {T : ℝ} (hT : 0 ≤ T) :
    kineticEnergy u T + ν * (∫ s in (0 : ℝ)..T, torusIntegral (gradNormSq3D (u s))) =
      kineticEnergy u 0 ∧
    0 ≤ kineticEnergy u T ∧
    kineticEnergy u T ≤ kineticEnergy u 0 ∧
    ν * (∫ s in (0 : ℝ)..T, torusIntegral (gradNormSq3D (u s))) ≤ kineticEnergy u 0 := by
  have h_joint_grad : Continuous (fun q : ℝ × R3 => gradNormSq3D (u q.1) q.2) := by
    unfold gradNormSq3D
    have p00 := (continuous_joint_spacePartial_comp hns.h_u_c2_spacetime 0 0).pow 2
    have p01 := (continuous_joint_spacePartial_comp hns.h_u_c2_spacetime 0 1).pow 2
    have p02 := (continuous_joint_spacePartial_comp hns.h_u_c2_spacetime 0 2).pow 2
    have p10 := (continuous_joint_spacePartial_comp hns.h_u_c2_spacetime 1 0).pow 2
    have p11 := (continuous_joint_spacePartial_comp hns.h_u_c2_spacetime 1 1).pow 2
    have p12 := (continuous_joint_spacePartial_comp hns.h_u_c2_spacetime 1 2).pow 2
    have p20 := (continuous_joint_spacePartial_comp hns.h_u_c2_spacetime 2 0).pow 2
    have p21 := (continuous_joint_spacePartial_comp hns.h_u_c2_spacetime 2 1).pow 2
    have p22 := (continuous_joint_spacePartial_comp hns.h_u_c2_spacetime 2 2).pow 2
    exact (((((((p00.add p01).add p02).add p10).add p11).add p12).add p20).add p21).add p22
  have h_cont_diss : Continuous (fun s => torusIntegral (gradNormSq3D (u s))) :=
    continuous_torusIntegral_of_joint_continuous h_joint_grad
  have h_ftc := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (a := (0 : ℝ)) (b := T)
    (f := kineticEnergy u)
    (f' := fun s => -ν * torusIntegral (gradNormSq3D (u s)))
    (fun s hs => by
      have hs_ge : s ≥ 0 := by
        rw [Set.uIcc_of_le hT] at hs
        exact hs.1
      exact (hasDerivAt_kineticEnergy_leray hns hs_ge).1)
    ((continuous_const.mul h_cont_diss).intervalIntegrable 0 T)
  have h_pull : (∫ s in (0 : ℝ)..T, -ν * torusIntegral (gradNormSq3D (u s))) =
      -ν * (∫ s in (0 : ℝ)..T, torusIntegral (gradNormSq3D (u s))) :=
    intervalIntegral.integral_const_mul (-ν) (fun s => torusIntegral (gradNormSq3D (u s)))
  have h_balance : kineticEnergy u T + ν * (∫ s in (0 : ℝ)..T, torusIntegral (gradNormSq3D (u s))) =
      kineticEnergy u 0 := by
    linarith [h_ftc, h_pull]
  have h_diss_nonneg : 0 ≤ ∫ s in (0 : ℝ)..T, torusIntegral (gradNormSq3D (u s)) :=
    intervalIntegral.integral_nonneg hT fun s hs =>
      torusIntegral_nonneg
        (continuous_gradNormSq3D (contDiff_one_of_three (hns.h_u_c3_global s hs.1)))
        (gradNormSq3D_nonneg (u s))
  have h_nu_diss_nonneg : 0 ≤ ν * (∫ s in (0 : ℝ)..T, torusIntegral (gradNormSq3D (u s))) :=
    mul_nonneg (le_of_lt hns.h_nu_pos) h_diss_nonneg
  have hE_T_nonneg : 0 ≤ kineticEnergy u T := by
    unfold kineticEnergy
    have huT_cont : Continuous (u T) := (hns.h_u_c3_global T hT).continuous
    have h_int_nn : 0 ≤ torusIntegral (fun x => dot3D (u T x) (u T x)) :=
      torusIntegral_nonneg (continuous_dot3D huT_cont huT_cont) (fun x => dot3D_self_nonneg (u T x))
    linarith
  exact ⟨h_balance, hE_T_nonneg, by linarith, by linarith⟩

/-- **MAIN THEOREM 3 OF MILESTONE 3B (Exact Time-Differentiated 3D Enstrophy Law on `𝕋³`):**
    For any periodic classical 3D Navier-Stokes solution `(u, p)` and any `t ≥ 0`:
      `d/dt Z(t) = S_stretch(t) - ν P(t)`
    where `Z`, `S_stretch`, and `P` are all true 3D Lebesgue integrals (`0 sorryAx`). -/
theorem hasDerivAt_enstrophy_evolution_3D
    {u : ℝ → R3 → R3} {p : ℝ → R3 → ℝ} {ν : ℝ}
    (hns : IsPeriodicClassicalNS3D_C3 u p ν) {t : ℝ} (ht : t ≥ 0) :
    HasDerivAt (enstrophy u) (vortexStretching3D (u t) - ν * palinstrophy3D (u t)) t ∧
    deriv (enstrophy u) t = vortexStretching3D (u t) - ν * palinstrophy3D (u t) := by
  have hw0 : Continuous (fun q : ℝ × R3 => curl3D (u q.1) q.2 0) :=
    (continuous_joint_spacePartial_comp hns.h_u_c2_spacetime 2 1).sub
    (continuous_joint_spacePartial_comp hns.h_u_c2_spacetime 1 2)
  have hw1 : Continuous (fun q : ℝ × R3 => curl3D (u q.1) q.2 1) :=
    (continuous_joint_spacePartial_comp hns.h_u_c2_spacetime 0 2).sub
    (continuous_joint_spacePartial_comp hns.h_u_c2_spacetime 2 0)
  have hw2 : Continuous (fun q : ℝ × R3 => curl3D (u q.1) q.2 2) :=
    (continuous_joint_spacePartial_comp hns.h_u_c2_spacetime 1 0).sub
    (continuous_joint_spacePartial_comp hns.h_u_c2_spacetime 0 1)
  have hF_cont : Continuous (fun q : ℝ × R3 =>
      (1 / 2 : ℝ) * dot3D (curl3D (u q.1) q.2) (curl3D (u q.1) q.2)) := by
    unfold dot3D
    exact continuous_const.mul (((hw0.mul hw0).add (hw1.mul hw1)).add (hw2.mul hw2))
  have hwt0 := continuous_joint_timeDeriv_curl3D_comp hns.h_u_c2_spacetime 0
  have hwt1 := continuous_joint_timeDeriv_curl3D_comp hns.h_u_c2_spacetime 1
  have hwt2 := continuous_joint_timeDeriv_curl3D_comp hns.h_u_c2_spacetime 2
  have hF'_cont : Continuous (fun q : ℝ × R3 =>
      dot3D (fun c => deriv (fun s => curl3D (u s) q.2 c) q.1) (curl3D (u q.1) q.2)) := by
    unfold dot3D
    exact ((hwt0.mul hw0).add (hwt1.mul hw1)).add (hwt2.mul hw2)
  have h_leibniz := hasDerivAt_torusIntegral_of_continuous
    (F := fun s x => (1 / 2 : ℝ) * dot3D (curl3D (u s) x) (curl3D (u s) x))
    (F' := fun s x => dot3D (fun c => deriv (fun r => curl3D (u r) x c) s) (curl3D (u s) x))
    hF_cont hF'_cont
    (fun s x => hasDerivAt_half_dot3D_self
      (w := fun r => curl3D (u r) x)
      (w' := fun c => deriv (fun r => curl3D (u r) x c) s)
      (hasDerivAt_curl3D_comp hns.h_u_c2_spacetime s x 0)
      (hasDerivAt_curl3D_comp hns.h_u_c2_spacetime s x 1)
      (hasDerivAt_curl3D_comp hns.h_u_c2_spacetime s x 2)) t
  have hZ_eq : enstrophy u =
      (fun s => torusIntegral (fun x => (1 / 2 : ℝ) * dot3D (curl3D (u s) x) (curl3D (u s) x))) := by
    funext s
    unfold enstrophy
    have hc : Continuous (fun x => dot3D (curl3D (u s) x) (curl3D (u s) x)) := by
      have hc0 : Continuous (fun x => curl3D (u s) x 0) := hw0.comp (continuous_const.prodMk continuous_id)
      have hc1 : Continuous (fun x => curl3D (u s) x 1) := hw1.comp (continuous_const.prodMk continuous_id)
      have hc2 : Continuous (fun x => curl3D (u s) x 2) := hw2.comp (continuous_const.prodMk continuous_id)
      unfold dot3D
      exact ((hc0.mul hc0).add (hc1.mul hc1)).add (hc2.mul hc2)
    exact (torusIntegral_const_mul (1 / 2 : ℝ) hc).symm
  rw [← hZ_eq, enstrophy_evolution_identity_torus3D hns ht] at h_leibniz
  exact ⟨h_leibniz, h_leibniz.deriv⟩

/-- **MAIN THEOREM 4 OF MILESTONE 3B (Conditional Enstrophy Monotonicity on `[0, T]`):**
    Whenever viscous palinstrophy dissipation dominates 3D vortex stretching along `[0, T]`
    (`S_stretch(s) ≤ ν P(s)`), the true enstrophy is non-increasing: `Z(T) ≤ Z(0)` (`0 sorryAx`). -/
theorem enstrophy_nonincreasing_of_stretching_le_dissipation
    {u : ℝ → R3 → R3} {p : ℝ → R3 → ℝ} {ν : ℝ}
    (hns : IsPeriodicClassicalNS3D_C3 u p ν) {T : ℝ} (hT : 0 ≤ T)
    (h_dom : ∀ s ∈ Set.Icc (0 : ℝ) T, vortexStretching3D (u s) ≤ ν * palinstrophy3D (u s)) :
    enstrophy u T ≤ enstrophy u 0 := by
  rcases eq_or_lt_of_le hT with rfl | hT_pos
  · exact le_rfl
  · by_contra hle
    have hlt : enstrophy u 0 < enstrophy u T := lt_of_not_ge hle
    let ε : ℝ := (enstrophy u T - enstrophy u 0) / (2 * T)
    have hε_pos : 0 < ε := div_pos (by linarith) (by linarith)
    have hεT : ε * T = (enstrophy u T - enstrophy u 0) / 2 := by
      have hTne : T ≠ 0 := ne_of_gt hT_pos
      dsimp only [ε]
      field_simp
    let g : ℝ → ℝ := fun r => enstrophy u r - ε * r
    have hg_deriv : ∀ s : ℝ, 0 ≤ s →
        HasDerivAt g ((vortexStretching3D (u s) - ν * palinstrophy3D (u s)) - ε) s := by
      intro s hs
      have h1 := (hasDerivAt_enstrophy_evolution_3D hns hs).1
      have hid : HasDerivAt (fun r : ℝ => r) 1 s := hasDerivAt_id s
      have h2 : HasDerivAt (fun r : ℝ => ε * r) ε s := by
        have hcm := hid.const_mul ε
        rwa [mul_one] at hcm
      exact h1.sub h2
    have hg_cont : ContinuousOn g (Set.Icc 0 T) :=
      fun s hs => (hg_deriv s hs.1).continuousAt.continuousWithinAt
    obtain ⟨c, hc_mem, hc_max⟩ := isCompact_Icc.exists_isMaxOn ⟨0, ⟨le_rfl, hT⟩⟩ hg_cont
    have hg0_lt_gT : g 0 < g T := by
      dsimp only [g]
      linarith
    have hc_ne_zero : c ≠ 0 := by
      intro hcz
      have hT_le : g T ≤ g 0 := hcz ▸ hc_max ⟨hT, le_rfl⟩
      linarith
    have hc_pos : 0 < c := lt_of_le_of_ne hc_mem.1 (Ne.symm hc_ne_zero)
    let d : ℝ := (vortexStretching3D (u c) - ν * palinstrophy3D (u c)) - ε
    have hd_neg : d < 0 := by
      dsimp only [d]
      linarith [h_dom c hc_mem]
    have hlo := (hg_deriv c hc_mem.1).hasFDerivAt.isLittleO.bound (show (0 : ℝ) < (-d) / 2 by linarith)
    obtain ⟨δ, hδ_pos, hδ⟩ := Metric.eventually_nhds_iff.mp hlo
    let hstep : ℝ := min (c / 2) (δ / 2)
    have hh_pos : 0 < hstep := lt_min (by linarith) (by linarith)
    let x : ℝ := c - hstep
    have hx_sub : x - c = -hstep := by dsimp only [x]; ring
    have hx_dist : dist x c < δ := by
      rw [Real.dist_eq, hx_sub, abs_neg, abs_of_pos hh_pos]
      exact lt_of_le_of_lt (min_le_right _ _) (by linarith)
    have hx_mem : x ∈ Set.Icc (0 : ℝ) T := by
      refine ⟨?_, ?_⟩
      · have : hstep ≤ c / 2 := min_le_left _ _
        dsimp only [x]; linarith
      · dsimp only [x]; linarith [hc_mem.2]
    have hbound := hδ hx_dist
    simp only [Real.norm_eq_abs] at hbound
    rw [hx_sub, abs_neg, abs_of_pos hh_pos] at hbound
    have hlow : -(-d / 2 * hstep) ≤ g x - g c - (-hstep) * d := by
      simpa [d] using (abs_le.mp hbound).1
    have hgx_le : g x ≤ g c := hc_max hx_mem
    nlinarith

-- ============================================================================
-- SECTION 5: AXIOM AUDIT TRAIL (0 sorryAx)
-- ============================================================================

#print axioms hasDerivAt_torusIntegral_of_continuous
#print axioms continuous_torusIntegral_of_joint_continuous
#print axioms hasDerivAt_kineticEnergy_leray
#print axioms global_leray_energy_balance_and_bound
#print axioms hasDerivAt_enstrophy_evolution_3D
#print axioms enstrophy_nonincreasing_of_stretching_le_dissipation

end GarryLerayEnergyLaw3D