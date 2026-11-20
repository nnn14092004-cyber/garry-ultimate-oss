import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import PoincareSobolevTorus3D

/-!
# GARRYULT v4.0.0 — Milestone 4B: Fourier Spectral Analysis, Sharp Wirtinger–Poincaré (`4π²`),
# Bernstein High-Frequency Shell Coercivity (`4π² N²`), Sharp Analytical Lemma 4 (`8π² Z ≤ P`),
# Sharp Exponential Energy Decay (`E(T) ≤ E(0) exp(-8π² ν T)`) & 3D Spectral PDE Operators on `𝕋³`
-/

namespace GarryFourierSpectral3D

open MeasureTheory Filter Topology GarryReal3DCalculus GarryVorticity3D
  GarryLerayTorus3D GarryLerayEnergyLaw3D GarryPoincareSobolev3D

private lemma two_add_one_eq_three4 {α : Type*} [AddMonoidWithOne α] :
    (2 : α) + 1 = 3 := by
  rw [← Nat.cast_ofNat (n := 2), ← Nat.cast_one, ← Nat.cast_add]
  exact Nat.cast_ofNat

private lemma contDiff_two_of_three4 {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {f : E → F} (hf : ContDiff ℝ 3 f) :
    ContDiff ℝ 2 f :=
  hf.of_le (by rw [← two_add_one_eq_three4]; exact le_self_add)

private lemma contDiff_one_of_two4 {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {f : E → F} (hf : ContDiff ℝ 2 f) :
    ContDiff ℝ 1 f :=
  hf.of_le (by rw [← one_add_one_eq_two]; exact le_self_add)

-- ============================================================================
-- SECTION 1: 1D FOURIER PARSEVAL, DERIVATIVE LAW, BERNSTEIN SHELL & WIRTINGER
-- ============================================================================

private lemma unit_lt : (0 : ℝ) < 1 := by norm_num

private theorem memLp_two_Ioc_unit {f : ℝ → ℂ} (hf : Continuous f) :
    MemLp f 2 (volume.restrict (Set.Ioc (0 : ℝ) 1)) := by
  have : IsFiniteMeasure (volume.restrict (Set.Ioc (0 : ℝ) 1)) :=
    ⟨by rw [Measure.restrict_apply_univ, Real.volume_Ioc]; exact ENNReal.ofReal_lt_top⟩
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 1)).exists_bound_of_continuousOn hf.continuousOn
  refine MemLp.of_bound hf.aestronglyMeasurable C ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
  exact hC x (Set.Ioc_subset_Icc_self hx)

/-- Parseval identity for continuous real functions on `[0, 1]`:
    `∑' n : ℤ, ‖fourierCoeffOn (0 < 1) (g : ℝ → ℂ) n‖² = ∫₀¹ g(s)² ds`. -/
theorem hasSum_sq_fourierCoeffOn_real {g : ℝ → ℝ} (hg : Continuous g) :
    HasSum (fun n : ℤ => ‖fourierCoeffOn unit_lt (fun s => (g s : ℂ)) n‖ ^ 2)
      (∫ s in (0 : ℝ)..1, (g s) ^ 2) := by
  have hgC : Continuous (fun s : ℝ => (g s : ℂ)) := Complex.continuous_ofReal.comp hg
  have hparse := hasSum_sq_fourierCoeffOn unit_lt (memLp_two_Ioc_unit hgC)
  convert hparse using 1
  have hpt : (fun s : ℝ => ‖(g s : ℂ)‖ ^ 2) = (fun s : ℝ => (g s) ^ 2) := by
    funext s
    rw [Complex.norm_real, Real.norm_eq_abs, sq_abs]
  rw [hpt]
  simp

/-- Zero-th Fourier mode equals the unit-interval mean. -/
theorem fourierCoeffOn_zero_eq_mean (g : ℝ → ℝ) :
    fourierCoeffOn unit_lt (fun s => (g s : ℂ)) 0 = ((∫ s in (0 : ℝ)..1, g s : ℝ) : ℂ) := by
  rw [fourierCoeffOn_eq_integral]
  simp only [neg_zero, fourier_zero, one_smul, sub_zero, div_one, one_smul]
  exact intervalIntegral.integral_ofReal

/-- **1D Periodic Fourier Derivative Norm Identity:**
    For any `C¹` 1-periodic `g : ℝ → ℝ` and any nonzero mode `n ≠ 0`:
      `4π² n² ‖ĝ(n)‖² = ‖ĝ'(n)‖²`. -/
theorem norm_sq_fourierCoeffOn_deriv
    {g g' : ℝ → ℝ}
    (hg'_cont : Continuous g')
    (hg_deriv : ∀ s : ℝ, HasDerivAt g (g' s) s)
    (hg_per : ∀ s : ℝ, g (s + 1) = g s)
    {n : ℤ} (hn : n ≠ 0) :
    4 * Real.pi ^ 2 * (n : ℝ) ^ 2 * ‖fourierCoeffOn unit_lt (fun s => (g s : ℂ)) n‖ ^ 2 =
      ‖fourierCoeffOn unit_lt (fun s => (g' s : ℂ)) n‖ ^ 2 := by
  have hgC_deriv : ∀ s ∈ Set.uIcc (0 : ℝ) 1,
      HasDerivAt (fun t : ℝ => (g t : ℂ)) (g' s : ℂ) s :=
    fun s _ => (hg_deriv s).ofReal_comp
  have hg'C_int : IntervalIntegrable (fun s : ℝ => (g' s : ℂ)) volume 0 1 :=
    (Complex.continuous_ofReal.comp hg'_cont).intervalIntegrable 0 1
  have hfd := fourierCoeffOn_of_hasDerivAt unit_lt hn hgC_deriv hg'C_int
  have hbdry : (g 1 : ℂ) - (g 0 : ℂ) = 0 := by
    have h10 : g 1 = g 0 := by simpa using hg_per 0
    rw [h10, sub_self]
  have h10C : ((1 : ℝ) : ℂ) - ((0 : ℝ) : ℂ) = 1 := by norm_num
  rw [hbdry, h10C, mul_zero, zero_sub, one_mul] at hfd
  have hnorm_eq : ‖fourierCoeffOn unit_lt (fun s => (g s : ℂ)) n‖ =
      ‖fourierCoeffOn unit_lt (fun s => (g' s : ℂ)) n‖ / (2 * Real.pi * |(n : ℝ)|) := by
    rw [hfd, norm_mul, norm_div, norm_one, norm_neg]
    have hden : ‖(-2 : ℂ) * (Real.pi : ℂ) * Complex.I * (n : ℂ)‖ = 2 * Real.pi * |(n : ℝ)| := by
      rw [norm_mul, norm_mul, norm_mul, Complex.norm_I, mul_one]
      have h1 : ‖(-2 : ℂ)‖ = 2 := by norm_num
      have h2 : ‖(Real.pi : ℂ)‖ = Real.pi := by
        rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
      have h3 : ‖(n : ℂ)‖ = |(n : ℝ)| := by
        rw [← Complex.ofReal_intCast, Complex.norm_real, Real.norm_eq_abs]
      rw [h1, h2, h3]
    rw [hden]
    ring
  have hden_pos : 0 < 2 * Real.pi * |(n : ℝ)| := by
    have hn_pos : (0 : ℝ) < |(n : ℝ)| := abs_pos.mpr (Int.cast_ne_zero.mpr hn)
    have hpi : 0 < Real.pi := Real.pi_pos
    positivity
  have hmul : 2 * Real.pi * |(n : ℝ)| * ‖fourierCoeffOn unit_lt (fun s => (g s : ℂ)) n‖ =
      ‖fourierCoeffOn unit_lt (fun s => (g' s : ℂ)) n‖ := by
    rw [hnorm_eq, mul_div_cancel₀ _ (ne_of_gt hden_pos)]
  calc 4 * Real.pi ^ 2 * (n : ℝ) ^ 2 * ‖fourierCoeffOn unit_lt (fun s => (g s : ℂ)) n‖ ^ 2
      = 4 * Real.pi ^ 2 * |(n : ℝ)| ^ 2 * ‖fourierCoeffOn unit_lt (fun s => (g s : ℂ)) n‖ ^ 2 := by
        rw [sq_abs]
    _ = (2 * Real.pi * |(n : ℝ)| * ‖fourierCoeffOn unit_lt (fun s => (g s : ℂ)) n‖) ^ 2 := by ring
    _ = ‖fourierCoeffOn unit_lt (fun s => (g' s : ℂ)) n‖ ^ 2 := by rw [hmul]

/-- **1D Bernstein High-Frequency Spectral Shell Inequality (`4π² N²`):**
    If all Fourier modes `|n| < N` of a `C¹` 1-periodic function `g` vanish, then
      `4π² N² ∫₀¹ g(s)² ds ≤ ∫₀¹ g'(s)² ds` (`0 sorryAx`). -/
theorem bernstein_1d_periodic_shell
    {g g' : ℝ → ℝ} (N : ℕ)
    (hg_cont : Continuous g) (hg'_cont : Continuous g')
    (hg_deriv : ∀ s : ℝ, HasDerivAt g (g' s) s)
    (hg_per : ∀ s : ℝ, g (s + 1) = g s)
    (h_low_zero : ∀ n : ℤ, n.natAbs < N → fourierCoeffOn unit_lt (fun s => (g s : ℂ)) n = 0) :
    4 * Real.pi ^ 2 * (N : ℝ) ^ 2 * (∫ s in (0 : ℝ)..1, (g s) ^ 2) ≤
      ∫ s in (0 : ℝ)..1, (g' s) ^ 2 := by
  have hsum_g := (hasSum_sq_fourierCoeffOn_real hg_cont).mul_left (4 * Real.pi ^ 2 * (N : ℝ) ^ 2)
  have hsum_g' := hasSum_sq_fourierCoeffOn_real hg'_cont
  refine hasSum_le (fun n => ?_) hsum_g hsum_g'
  by_cases hlt : n.natAbs < N
  · rw [h_low_zero n hlt, norm_zero, zero_pow (by norm_num : 2 ≠ 0), mul_zero]
    exact sq_nonneg _
  · push Not at hlt
    by_cases hn : n = 0
    · subst hn
      have hN0 : N = 0 := Nat.le_zero.mp hlt
      subst hN0
      simp only [Nat.cast_zero, zero_pow (by norm_num : 2 ≠ 0), mul_zero, zero_mul]
      exact sq_nonneg _
    · rw [← norm_sq_fourierCoeffOn_deriv hg'_cont hg_deriv hg_per hn]
      have hN_le_abs : (N : ℝ) ≤ |(n : ℝ)| := by
        have h1 : (N : ℝ) ≤ (n.natAbs : ℝ) := Nat.cast_le.mpr hlt
        have h2 : (n.natAbs : ℝ) = |(n : ℝ)| := by
          rw [← Int.cast_natCast, ← Int.cast_abs, Int.natCast_natAbs]
        linarith
      have hN_sq : (N : ℝ) ^ 2 ≤ (n : ℝ) ^ 2 := by
        have hsq : (N : ℝ) ^ 2 ≤ |(n : ℝ)| ^ 2 :=
          sq_le_sq.mpr (by rw [abs_of_nonneg (Nat.cast_nonneg N), abs_abs]; exact hN_le_abs)
        rwa [sq_abs] at hsq
      have hfac_nn : 0 ≤ 4 * Real.pi ^ 2 * ‖fourierCoeffOn unit_lt (fun s => (g s : ℂ)) n‖ ^ 2 := by
        positivity
      nlinarith

/-- **Sharp 1D Wirtinger–Poincaré Inequality (`4π²`):**
    For any `C¹` 1-periodic mean-zero function `g : ℝ → ℝ`:
      `4π² ∫₀¹ g(s)² ds ≤ ∫₀¹ g'(s)² ds` (`0 sorryAx`). -/
theorem wirtinger_1d_periodic
    {g g' : ℝ → ℝ}
    (hg_cont : Continuous g) (hg'_cont : Continuous g')
    (hg_deriv : ∀ s : ℝ, HasDerivAt g (g' s) s)
    (hg_per : ∀ s : ℝ, g (s + 1) = g s)
    (hg_mean : ∫ s in (0 : ℝ)..1, g s = 0) :
    4 * Real.pi ^ 2 * (∫ s in (0 : ℝ)..1, (g s) ^ 2) ≤ ∫ s in (0 : ℝ)..1, (g' s) ^ 2 := by
  have h := bernstein_1d_periodic_shell 1 hg_cont hg'_cont hg_deriv hg_per fun n hn => by
    have hn0 : n = 0 := Int.natAbs_eq_zero.mp (Nat.lt_one_iff.mp hn)
    subst hn0
    rw [fourierCoeffOn_zero_eq_mean, hg_mean, Complex.ofReal_zero]
  simpa using h

-- ============================================================================
-- SECTION 2: SHARP 3D WIRTINGER–POINCARÉ (`4π²`) & 3D BERNSTEIN SHELL (`4π² N²`)
-- ============================================================================

private noncomputable abbrev uMeas1' : Measure ℝ := volume.restrict (Set.Icc (0 : ℝ) 1)
private noncomputable abbrev uMeas2' : Measure (ℝ × ℝ) := uMeas1'.prod uMeas1'
private noncomputable abbrev uMeas3' : Measure (ℝ × (ℝ × ℝ)) := uMeas1'.prod uMeas2'
private noncomputable abbrev uSquare' : Set (ℝ × ℝ) := Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1
private noncomputable abbrev uCube' : Set (ℝ × (ℝ × ℝ)) := Set.Icc (0 : ℝ) 1 ×ˢ uSquare'

private theorem isFiniteMeasure_uMeas1' : IsFiniteMeasure uMeas1' :=
  ⟨by rw [Measure.restrict_apply_univ]; exact isCompact_Icc.measure_lt_top⟩

private theorem uMeas2'_eq_restrict : uMeas2' = (volume : Measure (ℝ × ℝ)).restrict uSquare' := by
  unfold uMeas2' uMeas1' uSquare'; rw [Measure.prod_restrict]; rfl

private theorem uMeas3'_eq_restrict :
    uMeas3' = (volume : Measure (ℝ × (ℝ × ℝ))).restrict uCube' := by
  unfold uMeas3' uMeas2' uMeas1' uCube' uSquare'
  rw [Measure.prod_restrict, Measure.prod_restrict]; rfl

private theorem isFiniteMeasure_uMeas2' : IsFiniteMeasure uMeas2' :=
  ⟨by rw [uMeas2'_eq_restrict, Measure.restrict_apply_univ]; exact (isCompact_Icc.prod isCompact_Icc).measure_lt_top⟩

private theorem int1_eq_uMeas1' {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (h : ℝ → E) :
    ∫ t in (0 : ℝ)..1, h t = ∫ t, h t ∂uMeas1' := by
  rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1),
      ← MeasureTheory.integral_Icc_eq_integral_Ioc]

private theorem int2_eq_uMeas2' {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {g : ℝ → ℝ → E} (hg : Continuous (fun p : ℝ × ℝ => g p.1 p.2)) :
    (∫ y in (0 : ℝ)..1, ∫ z in (0 : ℝ)..1, g y z) = ∫ p : ℝ × ℝ, g p.1 p.2 ∂uMeas2' := by
  simp_rw [int1_eq_uMeas1']
  have hint : Integrable (fun p : ℝ × ℝ => g p.1 p.2) uMeas2' := by
    rw [uMeas2'_eq_restrict]
    exact hg.continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)
  exact (MeasureTheory.integral_prod (fun p : ℝ × ℝ => g p.1 p.2) hint).symm

private theorem continuous_int1' {G : ℝ → ℝ → ℝ}
    (hG : Continuous (fun p : ℝ × ℝ => G p.1 p.2)) :
    Continuous (fun t => ∫ z in (0 : ℝ)..1, G t z) := by
  have : IsFiniteMeasure uMeas1' := isFiniteMeasure_uMeas1'
  have h_eq : (fun t => ∫ z in (0 : ℝ)..1, G t z) = (fun t => ∫ z, G t z ∂uMeas1') := by
    funext t; exact int1_eq_uMeas1' (G t)
  rw [h_eq]
  refine continuous_iff_continuousAt.mpr fun t₀ => ?_
  let s : Set ℝ := Set.Icc (t₀ - 1) (t₀ + 1)
  have hs : s ∈ 𝓝 t₀ := Icc_mem_nhds (by linarith) (by linarith)
  obtain ⟨C, hC⟩ := (isCompact_Icc.prod isCompact_Icc).exists_bound_of_continuousOn hG.continuousOn
    (s := s ×ˢ Set.Icc (0 : ℝ) 1)
  have h_meas : ∀ᶠ t in 𝓝 t₀, AEStronglyMeasurable (fun z => G t z) uMeas1' :=
    Eventually.of_forall fun t => (hG.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
  have h_bound : ∀ᶠ t in 𝓝 t₀, ∀ᵐ z ∂uMeas1', ‖G t z‖ ≤ C := by
    filter_upwards [hs] with t ht
    filter_upwards [ae_restrict_mem measurableSet_Icc] with z hz
    exact hC (t, z) ⟨ht, hz⟩
  have h_cont : ∀ᵐ z ∂uMeas1', ContinuousAt (fun t => G t z) t₀ :=
    Eventually.of_forall fun z => (hG.comp (continuous_id.prodMk continuous_const)).continuousAt
  exact continuousAt_of_dominated h_meas h_bound (integrable_const C) h_cont

private theorem continuous_int2' {G : ℝ → ℝ → ℝ → ℝ}
    (hG : Continuous (fun q : ℝ × (ℝ × ℝ) => G q.1 q.2.1 q.2.2)) :
    Continuous (fun x => ∫ y in (0 : ℝ)..1, ∫ z in (0 : ℝ)..1, G x y z) := by
  have h1 : Continuous (fun p : ℝ × ℝ => ∫ z in (0 : ℝ)..1, G p.1 p.2 z) := by
    have : IsFiniteMeasure uMeas1' := isFiniteMeasure_uMeas1'
    have h_eq : (fun p : ℝ × ℝ => ∫ z in (0 : ℝ)..1, G p.1 p.2 z) =
        (fun p : ℝ × ℝ => ∫ z, G p.1 p.2 z ∂uMeas1') := by
      funext p; exact int1_eq_uMeas1' (G p.1 p.2)
    rw [h_eq]
    refine continuous_iff_continuousAt.mpr fun p₀ => ?_
    let s : Set (ℝ × ℝ) := Set.Icc (p₀.1 - 1) (p₀.1 + 1) ×ˢ Set.Icc (p₀.2 - 1) (p₀.2 + 1)
    have hs : s ∈ 𝓝 p₀ := prod_mem_nhds (Icc_mem_nhds (by linarith) (by linarith))
      (Icc_mem_nhds (by linarith) (by linarith))
    have hG' : Continuous (fun r : (ℝ × ℝ) × ℝ => G r.1.1 r.1.2 r.2) :=
      hG.comp ((continuous_fst.comp continuous_fst).prodMk
        ((continuous_snd.comp continuous_fst).prodMk continuous_snd))
    obtain ⟨C, hC⟩ := ((isCompact_Icc.prod isCompact_Icc).prod isCompact_Icc).exists_bound_of_continuousOn
      hG'.continuousOn (s := s ×ˢ Set.Icc (0 : ℝ) 1)
    have h_meas : ∀ᶠ p in 𝓝 p₀, AEStronglyMeasurable (fun z => G p.1 p.2 z) uMeas1' :=
      Eventually.of_forall fun p =>
        (hG'.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
    have h_bound : ∀ᶠ p in 𝓝 p₀, ∀ᵐ z ∂uMeas1', ‖G p.1 p.2 z‖ ≤ C := by
      filter_upwards [hs] with p hp
      filter_upwards [ae_restrict_mem measurableSet_Icc] with z hz
      exact hC (p, z) ⟨hp, hz⟩
    have h_cont : ∀ᵐ z ∂uMeas1', ContinuousAt (fun p : ℝ × ℝ => G p.1 p.2 z) p₀ :=
      Eventually.of_forall fun z => (hG'.comp (continuous_id.prodMk continuous_const)).continuousAt
    exact continuousAt_of_dominated h_meas h_bound (integrable_const C) h_cont
  exact continuous_int1' h1

private theorem hasDerivAt_int1' {F F' : ℝ → ℝ → ℝ}
    (hF : Continuous (fun p : ℝ × ℝ => F p.1 p.2))
    (hF' : Continuous (fun p : ℝ × ℝ => F' p.1 p.2))
    (hdiff : ∀ t z : ℝ, HasDerivAt (fun s => F s z) (F' t z) t) (t₀ : ℝ) :
    HasDerivAt (fun t => ∫ z in (0 : ℝ)..1, F t z) (∫ z in (0 : ℝ)..1, F' t₀ z) t₀ := by
  have : IsFiniteMeasure uMeas1' := isFiniteMeasure_uMeas1'
  have h_eq : (fun t => ∫ z in (0 : ℝ)..1, F t z) = (fun t => ∫ z, F t z ∂uMeas1') := by
    funext t; exact int1_eq_uMeas1' (F t)
  rw [h_eq, int1_eq_uMeas1' (F' t₀)]
  let s : Set ℝ := Set.Icc (t₀ - 1) (t₀ + 1)
  have hs : s ∈ 𝓝 t₀ := Icc_mem_nhds (by linarith) (by linarith)
  obtain ⟨C, hC⟩ := (isCompact_Icc.prod isCompact_Icc).exists_bound_of_continuousOn hF'.continuousOn
    (s := s ×ˢ Set.Icc (0 : ℝ) 1)
  have h_meas : ∀ᶠ t in 𝓝 t₀, AEStronglyMeasurable (fun z => F t z) uMeas1' :=
    Eventually.of_forall fun t => (hF.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
  have h_int : Integrable (fun z => F t₀ z) uMeas1' :=
    (hF.comp (continuous_const.prodMk continuous_id)).continuousOn.integrableOn_compact isCompact_Icc
  have h_meas' : AEStronglyMeasurable (fun z => F' t₀ z) uMeas1' :=
    (hF'.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
  have h_bound : ∀ᵐ z ∂uMeas1', ∀ t ∈ s, ‖F' t z‖ ≤ C := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with z hz t ht
    exact hC (t, z) ⟨ht, hz⟩
  have h_diff_ae : ∀ᵐ z ∂uMeas1', ∀ t ∈ s, HasDerivAt (fun r => F r z) (F' t z) t :=
    Eventually.of_forall fun z t _ => hdiff t z
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le hs h_meas h_int h_meas'
    h_bound (integrable_const C) h_diff_ae).2

private theorem hasDerivAt_int2' {F F' : ℝ → ℝ → ℝ → ℝ}
    (hF : Continuous (fun q : ℝ × (ℝ × ℝ) => F q.1 q.2.1 q.2.2))
    (hF' : Continuous (fun q : ℝ × (ℝ × ℝ) => F' q.1 q.2.1 q.2.2))
    (hdiff : ∀ x y z : ℝ, HasDerivAt (fun s => F s y z) (F' x y z) x) (x₀ : ℝ) :
    HasDerivAt (fun x => ∫ y in (0 : ℝ)..1, ∫ z in (0 : ℝ)..1, F x y z)
      (∫ y in (0 : ℝ)..1, ∫ z in (0 : ℝ)..1, F' x₀ y z) x₀ := by
  have : IsFiniteMeasure uMeas2' := isFiniteMeasure_uMeas2'
  have hF_slice : ∀ x : ℝ, Continuous (fun p : ℝ × ℝ => F x p.1 p.2) :=
    fun x => hF.comp (continuous_const.prodMk continuous_id)
  have hF'_slice : Continuous (fun p : ℝ × ℝ => F' x₀ p.1 p.2) :=
    hF'.comp (continuous_const.prodMk continuous_id)
  have h_eq : (fun x => ∫ y in (0 : ℝ)..1, ∫ z in (0 : ℝ)..1, F x y z) =
      (fun x => ∫ p : ℝ × ℝ, F x p.1 p.2 ∂uMeas2') := by
    funext x; exact int2_eq_uMeas2' (hF_slice x)
  rw [h_eq, int2_eq_uMeas2' hF'_slice]
  let s : Set ℝ := Set.Icc (x₀ - 1) (x₀ + 1)
  have hs : s ∈ 𝓝 x₀ := Icc_mem_nhds (by linarith) (by linarith)
  obtain ⟨C, hC⟩ := (isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc)).exists_bound_of_continuousOn
    hF'.continuousOn (s := s ×ˢ uSquare')
  have h_meas : ∀ᶠ x in 𝓝 x₀, AEStronglyMeasurable (fun p : ℝ × ℝ => F x p.1 p.2) uMeas2' :=
    Eventually.of_forall fun x => (hF_slice x).aestronglyMeasurable
  have h_int : Integrable (fun p : ℝ × ℝ => F x₀ p.1 p.2) uMeas2' := by
    rw [uMeas2'_eq_restrict]
    exact (hF_slice x₀).continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)
  have h_meas' : AEStronglyMeasurable (fun p : ℝ × ℝ => F' x₀ p.1 p.2) uMeas2' :=
    hF'_slice.aestronglyMeasurable
  have h_bound : ∀ᵐ p ∂uMeas2', ∀ x ∈ s, ‖F' x p.1 p.2‖ ≤ C := by
    rw [uMeas2'_eq_restrict]
    filter_upwards [ae_restrict_mem (measurableSet_Icc.prod measurableSet_Icc)] with p hp x hx
    exact hC (x, p) ⟨hx, hp⟩
  have h_diff_ae : ∀ᵐ p ∂uMeas2', ∀ x ∈ s, HasDerivAt (fun r => F r p.1 p.2) (F' x p.1 p.2) x :=
    Eventually.of_forall fun p x _ => hdiff x p.1 p.2
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le hs h_meas h_int h_meas'
    h_bound (integrable_const C) h_diff_ae).2

private theorem variance_unit' {φ : ℝ → ℝ} (hφ : Continuous φ) :
    (∫ s in (0 : ℝ)..1, (φ s) ^ 2) =
      (∫ s in (0 : ℝ)..1, (φ s - ∫ u in (0 : ℝ)..1, φ u) ^ 2) +
      (∫ u in (0 : ℝ)..1, φ u) ^ 2 := by
  let m : ℝ := ∫ u in (0 : ℝ)..1, φ u
  have h_exp : (∫ s in (0 : ℝ)..1, (φ s - m) ^ 2) =
      ∫ s in (0 : ℝ)..1, (((φ s) ^ 2 - 2 * m * φ s) + m ^ 2) := by
    congr 1; funext s; ring
  have hc1 : Continuous (fun s => (φ s) ^ 2) := hφ.pow 2
  have hc2 : Continuous (fun s => 2 * m * φ s) := continuous_const.mul hφ
  have hc3 : Continuous (fun _ : ℝ => m ^ 2) := continuous_const
  have hc12 : Continuous (fun s : ℝ => (φ s) ^ 2 - 2 * m * φ s) := hc1.sub hc2
  rw [h_exp,
      intervalIntegral.integral_add (hc12.intervalIntegrable (μ := volume) 0 1) (hc3.intervalIntegrable (μ := volume) 0 1),
      intervalIntegral.integral_sub (hc1.intervalIntegrable (μ := volume) 0 1) (hc2.intervalIntegrable (μ := volume) 0 1),
      intervalIntegral.integral_const_mul (2 * m) φ,
      intervalIntegral.integral_const]
  simp only [sub_zero, one_smul]
  dsimp only [m]
  ring

private theorem unitSq_le_intSq' {φ : ℝ → ℝ} (hφ : Continuous φ) :
    (∫ t in (0 : ℝ)..1, φ t) ^ 2 ≤ ∫ t in (0 : ℝ)..1, (φ t) ^ 2 := by
  have h := intervalIntegral_sq_le_mul_integral_sq (by norm_num : (0 : ℝ) ≤ 1) hφ
  linarith

private theorem cont_vec3_xyz' : Continuous (fun q : ℝ × (ℝ × ℝ) => vec3 q.1 q.2.1 q.2.2) :=
  continuous_pi fun i => match i with
    | ⟨0, _⟩ => continuous_fst | ⟨1, _⟩ => continuous_fst.comp continuous_snd | ⟨2, _⟩ => continuous_snd.comp continuous_snd

private theorem cont_vec3_yz' (x : ℝ) : Continuous (fun p : ℝ × ℝ => vec3 x p.1 p.2) :=
  continuous_pi fun k => match k with
    | ⟨0, _⟩ => continuous_const | ⟨1, _⟩ => continuous_fst | ⟨2, _⟩ => continuous_snd

private theorem cont_vec3_z' (x y : ℝ) : Continuous (fun z : ℝ => vec3 x y z) :=
  continuous_pi fun k => match k with
    | ⟨0, _⟩ => continuous_const | ⟨1, _⟩ => continuous_const | ⟨2, _⟩ => continuous_id

private theorem vec3_add_b0' (x y z : ℝ) : vec3 (x + 1) y z = vec3 x y z + basisVec 0 := by
  funext i; match i with | ⟨0, _⟩ => simp [vec3, basisVec] | ⟨1, _⟩ => simp [vec3, basisVec] | ⟨2, _⟩ => simp [vec3, basisVec]

private theorem vec3_add_b1' (x y z : ℝ) : vec3 x (y + 1) z = vec3 x y z + basisVec 1 := by
  funext i; match i with | ⟨0, _⟩ => simp [vec3, basisVec] | ⟨1, _⟩ => simp [vec3, basisVec] | ⟨2, _⟩ => simp [vec3, basisVec]

private theorem vec3_add_b2' (x y z : ℝ) : vec3 x y (z + 1) = vec3 x y z + basisVec 2 := by
  funext i; match i with | ⟨0, _⟩ => simp [vec3, basisVec] | ⟨1, _⟩ => simp [vec3, basisVec] | ⟨2, _⟩ => simp [vec3, basisVec]

private theorem hda_vec3_0' (y z t : ℝ) : HasDerivAt (fun s => vec3 s y z) (basisVec 0) t := by
  refine hasDerivAt_pi.mpr fun k => ?_
  match k with
  | ⟨0, _⟩ => change HasDerivAt (fun s : ℝ => s) 1 t; exact hasDerivAt_id t
  | ⟨1, _⟩ => change HasDerivAt (fun _ : ℝ => y) 0 t; exact hasDerivAt_const t y
  | ⟨2, _⟩ => change HasDerivAt (fun _ : ℝ => z) 0 t; exact hasDerivAt_const t z

private theorem hda_vec3_1' (x z t : ℝ) : HasDerivAt (fun s => vec3 x s z) (basisVec 1) t := by
  refine hasDerivAt_pi.mpr fun k => ?_
  match k with
  | ⟨0, _⟩ => change HasDerivAt (fun _ : ℝ => x) 0 t; exact hasDerivAt_const t x
  | ⟨1, _⟩ => change HasDerivAt (fun s : ℝ => s) 1 t; exact hasDerivAt_id t
  | ⟨2, _⟩ => change HasDerivAt (fun _ : ℝ => z) 0 t; exact hasDerivAt_const t z

private theorem hda_vec3_2' (x y t : ℝ) : HasDerivAt (fun s => vec3 x y s) (basisVec 2) t := by
  refine hasDerivAt_pi.mpr fun k => ?_
  match k with
  | ⟨0, _⟩ => change HasDerivAt (fun _ : ℝ => x) 0 t; exact hasDerivAt_const t x
  | ⟨1, _⟩ => change HasDerivAt (fun _ : ℝ => y) 0 t; exact hasDerivAt_const t y
  | ⟨2, _⟩ => change HasDerivAt (fun s : ℝ => s) 1 t; exact hasDerivAt_id t

private theorem wirtinger_3d_step_z
    {f : R3 → ℝ} (hf : ContDiff ℝ 1 f) (hpf : IsPeriodic3D f) (x y : ℝ) :
    4 * Real.pi ^ 2 * (∫ z in (0 : ℝ)..1, (f (vec3 x y z) - ∫ u in (0 : ℝ)..1, f (vec3 x y u)) ^ 2) ≤
      ∫ z in (0 : ℝ)..1, (partialDerivScalar f (vec3 x y z) 2) ^ 2 := by
  have hdiff : Differentiable ℝ f := hf.differentiable (by simp)
  have hc_p2 := continuous_partialDerivScalar_of_contDiff hf 2
  have hcz : Continuous (fun z => f (vec3 x y z)) := hf.continuous.comp (cont_vec3_z' x y)
  have hcz_sub : Continuous (fun z => f (vec3 x y z) - ∫ u in (0 : ℝ)..1, f (vec3 x y u)) :=
    hcz.sub continuous_const
  have hcz' : Continuous (fun z => partialDerivScalar f (vec3 x y z) 2) :=
    hc_p2.comp (cont_vec3_z' x y)
  have hmean_z : ∫ z in (0 : ℝ)..1, (f (vec3 x y z) - ∫ u in (0 : ℝ)..1, f (vec3 x y u)) = 0 := by
    rw [intervalIntegral.integral_sub (hcz.intervalIntegrable (μ := volume) 0 1)
          (continuous_const.intervalIntegrable (μ := volume) 0 1),
        intervalIntegral.integral_const]
    simp only [sub_zero, one_smul]; ring
  exact wirtinger_1d_periodic hcz_sub hcz'
    (fun z => ((hdiff (vec3 x y z)).hasFDerivAt.comp_hasDerivAt z (hda_vec3_2' x y z)).sub_const _)
    (fun z => by rw [vec3_add_b2', hpf (vec3 x y z) 2])
    hmean_z

private theorem wirtinger_3d_step_y
    {f : R3 → ℝ} (hf : ContDiff ℝ 1 f) (hpf : IsPeriodic3D f) (x : ℝ) :
    4 * Real.pi ^ 2 * (∫ y in (0 : ℝ)..1,
        ((∫ z in (0 : ℝ)..1, f (vec3 x y z)) -
         ∫ v in (0 : ℝ)..1, ∫ z in (0 : ℝ)..1, f (vec3 x v z)) ^ 2) ≤
      ∫ y in (0 : ℝ)..1, ∫ z in (0 : ℝ)..1, (partialDerivScalar f (vec3 x y z) 1) ^ 2 := by
  have hdiff : Differentiable ℝ f := hf.differentiable (by simp)
  have hc_p1 := continuous_partialDerivScalar_of_contDiff hf 1
  let f1x : ℝ → ℝ := fun y => ∫ z in (0 : ℝ)..1, f (vec3 x y z)
  let df1 : ℝ → ℝ := fun y => ∫ z in (0 : ℝ)..1, partialDerivScalar f (vec3 x y z) 1
  have hF_cont : Continuous (fun p : ℝ × ℝ => f (vec3 x p.1 p.2)) :=
    hf.continuous.comp (cont_vec3_yz' x)
  have hF'_cont : Continuous (fun p : ℝ × ℝ => partialDerivScalar f (vec3 x p.1 p.2) 1) :=
    hc_p1.comp (cont_vec3_yz' x)
  have hF'_sq : Continuous (fun p : ℝ × ℝ => (partialDerivScalar f (vec3 x p.1 p.2) 1) ^ 2) :=
    hF'_cont.pow 2
  have hf1_cont : Continuous f1x := continuous_int1' (G := fun y z => f (vec3 x y z)) hF_cont
  have hf1_sub : Continuous (fun y => f1x y - ∫ v in (0 : ℝ)..1, f1x v) := hf1_cont.sub continuous_const
  have hdf1_cont : Continuous df1 :=
    continuous_int1' (G := fun y z => partialDerivScalar f (vec3 x y z) 1) hF'_cont
  have hf1_deriv : ∀ y : ℝ, HasDerivAt f1x (df1 y) y := fun y =>
    hasDerivAt_int1'
      (F := fun s z => f (vec3 x s z))
      (F' := fun s z => partialDerivScalar f (vec3 x s z) 1)
      hF_cont hF'_cont
      (fun s z => (hdiff (vec3 x s z)).hasFDerivAt.comp_hasDerivAt s (hda_vec3_1' x z s)) y
  have hmean_y : ∫ y in (0 : ℝ)..1, (f1x y - ∫ v in (0 : ℝ)..1, f1x v) = 0 := by
    rw [intervalIntegral.integral_sub (hf1_cont.intervalIntegrable (μ := volume) 0 1)
          (continuous_const.intervalIntegrable (μ := volume) 0 1),
        intervalIntegral.integral_const]
    simp only [sub_zero, one_smul]; ring
  have hw_y := wirtinger_1d_periodic hf1_sub hdf1_cont
    (fun y => (hf1_deriv y).sub_const _)
    (fun y => by
      dsimp only [f1x]
      have heq : (fun z => f (vec3 x (y + 1) z)) = (fun z => f (vec3 x y z)) := by
        funext z; rw [vec3_add_b1', hpf (vec3 x y z) 1]
      rw [heq])
    hmean_y
  have hc_lhs : Continuous (fun y => (df1 y) ^ 2) := hdf1_cont.pow 2
  have hc_rhs : Continuous (fun y => ∫ z in (0 : ℝ)..1, (partialDerivScalar f (vec3 x y z) 1) ^ 2) :=
    continuous_int1' (G := fun y z => (partialDerivScalar f (vec3 x y z) 1) ^ 2) hF'_sq
  have hcs_y : (∫ y in (0 : ℝ)..1, (df1 y) ^ 2) ≤
      ∫ y in (0 : ℝ)..1, ∫ z in (0 : ℝ)..1, (partialDerivScalar f (vec3 x y z) 1) ^ 2 :=
    intervalIntegral.integral_mono_on (μ := volume) (by norm_num : (0 : ℝ) ≤ 1)
      (hc_lhs.intervalIntegrable (μ := volume) 0 1) (hc_rhs.intervalIntegrable (μ := volume) 0 1)
      fun y _ => unitSq_le_intSq' (hc_p1.comp (cont_vec3_z' x y))
  exact le_trans hw_y hcs_y

private theorem wirtinger_3d_step_x
    {f : R3 → ℝ} (hf : ContDiff ℝ 1 f) (hpf : IsPeriodic3D f)
    (hmean : torusIntegral f = 0) :
    4 * Real.pi ^ 2 * (∫ x in (0 : ℝ)..1, (∫ y in (0 : ℝ)..1, ∫ z in (0 : ℝ)..1, f (vec3 x y z)) ^ 2) ≤
      torusIntegral (fun p => (partialDerivScalar f p 0) ^ 2) := by
  have hdiff : Differentiable ℝ f := hf.differentiable (by simp)
  have hc_p0 := continuous_partialDerivScalar_of_contDiff hf 0
  let f2 : ℝ → ℝ := fun x => ∫ y in (0 : ℝ)..1, ∫ z in (0 : ℝ)..1, f (vec3 x y z)
  let df2 : ℝ → ℝ := fun x =>
    ∫ y in (0 : ℝ)..1, ∫ z in (0 : ℝ)..1, partialDerivScalar f (vec3 x y z) 0
  have hF_all : Continuous (fun q : ℝ × (ℝ × ℝ) => f (vec3 q.1 q.2.1 q.2.2)) :=
    hf.continuous.comp cont_vec3_xyz'
  have hF'_cont : Continuous (fun q : ℝ × (ℝ × ℝ) => partialDerivScalar f (vec3 q.1 q.2.1 q.2.2) 0) :=
    hc_p0.comp cont_vec3_xyz'
  have hF'_sq : Continuous (fun q : ℝ × (ℝ × ℝ) => (partialDerivScalar f (vec3 q.1 q.2.1 q.2.2) 0) ^ 2) :=
    hF'_cont.pow 2
  have hf2_cont : Continuous f2 := continuous_int2' (G := fun x y z => f (vec3 x y z)) hF_all
  have hdf2_cont : Continuous df2 :=
    continuous_int2' (G := fun x y z => partialDerivScalar f (vec3 x y z) 0) hF'_cont
  have hf2_deriv : ∀ x : ℝ, HasDerivAt f2 (df2 x) x := fun x =>
    hasDerivAt_int2'
      (F := fun s y z => f (vec3 s y z))
      (F' := fun s y z => partialDerivScalar f (vec3 s y z) 0)
      hF_all hF'_cont
      (fun s y z => (hdiff (vec3 s y z)).hasFDerivAt.comp_hasDerivAt s (hda_vec3_0' y z s)) x
  have hw_x := wirtinger_1d_periodic hf2_cont hdf2_cont hf2_deriv
    (fun x => by
      dsimp only [f2]
      have heq : ∀ y z : ℝ, f (vec3 (x + 1) y z) = f (vec3 x y z) := fun y z => by
        rw [vec3_add_b0', hpf (vec3 x y z) 0]
      simp_rw [heq])
    hmean
  have hc_lhs : Continuous (fun x => (df2 x) ^ 2) := hdf2_cont.pow 2
  have hc_rhs : Continuous (fun x =>
      ∫ y in (0 : ℝ)..1, ∫ z in (0 : ℝ)..1, (partialDerivScalar f (vec3 x y z) 0) ^ 2) :=
    continuous_int2' (G := fun x y z => (partialDerivScalar f (vec3 x y z) 0) ^ 2) hF'_sq
  have hcs_x : (∫ x in (0 : ℝ)..1, (df2 x) ^ 2) ≤
      torusIntegral (fun p => (partialDerivScalar f p 0) ^ 2) := by
    unfold torusIntegral
    refine intervalIntegral.integral_mono_on (μ := volume) (by norm_num : (0 : ℝ) ≤ 1)
      (hc_lhs.intervalIntegrable (μ := volume) 0 1) (hc_rhs.intervalIntegrable (μ := volume) 0 1)
      fun x _ => ?_
    have hFx' : Continuous (fun p : ℝ × ℝ => partialDerivScalar f (vec3 x p.1 p.2) 0) :=
      hc_p0.comp (cont_vec3_yz' x)
    have hcy : Continuous (fun y => ∫ z in (0 : ℝ)..1, partialDerivScalar f (vec3 x y z) 0) :=
      continuous_int1' (G := fun y z => partialDerivScalar f (vec3 x y z) 0) hFx'
    have hcs1 := unitSq_le_intSq' hcy
    have hcy_sq : Continuous (fun y => (∫ z in (0 : ℝ)..1, partialDerivScalar f (vec3 x y z) 0) ^ 2) :=
      hcy.pow 2
    have hcz_sq : Continuous (fun y => ∫ z in (0 : ℝ)..1, (partialDerivScalar f (vec3 x y z) 0) ^ 2) :=
      continuous_int1' (G := fun y z => (partialDerivScalar f (vec3 x y z) 0) ^ 2) (hFx'.pow 2)
    have hcs2 : (∫ y in (0 : ℝ)..1, (∫ z in (0 : ℝ)..1, partialDerivScalar f (vec3 x y z) 0) ^ 2) ≤
        ∫ y in (0 : ℝ)..1, ∫ z in (0 : ℝ)..1, (partialDerivScalar f (vec3 x y z) 0) ^ 2 :=
      intervalIntegral.integral_mono_on (μ := volume) (by norm_num : (0 : ℝ) ≤ 1)
        (hcy_sq.intervalIntegrable (μ := volume) 0 1) (hcz_sq.intervalIntegrable (μ := volume) 0 1)
        fun y _ => unitSq_le_intSq' (hc_p0.comp (cont_vec3_z' x y))
    exact le_trans hcs1 hcs2
  exact le_trans hw_x hcs_x

/-- **Sharp 3D Wirtinger–Poincaré Inequality on `𝕋³` (Scalar, Optimal Constant `4π²`):**
    For any `C¹` periodic scalar field `f` with zero spatial mean:
      `4π² ∫_{𝕋³} f(x)² dx ≤ ∫_{𝕋³} |∇f(x)|² dx` (`0 sorryAx`). -/
theorem wirtinger_3d_torus
    {f : R3 → ℝ} (hf : ContDiff ℝ 1 f) (hpf : IsPeriodic3D f)
    (hmean : torusIntegral f = 0) :
    4 * Real.pi ^ 2 * torusIntegral (fun x => (f x) ^ 2) ≤
      torusIntegral (fun x =>
        (partialDerivScalar f x 0) ^ 2 +
        (partialDerivScalar f x 1) ^ 2 +
        (partialDerivScalar f x 2) ^ 2) := by
  let C : ℝ := 4 * Real.pi ^ 2
  have hc_p0 := continuous_partialDerivScalar_of_contDiff hf 0
  have hc_p1 := continuous_partialDerivScalar_of_contDiff hf 1
  have hc_p2 := continuous_partialDerivScalar_of_contDiff hf 2
  let f1 : ℝ → ℝ → ℝ := fun x y => ∫ z in (0 : ℝ)..1, f (vec3 x y z)
  let f2 : ℝ → ℝ := fun x => ∫ y in (0 : ℝ)..1, f1 x y
  have hF_all : Continuous (fun q : ℝ × (ℝ × ℝ) => f (vec3 q.1 q.2.1 q.2.2)) :=
    hf.continuous.comp cont_vec3_xyz'
  have hF_sq : Continuous (fun q : ℝ × (ℝ × ℝ) => (f (vec3 q.1 q.2.1 q.2.2)) ^ 2) := hF_all.pow 2
  have hF_p1_sq : Continuous (fun q : ℝ × (ℝ × ℝ) => (partialDerivScalar f (vec3 q.1 q.2.1 q.2.2) 1) ^ 2) :=
    (hc_p1.comp cont_vec3_xyz').pow 2
  have hF_p2_sq : Continuous (fun q : ℝ × (ℝ × ℝ) => (partialDerivScalar f (vec3 q.1 q.2.1 q.2.2) 2) ^ 2) :=
    (hc_p2.comp cont_vec3_xyz').pow 2
  have hf2_cont : Continuous f2 := continuous_int2' (G := fun x y z => f (vec3 x y z)) hF_all
  have h_xy_bound : ∀ x : ℝ,
      C * (∫ y in (0 : ℝ)..1, ∫ z in (0 : ℝ)..1, (f (vec3 x y z)) ^ 2) ≤
        (∫ y in (0 : ℝ)..1, ∫ z in (0 : ℝ)..1, (partialDerivScalar f (vec3 x y z) 2) ^ 2) +
        (∫ y in (0 : ℝ)..1, ∫ z in (0 : ℝ)..1, (partialDerivScalar f (vec3 x y z) 1) ^ 2) +
        C * (f2 x) ^ 2 := by
    intro x
    have hFx : Continuous (fun p : ℝ × ℝ => f (vec3 x p.1 p.2)) :=
      hf.continuous.comp (cont_vec3_yz' x)
    have hFx_sq : Continuous (fun p : ℝ × ℝ => (f (vec3 x p.1 p.2)) ^ 2) := hFx.pow 2
    have hFp2x_sq : Continuous (fun p : ℝ × ℝ => (partialDerivScalar f (vec3 x p.1 p.2) 2) ^ 2) :=
      (hc_p2.comp (cont_vec3_yz' x)).pow 2
    have hf1_cont : Continuous (fun y => f1 x y) :=
      continuous_int1' (G := fun y z => f (vec3 x y z)) hFx
    have h_step_z : ∀ y : ℝ,
        C * (∫ z in (0 : ℝ)..1, (f (vec3 x y z)) ^ 2) ≤
          (∫ z in (0 : ℝ)..1, (partialDerivScalar f (vec3 x y z) 2) ^ 2) + C * (f1 x y) ^ 2 := fun y => by
      have hcz : Continuous (fun z => f (vec3 x y z)) := hf.continuous.comp (cont_vec3_z' x y)
      have h_var_z := variance_unit' hcz
      have h_wz : C * (∫ z in (0 : ℝ)..1, (f (vec3 x y z) - f1 x y) ^ 2) ≤
          ∫ z in (0 : ℝ)..1, (partialDerivScalar f (vec3 x y z) 2) ^ 2 := wirtinger_3d_step_z hf hpf x y
      have hmul : C * (∫ z in (0 : ℝ)..1, (f (vec3 x y z)) ^ 2) =
          C * (∫ z in (0 : ℝ)..1, (f (vec3 x y z) - f1 x y) ^ 2) + C * (f1 x y) ^ 2 := by
        dsimp only [f1]; rw [h_var_z]; ring
      linarith
    have hc_lhs : Continuous (fun y => C * ∫ z in (0 : ℝ)..1, (f (vec3 x y z)) ^ 2) :=
      continuous_const.mul (continuous_int1' (G := fun y z => (f (vec3 x y z)) ^ 2) hFx_sq)
    have hc_rhs1 : Continuous (fun y => ∫ z in (0 : ℝ)..1, (partialDerivScalar f (vec3 x y z) 2) ^ 2) :=
      continuous_int1' (G := fun y z => (partialDerivScalar f (vec3 x y z) 2) ^ 2) hFp2x_sq
    have hc_rhs2 : Continuous (fun y => C * (f1 x y) ^ 2) := continuous_const.mul (hf1_cont.pow 2)
    have hc_rhs12 : Continuous (fun y =>
        (∫ z in (0 : ℝ)..1, (partialDerivScalar f (vec3 x y z) 2) ^ 2) + C * (f1 x y) ^ 2) :=
      hc_rhs1.add hc_rhs2
    have h_int_y := intervalIntegral.integral_mono_on (μ := volume) (by norm_num : (0 : ℝ) ≤ 1)
      (hc_lhs.intervalIntegrable (μ := volume) 0 1) (hc_rhs12.intervalIntegrable (μ := volume) 0 1)
      (fun y _ => h_step_z y)
    rw [intervalIntegral.integral_const_mul C,
        intervalIntegral.integral_add (hc_rhs1.intervalIntegrable (μ := volume) 0 1)
          (hc_rhs2.intervalIntegrable (μ := volume) 0 1),
        intervalIntegral.integral_const_mul C] at h_int_y
    have h_var_y := variance_unit' hf1_cont
    have h_wy : C * (∫ y in (0 : ℝ)..1, (f1 x y - f2 x) ^ 2) ≤
        ∫ y in (0 : ℝ)..1, ∫ z in (0 : ℝ)..1, (partialDerivScalar f (vec3 x y z) 1) ^ 2 :=
      wirtinger_3d_step_y hf hpf x
    have hmul_y : C * (∫ y in (0 : ℝ)..1, (f1 x y) ^ 2) =
        C * (∫ y in (0 : ℝ)..1, (f1 x y - f2 x) ^ 2) + C * (f2 x) ^ 2 := by
      dsimp only [f2, f1]; rw [h_var_y]; ring
    linarith
  have hc_x_lhs : Continuous (fun x => C * ∫ y in (0 : ℝ)..1, ∫ z in (0 : ℝ)..1, (f (vec3 x y z)) ^ 2) :=
    continuous_const.mul (continuous_int2' (G := fun x y z => (f (vec3 x y z)) ^ 2) hF_sq)
  have hc_x_p2 : Continuous (fun x => ∫ y in (0 : ℝ)..1, ∫ z in (0 : ℝ)..1, (partialDerivScalar f (vec3 x y z) 2) ^ 2) :=
    continuous_int2' (G := fun x y z => (partialDerivScalar f (vec3 x y z) 2) ^ 2) hF_p2_sq
  have hc_x_p1 : Continuous (fun x => ∫ y in (0 : ℝ)..1, ∫ z in (0 : ℝ)..1, (partialDerivScalar f (vec3 x y z) 1) ^ 2) :=
    continuous_int2' (G := fun x y z => (partialDerivScalar f (vec3 x y z) 1) ^ 2) hF_p1_sq
  have hc_x_f2 : Continuous (fun x => C * (f2 x) ^ 2) := continuous_const.mul (hf2_cont.pow 2)
  have hc_x_p21 : Continuous (fun x =>
      (∫ y in (0 : ℝ)..1, ∫ z in (0 : ℝ)..1, (partialDerivScalar f (vec3 x y z) 2) ^ 2) +
      (∫ y in (0 : ℝ)..1, ∫ z in (0 : ℝ)..1, (partialDerivScalar f (vec3 x y z) 1) ^ 2)) :=
    hc_x_p2.add hc_x_p1
  have hc_x_all : Continuous (fun x =>
      (∫ y in (0 : ℝ)..1, ∫ z in (0 : ℝ)..1, (partialDerivScalar f (vec3 x y z) 2) ^ 2) +
      (∫ y in (0 : ℝ)..1, ∫ z in (0 : ℝ)..1, (partialDerivScalar f (vec3 x y z) 1) ^ 2) +
      C * (f2 x) ^ 2) :=
    hc_x_p21.add hc_x_f2
  have h_final_x := intervalIntegral.integral_mono_on (μ := volume) (by norm_num : (0 : ℝ) ≤ 1)
    (hc_x_lhs.intervalIntegrable (μ := volume) 0 1) (hc_x_all.intervalIntegrable (μ := volume) 0 1)
    (fun x _ => h_xy_bound x)
  rw [intervalIntegral.integral_const_mul C,
      intervalIntegral.integral_add (hc_x_p21.intervalIntegrable (μ := volume) 0 1)
        (hc_x_f2.intervalIntegrable (μ := volume) 0 1),
      intervalIntegral.integral_add (hc_x_p2.intervalIntegrable (μ := volume) 0 1)
        (hc_x_p1.intervalIntegrable (μ := volume) 0 1),
      intervalIntegral.integral_const_mul C] at h_final_x
  have hc_p0_sq : Continuous (fun x => (partialDerivScalar f x 0) ^ 2) := hc_p0.pow 2
  have hc_p1_sq : Continuous (fun x => (partialDerivScalar f x 1) ^ 2) := hc_p1.pow 2
  have hc_p2_sq : Continuous (fun x => (partialDerivScalar f x 2) ^ 2) := hc_p2.pow 2
  have h_wx : C * (∫ x in (0 : ℝ)..1, (f2 x) ^ 2) ≤
      torusIntegral (fun p => (partialDerivScalar f p 0) ^ 2) := wirtinger_3d_step_x hf hpf hmean
  rw [torusIntegral_add3 hc_p0_sq hc_p1_sq hc_p2_sq]
  unfold torusIntegral at h_wx ⊢
  dsimp only [C, f2, f1] at h_final_x h_wx ⊢
  linarith

/-- **Sharp 3D Vector Wirtinger–Poincaré Inequality on `𝕋³` (`4π²`):**
    For any `C¹` periodic vector field `w` with zero-mean components:
      `4π² ∫_{𝕋³} |w(x)|² dx ≤ ∫_{𝕋³} |∇w(x)|² dx` (`0 sorryAx`). -/
theorem wirtinger_3d_torus_vec
    {w : R3 → R3} (hw : ContDiff ℝ 1 w) (hpw : IsPeriodic3D w)
    (hmean : ∀ comp : Fin 3, torusIntegral (fun x => w x comp) = 0) :
    4 * Real.pi ^ 2 * torusIntegral (fun x => dot3D (w x) (w x)) ≤ torusIntegral (gradNormSq3D w) := by
  have hw0 : ContDiff ℝ 1 (fun y => w y 0) := contDiff_pi.mp hw 0
  have hw1 : ContDiff ℝ 1 (fun y => w y 1) := contDiff_pi.mp hw 1
  have hw2 : ContDiff ℝ 1 (fun y => w y 2) := contDiff_pi.mp hw 2
  have hpw0 : IsPeriodic3D (fun y => w y 0) := fun x i => congrArg (fun v => v 0) (hpw x i)
  have hpw1 : IsPeriodic3D (fun y => w y 1) := fun x i => congrArg (fun v => v 1) (hpw x i)
  have hpw2 : IsPeriodic3D (fun y => w y 2) := fun x i => congrArg (fun v => v 2) (hpw x i)
  have hp0 := wirtinger_3d_torus hw0 hpw0 (hmean 0)
  have hp1 := wirtinger_3d_torus hw1 hpw1 (hmean 1)
  have hp2 := wirtinger_3d_torus hw2 hpw2 (hmean 2)
  have hdot : torusIntegral (fun x => dot3D (w x) (w x)) =
      torusIntegral (fun x => (w x 0) ^ 2) +
      torusIntegral (fun x => (w x 1) ^ 2) +
      torusIntegral (fun x => (w x 2) ^ 2) := by
    have hpt : ∀ x : R3, dot3D (w x) (w x) = (w x 0) ^ 2 + (w x 1) ^ 2 + (w x 2) ^ 2 := fun x => by
      unfold dot3D; ring
    have hcw0 : Continuous (fun x => (w x 0) ^ 2) := hw0.continuous.pow 2
    have hcw1 : Continuous (fun x => (w x 1) ^ 2) := hw1.continuous.pow 2
    have hcw2 : Continuous (fun x => (w x 2) ^ 2) := hw2.continuous.pow 2
    rw [torusIntegral_congr hpt, torusIntegral_add3 hcw0 hcw1 hcw2]
  have hq : ∀ (f : R3 → ℝ), ContDiff ℝ 1 f → Continuous (fun x =>
      (partialDerivScalar f x 0) ^ 2 + (partialDerivScalar f x 1) ^ 2 + (partialDerivScalar f x 2) ^ 2) :=
    fun f hf =>
      (((continuous_partialDerivScalar_of_contDiff hf 0).pow 2).add
       ((continuous_partialDerivScalar_of_contDiff hf 1).pow 2)).add
      ((continuous_partialDerivScalar_of_contDiff hf 2).pow 2)
  have hgrad : torusIntegral (gradNormSq3D w) =
      torusIntegral (fun x => (partialDerivScalar (fun y => w y 0) x 0) ^ 2 +
        (partialDerivScalar (fun y => w y 0) x 1) ^ 2 + (partialDerivScalar (fun y => w y 0) x 2) ^ 2) +
      torusIntegral (fun x => (partialDerivScalar (fun y => w y 1) x 0) ^ 2 +
        (partialDerivScalar (fun y => w y 1) x 1) ^ 2 + (partialDerivScalar (fun y => w y 1) x 2) ^ 2) +
      torusIntegral (fun x => (partialDerivScalar (fun y => w y 2) x 0) ^ 2 +
        (partialDerivScalar (fun y => w y 2) x 1) ^ 2 + (partialDerivScalar (fun y => w y 2) x 2) ^ 2) := by
    have hpt : ∀ x : R3, gradNormSq3D w x =
        ((partialDerivScalar (fun y => w y 0) x 0) ^ 2 +
         (partialDerivScalar (fun y => w y 0) x 1) ^ 2 + (partialDerivScalar (fun y => w y 0) x 2) ^ 2) +
        ((partialDerivScalar (fun y => w y 1) x 0) ^ 2 +
         (partialDerivScalar (fun y => w y 1) x 1) ^ 2 + (partialDerivScalar (fun y => w y 1) x 2) ^ 2) +
        ((partialDerivScalar (fun y => w y 2) x 0) ^ 2 +
         (partialDerivScalar (fun y => w y 2) x 1) ^ 2 + (partialDerivScalar (fun y => w y 2) x 2) ^ 2) :=
      fun x => by unfold gradNormSq3D; ring
    rw [torusIntegral_congr hpt, torusIntegral_add3 (hq _ hw0) (hq _ hw1) (hq _ hw2)]
  rw [hdot, hgrad]
  linarith

/-- **3D Bernstein High-Frequency Shell Coercivity (`4π² N²`):**
    If all `z`-slice Fourier modes `|n| < N` of a `C¹` periodic scalar field `f` vanish, then
      `4π² N² ∫_{𝕋³} f(x)² dx ≤ ∫_{𝕋³} |∇f(x)|² dx` (`0 sorryAx`). -/
theorem bernstein_3d_torus_z_shell
    {f : R3 → ℝ} (N : ℕ) (hf : ContDiff ℝ 1 f) (hpf : IsPeriodic3D f)
    (h_low : ∀ (x y : ℝ) (n : ℤ), n.natAbs < N →
      fourierCoeffOn unit_lt (fun z => (f (vec3 x y z) : ℂ)) n = 0) :
    4 * Real.pi ^ 2 * (N : ℝ) ^ 2 * torusIntegral (fun x => (f x) ^ 2) ≤
      torusIntegral (fun x =>
        (partialDerivScalar f x 0) ^ 2 +
        (partialDerivScalar f x 1) ^ 2 +
        (partialDerivScalar f x 2) ^ 2) := by
  let C : ℝ := 4 * Real.pi ^ 2 * (N : ℝ) ^ 2
  have hdiff : Differentiable ℝ f := hf.differentiable (by simp)
  have hc_p0 := continuous_partialDerivScalar_of_contDiff hf 0
  have hc_p1 := continuous_partialDerivScalar_of_contDiff hf 1
  have hc_p2 := continuous_partialDerivScalar_of_contDiff hf 2
  have h_slice : ∀ x y : ℝ,
      C * (∫ z in (0 : ℝ)..1, (f (vec3 x y z)) ^ 2) ≤
        ∫ z in (0 : ℝ)..1, (partialDerivScalar f (vec3 x y z) 2) ^ 2 := fun x y =>
    bernstein_1d_periodic_shell N
      (hf.continuous.comp (cont_vec3_z' x y))
      (hc_p2.comp (cont_vec3_z' x y))
      (fun z => (hdiff (vec3 x y z)).hasFDerivAt.comp_hasDerivAt z (hda_vec3_2' x y z))
      (fun z => by rw [vec3_add_b2', hpf (vec3 x y z) 2])
      (h_low x y)
  have hF_sq : Continuous (fun q : ℝ × (ℝ × ℝ) => (f (vec3 q.1 q.2.1 q.2.2)) ^ 2) :=
    (hf.continuous.comp cont_vec3_xyz').pow 2
  have hP2_sq : Continuous (fun q : ℝ × (ℝ × ℝ) => (partialDerivScalar f (vec3 q.1 q.2.1 q.2.2) 2) ^ 2) :=
    (hc_p2.comp cont_vec3_xyz').pow 2
  have h_y_int : ∀ x : ℝ,
      C * (∫ y in (0 : ℝ)..1, ∫ z in (0 : ℝ)..1, (f (vec3 x y z)) ^ 2) ≤
        ∫ y in (0 : ℝ)..1, ∫ z in (0 : ℝ)..1, (partialDerivScalar f (vec3 x y z) 2) ^ 2 := by
    intro x
    have hc1 : Continuous (fun y => C * ∫ z in (0 : ℝ)..1, (f (vec3 x y z)) ^ 2) :=
      continuous_const.mul (continuous_int1' (G := fun y z => (f (vec3 x y z)) ^ 2)
        ((hf.continuous.comp (cont_vec3_yz' x)).pow 2))
    have hc2 : Continuous (fun y => ∫ z in (0 : ℝ)..1, (partialDerivScalar f (vec3 x y z) 2) ^ 2) :=
      continuous_int1' (G := fun y z => (partialDerivScalar f (vec3 x y z) 2) ^ 2)
        ((hc_p2.comp (cont_vec3_yz' x)).pow 2)
    have hmono := intervalIntegral.integral_mono_on (μ := volume) (by norm_num : (0 : ℝ) ≤ 1)
      (hc1.intervalIntegrable (μ := volume) 0 1) (hc2.intervalIntegrable (μ := volume) 0 1)
      (fun y _ => h_slice x y)
    rwa [intervalIntegral.integral_const_mul C] at hmono
  have hc_x1 : Continuous (fun x => C * ∫ y in (0 : ℝ)..1, ∫ z in (0 : ℝ)..1, (f (vec3 x y z)) ^ 2) :=
    continuous_const.mul (continuous_int2' (G := fun x y z => (f (vec3 x y z)) ^ 2) hF_sq)
  have hc_x2 : Continuous (fun x => ∫ y in (0 : ℝ)..1, ∫ z in (0 : ℝ)..1, (partialDerivScalar f (vec3 x y z) 2) ^ 2) :=
    continuous_int2' (G := fun x y z => (partialDerivScalar f (vec3 x y z) 2) ^ 2) hP2_sq
  have h_x_int := intervalIntegral.integral_mono_on (μ := volume) (by norm_num : (0 : ℝ) ≤ 1)
    (hc_x1.intervalIntegrable (μ := volume) 0 1) (hc_x2.intervalIntegrable (μ := volume) 0 1)
    (fun x _ => h_y_int x)
  rw [intervalIntegral.integral_const_mul C] at h_x_int
  have hnn0 : 0 ≤ torusIntegral (fun x => (partialDerivScalar f x 0) ^ 2) :=
    torusIntegral_nonneg (hc_p0.pow 2) (fun _ => sq_nonneg _)
  have hnn1 : 0 ≤ torusIntegral (fun x => (partialDerivScalar f x 1) ^ 2) :=
    torusIntegral_nonneg (hc_p1.pow 2) (fun _ => sq_nonneg _)
  have hc_p0_sq : Continuous (fun x => (partialDerivScalar f x 0) ^ 2) := hc_p0.pow 2
  have hc_p1_sq : Continuous (fun x => (partialDerivScalar f x 1) ^ 2) := hc_p1.pow 2
  have hc_p2_sq : Continuous (fun x => (partialDerivScalar f x 2) ^ 2) := hc_p2.pow 2
  rw [torusIntegral_add3 hc_p0_sq hc_p1_sq hc_p2_sq]
  change C * torusIntegral (fun x => (f x) ^ 2) ≤ _
  have h_le2 : C * torusIntegral (fun x => (f x) ^ 2) ≤
      torusIntegral (fun x => (partialDerivScalar f x 2) ^ 2) := h_x_int
  linarith

-- ============================================================================
-- SECTION 3: SHARP ANALYTICAL LEMMA 4 (`8π² Z ≤ P`) & SHARP EXPONENTIAL DECAY
-- ============================================================================

/-- **SHARP ANALYTICAL LEMMA 4 (Optimal Bernstein–Poincaré Spectral Coercivity on `𝕋³`):**
    Upgrades Milestone 4's coercivity constant from `16` to the exact first Laplacian
    eigenvalue `8π²` directly from `IsPeriodicClassicalNS3D_C3`:
      `8π² * Z(t) ≤ P(t)`  and  `ν * (8π² * Z(t)) ≤ ν * P(t)` (`0 sorryAx`). -/
theorem sharp_analytical_lemma4_bernstein_poincare_vorticity
    {u : ℝ → R3 → R3} {p : ℝ → R3 → ℝ} {ν : ℝ}
    (hns : IsPeriodicClassicalNS3D_C3 u p ν) {t : ℝ} (ht : t ≥ 0) :
    8 * Real.pi ^ 2 * enstrophy u t ≤ palinstrophy3D (u t) ∧
    ν * (8 * Real.pi ^ 2 * enstrophy u t) ≤ ν * palinstrophy3D (u t) := by
  have hu3 : ContDiff ℝ 3 (u t) := hns.h_u_c3_global t ht
  have hu1 : ContDiff ℝ 1 (u t) := contDiff_one_of_two4 (contDiff_two_of_three4 hu3)
  have hw1 : ContDiff ℝ 1 (curl3D (u t)) := contDiff_one_of_two4 (contDiff_two_curl3D hu3)
  have hpu : IsPeriodic3D (u t) := hns.h_u_periodic t ht
  have hpw : IsPeriodic3D (curl3D (u t)) := hpu.curl3D (hu1.differentiable (by simp))
  have hmean : ∀ comp : Fin 3, torusIntegral (fun x => curl3D (u t) x comp) = 0 :=
    fun comp => vorticity_mean_zero hu1 hpu comp
  have hwirt := wirtinger_3d_torus_vec hw1 hpw hmean
  have h8pi : 8 * Real.pi ^ 2 * enstrophy u t ≤ palinstrophy3D (u t) := by
    unfold enstrophy palinstrophy3D
    linarith
  have h_l4 := GarryNavierStokesMathlib.lemma4_bernstein_poincare_spectral_coercivity
    ν (palinstrophy3D (u t)) (8 * Real.pi ^ 2) (enstrophy u t) (ν * palinstrophy3D (u t))
    (le_of_lt hns.h_nu_pos) h8pi rfl
  exact ⟨h8pi, h_l4⟩

/-- **SHARP Global Exponential Kinetic Energy Decay on `𝕋³` (`E(T) ≤ E(0) exp(-8π² ν T)`):**
    Optimal decay rate matching the exact first eigenvalue `4π²` of `-Δ` on `𝕋³` (`0 sorryAx`). -/
theorem sharp_global_exponential_energy_decay_torus3D
    {u : ℝ → R3 → R3} {p : ℝ → R3 → ℝ} {ν : ℝ}
    (hns : IsPeriodicClassicalNS3D_C3 u p ν)
    (hmean0 : ∀ comp : Fin 3, torusIntegral (fun x => u 0 x comp) = 0)
    {T : ℝ} (hT : 0 ≤ T) :
    kineticEnergy u T ≤ kineticEnergy u 0 * Real.exp (-(8 * Real.pi ^ 2 * ν) * T) := by
  let lam : ℝ := 8 * Real.pi ^ 2 * ν
  let h : ℝ → ℝ := fun s => Real.exp (lam * s) * kineticEnergy u s
  let h' : ℝ → ℝ := fun s =>
    Real.exp (lam * s) * (lam * kineticEnergy u s - ν * torusIntegral (gradNormSq3D (u s)))
  have h_deriv : ∀ s : ℝ, 0 ≤ s → HasDerivAt h (h' s) s := by
    intro s hs
    have hexp : HasDerivAt (fun r : ℝ => Real.exp (lam * r)) (Real.exp (lam * s) * lam) s := by
      have hlin : HasDerivAt (fun r : ℝ => lam * r) lam s := by
        have h1 : HasDerivAt (fun r : ℝ => lam * r) (lam * 1) s := (hasDerivAt_id s).const_mul lam
        rwa [mul_one] at h1
      exact (Real.hasDerivAt_exp (lam * s)).comp s hlin
    have hprod := hexp.mul (hasDerivAt_kineticEnergy_leray hns hs).1
    have heq_d : Real.exp (lam * s) * lam * kineticEnergy u s +
        Real.exp (lam * s) * (-ν * torusIntegral (gradNormSq3D (u s))) = h' s := by
      dsimp only [h']; ring
    rw [heq_d] at hprod
    exact hprod
  have h_nonpos : ∀ s : ℝ, 0 ≤ s → h' s ≤ 0 := by
    intro s hs
    have hmeans : ∀ comp : Fin 3, torusIntegral (fun x => u s x comp) = 0 := fun comp => by
      rw [momentum_conservation_torus3D hns hs comp, hmean0 comp]
    have hu1 : ContDiff ℝ 1 (u s) := contDiff_one_of_two4 (contDiff_two_of_three4 (hns.h_u_c3_global s hs))
    have hwirt := wirtinger_3d_torus_vec hu1 (hns.h_u_periodic s hs) hmeans
    have h8E : 8 * Real.pi ^ 2 * kineticEnergy u s ≤ torusIntegral (gradNormSq3D (u s)) := by
      unfold kineticEnergy; linarith
    have hbr : lam * kineticEnergy u s - ν * torusIntegral (gradNormSq3D (u s)) ≤ 0 := by
      dsimp only [lam]; nlinarith [hns.h_nu_pos, h8E]
    exact mul_nonpos_of_nonneg_of_nonpos (le_of_lt (Real.exp_pos _)) hbr
  have hu_cont : Continuous (fun q : ℝ × R3 => u q.1 q.2) :=
    (contDiff_iff_contDiffAt.mpr hns.h_u_c2_spacetime).continuous
  have hu0 : Continuous (fun q : ℝ × R3 => u q.1 q.2 0) := (continuous_apply 0).comp hu_cont
  have hu1 : Continuous (fun q : ℝ × R3 => u q.1 q.2 1) := (continuous_apply 1).comp hu_cont
  have hu2 : Continuous (fun q : ℝ × R3 => u q.1 q.2 2) := (continuous_apply 2).comp hu_cont
  have h_joint_E : Continuous (fun q : ℝ × R3 => dot3D (u q.1 q.2) (u q.1 q.2)) := by
    unfold dot3D; exact ((hu0.mul hu0).add (hu1.mul hu1)).add (hu2.mul hu2)
  have hE_cont : Continuous (kineticEnergy u) := by
    unfold kineticEnergy
    exact continuous_const.mul
      (continuous_torusIntegral_of_joint_continuous (G := fun s x => dot3D (u s x) (u s x)) h_joint_E)
  have h_joint_grad : Continuous (fun q : ℝ × R3 => gradNormSq3D (u q.1) q.2) := by
    have hc_sp : ∀ c i : Fin 3, Continuous (fun q : ℝ × R3 =>
        partialDerivScalar (fun y => u q.1 y c) q.2 i) := by
      intro c i
      have hFc : ∀ q : ℝ × R3, ContDiffAt ℝ 2 (fun r : ℝ × R3 => u r.1 r.2 c) q :=
        fun q => contDiffAt_pi.mp (hns.h_u_c2_spacetime q) c
      have hfun : (fun q : ℝ × R3 => partialDerivScalar (fun y => u q.1 y c) q.2 i) =
          (fun q : ℝ × R3 => fderiv ℝ (fun r : ℝ × R3 => u r.1 r.2 c) q ((0 : ℝ), basisVec i)) := by
        funext q; exact spacePartial_eq_fderiv_prod (fun r => u r.1 r.2 c) hFc q.1 q.2 i
      rw [hfun]
      have hcd1 : ContDiff ℝ 1 (fderiv ℝ (fun r : ℝ × R3 => u r.1 r.2 c)) :=
        (contDiff_iff_contDiffAt.mpr hFc).fderiv_right (by simp [one_add_one_eq_two])
      exact (ContinuousLinearMap.apply ℝ ℝ ((0 : ℝ), basisVec i)).continuous.comp hcd1.continuous
    unfold gradNormSq3D
    exact (((((((((hc_sp 0 0).pow 2).add ((hc_sp 0 1).pow 2)).add ((hc_sp 0 2).pow 2)).add
      ((hc_sp 1 0).pow 2)).add ((hc_sp 1 1).pow 2)).add ((hc_sp 1 2).pow 2)).add
      ((hc_sp 2 0).pow 2)).add ((hc_sp 2 1).pow 2)).add ((hc_sp 2 2).pow 2)
  have h_grad_cont : Continuous (fun s => torusIntegral (gradNormSq3D (u s))) :=
    continuous_torusIntegral_of_joint_continuous (G := fun s x => gradNormSq3D (u s) x) h_joint_grad
  have hh'_cont : Continuous h' :=
    (Real.continuous_exp.comp (continuous_const.mul continuous_id)).mul
      ((continuous_const.mul hE_cont).sub (continuous_const.mul h_grad_cont))
  have h_ftc := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (a := (0 : ℝ)) (b := T) (f := h) (f' := h')
    (fun s hs => by rw [Set.uIcc_of_le hT] at hs; exact h_deriv s hs.1)
    (hh'_cont.intervalIntegrable (μ := volume) 0 T)
  have h_int_nonpos : (∫ s in (0 : ℝ)..T, h' s) ≤ 0 := by
    have hnn : 0 ≤ ∫ s in (0 : ℝ)..T, (-h' s) :=
      intervalIntegral.integral_nonneg hT fun s hs => by linarith [h_nonpos s hs.1]
    rw [intervalIntegral.integral_neg] at hnn
    linarith
  have hhT_le : h T ≤ kineticEnergy u 0 := by
    have h0_eq : h 0 = kineticEnergy u 0 := by dsimp only [h]; simp
    linarith
  have hexp_pos : 0 < Real.exp (-lam * T) := Real.exp_pos _
  have hmul := mul_le_mul_of_nonneg_right hhT_le (le_of_lt hexp_pos)
  have hcancel : h T * Real.exp (-lam * T) = kineticEnergy u T := by
    dsimp only [h]
    have hz : lam * T + -lam * T = 0 := by ring
    calc Real.exp (lam * T) * kineticEnergy u T * Real.exp (-lam * T)
        = (Real.exp (lam * T) * Real.exp (-lam * T)) * kineticEnergy u T := by ring
      _ = Real.exp (lam * T + -lam * T) * kineticEnergy u T := by rw [← Real.exp_add]
      _ = Real.exp 0 * kineticEnergy u T := by rw [hz]
      _ = kineticEnergy u T := by simp
  dsimp only [lam] at hmul hcancel
  linarith

-- ============================================================================
-- SECTION 4: TRUE 3D FOURIER COEFFICIENTS & SPECTRAL PDE IDENTITIES ON `𝕋³`
-- ============================================================================

/-- 1D complex Fourier character `e_n(t) = exp(-2π i n t)`. -/
noncomputable def fourierChar1D (n : ℤ) (t : ℝ) : ℂ :=
  Complex.exp (-2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) * (t : ℂ))

/-- True 3D Fourier coefficient `f̂(k) = ∫_{𝕋³} e^{-2π i k·x} f(x) dx` for `k ∈ ℤ³`. -/
noncomputable def fourierCoeff3D (f : R3 → ℝ) (k : Fin 3 → ℤ) : ℂ :=
  ∫ x in (0 : ℝ)..1, ∫ y in (0 : ℝ)..1, ∫ z in (0 : ℝ)..1,
    fourierChar1D (k 0) x * fourierChar1D (k 1) y * fourierChar1D (k 2) z * (f (vec3 x y z) : ℂ)

private theorem continuous_fourierChar1D (n : ℤ) : Continuous (fourierChar1D n) :=
  Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal)

private theorem fourierChar1D_one (n : ℤ) : fourierChar1D n 1 = 1 := by
  unfold fourierChar1D
  have h : -2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) * ((1 : ℝ) : ℂ) =
      ((-n : ℤ) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by
    push_cast; ring
  rw [h]
  exact Complex.exp_int_mul_two_pi_mul_I (-n)

private theorem fourierChar1D_zero (n : ℤ) : fourierChar1D n 0 = 1 := by
  unfold fourierChar1D; simp

private theorem hasDerivAt_fourierChar1D (n : ℤ) (t : ℝ) :
    HasDerivAt (fourierChar1D n)
      ((-2 * (Real.pi : ℂ) * Complex.I * (n : ℂ)) * fourierChar1D n t) t := by
  let c : ℂ := -2 * (Real.pi : ℂ) * Complex.I * (n : ℂ)
  have hlin : HasDerivAt (fun s : ℝ => c * (s : ℂ)) c t := by
    have h1 : HasDerivAt (fun s : ℝ => (s : ℂ)) (1 : ℂ) t := by
      simpa using (hasDerivAt_id t).ofReal_comp
    have h2 := h1.const_mul c
    rwa [mul_one] at h2
  have hexp : HasDerivAt (fun s : ℝ => Complex.exp (c * (s : ℂ)))
      (Complex.exp (c * (t : ℂ)) * c) t := hlin.cexp
  have heq : Complex.exp (c * (t : ℂ)) * c = c * fourierChar1D n t := by
    unfold fourierChar1D; dsimp only [c]; ring
  rw [heq] at hexp
  exact hexp

/-- 1D complex Fourier integration by parts for periodic `C¹` functions. -/
private theorem complex_ibp_fourierChar1D
    {φ φ' : ℝ → ℝ} (hφ : Continuous φ) (hφ' : Continuous φ')
    (hderiv : ∀ t : ℝ, HasDerivAt φ (φ' t) t) (hper : φ 1 = φ 0) (n : ℤ) :
    (∫ t in (0 : ℝ)..1, fourierChar1D n t * (φ' t : ℂ)) =
      (2 * (Real.pi : ℂ) * Complex.I * (n : ℂ)) *
        (∫ t in (0 : ℝ)..1, fourierChar1D n t * (φ t : ℂ)) := by
  let c : ℂ := 2 * (Real.pi : ℂ) * Complex.I * (n : ℂ)
  have hprod_deriv : ∀ t : ℝ,
      HasDerivAt (fun s => fourierChar1D n s * (φ s : ℂ))
        ((-c) * (fourierChar1D n t * (φ t : ℂ)) + fourierChar1D n t * (φ' t : ℂ)) t := by
    intro t
    have h1 := hasDerivAt_fourierChar1D n t
    have h2 : HasDerivAt (fun s => (φ s : ℂ)) (φ' t : ℂ) t := (hderiv t).ofReal_comp
    have hp := h1.mul h2
    have hce : (-2 * (Real.pi : ℂ) * Complex.I * (n : ℂ)) * fourierChar1D n t * (φ t : ℂ) +
        fourierChar1D n t * (φ' t : ℂ) =
        (-c) * (fourierChar1D n t * (φ t : ℂ)) + fourierChar1D n t * (φ' t : ℂ) := by
      dsimp only [c]; ring
    rw [hce] at hp
    exact hp
  have hc1 : Continuous (fun t => (-c) * (fourierChar1D n t * (φ t : ℂ))) :=
    continuous_const.mul ((continuous_fourierChar1D n).mul (Complex.continuous_ofReal.comp hφ))
  have hc2 : Continuous (fun t => fourierChar1D n t * (φ' t : ℂ)) :=
    (continuous_fourierChar1D n).mul (Complex.continuous_ofReal.comp hφ')
  have hc12 : Continuous (fun t => (-c) * (fourierChar1D n t * (φ t : ℂ)) + fourierChar1D n t * (φ' t : ℂ)) :=
    hc1.add hc2
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (a := (0 : ℝ)) (b := 1)
    (f := fun s => fourierChar1D n s * (φ s : ℂ))
    (f' := fun t => (-c) * (fourierChar1D n t * (φ t : ℂ)) + fourierChar1D n t * (φ' t : ℂ))
    (fun t _ => hprod_deriv t) (hc12.intervalIntegrable (μ := volume) 0 1)
  rw [fourierChar1D_one, fourierChar1D_zero, hper, sub_self] at hftc
  rw [intervalIntegral.integral_add (hc1.intervalIntegrable (μ := volume) 0 1)
        (hc2.intervalIntegrable (μ := volume) 0 1),
      intervalIntegral.integral_const_mul (-c)] at hftc
  exact eq_of_sub_eq_zero (by linear_combination hftc)

private theorem complex_integral_swap_unit {g : ℝ → ℝ → ℂ}
    (hg : Continuous (fun p : ℝ × ℝ => g p.1 p.2)) :
    (∫ a in (0 : ℝ)..1, ∫ b in (0 : ℝ)..1, g a b) =
    ∫ b in (0 : ℝ)..1, ∫ a in (0 : ℝ)..1, g a b := by
  simp_rw [int1_eq_uMeas1']
  have hint : Integrable (fun p : ℝ × ℝ => g p.1 p.2) uMeas2' := by
    rw [uMeas2'_eq_restrict]
    exact hg.continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)
  exact MeasureTheory.integral_integral_swap hint

private theorem fourierCoeff3D_eq_uMeas3' {f : R3 → ℝ} (hf : Continuous f) (k : Fin 3 → ℤ) :
    fourierCoeff3D f k =
      ∫ q : ℝ × (ℝ × ℝ),
        fourierChar1D (k 0) q.1 * fourierChar1D (k 1) q.2.1 * fourierChar1D (k 2) q.2.2 *
          (f (vec3 q.1 q.2.1 q.2.2) : ℂ) ∂uMeas3' := by
  unfold fourierCoeff3D
  simp_rw [int1_eq_uMeas1']
  have hc3 : Continuous (fun q : ℝ × (ℝ × ℝ) =>
      fourierChar1D (k 0) q.1 * fourierChar1D (k 1) q.2.1 * fourierChar1D (k 2) q.2.2 *
        (f (vec3 q.1 q.2.1 q.2.2) : ℂ)) :=
    ((((continuous_fourierChar1D (k 0)).comp continuous_fst).mul
      ((continuous_fourierChar1D (k 1)).comp (continuous_fst.comp continuous_snd))).mul
      ((continuous_fourierChar1D (k 2)).comp (continuous_snd.comp continuous_snd))).mul
      (Complex.continuous_ofReal.comp (hf.comp cont_vec3_xyz'))
  have hint3 : Integrable (fun q : ℝ × (ℝ × ℝ) =>
      fourierChar1D (k 0) q.1 * fourierChar1D (k 1) q.2.1 * fourierChar1D (k 2) q.2.2 *
        (f (vec3 q.1 q.2.1 q.2.2) : ℂ)) uMeas3' := by
    rw [uMeas3'_eq_restrict]
    exact hc3.continuousOn.integrableOn_compact (isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc))
  have h_inner : ∀ x : ℝ,
      (∫ y, (∫ z, fourierChar1D (k 0) x * fourierChar1D (k 1) y * fourierChar1D (k 2) z *
          (f (vec3 x y z) : ℂ) ∂uMeas1') ∂uMeas1') =
      ∫ p : ℝ × ℝ, fourierChar1D (k 0) x * fourierChar1D (k 1) p.1 * fourierChar1D (k 2) p.2 *
        (f (vec3 x p.1 p.2) : ℂ) ∂uMeas2' := fun x => by
    have hc2 : Continuous (fun p : ℝ × ℝ =>
        fourierChar1D (k 0) x * fourierChar1D (k 1) p.1 * fourierChar1D (k 2) p.2 *
          (f (vec3 x p.1 p.2) : ℂ)) :=
      ((continuous_const.mul ((continuous_fourierChar1D (k 1)).comp continuous_fst)).mul
        ((continuous_fourierChar1D (k 2)).comp continuous_snd)).mul
        (Complex.continuous_ofReal.comp (hf.comp (cont_vec3_yz' x)))
    have hint2 : Integrable (fun p : ℝ × ℝ =>
        fourierChar1D (k 0) x * fourierChar1D (k 1) p.1 * fourierChar1D (k 2) p.2 *
          (f (vec3 x p.1 p.2) : ℂ)) uMeas2' := by
      rw [uMeas2'_eq_restrict]
      exact hc2.continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)
    exact (MeasureTheory.integral_prod _ hint2).symm
  simp_rw [h_inner]
  exact (MeasureTheory.integral_prod _ hint3).symm

/-- **3D Spectral Differentiation Law:**
    For any `C¹` periodic scalar field `f` on `𝕋³`, wavevector `k ∈ ℤ³`, and axis `j ∈ {0, 1, 2}`:
      `fourierCoeff3D (∂_j f) k = (2π i k_j) * fourierCoeff3D f k` (`0 sorryAx`). -/
private theorem complex_integral_factor_first (a b : ℂ) (φ ψ : ℝ → ℂ) :
    (∫ t in (0 : ℝ)..1, φ t * a * b * ψ t) = (a * b) * ∫ t in (0 : ℝ)..1, φ t * ψ t := by
  have heq : (fun t => φ t * a * b * ψ t) = (fun t => (a * b) * (φ t * ψ t)) := by
    funext t; ring
  rw [heq, intervalIntegral.integral_const_mul]

private theorem complex_integral_factor_mid (a b : ℂ) (φ ψ : ℝ → ℂ) :
    (∫ t in (0 : ℝ)..1, a * φ t * b * ψ t) = (a * b) * ∫ t in (0 : ℝ)..1, φ t * ψ t := by
  have heq : (fun t => a * φ t * b * ψ t) = (fun t => (a * b) * (φ t * ψ t)) := by
    funext t; ring
  rw [heq, intervalIntegral.integral_const_mul]

private theorem complex_integral_factor_last (a b : ℂ) (φ ψ : ℝ → ℂ) :
    (∫ t in (0 : ℝ)..1, a * b * φ t * ψ t) = (a * b) * ∫ t in (0 : ℝ)..1, φ t * ψ t := by
  have heq : (fun t => a * b * φ t * ψ t) = (fun t => (a * b) * (φ t * ψ t)) := by
    funext t; ring
  rw [heq, intervalIntegral.integral_const_mul]

private theorem fourierCoeff3D_partialDeriv_0
    {f : R3 → ℝ} (hf : ContDiff ℝ 1 f) (hpf : IsPeriodic3D f) (k : Fin 3 → ℤ) :
    fourierCoeff3D (fun x => partialDerivScalar f x 0) k =
      (2 * (Real.pi : ℂ) * Complex.I * (k 0 : ℂ)) * fourierCoeff3D f k := by
  have hdiff : Differentiable ℝ f := hf.differentiable (by simp)
  have hc0 : Continuous (fun x => partialDerivScalar f x 0) :=
    continuous_partialDerivScalar_of_contDiff hf 0
  have hc3_df : Continuous (fun q : ℝ × (ℝ × ℝ) =>
      fourierChar1D (k 0) q.1 * fourierChar1D (k 1) q.2.1 * fourierChar1D (k 2) q.2.2 *
        (partialDerivScalar f (vec3 q.1 q.2.1 q.2.2) 0 : ℂ)) :=
    ((((continuous_fourierChar1D (k 0)).comp continuous_fst).mul
      ((continuous_fourierChar1D (k 1)).comp (continuous_fst.comp continuous_snd))).mul
      ((continuous_fourierChar1D (k 2)).comp (continuous_snd.comp continuous_snd))).mul
      (Complex.continuous_ofReal.comp (hc0.comp cont_vec3_xyz'))
  have hc3_f : Continuous (fun q : ℝ × (ℝ × ℝ) =>
      fourierChar1D (k 0) q.1 * fourierChar1D (k 1) q.2.1 * fourierChar1D (k 2) q.2.2 *
        (f (vec3 q.1 q.2.1 q.2.2) : ℂ)) :=
    ((((continuous_fourierChar1D (k 0)).comp continuous_fst).mul
      ((continuous_fourierChar1D (k 1)).comp (continuous_fst.comp continuous_snd))).mul
      ((continuous_fourierChar1D (k 2)).comp (continuous_snd.comp continuous_snd))).mul
      (Complex.continuous_ofReal.comp (hf.continuous.comp cont_vec3_xyz'))
  have hint_df : Integrable (fun q : ℝ × (ℝ × ℝ) =>
      fourierChar1D (k 0) q.1 * fourierChar1D (k 1) q.2.1 * fourierChar1D (k 2) q.2.2 *
        (partialDerivScalar f (vec3 q.1 q.2.1 q.2.2) 0 : ℂ)) uMeas3' := by
    rw [uMeas3'_eq_restrict]
    exact hc3_df.continuousOn.integrableOn_compact (isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc))
  have hint_f : Integrable (fun q : ℝ × (ℝ × ℝ) =>
      fourierChar1D (k 0) q.1 * fourierChar1D (k 1) q.2.1 * fourierChar1D (k 2) q.2.2 *
        (f (vec3 q.1 q.2.1 q.2.2) : ℂ)) uMeas3' := by
    rw [uMeas3'_eq_restrict]
    exact hc3_f.continuousOn.integrableOn_compact (isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc))
  have h_lhs : fourierCoeff3D (fun x => partialDerivScalar f x 0) k =
      ∫ p : ℝ × ℝ, (∫ x in (0 : ℝ)..1, fourierChar1D (k 0) x * fourierChar1D (k 1) p.1 *
        fourierChar1D (k 2) p.2 * (partialDerivScalar f (vec3 x p.1 p.2) 0 : ℂ)) ∂uMeas2' := by
    rw [fourierCoeff3D_eq_uMeas3' hc0 k, MeasureTheory.integral_prod _ hint_df,
        MeasureTheory.integral_integral_swap hint_df]
    simp_rw [← int1_eq_uMeas1']
  have h_rhs : fourierCoeff3D f k =
      ∫ p : ℝ × ℝ, (∫ x in (0 : ℝ)..1, fourierChar1D (k 0) x * fourierChar1D (k 1) p.1 *
        fourierChar1D (k 2) p.2 * (f (vec3 x p.1 p.2) : ℂ)) ∂uMeas2' := by
    rw [fourierCoeff3D_eq_uMeas3' hf.continuous k, MeasureTheory.integral_prod _ hint_f,
        MeasureTheory.integral_integral_swap hint_f]
    simp_rw [← int1_eq_uMeas1']
  have h_inner : ∀ p : ℝ × ℝ,
      (∫ x in (0 : ℝ)..1, fourierChar1D (k 0) x * fourierChar1D (k 1) p.1 *
        fourierChar1D (k 2) p.2 * (partialDerivScalar f (vec3 x p.1 p.2) 0 : ℂ)) =
      (2 * (Real.pi : ℂ) * Complex.I * (k 0 : ℂ)) *
        (∫ x in (0 : ℝ)..1, fourierChar1D (k 0) x * fourierChar1D (k 1) p.1 *
          fourierChar1D (k 2) p.2 * (f (vec3 x p.1 p.2) : ℂ)) := by
    intro p
    rw [complex_integral_factor_first, complex_integral_factor_first]
    have hcx : Continuous (fun x : ℝ => vec3 x p.1 p.2) :=
      continuous_pi fun m => match m with
        | ⟨0, _⟩ => continuous_id | ⟨1, _⟩ => continuous_const | ⟨2, _⟩ => continuous_const
    have hcf : Continuous (fun x : ℝ => f (vec3 x p.1 p.2)) := hf.continuous.comp hcx
    have hcdf : Continuous (fun x : ℝ => partialDerivScalar f (vec3 x p.1 p.2) 0) := hc0.comp hcx
    have hibp := complex_ibp_fourierChar1D hcf hcdf
      (fun x => (hdiff (vec3 x p.1 p.2)).hasFDerivAt.comp_hasDerivAt x (hda_vec3_0' p.1 p.2 x))
      (by have h := vec3_add_b0' 0 p.1 p.2; simp only [zero_add] at h; rw [h, hpf (vec3 0 p.1 p.2) 0])
      (k 0)
    rw [hibp]; ring
  rw [h_lhs, h_rhs]
  simp_rw [h_inner, MeasureTheory.integral_const_mul]

private theorem fourierCoeff3D_partialDeriv_1
    {f : R3 → ℝ} (hf : ContDiff ℝ 1 f) (hpf : IsPeriodic3D f) (k : Fin 3 → ℤ) :
    fourierCoeff3D (fun x => partialDerivScalar f x 1) k =
      (2 * (Real.pi : ℂ) * Complex.I * (k 1 : ℂ)) * fourierCoeff3D f k := by
  have hdiff : Differentiable ℝ f := hf.differentiable (by simp)
  have hc1 : Continuous (fun x => partialDerivScalar f x 1) :=
    continuous_partialDerivScalar_of_contDiff hf 1
  have h_inner_z : ∀ x z : ℝ,
      (∫ y in (0 : ℝ)..1, fourierChar1D (k 0) x * fourierChar1D (k 1) y *
        fourierChar1D (k 2) z * (partialDerivScalar f (vec3 x y z) 1 : ℂ)) =
      (2 * (Real.pi : ℂ) * Complex.I * (k 1 : ℂ)) *
        (∫ y in (0 : ℝ)..1, fourierChar1D (k 0) x * fourierChar1D (k 1) y *
          fourierChar1D (k 2) z * (f (vec3 x y z) : ℂ)) := by
    intro x z
    rw [complex_integral_factor_mid, complex_integral_factor_mid]
    have hcy : Continuous (fun y : ℝ => vec3 x y z) :=
      continuous_pi fun m => match m with
        | ⟨0, _⟩ => continuous_const | ⟨1, _⟩ => continuous_id | ⟨2, _⟩ => continuous_const
    have hcf : Continuous (fun y : ℝ => f (vec3 x y z)) := hf.continuous.comp hcy
    have hcdf : Continuous (fun y : ℝ => partialDerivScalar f (vec3 x y z) 1) := hc1.comp hcy
    have hibp := complex_ibp_fourierChar1D hcf hcdf
      (fun y => (hdiff (vec3 x y z)).hasFDerivAt.comp_hasDerivAt y (hda_vec3_1' x z y))
      (by have h := vec3_add_b1' x 0 z; simp only [zero_add] at h; rw [h, hpf (vec3 x 0 z) 1])
      (k 1)
    rw [hibp]; ring
  have h_slice_x : ∀ x : ℝ,
      (∫ y in (0 : ℝ)..1, ∫ z in (0 : ℝ)..1, fourierChar1D (k 0) x * fourierChar1D (k 1) y *
        fourierChar1D (k 2) z * (partialDerivScalar f (vec3 x y z) 1 : ℂ)) =
      (2 * (Real.pi : ℂ) * Complex.I * (k 1 : ℂ)) *
        (∫ y in (0 : ℝ)..1, ∫ z in (0 : ℝ)..1, fourierChar1D (k 0) x * fourierChar1D (k 1) y *
          fourierChar1D (k 2) z * (f (vec3 x y z) : ℂ)) := by
    intro x
    have hcyz_df : Continuous (fun p : ℝ × ℝ =>
        fourierChar1D (k 0) x * fourierChar1D (k 1) p.1 * fourierChar1D (k 2) p.2 *
          (partialDerivScalar f (vec3 x p.1 p.2) 1 : ℂ)) :=
      ((continuous_const.mul ((continuous_fourierChar1D (k 1)).comp continuous_fst)).mul
        ((continuous_fourierChar1D (k 2)).comp continuous_snd)).mul
        (Complex.continuous_ofReal.comp (hc1.comp (cont_vec3_yz' x)))
    have hcyz_f : Continuous (fun p : ℝ × ℝ =>
        fourierChar1D (k 0) x * fourierChar1D (k 1) p.1 * fourierChar1D (k 2) p.2 *
          (f (vec3 x p.1 p.2) : ℂ)) :=
      ((continuous_const.mul ((continuous_fourierChar1D (k 1)).comp continuous_fst)).mul
        ((continuous_fourierChar1D (k 2)).comp continuous_snd)).mul
        (Complex.continuous_ofReal.comp (hf.continuous.comp (cont_vec3_yz' x)))
    have hswap1 := complex_integral_swap_unit
      (g := fun y z => fourierChar1D (k 0) x * fourierChar1D (k 1) y * fourierChar1D (k 2) z *
        (partialDerivScalar f (vec3 x y z) 1 : ℂ)) hcyz_df
    have hswap2 := complex_integral_swap_unit
      (g := fun y z => fourierChar1D (k 0) x * fourierChar1D (k 1) y * fourierChar1D (k 2) z *
        (f (vec3 x y z) : ℂ)) hcyz_f
    rw [hswap1, hswap2]
    simp_rw [h_inner_z, intervalIntegral.integral_const_mul]
  unfold fourierCoeff3D
  simp_rw [h_slice_x, intervalIntegral.integral_const_mul]

private theorem fourierCoeff3D_partialDeriv_2
    {f : R3 → ℝ} (hf : ContDiff ℝ 1 f) (hpf : IsPeriodic3D f) (k : Fin 3 → ℤ) :
    fourierCoeff3D (fun x => partialDerivScalar f x 2) k =
      (2 * (Real.pi : ℂ) * Complex.I * (k 2 : ℂ)) * fourierCoeff3D f k := by
  have hdiff : Differentiable ℝ f := hf.differentiable (by simp)
  have hc2 : Continuous (fun x => partialDerivScalar f x 2) :=
    continuous_partialDerivScalar_of_contDiff hf 2
  have h_inner : ∀ x y : ℝ,
      (∫ z in (0 : ℝ)..1, fourierChar1D (k 0) x * fourierChar1D (k 1) y *
        fourierChar1D (k 2) z * (partialDerivScalar f (vec3 x y z) 2 : ℂ)) =
      (2 * (Real.pi : ℂ) * Complex.I * (k 2 : ℂ)) *
        (∫ z in (0 : ℝ)..1, fourierChar1D (k 0) x * fourierChar1D (k 1) y *
          fourierChar1D (k 2) z * (f (vec3 x y z) : ℂ)) := by
    intro x y
    rw [complex_integral_factor_last, complex_integral_factor_last]
    have hcf : Continuous (fun z : ℝ => f (vec3 x y z)) := hf.continuous.comp (cont_vec3_z' x y)
    have hcdf : Continuous (fun z : ℝ => partialDerivScalar f (vec3 x y z) 2) := hc2.comp (cont_vec3_z' x y)
    have hibp := complex_ibp_fourierChar1D hcf hcdf
      (fun z => (hdiff (vec3 x y z)).hasFDerivAt.comp_hasDerivAt z (hda_vec3_2' x y z))
      (by have h := vec3_add_b2' x y 0; simp only [zero_add] at h; rw [h, hpf (vec3 x y 0) 2])
      (k 2)
    rw [hibp]; ring
  unfold fourierCoeff3D
  simp_rw [h_inner, intervalIntegral.integral_const_mul]

theorem fourierCoeff3D_partialDeriv
    {f : R3 → ℝ} (hf : ContDiff ℝ 1 f) (hpf : IsPeriodic3D f) (k : Fin 3 → ℤ) (j : Fin 3) :
    fourierCoeff3D (fun x => partialDerivScalar f x j) k =
      (2 * (Real.pi : ℂ) * Complex.I * (k j : ℂ)) * fourierCoeff3D f k := by
  fin_cases j
  · exact fourierCoeff3D_partialDeriv_0 hf hpf k
  · exact fourierCoeff3D_partialDeriv_1 hf hpf k
  · exact fourierCoeff3D_partialDeriv_2 hf hpf k

theorem fourierCoeff3D_add {f g : R3 → ℝ} (hf : Continuous f) (hg : Continuous g) (k : Fin 3 → ℤ) :
    fourierCoeff3D (fun x => f x + g x) k = fourierCoeff3D f k + fourierCoeff3D g k := by
  have hfg : Continuous (fun x => f x + g x) := hf.add hg
  rw [fourierCoeff3D_eq_uMeas3' hfg k, fourierCoeff3D_eq_uMeas3' hf k, fourierCoeff3D_eq_uMeas3' hg k]
  have hint_f : Integrable (fun q : ℝ × (ℝ × ℝ) =>
      fourierChar1D (k 0) q.1 * fourierChar1D (k 1) q.2.1 * fourierChar1D (k 2) q.2.2 *
        (f (vec3 q.1 q.2.1 q.2.2) : ℂ)) uMeas3' := by
    rw [uMeas3'_eq_restrict]
    exact (((((continuous_fourierChar1D (k 0)).comp continuous_fst).mul
      ((continuous_fourierChar1D (k 1)).comp (continuous_fst.comp continuous_snd))).mul
      ((continuous_fourierChar1D (k 2)).comp (continuous_snd.comp continuous_snd))).mul
      (Complex.continuous_ofReal.comp (hf.comp cont_vec3_xyz'))).continuousOn.integrableOn_compact
      (isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc))
  have hint_g : Integrable (fun q : ℝ × (ℝ × ℝ) =>
      fourierChar1D (k 0) q.1 * fourierChar1D (k 1) q.2.1 * fourierChar1D (k 2) q.2.2 *
        (g (vec3 q.1 q.2.1 q.2.2) : ℂ)) uMeas3' := by
    rw [uMeas3'_eq_restrict]
    exact (((((continuous_fourierChar1D (k 0)).comp continuous_fst).mul
      ((continuous_fourierChar1D (k 1)).comp (continuous_fst.comp continuous_snd))).mul
      ((continuous_fourierChar1D (k 2)).comp (continuous_snd.comp continuous_snd))).mul
      (Complex.continuous_ofReal.comp (hg.comp cont_vec3_xyz'))).continuousOn.integrableOn_compact
      (isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc))
  rw [← MeasureTheory.integral_add hint_f hint_g]
  congr 1; funext q
  push_cast; ring

/-- **3D Spectral Laplacian Eigenvalue Law:**
    For any `C²` periodic scalar field `f` and wavevector `k ∈ ℤ³`:
      `fourierCoeff3D (Δf) k = -4π² (k₀² + k₁² + k₂²) * fourierCoeff3D f k` (`0 sorryAx`). -/
theorem fourierCoeff3D_laplacianScalar
    {f : R3 → ℝ} (hf : ContDiff ℝ 2 f) (hpf : IsPeriodic3D f) (k : Fin 3 → ℤ) :
    fourierCoeff3D (laplacianScalar f) k =
      (-4 * (Real.pi : ℂ) ^ 2 * ((k 0 : ℂ) ^ 2 + (k 1 : ℂ) ^ 2 + (k 2 : ℂ) ^ 2)) *
        fourierCoeff3D f k := by
  have hf1 : ContDiff ℝ 1 f := contDiff_one_of_two4 hf
  have haxis : ∀ i : Fin 3,
      fourierCoeff3D (fun x => sndPartial f x i i) k =
        (-4 * (Real.pi : ℂ) ^ 2 * (k i : ℂ) ^ 2) * fourierCoeff3D f k := by
    intro i
    have hgi : ContDiff ℝ 1 (fun y => partialDerivScalar f y i) := contDiff_one_partialDerivScalar hf i
    have hpgi : IsPeriodic3D (fun y => partialDerivScalar f y i) :=
      IsPeriodic3D.partialDeriv hpf (hf1.differentiable (by simp)) i
    have hpt : (fun x => sndPartial f x i i) =
        (fun x => partialDerivScalar (fun y => partialDerivScalar f y i) x i) := by
      funext x; exact (partial_partial_eq_sndPartial f x hf.contDiffAt i i).symm
    rw [hpt, fourierCoeff3D_partialDeriv hgi hpgi k i, fourierCoeff3D_partialDeriv hf1 hpf k i]
    have hI : Complex.I ^ 2 = -1 := Complex.I_sq
    calc (2 * (Real.pi : ℂ) * Complex.I * (k i : ℂ)) *
          ((2 * (Real.pi : ℂ) * Complex.I * (k i : ℂ)) * fourierCoeff3D f k)
        = (4 * (Real.pi : ℂ) ^ 2 * Complex.I ^ 2 * (k i : ℂ) ^ 2) * fourierCoeff3D f k := by ring
      _ = (-4 * (Real.pi : ℂ) ^ 2 * (k i : ℂ) ^ 2) * fourierCoeff3D f k := by rw [hI]; ring
  have hc0 := continuous_sndPartial_of_contDiff hf 0 0
  have hc1 := continuous_sndPartial_of_contDiff hf 1 1
  have hc2 := continuous_sndPartial_of_contDiff hf 2 2
  have hc01 : Continuous (fun x => sndPartial f x 0 0 + sndPartial f x 1 1) := hc0.add hc1
  unfold laplacianScalar
  rw [fourierCoeff3D_add hc01 hc2 k, fourierCoeff3D_add hc0 hc1 k, haxis 0, haxis 1, haxis 2]
  ring

/-- **3D Spectral Incompressibility Orthogonality (`k · û(k) = 0`):**
    For any `C¹` periodic divergence-free velocity field `u` (`∇ · u = 0`) and any `k ∈ ℤ³`:
      `k₀ û₀(k) + k₁ û₁(k) + k₂ û₂(k) = 0` (`0 sorryAx`). -/
theorem fourierCoeff3D_solenoidal_ortho
    {u : R3 → R3} (hu : ContDiff ℝ 1 u) (hpu : IsPeriodic3D u)
    (hdiv : ∀ x : R3, div3D u x = 0) (k : Fin 3 → ℤ) :
    (k 0 : ℂ) * fourierCoeff3D (fun x => u x 0) k +
    (k 1 : ℂ) * fourierCoeff3D (fun x => u x 1) k +
    (k 2 : ℂ) * fourierCoeff3D (fun x => u x 2) k = 0 := by
  have hu0 : ContDiff ℝ 1 (fun y => u y 0) := contDiff_pi.mp hu 0
  have hu1 : ContDiff ℝ 1 (fun y => u y 1) := contDiff_pi.mp hu 1
  have hu2 : ContDiff ℝ 1 (fun y => u y 2) := contDiff_pi.mp hu 2
  have hpu0 : IsPeriodic3D (fun y => u y 0) := fun x i => congrArg (fun v => v 0) (hpu x i)
  have hpu1 : IsPeriodic3D (fun y => u y 1) := fun x i => congrArg (fun v => v 1) (hpu x i)
  have hpu2 : IsPeriodic3D (fun y => u y 2) := fun x i => congrArg (fun v => v 2) (hpu x i)
  have hc0 := continuous_partialDerivScalar_of_contDiff hu0 0
  have hc1 := continuous_partialDerivScalar_of_contDiff hu1 1
  have hc2 := continuous_partialDerivScalar_of_contDiff hu2 2
  have hc01 : Continuous (fun x => partialDerivScalar (fun y => u y 0) x 0 +
      partialDerivScalar (fun y => u y 1) x 1) := hc0.add hc1
  have hzero : fourierCoeff3D (div3D u) k = 0 := by
    have hfun : div3D u = (fun _ => (0 : ℝ)) := funext hdiv
    rw [hfun]
    unfold fourierCoeff3D
    simp
  unfold div3D at hzero
  rw [fourierCoeff3D_add hc01 hc2 k, fourierCoeff3D_add hc0 hc1 k,
      fourierCoeff3D_partialDeriv hu0 hpu0 k 0,
      fourierCoeff3D_partialDeriv hu1 hpu1 k 1,
      fourierCoeff3D_partialDeriv hu2 hpu2 k 2] at hzero
  have hfactor : (2 * (Real.pi : ℂ) * Complex.I) *
      ((k 0 : ℂ) * fourierCoeff3D (fun x => u x 0) k +
       (k 1 : ℂ) * fourierCoeff3D (fun x => u x 1) k +
       (k 2 : ℂ) * fourierCoeff3D (fun x => u x 2) k) = 0 := by
    linear_combination hzero
  have h2piI : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 := by
    have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
    exact mul_ne_zero (mul_ne_zero (by norm_num) hpi) Complex.I_ne_zero
  exact (mul_eq_zero.mp hfactor).resolve_left h2piI

-- ============================================================================
-- SECTION 5: AXIOM AUDIT TRAIL (0 sorryAx)
-- ============================================================================

#print axioms norm_sq_fourierCoeffOn_deriv
#print axioms bernstein_1d_periodic_shell
#print axioms wirtinger_1d_periodic
#print axioms wirtinger_3d_torus
#print axioms wirtinger_3d_torus_vec
#print axioms bernstein_3d_torus_z_shell
#print axioms sharp_analytical_lemma4_bernstein_poincare_vorticity
#print axioms sharp_global_exponential_energy_decay_torus3D
#print axioms fourierCoeff3D_partialDeriv
#print axioms fourierCoeff3D_laplacianScalar
#print axioms fourierCoeff3D_solenoidal_ortho

end GarryFourierSpectral3D