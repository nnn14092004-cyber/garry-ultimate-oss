import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import ParsevalSobolevTorus3D

/-!
# GARRYULT v4.0.0 — Milestone 5C: 3D Bilinear Plancherel, Explicit Lattice Convergence
# (`∑_{k≠0} |k|⁻⁴ ≤ 52`), Pointwise 3D Fourier Inversion, Sobolev Embedding `H²(𝕋³) ↪ L∞(𝕋³)`,
# Sharp 3D Agmon Inequality & Spectral Heat Semigroup `e^{νtΔ}` on `𝕋³`
-/

namespace GarrySobolevEmbedding3D

open MeasureTheory Filter Topology GarryReal3DCalculus GarryVorticity3D
  GarryLerayTorus3D GarryLerayEnergyLaw3D GarryPoincareSobolev3D
  GarryFourierSpectral3D GarrySpectralOperators3D GarryParsevalSobolev3D

private lemma two_add_one_eq_three5c {α : Type*} [AddMonoidWithOne α] :
    (2 : α) + 1 = 3 := by
  rw [← Nat.cast_ofNat (n := 2), ← Nat.cast_one, ← Nat.cast_add]
  exact Nat.cast_ofNat

private lemma contDiff_two_of_three5c {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {f : E → F} (hf : ContDiff ℝ 3 f) :
    ContDiff ℝ 2 f :=
  hf.of_le (by rw [← two_add_one_eq_three5c]; exact le_self_add)

private theorem torusIntegral_const_mul_5c (c : ℝ) (f : R3 → ℝ) :
    torusIntegral (fun x => c * f x) = c * torusIntegral f := by
  unfold torusIntegral
  simp_rw [intervalIntegral.integral_const_mul]

private theorem torusIntegral_add_5c {f g : R3 → ℝ} (hf : Continuous f) (hg : Continuous g) :
    torusIntegral (fun x => f x + g x) = torusIntegral f + torusIntegral g := by
  have h := torusIntegral_add3 hf hg (continuous_const (y := (0 : ℝ)))
  have h0 : torusIntegral (fun _ : R3 => (0 : ℝ)) = 0 := by unfold torusIntegral; simp
  simpa [h0] using h

-- ============================================================================
-- SECTION 1: 3D BILINEAR PLANCHEREL IDENTITY (SCALAR & VECTOR)
-- ============================================================================

private lemma complex_polarization_re (a b : ℂ) :
    ‖a + b‖ ^ 2 - ‖a - b‖ ^ 2 = 4 * (starRingEnd ℂ a * b).re := by
  have h1 : ‖a + b‖ ^ 2 = Complex.normSq (a + b) := (Complex.normSq_eq_norm_sq _).symm
  have h2 : ‖a - b‖ ^ 2 = Complex.normSq (a - b) := (Complex.normSq_eq_norm_sq _).symm
  rw [h1, h2, Complex.normSq_apply, Complex.normSq_apply]
  simp only [Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im,
    Complex.mul_re, Complex.conj_re, Complex.conj_im]
  ring

/-- **MAIN THEOREM 1 OF MILESTONE 5C (3D Bilinear Plancherel Identity — Scalar):**
    `∑' k : ℤ³, Re(conj(f̂(k)) * ĝ(k)) = ∫_{𝕋³} f(x) g(x) dx` (`0 sorryAx`). -/
theorem plancherel_inner_3d_scalar
    {f g : R3 → ℝ} (hf : Continuous f) (hg : Continuous g)
    (hpf : IsPeriodic3D f) (hpg : IsPeriodic3D g) :
    HasSum (fun k : Fin 3 → ℤ => (starRingEnd ℂ (fourierCoeff3D f k) * fourierCoeff3D g k).re)
      (torusIntegral (fun x => f x * g x)) := by
  have hc_add : Continuous (fun x => f x + g x) := hf.add hg
  have hc_sub : Continuous (fun x => f x - g x) := hf.sub hg
  have hp_add : IsPeriodic3D (fun x => f x + g x) := fun x i => by simp only [hpf x i, hpg x i]
  have hp_sub : IsPeriodic3D (fun x => f x - g x) := fun x i => by simp only [hpf x i, hpg x i]
  have h1 := hasSum_sq_fourierCoeff3D hc_add hp_add
  have h2 := hasSum_sq_fourierCoeff3D hc_sub hp_sub
  have hdiff := (h1.sub h2).mul_left (1 / 4 : ℝ)
  have h_lhs : (fun k : Fin 3 → ℤ => (1 / 4 : ℝ) *
      (‖fourierCoeff3D (fun x => f x + g x) k‖ ^ 2 -
       ‖fourierCoeff3D (fun x => f x - g x) k‖ ^ 2)) =
      (fun k : Fin 3 → ℤ => (starRingEnd ℂ (fourierCoeff3D f k) * fourierCoeff3D g k).re) := by
    funext k
    rw [fourierCoeff3D_add hf hg k, fourierCoeff3D_sub hf hg k, complex_polarization_re]
    ring
  have h_rhs : (1 / 4 : ℝ) * (torusIntegral (fun x => (f x + g x) ^ 2) -
      torusIntegral (fun x => (f x - g x) ^ 2)) = torusIntegral (fun x => f x * g x) := by
    have hpt : ∀ x : R3, (f x + g x) ^ 2 = (f x - g x) ^ 2 + 4 * (f x * g x) := fun x => by ring
    have hc_sub2 : Continuous (fun x => (f x - g x) ^ 2) := hc_sub.pow 2
    have hc_4fg : Continuous (fun x => 4 * (f x * g x)) := continuous_const.mul (hf.mul hg)
    have hsum_int : torusIntegral (fun x => (f x + g x) ^ 2) =
        torusIntegral (fun x => (f x - g x) ^ 2) + 4 * torusIntegral (fun x => f x * g x) := by
      rw [torusIntegral_congr hpt,
          torusIntegral_add_5c hc_sub2 hc_4fg,
          torusIntegral_const_mul_5c 4]
    linarith
  rw [h_lhs, h_rhs] at hdiff
  exact hdiff

/-- **3D Bilinear Plancherel Identity (Vector):**
    `∑' k : ℤ³, ∑_{c=0}^2 Re(conj(û_c(k)) * v̂_c(k)) = ∫_{𝕋³} (u(x) · v(x)) dx` (`0 sorryAx`). -/
theorem plancherel_inner_3d_vec
    {u v : R3 → R3} (hu : Continuous u) (hv : Continuous v)
    (hpu : IsPeriodic3D u) (hpv : IsPeriodic3D v) :
    HasSum (fun k : Fin 3 → ℤ =>
        (starRingEnd ℂ (fourierCoeff3DVec u k 0) * fourierCoeff3DVec v k 0).re +
        (starRingEnd ℂ (fourierCoeff3DVec u k 1) * fourierCoeff3DVec v k 1).re +
        (starRingEnd ℂ (fourierCoeff3DVec u k 2) * fourierCoeff3DVec v k 2).re)
      (torusIntegral (fun x => dot3D (u x) (v x))) := by
  have hu0 : Continuous (fun x => u x 0) := (continuous_apply 0).comp hu
  have hu1 : Continuous (fun x => u x 1) := (continuous_apply 1).comp hu
  have hu2 : Continuous (fun x => u x 2) := (continuous_apply 2).comp hu
  have hv0 : Continuous (fun x => v x 0) := (continuous_apply 0).comp hv
  have hv1 : Continuous (fun x => v x 1) := (continuous_apply 1).comp hv
  have hv2 : Continuous (fun x => v x 2) := (continuous_apply 2).comp hv
  have hpu0 : IsPeriodic3D (fun x => u x 0) := fun x i => congrArg (fun w => w 0) (hpu x i)
  have hpu1 : IsPeriodic3D (fun x => u x 1) := fun x i => congrArg (fun w => w 1) (hpu x i)
  have hpu2 : IsPeriodic3D (fun x => u x 2) := fun x i => congrArg (fun w => w 2) (hpu x i)
  have hpv0 : IsPeriodic3D (fun x => v x 0) := fun x i => congrArg (fun w => w 0) (hpv x i)
  have hpv1 : IsPeriodic3D (fun x => v x 1) := fun x i => congrArg (fun w => w 1) (hpv x i)
  have hpv2 : IsPeriodic3D (fun x => v x 2) := fun x i => congrArg (fun w => w 2) (hpv x i)
  have hsum := ((plancherel_inner_3d_scalar hu0 hv0 hpu0 hpv0).add
    (plancherel_inner_3d_scalar hu1 hv1 hpu1 hpv1)).add
    (plancherel_inner_3d_scalar hu2 hv2 hpu2 hpv2)
  have hc0 : Continuous (fun x => u x 0 * v x 0) := hu0.mul hv0
  have hc1 : Continuous (fun x => u x 1 * v x 1) := hu1.mul hv1
  have hc2 : Continuous (fun x => u x 2 * v x 2) := hu2.mul hv2
  have hdot : torusIntegral (fun x => u x 0 * v x 0) +
      torusIntegral (fun x => u x 1 * v x 1) +
      torusIntegral (fun x => u x 2 * v x 2) =
      torusIntegral (fun x => dot3D (u x) (v x)) := by
    rw [← torusIntegral_add3 hc0 hc1 hc2]; rfl
  rw [hdot] at hsum
  exact hsum

-- ============================================================================
-- SECTION 2: VANISHING LEMMA & 3D LATTICE SUMS (`∑_{k≠0} |k|⁻⁴ ≤ 52`, AGMON `≤ 13π`)
-- ============================================================================

private theorem eq_zero_of_intervalIntegral_eq_zero_of_nonneg
    {φ : ℝ → ℝ} (hφ : Continuous φ) (hnn : ∀ t ∈ Set.Icc (0 : ℝ) 1, 0 ≤ φ t)
    (hint : ∫ t in (0 : ℝ)..1, φ t = 0) :
    ∀ t ∈ Set.Icc (0 : ℝ) 1, φ t = 0 := by
  intro t₀ ht₀
  by_contra hne
  have hpos : 0 < φ t₀ := lt_of_le_of_ne (hnn t₀ ht₀) (Ne.symm hne)
  obtain ⟨δ, hδ_pos, hδ⟩ := Metric.continuousAt_iff.mp hφ.continuousAt (φ t₀ / 2) (half_pos hpos)
  let a : ℝ := max 0 (t₀ - δ / 2)
  let b : ℝ := min 1 (t₀ + δ / 2)
  have ha0 : 0 ≤ a := le_max_left _ _
  have hb1 : b ≤ 1 := min_le_left _ _
  have hab : a < b := by
    dsimp only [a, b]
    exact max_lt (lt_min (by norm_num) (by linarith [ht₀.1]))
      (lt_min (by linarith [ht₀.2]) (by linarith))
  have hge : ∀ t ∈ Set.Icc a b, φ t₀ / 2 ≤ φ t := by
    intro t ht
    have hdist : dist t t₀ < δ := by
      rw [Real.dist_eq, abs_lt]
      constructor <;> linarith [le_trans (le_max_right (0 : ℝ) (t₀ - δ / 2)) ht.1,
        le_trans ht.2 (min_le_right (1 : ℝ) (t₀ + δ / 2))]
    have hball := hδ hdist
    rw [Real.dist_eq, abs_lt] at hball
    linarith
  have hi1 : (0 : ℝ) ≤ ∫ t in (0 : ℝ)..a, φ t :=
    intervalIntegral.integral_nonneg ha0 fun t ht =>
      hnn t ⟨ht.1, le_trans ht.2 (le_trans (le_of_lt hab) hb1)⟩
  have hi3 : (0 : ℝ) ≤ ∫ t in b..1, φ t :=
    intervalIntegral.integral_nonneg hb1 fun t ht =>
      hnn t ⟨le_trans ha0 (le_trans (le_of_lt hab) ht.1), ht.2⟩
  have hi2 : (b - a) * (φ t₀ / 2) ≤ ∫ t in a..b, φ t := by
    have hmono := intervalIntegral.integral_mono_on (μ := volume) (le_of_lt hab)
      (continuous_const.intervalIntegrable (μ := volume) a b)
      (hφ.intervalIntegrable (μ := volume) a b) hge
    rw [intervalIntegral.integral_const, smul_eq_mul] at hmono
    exact hmono
  have hsplit1 := intervalIntegral.integral_add_adjacent_intervals
    (hφ.intervalIntegrable (μ := volume) 0 a) (hφ.intervalIntegrable (μ := volume) a b)
  have hsplit2 := intervalIntegral.integral_add_adjacent_intervals
    (hφ.intervalIntegrable (μ := volume) 0 b) (hφ.intervalIntegrable (μ := volume) b 1)
  have hpos_int : 0 < (b - a) * (φ t₀ / 2) := mul_pos (sub_pos.mpr hab) (half_pos hpos)
  linarith

private theorem isPeriodic3D_shift_int_5c {f : R3 → ℝ} (hpf : IsPeriodic3D f) :
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
        funext j; unfold basisVec
        by_cases hj : j = i
        · subst hj; simp [Nat.cast_add]; ring
        · simp [hj]
      rw [hstep, hpf _ i, ih]
  have h_one : ∀ (x : R3) (i : Fin 3) (n : ℤ),
      f (fun j => if j = i then x j + (n : ℝ) else x j) = f x := by
    intro x i n
    cases n with
    | ofNat k => simpa using h_nat k x i
    | negSucc k =>
      let y : R3 := fun j => if j = i then x j + ((Int.negSucc k : ℤ) : ℝ) else x j
      have hy : (fun j => if j = i then y j + ((k + 1 : ℕ) : ℝ) else y j) = x := by
        funext j; dsimp only [y]
        by_cases hj : j = i
        · subst hj; simp only [↓reduceIte, Int.cast_negSucc, Nat.cast_add, Nat.cast_one]; ring
        · simp [hj]
      have h := h_nat (k + 1) y i
      rw [hy] at h; exact h.symm
  intro x m
  let x1 : R3 := fun j => if j = 0 then x j + (m 0 : ℝ) else x j
  let x2 : R3 := fun j => if j = 1 then x1 j + (m 1 : ℝ) else x1 j
  let x3 : R3 := fun j => if j = 2 then x2 j + (m 2 : ℝ) else x2 j
  have h_eq : (fun i => x i + (m i : ℝ)) = x3 := by
    funext i; fin_cases i <;> simp [x3, x2, x1]
  rw [h_eq, h_one x2 2 (m 2), h_one x1 1 (m 1), h_one x 0 (m 0)]

/-- **Vanishing Lemma on `𝕋³`:**
    A continuous `ℤ³`-periodic function `h` with `∫_{𝕋³} h² = 0` vanishes identically (`0 sorryAx`). -/
theorem eq_zero_of_torusIntegral_sq_eq_zero
    {h : R3 → ℝ} (hh : Continuous h) (hph : IsPeriodic3D h)
    (hz : torusIntegral (fun x => (h x) ^ 2) = 0) :
    ∀ x : R3, h x = 0 := by
  have h_cube : ∀ x ∈ Set.Icc (0 : ℝ) 1, ∀ y ∈ Set.Icc (0 : ℝ) 1, ∀ z ∈ Set.Icc (0 : ℝ) 1,
      h (vec3 x y z) = 0 := by
    have hcont_xyz : Continuous (fun q : ℝ × (ℝ × ℝ) => (h (vec3 q.1 q.2.1 q.2.2)) ^ 2) :=
      (hh.comp (continuous_pi fun i => match i with
        | ⟨0, _⟩ => continuous_fst | ⟨1, _⟩ => continuous_fst.comp continuous_snd
        | ⟨2, _⟩ => continuous_snd.comp continuous_snd)).pow 2
    have hc_y : ∀ x : ℝ, Continuous (fun y : ℝ => ∫ z in (0 : ℝ)..1, (h (vec3 x y z)) ^ 2) := by
      intro x
      have hG : Continuous (fun p : ℝ × ℝ => (h (vec3 x p.1 p.2)) ^ 2) :=
        (hh.comp (continuous_pi fun i => match i with
          | ⟨0, _⟩ => continuous_const | ⟨1, _⟩ => continuous_fst | ⟨2, _⟩ => continuous_snd)).pow 2
      have h_eq : (fun y => ∫ z in (0 : ℝ)..1, (h (vec3 x y z)) ^ 2) =
          (fun y => ∫ z, (h (vec3 x y z)) ^ 2 ∂(volume.restrict (Set.Icc (0 : ℝ) 1))) := by
        funext y
        rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1),
            ← MeasureTheory.integral_Icc_eq_integral_Ioc]
      rw [h_eq]
      have : IsFiniteMeasure (volume.restrict (Set.Icc (0 : ℝ) 1)) :=
        ⟨by rw [Measure.restrict_apply_univ]; exact isCompact_Icc.measure_lt_top⟩
      refine continuous_iff_continuousAt.mpr fun y₀ => ?_
      let s : Set ℝ := Set.Icc (y₀ - 1) (y₀ + 1)
      have hs : s ∈ 𝓝 y₀ := Icc_mem_nhds (by linarith) (by linarith)
      obtain ⟨C, hC⟩ := (isCompact_Icc.prod isCompact_Icc).exists_bound_of_continuousOn hG.continuousOn
        (s := s ×ˢ Set.Icc (0 : ℝ) 1)
      refine continuousAt_of_dominated
        (Eventually.of_forall fun y => (hG.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable)
        ?_ (integrable_const C)
        (Eventually.of_forall fun z => (hG.comp (continuous_id.prodMk continuous_const)).continuousAt)
      filter_upwards [hs] with y hy
      filter_upwards [ae_restrict_mem measurableSet_Icc] with z hz
      exact hC (y, z) ⟨hy, hz⟩
    have hc_x : Continuous (fun x : ℝ => ∫ y in (0 : ℝ)..1, ∫ z in (0 : ℝ)..1, (h (vec3 x y z)) ^ 2) := by
      let μ2 := (volume.restrict (Set.Icc (0 : ℝ) 1)).prod (volume.restrict (Set.Icc (0 : ℝ) 1))
      have hμ2 : μ2 = (volume : Measure (ℝ × ℝ)).restrict (Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1) := by
        dsimp only [μ2]; rw [Measure.prod_restrict]; rfl
      have h_eq : (fun x => ∫ y in (0 : ℝ)..1, ∫ z in (0 : ℝ)..1, (h (vec3 x y z)) ^ 2) =
          (fun x => ∫ p : ℝ × ℝ, (h (vec3 x p.1 p.2)) ^ 2 ∂μ2) := by
        funext x
        have hG : Continuous (fun p : ℝ × ℝ => (h (vec3 x p.1 p.2)) ^ 2) :=
          (hh.comp (continuous_pi fun i => match i with
            | ⟨0, _⟩ => continuous_const | ⟨1, _⟩ => continuous_fst | ⟨2, _⟩ => continuous_snd)).pow 2
        have hint : Integrable (fun p : ℝ × ℝ => (h (vec3 x p.1 p.2)) ^ 2) μ2 := by
          rw [hμ2]; exact hG.continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)
        rw [MeasureTheory.integral_prod _ hint]
        simp_rw [MeasureTheory.integral_Icc_eq_integral_Ioc,
          ← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
      rw [h_eq]
      have : IsFiniteMeasure μ2 :=
        ⟨by rw [hμ2, Measure.restrict_apply_univ]; exact (isCompact_Icc.prod isCompact_Icc).measure_lt_top⟩
      refine continuous_iff_continuousAt.mpr fun x₀ => ?_
      let s : Set ℝ := Set.Icc (x₀ - 1) (x₀ + 1)
      have hs : s ∈ 𝓝 x₀ := Icc_mem_nhds (by linarith) (by linarith)
      obtain ⟨C, hC⟩ := (isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc)).exists_bound_of_continuousOn
        hcont_xyz.continuousOn (s := s ×ˢ (Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1))
      refine continuousAt_of_dominated
        (Eventually.of_forall fun x => (hcont_xyz.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable)
        ?_ (integrable_const C)
        (Eventually.of_forall fun p => (hcont_xyz.comp (continuous_id.prodMk continuous_const)).continuousAt)
      filter_upwards [hs] with x hx
      rw [hμ2]
      filter_upwards [ae_restrict_mem (measurableSet_Icc.prod measurableSet_Icc)] with p hp
      exact hC (x, p) ⟨hx, hp⟩
    have hnn_y : ∀ x y : ℝ, 0 ≤ ∫ z in (0 : ℝ)..1, (h (vec3 x y z)) ^ 2 := fun x y =>
      intervalIntegral.integral_nonneg (by norm_num) fun z _ => sq_nonneg _
    have hnn_x : ∀ x : ℝ, 0 ≤ ∫ y in (0 : ℝ)..1, ∫ z in (0 : ℝ)..1, (h (vec3 x y z)) ^ 2 := fun x =>
      intervalIntegral.integral_nonneg (by norm_num) fun y _ => hnn_y x y
    intro x hx y hy z hz_mem
    have hx0 := eq_zero_of_intervalIntegral_eq_zero_of_nonneg hc_x (fun t _ => hnn_x t) hz x hx
    have hy0 := eq_zero_of_intervalIntegral_eq_zero_of_nonneg (hc_y x) (fun t _ => hnn_y x t) hx0 y hy
    have hcz : Continuous (fun s => (h (vec3 x y s)) ^ 2) :=
      (hh.comp (continuous_pi fun i => match i with
        | ⟨0, _⟩ => continuous_const | ⟨1, _⟩ => continuous_const | ⟨2, _⟩ => continuous_id)).pow 2
    have hz0 := eq_zero_of_intervalIntegral_eq_zero_of_nonneg hcz (fun _ _ => sq_nonneg _) hy0 z hz_mem
    exact sq_eq_zero_iff.mp hz0
  intro p
  let m : Fin 3 → ℤ := fun i => -⌊p i⌋
  have hfract : ∀ i : Fin 3, p i + (m i : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by
    intro i; dsimp only [m]; rw [Int.cast_neg]
    exact ⟨by linarith [Int.floor_le (p i)], by linarith [Int.lt_floor_add_one (p i)]⟩
  have hshift := isPeriodic3D_shift_int_5c hph p m
  have hvec : (fun i => p i + (m i : ℝ)) =
      vec3 (p 0 + (m 0 : ℝ)) (p 1 + (m 1 : ℝ)) (p 2 + (m 2 : ℝ)) := by
    funext i; fin_cases i <;> rfl
  rw [← hshift, hvec]
  exact h_cube _ (hfract 0) _ (hfract 1) _ (hfract 2)

private def kMaxAbs (k : Fin 3 → ℤ) : ℕ :=
  max (k 0).natAbs (max (k 1).natAbs (k 2).natAbs)

private def latticeBox (N : ℕ) : Finset (Fin 3 → ℤ) :=
  Fintype.piFinset fun _ : Fin 3 => Finset.Icc (-(N : ℤ)) (N : ℤ)

private theorem mem_latticeBox_iff {N : ℕ} {k : Fin 3 → ℤ} :
    k ∈ latticeBox N ↔ kMaxAbs k ≤ N := by
  unfold latticeBox kMaxAbs
  rw [Fintype.mem_piFinset]
  simp only [Finset.mem_Icc, max_le_iff]
  have h1 : ∀ n : ℤ, (-(N : ℤ) ≤ n ∧ n ≤ (N : ℤ)) ↔ n.natAbs ≤ N := fun n => by omega
  constructor
  · intro h; exact ⟨(h1 (k 0)).mp (h 0), (h1 (k 1)).mp (h 1), (h1 (k 2)).mp (h 2)⟩
  · intro ⟨h0, h1', h2⟩ i
    fin_cases i
    · exact (h1 (k 0)).mpr h0
    · exact (h1 (k 1)).mpr h1'
    · exact (h1 (k 2)).mpr h2

private theorem card_latticeBox (N : ℕ) : (latticeBox N).card = (2 * N + 1) ^ 3 := by
  unfold latticeBox
  rw [Fintype.card_piFinset]
  simp only [Fin.prod_univ_three, Int.card_Icc]
  have hcard : ((N : ℤ) + 1 - -(N : ℤ)).toNat = 2 * N + 1 := by omega
  rw [hcard]; ring

private def latticeShell (m : ℕ) : Finset (Fin 3 → ℤ) :=
  (latticeBox m).filter (fun k => kMaxAbs k = m)

private theorem card_latticeShell_le (m : ℕ) (hm : 1 ≤ m) :
    (latticeShell m).card ≤ 26 * m ^ 2 := by
  have hsub : latticeShell m ⊆ latticeBox m \ latticeBox (m - 1) := by
    intro k hk
    rw [latticeShell, Finset.mem_filter] at hk
    rw [Finset.mem_sdiff, mem_latticeBox_iff, mem_latticeBox_iff]; omega
  have hbox_sub : latticeBox (m - 1) ⊆ latticeBox m := by
    intro k hk; rw [mem_latticeBox_iff] at hk ⊢; omega
  have hcard_sdiff : (latticeBox m \ latticeBox (m - 1)).card =
      (2 * m + 1) ^ 3 - (2 * (m - 1) + 1) ^ 3 := by
    rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hbox_sub, card_latticeBox, card_latticeBox]
  have hle := le_trans (Finset.card_le_card hsub) (le_of_eq hcard_sdiff)
  have hnum : (2 * m + 1) ^ 3 - (2 * (m - 1) + 1) ^ 3 ≤ 26 * m ^ 2 := by
    obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_le hm
    have : 1 + r - 1 = r := by omega
    rw [this]
    have h1 : (2 * (1 + r) + 1) ^ 3 = (2 * r + 1) ^ 3 + (24 * (1 + r) ^ 2 + 2) := by ring
    rw [h1, Nat.add_sub_cancel_left]; nlinarith
  exact le_trans hle hnum

private theorem kMaxAbs_sq_le_kNormSq (k : Fin 3 → ℤ) :
    ((kMaxAbs k : ℝ) ^ 2) ≤ kNormSq k := by
  unfold kMaxAbs kNormSq
  have h0 : ((k 0).natAbs : ℝ) ^ 2 = (k 0 : ℝ) ^ 2 := by
    rw [← Int.cast_natCast, Int.natCast_natAbs, Int.cast_abs, sq_abs]
  have h1 : ((k 1).natAbs : ℝ) ^ 2 = (k 1 : ℝ) ^ 2 := by
    rw [← Int.cast_natCast, Int.natCast_natAbs, Int.cast_abs, sq_abs]
  have h2 : ((k 2).natAbs : ℝ) ^ 2 = (k 2 : ℝ) ^ 2 := by
    rw [← Int.cast_natCast, Int.natCast_natAbs, Int.cast_abs, sq_abs]
  have hnn0 : 0 ≤ (k 0 : ℝ) ^ 2 := sq_nonneg _
  have hnn1 : 0 ≤ (k 1 : ℝ) ^ 2 := sq_nonneg _
  have hnn2 : 0 ≤ (k 2 : ℝ) ^ 2 := sq_nonneg _
  rcases max_choice (k 0).natAbs (max (k 1).natAbs (k 2).natAbs) with h | h
  · rw [h, h0]; linarith
  · rw [h]
    rcases max_choice (k 1).natAbs (k 2).natAbs with h' | h'
    · rw [h', h1]; linarith
    · rw [h', h2]; linarith

private theorem kMaxAbs_eq_zero_iff (k : Fin 3 → ℤ) : kMaxAbs k = 0 ↔ k = 0 := by
  unfold kMaxAbs
  constructor
  · intro h
    have h0 : (k 0).natAbs = 0 := by omega
    have h1 : (k 1).natAbs = 0 := by omega
    have h2 : (k 2).natAbs = 0 := by omega
    funext i; fin_cases i
    · exact Int.natAbs_eq_zero.mp h0
    · exact Int.natAbs_eq_zero.mp h1
    · exact Int.natAbs_eq_zero.mp h2
  · intro h; subst h; simp

private theorem sum_finset_le_of_radial_bound {w : (Fin 3 → ℤ) → ℝ} {φ : ℕ → ℝ} {B : ℝ}
    (hw_nn : ∀ k, 0 ≤ w k) (hw0 : w 0 = 0)
    (h_rad : ∀ k, k ≠ 0 → w k ≤ φ (kMaxAbs k))
    (h_sum_bound : ∀ N : ℕ, ∑ m ∈ Finset.Icc 1 N, (26 * (m : ℝ) ^ 2) * φ m ≤ B)
    (hφ_nn : ∀ m, 1 ≤ m → 0 ≤ φ m) :
    Summable w ∧ ∑' k, w k ≤ B := by
  have hfin : ∀ s : Finset (Fin 3 → ℤ), ∑ k ∈ s, w k ≤ B := by
    intro s
    let N : ℕ := s.sup kMaxAbs
    have hs_sub : s ⊆ latticeBox N := fun k hk =>
      mem_latticeBox_iff.mpr (Finset.le_sup (f := kMaxAbs) hk)
    have hle1 : ∑ k ∈ s, w k ≤ ∑ k ∈ latticeBox N, w k :=
      Finset.sum_le_sum_of_subset_of_nonneg hs_sub fun k _ _ => hw_nn k
    have hfib := (Finset.sum_fiberwise_of_maps_to
      (s := latticeBox N) (t := Finset.Icc 0 N) (g := kMaxAbs)
      (fun k hk => Finset.mem_Icc.mpr ⟨Nat.zero_le _, mem_latticeBox_iff.mp hk⟩) w).symm
    have h0_zero : ∑ k ∈ (latticeBox N).filter (fun k => kMaxAbs k = 0), w k = 0 := by
      refine Finset.sum_eq_zero fun k hk => ?_
      rw [Finset.mem_filter] at hk
      rw [(kMaxAbs_eq_zero_iff k).mp hk.2, hw0]
    have hsplit : Finset.Icc 0 N = insert 0 (Finset.Icc 1 N) := by
      ext m; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
    have hnotmem : (0 : ℕ) ∉ Finset.Icc 1 N := by simp
    rw [hsplit, Finset.sum_insert hnotmem, h0_zero, zero_add] at hfib
    have hshell : ∀ m ∈ Finset.Icc 1 N,
        ∑ k ∈ (latticeBox N).filter (fun k => kMaxAbs k = m), w k ≤ (26 * (m : ℝ) ^ 2) * φ m := by
      intro m hm
      have hm1 : 1 ≤ m := (Finset.mem_Icc.mp hm).1
      have hfilt_eq : (latticeBox N).filter (fun k => kMaxAbs k = m) = latticeShell m := by
        ext k; simp only [latticeShell, Finset.mem_filter, mem_latticeBox_iff]
        have hmN : m ≤ N := (Finset.mem_Icc.mp hm).2
        constructor <;> intro ⟨h1, h2⟩ <;> exact ⟨by omega, h2⟩
      rw [hfilt_eq]
      have hterm : ∀ k ∈ latticeShell m, w k ≤ φ m := by
        intro k hk
        rw [latticeShell, Finset.mem_filter] at hk
        have hne : k ≠ 0 := fun h => by rw [h, (kMaxAbs_eq_zero_iff 0).mpr rfl] at hk; omega
        rw [← hk.2]; exact h_rad k hne
      calc ∑ k ∈ latticeShell m, w k
          ≤ ∑ _k ∈ latticeShell m, φ m := Finset.sum_le_sum hterm
        _ = ((latticeShell m).card : ℝ) * φ m := by rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ (26 * (m : ℝ) ^ 2) * φ m := by
            have hc : ((latticeShell m).card : ℝ) ≤ 26 * (m : ℝ) ^ 2 := by
              exact_mod_cast card_latticeShell_le m hm1
            exact mul_le_mul_of_nonneg_right hc (hφ_nn m hm1)
    have hle2 : ∑ k ∈ latticeBox N, w k ≤ ∑ m ∈ Finset.Icc 1 N, (26 * (m : ℝ) ^ 2) * φ m := by
      rw [hfib]; exact Finset.sum_le_sum hshell
    exact le_trans hle1 (le_trans hle2 (h_sum_bound N))
  have hsum : Summable w := summable_of_sum_le hw_nn hfin
  exact ⟨hsum, le_of_tendsto hsum.hasSum (Eventually.of_forall hfin)⟩

/-- Weight `|k|⁻⁴` for `k ≠ 0`, `0` at `k = 0`. -/
noncomputable def invKNormSqSq (k : Fin 3 → ℤ) : ℝ :=
  if k = 0 then 0 else (kNormSq k)⁻¹ ^ 2

/-- **MAIN THEOREM 2 OF MILESTONE 5C (3D Lattice Convergence `∑_{k ≠ 0} |k|⁻⁴ ≤ 52`):** (`0 sorryAx`). -/
theorem summable_and_tsum_invKNormSqSq_le :
    Summable invKNormSqSq ∧ ∑' k : Fin 3 → ℤ, invKNormSqSq k ≤ 52 := by
  refine sum_finset_le_of_radial_bound (φ := fun m => ((m : ℝ) ^ 4)⁻¹) (B := 52)
    (fun k => by unfold invKNormSqSq; split_ifs <;> positivity)
    (by unfold invKNormSqSq; simp)
    (fun k hk => by
      unfold invKNormSqSq; simp only [hk, ↓reduceIte]
      have hm_pos : (0 : ℝ) < (kMaxAbs k : ℝ) :=
        Nat.cast_pos.mpr (Nat.pos_of_ne_zero (fun h => hk ((kMaxAbs_eq_zero_iff k).mp h)))
      have hsq : (kMaxAbs k : ℝ) ^ 2 ≤ kNormSq k := kMaxAbs_sq_le_kNormSq k
      have h4 : (kMaxAbs k : ℝ) ^ 4 ≤ (kNormSq k) ^ 2 := by nlinarith
      rw [inv_pow]; exact inv_anti₀ (by positivity) h4)
    (fun N => by
      have hterm : ∀ m ∈ Finset.Icc 1 N, (26 * (m : ℝ) ^ 2) * ((m : ℝ) ^ 4)⁻¹ = 26 * ((m : ℝ) ^ 2)⁻¹ := by
        intro m hm
        have hm_ne : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by have := (Finset.mem_Icc.mp hm).1; omega)
        field_simp [hm_ne]
      rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum]
      have h_tele : ∀ M : ℕ, 1 ≤ M → ∑ m ∈ Finset.Icc 1 M, ((m : ℝ) ^ 2)⁻¹ ≤ 2 - (M : ℝ)⁻¹ := by
        intro M hM
        induction M with
        | zero => omega
        | succ q ihq =>
          cases q with
          | zero => simp; norm_num
          | succ s =>
            have hsplit : Finset.Icc 1 (s + 2) = insert (s + 2) (Finset.Icc 1 (s + 1)) := by
              ext a; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
            rw [hsplit, Finset.sum_insert (by simp)]
            have hq := ihq (by omega)
            have hs1 : (0 : ℝ) < (s : ℝ) + 1 := by positivity
            have hs2 : (0 : ℝ) < (s : ℝ) + 2 := by positivity
            have hstep : (((s + 2 : ℕ) : ℝ) ^ 2)⁻¹ ≤ ((s + 1 : ℕ) : ℝ)⁻¹ - ((s + 2 : ℕ) : ℝ)⁻¹ := by
              push_cast
              rw [inv_sub_inv (ne_of_gt hs1) (ne_of_gt hs2)]
              have hnum : (s : ℝ) + 2 - ((s : ℝ) + 1) = 1 := by ring
              rw [hnum, one_div]; exact inv_anti₀ (by positivity) (by nlinarith)
            linarith
      cases N with
      | zero => simp
      | succ n =>
        have hle := h_tele (n + 1) (by omega)
        have hpos : (0 : ℝ) ≤ ((n + 1 : ℕ) : ℝ)⁻¹ := by positivity
        linarith)
    (fun m _ => by positivity)

/-- Agmon spectral weight `(R |k|² + R⁻¹ |k|⁴)⁻¹` for `k ≠ 0`, `0` at `k = 0`. -/
noncomputable def agmonWeight (R : ℝ) (k : Fin 3 → ℤ) : ℝ :=
  if k = 0 then 0 else (R * kNormSq k + R⁻¹ * (kNormSq k) ^ 2)⁻¹

/-- **Uniform 3D Agmon Lattice Bound (`∑_{k ≠ 0} (R |k|² + R⁻¹ |k|⁴)⁻¹ ≤ 13π` for ALL `R > 0`):** (`0 sorryAx`). -/
theorem summable_and_tsum_agmonWeight_le {R : ℝ} (hR : 0 < R) :
    Summable (agmonWeight R) ∧ ∑' k : Fin 3 → ℤ, agmonWeight R k ≤ 13 * Real.pi := by
  refine sum_finset_le_of_radial_bound (φ := fun m => (R * (m : ℝ) ^ 2 + R⁻¹ * (m : ℝ) ^ 4)⁻¹)
    (B := 13 * Real.pi)
    (fun k => by
      unfold agmonWeight; split_ifs
      · exact le_refl 0
      · have := kNormSq_pos_of_ne_zero ‹k ≠ 0›; positivity)
    (by unfold agmonWeight; simp)
    (fun k hk => by
      unfold agmonWeight; simp only [hk, ↓reduceIte]
      have hm_pos : (0 : ℝ) < (kMaxAbs k : ℝ) :=
        Nat.cast_pos.mpr (Nat.pos_of_ne_zero (fun h => hk ((kMaxAbs_eq_zero_iff k).mp h)))
      have hsq : (kMaxAbs k : ℝ) ^ 2 ≤ kNormSq k := kMaxAbs_sq_le_kNormSq k
      have h4 : (kMaxAbs k : ℝ) ^ 4 ≤ (kNormSq k) ^ 2 := by nlinarith
      have hRinv : 0 < R⁻¹ := inv_pos.mpr hR
      exact inv_anti₀ (by positivity) (by nlinarith))
    (fun N => by
      have hterm : ∀ m ∈ Finset.Icc 1 N,
          (26 * (m : ℝ) ^ 2) * (R * (m : ℝ) ^ 2 + R⁻¹ * (m : ℝ) ^ 4)⁻¹ =
          26 * (R + R⁻¹ * (m : ℝ) ^ 2)⁻¹ := by
        intro m hm
        have hm_ne : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by have := (Finset.mem_Icc.mp hm).1; omega)
        have hden : R * (m : ℝ) ^ 2 + R⁻¹ * (m : ℝ) ^ 4 = (m : ℝ) ^ 2 * (R + R⁻¹ * (m : ℝ) ^ 2) := by ring
        rw [hden, mul_inv]; field_simp [hm_ne]
      rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum]
      have h_arctan_step : ∀ m : ℕ, 1 ≤ m →
          (R + R⁻¹ * (m : ℝ) ^ 2)⁻¹ ≤
            Real.arctan ((m : ℝ) / R) - Real.arctan (((m - 1 : ℕ) : ℝ) / R) := by
        intro m hm
        let a : ℝ := ((m - 1 : ℕ) : ℝ)
        let b : ℝ := (m : ℝ)
        have hab : a < b := Nat.cast_lt.mpr (by omega)
        have hba : b - a = 1 := by dsimp only [a, b]; rw [Nat.cast_sub hm, Nat.cast_one]; ring
        have hderiv : ∀ x ∈ Set.Ioo a b,
            HasDerivAt (fun t : ℝ => Real.arctan (t / R)) ((R + R⁻¹ * x ^ 2)⁻¹) x := by
          intro x _
          have hcomp := (Real.hasDerivAt_arctan (x / R)).comp x ((hasDerivAt_id x).div_const R)
          have hval : 1 / (1 + (x / R) ^ 2) * (1 / R) = (R + R⁻¹ * x ^ 2)⁻¹ := by
            have hR_ne : R ≠ 0 := ne_of_gt hR
            have hden1 : 1 + (x / R) ^ 2 ≠ 0 := by positivity
            have hden2 : R + R⁻¹ * x ^ 2 ≠ 0 := by positivity
            field_simp [hR_ne, hden1, hden2]
          rw [hval] at hcomp
          exact hcomp
        obtain ⟨c, hc, hslope⟩ := exists_hasDerivAt_eq_slope (fun t : ℝ => Real.arctan (t / R))
          (fun x => (R + R⁻¹ * x ^ 2)⁻¹) hab
          (Real.continuous_arctan.comp (continuous_id.div_const R)).continuousOn hderiv
        rw [hba, div_one] at hslope
        rw [← hslope]
        have hc_nn : 0 ≤ c := le_trans (Nat.cast_nonneg _) (le_of_lt hc.1)
        have hc2 : c ^ 2 ≤ b ^ 2 := by nlinarith [hc.2]
        have hRinv : 0 < R⁻¹ := inv_pos.mpr hR
        exact inv_anti₀ (by positivity) (by nlinarith)
      have h_le_arc : ∀ M : ℕ, ∑ m ∈ Finset.Icc 1 M, (R + R⁻¹ * (m : ℝ) ^ 2)⁻¹ ≤
          Real.arctan ((M : ℝ) / R) := by
        intro M
        induction M with
        | zero => simp [Real.arctan_zero]
        | succ n ih =>
          have hsplit : Finset.Icc 1 (n + 1) = insert (n + 1) (Finset.Icc 1 n) := by
            ext a; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
          rw [hsplit, Finset.sum_insert (by simp)]
          have hstep := h_arctan_step (n + 1) (by omega)
          simp only [Nat.add_sub_cancel] at hstep
          linarith
      linarith [h_le_arc N, Real.arctan_lt_pi_div_two ((N : ℝ) / R)])
    (fun m _ => by positivity)

-- ============================================================================
-- SECTION 3: POINTWISE 3D FOURIER INVERSION FOR `C²` PERIODIC FUNCTIONS
-- ============================================================================

private theorem fourierChar1D_conj (n : ℤ) (t : ℝ) :
    starRingEnd ℂ (fourierChar1D n t) = fourierChar1D (-n) t := by
  unfold fourierChar1D
  rw [← Complex.exp_conj]
  congr 1
  simp only [map_mul, map_neg, map_ofNat, Complex.conj_ofReal, Complex.conj_I, Int.cast_neg]
  have hk : starRingEnd ℂ (n : ℂ) = (n : ℂ) := by
    rw [← Complex.ofReal_intCast, Complex.conj_ofReal]
  rw [hk]; ring

private theorem conj_intervalIntegral_unit (φ : ℝ → ℂ) :
    starRingEnd ℂ (∫ t in (0 : ℝ)..1, φ t) = ∫ t in (0 : ℝ)..1, starRingEnd ℂ (φ t) := by
  rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1),
      intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1), ← integral_conj]

private theorem fourierCoeff3D_conj_neg (f : R3 → ℝ) (k : Fin 3 → ℤ) :
    starRingEnd ℂ (fourierCoeff3D f k) = fourierCoeff3D f (-k) := by
  unfold fourierCoeff3D
  rw [conj_intervalIntegral_unit]
  refine intervalIntegral.integral_congr fun x _ => ?_
  rw [conj_intervalIntegral_unit]
  refine intervalIntegral.integral_congr fun y _ => ?_
  rw [conj_intervalIntegral_unit]
  refine intervalIntegral.integral_congr fun z _ => ?_
  simp only [map_mul, Complex.conj_ofReal, fourierChar1D_conj, Pi.neg_apply]

private theorem norm_fourierChar1D (n : ℤ) (t : ℝ) : ‖fourierChar1D n t‖ = 1 := by
  unfold fourierChar1D
  have h : -2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) * (t : ℂ) =
      ((-2 * Real.pi * (n : ℝ) * t : ℝ) : ℂ) * Complex.I := by push_cast; ring
  rw [h, Complex.norm_exp_ofReal_mul_I]

private theorem intervalIntegral_fourierChar1D_mul (m k : ℤ) :
    (∫ t in (0 : ℝ)..1, fourierChar1D k t * starRingEnd ℂ (fourierChar1D m t)) =
      if m = k then 1 else 0 := by
  have hprod : ∀ t : ℝ, fourierChar1D k t * starRingEnd ℂ (fourierChar1D m t) =
      fourierChar1D (k - m) t := fun t => by
    rw [fourierChar1D_conj]; unfold fourierChar1D; rw [← Complex.exp_add]; congr 1; push_cast; ring
  simp_rw [hprod]
  by_cases hmk : m = k
  · subst hmk; simp only [↓reduceIte, sub_self]
    have h1 : ∀ t : ℝ, fourierChar1D 0 t = 1 := fun t => by unfold fourierChar1D; simp
    simp [h1]
  · simp only [hmk, ↓reduceIte]
    let d : ℤ := k - m
    have hd : d ≠ 0 := sub_ne_zero.mpr (Ne.symm hmk)
    let c : ℂ := -2 * (Real.pi : ℂ) * Complex.I * (d : ℂ)
    have hc_ne : c ≠ 0 := by
      dsimp only [c]
      exact mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num)
        (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)) Complex.I_ne_zero) (Int.cast_ne_zero.mpr hd)
    have hderiv : ∀ t ∈ Set.uIcc (0 : ℝ) 1,
        HasDerivAt (fun s : ℝ => c⁻¹ * fourierChar1D d s) (fourierChar1D d t) t := by
      intro t _
      have hlin : HasDerivAt (fun s : ℝ => c * (s : ℂ)) c t := by
        simpa using ((hasDerivAt_id t).ofReal_comp).const_mul c
      have hexp : HasDerivAt (fourierChar1D d) (c * fourierChar1D d t) t := by
        have h := hlin.cexp
        have hfun : (fun s : ℝ => Complex.exp (c * (s : ℂ))) = fourierChar1D d := rfl
        have heq : Complex.exp (c * (t : ℂ)) * c = c * fourierChar1D d t := by
          unfold fourierChar1D; dsimp only [c]; ring
        rw [hfun, heq] at h
        exact h
      have hmul := hexp.const_mul c⁻¹
      have hsimp : c⁻¹ * (c * fourierChar1D d t) = fourierChar1D d t := by
        rw [← mul_assoc, inv_mul_cancel₀ hc_ne, one_mul]
      rwa [hsimp] at hmul
    have hcont : Continuous (fourierChar1D d) :=
      Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal)
    have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
      (hcont.intervalIntegrable (μ := volume) 0 1)
    have h1 : fourierChar1D d 1 = 1 := by
      unfold fourierChar1D
      have h : -2 * (Real.pi : ℂ) * Complex.I * (d : ℂ) * ((1 : ℝ) : ℂ) =
          ((-d : ℤ) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by push_cast; ring
      rw [h]; exact Complex.exp_int_mul_two_pi_mul_I (-d)
    have h0 : fourierChar1D d 0 = 1 := by unfold fourierChar1D; simp
    rw [hftc, h1, h0, sub_self]

private theorem isPeriodic3D_laplacianScalar_5c {f : R3 → ℝ} (hf : ContDiff ℝ 2 f) (hpf : IsPeriodic3D f) :
    IsPeriodic3D (laplacianScalar f) := by
  have hf1 : ContDiff ℝ 1 f := hf.of_le (by rw [← one_add_one_eq_two]; exact le_self_add)
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
  intro x i; unfold laplacianScalar; rw [haxis 0 x i, haxis 1 x i, haxis 2 x i]

/-- **Absolute Summability of 3D Fourier Coefficients for `C²` Periodic Functions:** (`0 sorryAx`). -/
theorem summable_norm_fourierCoeff3D_of_contDiff_two
    {f : R3 → ℝ} (hf : ContDiff ℝ 2 f) (hpf : IsPeriodic3D f) :
    Summable (fun k : Fin 3 → ℤ => ‖fourierCoeff3D f k‖) := by
  have hlat := summable_and_tsum_invKNormSqSq_le.1
  have hlap_cont : Continuous (laplacianScalar f) :=
    ((continuous_sndPartial_of_contDiff hf 0 0).add
     (continuous_sndPartial_of_contDiff hf 1 1)).add
    (continuous_sndPartial_of_contDiff hf 2 2)
  have hlap_sum : Summable (fun k : Fin 3 → ℤ => ‖fourierCoeff3D (laplacianScalar f) k‖ ^ 2) :=
    (hasSum_sq_fourierCoeff3D hlap_cont (isPeriodic3D_laplacianScalar_5c hf hpf)).summable
  let dom : (Fin 3 → ℤ) → ℝ := fun k =>
    (if k = 0 then ‖fourierCoeff3D f 0‖ else 0) +
    (1 / 2 : ℝ) * invKNormSqSq k +
    (1 / (32 * Real.pi ^ 4)) * ‖fourierCoeff3D (laplacianScalar f) k‖ ^ 2
  have hdom_sum : Summable dom :=
    ((summable_of_ne_finset_zero (s := {0}) (fun k hk => by
        simp only [Finset.mem_singleton] at hk; simp [hk])).add
      (hlat.mul_left (1 / 2 : ℝ))).add
      (hlap_sum.mul_left (1 / (32 * Real.pi ^ 4)))
  refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun k => ?_) hdom_sum
  dsimp only [dom]
  by_cases hk : k = 0
  · subst hk; simp only [↓reduceIte, invKNormSqSq, mul_zero, add_zero]
    have : 0 ≤ 1 / (32 * Real.pi ^ 4) * ‖fourierCoeff3D (laplacianScalar f) 0‖ ^ 2 := by positivity
    linarith
  · simp only [hk, ↓reduceIte, zero_add, invKNormSqSq]
    have hnorm := congrArg norm (fourierCoeff3D_laplacianScalar hf hpf k)
    have hcoeff : ‖(-4 : ℂ) * (Real.pi : ℂ) ^ 2 *
        ((k 0 : ℂ) ^ 2 + (k 1 : ℂ) ^ 2 + (k 2 : ℂ) ^ 2)‖ = 4 * Real.pi ^ 2 * kNormSq k := by
      have hk_eq : (-4 : ℂ) * (Real.pi : ℂ) ^ 2 *
          ((k 0 : ℂ) ^ 2 + (k 1 : ℂ) ^ 2 + (k 2 : ℂ) ^ 2) =
          ((-4 * Real.pi ^ 2 * kNormSq k : ℝ) : ℂ) := by unfold kNormSq; push_cast; ring
      have hk_pos : 0 < kNormSq k := kNormSq_pos_of_ne_zero hk
      have hpos4 : 0 < 4 * Real.pi ^ 2 * kNormSq k := by positivity
      rw [hk_eq, Complex.norm_real, Real.norm_eq_abs, abs_of_neg (by linarith)]; ring
    rw [norm_mul, hcoeff] at hnorm
    have hk_pos : 0 < kNormSq k := kNormSq_pos_of_ne_zero hk
    have h_eq : ‖fourierCoeff3D f k‖ =
        (kNormSq k)⁻¹ * (‖fourierCoeff3D (laplacianScalar f) k‖ / (4 * Real.pi ^ 2)) := by
      have h4 : 4 * Real.pi ^ 2 * kNormSq k ≠ 0 := by positivity
      field_simp [h4]; linarith
    rw [h_eq]
    have hyoung : 0 ≤ ((kNormSq k)⁻¹ - ‖fourierCoeff3D (laplacianScalar f) k‖ / (4 * Real.pi ^ 2)) ^ 2 :=
      sq_nonneg _
    have hpi_ne : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
    have hsq2 : (1 / 2 : ℝ) * (‖fourierCoeff3D (laplacianScalar f) k‖ / (4 * Real.pi ^ 2)) ^ 2 =
        1 / (32 * Real.pi ^ 4) * ‖fourierCoeff3D (laplacianScalar f) k‖ ^ 2 := by
      field_simp [hpi_ne]; ring
    nlinarith [hyoung, hsq2]

/-- **MAIN THEOREM 3 OF MILESTONE 5C (Pointwise 3D Fourier Inversion & `L∞ ≤ ℓ¹` Bound):**
    For EVERY `C²` periodic scalar field `f : R3 → ℝ` and EVERY `x ∈ ℝ³`:
      `(f x : ℂ) = ∑' k : ℤ³, fourierCoeff3D f k * conj(e_k(x))` and
      `|f(x)| ≤ ∑' k : ℤ³, ‖fourierCoeff3D f k‖` (`0 sorryAx`). -/
private theorem continuous_finset_sum_5c {α : Type*} [DecidableEq α] {s : Finset α} {X : Type*} [TopologicalSpace X]
    (φ : α → X → ℂ) (hφ : ∀ m ∈ s, Continuous (φ m)) :
    Continuous (fun x => ∑ m ∈ s, φ m x) := by
  induction s using Finset.induction_on with
  | empty => simpa using continuous_const
  | insert a t hat ih =>
    have heq : (fun x => ∑ m ∈ insert a t, φ m x) = (fun x => φ a x + ∑ m ∈ t, φ m x) :=
      funext fun x => Finset.sum_insert hat
    rw [heq]
    exact (hφ a (Finset.mem_insert_self a t)).add
      (ih fun m hm => hφ m (Finset.mem_insert_of_mem hm))

private theorem integral_finset_sum_unit {α : Type*} [DecidableEq α] (s : Finset α) (φ : α → ℝ → ℂ)
    (hφ : ∀ m ∈ s, Continuous (φ m)) :
    (∫ t in (0 : ℝ)..1, ∑ m ∈ s, φ m t) = ∑ m ∈ s, ∫ t in (0 : ℝ)..1, φ m t := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a t hat ih =>
    have heq : (fun r => ∑ m ∈ insert a t, φ m r) = (fun r => φ a r + ∑ m ∈ t, φ m r) :=
      funext fun r => Finset.sum_insert hat
    have hc_a : Continuous (φ a) := hφ a (Finset.mem_insert_self a t)
    have hc_t : Continuous (fun r => ∑ m ∈ t, φ m r) :=
      continuous_finset_sum_5c φ fun m hm => hφ m (Finset.mem_insert_of_mem hm)
    rw [heq, intervalIntegral.integral_add (hc_a.intervalIntegrable 0 1) (hc_t.intervalIntegrable 0 1),
        Finset.sum_insert hat, ih fun m hm => hφ m (Finset.mem_insert_of_mem hm)]

private theorem continuous_param_integral_unit {Y : Type*} [MetricSpace Y] [ProperSpace Y]
    {F : Y × ℝ → ℂ} (hF : Continuous F) :
    Continuous (fun y : Y => ∫ t in (0 : ℝ)..1, F (y, t)) := by
  have h_eq : (fun y : Y => ∫ t in (0 : ℝ)..1, F (y, t)) =
      (fun y : Y => ∫ t, F (y, t) ∂(volume.restrict (Set.Icc (0 : ℝ) 1))) := by
    funext y
    rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1),
        ← MeasureTheory.integral_Icc_eq_integral_Ioc]
  rw [h_eq]
  have : IsFiniteMeasure (volume.restrict (Set.Icc (0 : ℝ) 1)) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact isCompact_Icc.measure_lt_top⟩
  refine continuous_iff_continuousAt.mpr fun y₀ => ?_
  have hball : Metric.closedBall y₀ 1 ∈ 𝓝 y₀ := Metric.closedBall_mem_nhds y₀ zero_lt_one
  obtain ⟨C, hC⟩ := ((isCompact_closedBall y₀ 1).prod isCompact_Icc).exists_bound_of_continuousOn
    hF.continuousOn (s := Metric.closedBall y₀ 1 ×ˢ Set.Icc (0 : ℝ) 1)
  refine continuousAt_of_dominated
    (Eventually.of_forall fun y => (hF.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable)
    ?_ (integrable_const C)
    (Eventually.of_forall fun t => (hF.comp (continuous_id.prodMk continuous_const)).continuousAt)
  filter_upwards [hball] with y hy
  filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
  exact hC (y, t) ⟨hy, ht⟩

set_option maxHeartbeats 400000 in
private theorem intervalIntegral_sub_on_unit {φ ψ : ℝ → ℂ}
    (hφ : Continuous φ) (hψ : Continuous ψ) :
    (∫ t in (0 : ℝ)..1, φ t) - (∫ t in (0 : ℝ)..1, ψ t) =
      ∫ t in (0 : ℝ)..1, (φ t - ψ t) :=
  (intervalIntegral.integral_sub (hφ.intervalIntegrable 0 1) (hψ.intervalIntegrable 0 1)).symm

private theorem tripleIntegral_unit_sub
    {F G : ℝ → ℝ → ℝ → ℂ}
    (hF : Continuous (fun q : (ℝ × ℝ) × ℝ => F q.1.1 q.1.2 q.2))
    (hG : Continuous (fun q : (ℝ × ℝ) × ℝ => G q.1.1 q.1.2 q.2)) :
    (∫ x in (0 : ℝ)..1, ∫ y in (0 : ℝ)..1, ∫ z in (0 : ℝ)..1, F x y z) -
    (∫ x in (0 : ℝ)..1, ∫ y in (0 : ℝ)..1, ∫ z in (0 : ℝ)..1, G x y z) =
    ∫ x in (0 : ℝ)..1, ∫ y in (0 : ℝ)..1, ∫ z in (0 : ℝ)..1, (F x y z - G x y z) := by
  have hFz : Continuous (fun p : ℝ × ℝ => ∫ z in (0 : ℝ)..1, F p.1 p.2 z) :=
    continuous_param_integral_unit (Y := ℝ × ℝ) (F := fun q => F q.1.1 q.1.2 q.2) hF
  have hGz : Continuous (fun p : ℝ × ℝ => ∫ z in (0 : ℝ)..1, G p.1 p.2 z) :=
    continuous_param_integral_unit (Y := ℝ × ℝ) (F := fun q => G q.1.1 q.1.2 q.2) hG
  have hFx : Continuous (fun x : ℝ => ∫ y in (0 : ℝ)..1, ∫ z in (0 : ℝ)..1, F x y z) :=
    continuous_param_integral_unit (Y := ℝ)
      (F := fun p : ℝ × ℝ => ∫ z in (0 : ℝ)..1, F p.1 p.2 z) hFz
  have hGx : Continuous (fun x : ℝ => ∫ y in (0 : ℝ)..1, ∫ z in (0 : ℝ)..1, G x y z) :=
    continuous_param_integral_unit (Y := ℝ)
      (F := fun p : ℝ × ℝ => ∫ z in (0 : ℝ)..1, G p.1 p.2 z) hGz
  refine (intervalIntegral_sub_on_unit hFx hGx).trans ?_
  refine intervalIntegral.integral_congr fun x _ => ?_
  have hFy : Continuous (fun y : ℝ => ∫ z in (0 : ℝ)..1, F x y z) :=
    hFz.comp ((continuous_const (y := x)).prodMk continuous_id)
  have hGy : Continuous (fun y : ℝ => ∫ z in (0 : ℝ)..1, G x y z) :=
    hGz.comp ((continuous_const (y := x)).prodMk continuous_id)
  refine (intervalIntegral_sub_on_unit hFy hGy).trans ?_
  refine intervalIntegral.integral_congr fun y _ => ?_
  have hFz' : Continuous (fun z : ℝ => F x y z) :=
    hF.comp ((continuous_const (y := (x, y))).prodMk continuous_id)
  have hGz' : Continuous (fun z : ℝ => G x y z) :=
    hG.comp ((continuous_const (y := (x, y))).prodMk continuous_id)
  exact intervalIntegral_sub_on_unit hFz' hGz'

private theorem fourierCoeff3D_sub_complex {A B : R3 → ℂ} (hA : Continuous A) (hB : Continuous B)
    (k : Fin 3 → ℤ) :
    (∫ x in (0 : ℝ)..1, ∫ y in (0 : ℝ)..1, ∫ z in (0 : ℝ)..1,
      fourierChar1D (k 0) x * fourierChar1D (k 1) y * fourierChar1D (k 2) z * A (vec3 x y z)) -
    (∫ x in (0 : ℝ)..1, ∫ y in (0 : ℝ)..1, ∫ z in (0 : ℝ)..1,
      fourierChar1D (k 0) x * fourierChar1D (k 1) y * fourierChar1D (k 2) z * B (vec3 x y z)) =
    ∫ x in (0 : ℝ)..1, ∫ y in (0 : ℝ)..1, ∫ z in (0 : ℝ)..1,
      fourierChar1D (k 0) x * fourierChar1D (k 1) y * fourierChar1D (k 2) z *
        (A (vec3 x y z) - B (vec3 x y z)) := by
  have hc1 : ∀ (n : ℤ), Continuous (fourierChar1D n) := fun n =>
    Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal)
  have hvec : Continuous (fun q : (ℝ × ℝ) × ℝ => vec3 q.1.1 q.1.2 q.2) :=
    continuous_pi fun j => match j with
      | ⟨0, _⟩ => continuous_fst.comp continuous_fst
      | ⟨1, _⟩ => continuous_snd.comp continuous_fst
      | ⟨2, _⟩ => continuous_snd
  have hchar : Continuous (fun q : (ℝ × ℝ) × ℝ =>
      fourierChar1D (k 0) q.1.1 * fourierChar1D (k 1) q.1.2 * fourierChar1D (k 2) q.2) :=
    (((hc1 (k 0)).comp (continuous_fst.comp continuous_fst)).mul
      ((hc1 (k 1)).comp (continuous_snd.comp continuous_fst))).mul
      ((hc1 (k 2)).comp continuous_snd)
  have hF : Continuous (fun q : (ℝ × ℝ) × ℝ =>
      fourierChar1D (k 0) q.1.1 * fourierChar1D (k 1) q.1.2 * fourierChar1D (k 2) q.2 *
        A (vec3 q.1.1 q.1.2 q.2)) := hchar.mul (hA.comp hvec)
  have hG : Continuous (fun q : (ℝ × ℝ) × ℝ =>
      fourierChar1D (k 0) q.1.1 * fourierChar1D (k 1) q.1.2 * fourierChar1D (k 2) q.2 *
        B (vec3 q.1.1 q.1.2 q.2)) := hchar.mul (hB.comp hvec)
  refine (tripleIntegral_unit_sub
    (F := fun x y z => fourierChar1D (k 0) x * fourierChar1D (k 1) y * fourierChar1D (k 2) z * A (vec3 x y z))
    (G := fun x y z => fourierChar1D (k 0) x * fourierChar1D (k 1) y * fourierChar1D (k 2) z * B (vec3 x y z))
    hF hG).trans ?_
  refine intervalIntegral.integral_congr fun x _ => ?_
  refine intervalIntegral.integral_congr fun y _ => ?_
  refine intervalIntegral.integral_congr fun z _ => ?_
  exact (mul_sub _ _ _).symm

theorem fourier_inversion_3d_of_contDiff_two
    {f : R3 → ℝ} (hf : ContDiff ℝ 2 f) (hpf : IsPeriodic3D f) :
    (∀ x : R3, (f x : ℂ) =
      ∑' k : Fin 3 → ℤ, fourierCoeff3D f k *
        starRingEnd ℂ (fourierChar1D (k 0) (x 0) * fourierChar1D (k 1) (x 1) *
          fourierChar1D (k 2) (x 2))) ∧
    (∀ x : R3, |f x| ≤ ∑' k : Fin 3 → ℤ, ‖fourierCoeff3D f k‖) := by
  have hsum_norm := summable_norm_fourierCoeff3D_of_contDiff_two hf hpf
  let e_pos : (Fin 3 → ℤ) → R3 → ℂ := fun m x =>
    starRingEnd ℂ (fourierChar1D (m 0) (x 0) * fourierChar1D (m 1) (x 1) *
      fourierChar1D (m 2) (x 2))
  have he_norm : ∀ m x, ‖e_pos m x‖ = 1 := fun m x => by
    dsimp only [e_pos]
    rw [Complex.norm_conj, norm_mul, norm_mul, norm_fourierChar1D, norm_fourierChar1D,
        norm_fourierChar1D, mul_one, mul_one]
  have he_cont : ∀ m, Continuous (e_pos m) := fun m => by
    have hc1 : ∀ (n : ℤ) (i : Fin 3), Continuous (fun x : R3 => fourierChar1D n (x i)) := fun n i =>
      (Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal)).comp
        (continuous_apply i)
    exact Complex.continuous_conj.comp (((hc1 (m 0) 0).mul (hc1 (m 1) 1)).mul (hc1 (m 2) 2))
  let S : R3 → ℂ := fun x => ∑' m : Fin 3 → ℤ, fourierCoeff3D f m * e_pos m x
  let g : R3 → ℝ := fun x => (S x).re
  have hS_cont : Continuous S :=
    continuous_tsum (fun m => continuous_const.mul (he_cont m)) hsum_norm fun m x => by
      rw [norm_mul, he_norm, mul_one]
  have hg_cont : Continuous g := Complex.continuous_re.comp hS_cont
  have hS_real : ∀ x : R3, starRingEnd ℂ (S x) = S x := by
    intro x; dsimp only [S]
    have hsumm : Summable (fun m : Fin 3 → ℤ => fourierCoeff3D f m * e_pos m x) :=
      Summable.of_norm (by simpa only [norm_mul, he_norm, mul_one] using hsum_norm)
    have hconj : starRingEnd ℂ (∑' m : Fin 3 → ℤ, fourierCoeff3D f m * e_pos m x) =
        ∑' m : Fin 3 → ℤ, starRingEnd ℂ (fourierCoeff3D f m * e_pos m x) :=
      (Complex.conjCLE.toContinuousLinearMap.hasSum hsumm.hasSum).tsum_eq.symm
    have h_reidx : (∑' m : Fin 3 → ℤ, fourierCoeff3D f (-m) * e_pos (-m) x) =
        ∑' m : Fin 3 → ℤ, fourierCoeff3D f m * e_pos m x :=
      Equiv.tsum_eq (Equiv.neg (Fin 3 → ℤ)) (fun m => fourierCoeff3D f m * e_pos m x)
    rw [hconj, ← h_reidx]
    refine tsum_congr fun m => ?_
    dsimp only [e_pos]
    rw [map_mul, fourierCoeff3D_conj_neg]
    simp only [map_mul, fourierChar1D_conj, Pi.neg_apply]
  have hg_coe : ∀ x : R3, (g x : ℂ) = S x := fun x => by
    have him := congrArg Complex.im (hS_real x)
    rw [Complex.conj_im] at him
    apply Complex.ext
    · rfl
    · simp only [Complex.ofReal_im]; linarith
  have hg_per : IsPeriodic3D g := by
    intro x i
    have h1 : ∀ m : Fin 3 → ℤ, e_pos m (x + basisVec i) = e_pos m x := by
      intro m; dsimp only [e_pos]
      have hchar : ∀ (n : ℤ) (t : ℝ), fourierChar1D n (t + 1) = fourierChar1D n t := fun n t => by
        unfold fourierChar1D
        have hadd : -2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) * ((t + 1 : ℝ) : ℂ) =
            (-2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) * (t : ℂ)) +
            ((-n : ℤ) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by push_cast; ring
        rw [hadd, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]
      have hb0 : (x + basisVec 0) 0 = x 0 + 1 ∧ (x + basisVec 0) 1 = x 1 ∧ (x + basisVec 0) 2 = x 2 := by
        simp [basisVec]
      have hb1 : (x + basisVec 1) 0 = x 0 ∧ (x + basisVec 1) 1 = x 1 + 1 ∧ (x + basisVec 1) 2 = x 2 := by
        simp [basisVec]
      have hb2 : (x + basisVec 2) 0 = x 0 ∧ (x + basisVec 2) 1 = x 1 ∧ (x + basisVec 2) 2 = x 2 + 1 := by
        simp [basisVec]
      fin_cases i
      · change starRingEnd ℂ (fourierChar1D (m 0) ((x + basisVec 0) 0) *
            fourierChar1D (m 1) ((x + basisVec 0) 1) * fourierChar1D (m 2) ((x + basisVec 0) 2)) = _
        rw [hb0.1, hb0.2.1, hb0.2.2, hchar]
      · change starRingEnd ℂ (fourierChar1D (m 0) ((x + basisVec 1) 0) *
            fourierChar1D (m 1) ((x + basisVec 1) 1) * fourierChar1D (m 2) ((x + basisVec 1) 2)) = _
        rw [hb1.1, hb1.2.1, hb1.2.2, hchar]
      · change starRingEnd ℂ (fourierChar1D (m 0) ((x + basisVec 2) 0) *
            fourierChar1D (m 1) ((x + basisVec 2) 1) * fourierChar1D (m 2) ((x + basisVec 2) 2)) = _
        rw [hb2.1, hb2.2.1, hb2.2.2, hchar]
    dsimp only [g, S]; simp_rw [h1]
  have hfc_eq : ∀ k : Fin 3 → ℤ, fourierCoeff3D g k = fourierCoeff3D f k := by
    intro k
    have h_eps : ∀ ε : ℝ, 0 < ε → ‖fourierCoeff3D g k - fourierCoeff3D f k‖ ≤ ε := by
      intro ε hε
      obtain ⟨s₀, hs₀⟩ := Metric.tendsto_atTop.mp hsum_norm.hasSum ε hε
      let s : Finset (Fin 3 → ℤ) := insert k s₀
      have htail_lt : (∑' m, ‖fourierCoeff3D f m‖) - ∑ m ∈ s, ‖fourierCoeff3D f m‖ < ε := by
        have hdist := hs₀ s (Finset.subset_insert k s₀)
        rw [Real.dist_eq, abs_lt] at hdist; linarith
      let Ss : R3 → ℂ := fun x => ∑ m ∈ s, fourierCoeff3D f m * e_pos m x
      have hSs_cont : Continuous Ss :=
        continuous_finset_sum_5c (fun m x => fourierCoeff3D f m * e_pos m x)
          fun m _ => continuous_const.mul (he_cont m)
      have h_unif : ∀ x : R3, ‖S x - Ss x‖ ≤ ε := by
        intro x
        have hsumm_x : Summable (fun m => fourierCoeff3D f m * e_pos m x) :=
          Summable.of_norm (by simpa only [norm_mul, he_norm, mul_one] using hsum_norm)
        have h_ind_C : HasSum (fun m => if m ∈ s then fourierCoeff3D f m * e_pos m x else 0) (Ss x) := by
          refine tendsto_atTop_of_eventually_const (i₀ := s) fun t ht => ?_
          rw [← Finset.sum_filter, Finset.filter_mem_eq_inter, Finset.inter_eq_right.mpr ht]
        have h_ind_R : HasSum (fun m => if m ∈ s then ‖fourierCoeff3D f m‖ else 0)
            (∑ m ∈ s, ‖fourierCoeff3D f m‖) := by
          refine tendsto_atTop_of_eventually_const (i₀ := s) fun t ht => ?_
          rw [← Finset.sum_filter, Finset.filter_mem_eq_inter, Finset.inter_eq_right.mpr ht]
        have hsub_sum : HasSum (fun m => if m ∈ s then (0 : ℂ) else fourierCoeff3D f m * e_pos m x)
            (S x - Ss x) := by
          have h3 := hsumm_x.hasSum.sub h_ind_C
          have heq : (fun m => fourierCoeff3D f m * e_pos m x -
              if m ∈ s then fourierCoeff3D f m * e_pos m x else 0) =
              (fun m => if m ∈ s then (0 : ℂ) else fourierCoeff3D f m * e_pos m x) := by
            funext m; split_ifs <;> simp
          rwa [heq] at h3
        have hnorm_tail : Summable (fun m => ‖if m ∈ s then (0 : ℂ) else fourierCoeff3D f m * e_pos m x‖) :=
          Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
            (fun m => by split_ifs; simp; rw [norm_mul, he_norm, mul_one]) hsum_norm
        have hle1 : ‖S x - Ss x‖ ≤ ∑' m, ‖if m ∈ s then (0 : ℂ) else fourierCoeff3D f m * e_pos m x‖ := by
          rw [← hsub_sum.tsum_eq]; exact norm_tsum_le_tsum_norm hnorm_tail
        have hsum_rem : HasSum (fun m => ‖if m ∈ s then (0 : ℂ) else fourierCoeff3D f m * e_pos m x‖)
            ((∑' m, ‖fourierCoeff3D f m‖) - ∑ m ∈ s, ‖fourierCoeff3D f m‖) := by
          have h3 := hsum_norm.hasSum.sub h_ind_R
          have heq : (fun m => ‖fourierCoeff3D f m‖ - if m ∈ s then ‖fourierCoeff3D f m‖ else 0) =
              (fun m => ‖if m ∈ s then (0 : ℂ) else fourierCoeff3D f m * e_pos m x‖) := by
            funext m; split_ifs
            · simp
            · rw [sub_zero, norm_mul, he_norm, mul_one]
          rwa [heq] at h3
        rw [hsum_rem.tsum_eq] at hle1
        exact le_trans hle1 (le_of_lt htail_lt)
      have hfc_Ss : (∫ x in (0 : ℝ)..1, ∫ y in (0 : ℝ)..1, ∫ z in (0 : ℝ)..1,
          fourierChar1D (k 0) x * fourierChar1D (k 1) y * fourierChar1D (k 2) z * Ss (vec3 x y z)) =
          fourierCoeff3D f k := by
        have hc_char : ∀ n : ℤ, Continuous (fourierChar1D n) := fun n =>
          Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal)
        have h_z : ∀ x y : ℝ,
            (∫ z in (0 : ℝ)..1, fourierChar1D (k 0) x * fourierChar1D (k 1) y *
              fourierChar1D (k 2) z * Ss (vec3 x y z)) =
            ∑ m ∈ s, fourierCoeff3D f m *
              (fourierChar1D (k 0) x * starRingEnd ℂ (fourierChar1D (m 0) x)) *
              (fourierChar1D (k 1) y * starRingEnd ℂ (fourierChar1D (m 1) y)) *
              (if m 2 = k 2 then (1 : ℂ) else 0) := by
          intro x y
          let φz : (Fin 3 → ℤ) → ℝ → ℂ := fun m z =>
            (fourierCoeff3D f m *
              (fourierChar1D (k 0) x * starRingEnd ℂ (fourierChar1D (m 0) x)) *
              (fourierChar1D (k 1) y * starRingEnd ℂ (fourierChar1D (m 1) y))) *
              (fourierChar1D (k 2) z * starRingEnd ℂ (fourierChar1D (m 2) z))
          have hmul : (fun z => fourierChar1D (k 0) x * fourierChar1D (k 1) y *
              fourierChar1D (k 2) z * Ss (vec3 x y z)) = (fun z => ∑ m ∈ s, φz m z) := by
            funext z; dsimp only [Ss, e_pos, vec3, φz]
            rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun m _ => ?_
            simp only [map_mul]; ring
          rw [hmul, integral_finset_sum_unit s φz (fun m _ =>
            continuous_const.mul ((hc_char (k 2)).mul (Complex.continuous_conj.comp (hc_char (m 2)))))]
          refine Finset.sum_congr rfl fun m _ => ?_
          dsimp only [φz]
          rw [intervalIntegral.integral_const_mul, intervalIntegral_fourierChar1D_mul]
        simp_rw [h_z]
        have h_y : ∀ x : ℝ,
            (∫ y in (0 : ℝ)..1, ∑ m ∈ s, fourierCoeff3D f m *
              (fourierChar1D (k 0) x * starRingEnd ℂ (fourierChar1D (m 0) x)) *
              (fourierChar1D (k 1) y * starRingEnd ℂ (fourierChar1D (m 1) y)) *
              (if m 2 = k 2 then (1 : ℂ) else 0)) =
            ∑ m ∈ s, fourierCoeff3D f m *
              (fourierChar1D (k 0) x * starRingEnd ℂ (fourierChar1D (m 0) x)) *
              (if m 1 = k 1 then (1 : ℂ) else 0) * (if m 2 = k 2 then (1 : ℂ) else 0) := by
          intro x
          let φy : (Fin 3 → ℤ) → ℝ → ℂ := fun m y =>
            fourierCoeff3D f m *
              (fourierChar1D (k 0) x * starRingEnd ℂ (fourierChar1D (m 0) x)) *
              (fourierChar1D (k 1) y * starRingEnd ℂ (fourierChar1D (m 1) y)) *
              (if m 2 = k 2 then (1 : ℂ) else 0)
          rw [integral_finset_sum_unit s φy (fun m _ =>
            ((continuous_const.mul ((hc_char (k 1)).mul (Complex.continuous_conj.comp (hc_char (m 1))))).mul
              continuous_const))]
          refine Finset.sum_congr rfl fun m _ => ?_
          have hsep : φy m = (fun y => (fourierCoeff3D f m *
                (fourierChar1D (k 0) x * starRingEnd ℂ (fourierChar1D (m 0) x)) *
                (if m 2 = k 2 then (1 : ℂ) else 0)) *
                (fourierChar1D (k 1) y * starRingEnd ℂ (fourierChar1D (m 1) y))) := by
            funext y; dsimp only [φy]; ring
          rw [hsep, intervalIntegral.integral_const_mul, intervalIntegral_fourierChar1D_mul]; ring
        simp_rw [h_y]
        let φx : (Fin 3 → ℤ) → ℝ → ℂ := fun m x =>
          fourierCoeff3D f m *
            (fourierChar1D (k 0) x * starRingEnd ℂ (fourierChar1D (m 0) x)) *
            (if m 1 = k 1 then (1 : ℂ) else 0) * (if m 2 = k 2 then (1 : ℂ) else 0)
        rw [integral_finset_sum_unit s φx (fun m _ =>
          (((continuous_const.mul ((hc_char (k 0)).mul (Complex.continuous_conj.comp (hc_char (m 0))))).mul
            continuous_const).mul continuous_const))]
        have hterm : ∀ m ∈ s, (∫ x in (0 : ℝ)..1, φx m x) = if m = k then fourierCoeff3D f k else 0 := by
          intro m _
          have hsep : φx m = (fun x => (fourierCoeff3D f m * (if m 1 = k 1 then (1 : ℂ) else 0) *
                (if m 2 = k 2 then (1 : ℂ) else 0)) *
                (fourierChar1D (k 0) x * starRingEnd ℂ (fourierChar1D (m 0) x))) := by
            funext x; dsimp only [φx]; ring
          rw [hsep, intervalIntegral.integral_const_mul, intervalIntegral_fourierChar1D_mul]
          by_cases hmk : m = k
          · subst hmk; simp
          · simp only [hmk, ↓reduceIte]
            have hex : m 0 ≠ k 0 ∨ m 1 ≠ k 1 ∨ m 2 ≠ k 2 := by
              by_contra hall; push Not at hall; apply hmk; funext i; fin_cases i <;> tauto
            rcases hex with h0 | h1 | h2
            · simp [h0]
            · simp [h1]
            · simp [h2]
        rw [Finset.sum_congr rfl hterm, Finset.sum_ite_eq']
        simp [s]
      have hdiff_int : fourierCoeff3D g k - fourierCoeff3D f k =
          ∫ x in (0 : ℝ)..1, ∫ y in (0 : ℝ)..1, ∫ z in (0 : ℝ)..1,
            fourierChar1D (k 0) x * fourierChar1D (k 1) y * fourierChar1D (k 2) z *
              (S (vec3 x y z) - Ss (vec3 x y z)) := by
        rw [← hfc_Ss]; unfold fourierCoeff3D; simp_rw [hg_coe]
        exact fourierCoeff3D_sub_complex hS_cont hSs_cont k
      rw [hdiff_int]
      have h1_abs : |(1 : ℝ) - 0| = 1 := by norm_num
      have hb_z : ∀ x y : ℝ, ‖∫ z in (0 : ℝ)..1, fourierChar1D (k 0) x * fourierChar1D (k 1) y *
          fourierChar1D (k 2) z * (S (vec3 x y z) - Ss (vec3 x y z))‖ ≤ ε := fun x y => by
        have h := intervalIntegral.norm_integral_le_of_norm_le_const (C := ε) (a := (0 : ℝ)) (b := 1)
          (f := fun z => fourierChar1D (k 0) x * fourierChar1D (k 1) y *
            fourierChar1D (k 2) z * (S (vec3 x y z) - Ss (vec3 x y z))) fun z _ => by
          rw [norm_mul, norm_mul, norm_mul, norm_fourierChar1D, norm_fourierChar1D,
              norm_fourierChar1D, one_mul, one_mul, one_mul]
          exact h_unif (vec3 x y z)
        rwa [h1_abs, mul_one] at h
      have hb_y : ∀ x : ℝ, ‖∫ y in (0 : ℝ)..1, ∫ z in (0 : ℝ)..1, fourierChar1D (k 0) x *
          fourierChar1D (k 1) y * fourierChar1D (k 2) z * (S (vec3 x y z) - Ss (vec3 x y z))‖ ≤ ε := fun x => by
        have h := intervalIntegral.norm_integral_le_of_norm_le_const (C := ε) (a := (0 : ℝ)) (b := 1)
          fun y _ => hb_z x y
        rwa [h1_abs, mul_one] at h
      have hb_x := intervalIntegral.norm_integral_le_of_norm_le_const (C := ε) (a := (0 : ℝ)) (b := 1)
        fun x _ => hb_y x
      rwa [h1_abs, mul_one] at hb_x
    have hnorm0 : ‖fourierCoeff3D g k - fourierCoeff3D f k‖ = 0 := by
      refine le_antisymm ?_ (norm_nonneg _)
      by_contra hgt; push Not at hgt
      have h := h_eps (‖fourierCoeff3D g k - fourierCoeff3D f k‖ / 2) (half_pos hgt)
      linarith
    exact sub_eq_zero.mp (norm_eq_zero.mp hnorm0)
  have hdiff_per : IsPeriodic3D (fun x => f x - g x) := fun x i => by simp only [hpf x i, hg_per x i]
  have hdiff_cont : Continuous (fun x => f x - g x) := hf.continuous.sub hg_cont
  have hparse_diff := hasSum_sq_fourierCoeff3D hdiff_cont hdiff_per
  have hzero_coeff : (fun k : Fin 3 → ℤ => ‖fourierCoeff3D (fun x => f x - g x) k‖ ^ 2) = 0 := by
    funext k
    rw [fourierCoeff3D_sub hf.continuous hg_cont k, hfc_eq k, sub_self, norm_zero]; simp
  rw [hzero_coeff] at hparse_diff
  have hint_zero : torusIntegral (fun x => (f x - g x) ^ 2) = 0 := hparse_diff.unique hasSum_zero
  have hf_eq_g : ∀ x : R3, f x = g x := fun x =>
    sub_eq_zero.mp (eq_zero_of_torusIntegral_sq_eq_zero hdiff_cont hdiff_per hint_zero x)
  constructor
  · intro x; rw [hf_eq_g x, hg_coe x]
  · intro x
    have h1 : |f x| = ‖(f x : ℂ)‖ := by rw [Complex.norm_real, Real.norm_eq_abs]
    rw [h1, hf_eq_g x, hg_coe x]
    dsimp only [S]
    have hsumm_norm_x : Summable (fun m : Fin 3 → ℤ => ‖fourierCoeff3D f m * e_pos m x‖) := by
      simpa only [norm_mul, he_norm, mul_one] using hsum_norm
    have hle := norm_tsum_le_tsum_norm hsumm_norm_x
    have heq_norm : (fun m : Fin 3 → ℤ => ‖fourierCoeff3D f m * e_pos m x‖) =
        (fun m => ‖fourierCoeff3D f m‖) := by
      funext m; rw [norm_mul, he_norm, mul_one]
    rwa [heq_norm] at hle

-- ============================================================================
-- SECTION 4: SOBOLEV EMBEDDING `H²(𝕋³) ↪ L∞(𝕋³)` & SHARP 3D AGMON INEQUALITY
-- ============================================================================

private theorem tsum_le_sqrt_mul_sqrt {a w b : (Fin 3 → ℤ) → ℝ}
    (ha : Summable a) (hw : Summable w) (hb : Summable b)
    (ha_nn : ∀ k, 0 ≤ a k) (hw_nn : ∀ k, 0 ≤ w k) (hb_nn : ∀ k, 0 ≤ b k)
    (h_pt : ∀ k, (a k) ^ 2 ≤ w k * b k) :
    (∑' k, a k) ^ 2 ≤ (∑' k, w k) * (∑' k, b k) := by
  let A := ∑' k, a k
  let W := ∑' k, w k
  let B := ∑' k, b k
  have hquad : ∀ r : ℝ, 0 ≤ r ^ 2 * W - 2 * r * A + B := by
    intro r
    have hcomb := ((hw.hasSum.mul_left (r ^ 2)).sub (ha.hasSum.mul_left (2 * r))).add hb.hasSum
    have hnn : ∀ k, 0 ≤ r ^ 2 * w k - 2 * r * a k + b k := fun k => by
      have h1 : 0 ≤ (r * Real.sqrt (w k) - Real.sqrt (b k)) ^ 2 := sq_nonneg _
      have hsq_w : Real.sqrt (w k) ^ 2 = w k := Real.sq_sqrt (hw_nn k)
      have hsq_b : Real.sqrt (b k) ^ 2 = b k := Real.sq_sqrt (hb_nn k)
      have hprod : a k ≤ Real.sqrt (w k) * Real.sqrt (b k) := by
        rw [← Real.sqrt_mul (hw_nn k)]; exact Real.le_sqrt_of_sq_le (h_pt k)
      have h2 : (r * Real.sqrt (w k) - Real.sqrt (b k)) ^ 2 =
          r ^ 2 * w k - 2 * r * (Real.sqrt (w k) * Real.sqrt (b k)) + b k := by
        nlinarith [hsq_w, hsq_b]
      by_cases hr : 0 ≤ r
      · nlinarith
      · push Not at hr
        have h3 : 0 ≤ r ^ 2 * w k := mul_nonneg (sq_nonneg _) (hw_nn k)
        have h4 : 0 ≤ -2 * r * a k := by nlinarith [ha_nn k]
        linarith [hb_nn k]
    exact hasSum_le hnn hasSum_zero hcomb
  have hW_nn : 0 ≤ W := tsum_nonneg hw_nn
  change A ^ 2 ≤ W * B
  rcases eq_or_lt_of_le hW_nn with hW0 | hW_pos
  · have hA0 : A = 0 := by
      by_contra hne
      have h1 := hquad ((B + 1) / (2 * A))
      have h2A : 2 * A ≠ 0 := mul_ne_zero (by norm_num) hne
      rw [← hW0, mul_zero, zero_sub] at h1
      have hcalc : 2 * ((B + 1) / (2 * A)) * A = B + 1 := by field_simp [h2A]
      linarith
    rw [hA0, ← hW0]; norm_num
  · have hq := hquad (A / W)
    have hmul : 0 ≤ ((A / W) ^ 2 * W - 2 * (A / W) * A + B) * W := mul_nonneg hq (le_of_lt hW_pos)
    have hW_ne : W ≠ 0 := ne_of_gt hW_pos
    have halg : ((A / W) ^ 2 * W - 2 * (A / W) * A + B) * W = W * B - A ^ 2 := by
      field_simp [hW_ne]; ring
    linarith

private theorem fourierCoeff3D_zero_eq_torusIntegral (f : R3 → ℝ) :
    fourierCoeff3D f 0 = (torusIntegral f : ℂ) := by
  unfold fourierCoeff3D torusIntegral
  have h1 : ∀ t : ℝ, fourierChar1D 0 t = 1 := fun t => by unfold fourierChar1D; simp
  simp only [Pi.zero_apply, h1, one_mul]
  simp_rw [intervalIntegral.integral_ofReal]

/-- **MAIN THEOREM 4 OF MILESTONE 5C (3D Sobolev Embedding `H²(𝕋³) ↪ L∞(𝕋³)` — Scalar):**
    `|f(x)| ≤ |∫_{𝕋³} f| + (√52 / (4π²)) * √(∫_{𝕋³} (Δf)²)` (`0 sorryAx`). -/
theorem sobolev_H2_Linf_3d_scalar
    {f : R3 → ℝ} (hf : ContDiff ℝ 2 f) (hpf : IsPeriodic3D f) (x : R3) :
    |f x| ≤ |torusIntegral f| +
      (Real.sqrt 52 / (4 * Real.pi ^ 2)) *
        Real.sqrt (torusIntegral (fun y => (laplacianScalar f y) ^ 2)) := by
  have hsum_norm := summable_norm_fourierCoeff3D_of_contDiff_two hf hpf
  have hinv := (fourier_inversion_3d_of_contDiff_two hf hpf).2 x
  have hlap_cont : Continuous (laplacianScalar f) :=
    ((continuous_sndPartial_of_contDiff hf 0 0).add
     (continuous_sndPartial_of_contDiff hf 1 1)).add
    (continuous_sndPartial_of_contDiff hf 2 2)
  have hparse_lap := hasSum_sq_fourierCoeff3D hlap_cont (isPeriodic3D_laplacianScalar_5c hf hpf)
  let tail : (Fin 3 → ℤ) → ℝ := fun k => if k = 0 then 0 else ‖fourierCoeff3D f k‖
  have htail_sum : Summable tail :=
    Summable.of_nonneg_of_le (fun k => by dsimp only [tail]; split_ifs <;> positivity)
      (fun k => by dsimp only [tail]; split_ifs; exact norm_nonneg _; exact le_refl _) hsum_norm
  have hsplit : (∑' k, ‖fourierCoeff3D f k‖) = ‖fourierCoeff3D f 0‖ + ∑' k, tail k := by
    have h0_sum : Summable (fun k : Fin 3 → ℤ => if k = 0 then ‖fourierCoeff3D f 0‖ else 0) :=
      summable_of_ne_finset_zero (s := {0}) (fun k hk => by simp only [Finset.mem_singleton] at hk; simp [hk])
    have heq : (fun k : Fin 3 → ℤ => ‖fourierCoeff3D f k‖) =
        (fun k => (if k = 0 then ‖fourierCoeff3D f 0‖ else 0) + tail k) := by
      funext k; dsimp only [tail]; split_ifs with hk
      · subst hk; simp
      · simp
    rw [heq, h0_sum.tsum_add htail_sum, tsum_ite_eq]
  have hcs := tsum_le_sqrt_mul_sqrt htail_sum summable_and_tsum_invKNormSqSq_le.1
    (hparse_lap.summable.mul_left (1 / (16 * Real.pi ^ 4)))
    (fun k => by dsimp only [tail]; split_ifs <;> positivity)
    (fun k => by unfold invKNormSqSq; split_ifs <;> positivity)
    (fun k => by positivity)
    (fun k => by
      dsimp only [tail]; unfold invKNormSqSq
      by_cases hk : k = 0
      · simp [hk]
      · simp only [hk, ↓reduceIte]
        have hnorm := congrArg (fun z => ‖z‖ ^ 2) (fourierCoeff3D_laplacianScalar hf hpf k)
        have hcoeff : ‖(-4 : ℂ) * (Real.pi : ℂ) ^ 2 *
            ((k 0 : ℂ) ^ 2 + (k 1 : ℂ) ^ 2 + (k 2 : ℂ) ^ 2)‖ ^ 2 =
            16 * Real.pi ^ 4 * (kNormSq k) ^ 2 := by
          have hk_eq : (-4 : ℂ) * (Real.pi : ℂ) ^ 2 *
              ((k 0 : ℂ) ^ 2 + (k 1 : ℂ) ^ 2 + (k 2 : ℂ) ^ 2) =
              ((-4 * Real.pi ^ 2 * kNormSq k : ℝ) : ℂ) := by unfold kNormSq; push_cast; ring
          rw [hk_eq, Complex.norm_real, Real.norm_eq_abs, sq_abs]; ring
        rw [norm_mul, mul_pow, hcoeff] at hnorm
        have hk_pos : 0 < kNormSq k := kNormSq_pos_of_ne_zero hk
        have h4 : 16 * Real.pi ^ 4 * (kNormSq k) ^ 2 ≠ 0 := by positivity
        rw [inv_pow]
        have heq_sq : ‖fourierCoeff3D f k‖ ^ 2 =
            ((kNormSq k) ^ 2)⁻¹ * (1 / (16 * Real.pi ^ 4) * ‖fourierCoeff3D (laplacianScalar f) k‖ ^ 2) := by
          field_simp [h4]; linarith
        exact le_of_eq heq_sq)
  rw [tsum_mul_left, hparse_lap.tsum_eq] at hcs
  have hL_nn : 0 ≤ torusIntegral (fun y => (laplacianScalar f y) ^ 2) :=
    torusIntegral_nonneg (hlap_cont.pow 2) (fun _ => sq_nonneg _)
  have hcs2 : (∑' k, tail k) ^ 2 ≤
      52 * (1 / (16 * Real.pi ^ 4) * torusIntegral (fun y => (laplacianScalar f y) ^ 2)) :=
    le_trans hcs (mul_le_mul_of_nonneg_right summable_and_tsum_invKNormSqSq_le.2 (by positivity))
  have htail_le : ∑' k, tail k ≤
      (Real.sqrt 52 / (4 * Real.pi ^ 2)) *
        Real.sqrt (torusIntegral (fun y => (laplacianScalar f y) ^ 2)) := by
    have hrhs_nn : 0 ≤ (Real.sqrt 52 / (4 * Real.pi ^ 2)) *
        Real.sqrt (torusIntegral (fun y => (laplacianScalar f y) ^ 2)) := by positivity
    have hsq_rhs : ((Real.sqrt 52 / (4 * Real.pi ^ 2)) *
        Real.sqrt (torusIntegral (fun y => (laplacianScalar f y) ^ 2))) ^ 2 =
        52 * (1 / (16 * Real.pi ^ 4) * torusIntegral (fun y => (laplacianScalar f y) ^ 2)) := by
      rw [mul_pow, div_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 52), Real.sq_sqrt hL_nn]; ring
    have htail_nn : 0 ≤ ∑' k, tail k :=
      tsum_nonneg fun k => by dsimp only [tail]; split_ifs <;> positivity
    nlinarith
  have h0_eq : ‖fourierCoeff3D f 0‖ = |torusIntegral f| := by
    rw [fourierCoeff3D_zero_eq_torusIntegral, Complex.norm_real, Real.norm_eq_abs]
  linarith

/-- **3D Sobolev `H² ↪ L∞` Velocity Bound for Periodic Navier–Stokes Solutions:**
    `|u(t, x)|² ≤ (13 / (4π⁴)) * palinstrophy3D (u t)` (`0 sorryAx`). -/
theorem sobolev_H2_Linf_ns_velocity
    {u : ℝ → R3 → R3} {p : ℝ → R3 → ℝ} {ν : ℝ}
    (hns : IsPeriodicClassicalNS3D_C3 u p ν)
    (hmean0 : ∀ comp : Fin 3, torusIntegral (fun x => u 0 x comp) = 0)
    {t : ℝ} (ht : t ≥ 0) (x : R3) :
    dot3D (u t x) (u t x) ≤ (13 / (4 * Real.pi ^ 4)) * palinstrophy3D (u t) := by
  have hu3 : ContDiff ℝ 3 (u t) := hns.h_u_c3_global t ht
  have hu2 : ContDiff ℝ 2 (u t) := contDiff_two_of_three5c hu3
  have hpu : IsPeriodic3D (u t) := hns.h_u_periodic t ht
  have hcomp : ∀ c : Fin 3, (u t x c) ^ 2 ≤
      (13 / (4 * Real.pi ^ 4)) * torusIntegral (fun y => (laplacianScalar (fun z => u t z c) y) ^ 2) := by
    intro c
    have huc : ContDiff ℝ 2 (fun z => u t z c) := contDiff_pi.mp hu2 c
    have hpuc : IsPeriodic3D (fun z => u t z c) := fun y i => congrArg (fun v => v c) (hpu y i)
    have hmean : torusIntegral (fun z => u t z c) = 0 := by
      rw [momentum_conservation_torus3D hns ht c, hmean0 c]
    have hsob := sobolev_H2_Linf_3d_scalar huc hpuc x
    rw [hmean, abs_zero, zero_add] at hsob
    have hL_nn : 0 ≤ torusIntegral (fun y => (laplacianScalar (fun z => u t z c) y) ^ 2) :=
      torusIntegral_nonneg ((((continuous_sndPartial_of_contDiff huc 0 0).add
        (continuous_sndPartial_of_contDiff huc 1 1)).add
        (continuous_sndPartial_of_contDiff huc 2 2)).pow 2) (fun _ => sq_nonneg _)
    have hsq : |u t x c| ^ 2 ≤ ((Real.sqrt 52 / (4 * Real.pi ^ 2)) *
        Real.sqrt (torusIntegral (fun y => (laplacianScalar (fun z => u t z c) y) ^ 2))) ^ 2 := by
      nlinarith [abs_nonneg (u t x c)]
    rw [sq_abs, mul_pow, div_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 52),
        Real.sq_sqrt hL_nn] at hsq
    have hconst : 52 / (4 * Real.pi ^ 2) ^ 2 = 13 / (4 * Real.pi ^ 4) := by ring
    rwa [hconst] at hsq
  have hP := palinstrophy_eq_laplacianNormSq hu3 hpu (hns.h_incompressible t ht)
  have hlap_split : torusIntegral (fun y => dot3D (laplacian3D (u t) y) (laplacian3D (u t) y)) =
      torusIntegral (fun y => (laplacianScalar (fun z => u t z 0) y) ^ 2) +
      torusIntegral (fun y => (laplacianScalar (fun z => u t z 1) y) ^ 2) +
      torusIntegral (fun y => (laplacianScalar (fun z => u t z 2) y) ^ 2) := by
    have hc : ∀ c : Fin 3, Continuous (fun y => (laplacianScalar (fun z => u t z c) y) ^ 2) := fun c =>
      ((continuous_apply c).comp (continuous_laplacian3D hu2)).pow 2
    have hpt : ∀ y : R3, dot3D (laplacian3D (u t) y) (laplacian3D (u t) y) =
        (laplacianScalar (fun z => u t z 0) y) ^ 2 +
        (laplacianScalar (fun z => u t z 1) y) ^ 2 +
        (laplacianScalar (fun z => u t z 2) y) ^ 2 := fun y => by
      unfold dot3D laplacian3D; ring
    rw [torusIntegral_congr hpt, torusIntegral_add3 (hc 0) (hc 1) (hc 2)]
  have hdot : dot3D (u t x) (u t x) = (u t x 0) ^ 2 + (u t x 1) ^ 2 + (u t x 2) ^ 2 := by
    unfold dot3D; ring
  rw [hdot, hP, hlap_split]
  linarith [hcomp 0, hcomp 1, hcomp 2]

/-- **MAIN THEOREM 5 OF MILESTONE 5C (Sharp 3D Agmon Inequality on `𝕋³`):**
    `f(x)² ≤ (13 / (4π²)) * √(∫_{𝕋³} |∇f|²) * √(∫_{𝕋³} (Δf)²)` (`0 sorryAx`). -/
theorem agmon_3d_torus_scalar
    {f : R3 → ℝ} (hf : ContDiff ℝ 2 f) (hpf : IsPeriodic3D f)
    (hmean : torusIntegral f = 0) (x : R3) :
    (f x) ^ 2 ≤ (13 / (4 * Real.pi ^ 2)) *
      Real.sqrt (torusIntegral (fun y =>
        (partialDerivScalar f y 0) ^ 2 +
        (partialDerivScalar f y 1) ^ 2 +
        (partialDerivScalar f y 2) ^ 2)) *
      Real.sqrt (torusIntegral (fun y => (laplacianScalar f y) ^ 2)) := by
  have hf1 : ContDiff ℝ 1 f := hf.of_le (by rw [← one_add_one_eq_two]; exact le_self_add)
  let G : ℝ := torusIntegral (fun y =>
    (partialDerivScalar f y 0) ^ 2 + (partialDerivScalar f y 1) ^ 2 + (partialDerivScalar f y 2) ^ 2)
  let L : ℝ := torusIntegral (fun y => (laplacianScalar f y) ^ 2)
  have hsum_norm := summable_norm_fourierCoeff3D_of_contDiff_two hf hpf
  have hinv := (fourier_inversion_3d_of_contDiff_two hf hpf).2 x
  have h0_zero : fourierCoeff3D f 0 = 0 := by
    rw [fourierCoeff3D_zero_eq_torusIntegral, hmean, Complex.ofReal_zero]
  have hG_sum := hasSum_gradNormSq_scalar hf1 hpf
  have hlap_cont : Continuous (laplacianScalar f) :=
    ((continuous_sndPartial_of_contDiff hf 0 0).add
     (continuous_sndPartial_of_contDiff hf 1 1)).add
    (continuous_sndPartial_of_contDiff hf 2 2)
  have hL_parse := hasSum_sq_fourierCoeff3D hlap_cont (isPeriodic3D_laplacianScalar_5c hf hpf)
  have hL_sum : HasSum (fun k : Fin 3 → ℤ =>
      16 * Real.pi ^ 4 * (kNormSq k) ^ 2 * ‖fourierCoeff3D f k‖ ^ 2) L := by
    have hfun : (fun k : Fin 3 → ℤ => ‖fourierCoeff3D (laplacianScalar f) k‖ ^ 2) =
        (fun k => 16 * Real.pi ^ 4 * (kNormSq k) ^ 2 * ‖fourierCoeff3D f k‖ ^ 2) := by
      funext k
      rw [fourierCoeff3D_laplacianScalar hf hpf k, norm_mul, mul_pow]
      have hk_eq : (-4 : ℂ) * (Real.pi : ℂ) ^ 2 *
          ((k 0 : ℂ) ^ 2 + (k 1 : ℂ) ^ 2 + (k 2 : ℂ) ^ 2) =
          ((-4 * Real.pi ^ 2 * kNormSq k : ℝ) : ℂ) := by unfold kNormSq; push_cast; ring
      rw [hk_eq, Complex.norm_real, Real.norm_eq_abs, sq_abs]; ring
    rwa [hfun] at hL_parse
  have hG_nn : 0 ≤ G := torusIntegral_nonneg
    ((((continuous_partialDerivScalar_of_contDiff hf1 0).pow 2).add
      ((continuous_partialDerivScalar_of_contDiff hf1 1).pow 2)).add
      ((continuous_partialDerivScalar_of_contDiff hf1 2).pow 2)) (fun _ => by positivity)
  have hL_nn : 0 ≤ L := torusIntegral_nonneg (hlap_cont.pow 2) (fun _ => sq_nonneg _)
  change (f x) ^ 2 ≤ (13 / (4 * Real.pi ^ 2)) * Real.sqrt G * Real.sqrt L
  rcases eq_or_lt_of_le hG_nn with hG0 | hG_pos
  · have hw := wirtinger_3d_torus hf1 hpf hmean
    change 4 * Real.pi ^ 2 * torusIntegral (fun y => (f y) ^ 2) ≤ G at hw
    have hf2_nn : 0 ≤ torusIntegral (fun y => (f y) ^ 2) :=
      torusIntegral_nonneg (hf.continuous.pow 2) (fun _ => sq_nonneg _)
    have hpi2 : 0 < 4 * Real.pi ^ 2 := by positivity
    have hf2_zero : torusIntegral (fun y => (f y) ^ 2) = 0 := by nlinarith
    rw [eq_zero_of_torusIntegral_sq_eq_zero hf.continuous hpf hf2_zero x]
    simp only [zero_pow (by norm_num : 2 ≠ 0)]; positivity
  rcases eq_or_lt_of_le hL_nn with hL0 | hL_pos
  · have hsob := sobolev_H2_Linf_3d_scalar hf hpf x
    change |f x| ≤ |torusIntegral f| + (Real.sqrt 52 / (4 * Real.pi ^ 2)) * Real.sqrt L at hsob
    rw [hmean, ← hL0, abs_zero, Real.sqrt_zero, mul_zero, add_zero] at hsob
    have hfx0 : f x = 0 := abs_eq_zero.mp (le_antisymm hsob (abs_nonneg _))
    rw [hfx0]; simp only [zero_pow (by norm_num : 2 ≠ 0)]; positivity
  let R : ℝ := Real.sqrt L / (2 * Real.pi * Real.sqrt G)
  have hR_pos : 0 < R := by positivity
  have hag := summable_and_tsum_agmonWeight_le hR_pos
  let b : (Fin 3 → ℤ) → ℝ := fun k =>
    (R * kNormSq k + R⁻¹ * (kNormSq k) ^ 2) * ‖fourierCoeff3D f k‖ ^ 2
  have hb_hasSum : HasSum b (R * (G / (4 * Real.pi ^ 2)) + R⁻¹ * (L / (16 * Real.pi ^ 4))) := by
    have hsum := (hG_sum.mul_left (R / (4 * Real.pi ^ 2))).add (hL_sum.mul_left (R⁻¹ / (16 * Real.pi ^ 4)))
    have hfun : (fun k => R / (4 * Real.pi ^ 2) * (4 * Real.pi ^ 2 * kNormSq k * ‖fourierCoeff3D f k‖ ^ 2) +
        R⁻¹ / (16 * Real.pi ^ 4) * (16 * Real.pi ^ 4 * (kNormSq k) ^ 2 * ‖fourierCoeff3D f k‖ ^ 2)) = b := by
      funext k; dsimp only [b]; have hpi : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
      field_simp [hpi]
    have hrhs : R / (4 * Real.pi ^ 2) * G + R⁻¹ / (16 * Real.pi ^ 4) * L =
        R * (G / (4 * Real.pi ^ 2)) + R⁻¹ * (L / (16 * Real.pi ^ 4)) := by ring
    rwa [hfun, hrhs] at hsum
  have hcs := tsum_le_sqrt_mul_sqrt hsum_norm hag.1 hb_hasSum.summable
    (fun _ => norm_nonneg _)
    (fun k => by
      unfold agmonWeight; split_ifs
      · exact le_refl 0
      · have := kNormSq_pos_of_ne_zero ‹k ≠ 0›; positivity)
    (fun k => by
      dsimp only [b]
      have hk_nn : 0 ≤ kNormSq k := by unfold kNormSq; positivity
      positivity)
    (fun k => by
      by_cases hk : k = 0
      · subst hk; simp [h0_zero, agmonWeight]
      · unfold agmonWeight; dsimp only [b]; simp only [hk, ↓reduceIte]
        have hk_pos : 0 < kNormSq k := kNormSq_pos_of_ne_zero hk
        have hden : R * kNormSq k + R⁻¹ * (kNormSq k) ^ 2 ≠ 0 := by positivity
        rw [← mul_assoc, inv_mul_cancel₀ hden, one_mul])
  rw [hb_hasSum.tsum_eq] at hcs
  have hval_b : R * (G / (4 * Real.pi ^ 2)) + R⁻¹ * (L / (16 * Real.pi ^ 4)) =
      Real.sqrt G * Real.sqrt L / (4 * Real.pi ^ 3) := by
    dsimp only [R]
    have hpi : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
    have hsg : Real.sqrt G ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hG_pos)
    have hsl : Real.sqrt L ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hL_pos)
    have hG_sq : Real.sqrt G ^ 2 = G := Real.sq_sqrt hG_nn
    have hL_sq : Real.sqrt L ^ 2 = L := Real.sq_sqrt hL_nn
    generalize Real.sqrt G = a at hsg hG_sq ⊢
    generalize Real.sqrt L = b at hsl hL_sq ⊢
    rw [← hG_sq, ← hL_sq]
    field_simp [hpi, hsg, hsl]
    ring
  rw [hval_b] at hcs
  have hle_sum : (∑' k, ‖fourierCoeff3D f k‖) ^ 2 ≤
      (13 * Real.pi) * (Real.sqrt G * Real.sqrt L / (4 * Real.pi ^ 3)) :=
    le_trans hcs (mul_le_mul_of_nonneg_right hag.2 (by positivity))
  have hconst : (13 * Real.pi) * (Real.sqrt G * Real.sqrt L / (4 * Real.pi ^ 3)) =
      (13 / (4 * Real.pi ^ 2)) * Real.sqrt G * Real.sqrt L := by
    have hpi : Real.pi ≠ 0 := ne_of_gt Real.pi_pos; field_simp [hpi]
  rw [hconst] at hle_sum
  have hfx_sq : (f x) ^ 2 ≤ (∑' k, ‖fourierCoeff3D f k‖) ^ 2 := by
    rw [← sq_abs (f x)]; nlinarith [abs_nonneg (f x)]
  exact le_trans hfx_sq hle_sum

-- ============================================================================
-- SECTION 5: 3D SPECTRAL HEAT SEMIGROUP `e^{νtΔ}` (BRIDGE TO MILESTONE 6)
-- ============================================================================

/-- Spectral multiplier of the 3D heat semigroup `e^{νtΔ}` at wavevector `k ∈ ℤ³`. -/
noncomputable def heatMultiplier3D (ν t : ℝ) (k : Fin 3 → ℤ) : ℝ :=
  Real.exp (-4 * Real.pi ^ 2 * ν * kNormSq k * t)

theorem heatMultiplier3D_zero (ν : ℝ) (k : Fin 3 → ℤ) :
    heatMultiplier3D ν 0 k = 1 := by
  unfold heatMultiplier3D; simp

theorem heatMultiplier3D_add (ν t s : ℝ) (k : Fin 3 → ℤ) :
    heatMultiplier3D ν (t + s) k = heatMultiplier3D ν t k * heatMultiplier3D ν s k := by
  unfold heatMultiplier3D; rw [← Real.exp_add]; congr 1; ring

theorem heatMultiplier3D_pos_le_one {ν t : ℝ} (hν : 0 ≤ ν) (ht : 0 ≤ t) (k : Fin 3 → ℤ) :
    0 < heatMultiplier3D ν t k ∧ heatMultiplier3D ν t k ≤ 1 := by
  unfold heatMultiplier3D
  refine ⟨Real.exp_pos _, Real.exp_le_one_iff.mpr ?_⟩
  have hk_nn : 0 ≤ kNormSq k := by unfold kNormSq; positivity
  have hnn : 0 ≤ 4 * Real.pi ^ 2 * ν * kNormSq k * t := by positivity
  linarith

/-- **Parabolic `L² → H¹` Smoothing Estimate for `e^{νtΔ}` (`0 sorryAx`):**
    `4π² |k|² (e^{-4π²ν|k|²t})² ≤ 1 / (2νt)` for all `ν > 0, t > 0`. -/
theorem heatMultiplier3D_smoothing_H1 {ν t : ℝ} (hν : 0 < ν) (ht : 0 < t) (k : Fin 3 → ℤ) :
    4 * Real.pi ^ 2 * kNormSq k * (heatMultiplier3D ν t k) ^ 2 ≤ 1 / (2 * ν * t) := by
  let x : ℝ := 8 * Real.pi ^ 2 * ν * kNormSq k * t
  have hx_nn : 0 ≤ x := by
    dsimp only [x]
    have hk_nn : 0 ≤ kNormSq k := by unfold kNormSq; positivity
    positivity
  have hexp_ge : x ≤ Real.exp x := by linarith [Real.add_one_le_exp x]
  have hsq : (heatMultiplier3D ν t k) ^ 2 = (Real.exp x)⁻¹ := by
    unfold heatMultiplier3D; rw [← Real.exp_nat_mul, ← Real.exp_neg]; congr 1; dsimp only [x]; ring
  rw [hsq]
  have h_pos : 0 < Real.exp x := Real.exp_pos x
  have h2vt : 0 < 2 * ν * t := by positivity
  have hmul : 4 * Real.pi ^ 2 * kNormSq k * (Real.exp x)⁻¹ * (2 * ν * t) ≤ 1 := by
    have heq : 4 * Real.pi ^ 2 * kNormSq k * (Real.exp x)⁻¹ * (2 * ν * t) = x * (Real.exp x)⁻¹ := by
      dsimp only [x]; ring
    rw [heq]
    calc x * (Real.exp x)⁻¹ ≤ Real.exp x * (Real.exp x)⁻¹ :=
          mul_le_mul_of_nonneg_right hexp_ge (inv_nonneg.mpr (le_of_lt h_pos))
      _ = 1 := mul_inv_cancel₀ (ne_of_gt h_pos)
  exact (le_div_iff₀ h2vt).mpr hmul

/-- **Parabolic `L² → H²` Smoothing Estimate for `e^{νtΔ}` (`0 sorryAx`):**
    `16π⁴ |k|⁴ (e^{-4π²ν|k|²t})² ≤ 1 / (ν² t²)` for all `ν > 0, t > 0`. -/
theorem heatMultiplier3D_smoothing_H2 {ν t : ℝ} (hν : 0 < ν) (ht : 0 < t) (k : Fin 3 → ℤ) :
    16 * Real.pi ^ 4 * (kNormSq k) ^ 2 * (heatMultiplier3D ν t k) ^ 2 ≤ 1 / (ν ^ 2 * t ^ 2) := by
  let x : ℝ := 8 * Real.pi ^ 2 * ν * kNormSq k * t
  have hx_nn : 0 ≤ x := by
    dsimp only [x]
    have hk_nn : 0 ≤ kNormSq k := by unfold kNormSq; positivity
    positivity
  have hhalf : x / 2 ≤ Real.exp (x / 2) := by linarith [Real.add_one_le_exp (x / 2)]
  have hexp_ge : x ^ 2 / 4 ≤ Real.exp x := by
    have hsq : (x / 2) ^ 2 ≤ (Real.exp (x / 2)) ^ 2 := by nlinarith
    have h2 : (Real.exp (x / 2)) ^ 2 = Real.exp x := by
      rw [← Real.exp_nat_mul]; congr 1; ring
    linarith
  have hsq : (heatMultiplier3D ν t k) ^ 2 = (Real.exp x)⁻¹ := by
    unfold heatMultiplier3D; rw [← Real.exp_nat_mul, ← Real.exp_neg]; congr 1; dsimp only [x]; ring
  rw [hsq]
  have h_pos : 0 < Real.exp x := Real.exp_pos x
  have hvt2 : 0 < ν ^ 2 * t ^ 2 := by positivity
  have hmul : 16 * Real.pi ^ 4 * (kNormSq k) ^ 2 * (Real.exp x)⁻¹ * (ν ^ 2 * t ^ 2) ≤ 1 := by
    have heq : 16 * Real.pi ^ 4 * (kNormSq k) ^ 2 * (Real.exp x)⁻¹ * (ν ^ 2 * t ^ 2) =
        (x ^ 2 / 4) * (Real.exp x)⁻¹ := by dsimp only [x]; ring
    rw [heq]
    calc (x ^ 2 / 4) * (Real.exp x)⁻¹ ≤ Real.exp x * (Real.exp x)⁻¹ :=
          mul_le_mul_of_nonneg_right hexp_ge (inv_nonneg.mpr (le_of_lt h_pos))
      _ = 1 := mul_inv_cancel₀ (ne_of_gt h_pos)
  exact (le_div_iff₀ hvt2).mpr hmul

-- ============================================================================
-- SECTION 6: AXIOM AUDIT TRAIL (0 sorryAx)
-- ============================================================================

#print axioms plancherel_inner_3d_scalar
#print axioms plancherel_inner_3d_vec
#print axioms eq_zero_of_torusIntegral_sq_eq_zero
#print axioms summable_and_tsum_invKNormSqSq_le
#print axioms summable_and_tsum_agmonWeight_le
#print axioms fourier_inversion_3d_of_contDiff_two
#print axioms sobolev_H2_Linf_3d_scalar
#print axioms sobolev_H2_Linf_ns_velocity
#print axioms agmon_3d_torus_scalar
#print axioms heatMultiplier3D_smoothing_H1
#print axioms heatMultiplier3D_smoothing_H2

end GarrySobolevEmbedding3D