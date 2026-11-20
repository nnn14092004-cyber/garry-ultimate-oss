import SmoothClassicalSynthesisTorus3D
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

/-!
# Milestone 9A (Tier I — 100% Unconditional): H¹ Enstrophy Basin, Finite-Time Waterfall Trap & H² Entry on 𝕋³

This module eliminates the stretching hypothesis `h_stretch` of Milestone 7B completely and
proves unconditionally (`0 sorryAx`, `0` custom axioms) for periodic mean-zero 3D Navier-Stokes
classical solutions on `𝕋³ = (ℝ/ℤ)³`:

1. Exact periodic IBP identity `S_stretch = -∫_{𝕋³} u · ((ω · ∇)ω) dx` using `∇ · ω = 0`.
2. Vector Agmon 3D inequality `|u(x)|² ≤ (13 / (4π²)) √(2Z) √P`.
3. Unconditional supercritical stretching bound `|S_stretch| ≤ C3D_agmon · Z^{3/4} · P^{3/4}`
   with explicit constant `C3D_agmon⁴ = 169 / (2π⁴)`.
4. Unconditional sharp enstrophy ODE with explicit `H¹` basin threshold
   `Z_crit_H1 ν = 4π³ ν² / 13` (≈ `9.5404 ν²`).
5. Unconditional `H¹` basin invariance and global exponential decay for any `Z(t₀) < Z_crit_H1 ν`.
6. Unconditional global palinstrophy integral bound `∫_{t₀}^T P(s) ds ≤ (16 / (3ν)) Z(t₀)` and
   finite-time entry into the Milestone 8A `H²` threshold `P(T_enter) < π⁶ ν² / 27136`.
7. Unconditional Finite-Time Waterfall Trap Theorem: any solution surviving past
   `T_trap(E₀, ν) = 13 E₀ / (4π³ ν³)` must enter the half-critical `H¹` basin `Z(t*) < Z_crit_H1 ν / 2`.
-/

namespace GarryEnstrophyBasin3D

open MeasureTheory Filter Topology
open GarryReal3DCalculus
open GarryVorticity3D
open GarryLerayTorus3D
open GarryLerayEnergyLaw3D
open GarryPoincareSobolev3D
open GarryFourierSpectral3D
open GarryParsevalSobolev3D
open GarrySobolevEmbedding3D
open GarrySupercriticalBridge3D

-- ============================================================================
-- SECTION 0: EXPLICIT CONSTANTS & ELEMENTARY HELPERS
-- ============================================================================

/-- Explicit unconditional 3D Agmon-IBP vortex stretching constant `C3D_agmon = √(13√2 / (2π²))`,
    satisfying `C3D_agmon⁴ = 169 / (2π⁴)`. -/
noncomputable def C3D_agmon : ℝ :=
  Real.sqrt (13 * Real.sqrt 2 / (2 * Real.pi ^ 2))

/-- Explicit unconditional `H¹` enstrophy basin critical threshold on `𝕋³`:
    `Z_crit_H1 ν = (4 π³ / 13) ν²`. Below this threshold, viscous dissipation strictly
    dominates 3D vortex stretching (`dZ/dt < 0`). -/
noncomputable def Z_crit_H1 (ν : ℝ) : ℝ :=
  4 * Real.pi ^ 3 * ν ^ 2 / 13

/-- Explicit finite-time waterfall-to-river trap horizon for unconditional entry into
    the half-critical `H¹` basin `Z < Z_crit_H1 ν / 2 = (2 π³ / 13) ν²`:
    `T_trap_H1 E₀ ν = 13 E₀ / (4 π³ ν³)`. -/
noncomputable def T_trap_H1 (E₀ ν : ℝ) : ℝ :=
  13 * E₀ / (4 * Real.pi ^ 3 * ν ^ 3)

lemma C3D_agmon_nonneg : 0 ≤ C3D_agmon := Real.sqrt_nonneg _

lemma C3D_agmon_pow_four :
    C3D_agmon ^ 4 = 169 / (2 * Real.pi ^ 4) := by
  unfold C3D_agmon
  have hinner : 0 ≤ 13 * Real.sqrt 2 / (2 * Real.pi ^ 2) := by positivity
  have hsq : Real.sqrt (13 * Real.sqrt 2 / (2 * Real.pi ^ 2)) ^ 2 =
      13 * Real.sqrt 2 / (2 * Real.pi ^ 2) := Real.sq_sqrt hinner
  calc (Real.sqrt (13 * Real.sqrt 2 / (2 * Real.pi ^ 2))) ^ 4
      = ((Real.sqrt (13 * Real.sqrt 2 / (2 * Real.pi ^ 2))) ^ 2) ^ 2 := by ring
    _ = (13 * Real.sqrt 2 / (2 * Real.pi ^ 2)) ^ 2 := by rw [hsq]
    _ = 169 * (Real.sqrt 2) ^ 2 / (4 * Real.pi ^ 4) := by ring
    _ = 169 * 2 / (4 * Real.pi ^ 4) := by rw [Real.sq_sqrt (by norm_num)]
    _ = 169 / (2 * Real.pi ^ 4) := by ring

lemma Z_crit_H1_pos {ν : ℝ} (hν : 0 < ν) : 0 < Z_crit_H1 ν := by
  unfold Z_crit_H1; positivity

private lemma cd2_of_3_9a {f : R3 → R3} (h : ContDiff ℝ 3 f) : ContDiff ℝ 2 f :=
  h.of_le (by exact_mod_cast (show (2 : ℕ) ≤ 3 by decide))

private lemma cd1_of_2_9a {f : R3 → R3} (h : ContDiff ℝ 2 f) : ContDiff ℝ 1 f :=
  h.of_le (by exact_mod_cast (show (1 : ℕ) ≤ 2 by decide))

private lemma torusIntegral_le_of_le {f g : R3 → ℝ} (hf : Continuous f) (hg : Continuous g)
    (hfg : ∀ x : R3, f x ≤ g x) :
    torusIntegral f ≤ torusIntegral g := by
  have hnn : 0 ≤ torusIntegral (fun x => g x - f x) :=
    torusIntegral_nonneg (hg.sub hf) (fun x => sub_nonneg.mpr (hfg x))
  rw [torusIntegral_sub hg hf] at hnn
  linarith

private lemma cauchy_schwarz_3_nonneg {a0 a1 a2 b0 b1 b2 : ℝ}
    (ha0 : 0 ≤ a0) (ha1 : 0 ≤ a1) (ha2 : 0 ≤ a2)
    (hb0 : 0 ≤ b0) (hb1 : 0 ≤ b1) (hb2 : 0 ≤ b2) :
    Real.sqrt a0 * Real.sqrt b0 + Real.sqrt a1 * Real.sqrt b1 + Real.sqrt a2 * Real.sqrt b2 ≤
      Real.sqrt (a0 + a1 + a2) * Real.sqrt (b0 + b1 + b2) := by
  have hL_nn : 0 ≤ Real.sqrt a0 * Real.sqrt b0 + Real.sqrt a1 * Real.sqrt b1 +
      Real.sqrt a2 * Real.sqrt b2 := by positivity
  have hR_nn : 0 ≤ Real.sqrt (a0 + a1 + a2) * Real.sqrt (b0 + b1 + b2) := by positivity
  have hsq : (Real.sqrt a0 * Real.sqrt b0 + Real.sqrt a1 * Real.sqrt b1 +
      Real.sqrt a2 * Real.sqrt b2) ^ 2 ≤
      (Real.sqrt (a0 + a1 + a2) * Real.sqrt (b0 + b1 + b2)) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (by linarith), Real.sq_sqrt (by linarith)]
    have s0 : (Real.sqrt a0) ^ 2 = a0 := Real.sq_sqrt ha0
    have s1 : (Real.sqrt a1) ^ 2 = a1 := Real.sq_sqrt ha1
    have s2 : (Real.sqrt a2) ^ 2 = a2 := Real.sq_sqrt ha2
    have t0 : (Real.sqrt b0) ^ 2 = b0 := Real.sq_sqrt hb0
    have t1 : (Real.sqrt b1) ^ 2 = b1 := Real.sq_sqrt hb1
    have t2 : (Real.sqrt b2) ^ 2 = b2 := Real.sq_sqrt hb2
    nlinarith [sq_nonneg (Real.sqrt a0 * Real.sqrt b1 - Real.sqrt a1 * Real.sqrt b0),
               sq_nonneg (Real.sqrt a0 * Real.sqrt b2 - Real.sqrt a2 * Real.sqrt b0),
               sq_nonneg (Real.sqrt a1 * Real.sqrt b2 - Real.sqrt a2 * Real.sqrt b1)]
  nlinarith

-- ============================================================================
-- SECTION 1: EXACT PERIODIC IBP IDENTITY FOR 3D VORTEX STRETCHING
-- ============================================================================

private lemma torusIntegral_ibp_prod
    {f g h : R3 → ℝ} (hf : ContDiff ℝ 1 f) (hg : ContDiff ℝ 1 g) (hh : ContDiff ℝ 1 h)
    (hpf : IsPeriodic3D f) (hpg : IsPeriodic3D g) (hph : IsPeriodic3D h) (i : Fin 3) :
    torusIntegral (fun x => (f x * g x) * partialDerivScalar h x i) =
      -torusIntegral (fun x =>
        (partialDerivScalar f x i * g x + f x * partialDerivScalar g x i) * h x) := by
  have hfg : ContDiff ℝ 1 (fun y => f y * g y) := hf.mul hg
  have hpfg : IsPeriodic3D (fun y => f y * g y) := fun x j =>
    congrArg₂ (· * ·) (hpf x j) (hpg x j)
  rw [torusIntegral_ibp hfg hh hpfg hph i]
  congr 1
  apply torusIntegral_congr
  intro x
  have hmul := partialDerivScalar_mul
    ((hf.differentiable (by simp)) x) ((hg.differentiable (by simp)) x) i
  rw [hmul]
  ring

private lemma ibp_stretch_term {u : R3 → R3} (hu3 : ContDiff ℝ 3 u) (hpu : IsPeriodic3D u)
    (c i : Fin 3) :
    torusIntegral (fun x => (curl3D u x i * curl3D u x c) *
        partialDerivScalar (fun y => u y c) x i) =
      -torusIntegral (fun x =>
        (partialDerivScalar (fun y => curl3D u y i) x i * curl3D u x c +
         curl3D u x i * partialDerivScalar (fun y => curl3D u y c) x i) * u x c) := by
  have hu1 : ContDiff ℝ 1 u := cd1_of_2_9a (cd2_of_3_9a hu3)
  have hw1 : ContDiff ℝ 1 (curl3D u) := cd1_of_2_9a (contDiff_two_curl3D hu3)
  have hpw : IsPeriodic3D (curl3D u) := hpu.curl3D (hu1.differentiable (by simp))
  exact torusIntegral_ibp_prod
    (contDiff_pi.mp hw1 i) (contDiff_pi.mp hw1 c) (contDiff_pi.mp hu1 c)
    (fun x j => congrArg (fun v => v i) (hpw x j))
    (fun x j => congrArg (fun v => v c) (hpw x j))
    (fun x j => congrArg (fun v => v c) (hpu x j))
    i

/-- **THEOREM 1 (Exact Periodic IBP Identity for 3D Vortex Stretching):**
    Using `∇ · ω = div3D (curl3D u) = 0`, integrating by parts moves the spatial gradient
    from `u` onto `ω`:
    `∫_{𝕋³} ⟨(ω · ∇)u, ω⟩ dx = -∫_{𝕋³} ⟨u, (ω · ∇)ω⟩ dx`. -/
theorem vortexStretching3D_eq_neg_ibp
    {u : R3 → R3} (hu3 : ContDiff ℝ 3 u) (hpu : IsPeriodic3D u) :
    vortexStretching3D u =
      -torusIntegral (fun x => dot3D (u x) (directionalAdvection3D (curl3D u) (curl3D u) x)) := by
  have hu2 : ContDiff ℝ 2 u := cd2_of_3_9a hu3
  have hu1 : ContDiff ℝ 1 u := cd1_of_2_9a hu2
  have hw2 : ContDiff ℝ 2 (curl3D u) := contDiff_two_curl3D hu3
  have hw1 : ContDiff ℝ 1 (curl3D u) := cd1_of_2_9a hw2
  have h_comp : ∀ c : Fin 3,
      torusIntegral (fun x => directionalAdvection3D (curl3D u) u x c * curl3D u x c) =
        -torusIntegral (fun x => u x c * directionalAdvection3D (curl3D u) (curl3D u) x c) := by
    intro c
    have hwc : ContDiff ℝ 1 (fun y => curl3D u y c) := contDiff_pi.mp hw1 c
    have huc : ContDiff ℝ 1 (fun y => u y c) := contDiff_pi.mp hu1 c
    have hc_l : ∀ i : Fin 3, Continuous (fun x =>
        (curl3D u x i * curl3D u x c) * partialDerivScalar (fun y => u y c) x i) := fun i =>
      (((contDiff_pi.mp hw1 i).continuous.mul hwc.continuous).mul
        (continuous_partialDerivScalar_of_contDiff huc i))
    have hc_r : ∀ i : Fin 3, Continuous (fun x =>
        (partialDerivScalar (fun y => curl3D u y i) x i * curl3D u x c +
         curl3D u x i * partialDerivScalar (fun y => curl3D u y c) x i) * u x c) := fun i =>
      (((continuous_partialDerivScalar_of_contDiff (contDiff_pi.mp hw1 i) i).mul hwc.continuous).add
        ((contDiff_pi.mp hw1 i).continuous.mul
          (continuous_partialDerivScalar_of_contDiff hwc i))).mul huc.continuous
    have hlhs_pt : ∀ x : R3,
        directionalAdvection3D (curl3D u) u x c * curl3D u x c =
          (curl3D u x 0 * curl3D u x c) * partialDerivScalar (fun y => u y c) x 0 +
          (curl3D u x 1 * curl3D u x c) * partialDerivScalar (fun y => u y c) x 1 +
          (curl3D u x 2 * curl3D u x c) * partialDerivScalar (fun y => u y c) x 2 := fun x => by
      unfold directionalAdvection3D; ring
    have hrhs_pt : ∀ x : R3,
        ((partialDerivScalar (fun y => curl3D u y 0) x 0 * curl3D u x c +
          curl3D u x 0 * partialDerivScalar (fun y => curl3D u y c) x 0) * u x c) +
        ((partialDerivScalar (fun y => curl3D u y 1) x 1 * curl3D u x c +
          curl3D u x 1 * partialDerivScalar (fun y => curl3D u y c) x 1) * u x c) +
        ((partialDerivScalar (fun y => curl3D u y 2) x 2 * curl3D u x c +
          curl3D u x 2 * partialDerivScalar (fun y => curl3D u y c) x 2) * u x c) =
        u x c * directionalAdvection3D (curl3D u) (curl3D u) x c := fun x => by
      have hdiv0 : div3D (curl3D u) x = 0 := div3D_curl3D_eq_zero u x hu2.contDiffAt
      unfold div3D at hdiv0
      unfold directionalAdvection3D
      linear_combination (curl3D u x c * u x c) * hdiv0
    rw [torusIntegral_congr hlhs_pt, torusIntegral_add3 (hc_l 0) (hc_l 1) (hc_l 2),
        ibp_stretch_term hu3 hpu c 0, ibp_stretch_term hu3 hpu c 1, ibp_stretch_term hu3 hpu c 2]
    have hsum := torusIntegral_add3 (hc_r 0) (hc_r 1) (hc_r 2)
    rw [torusIntegral_congr hrhs_pt] at hsum
    linarith
  have hc_lhs : ∀ c : Fin 3,
      Continuous (fun x => directionalAdvection3D (curl3D u) u x c * curl3D u x c) := fun c => by
    unfold directionalAdvection3D
    have huc : ContDiff ℝ 1 (fun y => u y c) := contDiff_pi.mp hu1 c
    have hwc : ContDiff ℝ 1 (fun y => curl3D u y c) := contDiff_pi.mp hw1 c
    exact ((((contDiff_pi.mp hw1 0).continuous.mul (continuous_partialDerivScalar_of_contDiff huc 0)).add
      ((contDiff_pi.mp hw1 1).continuous.mul (continuous_partialDerivScalar_of_contDiff huc 1))).add
      ((contDiff_pi.mp hw1 2).continuous.mul (continuous_partialDerivScalar_of_contDiff huc 2))).mul
      hwc.continuous
  have hc_rhs : ∀ c : Fin 3,
      Continuous (fun x => u x c * directionalAdvection3D (curl3D u) (curl3D u) x c) := fun c => by
    unfold directionalAdvection3D
    have hwc : ContDiff ℝ 1 (fun y => curl3D u y c) := contDiff_pi.mp hw1 c
    exact (contDiff_pi.mp hu1 c).continuous.mul
      ((((contDiff_pi.mp hw1 0).continuous.mul (continuous_partialDerivScalar_of_contDiff hwc 0)).add
        ((contDiff_pi.mp hw1 1).continuous.mul (continuous_partialDerivScalar_of_contDiff hwc 1))).add
        ((contDiff_pi.mp hw1 2).continuous.mul (continuous_partialDerivScalar_of_contDiff hwc 2)))
  unfold vortexStretching3D
  have hdot_l : ∀ x : R3,
      dot3D (directionalAdvection3D (curl3D u) u x) (curl3D u x) =
        directionalAdvection3D (curl3D u) u x 0 * curl3D u x 0 +
        directionalAdvection3D (curl3D u) u x 1 * curl3D u x 1 +
        directionalAdvection3D (curl3D u) u x 2 * curl3D u x 2 := fun _ => rfl
  have hdot_r : ∀ x : R3,
      dot3D (u x) (directionalAdvection3D (curl3D u) (curl3D u) x) =
        u x 0 * directionalAdvection3D (curl3D u) (curl3D u) x 0 +
        u x 1 * directionalAdvection3D (curl3D u) (curl3D u) x 1 +
        u x 2 * directionalAdvection3D (curl3D u) (curl3D u) x 2 := fun _ => rfl
  rw [torusIntegral_congr hdot_l, torusIntegral_add3 (hc_lhs 0) (hc_lhs 1) (hc_lhs 2),
      torusIntegral_congr hdot_r, torusIntegral_add3 (hc_rhs 0) (hc_rhs 1) (hc_rhs 2),
      h_comp 0, h_comp 1, h_comp 2]
  ring

-- ============================================================================
-- SECTION 2: VECTOR AGMON 3D & UNCONDITIONAL VORTEX STRETCHING BOUND
-- ============================================================================

/-- **THEOREM 2 (Unconditional Vector Agmon 3D Inequality on `𝕋³`):**
    For any mean-zero solenoidal periodic `C³` velocity field `u` on `𝕋³`,
    `|u(x)|² ≤ (13 / (4π²)) · √(∫ |ω|² dx) · √(∫ |∇ω|² dx)`. -/
theorem agmon_3d_torus_ns_velocity
    {u : R3 → R3} (hu3 : ContDiff ℝ 3 u) (hpu : IsPeriodic3D u)
    (hdiv : ∀ x : R3, div3D u x = 0)
    (hmean : ∀ c : Fin 3, torusIntegral (fun x => u x c) = 0)
    (x : R3) :
    dot3D (u x) (u x) ≤
      (13 / (4 * Real.pi ^ 2)) *
        Real.sqrt (torusIntegral (fun y => dot3D (curl3D u y) (curl3D u y))) *
        Real.sqrt (palinstrophy3D u) := by
  have hu2 : ContDiff ℝ 2 u := cd2_of_3_9a hu3
  have hu1 : ContDiff ℝ 1 u := cd1_of_2_9a hu2
  let G : Fin 3 → ℝ := fun c =>
    torusIntegral (fun y =>
      (partialDerivScalar (fun z => u z c) y 0) ^ 2 +
      (partialDerivScalar (fun z => u z c) y 1) ^ 2 +
      (partialDerivScalar (fun z => u z c) y 2) ^ 2)
  let L : Fin 3 → ℝ := fun c =>
    torusIntegral (fun y => (laplacianScalar (fun z => u z c) y) ^ 2)
  have hGc_cont : ∀ c : Fin 3, Continuous (fun y =>
      (partialDerivScalar (fun z => u z c) y 0) ^ 2 +
      (partialDerivScalar (fun z => u z c) y 1) ^ 2 +
      (partialDerivScalar (fun z => u z c) y 2) ^ 2) := fun c => by
    have huc := contDiff_pi.mp hu1 c
    exact (((continuous_partialDerivScalar_of_contDiff huc 0).pow 2).add
      ((continuous_partialDerivScalar_of_contDiff huc 1).pow 2)).add
      ((continuous_partialDerivScalar_of_contDiff huc 2).pow 2)
  have hLc_cont : ∀ c : Fin 3, Continuous (fun y =>
      (laplacianScalar (fun z => u z c) y) ^ 2) := fun c => by
    have huc2 := contDiff_pi.mp hu2 c
    unfold laplacianScalar
    have c0 := continuous_sndPartial_of_contDiff huc2 0 0
    have c1 := continuous_sndPartial_of_contDiff huc2 1 1
    have c2 := continuous_sndPartial_of_contDiff huc2 2 2
    exact ((c0.add c1).add c2).pow 2
  have hG_nn : ∀ c : Fin 3, 0 ≤ G c := fun c =>
    torusIntegral_nonneg (hGc_cont c) (fun y => by positivity)
  have hL_nn : ∀ c : Fin 3, 0 ≤ L c := fun c =>
    torusIntegral_nonneg (hLc_cont c) (fun y => sq_nonneg _)
  have hag : ∀ c : Fin 3, (u x c) ^ 2 ≤ (13 / (4 * Real.pi ^ 2)) * Real.sqrt (G c) * Real.sqrt (L c) :=
    fun c => agmon_3d_torus_scalar (contDiff_pi.mp hu2 c)
      (fun y j => congrArg (fun v => v c) (hpu y j)) (hmean c) x
  have hG_sum : G 0 + G 1 + G 2 = torusIntegral (fun y => dot3D (curl3D u y) (curl3D u y)) := by
    rw [enstrophy_eq_half_gradNormSq hu2 hpu hdiv]
    dsimp only [G]
    rw [← torusIntegral_add3 (hGc_cont 0) (hGc_cont 1) (hGc_cont 2)]
    apply torusIntegral_congr
    intro y
    unfold gradNormSq3D; ring
  have hL_sum : L 0 + L 1 + L 2 = palinstrophy3D u := by
    rw [palinstrophy_eq_laplacianNormSq hu3 hpu hdiv]
    dsimp only [L]
    rw [← torusIntegral_add3 (hLc_cont 0) (hLc_cont 1) (hLc_cont 2)]
    apply torusIntegral_congr
    intro y
    unfold dot3D laplacian3D; ring
  have hcs := cauchy_schwarz_3_nonneg (hG_nn 0) (hG_nn 1) (hG_nn 2) (hL_nn 0) (hL_nn 1) (hL_nn 2)
  rw [hG_sum, hL_sum] at hcs
  have hcoef : 0 ≤ 13 / (4 * Real.pi ^ 2) := by positivity
  have hdot_sq : dot3D (u x) (u x) = (u x 0) ^ 2 + (u x 1) ^ 2 + (u x 2) ^ 2 := by
    unfold dot3D; ring
  rw [hdot_sq]
  have hsum_ag : (u x 0) ^ 2 + (u x 1) ^ 2 + (u x 2) ^ 2 ≤
      (13 / (4 * Real.pi ^ 2)) *
        (Real.sqrt (G 0) * Real.sqrt (L 0) + Real.sqrt (G 1) * Real.sqrt (L 1) +
         Real.sqrt (G 2) * Real.sqrt (L 2)) := by
    have h0 := hag 0; have h1 := hag 1; have h2 := hag 2; linarith
  have hmul := mul_le_mul_of_nonneg_left hcs hcoef
  linarith

private lemma pointwise_stretch_sq_le (u ω : R3) (dw00 dw01 dw02 dw10 dw11 dw12 dw20 dw21 dw22 : ℝ) :
    (u 0 * (ω 0 * dw00 + ω 1 * dw01 + ω 2 * dw02) +
     u 1 * (ω 0 * dw10 + ω 1 * dw11 + ω 2 * dw12) +
     u 2 * (ω 0 * dw20 + ω 1 * dw21 + ω 2 * dw22)) ^ 2 ≤
      dot3D u u * dot3D ω ω *
        (dw00 ^ 2 + dw01 ^ 2 + dw02 ^ 2 +
         dw10 ^ 2 + dw11 ^ 2 + dw12 ^ 2 +
         dw20 ^ 2 + dw21 ^ 2 + dw22 ^ 2) := by
  let b0 := ω 0 * dw00 + ω 1 * dw01 + ω 2 * dw02
  let b1 := ω 0 * dw10 + ω 1 * dw11 + ω 2 * dw12
  let b2 := ω 0 * dw20 + ω 1 * dw21 + ω 2 * dw22
  have hcs_u : (u 0 * b0 + u 1 * b1 + u 2 * b2) ^ 2 ≤
      dot3D u u * (b0 ^ 2 + b1 ^ 2 + b2 ^ 2) := by
    unfold dot3D
    nlinarith [sq_nonneg (u 0 * b1 - u 1 * b0),
               sq_nonneg (u 0 * b2 - u 2 * b0),
               sq_nonneg (u 1 * b2 - u 2 * b1)]
  have hb0 : b0 ^ 2 ≤ dot3D ω ω * (dw00 ^ 2 + dw01 ^ 2 + dw02 ^ 2) := by
    unfold dot3D; dsimp only [b0]
    nlinarith [sq_nonneg (ω 0 * dw01 - ω 1 * dw00),
               sq_nonneg (ω 0 * dw02 - ω 2 * dw00),
               sq_nonneg (ω 1 * dw02 - ω 2 * dw01)]
  have hb1 : b1 ^ 2 ≤ dot3D ω ω * (dw10 ^ 2 + dw11 ^ 2 + dw12 ^ 2) := by
    unfold dot3D; dsimp only [b1]
    nlinarith [sq_nonneg (ω 0 * dw11 - ω 1 * dw10),
               sq_nonneg (ω 0 * dw12 - ω 2 * dw10),
               sq_nonneg (ω 1 * dw12 - ω 2 * dw11)]
  have hb2 : b2 ^ 2 ≤ dot3D ω ω * (dw20 ^ 2 + dw21 ^ 2 + dw22 ^ 2) := by
    unfold dot3D; dsimp only [b2]
    nlinarith [sq_nonneg (ω 0 * dw21 - ω 1 * dw20),
               sq_nonneg (ω 0 * dw22 - ω 2 * dw20),
               sq_nonneg (ω 1 * dw22 - ω 2 * dw21)]
  have hu_nn : 0 ≤ dot3D u u := dot3D_self_nonneg u
  have hsum : b0 ^ 2 + b1 ^ 2 + b2 ^ 2 ≤
      dot3D ω ω * (dw00 ^ 2 + dw01 ^ 2 + dw02 ^ 2 +
        dw10 ^ 2 + dw11 ^ 2 + dw12 ^ 2 + dw20 ^ 2 + dw21 ^ 2 + dw22 ^ 2) := by
    linarith
  have hmul := mul_le_mul_of_nonneg_left hsum hu_nn
  linarith

/-- **THEOREM 3 (Unconditional 3D Vortex Stretching Bound — Eliminating `h_stretch`):**
    For EVERY mean-zero solenoidal periodic `C³` field `u` on `𝕋³`, with NO extra hypotheses,
    `|vortexStretching3D u| ≤ C3D_agmon · Z^{3/4} · P^{3/4}`,
    where `Z = ½ ∫ |ω|² dx`, `P = ∫ |∇ω|² dx`, and `C3D_agmon⁴ = 169 / (2π⁴)`. -/
theorem unconditional_vortexStretching_le_agmon_3d
    {u : R3 → R3} (hu3 : ContDiff ℝ 3 u) (hpu : IsPeriodic3D u)
    (hdiv : ∀ x : R3, div3D u x = 0)
    (hmean : ∀ c : Fin 3, torusIntegral (fun x => u x c) = 0) :
    let Z : ℝ := (1 / 2 : ℝ) * torusIntegral (fun x => dot3D (curl3D u x) (curl3D u x))
    let P : ℝ := palinstrophy3D u
    |vortexStretching3D u| ≤
      C3D_agmon * (Real.sqrt (Real.sqrt Z)) ^ 3 * (Real.sqrt (Real.sqrt P)) ^ 3 := by
  intro Z P
  have hu2 : ContDiff ℝ 2 u := cd2_of_3_9a hu3
  have hu1 : ContDiff ℝ 1 u := cd1_of_2_9a hu2
  have hw2 : ContDiff ℝ 2 (curl3D u) := contDiff_two_curl3D hu3
  have hw1 : ContDiff ℝ 1 (curl3D u) := cd1_of_2_9a hw2
  have hc_w2 : Continuous (fun x => dot3D (curl3D u x) (curl3D u x)) := by
    unfold dot3D
    have c0 := (contDiff_pi.mp hw1 0).continuous
    have c1 := (contDiff_pi.mp hw1 1).continuous
    have c2 := (contDiff_pi.mp hw1 2).continuous
    exact ((c0.mul c0).add (c1.mul c1)).add (c2.mul c2)
  have hc_gw : Continuous (gradNormSq3D (curl3D u)) := by
    unfold gradNormSq3D
    have h0 := contDiff_pi.mp hw1 0
    have h1 := contDiff_pi.mp hw1 1
    have h2 := contDiff_pi.mp hw1 2
    exact (((((((((continuous_partialDerivScalar_of_contDiff h0 0).pow 2).add
      ((continuous_partialDerivScalar_of_contDiff h0 1).pow 2)).add
      ((continuous_partialDerivScalar_of_contDiff h0 2).pow 2)).add
      ((continuous_partialDerivScalar_of_contDiff h1 0).pow 2)).add
      ((continuous_partialDerivScalar_of_contDiff h1 1).pow 2)).add
      ((continuous_partialDerivScalar_of_contDiff h1 2).pow 2)).add
      ((continuous_partialDerivScalar_of_contDiff h2 0).pow 2)).add
      ((continuous_partialDerivScalar_of_contDiff h2 1).pow 2)).add
      ((continuous_partialDerivScalar_of_contDiff h2 2).pow 2)
  have hc_int : Continuous (fun x => dot3D (u x) (directionalAdvection3D (curl3D u) (curl3D u) x)) := by
    unfold dot3D directionalAdvection3D
    have h0 := contDiff_pi.mp hw1 0
    have h1 := contDiff_pi.mp hw1 1
    have h2 := contDiff_pi.mp hw1 2
    have t0 := (contDiff_pi.mp hu1 0).continuous.mul
      (((h0.continuous.mul (continuous_partialDerivScalar_of_contDiff h0 0)).add
        (h1.continuous.mul (continuous_partialDerivScalar_of_contDiff h0 1))).add
        (h2.continuous.mul (continuous_partialDerivScalar_of_contDiff h0 2)))
    have t1 := (contDiff_pi.mp hu1 1).continuous.mul
      (((h0.continuous.mul (continuous_partialDerivScalar_of_contDiff h1 0)).add
        (h1.continuous.mul (continuous_partialDerivScalar_of_contDiff h1 1))).add
        (h2.continuous.mul (continuous_partialDerivScalar_of_contDiff h1 2)))
    have t2 := (contDiff_pi.mp hu1 2).continuous.mul
      (((h0.continuous.mul (continuous_partialDerivScalar_of_contDiff h2 0)).add
        (h1.continuous.mul (continuous_partialDerivScalar_of_contDiff h2 1))).add
        (h2.continuous.mul (continuous_partialDerivScalar_of_contDiff h2 2)))
    exact (t0.add t1).add t2
  have h2Z_nn : 0 ≤ torusIntegral (fun x => dot3D (curl3D u x) (curl3D u x)) :=
    torusIntegral_nonneg hc_w2 (fun x => dot3D_self_nonneg _)
  have hZ_nn : 0 ≤ Z := by dsimp only [Z]; linarith
  have hP_nn : 0 ≤ P := torusIntegral_nonneg hc_gw (fun x => gradNormSq3D_nonneg _ _)
  let M : ℝ := (13 / (4 * Real.pi ^ 2)) *
      Real.sqrt (torusIntegral (fun x => dot3D (curl3D u x) (curl3D u x))) * Real.sqrt P
  have hM_nn : 0 ≤ M := by dsimp only [M]; positivity
  have hpt_sq : ∀ x : R3,
      (dot3D (u x) (directionalAdvection3D (curl3D u) (curl3D u) x)) ^ 2 ≤
        M * dot3D (curl3D u x) (curl3D u x) * gradNormSq3D (curl3D u) x := fun x => by
    have h1 := pointwise_stretch_sq_le (u x) (curl3D u x)
      (partialDerivScalar (fun y => curl3D u y 0) x 0)
      (partialDerivScalar (fun y => curl3D u y 0) x 1)
      (partialDerivScalar (fun y => curl3D u y 0) x 2)
      (partialDerivScalar (fun y => curl3D u y 1) x 0)
      (partialDerivScalar (fun y => curl3D u y 1) x 1)
      (partialDerivScalar (fun y => curl3D u y 1) x 2)
      (partialDerivScalar (fun y => curl3D u y 2) x 0)
      (partialDerivScalar (fun y => curl3D u y 2) x 1)
      (partialDerivScalar (fun y => curl3D u y 2) x 2)
    have h2 : dot3D (u x) (u x) ≤ M := agmon_3d_torus_ns_velocity hu3 hpu hdiv hmean x
    have hwg_nn : 0 ≤ dot3D (curl3D u x) (curl3D u x) * gradNormSq3D (curl3D u) x :=
      mul_nonneg (dot3D_self_nonneg _) (gradNormSq3D_nonneg _ _)
    have hmul : dot3D (u x) (u x) * (dot3D (curl3D u x) (curl3D u x) * gradNormSq3D (curl3D u) x) ≤
        M * (dot3D (curl3D u x) (curl3D u x) * gradNormSq3D (curl3D u) x) :=
      mul_le_mul_of_nonneg_right h2 hwg_nn
    change (u x 0 * (curl3D u x 0 * partialDerivScalar (fun y => curl3D u y 0) x 0 +
      curl3D u x 1 * partialDerivScalar (fun y => curl3D u y 0) x 1 +
      curl3D u x 2 * partialDerivScalar (fun y => curl3D u y 0) x 2) +
      u x 1 * (curl3D u x 0 * partialDerivScalar (fun y => curl3D u y 1) x 0 +
      curl3D u x 1 * partialDerivScalar (fun y => curl3D u y 1) x 1 +
      curl3D u x 2 * partialDerivScalar (fun y => curl3D u y 1) x 2) +
      u x 2 * (curl3D u x 0 * partialDerivScalar (fun y => curl3D u y 2) x 0 +
      curl3D u x 1 * partialDerivScalar (fun y => curl3D u y 2) x 1 +
      curl3D u x 2 * partialDerivScalar (fun y => curl3D u y 2) x 2)) ^ 2 ≤ _
    unfold gradNormSq3D at hmul ⊢
    linarith
  -- Step A: If M = 0, the integrand is identically 0
  by_cases hM0 : M = 0
  · have hzero : ∀ x : R3, dot3D (u x) (directionalAdvection3D (curl3D u) (curl3D u) x) = 0 := by
      intro x
      have hsq := hpt_sq x
      rw [hM0] at hsq
      nlinarith [sq_nonneg (dot3D (u x) (directionalAdvection3D (curl3D u) (curl3D u) x))]
    rw [vortexStretching3D_eq_neg_ibp hu3 hpu, torusIntegral_congr hzero]
    have hti0 : torusIntegral (fun _ : R3 => (0 : ℝ)) = 0 := by
      unfold torusIntegral; simp
    rw [hti0, neg_zero, abs_zero]
    exact mul_nonneg (mul_nonneg C3D_agmon_nonneg (by positivity)) (by positivity)
  · -- Step B: M > 0 implies Z > 0 and P > 0; apply AM-GM with optimal α = √(M P / (2 Z))
    have hM_pos : 0 < M := lt_of_le_of_ne hM_nn (Ne.symm hM0)
    have hZ_pos : 0 < Z := by
      by_contra hle
      push Not at hle
      have hZ0 : Z = 0 := le_antisymm hle hZ_nn
      have h2Z0 : torusIntegral (fun x => dot3D (curl3D u x) (curl3D u x)) = 0 := by
        dsimp only [Z] at hZ0; linarith
      have : M = 0 := by dsimp only [M]; rw [h2Z0, Real.sqrt_zero]; ring
      exact hM0 this
    have hP_pos : 0 < P := by
      by_contra hle
      push Not at hle
      have hP0 : P = 0 := le_antisymm hle hP_nn
      have : M = 0 := by dsimp only [M]; rw [hP0, Real.sqrt_zero]; ring
      exact hM0 this
    let α : ℝ := Real.sqrt (M * P / (2 * Z))
    have hα_pos : 0 < α := Real.sqrt_pos.mpr (by positivity)
    have hpt_amgm : ∀ x : R3,
        dot3D (u x) (directionalAdvection3D (curl3D u) (curl3D u) x) ≤
          (α / 2) * dot3D (curl3D u x) (curl3D u x) + (M / (2 * α)) * gradNormSq3D (curl3D u) x ∧
        -(dot3D (u x) (directionalAdvection3D (curl3D u) (curl3D u) x)) ≤
          (α / 2) * dot3D (curl3D u x) (curl3D u x) + (M / (2 * α)) * gradNormSq3D (curl3D u) x := by
      intro x
      set S := dot3D (u x) (directionalAdvection3D (curl3D u) (curl3D u) x)
      set W := dot3D (curl3D u x) (curl3D u x)
      set G := gradNormSq3D (curl3D u) x
      have hW : 0 ≤ W := dot3D_self_nonneg _
      have hG : 0 ≤ G := gradNormSq3D_nonneg _ _
      have hR_nn : 0 ≤ (α / 2) * W + (M / (2 * α)) * G := by positivity
      have hdiff : ((α / 2) * W + (M / (2 * α)) * G) ^ 2 - M * W * G =
          ((α / 2) * W - (M / (2 * α)) * G) ^ 2 := by
        have hα0 : α ≠ 0 := ne_of_gt hα_pos
        field_simp
        ring
      have hsq_le : S ^ 2 ≤ ((α / 2) * W + (M / (2 * α)) * G) ^ 2 := by
        have h1 := hpt_sq x
        nlinarith [sq_nonneg ((α / 2) * W - (M / (2 * α)) * G)]
      constructor <;> nlinarith
    have hc_t1 : Continuous (fun x => (α / 2) * dot3D (curl3D u x) (curl3D u x)) :=
      continuous_const.mul hc_w2
    have hc_t2 : Continuous (fun x => (M / (2 * α)) * gradNormSq3D (curl3D u) x) :=
      continuous_const.mul hc_gw
    have hc_rhs : Continuous (fun x =>
        (α / 2) * dot3D (curl3D u x) (curl3D u x) + (M / (2 * α)) * gradNormSq3D (curl3D u) x) :=
      hc_t1.add hc_t2
    have hint_rhs : torusIntegral (fun x =>
        (α / 2) * dot3D (curl3D u x) (curl3D u x) + (M / (2 * α)) * gradNormSq3D (curl3D u) x) =
        α * Z + (M / (2 * α)) * P := by
      have hadd := torusIntegral_add hc_t1 hc_t2
      have hm1 := torusIntegral_const_mul (α / 2) hc_w2
      have hm2 := torusIntegral_const_mul (M / (2 * α)) hc_gw
      rw [hadd, hm1, hm2]
      dsimp only [Z, P, palinstrophy3D]
      ring
    have hpos_le : torusIntegral (fun x => dot3D (u x) (directionalAdvection3D (curl3D u) (curl3D u) x)) ≤
        α * Z + (M / (2 * α)) * P := by
      rw [← hint_rhs]
      exact torusIntegral_le_of_le hc_int hc_rhs (fun x => (hpt_amgm x).1)
    have hneg_le : -torusIntegral (fun x => dot3D (u x) (directionalAdvection3D (curl3D u) (curl3D u) x)) ≤
        α * Z + (M / (2 * α)) * P := by
      rw [← torusIntegral_neg hc_int, ← hint_rhs]
      exact torusIntegral_le_of_le hc_int.neg hc_rhs (fun x => (hpt_amgm x).2)
    have habs_le : |vortexStretching3D u| ≤ α * Z + (M / (2 * α)) * P := by
      rw [vortexStretching3D_eq_neg_ibp hu3 hpu, abs_neg, abs_le]
      exact ⟨by linarith, hpos_le⟩
    have h_eq : α * Z + (M / (2 * α)) * P =
        C3D_agmon * (Real.sqrt (Real.sqrt Z)) ^ 3 * (Real.sqrt (Real.sqrt P)) ^ 3 := by
      have hL_nn : 0 ≤ α * Z + (M / (2 * α)) * P := by positivity
      have hR_nn : 0 ≤ C3D_agmon * (Real.sqrt (Real.sqrt Z)) ^ 3 * (Real.sqrt (Real.sqrt P)) ^ 3 := by
        exact mul_nonneg (mul_nonneg C3D_agmon_nonneg (by positivity)) (by positivity)
      have hsq_eq : (α * Z + (M / (2 * α)) * P) ^ 2 =
          (C3D_agmon * (Real.sqrt (Real.sqrt Z)) ^ 3 * (Real.sqrt (Real.sqrt P)) ^ 3) ^ 2 := by
        have hα2 : α ^ 2 = M * P / (2 * Z) := Real.sq_sqrt (by positivity)
        have hα0 : α ≠ 0 := ne_of_gt hα_pos
        have hZ0 : Z ≠ 0 := ne_of_gt hZ_pos
        have hL2 : (α * Z + (M / (2 * α)) * P) ^ 2 = 2 * M * Z * P := by
          have hexp : (α * Z + (M / (2 * α)) * P) ^ 2 =
              α ^ 2 * Z ^ 2 + M * P * Z + M ^ 2 * P ^ 2 / (4 * α ^ 2) := by
            field_simp
            ring
          rw [hexp, hα2]
          field_simp
          ring
        have hC2 : C3D_agmon ^ 2 = 13 * Real.sqrt 2 / (2 * Real.pi ^ 2) := by
          unfold C3D_agmon; exact Real.sq_sqrt (by positivity)
        have hZ32 : ((Real.sqrt (Real.sqrt Z)) ^ 3) ^ 2 = Z * Real.sqrt Z := by
          calc ((Real.sqrt (Real.sqrt Z)) ^ 3) ^ 2
              = ((Real.sqrt (Real.sqrt Z)) ^ 2) ^ 3 := by ring
            _ = (Real.sqrt Z) ^ 3 := by rw [Real.sq_sqrt (Real.sqrt_nonneg _)]
            _ = (Real.sqrt Z) ^ 2 * Real.sqrt Z := by ring
            _ = Z * Real.sqrt Z := by rw [Real.sq_sqrt hZ_nn]
        have hP32 : ((Real.sqrt (Real.sqrt P)) ^ 3) ^ 2 = P * Real.sqrt P := by
          calc ((Real.sqrt (Real.sqrt P)) ^ 3) ^ 2
              = ((Real.sqrt (Real.sqrt P)) ^ 2) ^ 3 := by ring
            _ = (Real.sqrt P) ^ 3 := by rw [Real.sq_sqrt (Real.sqrt_nonneg _)]
            _ = (Real.sqrt P) ^ 2 * Real.sqrt P := by ring
            _ = P * Real.sqrt P := by rw [Real.sq_sqrt hP_nn]
        have h2Z_eq : torusIntegral (fun x => dot3D (curl3D u x) (curl3D u x)) = 2 * Z := by
          dsimp only [Z]; ring
        have hsq2Z : Real.sqrt (2 * Z) = Real.sqrt 2 * Real.sqrt Z :=
          Real.sqrt_mul (by norm_num) Z
        rw [hL2]
        calc 2 * M * Z * P
            = 2 * ((13 / (4 * Real.pi ^ 2)) * (Real.sqrt 2 * Real.sqrt Z) * Real.sqrt P) * Z * P := by
                dsimp only [M]; rw [h2Z_eq, hsq2Z]
          _ = (13 * Real.sqrt 2 / (2 * Real.pi ^ 2)) * (Z * Real.sqrt Z) * (P * Real.sqrt P) := by ring
          _ = C3D_agmon ^ 2 * ((Real.sqrt (Real.sqrt Z)) ^ 3) ^ 2 * ((Real.sqrt (Real.sqrt P)) ^ 3) ^ 2 := by
                rw [hC2, hZ32, hP32]
          _ = (C3D_agmon * (Real.sqrt (Real.sqrt Z)) ^ 3 * (Real.sqrt (Real.sqrt P)) ^ 3) ^ 2 := by ring
      nlinarith
    linarith

-- ============================================================================
-- SECTION 3: UNCONDITIONAL SHARP ENSTROPHY ODE & H¹ BASIN INVARIANCE
-- ============================================================================

private lemma enstrophy_nonneg_9a {u : ℝ → R3 → R3} {p : ℝ → R3 → ℝ} {ν : ℝ}
    (hns : IsPeriodicClassicalNS3D_C3 u p ν) {t : ℝ} (ht : t ≥ 0) :
    0 ≤ enstrophy u t := by
  have hu3 := hns.h_u_c3_global t ht
  have hw1 := cd1_of_2_9a (contDiff_two_curl3D hu3)
  have hc : Continuous (fun x => dot3D (curl3D (u t) x) (curl3D (u t) x)) := by
    unfold dot3D
    have c0 := (contDiff_pi.mp hw1 0).continuous
    have c1 := (contDiff_pi.mp hw1 1).continuous
    have c2 := (contDiff_pi.mp hw1 2).continuous
    exact ((c0.mul c0).add (c1.mul c1)).add (c2.mul c2)
  unfold enstrophy
  have h := torusIntegral_nonneg hc (fun x => dot3D_self_nonneg _)
  linarith

/-- **THEOREM 4 (Unconditional Sharp 3D Enstrophy Differential Inequality on `𝕋³`):**
    Combines Theorem 3 (`unconditional_vortexStretching_le_agmon_3d`), Milestone 7B Young absorption,
    and Milestone 4B sharp Wirtinger-Poincaré (`8π² Z ≤ P`) with ZERO extra hypotheses:
    1. `dZ/dt ≤ -(ν/4) P + (169 / (8π⁴ ν³)) Z³`,
    2. `dZ/dt ≤ ((169 / (8π⁴ ν³)) Z² - 2π² ν) Z`,
    3. Below `Z_crit_H1 ν = 4π³ ν² / 13`, `dZ/dt ≤ 0` (strictly `< 0` if `0 < Z < Z_crit_H1 ν`). -/
theorem unconditional_enstrophy_ode_torus3D
    {u : ℝ → R3 → R3} {p : ℝ → R3 → ℝ} {ν : ℝ}
    (hns : IsPeriodicClassicalNS3D_C3 u p ν)
    (hmean : ∀ s ≥ 0, ∀ c : Fin 3, torusIntegral (fun x => u s x c) = 0)
    {t : ℝ} (ht : t ≥ 0) :
    deriv (enstrophy u) t ≤
      -(ν / 4) * palinstrophy3D (u t) + (169 / (8 * Real.pi ^ 4 * ν ^ 3)) * (enstrophy u t) ^ 3 ∧
    deriv (enstrophy u) t ≤
      ((169 / (8 * Real.pi ^ 4 * ν ^ 3)) * (enstrophy u t) ^ 2 - 2 * Real.pi ^ 2 * ν) *
        enstrophy u t ∧
    (enstrophy u t ≤ Z_crit_H1 ν → deriv (enstrophy u) t ≤ 0) ∧
    (0 < enstrophy u t → enstrophy u t < Z_crit_H1 ν → deriv (enstrophy u) t < 0) := by
  have hν : 0 < ν := hns.h_nu_pos
  have hZ_nn : 0 ≤ enstrophy u t := enstrophy_nonneg_9a hns ht
  have hstr_abs := unconditional_vortexStretching_le_agmon_3d
    (hns.h_u_c3_global t ht) (hns.h_u_periodic t ht) (hns.h_incompressible t ht) (hmean t ht)
  have hstr : vortexStretching3D (u t) ≤
      C3D_agmon * (Real.sqrt (Real.sqrt (enstrophy u t))) ^ 3 *
        (Real.sqrt (Real.sqrt (palinstrophy3D (u t)))) ^ 3 :=
    le_trans (le_abs_self _) hstr_abs
  have hwall := supercritical_young_absorption_wall_torus3D hns ht C3D_agmon_nonneg hstr
  have hcoef : C3D_agmon ^ 4 / (4 * ν ^ 3) = 169 / (8 * Real.pi ^ 4 * ν ^ 3) := by
    rw [C3D_agmon_pow_four]; ring
  have h1 : deriv (enstrophy u) t ≤
      -(ν / 4) * palinstrophy3D (u t) +
        (169 / (8 * Real.pi ^ 4 * ν ^ 3)) * (enstrophy u t) ^ 3 := by
    rw [hcoef] at hwall; exact hwall.1
  have hwirt := (sharp_analytical_lemma4_bernstein_poincare_vorticity hns ht).1
  have h2 : deriv (enstrophy u) t ≤
      ((169 / (8 * Real.pi ^ 4 * ν ^ 3)) * (enstrophy u t) ^ 2 - 2 * Real.pi ^ 2 * ν) *
        enstrophy u t := by
    have hneg : -(ν / 4) * palinstrophy3D (u t) ≤ -2 * Real.pi ^ 2 * ν * enstrophy u t := by
      nlinarith
    nlinarith
  have hcrit_sq : (169 / (8 * Real.pi ^ 4 * ν ^ 3)) * (Z_crit_H1 ν) ^ 2 = 2 * Real.pi ^ 2 * ν := by
    unfold Z_crit_H1
    have hpi : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
    have hν0 : ν ≠ 0 := ne_of_gt hν
    field_simp
    ring
  have h3 : enstrophy u t ≤ Z_crit_H1 ν → deriv (enstrophy u) t ≤ 0 := by
    intro hle
    have hsq : (enstrophy u t) ^ 2 ≤ (Z_crit_H1 ν) ^ 2 := by nlinarith [Z_crit_H1_pos hν]
    have hc_pos : 0 ≤ 169 / (8 * Real.pi ^ 4 * ν ^ 3) := by positivity
    have hbr : (169 / (8 * Real.pi ^ 4 * ν ^ 3)) * (enstrophy u t) ^ 2 - 2 * Real.pi ^ 2 * ν ≤ 0 := by
      nlinarith
    have hmul := mul_nonpos_of_nonpos_of_nonneg hbr hZ_nn
    linarith
  have h4 : 0 < enstrophy u t → enstrophy u t < Z_crit_H1 ν → deriv (enstrophy u) t < 0 := by
    intro hZpos hlt
    have hsq : (enstrophy u t) ^ 2 < (Z_crit_H1 ν) ^ 2 := by nlinarith [Z_crit_H1_pos hν]
    have hc_pos : 0 < 169 / (8 * Real.pi ^ 4 * ν ^ 3) := by positivity
    have hbr : (169 / (8 * Real.pi ^ 4 * ν ^ 3)) * (enstrophy u t) ^ 2 - 2 * Real.pi ^ 2 * ν < 0 := by
      nlinarith
    have hmul := mul_neg_of_neg_of_pos hbr hZpos
    linarith
  exact ⟨h1, h2, h3, h4⟩

/-- **THEOREM 5 (Unconditional `H¹` Enstrophy Basin Invariance & Exponential Decay):**
    If at ANY finite time `t₀ ≥ 0`, `enstrophy u t₀ < Z_crit_H1 ν = 4π³ ν² / 13`, then
    unconditionally for ALL `t ≥ t₀`:
    1. `enstrophy u t ≤ enstrophy u t₀` (trapped forever inside the `H¹` basin),
    2. `enstrophy u t ≤ enstrophy u t₀ * exp(-lam0 (t - t₀))` with strict decay rate
       `lam0 = 2π² ν - (169 / (8π⁴ ν³)) Z(t₀)² > 0`,
    3. When `enstrophy u t₀ ≤ Z_crit_H1 ν / 2`, `enstrophy u t ≤ enstrophy u t₀ * exp(-(3/2) π² ν (t - t₀))`. -/
theorem unconditional_H1_enstrophy_basin_invariance_and_exp_decay_torus3D
    {u : ℝ → R3 → R3} {p : ℝ → R3 → ℝ} {ν : ℝ}
    (hns : IsPeriodicClassicalNS3D_C3 u p ν)
    (hmean : ∀ s ≥ 0, ∀ c : Fin 3, torusIntegral (fun x => u s x c) = 0)
    {t₀ : ℝ} (ht₀ : 0 ≤ t₀)
    (hbasin : enstrophy u t₀ < Z_crit_H1 ν) :
    let lam0 : ℝ := 2 * Real.pi ^ 2 * ν - (169 / (8 * Real.pi ^ 4 * ν ^ 3)) * (enstrophy u t₀) ^ 2
    0 < lam0 ∧
    (∀ t ≥ t₀, enstrophy u t ≤ enstrophy u t₀) ∧
    (∀ t ≥ t₀, enstrophy u t ≤ enstrophy u t₀ * Real.exp (-lam0 * (t - t₀))) ∧
    (enstrophy u t₀ ≤ Z_crit_H1 ν / 2 →
      ∀ t ≥ t₀, enstrophy u t ≤ enstrophy u t₀ * Real.exp (-(3 / 2 * Real.pi ^ 2 * ν) * (t - t₀))) := by
  intro lam0
  have hν : 0 < ν := hns.h_nu_pos
  have hZ0_nn : 0 ≤ enstrophy u t₀ := enstrophy_nonneg_9a hns ht₀
  have hcrit_sq : (169 / (8 * Real.pi ^ 4 * ν ^ 3)) * (Z_crit_H1 ν) ^ 2 = 2 * Real.pi ^ 2 * ν := by
    unfold Z_crit_H1
    have hpi : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
    have hν0 : ν ≠ 0 := ne_of_gt hν
    field_simp
    ring
  have hlam0_pos : 0 < lam0 := by
    dsimp only [lam0]
    have hsq : (enstrophy u t₀) ^ 2 < (Z_crit_H1 ν) ^ 2 := by nlinarith [Z_crit_H1_pos hν]
    have hc_pos : 0 < 169 / (8 * Real.pi ^ 4 * ν ^ 3) := by positivity
    nlinarith
  have h_inv : ∀ t ≥ t₀, enstrophy u t ≤ enstrophy u t₀ := by
    intro T hT
    by_contra hgt
    push Not at hgt
    let M : ℝ := min ((enstrophy u t₀ + Z_crit_H1 ν) / 2) (enstrophy u T)
    have hZ0_lt_M : enstrophy u t₀ < M := lt_min (by linarith) hgt
    have hM_lt_crit : M < Z_crit_H1 ν := lt_of_le_of_lt (min_le_left _ _) (by linarith)
    have hM_le_ZT : M ≤ enstrophy u T := min_le_right _ _
    have hZ_cont : ContinuousOn (enstrophy u) (Set.Icc t₀ T) :=
      fun s hs => (hasDerivAt_enstrophy_evolution_3D hns (le_trans ht₀ hs.1)).1.continuousAt.continuousWithinAt
    let S : Set ℝ := Set.Icc t₀ T ∩ (enstrophy u) ⁻¹' Set.Ici M
    have hS_closed : IsClosed S :=
      hZ_cont.preimage_isClosed_of_isClosed isClosed_Icc isClosed_Ici
    have hS_ne : S.Nonempty := ⟨T, ⟨⟨hT, le_rfl⟩, hM_le_ZT⟩⟩
    have hS_bdd : BddBelow S := ⟨t₀, fun s hs => hs.1.1⟩
    let t₁ : ℝ := sInf S
    have ht₁_mem : t₁ ∈ S := hS_closed.csInf_mem hS_ne hS_bdd
    have ht₀_le_t₁ : t₀ ≤ t₁ := ht₁_mem.1.1
    have ht₁_le_T : t₁ ≤ T := ht₁_mem.1.2
    have hM_le_Zt₁ : M ≤ enstrophy u t₁ := ht₁_mem.2
    have ht₀_lt_t₁ : t₀ < t₁ := by
      refine lt_of_le_of_ne ht₀_le_t₁ ?_
      intro heq
      rw [← heq] at hM_le_Zt₁
      linarith
    have hZ_cont1 : ContinuousOn (enstrophy u) (Set.Icc t₀ t₁) :=
      hZ_cont.mono (Set.Icc_subset_Icc_right ht₁_le_T)
    have hZ_deriv1 : ∀ s ∈ Set.Ioo t₀ t₁,
        HasDerivAt (enstrophy u) (deriv (enstrophy u) s) s := fun s hs => by
      have hd := hasDerivAt_enstrophy_evolution_3D hns (le_trans ht₀ (le_of_lt hs.1))
      rw [hd.2]; exact hd.1
    obtain ⟨c, hc_mem, hc_eq⟩ := exists_hasDerivAt_eq_slope (enstrophy u) (deriv (enstrophy u))
      ht₀_lt_t₁ hZ_cont1 hZ_deriv1
    have hc_not_S : c ∉ S := fun hmem => not_le_of_gt hc_mem.2 (csInf_le hS_bdd hmem)
    have hc_lt_M : enstrophy u c < M := by
      by_contra hge
      push Not at hge
      exact hc_not_S ⟨⟨le_of_lt hc_mem.1, le_trans (le_of_lt hc_mem.2) ht₁_le_T⟩, hge⟩
    have hc_le_zero : deriv (enstrophy u) c ≤ 0 :=
      (unconditional_enstrophy_ode_torus3D hns hmean (le_trans ht₀ (le_of_lt hc_mem.1))).2.2.1
        (le_of_lt (lt_trans hc_lt_M hM_lt_crit))
    have hslope_pos : 0 < (enstrophy u t₁ - enstrophy u t₀) / (t₁ - t₀) :=
      div_pos (by linarith) (by linarith)
    linarith
  have h_exp : ∀ t ≥ t₀, enstrophy u t ≤ enstrophy u t₀ * Real.exp (-lam0 * (t - t₀)) := by
    intro T hT
    rcases eq_or_lt_of_le hT with rfl | hT_gt
    · simp
    · let g : ℝ → ℝ := fun s => Real.exp (lam0 * (s - t₀)) * enstrophy u s
      let g' : ℝ → ℝ := fun s =>
        Real.exp (lam0 * (s - t₀)) * (deriv (enstrophy u) s + lam0 * enstrophy u s)
      have hg_deriv : ∀ s ≥ t₀, HasDerivAt g (g' s) s := fun s hs => by
        have h1 : HasDerivAt (fun r : ℝ => lam0 * (r - t₀)) lam0 s := by
          have ha : HasDerivAt (fun r : ℝ => r - t₀) 1 s := (hasDerivAt_id s).sub_const t₀
          simpa [mul_one] using ha.const_mul lam0
        have he : HasDerivAt (fun r : ℝ => Real.exp (lam0 * (r - t₀)))
            (Real.exp (lam0 * (s - t₀)) * lam0) s := h1.exp
        have hZ : HasDerivAt (enstrophy u) (deriv (enstrophy u) s) s := by
          have hd := hasDerivAt_enstrophy_evolution_3D hns (le_trans ht₀ hs)
          rw [hd.2]; exact hd.1
        have hprod := he.mul hZ
        convert hprod using 1
        dsimp only [g']; ring
      have hg_cont : ContinuousOn g (Set.Icc t₀ T) :=
        fun s hs => (hg_deriv s hs.1).continuousAt.continuousWithinAt
      obtain ⟨c, hc_mem, hc_eq⟩ := exists_hasDerivAt_eq_slope g g' hT_gt hg_cont
        (fun s hs => hg_deriv s (le_of_lt hs.1))
      have hc_ge : c ≥ t₀ := le_of_lt hc_mem.1
      have hZc_le : enstrophy u c ≤ enstrophy u t₀ := h_inv c hc_ge
      have hZc_nn : 0 ≤ enstrophy u c := enstrophy_nonneg_9a hns (le_trans ht₀ hc_ge)
      have hode_c := (unconditional_enstrophy_ode_torus3D hns hmean (le_trans ht₀ hc_ge)).2.1
      have hcoef_nn : 0 ≤ 169 / (8 * Real.pi ^ 4 * ν ^ 3) := by positivity
      have hsq_le : (enstrophy u c) ^ 2 ≤ (enstrophy u t₀) ^ 2 := by nlinarith
      have hbr_le : (169 / (8 * Real.pi ^ 4 * ν ^ 3)) * (enstrophy u c) ^ 2 - 2 * Real.pi ^ 2 * ν ≤ -lam0 := by
        dsimp only [lam0]; nlinarith
      have hdz_le : deriv (enstrophy u) c + lam0 * enstrophy u c ≤ 0 := by
        nlinarith [mul_le_mul_of_nonneg_right hbr_le hZc_nn]
      have hg'_le : g' c ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos (le_of_lt (Real.exp_pos _)) hdz_le
      have hgT_le : g T ≤ g t₀ := by
        have hpos : 0 < T - t₀ := by linarith
        have hdiv : (g T - g t₀) / (T - t₀) ≤ 0 := by linarith
        have hsub : g T - g t₀ ≤ 0 := by
          rcases div_nonpos_iff.mp hdiv with ⟨_, hle⟩ | ⟨hge, _⟩
          · linarith
          · exact hge
        linarith
      have hg0 : g t₀ = enstrophy u t₀ := by dsimp only [g]; simp
      rw [hg0] at hgT_le
      dsimp only [g] at hgT_le
      have hexp_pos : 0 < Real.exp (-lam0 * (T - t₀)) := Real.exp_pos _
      have hmul := mul_le_mul_of_nonneg_right hgT_le (le_of_lt hexp_pos)
      have hcancel : Real.exp (lam0 * (T - t₀)) * enstrophy u T * Real.exp (-lam0 * (T - t₀)) =
          enstrophy u T := by
        calc Real.exp (lam0 * (T - t₀)) * enstrophy u T * Real.exp (-lam0 * (T - t₀))
            = enstrophy u T * (Real.exp (lam0 * (T - t₀)) * Real.exp (-lam0 * (T - t₀))) := by ring
          _ = enstrophy u T * Real.exp (lam0 * (T - t₀) + -lam0 * (T - t₀)) := by rw [← Real.exp_add]
          _ = enstrophy u T := by simp
      linarith
  have h_half : enstrophy u t₀ ≤ Z_crit_H1 ν / 2 →
      ∀ t ≥ t₀, enstrophy u t ≤ enstrophy u t₀ * Real.exp (-(3 / 2 * Real.pi ^ 2 * ν) * (t - t₀)) := by
    intro hhalf t ht
    have hlam_ge : 3 / 2 * Real.pi ^ 2 * ν ≤ lam0 := by
      dsimp only [lam0]
      have hsq : (enstrophy u t₀) ^ 2 ≤ (Z_crit_H1 ν) ^ 2 / 4 := by nlinarith [Z_crit_H1_pos hν]
      have hc_nn : 0 ≤ 169 / (8 * Real.pi ^ 4 * ν ^ 3) := by positivity
      nlinarith
    have hexp_le : Real.exp (-lam0 * (t - t₀)) ≤ Real.exp (-(3 / 2 * Real.pi ^ 2 * ν) * (t - t₀)) :=
      Real.exp_le_exp.mpr (by nlinarith)
    exact le_trans (h_exp t ht) (mul_le_mul_of_nonneg_left hexp_le hZ0_nn)
  exact ⟨hlam0_pos, h_inv, h_exp, h_half⟩

-- ============================================================================
-- SECTION 4: UNCONDITIONAL PALINSTROPHY INTEGRAL & FINITE-TIME H² ENTRY
-- ============================================================================

/-- **THEOREM 6 (Unconditional Global Palinstrophy Integral & Finite-Time `H²` Threshold Entry):**
    Inside the half-critical `H¹` basin `enstrophy u t₀ ≤ Z_crit_H1 ν / 2`:
    1. `Z(T) + (3ν/16) ∫_{t₀}^T P(s) ds ≤ Z(t₀)` for all `T ≥ t₀` (unconditional dissipation bound),
    2. For any `P_target > 0` and any time window `Δ > 16 Z(t₀) / (3 ν P_target)`, there exists
       `T_enter ∈ [t₀, t₀ + Δ]` with `palinstrophy3D (u T_enter) < P_target` (in particular
       hitting the Milestone 8A `H²` threshold `π⁶ ν² / 27136`). -/
theorem unconditional_H1_basin_palinstrophy_integral_and_H2_entry_torus3D
    {u : ℝ → R3 → R3} {p : ℝ → R3 → ℝ} {ν : ℝ}
    (hns : IsPeriodicClassicalNS3D_C3 u p ν)
    (hmean : ∀ s ≥ 0, ∀ c : Fin 3, torusIntegral (fun x => u s x c) = 0)
    (hP_cont : Continuous (fun s : ℝ => palinstrophy3D (u s)))
    {t₀ : ℝ} (ht₀ : 0 ≤ t₀)
    (hhalf : enstrophy u t₀ ≤ Z_crit_H1 ν / 2) :
    (∀ T ≥ t₀,
      enstrophy u T + (3 * ν / 16) * (∫ s in t₀..T, palinstrophy3D (u s)) ≤ enstrophy u t₀) ∧
    (∀ P_target Δ : ℝ, 0 < P_target → 0 < Δ →
      16 * enstrophy u t₀ / (3 * ν * P_target) < Δ →
      ∃ T_enter ∈ Set.Icc t₀ (t₀ + Δ), palinstrophy3D (u T_enter) < P_target) := by
  have hν : 0 < ν := hns.h_nu_pos
  have hbasin : enstrophy u t₀ < Z_crit_H1 ν := by linarith [Z_crit_H1_pos hν]
  have hinv := (unconditional_H1_enstrophy_basin_invariance_and_exp_decay_torus3D
    hns hmean ht₀ hbasin).2.1
  have hcrit_sq : (169 / (8 * Real.pi ^ 4 * ν ^ 3)) * (Z_crit_H1 ν) ^ 2 = 2 * Real.pi ^ 2 * ν := by
    unfold Z_crit_H1
    have hpi : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
    have hν0 : ν ≠ 0 := ne_of_gt hν
    field_simp; ring
  have hbal : ∀ T ≥ t₀,
      enstrophy u T + (3 * ν / 16) * (∫ s in t₀..T, palinstrophy3D (u s)) ≤ enstrophy u t₀ := by
    intro T hT
    rcases eq_or_lt_of_le hT with rfl | hT_gt
    · simp
    · let h : ℝ → ℝ := fun r => enstrophy u r + (3 * ν / 16) * (∫ s in t₀..r, palinstrophy3D (u s))
      let h' : ℝ → ℝ := fun r => deriv (enstrophy u) r + (3 * ν / 16) * palinstrophy3D (u r)
      have hh_deriv : ∀ r ≥ t₀, HasDerivAt h (h' r) r := fun r hr => by
        have hZ : HasDerivAt (enstrophy u) (deriv (enstrophy u) r) r := by
          have hd := hasDerivAt_enstrophy_evolution_3D hns (le_trans ht₀ hr)
          rw [hd.2]; exact hd.1
        have hI : HasDerivAt (fun q => ∫ s in t₀..q, palinstrophy3D (u s)) (palinstrophy3D (u r)) r :=
          intervalIntegral.integral_hasDerivAt_right
            (hP_cont.intervalIntegrable t₀ r)
            (hP_cont.stronglyMeasurableAtFilter volume (nhds r))
            hP_cont.continuousAt
        exact hZ.add (hI.const_mul (3 * ν / 16))
      have hh_cont : ContinuousOn h (Set.Icc t₀ T) :=
        fun r hr => (hh_deriv r hr.1).continuousAt.continuousWithinAt
      obtain ⟨c, hc_mem, hc_eq⟩ := exists_hasDerivAt_eq_slope h h' hT_gt hh_cont
        (fun r hr => hh_deriv r (le_of_lt hr.1))
      have hc_ge : c ≥ t₀ := le_of_lt hc_mem.1
      have hZc_le : enstrophy u c ≤ Z_crit_H1 ν / 2 := le_trans (hinv c hc_ge) hhalf
      have hZc_nn : 0 ≤ enstrophy u c := enstrophy_nonneg_9a hns (le_trans ht₀ hc_ge)
      have hode := (unconditional_enstrophy_ode_torus3D hns hmean (le_trans ht₀ hc_ge)).1
      have hwirt := (sharp_analytical_lemma4_bernstein_poincare_vorticity hns (le_trans ht₀ hc_ge)).1
      have hcubic : (169 / (8 * Real.pi ^ 4 * ν ^ 3)) * (enstrophy u c) ^ 3 ≤
          (ν / 16) * palinstrophy3D (u c) := by
        have hsq : (enstrophy u c) ^ 2 ≤ (Z_crit_H1 ν) ^ 2 / 4 := by nlinarith [Z_crit_H1_pos hν]
        have hc_nn : 0 ≤ 169 / (8 * Real.pi ^ 4 * ν ^ 3) := by positivity
        have hstep1 : (169 / (8 * Real.pi ^ 4 * ν ^ 3)) * (enstrophy u c) ^ 2 ≤
            (1 / 2) * Real.pi ^ 2 * ν := by nlinarith
        have hstep2 : (169 / (8 * Real.pi ^ 4 * ν ^ 3)) * (enstrophy u c) ^ 3 ≤
            (1 / 2) * Real.pi ^ 2 * ν * enstrophy u c := by
          have := mul_le_mul_of_nonneg_right hstep1 hZc_nn
          linarith
        nlinarith
      have hh'_le : h' c ≤ 0 := by dsimp only [h']; linarith
      have hhT_le : h T ≤ h t₀ := by
        have hdiv : (h T - h t₀) / (T - t₀) ≤ 0 := by linarith
        have hsub : h T - h t₀ ≤ 0 := by
          rcases div_nonpos_iff.mp hdiv with ⟨_, hle⟩ | ⟨hge, _⟩
          · linarith
          · exact hge
        linarith
      have hh0 : h t₀ = enstrophy u t₀ := by dsimp only [h]; simp
      rw [hh0] at hhT_le
      exact hhT_le
  have hentry : ∀ P_target Δ : ℝ, 0 < P_target → 0 < Δ →
      16 * enstrophy u t₀ / (3 * ν * P_target) < Δ →
      ∃ T_enter ∈ Set.Icc t₀ (t₀ + Δ), palinstrophy3D (u T_enter) < P_target := by
    intro P_target Δ hPt hΔ hbig
    by_contra hnone
    push Not at hnone
    have hle_int : Δ * P_target ≤ ∫ s in t₀..(t₀ + Δ), palinstrophy3D (u s) := by
      have hc : (∫ _ in t₀..(t₀ + Δ), P_target) = Δ * P_target := by
        rw [intervalIntegral.integral_const, smul_eq_mul]; ring
      rw [← hc]
      exact intervalIntegral.integral_mono_on (by linarith)
        (continuous_const.intervalIntegrable t₀ (t₀ + Δ))
        (hP_cont.intervalIntegrable t₀ (t₀ + Δ))
        hnone
    have hb := hbal (t₀ + Δ) (by linarith)
    have hZ_end_nn : 0 ≤ enstrophy u (t₀ + Δ) := enstrophy_nonneg_9a hns (by linarith)
    have hint_le : (3 * ν / 16) * (Δ * P_target) ≤ enstrophy u t₀ := by
      have hmul := mul_le_mul_of_nonneg_left hle_int (by positivity : (0 : ℝ) ≤ 3 * ν / 16)
      linarith
    have hbig' : 16 * enstrophy u t₀ < Δ * (3 * ν * P_target) :=
      (div_lt_iff₀ (by positivity)).mp hbig
    linarith
  exact ⟨hbal, hentry⟩

-- ============================================================================
-- SECTION 5: UNCONDITIONAL FINITE-TIME WATERFALL TRAP & MILESTONE 9A MASTER
-- ============================================================================

/-- **THEOREM 7 (Unconditional Finite-Time Enstrophy Trap — "Leaf Over the Waterfall"):**
    By Leray's global enstrophy dissipation law (`∫₀^T Z(s) ds ≤ E₀ / (2ν)`), for ANY
    target threshold `Z_target > 0` and any horizon `T > E₀ / (2 ν Z_target)`, there
    unconditionally exists a finite capture time `t* ∈ [0, T]` with `enstrophy u t* < Z_target`. -/
theorem unconditional_finite_time_enstrophy_trap_torus3D
    {u : ℝ → R3 → R3} {p : ℝ → R3 → ℝ} {ν Z_target T : ℝ}
    (hns : IsPeriodicClassicalNS3D_C3 u p ν)
    (hZt : 0 < Z_target)
    (hT_big : kineticEnergy u 0 / (2 * ν * Z_target) < T) :
    ∃ t_star ∈ Set.Icc (0 : ℝ) T, enstrophy u t_star < Z_target := by
  have hν : 0 < ν := hns.h_nu_pos
  have hE0_nn : 0 ≤ kineticEnergy u 0 := by
    have hbal := global_leray_energy_balance_and_bound hns (le_refl (0 : ℝ))
    exact hbal.2.1
  have hT_pos : 0 < T := lt_of_le_of_lt (by positivity) hT_big
  have hT_nn : 0 ≤ T := le_of_lt hT_pos
  have hZ_cont : ContinuousOn (enstrophy u) (Set.Icc 0 T) :=
    fun s hs => (hasDerivAt_enstrophy_evolution_3D hns hs.1).1.continuousAt.continuousWithinAt
  have hZ_int : IntervalIntegrable (enstrophy u) volume 0 T :=
    hZ_cont.intervalIntegrable_of_Icc hT_nn
  by_contra hnone
  push Not at hnone
  have hlow : T * Z_target ≤ ∫ s in (0 : ℝ)..T, enstrophy u s := by
    have hc : (∫ _ in (0 : ℝ)..T, Z_target) = T * Z_target := by
      rw [intervalIntegral.integral_const, smul_eq_mul]; ring
    rw [← hc]
    exact intervalIntegral.integral_mono_on hT_nn
      (continuous_const.intervalIntegrable 0 T) hZ_int hnone
  have hleray := (global_enstrophy_time_integral_bound hns hT_nn).2
  have hTZ_le : T * Z_target ≤ kineticEnergy u 0 / (2 * ν) := le_trans hlow hleray
  have hbig' : kineticEnergy u 0 < T * (2 * ν * Z_target) :=
    (div_lt_iff₀ (by positivity)).mp hT_big
  have hmul : 2 * ν * (T * Z_target) ≤ kineticEnergy u 0 := by
    have := (le_div_iff₀ (by positivity : (0 : ℝ) < 2 * ν)).mp hTZ_le
    linarith
  linarith

/-- **THEOREM 8 (MILESTONE 9A MASTER THEOREM — Unconditional Waterfall Trap to Exponential River):**
    For ANY mean-zero 3D Navier-Stokes classical solution `(u, p)` on `𝕋³` with arbitrary initial
    energy `E₀ = kineticEnergy u 0` and viscosity `ν > 0`, beyond the explicit finite trap horizon
    `T_trap_H1 E₀ ν = 13 E₀ / (4 π³ ν³)`:
    1. Unconditional finite-time capture into the half-critical `H¹` basin:
       `∃ t* ∈ [0, T], enstrophy u t* < Z_crit_H1 ν / 2 = 2π³ ν² / 13`;
    2. Permanent `H¹` basin trapping and global exponential decay for ALL `t ≥ t*`:
       `enstrophy u t ≤ enstrophy u t* * exp(-(3/2) π² ν (t - t*))`;
    3. If `palinstrophy3D (u ·)` is continuous, uniform global palinstrophy dissipation
       `Z(T') + (3ν/16) ∫_{t*}^{T'} P(s) ds ≤ Z(t*)` for ALL `T' ≥ t*`, AND unconditional
       finite-time entry into the Milestone 8A `H²` threshold `palinstrophy3D (u T_enter) < π⁶ ν² / 27136`. -/
theorem unconditional_waterfall_trap_to_exponential_river_torus3D
    {u : ℝ → R3 → R3} {p : ℝ → R3 → ℝ} {ν T : ℝ}
    (hns : IsPeriodicClassicalNS3D_C3 u p ν)
    (hmean : ∀ s ≥ 0, ∀ c : Fin 3, torusIntegral (fun x => u s x c) = 0)
    (hT_trap : T_trap_H1 (kineticEnergy u 0) ν < T) :
    ∃ t_star ∈ Set.Icc (0 : ℝ) T,
      enstrophy u t_star < Z_crit_H1 ν / 2 ∧
      (∀ t ≥ t_star, enstrophy u t ≤ enstrophy u t_star) ∧
      (∀ t ≥ t_star, enstrophy u t ≤
        enstrophy u t_star * Real.exp (-(3 / 2 * Real.pi ^ 2 * ν) * (t - t_star))) ∧
      (Continuous (fun s : ℝ => palinstrophy3D (u s)) →
        (∀ T' ≥ t_star,
          enstrophy u T' + (3 * ν / 16) * (∫ s in t_star..T', palinstrophy3D (u s)) ≤
            enstrophy u t_star) ∧
        (∀ Δ : ℝ, 0 < Δ →
          16 * 27136 * enstrophy u t_star / (3 * Real.pi ^ 6 * ν ^ 3) < Δ →
          ∃ T_enter ∈ Set.Icc t_star (t_star + Δ),
            palinstrophy3D (u T_enter) < Real.pi ^ 6 * ν ^ 2 / 27136)) := by
  have hν : 0 < ν := hns.h_nu_pos
  have hZhalf_pos : 0 < Z_crit_H1 ν / 2 := half_pos (Z_crit_H1_pos hν)
  have hT_eq : kineticEnergy u 0 / (2 * ν * (Z_crit_H1 ν / 2)) =
      T_trap_H1 (kineticEnergy u 0) ν := by
    unfold Z_crit_H1 T_trap_H1
    have hpi : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
    have hν0 : ν ≠ 0 := ne_of_gt hν
    field_simp
  have hT_big : kineticEnergy u 0 / (2 * ν * (Z_crit_H1 ν / 2)) < T := by
    rw [hT_eq]; exact hT_trap
  obtain ⟨t_star, ht_mem, ht_cap⟩ :=
    unconditional_finite_time_enstrophy_trap_torus3D hns hZhalf_pos hT_big
  have hbasin : enstrophy u t_star < Z_crit_H1 ν := by linarith [Z_crit_H1_pos hν]
  have hdec := unconditional_H1_enstrophy_basin_invariance_and_exp_decay_torus3D
    hns hmean ht_mem.1 hbasin
  refine ⟨t_star, ht_mem, ht_cap, hdec.2.1, hdec.2.2.2 (le_of_lt ht_cap), ?_⟩
  intro hP_cont
  have hpal := unconditional_H1_basin_palinstrophy_integral_and_H2_entry_torus3D
    hns hmean hP_cont ht_mem.1 (le_of_lt ht_cap)
  refine ⟨hpal.1, ?_⟩
  intro Δ hΔ hbig
  have hPt_pos : 0 < Real.pi ^ 6 * ν ^ 2 / 27136 := by positivity
  have hreq : 16 * enstrophy u t_star / (3 * ν * (Real.pi ^ 6 * ν ^ 2 / 27136)) < Δ := by
    have heq : 16 * enstrophy u t_star / (3 * ν * (Real.pi ^ 6 * ν ^ 2 / 27136)) =
        16 * 27136 * enstrophy u t_star / (3 * Real.pi ^ 6 * ν ^ 3) := by
      have hpi : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
      have hν0 : ν ≠ 0 := ne_of_gt hν
      field_simp
    rw [heq]; exact hbig
  exact hpal.2 (Real.pi ^ 6 * ν ^ 2 / 27136) Δ hPt_pos hΔ hreq

-- ============================================================================
-- SECTION 6: AXIOM AUDIT TRAIL (0 sorryAx, 0 custom axioms)
-- ============================================================================

#print axioms vortexStretching3D_eq_neg_ibp
#print axioms agmon_3d_torus_ns_velocity
#print axioms unconditional_vortexStretching_le_agmon_3d
#print axioms unconditional_enstrophy_ode_torus3D
#print axioms unconditional_H1_enstrophy_basin_invariance_and_exp_decay_torus3D
#print axioms unconditional_H1_basin_palinstrophy_integral_and_H2_entry_torus3D
#print axioms unconditional_finite_time_enstrophy_trap_torus3D
#print axioms unconditional_waterfall_trap_to_exponential_river_torus3D

end GarryEnstrophyBasin3D