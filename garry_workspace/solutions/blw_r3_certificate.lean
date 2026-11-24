-- ==============================================================================
-- GARRYULT v4.0.0 — MILESTONE 15G BLW WATERFALL LEAN 4 CERTIFICATE
-- Witness Seal: 0x76039629 | Scale: 10^6 (Micro) | 0 sorryAx
-- Links directly to `SupercriticalClayFrontier15G` (GarryBLWWaterfallWitnessR3)
-- ==============================================================================

import SupercriticalClayFrontier15G

set_option autoImplicit false

open GarryReal3DCalculus
open GarryWholeSpaceR3
open GarryAdversarialSupercriticalLabNS3D
open GarrySupercriticalClayFrontier15G

namespace GarryBlwCertifiedWitnessR3

noncomputable def nuCert : ℝ := (100000 : ℝ) / (1000000 : ℝ)
noncomputable def eTermCert : ℝ := (1500000 : ℝ) / (1000000 : ℝ)

noncomputable def tGridCert : ℕ → ℝ
  | 0 => (0 : ℝ) / (1000000 : ℝ)
  | 1 => (250000 : ℝ) / (1000000 : ℝ)
  | 2 => (600000 : ℝ) / (1000000 : ℝ)
  | 3 => (1100000 : ℝ) / (1000000 : ℝ)
  | 4 => (1800000 : ℝ) / (1000000 : ℝ)
  | _ => (1800000 : ℝ) / (1000000 : ℝ)

noncomputable def zCapCert : ℕ → ℝ
  | 0 => (4000000 : ℝ) / (1000000 : ℝ)
  | 1 => (3200000 : ℝ) / (1000000 : ℝ)
  | 2 => (2600000 : ℝ) / (1000000 : ℝ)
  | 3 => (2100000 : ℝ) / (1000000 : ℝ)
  | 4 => (1800000 : ℝ) / (1000000 : ℝ)
  | _ => (1800000 : ℝ) / (1000000 : ℝ)

theorem nuCert_pos : 0 < nuCert := by
  unfold nuCert; norm_num

theorem blw_safe_steps_and_basin_capture :
    tGridCert 0 = 0 ∧
    (∀ k < 4, tGridCert k ≤ tGridCert (k + 1)) ∧
    (∀ k ≤ 4, 0 ≤ zCapCert k) ∧
    (∀ k < 4, 2 * (1 / (23328 * nuCert ^ 3)) * (zCapCert k) ^ 2 * (tGridCert (k + 1) - tGridCert k) ≤ 1 / 2) ∧
    eTermCert * zCapCert 4 < 46656 * nuCert ^ 4 := by
  refine ⟨by unfold tGridCert; norm_num, ?_, ?_, ?_, ?_⟩
  · intro k hk; interval_cases k <;> unfold tGridCert <;> norm_num
  · intro k hk; interval_cases k <;> unfold zCapCert <;> norm_num
  · intro k hk; interval_cases k <;> unfold nuCert tGridCert zCapCert <;> norm_num
  · unfold nuCert eTermCert zCapCert; norm_num

noncomputable def buildCertifiedWitnessR3 {u : ℝ → R3 → R3}
    (hnode : ∀ k ≤ 4, enstrophyR3 (u (tGridCert k)) ≤ zCapCert k) :
    GarryBLWWaterfallWitnessR3 u nuCert where
  steps := 4
  tGrid := tGridCert
  zCap := zCapCert
  ht0 := blw_safe_steps_and_basin_capture.1
  hmono := blw_safe_steps_and_basin_capture.2.1
  hzCap_nonneg := blw_safe_steps_and_basin_capture.2.2.1
  hnode_cap := hnode
  hsafe_step := by
    intro k hk
    have hmaster := milestone15_adversarial_supercritical_lab_master (E₀ := 1) (ν := nuCert) (by norm_num) nuCert_pos
    rw [hmaster.1.2.2.1]
    exact blw_safe_steps_and_basin_capture.2.2.2.1 k hk

#print axioms blw_safe_steps_and_basin_capture
#print axioms buildCertifiedWitnessR3

end GarryBlwCertifiedWitnessR3
