import Lake

open Lake DSL

package formal_proofs_mathlib where

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"

@[default_target]
lean_lib GarryNavierStokesMathlib where

lean_lib Real3DVectorCalculus where

lean_lib VorticityEquation3D where

lean_lib LerayEnergyTorus3D where

lean_lib LerayEnergyLaw3D where

lean_lib PoincareSobolevTorus3D where

lean_lib FourierSpectralTorus3D where

lean_lib SpectralOperatorsTorus3D where

lean_lib ParsevalSobolevTorus3D where

lean_lib SobolevEmbeddingTorus3D where

lean_lib SpectralAlgebraTorus3D where

lean_lib SpectralBilinearTorus3D where

lean_lib DuhamelOperatorTorus3D where

lean_lib LocalExistenceTorus3D where

lean_lib GlobalRegularityCriteriaTorus3D where

lean_lib GarrySupercriticalBridgeTorus3D where

@[default_target]
lean_lib SupercriticalBoundaryAuditTorus3D where

lean_lib HigherSobolevBootstrapTorus3D where

lean_lib SmoothClassicalSynthesisTorus3D where

lean_lib EnstrophyBasinTorus3D where

lean_lib CriticalProdiSerrinTorus3D where

lean_lib GarryWaterfallCertificateTorus3D where

lean_lib WholeSpaceR3Integral where

lean_lib WholeSpaceR3Agmon where

lean_lib WholeSpaceR3EnstrophyWaterfall where

lean_lib GlobalUniquenessNS3D where

lean_lib GlobalRegularityBootstrapNS3D where

lean_lib TwoTierBoundaryAuditNS3D where

lean_lib StrainPressureGeometryNS3D where

lean_lib SupercriticalFrontierProbeNS3D where

lean_lib HeatLerayMildNS3D where

lean_lib ConcreteNS3DClosures where

lean_lib ClassicalPDEBridgeNS3D where

lean_lib GeometricDepletionCriteriaNS3D where

lean_lib AdversarialSupercriticalLabNS3D where

lean_lib WholeSpaceR3LocalExistence where

lean_lib SpacetimeSmoothnessNS3D where

lean_lib SchwartzClayPackagingNS3D where

@[default_target]
lean_lib SupercriticalClayFrontier15G where