#!/usr/bin/env python3
"""Replay native elaboration, declaration linting, and transitive axiom checks.

The required root build is enforced. Diagnostic drivers live in temporary scratch only.
"""

import argparse
import hashlib
import json
import platform
import shutil
import subprocess
import tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
MODULES = [
    "RicciFlowSharpEstimate.Variational.Parameters",
    "RicciFlowSharpEstimate.Variational.PairFunctional",
    "RicciFlowSharpEstimate.Variational.Contacts",
    "RicciFlowSharpEstimate.Variational.FreeArc",
    "RicciFlowSharpEstimate.Variational.ObstacleProfile",
    "RicciFlowSharpEstimate.Analysis.ExponentialRemainder",
    "RicciFlowSharpEstimate.Variational.ObstaclePrimitives",
    "RicciFlowSharpEstimate.Variational.PairIteration",
    "RicciFlowSharpEstimate.Variational.Calibration",
    "RicciFlowSharpEstimate.Variational.OptimalValue",
    "RicciFlowSharpEstimate.Variational.PairRigidity",
    "RicciFlowSharpEstimate.Variational.ContactRegularity",
    "RicciFlowSharpEstimate.Variational.OptimizerRigidity",
    "RicciFlowSharpEstimate.Variational.ObstacleWeight",
    "RicciFlowSharpEstimate.Variational.ObstacleAnchoring",
    "RicciFlowSharpEstimate.Variational.RemainderCoercivity",
    "RicciFlowSharpEstimate.Variational.WeightedVariance",
    "RicciFlowSharpEstimate.Analysis.WeightedAnchor",
    "RicciFlowSharpEstimate.Analysis.ReflectionEnergy",
    "RicciFlowSharpEstimate.Variational.Stability",
    "RicciFlowSharpEstimate.Variational.HemisphereStability",
    "RicciFlowSharpEstimate.Analysis.SmoothFactor",
    "RicciFlowSharpEstimate.Geometry.RotationalProfile",
    "RicciFlowSharpEstimate.Geometry.RotationalPoleData",
    "RicciFlowSharpEstimate.Geometry.RotationalSphereMetric",
    "RicciFlowSharpEstimate.Geometry.BalancedSphereMetric",
    "RicciFlowSharpEstimate.LinearAlgebra.RankOneDeterminant",
    "RicciFlowSharpEstimate.Geometry.SphereHeightIntegral",
    "RicciFlowSharpEstimate.Geometry.RotationalVolume",
    "RicciFlowSharpEstimate.Geometry.RotationalDiagonalCurvature",
    "RicciFlowSharpEstimate.Geometry.RotationalCurvatureProfile",
    "RicciFlowSharpEstimate.Geometry.RotationalCoordinates",
    "RicciFlowSharpEstimate.Geometry.RotationalCoordinateRange",
    "RicciFlowSharpEstimate.Geometry.RotationalCurvature",
    "RicciFlowSharpEstimate.Geometry.CanonicalDerivatives",
    "RicciFlowSharpEstimate.Geometry.TraceFreeSymmetric",
    "RicciFlowSharpEstimate.Geometry.RotationalOneForms",
    "RicciFlowSharpEstimate.Geometry.OneFormDissipation",
    "RicciFlowSharpEstimate.Geometry.RotationalDissipation",
    "RicciFlowSharpEstimate.Geometry.ExactOneFormRoughLaplacian",
    "RicciFlowSharpEstimate.Geometry.SymmetricTensorContractions",
    "RicciFlowSharpEstimate.Geometry.RotationalCometric",
    "RicciFlowSharpEstimate.Geometry.MeridionalAction",
    "RicciFlowSharpEstimate.Geometry.RotationalMeridionalHessian",
    "RicciFlowSharpEstimate.Geometry.RotationalMeridionalReduction",
    "RicciFlowSharpEstimate.Geometry.OneFormDissipationNaturality",
    "RicciFlowSharpEstimate.Geometry.RotationalReflection",
    "RicciFlowSharpEstimate.Geometry.RotationalZonalOrthogonality",
    "RicciFlowSharpEstimate.Geometry.AlternatingSurfaceTensors",
    "RicciFlowSharpEstimate.Geometry.RotationalAreaForm",
    "RicciFlowSharpEstimate.Geometry.RotationalHodgeRotation",
    "RicciFlowSharpEstimate.Geometry.SurfaceRotationContractions",
    "RicciFlowSharpEstimate.Geometry.OneFormRotation",
    "RicciFlowSharpEstimate.Geometry.OneFormRotationDissipation",
    "RicciFlowSharpEstimate.Geometry.RotationalZonalReduction",
    "RicciFlowSharpEstimate.Analysis.ManifoldIntervalIntegral",
    "RicciFlowSharpEstimate.Geometry.RotationalCircleAction",
    "RicciFlowSharpEstimate.Geometry.TensorPullbackFamily",
    "RicciFlowSharpEstimate.Geometry.RotationalTensorAction",
    "RicciFlowSharpEstimate.Geometry.TensorIntervalIntegral",
    "RicciFlowSharpEstimate.Geometry.RotationalPairingIntegral",
    "RicciFlowSharpEstimate.Geometry.RotationalAverage",
    "RicciFlowSharpEstimate.Geometry.TensorIntegralContractions",
    "RicciFlowSharpEstimate.Geometry.RotationalAverageDerivatives",
    "RicciFlowSharpEstimate.Geometry.RotationalHaarDissipation",
    "RicciFlowSharpEstimate.Analysis.SmoothQuotient",
    "RicciFlowSharpEstimate.Analysis.SmoothParity",
    "RicciFlowSharpEstimate.Analysis.RotationCovectorPlane",
    "RicciFlowSharpEstimate.Geometry.RotationalStereographic",
    "RicciFlowSharpEstimate.Geometry.RotationalInvariantPoleForms",
    "RicciFlowSharpEstimate.Geometry.RotationalInvariantProfiles",
    "RicciFlowSharpEstimate.Geometry.RotationalInvariantClassification",
    "RicciFlowSharpEstimate.Geometry.OneFormScalars",
    "RicciFlowSharpEstimate.Geometry.TensorOrthonormalContractions",
    "RicciFlowSharpEstimate.Geometry.SurfaceTensorDecomposition",
    "RicciFlowSharpEstimate.Geometry.CanonicalTensorIntegration",
    "RicciFlowSharpEstimate.Geometry.SurfaceCovariantCommutator",
    "RicciFlowSharpEstimate.Geometry.OneFormSecondDerivativeNorm",
    "RicciFlowSharpEstimate.Geometry.SurfaceTensorDerivativeDecomposition",
    "RicciFlowSharpEstimate.Geometry.SurfaceTensorIntegration",
    "RicciFlowSharpEstimate.Geometry.OneFormScalarization",
    "RicciFlowSharpEstimate.Geometry.RotationalScalarization",
    "RicciFlowSharpEstimate.Geometry.OneFormScalarNaturality",
    "RicciFlowSharpEstimate.Geometry.RotationalAreaInvariance",
    "RicciFlowSharpEstimate.Geometry.RotationalScalarAverage",
    "RicciFlowSharpEstimate.Geometry.RotationalScalarCompatibility",
    "RicciFlowSharpEstimate.Analysis.CircleWirtinger",
    "RicciFlowSharpEstimate.Analysis.PolarEndpointBounds",
    "RicciFlowSharpEstimate.Analysis.PolarSquareCompletion",
    "RicciFlowSharpEstimate.Analysis.PolarScalarGap",
    "RicciFlowSharpEstimate.Geometry.RotationalPolarCoordinates",
    "RicciFlowSharpEstimate.Geometry.RotationalPolarDifferential",
    "RicciFlowSharpEstimate.Geometry.RotationalPolarIntegration",
    "RicciFlowSharpEstimate.Geometry.RotationalScalarGap",
    "RicciFlowSharpEstimate.Geometry.WeightedIntegralRigidity",
    "RicciFlowSharpEstimate.Geometry.OneFormDerivativeRigidity",
    "RicciFlowSharpEstimate.Geometry.RotationalRemainderBounds",
    "RicciFlowSharpEstimate.Geometry.RotationalRemainder",
    "RicciFlowSharpEstimate.Analysis.ReciprocalLogarithm",
    "RicciFlowSharpEstimate.Variational.ReciprocalProfile",
    "RicciFlowSharpEstimate.Variational.CriticalCap",
    "RicciFlowSharpEstimate.Geometry.HemispherePairFunctional",
    "RicciFlowSharpEstimate.Geometry.ConstantZonalAction",
    "RicciFlowSharpEstimate.Geometry.ConformalKillingOneForms",
    "RicciFlowSharpEstimate.Geometry.RotationalConformalKilling",
    "RicciFlowSharpEstimate.Geometry.RotationalCurvatureBounds",
    "RicciFlowSharpEstimate.Geometry.ConformalKillingSafety",
    "RicciFlowSharpEstimate.Analysis.EvenSmoothApproximation",
    "RicciFlowSharpEstimate.Variational.EvenReciprocalProfile",
    "RicciFlowSharpEstimate.Geometry.ReciprocalProfileAction",
    "RicciFlowSharpEstimate.Geometry.ConstantProbeContinuity",
    "RicciFlowSharpEstimate.Geometry.ConformalKillingStability",
    "RicciFlowSharpEstimate.Geometry.SmoothReciprocalRecovery",
    "RicciFlowSharpEstimate.Geometry.ConformalKillingSharpness",
    "RicciFlowSharpEstimate.Geometry.PullbackAlgebra",
    "RicciFlowSharpEstimate.Geometry.ConjugatedRotationalAverage",
    "RicciFlowSharpEstimate.Geometry.ConjugatedCircleAction",
    "RicciFlowSharpEstimate.Geometry.ConjugatedHaarDissipation",
    "RicciFlowSharpEstimate.Geometry.RepresentedRotationalMetric",
    "RicciFlowSharpEstimate.Geometry.ConjugatedZonalGeometry",
    "RicciFlowSharpEstimate.Geometry.RepresentedHaarGeometry",
    "RicciFlowSharpEstimate.Geometry.ConjugatedStability",
    "RicciFlowSharpEstimate.Geometry.ConformalKillingThreshold",
    "RicciFlowSharpEstimate.Geometry.AreaProfile",
    "RicciFlowSharpEstimate.Analysis.SecondPrimitive",
    "RicciFlowSharpEstimate.Geometry.AreaProfileCalculus",
    "RicciFlowSharpEstimate.Analysis.SmoothIntervalExtension",
    "RicciFlowSharpEstimate.Analysis.SmoothIntervalInverse",
    "RicciFlowSharpEstimate.Geometry.AreaAction",
    "RicciFlowSharpEstimate.Geometry.AreaActionBridge",
    "RicciFlowSharpEstimate.Geometry.AreaGeometricRealization",
    "RicciFlowSharpEstimate.Variational.ReciprocalProfileShape",
    "RicciFlowSharpEstimate.Analysis.ContinuousIntervalInverse",
    "RicciFlowSharpEstimate.Geometry.ReciprocalAreaGeometry",
    "RicciFlowSharpEstimate.Geometry.ReciprocalAreaSymmetry",
    "RicciFlowSharpEstimate.Analysis.PositiveSmoothBump",
    "RicciFlowSharpEstimate.Geometry.AreaPlateauInstability",
    "RicciFlowSharpEstimate.Geometry.CriticalAreaProfile",
    "RicciFlowSharpEstimate.Geometry.CriticalPlateauInstability",
    "RicciFlowSharpEstimate.Analysis.SampledBernstein",
    "RicciFlowSharpEstimate.Analysis.SymmetricBernstein",
    "RicciFlowSharpEstimate.Analysis.L1Subsequence",
    "RicciFlowSharpEstimate.Analysis.SymmetricMomentRecovery",
    "RicciFlowSharpEstimate.Geometry.AreaActionContinuity",
    "RicciFlowSharpEstimate.Geometry.ConstantCurvatureDissipation",
    "RicciFlowSharpEstimate.Geometry.CriticalCurvatureContraction",
    "RicciFlowSharpEstimate.Geometry.SmoothNegativeAreaRecovery",
    "RicciFlowSharpEstimate.Geometry.StrictRotationalWitness",
    "RicciFlowSharpEstimate.Geometry.RotationalThreshold",
    "RicciFlowSharpEstimate.Geometry.AreaActionFactorization",
    "RicciFlowSharpEstimate.Geometry.AreaActionVariation",
    "RicciFlowSharpEstimate.Geometry.AreaVariationGeometry",
    "RicciFlowSharpEstimate.Analysis.VolterraPairing",
    "RicciFlowSharpEstimate.Analysis.AffineIntervalVariation",
    "RicciFlowSharpEstimate.Geometry.AreaCurvaturePrimitives",
    "RicciFlowSharpEstimate.Geometry.AreaProbeRayleigh",
    "RicciFlowSharpEstimate.Geometry.AreaCurvatureVariation",
    "RicciFlowSharpEstimate.Geometry.AreaCurvatureOptimality",
    "RicciFlowSharpEstimate.Analysis.ClosedIntervalDerivatives",
    "RicciFlowSharpEstimate.Geometry.SmoothAreaNormalization",
    "RicciFlowSharpEstimate.Geometry.PhysicalProbeNonzero",
    "RicciFlowSharpEstimate.Geometry.NormalizedAreaAction",
    "RicciFlowSharpEstimate.Geometry.NormalizedAreaMass",
    "RicciFlowSharpEstimate.Geometry.NormalizedAreaHaar",
    "RicciFlowSharpEstimate.Geometry.NormalizedAreaVariation",
    "RicciFlowSharpEstimate.Geometry.NormalizedAreaRayleigh",
    "RicciFlowSharpEstimate.Analysis.ParabolicWeightedHardy",
    "RicciFlowSharpEstimate.Geometry.AreaWarpBounds",
    "RicciFlowSharpEstimate.Geometry.AreaProbeEnergy",
    "RicciFlowSharpEstimate.Geometry.AreaPolarMass",
    "RicciFlowSharpEstimate.Geometry.AreaActionCoercivity",
    "RicciFlowSharpEstimate.Analysis.ParabolicDerivativeEnergy",
    "RicciFlowSharpEstimate.Analysis.ParabolicPolarControl",
    "RicciFlowSharpEstimate.Geometry.AreaProbeRegularity",
    "RicciFlowSharpEstimate.Geometry.AreaActionPolarControl",
    "RicciFlowSharpEstimate.Analysis.BoundedWeakPairing",
    "RicciFlowSharpEstimate.Analysis.HilbertWeakSubsequence",
    "RicciFlowSharpEstimate.Analysis.InteriorSobolevCompactness",
    "RicciFlowSharpEstimate.Analysis.IntervalDerivativeEnergy",
    "RicciFlowSharpEstimate.Analysis.L2UniformIntegrability",
    "RicciFlowSharpEstimate.Analysis.L2WeakOrder",
    "RicciFlowSharpEstimate.Analysis.L2WeightedMassContinuity",
    "RicciFlowSharpEstimate.Analysis.LocallyUniformSubsequence",
    "RicciFlowSharpEstimate.Analysis.ParabolicSobolev",
    "RicciFlowSharpEstimate.Analysis.WeakDerivative",
    "RicciFlowSharpEstimate.Analysis.WeakDerivativeLimits",
    "RicciFlowSharpEstimate.Analysis.WeightedWeakDerivativeLimit",
    "RicciFlowSharpEstimate.Geometry.AreaCurvatureCompactness",
    "RicciFlowSharpEstimate.Geometry.AreaJointCompactness",
    "RicciFlowSharpEstimate.Geometry.AreaProbeCompactness",
    "RicciFlowSharpEstimate.Geometry.AreaUniformPrimitives",
    "RicciFlowSharpEstimate.Geometry.AreaWeakPrimitives",
    "RicciFlowSharpEstimate.Geometry.WeakAreaAction",
    "RicciFlowSharpEstimate.Analysis.BoundedWeakPairingLimits",
    "RicciFlowSharpEstimate.Analysis.L2PointwiseProducts",
    "RicciFlowSharpEstimate.Analysis.L2WeakLowerSemicontinuity",
    "RicciFlowSharpEstimate.Analysis.L2WeakMultipliers",
    "RicciFlowSharpEstimate.Geometry.AreaSublevelGraphBounds",
    "RicciFlowSharpEstimate.Geometry.AreaDerivativeProductLimit",
    "RicciFlowSharpEstimate.Geometry.AreaCurvatureProductLimits",
    "RicciFlowSharpEstimate.Geometry.AreaActionLowerSemicontinuity",
    "RicciFlowSharpEstimate.Geometry.AreaJointActionCompactness",
    "RicciFlowSharpEstimate.Analysis.HilbertConvexApproximation",
    "RicciFlowSharpEstimate.Analysis.L2StrongMultipliers",
    "RicciFlowSharpEstimate.Geometry.AreaRelativeWarpContinuity",
    "RicciFlowSharpEstimate.Geometry.AreaSmoothConvexity",
    "RicciFlowSharpEstimate.Analysis.L2ConvexApproximation",
    "RicciFlowSharpEstimate.Geometry.SmoothAreaRecoveryNormalization",
    "RicciFlowSharpEstimate.Geometry.AreaConvexGraphRecovery",
    "RicciFlowSharpEstimate.Geometry.AreaStrongGraphContinuity",
    "RicciFlowSharpEstimate.Geometry.AreaScalarGraphRecovery",
    "RicciFlowSharpEstimate.Geometry.AreaJointSmoothRecovery",
    "RicciFlowSharpEstimate.Analysis.ParabolicGraphConvergence",
    "RicciFlowSharpEstimate.Geometry.SmoothAreaInfimum",
    "RicciFlowSharpEstimate.Geometry.RecoverableAreaCompetitor",
    "RicciFlowSharpEstimate.Geometry.AreaJointMinimum",
    "RicciFlowSharpEstimate.Geometry.AreaMinimumGeometry",
    "RicciFlowSharpEstimate.Geometry.NormalizedAreaInfimum",
    "RicciFlowSharpEstimate.Analysis.ParabolicWeakDerivativeAlgebra",
    "RicciFlowSharpEstimate.Geometry.RecoverableAreaGeometry",
    "RicciFlowSharpEstimate.Geometry.WeakAreaPolarization",
    "RicciFlowSharpEstimate.Geometry.RecoverableProbeVariation",
    "RicciFlowSharpEstimate.Geometry.RecoverableProbeStationarity",
    "RicciFlowSharpEstimate.Geometry.AreaIntegrableAffine",
    "RicciFlowSharpEstimate.Geometry.SmoothAreaCurvature",
    "RicciFlowSharpEstimate.Geometry.WeakCurvatureSegment",
    "RicciFlowSharpEstimate.Geometry.RecoverableCurvatureSegment",
    "RicciFlowSharpEstimate.Geometry.RecoverableCurvatureOptimality",
    "RicciFlowSharpEstimate.Analysis.UnitIntervalGreen",
    "RicciFlowSharpEstimate.Analysis.WeightedKernelPairing",
    "RicciFlowSharpEstimate.Geometry.WeakCurvatureCoefficients",
    "RicciFlowSharpEstimate.Geometry.AreaGreenPrimitives",
    "RicciFlowSharpEstimate.Geometry.WeakCurvatureAdjoint",
    "RicciFlowSharpEstimate.Analysis.SmoothBoxApproximation",
    "RicciFlowSharpEstimate.Analysis.InteriorMomentBasis",
    "RicciFlowSharpEstimate.Analysis.InteriorMomentRecovery",
    "RicciFlowSharpEstimate.Analysis.BalancedMomentRecovery",
    "RicciFlowSharpEstimate.Geometry.BoundedAreaCurvature",
    "RicciFlowSharpEstimate.Geometry.BoundedCurvatureOptimality",
    "RicciFlowSharpEstimate.Analysis.BoxVariationalInequality",
    "RicciFlowSharpEstimate.Geometry.AreaCurvatureBoxQualification",
    "RicciFlowSharpEstimate.Analysis.BoxMomentMultipliers",
    "RicciFlowSharpEstimate.Geometry.AreaMomentMultipliers",
    "RicciFlowSharpEstimate.Analysis.SecondOrderWeakEuler",
    "RicciFlowSharpEstimate.Geometry.WeakProbeEulerCoefficients",
    "RicciFlowSharpEstimate.Geometry.WeakProbeEulerFlux",
    "RicciFlowSharpEstimate.Analysis.ParabolicGraphMultiplication",
    "RicciFlowSharpEstimate.Geometry.RecoverableProbeMultiplication",
    "RicciFlowSharpEstimate.Geometry.RecoverableMultiplicativeStationarity",
    "RicciFlowSharpEstimate.Geometry.AreaGroundStateComparison",
    "RicciFlowSharpEstimate.Geometry.WeakGroundStateComparison",
    "RicciFlowSharpEstimate.Analysis.WeakDerivativePrimitives",
    "RicciFlowSharpEstimate.Analysis.ParabolicSobolevRegularity",
    "RicciFlowSharpEstimate.Geometry.RecoverableAreaRegularity",
    "RicciFlowSharpEstimate.Geometry.WeakProbeFirstOrderSystem",
    "RicciFlowSharpEstimate.Geometry.AreaProbeMaximumPrinciple",
    "RicciFlowSharpEstimate.Analysis.IntegrableBoundaryTrace",
    "RicciFlowSharpEstimate.Analysis.DivergenceMaximumPrinciple",
    "RicciFlowSharpEstimate.Geometry.WeakProbeDerivativeFlux",
    "RicciFlowSharpEstimate.Geometry.WeakProbeMaximumPrinciple",
    "RicciFlowSharpEstimate.Analysis.DivergenceStrongMaximum",
    "RicciFlowSharpEstimate.Geometry.WeakProbeStrongMaximum",
    "RicciFlowSharpEstimate.Geometry.RecoverableProbeSign",
    "RicciFlowSharpEstimate.Geometry.SmoothAreaSafety",
    "RicciFlowSharpEstimate.Geometry.RecoverableAreaCap",
    "RicciFlowSharpEstimate.Geometry.RotationalEndpointSafety",
    "RicciFlowSharpEstimate.Geometry.AreaThresholdMinimum",
]
OPTIONS = [
    "-DautoImplicit=false", "-Dpp.unicode.fun=true",
    "-DmaxSynthPendingDepth=3", "-Dweak.linter.mathlibStandardSet=true",
    "-Dlinter.style.header.license=No license is granted by this file.",
]
SELECTOR = r"""
  let decls ← liftCoreM <|
    Batteries.Tactic.Lint.getDeclsInPackage `RicciFlowSharpEstimate
  let geo := `RicciFlowSharpEstimate.Geometry
  let analysis := `RicciFlowSharpEstimate.Analysis
  let variational := `RicciFlowSharpEstimate.Variational
  let profile := `RicciFlowSharpEstimate.Geometry.RotationalProfile
  let represented := `RicciFlowSharpEstimate.Geometry.IsRepresentedRotationalMetric
  let area := `RicciFlowSharpEstimate.Geometry.AreaProfile
  let recipArea := `RicciFlowSharpEstimate.Geometry.ReciprocalArea
  let criticalArea := `RicciFlowSharpEstimate.Geometry.CriticalAreaProfile
  let l1Subseq := `RicciFlowSharpEstimate.Analysis.L1Subsequence
  let momentRecovery := `RicciFlowSharpEstimate.Analysis.SymmetricMomentRecovery
  let poleData := `RicciFlowSharpEstimate.Geometry.RotationalProfile.PoleData
  for required in #[`RicciFlowSharpEstimate.Variational.existsUnique_capParameter,
      `RicciFlowSharpEstimate.Variational.capParameter_spec,
      `RicciFlowSharpEstimate.Variational.pairFunctional_sub_eq_integral_marginal,
      `RicciFlowSharpEstimate.Variational.pairFunctional_congr,
      `RicciFlowSharpEstimate.Variational.strictMonoOn_capParameter,
      `RicciFlowSharpEstimate.Variational.contact_bounds,
      `RicciFlowSharpEstimate.Variational.one_sub_upperContact_sq,
      `RicciFlowSharpEstimate.Variational.integral_freeExponential,
      `RicciFlowSharpEstimate.Variational.integral_two_mul_div_freeExponential,
      `RicciFlowSharpEstimate.Variational.obstacleLogProfile_admissible,
      `RicciFlowSharpEstimate.Variational.contact_separation_iff,
      `RicciFlowSharpEstimate.Analysis.exp_tangent_quadratic_lower,
      `RicciFlowSharpEstimate.Variational.obstacleTail_eq_free,
      `RicciFlowSharpEstimate.Variational.obstaclePrefix_eq_high,
      `RicciFlowSharpEstimate.Variational.pairFunctional_eq_intervalIntegral,
      `RicciFlowSharpEstimate.Variational.pairMarginal_obstacleLogProfile_low,
      `RicciFlowSharpEstimate.Variational.pairMarginal_obstacleLogProfile_free,
      `RicciFlowSharpEstimate.Variational.pairMarginal_obstacleLogProfile_high,
      `RicciFlowSharpEstimate.Variational.pairFunctional_obstacleLogProfile_le,
      `RicciFlowSharpEstimate.Variational.pairFunctional_obstacleLogProfile_eq,
      `RicciFlowSharpEstimate.Variational.pairFunctional_obstacleLogProfile_one,
      `RicciFlowSharpEstimate.Variational.pairRemainder_eq_zero_iff,
      `RicciFlowSharpEstimate.Variational.not_differentiableAt_obstacleLogProfile_lowerContact,
      `RicciFlowSharpEstimate.Variational.not_differentiableAt_obstacleLogProfile_upperContact,
      `RicciFlowSharpEstimate.Variational.pairFunctional_eq_obstacleLogProfile_iff,
      `RicciFlowSharpEstimate.Variational.pairFunctional_ge_closedForm,
      `RicciFlowSharpEstimate.Variational.pairFunctional_eq_closedForm_iff,
      `RicciFlowSharpEstimate.Variational.pairFunctional_obstacleLogProfile_lt_of_differentiableOn,
      `RicciFlowSharpEstimate.Variational.integral_lowerObstacleWeight,
      `RicciFlowSharpEstimate.Variational.integral_lowerObstacleWeight_sq,
      `RicciFlowSharpEstimate.Variational.pairFirstVariation_eq_intervalIntegral_marginal,
      `RicciFlowSharpEstimate.Variational.pairFirstVariation_obstacleLogProfile_nonneg,
      `RicciFlowSharpEstimate.Variational.integral_lowerObstacleWeight_error_sq_le,
      `RicciFlowSharpEstimate.Variational.pairRemainder_ge_quadratic_integral,
      `RicciFlowSharpEstimate.Variational.pairQuadratic_eq_centered_integrals,
      `RicciFlowSharpEstimate.Variational.integral_unitCentered_sq_le_pairQuadratic,
      `RicciFlowSharpEstimate.Analysis.integral_sq_le_of_variance_anchor,
      `RicciFlowSharpEstimate.Analysis.integral_evenExtension_error_sq_eq,
      `RicciFlowSharpEstimate.Analysis.integral_reflection_error_sq_le,
      `RicciFlowSharpEstimate.Analysis.integral_symmetrization_error_sq_eq,
      `RicciFlowSharpEstimate.Variational.stabilityConstant_pos,
      `RicciFlowSharpEstimate.Variational.pairFunctional_deficit_controls_L2,
      `RicciFlowSharpEstimate.Variational.hemisphereDeficit_controls_evenExtension,
      `RicciFlowSharpEstimate.Variational.hemisphereDeficit_controls_reflection,
      `RicciFlowSharpEstimate.Variational.hemisphereDeficit_controls_symmetrization,
      `RicciFlowSharpEstimate.Analysis.exists_contDiff_one_sub_sq_factor_of_roots,
      `RicciFlowSharpEstimate.Geometry.RotationalProfile.warp_pos_of_balance,
      `RicciFlowSharpEstimate.Geometry.RotationalProfile.momentCoordinate_strictMonoOn,
      `RicciFlowSharpEstimate.Geometry.RotationalProfile.warp_contDiff,
      `RicciFlowSharpEstimate.Geometry.RotationalProfile.warp_const,
      `RicciFlowSharpEstimate.Geometry.RotationalProfile.exists_smooth_positive_warp_factor,
      `RicciFlowSharpEstimate.Geometry.RotationalProfile.exists_poleData,
      `RicciFlowSharpEstimate.Geometry.RotationalProfile.PoleData.constant,
      `RicciFlowSharpEstimate.Geometry.sphereHeight_contMDiff,
      `RicciFlowSharpEstimate.Geometry.heightOneForm_apply,
      `RicciFlowSharpEstimate.Geometry.HeightMetricCoefficients.heightOneForm_sq_le,
      `RicciFlowSharpEstimate.Geometry.HeightMetricCoefficients.metric_inner_apply,
      `RicciFlowSharpEstimate.Geometry.RotationalProfile.PoleData.metric_inner,
      `RicciFlowSharpEstimate.Geometry.RotationalProfile.PoleData.constant_metric_inner,
      `RicciFlowSharpEstimate.Geometry.exists_metric_of_smooth_positive_balanced_profile,
      `LinearMap.det_smul_add_rankOne_gram_fin_two,
      `RicciFlowSharpEstimate.Geometry.round_grad_sphereHeight_inner_self,
      `RicciFlowSharpEstimate.Geometry.RotationalProfile.PoleData.det_chartGramMatrix_metric,
      `RicciFlowSharpEstimate.Geometry.RotationalProfile.PoleData.chartDensity_metric,
      `RicciFlowSharpEstimate.Geometry.RotationalProfile.PoleData.volume_metric_eq_withDensity,
      `RicciFlowSharpEstimate.Geometry.RotationalProfile.PoleData.integral_volume_metric,
      `RicciFlowSharpEstimate.Geometry.integral_round_height,
      `RicciFlowSharpEstimate.Geometry.RotationalProfile.PoleData.integral_height_metric,
      `RicciFlowSharpEstimate.Geometry.metricScalarAt_eq_radialDiagonalJet,
      `RicciFlowSharpEstimate.Geometry.RotationalProfile.PoleData.radial_curvature_identity,
      `RicciFlowSharpEstimate.Geometry.cylinderMap_contMDiff,
      `RicciFlowSharpEstimate.Geometry.sphereHeight_cylinderMap,
      `RicciFlowSharpEstimate.Geometry.cylinderMap_dIncl_mfderiv,
      `RicciFlowSharpEstimate.Geometry.cylinderMap_mfderiv_injective,
      `RicciFlowSharpEstimate.Geometry.RotationalProfile.PoleData.cylinderMap_metric_inner,
      `RicciFlowSharpEstimate.Geometry.range_cylinderMap,
      `RicciFlowSharpEstimate.Geometry.denseRange_cylinderMap,
      `RicciFlowSharpEstimate.Geometry.RotationalProfile.PoleData.metricScalarAt_cylinderMap,
      `RicciFlowSharpEstimate.Geometry.RotationalProfile.PoleData.metricScalarAt_metric,
      `RicciFlowSharpEstimate.Geometry.RotationalProfile.PoleData.sectionalCurvature_metric,
      `DifferentialGeometry.Tensor0SBundle.TotalNabla0SRealizes.unique,
      `DifferentialGeometry.Tensor0SBundle.CanonicalSpatialDerivs0S.unique,
      `RicciFlowSharpEstimate.Geometry.canonicalDerivatives,
      `RicciFlowSharpEstimate.Geometry.canonicalDerivatives_first,
      `RicciFlowSharpEstimate.Geometry.canonicalDerivatives_second,
      `RicciFlowSharpEstimate.Geometry.canonicalDerivatives_unique,
      `RicciFlowSharpEstimate.Geometry.canonicalDerivatives_nabla2OneFormRealizesAt,
      `RicciFlowSharpEstimate.Geometry.ahlforsPart_apply,
      `RicciFlowSharpEstimate.Geometry.ahlforsPart_symmetric,
      `RicciFlowSharpEstimate.Geometry.ahlforsPart_trace_eq_zero,
      `RicciFlowSharpEstimate.Geometry.sphereAzimuthalOneForm_apply,
      `RicciFlowSharpEstimate.Geometry.RotationalProfile.PoleData.meridionalOneForm_apply,
      `RicciFlowSharpEstimate.Geometry.RotationalProfile.PoleData.azimuthalOneForm_apply,
      poleData ++ `meridionalOneForm_cylinderMap_mfderiv,
      poleData ++ `azimuthalOneForm_cylinderMap_mfderiv,
      `RicciFlowSharpEstimate.Geometry.RotationalProfile.PoleData.meridionalOneForm_one_ne_zero,
      `RicciFlowSharpEstimate.Geometry.RotationalProfile.PoleData.azimuthalOneForm_one_ne_zero,
      `RicciFlowSharpEstimate.Geometry.oneFormDissipationDensity_smooth,
      `RicciFlowSharpEstimate.Geometry.oneFormDissipationDensity_integrable,
      `RicciFlowSharpEstimate.Geometry.oneFormDissipationPairingDensity_integrable,
      `RicciFlowSharpEstimate.Geometry.oneFormDissipation,
      `RicciFlowSharpEstimate.Geometry.oneFormDissipationPairing_add_left,
      `RicciFlowSharpEstimate.Geometry.oneFormDissipation_smul,
      `RicciFlowSharpEstimate.Geometry.oneFormDissipation_parallelogram,
      `RicciFlowSharpEstimate.Geometry.RotationalProfile.PoleData.oneFormDissipationDensity_metric,
      poleData ++ `oneFormDissipation_eq_weightedRoundIntegral,
      poleData ++ `weighted_dissipationDensity_integrable,
      geo ++ `roughLap0SField_duSec_apply,
      geo ++ `roughLap0SField_duSec_of_finrank_eq_two,
      geo ++ `metricTracePair0SAt_product_one,
      geo ++ `inner0S_product_one,
      geo ++ `normSq0S_of_apply_eq_rankOne_add_metric,
      geo ++ `normSq0S_ahlforsPart_of_apply_eq_rankOne_add_metric,
      poleData ++ `inverseMetricSharpFib_heightOneForm,
      poleData ++ `heightOneForm_normSq,
      poleData ++ `meridionalOneForm_normSq,
      poleData ++ `meridionalWeight_hasDerivAt,
      poleData ++ `meridionalDensity_intervalIntegrable,
      poleData ++ `meridionalAction_constant_one,
      poleData ++ `duSec_meridionalPotential,
      poleData ++ `metricNabla0S_meridionalOneForm,
      poleData ++ `meridionalOneForm_nabla_trace,
      poleData ++ `meridionalOneForm_nabla_normSq,
      poleData ++ `meridionalOneForm_ahlfors_normSq,
      poleData ++ `laplacian_meridionalPotential,
      poleData ++ `roughLap0SField_meridionalOneForm,
      poleData ++ `oneFormDissipationDensity_meridional,
      poleData ++ `oneFormDissipation_meridional,
      poleData ++ `oneFormDissipation_constant_meridional_one,
      geo ++ `diffeomorphTensorPullback,
      geo ++ `diffeomorphTensorPullback_apply,
      geo ++ `diffeomorphTensorPullback_refl,
      geo ++ `diffeomorphTensorPullback_trans,
      geo ++ `diffeomorphTensorPullback_symm_apply,
      geo ++ `diffeomorphTensorPullback_apply_symm,
      geo ++ `metricNabla0S_diffeomorphTensorPullback,
      geo ++ `metricNabla0S_twice_diffeomorphTensorPullback,
      geo ++ `roughLap0SField_diffeomorphTensorPullback,
      geo ++ `ahlforsPart_diffeomorphTensorPullback,
      geo ++ `oneFormDissipation_diffeomorphTensorPullback,
      geo ++ `oneFormDissipationPairing_diffeomorphTensorPullback_of_isometry,
      geo ++ `meridianReflectionSphereDiffeo_coe,
      geo ++ `meridianReflectionSphereDiffeo_dIncl_mfderiv,
      geo ++ `metricNabla0S_eq_zero_of_alternating_const_normSq,
      geo ++ `normSq0S_eq_two_of_unit_alternating,
      geo ++ `roundSphereAreaForm_apply,
      poleData ++ `pullbackMetric_meridianReflectionSphereDiffeo,
      poleData ++ `oneFormDissipationPairing_meridional_azimuthal,
      poleData ++ `oneFormDissipation_meridional_add_azimuthal,
      poleData ++ `areaForm_apply,
      poleData ++ `areaForm_normSq,
      poleData ++ `metricNabla0S_areaForm,
      geo ++ `dIncl_round_grad_sphereHeight,
      geo ++ `roundSphereAreaForm_round_grad_sphereHeight,
      geo ++ `normSq0S_one_eq_of_rotation,
      geo ++ `normSq0S_two_eq_of_rotation,
      geo ++ `normSq0S_ahlforsPart_eq_of_rotation,
      geo ++ `oneFormAreaContraction,
      geo ++ `oneFormAreaContraction_apply,
      geo ++ `oneFormAreaContraction_add,
      geo ++ `oneFormAreaContraction_smul,
      geo ++ `metricNabla0S_oneFormAreaContraction,
      geo ++ `metricNabla0S_twice_oneFormAreaContraction,
      geo ++ `roughLap0SField_oneFormAreaContraction,
      geo ++ `oneFormDissipationDensity_oneFormAreaContraction,
      geo ++ `oneFormDissipation_oneFormAreaContraction,
      poleData ++ `inverseMetricSharpFib_meridionalOneForm,
      poleData ++ `areaForm_inverseMetricSharpFib_meridionalOneForm,
      poleData ++ `hodgeRotation,
      poleData ++ `hodgeRotation_apply,
      poleData ++ `hodgeRotation_meridionalOneForm,
      poleData ++ `oneFormDissipation_hodgeRotation,
      poleData ++ `oneFormDissipation_azimuthal_eq_meridional,
      poleData ++ `oneFormDissipation_azimuthal,
      poleData ++ `oneFormDissipation_zonal,
      analysis ++ `contMDiffOn_intervalIntegral,
      analysis ++ `contMDiff_intervalIntegral,
      analysis ++ `mvfderiv_intervalIntegral_apply_of_contMDiffOn,
      analysis ++ `mvfderiv_intervalIntegral_apply,
      analysis ++ `continuousOn_mvfderiv_apply_of_contMDiffOn,
      analysis ++ `continuous_mvfderiv_apply,
      analysis ++ `intervalIntegrable_mvfderiv_apply_of_contMDiffOn,
      analysis ++ `intervalIntegrable_mvfderiv_apply,
      geo ++ `axisRotation_apply,
      geo ++ `axisRotationRepresentation,
      geo ++ `circleSphereDiffeo_coe,
      geo ++ `circleSphereDiffeo_mul,
      geo ++ `circleSphereDiffeo_inv,
      geo ++ `circleSphereDiffeo_dIncl_mfderiv,
      geo ++ `angleRotation_add,
      geo ++ `angleRotation_periodic,
      geo ++ `angleRotation_contMDiff,
      geo ++ `mfderiv_family_zero_parameter,
      geo ++ `contMDiff_diffeomorphTensorPullback_family,
      geo ++ `contMDiff_diffeomorphTensorPullback_family_apply_sections,
      geo ++ `continuous_diffeomorphTensorPullback_family_at,
      geo ++ `diffeomorphTensorPullback_angleRotation_add,
      geo ++ `contMDiff_diffeomorphTensorPullback_angleRotation,
      geo ++ `tensorIntervalIntegral_apply,
      geo ++ `tensorIntervalIntegral_eval,
      geo ++ `intervalIntegrable_tensorFamily_at,
      geo ++ `metricNabla0S_tensorIntervalIntegral,
      geo ++ `inner0S_tensorIntervalIntegral_left,
      geo ++ `intervalIntegrable_inner0S_tensorFamily_left,
      geo ++ `metricTracePair0SAt_tensorIntervalIntegral,
      geo ++ `roughLap0STensor_tensorIntervalIntegral_apply,
      geo ++ `ahlforsPart_tensorIntervalIntegral_apply,
      geo ++ `rotationalAverage_apply,
      geo ++ `rotationalAverage_add,
      geo ++ `rotationalAverage_smul,
      geo ++ `diffeomorphTensorPullback_circle_rotationalAverage,
      geo ++ `rotationalAverage_eq_self_iff,
      geo ++ `rotationalAverage_idempotent,
      geo ++ `rotationalAverage_sub_average,
      poleData ++ `pullbackMetric_angleRotation,
      poleData ++ `metricNabla0S_angleRotation,
      poleData ++ `continuous_oneFormDissipationPairingDensity_angleRotation,
      poleData ++ `integrable_oneFormDissipationPairingDensity_angleRotation,
      poleData ++ `intervalIntegrable_oneFormDissipationPairing_angleRotation,
      poleData ++ `integral_intervalIntegral_oneFormDissipationPairingDensity_angleRotation,
      poleData ++ `rotationalAverage_meridionalOneForm,
      poleData ++ `rotationalAverage_meridional_one_ne_zero,
      poleData ++ `metricNabla0S_rotationalAverage,
      poleData ++ `metricNabla0S_twice_rotationalAverage,
      poleData ++ `roughLap0SField_rotationalAverage,
      poleData ++ `ahlforsPart_rotationalAverage,
      poleData ++ `ahlforsPart_metricNabla0S_rotationalAverage,
      poleData ++ `oneFormDissipationPairingDensity_rotationalAverage,
      poleData ++ `oneFormDissipationPairing_rotationalAverage,
      poleData ++ `oneFormDissipationPairing_rotationalAverage_selfAdjoint,
      poleData ++ `oneFormDissipationPairing_average_sub_average,
      poleData ++ `oneFormDissipation_haar_split,
      analysis ++ `exists_contDiff_mul_eq_on_Icc,
      analysis ++ `exists_contDiff_comp_sq_of_even,
      analysis ++ `exists_contDiff_mul_comp_sq_of_odd,
      analysis ++ `planeRotate,
      analysis ++ `IsRotationCovectorPair,
      analysis ++ `exists_smooth_radial_tangential_coefficients,
      geo ++ `stereoDenominator,
      geo ++ `stereoDenominator_pos,
      geo ++ `stereoAmbient,
      geo ++ `stereoPoint,
      geo ++ `stereoPoint_contMDiff,
      geo ++ `stereoPoint_coe,
      geo ++ `sphereHeight_stereoPoint,
      geo ++ `stereoPoint_height_denominator,
      geo ++ `stereoPoint_planeRotate,
      geo ++ `stereoInversePoint,
      geo ++ `stereoInversePoint_stereoPoint,
      geo ++ `stereoPoint_inverse,
      geo ++ `stereoPoint_dIncl_mfderiv,
      geo ++ `stereoPoint_mfderiv_injective,
      geo ++ `stereoPoint_mfderiv_surjective,
      geo ++ `heightOneForm_stereoPoint_mfderiv,
      geo ++ `sphereAzimuthalOneForm_stereoPoint_mfderiv,
      geo ++ `exists_smooth_stereographic_coefficients,
      geo ++ `exists_smooth_height_azimuthal_profiles,
      poleData ++ `exists_smooth_zonal_decomposition_of_rotationInvariant,
      poleData ++ `exists_smooth_zonal_decomposition_rotationalAverage,
      poleData ++ `exists_haar_zonal_dissipation,
      geo ++ `oneFormTrace,
      geo ++ `oneFormCurl,
      geo ++ `oneFormTrace_contMDiff,
      geo ++ `oneFormCurl_contMDiff,
      geo ++ `inner0S_eq_sum_orthonormal,
      geo ++ `normSq0S_eq_sum_sq_orthonormal,
      geo ++ `twoTensor_eq_ahlforsPart_add_trace_add_curl,
      geo ++ `normSq0S_twoTensor_eq_ahlforsPart_trace_curl,
      geo ++ `inner0S_ahlforsPart_self,
      geo ++ `compactTensor0S,
      geo ++ `compactTensor0S_toSection,
      geo ++ `compactTensor0S_toFun,
      geo ++ `metricNabla0S_apply_section,
      geo ++ `metricNabla0S_apply_cons,
      geo ++ `covariantDerivative_compactTensor0S,
      geo ++ `covGrad_compactTensor0S_toSection,
      geo ++ `covDivergence_compactTensor0S_toSection,
      geo ++ `tensorInnerPointwise_toRS0_eq_inner0S,
      geo ++ `integral_inner0S_metricNabla0S_eq_neg_covDiv0SField,
      geo ++ `integral_inner0S_metricNabla0S_eq_neg_roughLap0SField,
      geo ++ `integral_inner0S_roughLap0SField_left_eq_right,
      geo ++ `metricNabla0S_commutator,
      geo ++ `covDiv0SField_gradSlotSwap_commutator_of_finrank_eq_two,
      geo ++ `oneForm_secondDerivative_skew_pairing,
      geo ++ `differential1FormFun_metricTrace_apply,
      geo ++ `differential1FormFun_inner0S_two_apply,
      geo ++ `metricNabla0S_ahlforsPart_apply,
      geo ++ `normSq0S_metricNabla0S_twoTensor_split,
      geo ++ `integral_inner0S_gradSlotSwap,
      geo ++ `oneFormDissipation_scalarization,
      poleData ++ `oneFormDissipation_scalarization,
      geo ++ `inner0S_diffeomorphTensorPullback,
      geo ++ `metricTracePair0SAt_diffeomorphTensorPullback,
      geo ++ `oneFormTrace_diffeomorphTensorPullback,
      geo ++ `oneFormCurl_diffeomorphTensorPullback,
      geo ++ `diffeomorphTensorPullback_roundSphereAreaForm_circleSphereDiffeo,
      geo ++ `diffeomorphTensorPullback_roundSphereAreaForm_angleRotation,
      geo ++ `rotationalScalarAverage,
      geo ++ `rotationalScalarAverage_contMDiff,
      geo ++ `rotationalScalarAverage_add,
      geo ++ `rotationalScalarAverage_sub,
      geo ++ `rotationalScalarAverage_smul,
      geo ++ `rotationalScalarAverage_const,
      geo ++ `rotationalScalarAverage_zero,
      geo ++ `rotationalScalarAverage_one,
      geo ++ `rotationalScalarAverage_angleRotation,
      geo ++ `rotationalScalarAverage_comp_angleRotation,
      geo ++ `rotationalScalarAverage_eq_self_of_invariant,
      geo ++ `rotationalScalarAverage_idempotent,
      geo ++ `rotationalScalarAverage_eq_at_pole,
      geo ++ `rotationalScalarAverage_eq_zero_at_pole,
      poleData ++ `diffeomorphTensorPullback_areaForm_circleSphereDiffeo,
      poleData ++ `diffeomorphTensorPullback_areaForm_angleRotation,
      poleData ++ `metricTracePair0SAt_rotationalAverage,
      poleData ++ `inner0S_areaForm_rotationalAverage,
      poleData ++ `oneFormTrace_angleRotation,
      poleData ++ `oneFormCurl_angleRotation,
      poleData ++ `oneFormTrace_rotationalAverage,
      poleData ++ `oneFormCurl_rotationalAverage,
      poleData ++ `rotationalScalarAverage_oneFormTrace_remainder,
      poleData ++ `rotationalScalarAverage_oneFormCurl_remainder,
      poleData ++ `oneFormTrace_remainder_eq_zero_at_pole,
      poleData ++ `oneFormCurl_remainder_eq_zero_at_pole,
      analysis ++ `integral_sq_le_deriv_sq_of_periodic_mean_zero,
      analysis ++ `contDiff_deriv_fst,
      analysis ++ `contDiff_deriv_snd,
      analysis ++ `exists_pos_polar_endpoint_bounds,
      analysis ++ `intervalIntegrable_polar_square,
      analysis ++ `integral_polar_square_completion,
      analysis ++ `integral_weighted_sin_sq_le_polar_energy,
      analysis ++ `integrable_polar_energy_terms,
      analysis ++ `integral_polar_energy_ge_of_angular_mean_zero,
      analysis ++ `tendsto_polar_boundary_at_endpoints,
      geo ++ `polarSpherePoint,
      geo ++ `polarSpherePoint_coe,
      geo ++ `sphereHeight_polarSpherePoint,
      geo ++ `polarSpherePoint_contMDiff,
      geo ++ `polarSpherePoint_periodic,
      geo ++ `angleRotation_polarSpherePoint,
      geo ++ `polarSpherePoint_zero,
      geo ++ `polarSpherePoint_pi,
      geo ++ `polarRadialVelocity,
      geo ++ `polarAngularVelocity,
      geo ++ `polarRadialVelocity_dIncl,
      geo ++ `polarAngularVelocity_dIncl,
      geo ++ `polarVelocities_linearIndependent,
      geo ++ `polarVelocities_span,
      geo ++ `polarTangentBasis,
      geo ++ `polarTangentBasis_zero,
      geo ++ `polarTangentBasis_one,
      geo ++ `exists_polarSpherePoint_arccos,
      geo ++ `contDiff_scalar_polar,
      geo ++ `differential1FormFun_polarRadialVelocity,
      geo ++ `differential1FormFun_polarAngularVelocity,
      geo ++ `scalar_polar_endpoint_bounds,
      geo ++ `scalar_polar_boundary_limits,
      poleData ++ `metric_inner_polarRadialVelocity,
      poleData ++ `metric_inner_polarAngularVelocity,
      poleData ++ `metric_inner_polarRadialAngular,
      poleData ++ `normSq0S_polar_covector,
      poleData ++ `normSq0S_differential1FormFun_polar,
      poleData ++ `integral_polar_metric,
      poleData ++ `integral_scalar_energy_ge_of_rotationalScalarAverage_eq_zero,
      geo ++ `integral_weight_mul_normSq_eq_zero_iff,
      geo ++ `integral_weight_mul_sq_eq_zero_iff,
      geo ++ `metricNabla0S_zero,
      geo ++ `metricNabla0S_second_eq_zero_of_first_eq_zero,
      geo ++ `roughLap0SField_eq_zero_of_metricNabla0S_eq_zero,
      geo ++ `metricNabla0S_eq_zero_of_ahlfors_trace_curl_eq_zero,
      geo ++ `oneFormDissipation_eq_curvature_energy_of_metricNabla0S_eq_zero,
      poleData ++ `oneFormDissipation_remainder_lower_bound,
      poleData ++ `oneFormDissipation_remainder_nonneg,
      poleData ++ `oneFormDissipation_remainder_eq_zero_iff,
      poleData ++ `oneFormDissipation_remainder_pos_iff,
      poleData ++ `oneFormDissipation_rotationalAverage_le,
      poleData ++ `oneFormDissipation_eq_rotationalAverage_iff,
      poleData ++ `oneFormDissipation_eq_rotationalAverage_iff_invariant,
      poleData ++ `exists_haar_zonal_lower_bound,
      analysis ++ `continuousOn_log_reciprocal,
      analysis ++ `hasDerivAt_log_reciprocal,
      analysis ++ `log_reciprocal_bounds,
      `RicciFlowSharpEstimate.Variational.pairFunctional_eq_forward_intervalIntegral,
      `RicciFlowSharpEstimate.Variational.pairFunctional_log_reciprocal,
      `RicciFlowSharpEstimate.Variational.criticalCap,
      `RicciFlowSharpEstimate.Variational.one_lt_criticalCap,
      `RicciFlowSharpEstimate.Variational.capParameter_criticalCap,
      `RicciFlowSharpEstimate.Variational.capParameter_criticalCap_cube,
      `RicciFlowSharpEstimate.Variational.upperContact_capParameter_criticalCap,
      `RicciFlowSharpEstimate.Variational.pairFunctional_obstacleLogProfile_criticalCap,
      `RicciFlowSharpEstimate.Variational.pairFunctional_obstacleLogProfile_ge_one_third_iff,
      `RicciFlowSharpEstimate.Variational.pairFunctional_gt_one_third_of_differentiableOn,
      geo ++ `IsConformalKillingOneForm,
      geo ++ `isConformalKillingOneForm_iff,
      geo ++ `isConformalKillingOneForm_iff_normSq_eq_zero,
      geo ++ `IsConformalKillingOneForm.add,
      geo ++ `IsConformalKillingOneForm.smul,
      geo ++ `IsConformalKillingOneForm.neg,
      geo ++ `IsConformalKillingOneForm.sub,
      geo ++ `IsConformalKillingOneForm.diffeomorphTensorPullback,
      geo ++ `IsConformalKillingOneForm.diffeomorphTensorPullback_of_isometry,
      poleData ++ `northLogProfile_continuousOn,
      poleData ++ `southLogProfile_continuousOn,
      poleData ++ `northLogProfile_hasDerivAt,
      poleData ++ `southLogProfile_hasDerivAt,
      poleData ++ `northLogProfile_differentiableOn,
      poleData ++ `southLogProfile_differentiableOn,
      poleData ++ `reciprocalCap_parameters,
      poleData ++ `northLogProfile_admissible,
      poleData ++ `southLogProfile_admissible,
      poleData ++ `warp_reflected,
      poleData ++ `pairFunctional_northLogProfile,
      poleData ++ `pairFunctional_southLogProfile,
      poleData ++ `integral_meridionalWeight_eq_pairFunctional_sum,
      poleData ++ `meridionalDensity_const,
      poleData ++ `meridionalAction_const,
      poleData ++ `oneFormDissipation_constant_zonal,
      poleData ++ `oneFormDissipation_constant_zonal_eq_pair_sum,
      poleData ++ `isConformalKillingOneForm_meridional_const,
      poleData ++ `azimuthalOneForm_ahlfors_normSq,
      poleData ++ `isConformalKillingOneForm_azimuthal_const,
      poleData ++ `isConformalKillingOneForm_constant_zonal_sum,
      poleData ++ `meridional_probe_eq_const_of_isConformalKillingOneForm,
      poleData ++ `azimuthal_probe_eq_const_of_isConformalKillingOneForm,
      poleData ++
        `exists_constant_zonal_decomposition_of_rotationInvariant_of_isConformalKillingOneForm,
      poleData ++
        `rotationInvariant_isConformalKillingOneForm_iff_exists_constant_zonal_decomposition,
      poleData ++ `isConformalKillingOneForm_rotationalAverage,
      poleData ++
        `exists_constant_zonal_decomposition_rotationalAverage_of_isConformalKillingOneForm,
      poleData ++ `meridional_one_nonzero_conformalKilling,
      poleData ++ `curvature_bounds_iff_profile_bounds,
      poleData ++ `constant_zonal_coefficient_pos,
      poleData ++ `oneFormDissipation_nonneg_of_conformalKilling_profile_bounds,
      poleData ++ `oneFormDissipation_eq_zero_iff_of_conformalKilling_profile_bounds,
      poleData ++ `oneFormDissipation_meridional_one_pos_of_profile_bounds,
      poleData ++ `oneFormDissipation_nonneg_of_conformalKilling_curvature_bounds,
      poleData ++ `oneFormDissipation_eq_zero_iff_of_conformalKilling_curvature_bounds,
      analysis ++ `exists_contDiff_even_sequence_Icc,
      variational ++ `evenReciprocalProfile,
      variational ++ `evenReciprocalProfile_eq,
      variational ++ `even_evenReciprocalProfile,
      variational ++ `uniformContinuous_evenReciprocalProfile,
      variational ++ `evenReciprocalProfile_bounds,
      profile ++ `balance_eq_zero_of_even,
      profile ++ `warp_reflected_of_balance,
      profile ++ `integral_warp_div_eq_pairFunctional_sum,
      profile ++ `integral_warp_div_evenReciprocalProfile,
      profile ++ `constantProbeIntegral_evenReciprocalProfile,
      profile ++ `continuousOn_warp,
      profile ++ `intervalIntegrable_warp_div,
      profile ++ `tendsto_integral_warp_div_of_tendstoUniformlyOn,
      profile ++ `abs_integral_warp_div_sub_le,
      poleData ++ `hemisphereDeficit_logProfile_eq_normalized_constant_zonal,
      poleData ++ `oneFormDissipation_constant_zonal_controls_evenExtension,
      poleData ++ `oneFormDissipation_constant_zonal_controls_reflection,
      poleData ++ `oneFormDissipation_constant_zonal_controls_symmetrization,
      poleData ++ `constant_zonal_zero_of_sq_sum_eq_zero,
      profile ++ `exists_smooth_even_reciprocal_profiles,
      poleData ++ `oneFormDissipation_meridional_one_eq_integral,
      profile ++ `exists_poleData_unit_probe_recovery,
      profile ++ `exists_negative_unit_meridional_of_criticalCap_lt,
      profile ++ `exists_critical_unit_probe_recovery,
      geo ++ `diffeomorphTensorPullback_zero,
      geo ++ `diffeomorphTensorPullback_neg,
      geo ++ `diffeomorphTensorPullback_sub,
      geo ++ `diffeomorphTensorPullback_injective,
      geo ++ `diffeomorphTensorPullback_eq_zero_iff,
      geo ++ `pullbackMetric_symm_apply,
      geo ++ `pullbackMetric_apply_symm,
      geo ++ `conjugatedRotationalAverage,
      geo ++ `conjugatedRotationalAverage_refl,
      geo ++ `conjugatedRotationalAverage_diffeomorphTensorPullback,
      geo ++ `diffeomorphTensorPullback_symm_conjugatedRotationalAverage,
      geo ++ `conjugatedRotationalAverage_zero,
      geo ++ `conjugatedRotationalAverage_add,
      geo ++ `conjugatedRotationalAverage_smul,
      geo ++ `conjugatedRotationalAverage_sub,
      geo ++ `conjugatedRotationalAverage_idempotent,
      geo ++ `conjugatedRotationalAverage_sub_average,
      geo ++ `conjugatedRotationalAverage_eq_self_iff_pullback,
      geo ++ `conjugatedCircleSphereDiffeo,
      geo ++ `conjugatedCircleSphereDiffeo_apply,
      geo ++ `conjugatedCircleSphereDiffeo_one,
      geo ++ `conjugatedCircleSphereDiffeo_mul,
      geo ++ `conjugatedCircleSphereAction,
      geo ++ `conjugatedCircleSphereDiffeo_inv,
      geo ++ `conjugatedAngleRotation,
      geo ++ `conjugatedAngleRotation_apply,
      geo ++ `conjugatedAngleRotation_zero,
      geo ++ `conjugatedAngleRotation_add,
      geo ++ `conjugatedAngleRotation_neg,
      geo ++ `conjugatedAngleRotation_periodic,
      geo ++ `conjugatedAngleRotation_contMDiff,
      poleData ++ `pullbackMetric_conjugatedCircleSphereDiffeo,
      poleData ++ `metric_inner_conjugatedCircleSphereDiffeo,
      poleData ++ `pullbackMetric_conjugatedAngleRotation,
      geo ++ `diffeomorphTensorPullback_conjugatedCircleSphereDiffeo,
      geo ++ `contMDiff_diffeomorphTensorPullback_conjugatedAngleRotation,
      geo ++ `intervalIntegrable_conjugatedAngleRotation_apply,
      geo ++ `conjugatedRotationalAverage_eval,
      geo ++ `conjugatedRotationalAverage_apply,
      geo ++ `diffeomorphTensorPullback_conjugatedCircle_conjugatedRotationalAverage,
      geo ++ `conjugatedRotationalAverage_eq_self_iff,
      poleData ++ `metricNabla0S_conjugatedRotationalAverage,
      poleData ++ `metricNabla0S_twice_conjugatedRotationalAverage,
      poleData ++ `roughLap0SField_conjugatedRotationalAverage,
      poleData ++ `ahlforsPart_conjugatedRotationalAverage,
      poleData ++ `ahlforsPart_metricNabla0S_conjugatedRotationalAverage,
      poleData ++ `oneFormDissipationPairing_conjugatedRotationalAverage_selfAdjoint,
      poleData ++ `oneFormDissipationPairing_conjugated_average_sub_average,
      poleData ++ `oneFormDissipation_conjugated_split,
      poleData ++ `oneFormDissipation_conjugated_remainder_nonneg,
      poleData ++ `oneFormDissipation_conjugated_remainder_eq_zero_iff,
      geo ++ `IsRepresentedRotationalMetric,
      poleData ++ `isRepresentedRotationalMetric,
      poleData ++ `isRepresentedRotationalMetric_pullback,
      poleData ++ `metricScalarAt_pullback,
      poleData ++ `curvature_bounds_pullback_iff,
      poleData ++ `riemannianVolume_measurePreserving_pullback,
      poleData ++ `riemannianVolume_map_pullback,
      poleData ++ `areaForm_pullback_apply,
      poleData ++ `areaForm_pullback_normSq,
      poleData ++ `metricNabla0S_areaForm_pullback,
      poleData ++ `oneFormCurl_areaForm_pullback,
      poleData ++ `oneFormDissipation_nonneg_pullback_of_conformalKilling_curvature_bounds,
      poleData ++ `oneFormDissipation_eq_zero_iff_pullback_of_conformalKilling_curvature_bounds,
      represented ++ `pullback,
      represented ++ `oneFormDissipation_nonneg_of_conformalKilling_curvature_bounds,
      represented ++ `oneFormDissipation_eq_zero_iff_of_conformalKilling_curvature_bounds,
      poleData ++ `oneFormDissipation_pullback_zonal,
      poleData ++ `exists_smooth_zonal_decomposition_conjugatedRotationalAverage,
      poleData ++ `exists_conjugated_haar_zonal_dissipation,
      poleData ++ `oneFormDissipation_conjugatedRotationalAverage_le,
      poleData ++ `oneFormDissipation_eq_conjugatedRotationalAverage_iff,
      poleData ++ `oneFormDissipation_eq_conjugatedRotationalAverage_iff_invariant,
      poleData ++ `exists_conjugated_haar_zonal_lower_bound,
      poleData ++ `isConformalKillingOneForm_conjugatedRotationalAverage,
      poleData ++ `exists_conjugated_constant_zonal_of_conformalKilling,
      represented ++ `exists_haar_representation,
      represented ++ `exists_haar_zonal_decomposition,
      poleData ++ `hemisphereDeficit_logProfile_eq_normalized_pullback_constant_zonal,
      poleData ++ `oneFormDissipation_pullback_constant_zonal_controls_evenExtension,
      poleData ++ `oneFormDissipation_pullback_constant_zonal_controls_reflection,
      poleData ++ `oneFormDissipation_pullback_constant_zonal_controls_symmetrization,
      poleData ++ `pullback_constant_zonal_zero_of_sq_sum_eq_zero,
      represented ++ `exists_stability_representation,
      geo ++ `conformalKillingSafeCaps,
      geo ++ `conformalKillingSafeCaps_eq,
      geo ++ `conformalKillingSafeCaps_nonempty,
      geo ++ `conformalKillingSafeCaps_bddAbove,
      geo ++ `conformalKillingThreshold,
      geo ++ `conformalKillingThreshold_eq_criticalCap,
      geo ++ `conformalKillingThreshold_closedForm,
      represented ++ `oneFormDissipation_pos_of_conformalKilling,
      geo ++ `exists_represented_negative_unit_meridional,
      geo ++ `exists_represented_critical_unit_probe_recovery,
      area ++ `heightCoordinate,
      area ++ `warp,
      area ++ `warpSlope,
      area ++ `meridionalActionDensity,
      area ++ `meridionalAction,
      area ++ `heightCoordinate_hasDerivAt,
      area ++ `deriv_heightCoordinate,
      area ++ `heightCoordinate_contDiff,
      area ++ `heightCoordinate_zero,
      area ++ `heightCoordinate_one,
      area ++ `warp_zero,
      area ++ `warpSlope_zero,
      area ++ `warpSlope_eq_neg_two_height,
      analysis ++ `SecondPrimitive.integral_kernel_eq,
      analysis ++ `SecondPrimitive.integral_kernel_hasDerivAt,
      analysis ++ `SecondPrimitive.integral_contDiff,
      analysis ++ `SecondPrimitive.integral_kernel_contDiff,
      area ++ `warp_hasDerivAt,
      area ++ `warpSlope_hasDerivAt,
      area ++ `deriv_warp,
      area ++ `deriv_warpSlope,
      area ++ `deriv_deriv_warp,
      area ++ `warp_contDiff,
      area ++ `warpSlope_contDiff,
      area ++ `warp_one,
      area ++ `warpSlope_one,
      area ++ `heightCoordinate_continuous,
      area ++ `warp_continuous,
      area ++ `warpSlope_continuous,
      area ++ `heightCoordinate_strictMonoOn,
      area ++ `heightCoordinate_mapsTo,
      area ++ `heightCoordinate_bijOn,
      area ++ `warp_strictConcaveOn,
      area ++ `warp_pos_of_moments,
      area ++ `integral_heightCoordinate,
      analysis ++ `exists_contDiff_extension_Icc,
      analysis ++ `exists_contDiff_inverse_on_Icc,
      area ++ `meridionalAction_integrand_continuous,
      area ++ `meridionalAction_integrand_intervalIntegrable,
      area ++ `warp_two,
      area ++ `warpSlope_two,
      area ++ `meridionalAction_two_one,
      area ++ `profile_warp_heightCoordinate,
      area ++ `deriv_profile_heightCoordinate,
      area ++ `deriv_probe_heightCoordinate,
      area ++ `deriv_deriv_probe_heightCoordinate,
      area ++ `meridionalWeight_heightCoordinate,
      area ++ `deriv_meridionalWeight_heightCoordinate,
      area ++ `meridionalOperator_heightCoordinate,
      area ++ `meridionalDensity_heightCoordinate_mul_curvature,
      area ++ `oneFormDissipation_eq_areaAction_of_profile_probe,
      area ++ `exists_smooth_geometric_realization,
      area ++ `round_unit_probe_normalization,
      variational ++ `monotone_obstacleExponential,
      variational ++ `monotone_obstacleLogProfile,
      variational ++ `evenReciprocalProfile_eq_low,
      variational ++ `evenReciprocalProfile_eq_high,
      variational ++ `evenReciprocalProfile_at_zero,
      variational ++ `evenReciprocalProfile_at_one,
      variational ++ `evenReciprocalProfile_one,
      variational ++ `antitoneOn_evenReciprocalProfile,
      variational ++ `monotoneOn_evenReciprocalProfile,
      variational ++ `evenReciprocalProfile_central_plateau,
      variational ++ `evenReciprocalProfile_strict_average_bounds,
      analysis ++ `clampedIntervalInverse,
      analysis ++ `clampedIntervalInverse_mem,
      analysis ++ `clampedIntervalInverse_apply,
      analysis ++ `apply_clampedIntervalInverse,
      analysis ++ `clampedIntervalInverse_continuous,
      recipArea ++ `length,
      recipArea ++ `coordinate,
      recipArea ++ `inverse,
      recipArea ++ `curvature,
      recipArea ++ `length_pos,
      recipArea ++ `coordinate_hasDerivAt,
      recipArea ++ `coordinate_continuous,
      recipArea ++ `coordinate_neg_one,
      recipArea ++ `coordinate_one,
      recipArea ++ `coordinate_strictMonoOn,
      recipArea ++ `coordinate_mapsTo,
      recipArea ++ `coordinate_bijOn,
      recipArea ++ `inverse_mem,
      recipArea ++ `inverse_continuous,
      recipArea ++ `inverse_coordinate,
      recipArea ++ `coordinate_inverse,
      recipArea ++ `inverse_zero,
      recipArea ++ `inverse_one,
      recipArea ++ `inverse_strictMonoOn,
      recipArea ++ `curvature_continuous,
      recipArea ++ `curvature_pos,
      recipArea ++ `curvature_coordinate,
      recipArea ++ `integral_comp_coordinate,
      recipArea ++ `warpSlope_coordinate,
      recipArea ++ `heightCoordinate_coordinate,
      recipArea ++ `integral_curvature,
      recipArea ++ `warp_coordinate,
      recipArea ++ `integral_mul_curvature,
      recipArea ++ `curvature_mem_Icc,
      recipArea ++ `meridionalAction_one_eq_integral,
      recipArea ++ `meridionalAction_one,
      recipArea ++ `coordinate_reflection,
      recipArea ++ `coordinate_zero,
      recipArea ++ `inverse_half,
      recipArea ++ `inverse_reflection,
      recipArea ++ `curvature_reflection,
      recipArea ++ `curvature_antitoneOn_left,
      recipArea ++ `curvature_monotoneOn_right,
      analysis ++ `exists_contDiff_nonneg_tsupport_subset_integral_mul_pos,
      area ++ `constantProbeVariationDensity,
      area ++ `meridionalActionDensity_one_sub_mul,
      area ++ `plateauFlux,
      area ++ `plateauFlux_hasDerivAt,
      area ++ `plateauFlux_endpoints,
      area ++ `constantProbeVariation_integral_eq_plateau_pairing,
      area ++ `meridionalAction_one_sub_mul_of_plateau,
      area ++ `exists_smooth_plateau_probe,
      area ++ `exists_smooth_probe_action_neg_of_constant_curvature_plateau,
      criticalArea ++ `reciprocal,
      criticalArea ++ `length,
      criticalArea ++ `coordinate,
      criticalArea ++ `inverse,
      criticalArea ++ `curvature,
      criticalArea ++ `length_pos,
      criticalArea ++ `strict_average_bounds,
      criticalArea ++ `coordinate_hasDerivAt,
      criticalArea ++ `coordinate_neg_one,
      criticalArea ++ `coordinate_one,
      criticalArea ++ `inverse_zero,
      criticalArea ++ `inverse_one,
      criticalArea ++ `coordinate_bijOn,
      criticalArea ++ `inverse_mem,
      criticalArea ++ `inverse_coordinate,
      criticalArea ++ `coordinate_inverse,
      criticalArea ++ `inverse_continuous,
      criticalArea ++ `curvature_continuous,
      criticalArea ++ `curvature_pos,
      criticalArea ++ `curvature_coordinate,
      criticalArea ++ `curvature_bounds,
      criticalArea ++ `curvature_moments,
      criticalArea ++ `warp_coordinate,
      criticalArea ++ `warpSlope_coordinate,
      criticalArea ++ `heightCoordinate_eq_inverse,
      criticalArea ++ `coordinate_reflection,
      criticalArea ++ `coordinate_zero,
      criticalArea ++ `inverse_half,
      criticalArea ++ `curvature_reflection,
      criticalArea ++ `curvature_antitoneOn_left,
      criticalArea ++ `curvature_monotoneOn_right,
      criticalArea ++ `warp_pos,
      criticalArea ++ `exists_positive_constant_plateau,
      criticalArea ++ `meridionalAction_one_eq_zero,
      criticalArea ++ `exists_smooth_negative_probe_data,
      criticalArea ++ `exists_smooth_negative_probe,
      analysis ++ `bernsteinPolynomialOfCoefficients,
      analysis ++ `eval_bernsteinPolynomialOfCoefficients,
      analysis ++ `eval_bernsteinPolynomialOfCoefficients_unitInterval,
      analysis ++ `derivative_bernsteinPolynomialOfCoefficients_succ,
      analysis ++ `sampledBernsteinPolynomial,
      analysis ++ `eval_sampledBernsteinPolynomial,
      analysis ++ `bernsteinPolynomialOfCoefficients_mem_Icc,
      analysis ++ `monotoneOn_sampledBernsteinPolynomial,
      analysis ++ `tendsto_sampledBernsteinPolynomial,
      analysis ++ `squaredMidpointRadius,
      analysis ++ `squaredMidpointRadius_mem_Icc,
      analysis ++ `upperRadialProfile,
      analysis ++ `upperRadialArgument_mem_Icc,
      analysis ++ `monotoneOn_upperRadialProfile,
      analysis ++ `symmetricBernsteinApproximation,
      analysis ++ `symmetricBernsteinPolynomial,
      analysis ++ `eval_symmetricBernsteinPolynomial,
      analysis ++ `contDiff_symmetricBernsteinApproximation,
      analysis ++ `symmetric_symmetricBernsteinApproximation,
      analysis ++ `monotoneOn_symmetricBernsteinApproximation,
      analysis ++ `antitoneOn_symmetricBernsteinApproximation,
      analysis ++ `symmetricBernsteinApproximation_mem_Icc,
      analysis ++ `upperRadialProfile_squaredMidpointRadius_eq,
      l1Subseq ++ `exists_strictMono_ae_tendsto_of_integral_norm_tendsto_zero,
      momentRecovery ++ `firstMoment_eq_half_integral_of_reflection,
      momentRecovery ++ `exists_smooth_exactMoments_mem_box_l1_ae,
      area ++ `abs_warp_sub_le_integral_abs,
      area ++ `abs_warpSlope_sub_le_integral_abs,
      area ++ `tendsto_warp_of_l1,
      area ++ `tendsto_warpSlope_of_l1,
      area ++ `tendstoUniformlyOn_warp_of_l1,
      area ++ `tendstoUniformlyOn_warpSlope_of_l1,
      area ++ `tendsto_meridionalAction_of_l1_of_ae,
      area ++ `warp_affine_two,
      area ++ `warpSlope_affine_two,
      area ++ `continuous_meridionalAction_affine,
      geo ++ `oneFormDissipation_squares_integrable,
      geo ++ `oneFormDissipation_eq_integral_squares_of_constant_curvature,
      geo ++ `oneFormDissipation_nonneg_of_constant_curvature,
      criticalArea ++ `contractedCurvature,
      criticalArea ++ `contractedLower,
      criticalArea ++ `contractedUpper,
      criticalArea ++ `contractedCurvature_continuous,
      criticalArea ++ `contractedCurvature_moments,
      criticalArea ++ `contractedCurvature_reflection,
      criticalArea ++ `contractedCurvature_antitoneOn_left,
      criticalArea ++ `contractedCurvature_monotoneOn_right,
      criticalArea ++ `contractedCurvature_bounds,
      criticalArea ++ `contracted_strict_bounds,
      criticalArea ++ `contracted_ratio_deficit,
      criticalArea ++ `contracted_ratio_deficit_pos,
      criticalArea ++ `contracted_ratio_lt_criticalCap,
      criticalArea ++ `exists_negative_contraction_parameter_of_negative_action,
      criticalArea ++ `exists_smooth_negative_contraction,
      area ++ `exists_smooth_negative_action_of_symmetric_box,
      criticalArea ++ `exists_smooth_negative_area_data,
      geo ++ `exists_smooth_negative_geometric_realization,
      geo ++ `exists_negative_rotational_below_conformalKillingThreshold,
      geo ++ `rotationalSafeCaps,
      geo ++ `one_mem_rotationalSafeCaps,
      geo ++ `rotationalSafeCaps_nonempty,
      geo ++ `rotationalSafeCaps_downward,
      geo ++ `exists_contracted_bound_for_rotationalSafeCaps,
      geo ++ `rotationalSafeCaps_bddAbove,
      geo ++ `rotationalThreshold,
      geo ++ `one_le_rotationalThreshold,
      geo ++ `exists_contracted_ratio_above_rotationalThreshold,
      geo ++ `rotationalThreshold_lt_conformalKillingThreshold,
      area ++ `meridionalOperator,
      area ++ `meridionalOperator_contDiff,
      area ++ `meridionalAction_eq_square_potential,
      area ++ `meridionalGreenFlux,
      area ++ `meridionalGreenFlux_hasDerivAt,
      area ++ `meridionalGreenFlux_endpoints,
      area ++ `integral_warp_mul_operator_mul,
      area ++ `meridionalJacobiOperator,
      area ++ `meridionalJacobiOperator_contDiff,
      area ++ `integral_meridionalOperator_pair_eq_jacobi,
      area ++ `meridionalOperator_add_mul,
      area ++ `meridionalAction_add_mul,
      area ++ `meridionalAction_hasDerivAt,
      area ++ `integral_warp_mul_sq_pos,
      area ++ `meridionalAction_stationary_iff,
      area ++ `meridionalJacobiOperator_zero,
      area ++ `meridionalJacobiOperator_one,
      area ++ `meridionalAction_eq_integral_jacobi,
      area ++ `meridionalAction_const_mul,
      area ++ `exists_normalized_area_probe,
      area ++ `oneFormDissipation_eq_integral_jacobi_of_profile_probe,
      area ++ `oneFormDissipation_meridional_hasDerivAt,
      analysis ++ `VolterraPairing.integral_mul_primitive_eq,
      analysis ++ `VolterraPairing.integral_mul_kernel_eq,
      analysis ++ `exists_pos_add_mul_pos_of_isCompact,
      analysis ++ `exists_pos_add_mul_mem_Ioo_of_isCompact,
      analysis ++ `add_mul_sub_mem_Icc,
      analysis ++ `exists_pos_add_mul_mem_Icc_of_isCompact_of_free_support,
      area ++ `warpVariation,
      area ++ `warpSlopeVariation,
      area ++ `warp_add_mul,
      area ++ `warpSlope_add_mul,
      area ++ `warpVariation_hasDerivAt,
      area ++ `warpSlopeVariation_hasDerivAt,
      area ++ `warpVariation_continuous,
      area ++ `warpSlopeVariation_continuous,
      area ++ `curvature_moments_add_mul,
      area ++ `curvature_variation_endpoints,
      area ++ `probeMass,
      area ++ `rayleighQuotient,
      area ++ `probeMass_add_mul,
      area ++ `probeMass_hasDerivAt,
      area ++ `rayleighQuotient_hasDerivAt,
      area ++ `rayleighQuotient_stationary_iff,
      area ++ `rayleighQuotient_eq_of_probeMass_eq_one,
      area ++ `rayleighQuotient_stationary_iff_of_probeMass_eq_one,
      area ++ `rayleighQuotient_stationary_iff_of_action_eq_zero,
      area ++ `rayleighQuotient_euler_eq_of_isLocalMin,
      area ++ `normalizedProbe,
      area ++ `probeMass_normalizedProbe,
      area ++ `meridionalAction_normalizedProbe,
      area ++ `normalized_probe_action_hasDerivAt,
      area ++ `normalized_probe_euler_eq_of_isLocalMin,
      area ++ `curvatureWarpCoefficient,
      area ++ `curvatureSlopeCoefficient,
      area ++ `curvatureCoefficient,
      area ++ `meridionalOperator_continuous,
      area ++ `curvatureWarpCoefficient_continuous,
      area ++ `curvatureSlopeCoefficient_continuous,
      area ++ `curvatureCoefficient_continuous,
      area ++ `curvatureFirstVariation,
      area ++ `meridionalAction_curvature_hasDerivAt,
      area ++ `curvatureSwitchingDensity,
      area ++ `curvatureSwitchingDensity_continuous,
      area ++ `curvatureFirstVariation_eq_integral_switching,
      area ++ `meridionalAction_curvature_hasDerivAt_switching,
      area ++ `probeMass_curvature_add_mul,
      area ++ `probeMass_curvature_hasDerivAt,
      area ++ `curvatureLagrangeDensity,
      area ++ `action_sub_mass_curvature_hasDerivAt,
      area ++ `rayleighQuotient_curvature_hasDerivAt,
      area ++ `normalized_curvature_action_hasDerivAt,
      area ++ `eventually_normalized_curvature_variation,
      area ++ `isLocalMinOn_normalized_curvature_iff,
      area ++ `curvatureParameters,
      area ++ `mem_curvatureParameters_iff,
      area ++ `Icc_subset_curvatureParameters_segment,
      area ++ `curvatureParameters_mem_nhds_of_interior,
      area ++ `curvature_pairing_nonneg_of_isLocalMinOn_segment,
      area ++ `curvature_pairing_eq_zero_of_isLocalMinOn_interior,
      area ++ `curvatureParameters_mem_nhds_of_free_support,
      area ++ `curvature_pairing_eq_zero_of_isLocalMinOn_free_support,
      analysis ++ `eqOn_derivatives_Icc,
      geo ++ `ReciprocalArea.coordinate_contDiff,
      poleData ++ `AreaNormalization,
      poleData ++ `nonempty_areaNormalization,
      poleData ++ `areaNormalization,
      poleData ++ `AreaNormalization.inverse,
      poleData ++ `AreaNormalization.probe,
      poleData ++ `AreaNormalization.curvature_pos,
      poleData ++ `AreaNormalization.integral_curvature,
      poleData ++ `AreaNormalization.integral_mul_curvature,
      poleData ++ `AreaNormalization.inverse_contDiff,
      poleData ++ `AreaNormalization.inverse_hasDerivAt,
      poleData ++ `AreaNormalization.inverse_coordinate,
      poleData ++ `AreaNormalization.inverse_eq,
      poleData ++ `AreaNormalization.inverse_mem,
      poleData ++ `AreaNormalization.coordinate_inverse,
      poleData ++ `AreaNormalization.inverse_zero,
      poleData ++ `AreaNormalization.inverse_one,
      poleData ++ `AreaNormalization.curvature_coordinate,
      poleData ++ `AreaNormalization.warp_coordinate,
      poleData ++ `AreaNormalization.warpSlope_coordinate,
      poleData ++ `meridionalOneForm_eq_zero_iff,
      poleData ++ `meridionalOneForm_ne_zero_iff,
      poleData ++ `azimuthalOneForm_eq_zero_iff,
      poleData ++ `azimuthalOneForm_ne_zero_iff,
      area ++ `meridionalAction_congr,
      poleData ++ `AreaNormalization.probe_contDiff,
      poleData ++ `AreaNormalization.probe_coordinate,
      poleData ++ `AreaNormalization.deriv_probe,
      poleData ++ `AreaNormalization.deriv_deriv_probe,
      poleData ++ `AreaNormalization.curvature_deriv_coordinate,
      poleData ++ `AreaNormalization.meridionalOperator_coordinate,
      poleData ++ `AreaNormalization.meridionalDensity_coordinate,
      poleData ++ `AreaNormalization.meridionalAction_eq,
      poleData ++ `AreaNormalization.oneFormDissipation_meridional_eq,
      poleData ++ `AreaNormalization.curvature_eq_on,
      poleData ++ `AreaNormalization.curvature_deriv_eq_on,
      poleData ++ `AreaNormalization.inverse_eq_on,
      poleData ++ `AreaNormalization.probe_eq_on,
      poleData ++ `AreaNormalization.probe_derivatives_eq_on,
      poleData ++ `AreaNormalization.meridionalAction_extension_independent,
      poleData ++ `AreaNormalization.probe_comp_coordinate,
      poleData ++ `AreaNormalization.meridionalAction_comp_coordinate,
      poleData ++ `AreaNormalization.inverse_mem_Ioo,
      poleData ++ `AreaNormalization.probe_nonzero_iff,
      poleData ++ `AreaNormalization.probeMass_pos_iff_meridional_ne_zero,
      poleData ++ `AreaNormalization.probeMass_pos_iff_azimuthal_ne_zero,
      poleData ++ `AreaNormalization.normalized_probe_action,
      poleData ++ `AreaNormalization.integral_normSq_eq_probeMass,
      poleData ++ `AreaNormalization.curvature_inverse,
      poleData ++ `AreaNormalization.profile_mul_curvature,
      poleData ++ `AreaNormalization.curvature_bounds_scaled,
      poleData ++ `AreaNormalization.probeMass_pos_iff_pullback_meridional_ne_zero,
      poleData ++ `AreaNormalization.probeMass_pos_iff_pullback_azimuthal_ne_zero,
      poleData ++ `AreaNormalization.oneFormDissipation_pullback_meridional_eq,
      poleData ++ `AreaNormalization.meridionalAction_nonneg_of_normalized_safety,
      poleData ++ `AreaNormalization.exists_conjugated_haar_area_dissipation,
      poleData ++ `AreaNormalization.oneFormDissipation_nonneg_of_normalized_safety,
      poleData ++ `oneFormDissipation_eq_normalizedAreaAction,
      geo ++ `IsRepresentedRotationalMetric.exists_normalized_area_representation,
      geo ++ `rotationalSafeCaps_of_normalized_area_safety,
      geo ++ `areaAction_nonneg_of_rotationalSafeCap,
      poleData ++ `AreaNormalization.oneFormDissipation_meridional_hasDerivAt,
      poleData ++ `AreaNormalization.oneFormDissipation_meridional_stationary_iff,
      poleData ++ `AreaNormalization.oneFormDissipation_pullback_meridional_hasDerivAt,
      poleData ++ `AreaNormalization.oneFormDissipation_div_normSq_eq,
      poleData ++ `AreaNormalization.oneFormDissipation_div_normSq_hasDerivAt,
      poleData ++ `AreaNormalization.oneFormDissipation_div_normSq_euler_eq_of_isLocalMin,
      analysis ++ `integral_sq_le_parabolic_weighted_energy,
      area ++ `quadratic_le_warp_of_curvature_lower,
      area ++ `warp_le_quadratic_of_curvature_upper,
      area ++ `warp_bounds_of_curvature_bounds,
      area ++ `abs_warpSlope_le_two,
      area ++ `warp_nonneg_le_two_mul_min,
      area ++ `curvature_bounds_of_ratio,
      area ++ `probeOperatorEnergy,
      area ++ `probeGradientEnergy,
      area ++ `meridionalOperator_continuous_of_contDiff_two,
      area ++ `integral_warp_mul_probe_operator,
      area ++ `probeGradientEnergy_nonneg,
      area ++ `probeOperatorEnergy_nonneg,
      area ++ `probeGradientEnergy_interpolation,
      area ++ `integral_sq_le_probeMass_gradient,
      area ++ `polarProbeMass,
      area ++ `polarProbeMass_nonneg,
      area ++ `polarProbeMass_le_four_mul_radius,
      area ++ `probeOperatorEnergy_sub_le_action,
      area ++ `actionMassCorrection,
      area ++ `actionMassCorrection_nonneg,
      area ++ `meridionalAction_coercive,
      area ++ `exists_uniform_action_coercivity,
      area ++ `probe_energies_le_of_unit_mass_action_le,
      area ++ `polarProbeMass_le_of_unit_mass_action_le,
      area ++ `exists_uniform_polar_mass_radius,
      area ++ `meridionalAction_coercive_of_curvature_ratio,
      area ++ `exists_uniform_polar_mass_radius_of_ratio,
      analysis ++ `integral_parabolic_mul_sq_le,
      analysis ++ `integral_left_sq_le_parabolic_energy,
      analysis ++ `integral_polar_sq_le_parabolic_energy,
      area ++ `integral_warp_operator_add_curvature_sq,
      area ++ `integral_warp_cube_second_deriv_sq_le,
      area ++ `integral_parabolic_deriv_sq_le,
      area ++ `meridionalActionRemainder,
      area ++ `meridionalActionRemainder_continuous,
      area ++ `polarActionRemainder,
      area ++ `polarActionRemainder_le,
      area ++ `exists_uniform_probe_regularity_bound,
      area ++ `exists_uniform_polar_action_radius,
      area ++ `exists_uniform_polar_action_radius_of_ratio,
      analysis ++ `integrable_mul_of_ae_abs_le,
      analysis ++ `abs_integral_mul_sub_le_of_ae_abs_le,
      analysis ++ `tendsto_integral_mul_of_bounded_L2_pairings,
      analysis ++ `HilbertWeakSubsequence.norm_le_of_tendsto_inner,
      analysis ++ `HilbertWeakSubsequence.exists_subseq_tendsto_inner_of_norm_le,
      analysis ++ `exists_subseq_locallyUniform_of_local_derivative_energy,
      analysis ++ `mul_integral_sq_le_parabolic_energy,
      analysis ++ `exists_subseq_locallyUniform_probe_deriv_of_weighted_energy,
      analysis ++ `sq_sub_le_length_mul_integral_deriv_sq,
      analysis ++ `sq_sub_le_abs_mul_integral_deriv_sq,
      analysis ++ `length_mul_sq_le_integral_sq_add_integral_deriv_sq,
      analysis ++ `memLp_two_of_ae_tendsto_of_integral_sq_bound,
      analysis ++ `uniformIntegrable_two_of_sq_tails,
      analysis ++ `memLp_and_tendsto_eLpNorm_two_of_sq_tails,
      analysis ++ `L2WeakOrder.ae_nonneg_of_tendsto_inner,
      analysis ++ `L2WeakOrder.ae_bounds_of_tendsto_inner,
      analysis ++ `L2WeightedMassContinuity.tendsto_integral_mul_sq,
      analysis ++ `L2WeightedMassContinuity.tendsto_top_of_eventually_ae_abs_sub_le,
      analysis ++ `exists_subseq_tendstoLocallyUniformly_of_equicontinuous,
      analysis ++ `HasParabolicWeakDerivatives,
      analysis ++ `HasParabolicWeakDerivatives.integrable_sq,
      analysis ++ `HasParabolicWeakDerivatives.integrable_weighted_deriv_sq,
      analysis ++ `HasParabolicWeakDerivatives.integrable_weighted_secondDeriv_sq,
      analysis ++ `hasParabolicWeakDerivatives_of_contDiff,
      analysis ++ `HasParabolicWeakDerivatives.ae_unique,
      analysis ++ `HasParabolicWeakDerivatives.memLp_deriv_compact,
      analysis ++ `HasParabolicWeakDerivatives.memLp_secondDeriv_compact,
      analysis ++ `integrable_mul_of_locallyIntegrableOn,
      analysis ++ `HasWeakDerivOn,
      analysis ++ `HasWeakDerivOn.integrable_deriv_test_mul,
      analysis ++ `HasWeakDerivOn.integrable_test_mul_weakDeriv,
      analysis ++ `HasWeakDerivOn.ae_unique,
      analysis ++ `hasWeakDerivOn_of_contDiffOn,
      analysis ++ `hasWeakDerivOn_of_contDiff,
      analysis ++ `HasWeakDerivOn.congr_ae,
      analysis ++ `test_mul_integral_tendsto_of_locallyUniformlyOn,
      analysis ++ `HasWeakDerivOn.of_tendsto_test_pairings,
      analysis ++ `hasWeakDerivOn_of_locallyUniformlyOn,
      analysis ++ `locallyIntegrableOn_Ioo_div_weight,
      analysis ++ `memLp_two_Ioo_div_weight_on_compact,
      analysis ++ `memLp_two_Ioo_div_test,
      analysis ++ `ae_weight_mul_div_Ioo,
      analysis ++ `memLp_two_Ioo_weight_mul_div,
      analysis ++ `memLp_two_Ioo_weighted_deriv,
      analysis ++ `hasWeakDerivOn_Ioo_of_weighted_weak_L2_limit,
      area ++ `exists_curvature_subsequence_of_ratio_bound,
      area ++ `exists_normalized_joint_weak_limit,
      area ++ `exists_subseq_locallyUniform_probe_deriv_of_action_bound,
      area ++ `uniformIntegrable_probes_of_action_bound,
      area ++ `exists_subseq_strong_probe_of_action_bound,
      area ++ `exists_subseq_weak_probe_of_action_bound,
      area ++ `tendstoUniformlyOn_warpSlope_of_weak_L2,
      area ++ `tendstoUniformlyOn_warp_of_weak_L2,
      area ++ `continuousOn_warpSlope_of_weak_L2,
      area ++ `continuousOn_warp_of_weak_L2,
      area ++ `warp_bounds_of_weak_L2,
      area ++ `abs_warpSlope_le_two_of_weak_L2,
      area ++ `warp_endpoints_of_weak_L2,
      area ++ `hasWeakDerivOn_warp_of_weak_L2,
      area ++ `hasWeakDerivOn_warpSlope_of_weak_L2,
      area ++ `tendsto_warpSlope_of_weak_L2,
      area ++ `tendsto_warp_of_weak_L2,
      area ++ `weakMeridionalOperator,
      area ++ `weakMeridionalAction,
      area ++ `weakMeridionalAction_deriv,
      area ++ `memLp_weak_operator_and_potential_of_warp_bounds,
      area ++ `integrable_weakMeridionalActionDensity_of_warp_bounds,
      area ++ `weakMeridionalAction_intervalIntegrable_of_warp_bounds,
      area ++ `weakMeridionalAction_decomposition_of_warp_bounds,
      analysis ++ `HasWeakDerivOn.locallyIntegrable,
      analysis ++ `HasWeakDerivOn.locallyIntegrable_deriv,
      analysis ++ `HasWeakDerivOn.integral_deriv_mul,
      analysis ++ `HasParabolicWeakDerivatives.weakDeriv,
      analysis ++ `HasParabolicWeakDerivatives.weakDeriv_deriv,
      analysis ++ `HasParabolicWeakDerivatives.memLp,
      analysis ++ `HasParabolicWeakDerivatives.memLp_weighted_deriv,
      analysis ++ `HasParabolicWeakDerivatives.memLp_weighted_secondDeriv,
      analysis ++ `integrable_and_tendsto_mul_of_bounded_weak_pairing,
      analysis ++ `uniformIntegrable_mul_left_of_eLpNorm_two_bound,
      analysis ++ `tendsto_eLpNorm_one_mul_sub_of_ae_tendsto_of_integral_sq_bound,
      analysis ++ `tendsto_integral_abs_mul_sub_of_tendsto_eLpNorm_two,
      analysis ++ `tendsto_integral_abs_sub_of_ae_tendsto_of_integral_sq_bound,
      analysis ++ `tendsto_integral_mul_of_ae_tendsto_of_integral_sq_bound,
      analysis ++ `eventually_lt_integral_sq_of_weak_L2,
      analysis ++ `integral_sq_le_liminf_of_weak_L2,
      analysis ++ `eventually_lt_sum_integral_sq_sub_of_weak_L2,
      analysis ++ `memLp_mul_of_ae_abs_le,
      analysis ++ `tendsto_integral_mul_of_weak_L2_strong_L2,
      analysis ++ `tendsto_L2_mul_of_ae_tendsto,
      analysis ++ `weak_L2_mul_of_ae_tendsto_of_ae_abs_le,
      area ++ `exists_uniform_parabolic_graph_bound,
      area ++ `weak_derivative_part_of_area_limits,
      area ++ `curvature_action_pairings_tendsto,
      area ++ `weak_factors_and_action_liminf_of_area_limits,
      area ++ `exists_normalized_joint_weak_limit_le_liminf_action,
      analysis ++ `exists_tail_convexCombination_tendsto_of_tendsto_inner,
      analysis ++ `exists_tail_convexCombination_tendsto_family,
      analysis ++ `strong_L2_mul_of_ae_tendsto_of_ae_abs_le,
      analysis ++ `tendsto_integral_mul_of_tendsto_eLpNorm_two,
      area ++ `warp_sub_eq_integral_right_of_moments,
      area ++ `abs_warp_sub_le_relative_integral_abs,
      area ++ `abs_warpSlope_sub_le_integral_abs_of_integrableOn,
      area ++ `smooth_area_pair_convexCombination,
      analysis ++ `exists_tail_convexCombination_tendsto_eLpNorm_two,
      area ++ `exists_smooth_geometric_recovery_of_scalar_limits,
      area ++ `exists_smooth_convex_recovery_of_weak_graph_pairings,
      area ++ `action_mass_tendsto_of_strong_area_graph,
      area ++ `exists_smooth_scalar_recovery_of_weak_graph_pairings,
      area ++ `exists_joint_weak_limit_with_smooth_geometric_recovery,
      analysis ++ `strong_L2_const_mul_of_tendsto,
      analysis ++ `parabolicGraph_tendsto_const_mul,
      area ++ `IsSmoothAreaCompetitor,
      area ++ `smoothAreaActionValues,
      area ++ `smoothAreaInfimum,
      area ++ `IsSmoothAreaCompetitor.common_bounds,
      area ++ `IsSmoothAreaCompetitor.memLp_curvature,
      area ++ `probeMass_two_sqrt_three,
      area ++ `meridionalAction_two_sqrt_three,
      area ++ `isSmoothAreaCompetitor_round,
      area ++ `IsSmoothAreaCompetitor.action_lower_bound,
      area ++ `smoothAreaActionValues_nonempty,
      area ++ `smoothAreaActionValues_bddBelow,
      area ++ `smoothAreaInfimum_le_action,
      area ++ `smoothAreaInfimum_le_four,
      area ++ `neg_actionMassCorrection_le_smoothAreaInfimum,
      area ++ `exists_smooth_area_minimizing_sequence,
      area ++ `IsRecoverableAreaCompetitor,
      area ++ `IsSmoothAreaCompetitor.recoverable,
      area ++ `IsRecoverableAreaCompetitor.exists_action_recovery,
      area ++ `IsRecoverableAreaCompetitor.infimum_le_action,
      area ++ `exists_recoverable_area_minimizer,
      area ++ `exists_area_minimizer_with_geometric_recovery,
      poleData ++ `AreaNormalization.isSmoothAreaCompetitor_normalizedProbe,
      poleData ++
        `AreaNormalization.smoothAreaInfimum_le_length_sq_mul_oneFormDissipation_div_normSq,
      analysis ++ `HasWeakDerivOn.add,
      analysis ++ `HasWeakDerivOn.const_mul,
      analysis ++ `HasParabolicWeakDerivatives.add,
      analysis ++ `HasParabolicWeakDerivatives.const_mul,
      analysis ++ `parabolicGraph_tendsto_add_fixed_smooth,
      area ++ `IsRecoverableAreaCompetitor.strong_curvature_subsequence,
      area ++ `IsRecoverableAreaCompetitor.geometry_bounds,
      area ++ `weakMeridionalPairingDensity,
      area ++ `weakMeridionalPairing,
      area ++ `weakMeridionalPairing_symm,
      area ++ `weakMeridionalPairing_self,
      area ++ `weakMeridionalAction_const_mul,
      area ++ `integrable_weakMeridionalPairingDensity_of_warp_bounds,
      area ++ `weakMeridionalPairing_intervalIntegrable_of_warp_bounds,
      area ++ `weakMeridionalAction_add_mul,
      area ++ `weakMeridionalAction_hasDerivAt,
      area ++ `integrable_probeMassDensity_of_warp_bounds,
      area ++ `probeMass_intervalIntegrable_of_warp_bounds,
      area ++ `integrable_probeMassPairing_of_warp_bounds,
      area ++ `probeMassPairing_intervalIntegrable_of_warp_bounds,
      area ++ `probeMass_add_mul_of_warp_bounds,
      area ++ `probeMass_hasDerivAt_of_warp_bounds,
      area ++ `IsRecoverableAreaCompetitor.normalized_probe_add_mul,
      area ++ `IsRecoverableAreaCompetitor.weak_probe_equation_of_minimum,
      area ++ `exists_recoverable_area_minimizer_weak_probe_equation,
      area ++ `warp_affine_of_integrableOn,
      area ++ `warpSlope_affine_of_integrableOn,
      area ++ `curvature_moments_affine_of_integrableOn,
      area ++ `probeMass_affine_curvature_of_integrableOn,
      area ++ `probeMass_curvature_difference_intervalIntegrable,
      area ++ `probeMass_curvature_segment_hasDerivAt,
      area ++ `IsSmoothAreaCurvature,
      area ++ `IsSmoothAreaCompetitor.curvature_admissible,
      area ++ `IsSmoothAreaCurvature.with_unit_probe,
      area ++ `IsSmoothAreaCurvature.common_bounds,
      area ++ `IsSmoothAreaCurvature.memLp_curvature,
      area ++ `IsSmoothAreaCurvature.geometry_bounds,
      area ++ `IsSmoothAreaCurvature.convex_combination,
      area ++ `isSmoothAreaCurvature_round,
      area ++ `weakCurvatureSegmentDensity,
      area ++ `weakCurvatureSegmentVariation,
      area ++ `weakCurvatureSegmentDensity_integrable,
      area ++ `weakCurvatureSegmentDensity_intervalIntegrable,
      area ++ `weakMeridionalAction_curvature_segment_hasDerivAt,
      area ++ `IsRecoverableAreaCompetitor.probeMass_curvature_segment_pos,
      area ++ `IsRecoverableAreaCompetitor.normalized_curvature_segment,
      area ++ `IsRecoverableAreaCompetitor.curvature_segment_inequality_of_minimum,
      area ++ `exists_recoverable_area_minimizer_weak_conditions,
      analysis ++ `unitDirichletKernel,
      analysis ++ `unitDirichletSlopeKernel,
      analysis ++ `continuous_unitDirichletKernel,
      analysis ++ `measurable_unitDirichletKernel,
      analysis ++ `measurable_unitDirichletSlopeKernel,
      analysis ++ `abs_unitDirichletKernel_le,
      analysis ++ `abs_unitDirichletSlopeKernel_le_one,
      analysis ++ `integral_unitDirichletKernel,
      analysis ++ `integral_unitDirichletSlopeKernel,
      analysis ++ `integrable_kernel_adjoint_of_weighted_integrable,
      analysis ++ `integral_kernel_pairing_of_weighted_integrable,
      area ++ `weakCurvatureWarpCoefficient,
      area ++ `weakCurvatureSlopeCoefficient,
      area ++ `weakCurvatureCoefficient,
      area ++ `weakCurvatureWarpCoefficient_deriv,
      area ++ `weakCurvatureSlopeCoefficient_deriv,
      area ++ `weakCurvatureCoefficient_deriv,
      area ++ `IsRecoverableAreaCompetitor.curvature_coefficients_integrable,
      area ++ `warp_sub_eq_integral_unitDirichletKernel,
      area ++ `warpSlope_sub_eq_integral_unitDirichletSlopeKernel,
      area ++ `weakCurvatureAdjoint,
      area ++ `IsRecoverableAreaCompetitor.weakCurvatureAdjoint_integrable,
      area ++ `IsRecoverableAreaCompetitor.curvature_variation_eq_integral_adjoint,
      area ++ `IsRecoverableAreaCompetitor.curvature_adjoint_inequality_of_minimum,
      area ++ `exists_recoverable_area_minimizer_with_curvature_adjoint,
      analysis ++ `exists_contDiff_approx_Icc_of_memLp,
      analysis ++ `exists_contDiff_interior_moment_basis,
      analysis ++ `exists_contDiff_exact_moments_of_memLp_of_interior_box,
      analysis ++ `exists_contDiff_Icc_exact_balanced_moments,
      analysis ++ `exists_contDiff_Icc_exact_balanced_moments_sequence,
      area ++ `IsBoundedAreaCurvature,
      area ++ `IsBoundedAreaCurvature.memLp_curvature,
      area ++ `IsSmoothAreaCurvature.bounded,
      area ++ `IsRecoverableAreaCompetitor.curvature_bounded,
      area ++ `IsBoundedAreaCurvature.exists_smooth_recovery,
      area ++ `IsRecoverableAreaCompetitor.bounded_curvature_adjoint_inequality_of_minimum,
      area ++ `exists_recoverable_area_minimizer_with_bounded_curvature_adjoint,
      analysis ++ `box_variational_inequality_iff,
      analysis ++ `exists_box_moment_multipliers,
      area ++ `IsBoundedAreaCurvature.exists_strict_box,
      area ++ `IsBoundedAreaCurvature.ae_eq_round_of_cap_one,
      area ++ `IsRecoverableAreaCompetitor.exists_curvature_moment_multipliers,
      area ++ `exists_recoverable_area_minimizer_with_moment_multipliers,
      analysis ++ `second_order_weak_euler_flux,
      area ++ `weakProbeSecondCoefficient,
      area ++ `weakProbeFirstCoefficient,
      area ++ `weakProbeZerothCoefficient,
      area ++ `weakMeridionalPairingDensity_eq_probe_coefficients,
      area ++ `IsRecoverableAreaCompetitor.weak_probe_euler_coefficients_integrable,
      area ++ `weakProbeEulerFlux,
      area ++ `weakProbeEulerMomentum,
      area ++ `IsRecoverableAreaCompetitor.probe_euler_flux_of_minimum,
      area ++ `exists_recoverable_area_minimizer_with_natural_flux,
      analysis ++ `HasParabolicWeakDerivatives.mul_contDiff,
      analysis ++ `parabolicGraph_tendsto_mul_contDiff,
      area ++ `IsRecoverableAreaCompetitor.normalized_probe_mul,
      area ++ `IsRecoverableAreaCompetitor.weak_probe_mul_equation_of_minimum,
      area ++ `weakMeridionalPicone_density_identity,
      area ++ `meridionalAction_mul_sub_pairing_eq_picone,
      area ++ `meridionalAction_ge_mass_of_ground_state,
      area ++ `IsRecoverableAreaCompetitor.picone_identity_of_minimum,
      analysis ++ `HasWeakDerivOn.exists_integral_representative_Ioo,
      analysis ++ `HasWeakDerivOn.exists_continuous_representative_Ioo,
      analysis ++ `HasWeakDerivOn.absolutelyContinuousOnInterval,
      analysis ++ `HasWeakDerivOn.integral_eq_sub_of_continuousOn,
      analysis ++ `HasWeakDerivOn.hasDerivAt_of_continuousOn,
      analysis ++ `HasWeakDerivOn.contDiffOn_one_of_continuousOn,
      analysis ++ `HasWeakDerivOn.ae_hasDerivAt_of_continuousOn,
      analysis ++ `HasParabolicWeakDerivatives.contDiffOn_one_of_continuousOn,
      analysis ++ `not_exists_parabolicWeakDerivatives_abs_sub,
      area ++ `IsRecoverableAreaCompetitor.primitive_weak_derivatives,
      area ++ `IsRecoverableAreaCompetitor.primitive_local_regularity,
      area ++ `IsRecoverableAreaCompetitor.probe_first_order_system_of_minimum,
      area ++ `nonneg_of_meridionalOperator_nonpos,
      area ++ `pos_of_meridionalOperator_neg,
      area ++ `meridionalAction_ge_mass_of_negative_source,
      analysis ++ `eq_zero_of_integrableOn_div_left,
      analysis ++ `eq_zero_of_integrableOn_div_right,
      analysis ++ `nonneg_of_divergence_inequality,
      area ++ `weakProbeDerivativeFlux,
      area ++ `IsRecoverableAreaCompetitor.derivative_flux_absolutelyContinuous,
      area ++ `IsRecoverableAreaCompetitor.nonneg_of_weakMeridionalOperator_nonpos,
      analysis ++ `pos_of_divergence_inequality_of_nonneg,
      area ++ `IsRecoverableAreaCompetitor.pos_of_weakMeridionalOperator_nonpos,
      area ++ `probeMass_neg,
      area ++ `weakMeridionalOperator_neg,
      area ++ `weakMeridionalAction_neg,
      area ++ `IsRecoverableAreaCompetitor.neg_probe,
      area ++ `smoothAreaInfimum_nonneg_iff_rotationalSafeCap,
      area ++ `smoothAreaInfimum_neg_of_rotationalThreshold_lt,
      area ++ `IsRecoverableAreaCompetitor.of_curvature_cap,
      geo ++ `mem_rotationalSafeCaps_of_lt_rotationalThreshold,
      geo ++ `rotationalThreshold_mem_rotationalSafeCaps,
      area ++ `smoothAreaInfimum_rotationalThreshold,
      area ++ `exists_zero_action_recoverable_area_minimizer
    ] do
    unless decls.contains required do
      throwError "Missing required declaration {required}"
  if decls.size < 200 then
    throwError "Expected at least two hundred project declarations"
""".lstrip("\n")
LINT_DRIVER = "import RicciFlowSharpEstimate\n\nopen Lean Elab Command in\nrun_cmd do\n" + SELECTOR + r"""
  for declName in decls do
    let info ← getConstInfo declName
    match info with
    | .defnInfo value =>
      if ← liftTermElabM <| Meta.isProp value.type then
        throwError "Definition {declName} has a proposition as its type"
    | .thmInfo value =>
      unless ← liftTermElabM <| Meta.isProp value.type do
        throwError "Theorem {declName} has a data-valued type"
    | _ => pure ()
  let linters ← liftCoreM <| Batteries.Tactic.Lint.getChecks true
    (some [`unusedArguments, `simpNF, `synTaut]) none
  unless linters.size = 3 do
    throwError "The three declaration linters were not all selected"
  let results ← liftCoreM <| Batteries.Tactic.Lint.lintCore decls linters
  if results.any (!·.2.isEmpty) then
    let message ← liftCoreM <| Batteries.Tactic.Lint.formatLinterResults results decls
      (groupByFilename := true) "in RicciFlowSharpEstimate"
      (runSlowLinters := true) .low linters.size
    throwError message
""".lstrip("\n")
AXIOM_DRIVER = "import RicciFlowSharpEstimate\n\nopen Lean Elab Command in\nrun_cmd do\n" + SELECTOR + r"""
  logInfo m!"Selected {decls.size} project declarations, including private/generated declarations"
  let allowed := #[`propext, `Classical.choice, `Quot.sound]
  for declName in decls.qsort Name.quickLt do
    let axioms ← liftCoreM <| collectAxioms declName
    unless axioms.all (allowed.contains ·) do
      throwError "Unapproved transitive axioms for {declName}: {axioms}"
    logInfo m!"{declName}: {axioms}"
""".lstrip("\n")
SIGNATURE_DRIVER = """import RicciFlowSharpEstimate

#check RicciFlowSharpEstimate.Variational.existsUnique_capParameter
#check RicciFlowSharpEstimate.Variational.capParameter_spec
#check RicciFlowSharpEstimate.Variational.capParameter_eq_one_iff
#print RicciFlowSharpEstimate.Variational.orderedTriangle
#print RicciFlowSharpEstimate.Variational.pairFunctional
#print RicciFlowSharpEstimate.Variational.pairMarginal
#print RicciFlowSharpEstimate.Variational.pairRemainder
#check RicciFlowSharpEstimate.Variational.pairFunctional_sub_eq_integral_marginal
#check RicciFlowSharpEstimate.Variational.pairRemainder_nonneg
#check RicciFlowSharpEstimate.Variational.pairFunctional_le_of_firstVariation_nonneg
#check RicciFlowSharpEstimate.Variational.pairFunctional_congr
#check RicciFlowSharpEstimate.Variational.strictMonoOn_capParameter
#print RicciFlowSharpEstimate.Variational.lowerContact
#print RicciFlowSharpEstimate.Variational.upperContact
#check RicciFlowSharpEstimate.Variational.contact_bounds
#check RicciFlowSharpEstimate.Variational.one_sub_upperContact_sq
#print RicciFlowSharpEstimate.Variational.freeExponential
#print RicciFlowSharpEstimate.Variational.freeLeftPrimitive
#print RicciFlowSharpEstimate.Variational.freeRightPrimitive
#check RicciFlowSharpEstimate.Variational.integral_freeExponential
#check RicciFlowSharpEstimate.Variational.integral_two_mul_div_freeExponential
#print RicciFlowSharpEstimate.Variational.obstacleExponential
#print RicciFlowSharpEstimate.Variational.obstacleLogProfile
#check RicciFlowSharpEstimate.Variational.obstacleExponential_eq_piecewise
#check RicciFlowSharpEstimate.Variational.obstacleLogProfile_admissible
#check RicciFlowSharpEstimate.Variational.obstacleLogProfile_one
#check RicciFlowSharpEstimate.Variational.contact_separation_iff
#check RicciFlowSharpEstimate.Analysis.exp_tangent_quadratic_lower
#print RicciFlowSharpEstimate.Variational.obstaclePrefix
#print RicciFlowSharpEstimate.Variational.obstacleTail
#check RicciFlowSharpEstimate.Variational.obstaclePrefix_eq_low
#check RicciFlowSharpEstimate.Variational.obstaclePrefix_eq_free
#check RicciFlowSharpEstimate.Variational.obstaclePrefix_eq_high
#check RicciFlowSharpEstimate.Variational.obstacleTail_eq_low
#check RicciFlowSharpEstimate.Variational.obstacleTail_eq_free
#check RicciFlowSharpEstimate.Variational.obstacleTail_eq_high
#check RicciFlowSharpEstimate.Variational.pairMarginal_eq_intervalIntegrals
#check RicciFlowSharpEstimate.Variational.pairMarginal_eq_zero_of_not_mem
#check RicciFlowSharpEstimate.Variational.integrable_pairMarginal
#check RicciFlowSharpEstimate.Variational.pairFunctional_eq_intervalIntegral
#check RicciFlowSharpEstimate.Variational.pairMarginal_obstacleLogProfile_low
#check RicciFlowSharpEstimate.Variational.pairMarginal_obstacleLogProfile_free
#check RicciFlowSharpEstimate.Variational.pairMarginal_obstacleLogProfile_high
#check RicciFlowSharpEstimate.Variational.pairFunctional_obstacleLogProfile_le
#check RicciFlowSharpEstimate.Variational.pairFunctional_obstacleLogProfile_eq
#check RicciFlowSharpEstimate.Variational.pairFunctional_obstacleLogProfile_one
#check RicciFlowSharpEstimate.Variational.pairRemainder_eq_zero_iff
#check RicciFlowSharpEstimate.Variational.hasDerivWithinAt_obstacleLogProfile_lowerContact_Iic
#check RicciFlowSharpEstimate.Variational.hasDerivWithinAt_obstacleLogProfile_lowerContact_Ici
#check RicciFlowSharpEstimate.Variational.hasDerivWithinAt_obstacleLogProfile_upperContact_Iic
#check RicciFlowSharpEstimate.Variational.hasDerivWithinAt_obstacleLogProfile_upperContact_Ici
#check RicciFlowSharpEstimate.Variational.not_differentiableAt_obstacleLogProfile_lowerContact
#check RicciFlowSharpEstimate.Variational.not_differentiableAt_obstacleLogProfile_upperContact
#check RicciFlowSharpEstimate.Variational.pairFunctional_eq_obstacleLogProfile_iff
#check RicciFlowSharpEstimate.Variational.pairFunctional_ge_closedForm
#check RicciFlowSharpEstimate.Variational.pairFunctional_eq_closedForm_iff
#check RicciFlowSharpEstimate.Variational.pairFunctional_obstacleLogProfile_lt_of_differentiableOn
#print RicciFlowSharpEstimate.Variational.lowerObstacleWeight
#check RicciFlowSharpEstimate.Variational.integral_lowerObstacleWeight
#check RicciFlowSharpEstimate.Variational.integral_lowerObstacleWeight_sq
#check RicciFlowSharpEstimate.Variational.pairFirstVariation_eq_intervalIntegral_marginal
#check RicciFlowSharpEstimate.Variational.pairFirstVariation_obstacleLogProfile_nonneg
#check RicciFlowSharpEstimate.Variational.integral_lowerObstacleWeight_error_sq_le
#check RicciFlowSharpEstimate.Variational.pairRemainder_ge_quadratic_integral
#print RicciFlowSharpEstimate.Variational.pairQuadratic
#print RicciFlowSharpEstimate.Variational.unitMean
#print RicciFlowSharpEstimate.Variational.unitCentered
#print RicciFlowSharpEstimate.Variational.centeredPrimitive
#check RicciFlowSharpEstimate.Variational.pairQuadratic_eq_centered_integrals
#check RicciFlowSharpEstimate.Variational.integral_unitCentered_sq_le_pairQuadratic
#check RicciFlowSharpEstimate.Analysis.integral_sq_le_of_variance_anchor
#check RicciFlowSharpEstimate.Analysis.integral_evenExtension_error_sq_eq
#check RicciFlowSharpEstimate.Analysis.integral_reflection_error_sq_le
#check RicciFlowSharpEstimate.Analysis.integral_symmetrization_error_sq_eq
#print RicciFlowSharpEstimate.Variational.stabilityConstant
#check RicciFlowSharpEstimate.Variational.stabilityConstant_pos
#check RicciFlowSharpEstimate.Variational.pairFunctional_deficit_controls_L2
#print RicciFlowSharpEstimate.Variational.hemisphereDeficit
#check RicciFlowSharpEstimate.Variational.hemisphereDeficit_controls_evenExtension
#check RicciFlowSharpEstimate.Variational.hemisphereDeficit_controls_reflection
#check RicciFlowSharpEstimate.Variational.hemisphereDeficit_controls_symmetrization
#check RicciFlowSharpEstimate.Analysis.exists_contDiff_one_sub_sq_factor_of_roots
#print RicciFlowSharpEstimate.Geometry.RotationalProfile.balance
#print RicciFlowSharpEstimate.Geometry.RotationalProfile.warp
#print RicciFlowSharpEstimate.Geometry.RotationalProfile.momentCoordinate
#check RicciFlowSharpEstimate.Geometry.RotationalProfile.momentCoordinate_hasDerivAt
#check RicciFlowSharpEstimate.Geometry.RotationalProfile.warp_hasDerivAt
#check RicciFlowSharpEstimate.Geometry.RotationalProfile.momentCoordinate_strictMonoOn
#check RicciFlowSharpEstimate.Geometry.RotationalProfile.warp_northPole_slope
#check RicciFlowSharpEstimate.Geometry.RotationalProfile.warp_southPole_slope
#check RicciFlowSharpEstimate.Geometry.RotationalProfile.warp_pos_of_balance
#check RicciFlowSharpEstimate.Geometry.RotationalProfile.warp_contDiff
#check RicciFlowSharpEstimate.Geometry.RotationalProfile.warp_const
#check RicciFlowSharpEstimate.Geometry.RotationalProfile.balance_const
#check RicciFlowSharpEstimate.Geometry.RotationalProfile.exists_smooth_positive_warp_factor
#print RicciFlowSharpEstimate.Geometry.RotationalProfile.PoleData
#check RicciFlowSharpEstimate.Geometry.RotationalProfile.exists_poleData
#check RicciFlowSharpEstimate.Geometry.RotationalProfile.PoleData.constant
#print RicciFlowSharpEstimate.Geometry.RotationalSphere
#print RicciFlowSharpEstimate.Geometry.sphereHeight
#check RicciFlowSharpEstimate.Geometry.sphereHeight_contMDiff
#check RicciFlowSharpEstimate.Geometry.sphereHeight_mem_Icc
#print RicciFlowSharpEstimate.Geometry.heightOneForm
#check RicciFlowSharpEstimate.Geometry.heightOneForm_apply
#print RicciFlowSharpEstimate.Geometry.HeightMetricCoefficients
#check RicciFlowSharpEstimate.Geometry.HeightMetricCoefficients.heightOneForm_sq_le
#check RicciFlowSharpEstimate.Geometry.HeightMetricCoefficients.metric_inner_apply
#check RicciFlowSharpEstimate.Geometry.RotationalProfile.PoleData.radial_identity
#check RicciFlowSharpEstimate.Geometry.RotationalProfile.PoleData.metric_inner
#check RicciFlowSharpEstimate.Geometry.RotationalProfile.PoleData.constant_metric_inner
#check RicciFlowSharpEstimate.Geometry.exists_metric_of_smooth_positive_balanced_profile
#check LinearMap.det_smul_add_rankOne_gram_fin_two
#check RicciFlowSharpEstimate.Geometry.round_grad_sphereHeight_inner_self
#check RicciFlowSharpEstimate.Geometry.RotationalProfile.PoleData.det_chartGramMatrix_metric
#check RicciFlowSharpEstimate.Geometry.RotationalProfile.PoleData.chartDensity_metric
#check RicciFlowSharpEstimate.Geometry.RotationalProfile.PoleData.volume_metric_eq_withDensity
#check RicciFlowSharpEstimate.Geometry.RotationalProfile.PoleData.integral_volume_metric
#check RicciFlowSharpEstimate.Geometry.integral_round_height
#check RicciFlowSharpEstimate.Geometry.RotationalProfile.PoleData.integral_height_metric
#check RicciFlowSharpEstimate.Geometry.metricScalarAt_eq_radialDiagonalJet
#print RicciFlowSharpEstimate.Geometry.RotationalProfile.PoleData.radialCoefficient
#check RicciFlowSharpEstimate.Geometry.RotationalProfile.PoleData.radialCoefficient_contDiffOn
#check RicciFlowSharpEstimate.Geometry.RotationalProfile.PoleData.deriv_warp_hasDerivAt
#check RicciFlowSharpEstimate.Geometry.RotationalProfile.PoleData.radialCoefficient_hasDerivAt
#check RicciFlowSharpEstimate.Geometry.RotationalProfile.PoleData.radial_curvature_identity
#print RicciFlowSharpEstimate.Geometry.cylinderDomain
#print RicciFlowSharpEstimate.Geometry.cylinderMap
#check RicciFlowSharpEstimate.Geometry.cylinderMap_coe
#check RicciFlowSharpEstimate.Geometry.sphereHeight_cylinderMap
#check RicciFlowSharpEstimate.Geometry.cylinderMap_contMDiff
#check RicciFlowSharpEstimate.Geometry.cylinderMap_dIncl_mfderiv
#check RicciFlowSharpEstimate.Geometry.cylinderMap_round_inner
#check RicciFlowSharpEstimate.Geometry.cylinderMap_mfderiv_injective
#check RicciFlowSharpEstimate.Geometry.RotationalProfile.PoleData.cylinderMap_warp_pos
#check RicciFlowSharpEstimate.Geometry.RotationalProfile.PoleData.cylinderMap_metric_inner
#check RicciFlowSharpEstimate.Geometry.range_cylinderMap
#check RicciFlowSharpEstimate.Geometry.denseRange_cylinderMap
#check RicciFlowSharpEstimate.Geometry.RotationalProfile.PoleData.metricScalarAt_cylinderMap
#check RicciFlowSharpEstimate.Geometry.RotationalProfile.PoleData.metricScalarAt_metric
#check RicciFlowSharpEstimate.Geometry.RotationalProfile.PoleData.sectionalCurvature_metric
#check DifferentialGeometry.Tensor0SBundle.TotalNabla0SRealizes.unique
#check DifferentialGeometry.Tensor0SBundle.CanonicalSpatialDerivs0S.unique
#print RicciFlowSharpEstimate.Geometry.canonicalDerivatives
#check RicciFlowSharpEstimate.Geometry.canonicalDerivatives_nablaA
#check RicciFlowSharpEstimate.Geometry.canonicalDerivatives_nabla2A
#check RicciFlowSharpEstimate.Geometry.canonicalDerivatives_first
#check RicciFlowSharpEstimate.Geometry.canonicalDerivatives_second
#check RicciFlowSharpEstimate.Geometry.canonicalDerivatives_unique
#check RicciFlowSharpEstimate.Geometry.canonicalDerivatives_nabla2A_add
#check RicciFlowSharpEstimate.Geometry.canonicalDerivatives_nabla2A_smul
#check RicciFlowSharpEstimate.Geometry.canonicalDerivatives_nabla2OneFormRealizesAt
#check RicciFlowSharpEstimate.Geometry.roughLap0SField_add
#check RicciFlowSharpEstimate.Geometry.roughLap0SField_smul
#print RicciFlowSharpEstimate.Geometry.ahlforsPart
#check RicciFlowSharpEstimate.Geometry.ahlforsPart_apply
#check RicciFlowSharpEstimate.Geometry.ahlforsPart_apply_of_finrank_eq_two
#check RicciFlowSharpEstimate.Geometry.ahlforsPart_symmetric
#check RicciFlowSharpEstimate.Geometry.ahlforsPart_trace_eq_zero
#check RicciFlowSharpEstimate.Geometry.ahlforsPart_add
#check RicciFlowSharpEstimate.Geometry.ahlforsPart_smul
#check RicciFlowSharpEstimate.Geometry.sphereCoordinateOneForm_apply
#check RicciFlowSharpEstimate.Geometry.sphereCoordinateOneForm_two
#check RicciFlowSharpEstimate.Geometry.sphereAzimuthalOneForm_apply
#check RicciFlowSharpEstimate.Geometry.heightOneForm_eq_zero_at_pole
#check RicciFlowSharpEstimate.Geometry.sphereAzimuthalOneForm_eq_zero_at_pole
#print RicciFlowSharpEstimate.Geometry.RotationalProfile.PoleData.meridionalOneForm
#print RicciFlowSharpEstimate.Geometry.RotationalProfile.PoleData.azimuthalOneForm
#check RicciFlowSharpEstimate.Geometry.RotationalProfile.PoleData.meridionalOneForm_apply_dIncl
#check RicciFlowSharpEstimate.Geometry.RotationalProfile.PoleData.azimuthalOneForm_apply_dIncl
#check
  RicciFlowSharpEstimate.Geometry.RotationalProfile.PoleData.meridionalOneForm_cylinderMap_mfderiv
#check
  RicciFlowSharpEstimate.Geometry.RotationalProfile.PoleData.azimuthalOneForm_cylinderMap_mfderiv
#check RicciFlowSharpEstimate.Geometry.RotationalProfile.PoleData.meridionalOneForm_eq_zero_at_pole
#check RicciFlowSharpEstimate.Geometry.RotationalProfile.PoleData.azimuthalOneForm_eq_zero_at_pole
#check RicciFlowSharpEstimate.Geometry.RotationalProfile.PoleData.meridionalOneForm_one_ne_zero
#check RicciFlowSharpEstimate.Geometry.RotationalProfile.PoleData.azimuthalOneForm_one_ne_zero
#print RicciFlowSharpEstimate.Geometry.oneFormDissipationDensity
#print RicciFlowSharpEstimate.Geometry.oneFormDissipationPairingDensity
#check RicciFlowSharpEstimate.Geometry.oneFormDissipationDensity_smooth
#check RicciFlowSharpEstimate.Geometry.oneFormDissipationDensity_integrable
#check RicciFlowSharpEstimate.Geometry.oneFormDissipationPairingDensity_smooth
#check RicciFlowSharpEstimate.Geometry.oneFormDissipationPairingDensity_integrable
#print RicciFlowSharpEstimate.Geometry.oneFormDissipation
#print RicciFlowSharpEstimate.Geometry.oneFormDissipationPairing
#check RicciFlowSharpEstimate.Geometry.oneFormDissipationPairing_self
#check RicciFlowSharpEstimate.Geometry.oneFormDissipationPairing_symm
#check RicciFlowSharpEstimate.Geometry.oneFormDissipationPairing_add_left
#check RicciFlowSharpEstimate.Geometry.oneFormDissipationPairing_add_right
#check RicciFlowSharpEstimate.Geometry.oneFormDissipationPairing_smul_left
#check RicciFlowSharpEstimate.Geometry.oneFormDissipationPairing_smul_right
#check RicciFlowSharpEstimate.Geometry.oneFormDissipation_zero
#check RicciFlowSharpEstimate.Geometry.oneFormDissipation_smul
#check RicciFlowSharpEstimate.Geometry.oneFormDissipation_add
#check RicciFlowSharpEstimate.Geometry.oneFormDissipation_sub
#check RicciFlowSharpEstimate.Geometry.oneFormDissipation_parallelogram
#check RicciFlowSharpEstimate.Geometry.RotationalProfile.PoleData.oneFormDissipationDensity_metric
open RicciFlowSharpEstimate.Geometry.RotationalProfile.PoleData in
#check oneFormDissipation_eq_weightedRoundIntegral
open RicciFlowSharpEstimate.Geometry.RotationalProfile.PoleData in
#check weighted_dissipationDensity_integrable
open RicciFlowSharpEstimate.Geometry in
#check roughLap0SField_duSec_apply
open RicciFlowSharpEstimate.Geometry in
#check roughLap0SField_duSec_of_finrank_eq_two
open RicciFlowSharpEstimate.Geometry in
#check metricTracePair0SAt_product_one
open RicciFlowSharpEstimate.Geometry in
#check inner0S_product_one
open RicciFlowSharpEstimate.Geometry in
#check normSq0S_of_apply_eq_rankOne_add_metric
open RicciFlowSharpEstimate.Geometry in
#check normSq0S_ahlforsPart_of_apply_eq_rankOne_add_metric
open RicciFlowSharpEstimate.Geometry.RotationalProfile.PoleData in
#check inverseMetricSharpFib_heightOneForm
open RicciFlowSharpEstimate.Geometry.RotationalProfile.PoleData in
#check heightOneForm_normSq
open RicciFlowSharpEstimate.Geometry.RotationalProfile.PoleData in
#check meridionalOneForm_normSq
open RicciFlowSharpEstimate.Geometry.RotationalProfile.PoleData in
#check meridionalWeight_hasDerivAt
open RicciFlowSharpEstimate.Geometry.RotationalProfile.PoleData in
#check meridionalDensity_intervalIntegrable
open RicciFlowSharpEstimate.Geometry.RotationalProfile.PoleData in
#check meridionalAction_constant_one
open RicciFlowSharpEstimate.Geometry.RotationalProfile.PoleData in
#check duSec_meridionalPotential
open RicciFlowSharpEstimate.Geometry.RotationalProfile.PoleData in
#check metricNabla0S_meridionalOneForm
open RicciFlowSharpEstimate.Geometry.RotationalProfile.PoleData in
#check meridionalOneForm_nabla_trace
open RicciFlowSharpEstimate.Geometry.RotationalProfile.PoleData in
#check meridionalOneForm_nabla_normSq
open RicciFlowSharpEstimate.Geometry.RotationalProfile.PoleData in
#check meridionalOneForm_ahlfors_normSq
open RicciFlowSharpEstimate.Geometry.RotationalProfile.PoleData in
#check laplacian_meridionalPotential
open RicciFlowSharpEstimate.Geometry.RotationalProfile.PoleData in
#check roughLap0SField_meridionalOneForm
open RicciFlowSharpEstimate.Geometry.RotationalProfile.PoleData in
#check oneFormDissipationDensity_meridional
open RicciFlowSharpEstimate.Geometry.RotationalProfile.PoleData in
#check oneFormDissipation_meridional
open RicciFlowSharpEstimate.Geometry.RotationalProfile.PoleData in
#check oneFormDissipation_constant_meridional_one
open RicciFlowSharpEstimate.Geometry.RotationalProfile.PoleData in
#print meridionalWeight
open RicciFlowSharpEstimate.Geometry.RotationalProfile.PoleData in
#print meridionalOperator
open RicciFlowSharpEstimate.Geometry.RotationalProfile.PoleData in
#print meridionalDensity
open RicciFlowSharpEstimate.Geometry.RotationalProfile.PoleData in
#print meridionalAction
open RicciFlowSharpEstimate.Geometry in
#check diffeomorphTensorPullback
open RicciFlowSharpEstimate.Geometry in
#check diffeomorphTensorPullback_apply
open RicciFlowSharpEstimate.Geometry in
#check diffeomorphTensorPullback_refl
open RicciFlowSharpEstimate.Geometry in
#check diffeomorphTensorPullback_trans
open RicciFlowSharpEstimate.Geometry in
#check diffeomorphTensorPullback_symm_apply
open RicciFlowSharpEstimate.Geometry in
#check diffeomorphTensorPullback_apply_symm
open RicciFlowSharpEstimate.Geometry in
#check metricNabla0S_diffeomorphTensorPullback
open RicciFlowSharpEstimate.Geometry in
#check metricNabla0S_twice_diffeomorphTensorPullback
open RicciFlowSharpEstimate.Geometry in
#check roughLap0SField_diffeomorphTensorPullback
open RicciFlowSharpEstimate.Geometry in
#check ahlforsPart_diffeomorphTensorPullback
open RicciFlowSharpEstimate.Geometry in
#check oneFormDissipation_diffeomorphTensorPullback
open RicciFlowSharpEstimate.Geometry in
#check oneFormDissipationPairing_diffeomorphTensorPullback_of_isometry
open RicciFlowSharpEstimate.Geometry in
#check meridianReflectionSphereDiffeo_coe
open RicciFlowSharpEstimate.Geometry in
#check meridianReflectionSphereDiffeo_dIncl_mfderiv
open RicciFlowSharpEstimate.Geometry in
#check metricNabla0S_eq_zero_of_alternating_const_normSq
open RicciFlowSharpEstimate.Geometry in
#check normSq0S_eq_two_of_unit_alternating
open RicciFlowSharpEstimate.Geometry in
#check roundSphereAreaForm_apply
open RicciFlowSharpEstimate.Geometry.RotationalProfile.PoleData in
#check pullbackMetric_meridianReflectionSphereDiffeo
open RicciFlowSharpEstimate.Geometry.RotationalProfile.PoleData in
#check oneFormDissipationPairing_meridional_azimuthal
open RicciFlowSharpEstimate.Geometry.RotationalProfile.PoleData in
#check oneFormDissipation_meridional_add_azimuthal
open RicciFlowSharpEstimate.Geometry.RotationalProfile.PoleData in
#check areaForm_apply
open RicciFlowSharpEstimate.Geometry.RotationalProfile.PoleData in
#check areaForm_normSq
open RicciFlowSharpEstimate.Geometry.RotationalProfile.PoleData in
#check metricNabla0S_areaForm
open RicciFlowSharpEstimate.Geometry in
#check dIncl_round_grad_sphereHeight
open RicciFlowSharpEstimate.Geometry in
#check roundSphereAreaForm_round_grad_sphereHeight
open RicciFlowSharpEstimate.Geometry in
#check normSq0S_one_eq_of_rotation
open RicciFlowSharpEstimate.Geometry in
#check normSq0S_two_eq_of_rotation
open RicciFlowSharpEstimate.Geometry in
#check normSq0S_ahlforsPart_eq_of_rotation
open RicciFlowSharpEstimate.Geometry in
#check oneFormAreaContraction
open RicciFlowSharpEstimate.Geometry in
#check oneFormAreaContraction_apply
open RicciFlowSharpEstimate.Geometry in
#check oneFormAreaContraction_add
open RicciFlowSharpEstimate.Geometry in
#check oneFormAreaContraction_smul
open RicciFlowSharpEstimate.Geometry in
#check metricNabla0S_oneFormAreaContraction
open RicciFlowSharpEstimate.Geometry in
#check metricNabla0S_twice_oneFormAreaContraction
open RicciFlowSharpEstimate.Geometry in
#check roughLap0SField_oneFormAreaContraction
open RicciFlowSharpEstimate.Geometry in
#check oneFormDissipationDensity_oneFormAreaContraction
open RicciFlowSharpEstimate.Geometry in
#check oneFormDissipation_oneFormAreaContraction
open RicciFlowSharpEstimate.Geometry.RotationalProfile.PoleData in
#check inverseMetricSharpFib_meridionalOneForm
open RicciFlowSharpEstimate.Geometry.RotationalProfile.PoleData in
#check areaForm_inverseMetricSharpFib_meridionalOneForm
open RicciFlowSharpEstimate.Geometry.RotationalProfile.PoleData in
#check hodgeRotation
open RicciFlowSharpEstimate.Geometry.RotationalProfile.PoleData in
#check hodgeRotation_apply
open RicciFlowSharpEstimate.Geometry.RotationalProfile.PoleData in
#check hodgeRotation_meridionalOneForm
open RicciFlowSharpEstimate.Geometry.RotationalProfile.PoleData in
#check oneFormDissipation_hodgeRotation
open RicciFlowSharpEstimate.Geometry.RotationalProfile.PoleData in
#check oneFormDissipation_azimuthal_eq_meridional
open RicciFlowSharpEstimate.Geometry.RotationalProfile.PoleData in
#check oneFormDissipation_azimuthal
open RicciFlowSharpEstimate.Geometry.RotationalProfile.PoleData in
#check oneFormDissipation_zonal
open RicciFlowSharpEstimate.Analysis in
#check contMDiffOn_intervalIntegral
open RicciFlowSharpEstimate.Analysis in
#check contMDiff_intervalIntegral
open RicciFlowSharpEstimate.Analysis in
#check mvfderiv_intervalIntegral_apply_of_contMDiffOn
open RicciFlowSharpEstimate.Analysis in
#check mvfderiv_intervalIntegral_apply
open RicciFlowSharpEstimate.Analysis in
#check continuousOn_mvfderiv_apply_of_contMDiffOn
open RicciFlowSharpEstimate.Analysis in
#check continuous_mvfderiv_apply
open RicciFlowSharpEstimate.Analysis in
#check intervalIntegrable_mvfderiv_apply_of_contMDiffOn
open RicciFlowSharpEstimate.Analysis in
#check intervalIntegrable_mvfderiv_apply
open RicciFlowSharpEstimate.Geometry in
#check axisRotation_apply
open RicciFlowSharpEstimate.Geometry in
#check axisRotationRepresentation
open RicciFlowSharpEstimate.Geometry in
#check circleSphereDiffeo_coe
open RicciFlowSharpEstimate.Geometry in
#check circleSphereDiffeo_mul
open RicciFlowSharpEstimate.Geometry in
#check circleSphereDiffeo_inv
open RicciFlowSharpEstimate.Geometry in
#check circleSphereDiffeo_dIncl_mfderiv
open RicciFlowSharpEstimate.Geometry in
#check angleRotation_add
open RicciFlowSharpEstimate.Geometry in
#check angleRotation_periodic
open RicciFlowSharpEstimate.Geometry in
#check angleRotation_contMDiff
open RicciFlowSharpEstimate.Geometry in
#check mfderiv_family_zero_parameter
open RicciFlowSharpEstimate.Geometry in
#check contMDiff_diffeomorphTensorPullback_family
open RicciFlowSharpEstimate.Geometry in
#check contMDiff_diffeomorphTensorPullback_family_apply_sections
open RicciFlowSharpEstimate.Geometry in
#check continuous_diffeomorphTensorPullback_family_at
open RicciFlowSharpEstimate.Geometry in
#check diffeomorphTensorPullback_angleRotation_add
open RicciFlowSharpEstimate.Geometry in
#check contMDiff_diffeomorphTensorPullback_angleRotation
open RicciFlowSharpEstimate.Geometry in
#check tensorIntervalIntegral_apply
open RicciFlowSharpEstimate.Geometry in
#check tensorIntervalIntegral_eval
open RicciFlowSharpEstimate.Geometry in
#check intervalIntegrable_tensorFamily_at
open RicciFlowSharpEstimate.Geometry in
#check metricNabla0S_tensorIntervalIntegral
open RicciFlowSharpEstimate.Geometry in
#check inner0S_tensorIntervalIntegral_left
open RicciFlowSharpEstimate.Geometry in
#check intervalIntegrable_inner0S_tensorFamily_left
open RicciFlowSharpEstimate.Geometry in
#check metricTracePair0SAt_tensorIntervalIntegral
open RicciFlowSharpEstimate.Geometry in
#check roughLap0STensor_tensorIntervalIntegral_apply
open RicciFlowSharpEstimate.Geometry in
#check ahlforsPart_tensorIntervalIntegral_apply
open RicciFlowSharpEstimate.Geometry in
#check rotationalAverage_apply
open RicciFlowSharpEstimate.Geometry in
#check rotationalAverage_add
open RicciFlowSharpEstimate.Geometry in
#check rotationalAverage_smul
open RicciFlowSharpEstimate.Geometry in
#check diffeomorphTensorPullback_circle_rotationalAverage
open RicciFlowSharpEstimate.Geometry in
#check rotationalAverage_eq_self_iff
open RicciFlowSharpEstimate.Geometry in
#check rotationalAverage_idempotent
open RicciFlowSharpEstimate.Geometry in
#check rotationalAverage_sub_average
open RicciFlowSharpEstimate.Geometry.RotationalProfile.PoleData in
#check pullbackMetric_angleRotation
open RicciFlowSharpEstimate.Geometry.RotationalProfile.PoleData in
#check metricNabla0S_angleRotation
open RicciFlowSharpEstimate.Geometry.RotationalProfile.PoleData in
#check continuous_oneFormDissipationPairingDensity_angleRotation
open RicciFlowSharpEstimate.Geometry.RotationalProfile.PoleData in
#check integrable_oneFormDissipationPairingDensity_angleRotation
open RicciFlowSharpEstimate.Geometry.RotationalProfile.PoleData in
#check intervalIntegrable_oneFormDissipationPairing_angleRotation
open RicciFlowSharpEstimate.Geometry.RotationalProfile.PoleData in
#check integral_intervalIntegral_oneFormDissipationPairingDensity_angleRotation
open RicciFlowSharpEstimate.Geometry.RotationalProfile.PoleData in
#check rotationalAverage_meridionalOneForm
open RicciFlowSharpEstimate.Geometry.RotationalProfile.PoleData in
#check rotationalAverage_meridional_one_ne_zero
open RicciFlowSharpEstimate.Geometry.RotationalProfile.PoleData in
#check metricNabla0S_rotationalAverage
open RicciFlowSharpEstimate.Geometry.RotationalProfile.PoleData in
#check metricNabla0S_twice_rotationalAverage
open RicciFlowSharpEstimate.Geometry.RotationalProfile.PoleData in
#check roughLap0SField_rotationalAverage
open RicciFlowSharpEstimate.Geometry.RotationalProfile.PoleData in
#check ahlforsPart_rotationalAverage
open RicciFlowSharpEstimate.Geometry.RotationalProfile.PoleData in
#check ahlforsPart_metricNabla0S_rotationalAverage
open RicciFlowSharpEstimate.Geometry.RotationalProfile.PoleData in
#check oneFormDissipationPairingDensity_rotationalAverage
open RicciFlowSharpEstimate.Geometry.RotationalProfile.PoleData in
#check oneFormDissipationPairing_rotationalAverage
open RicciFlowSharpEstimate.Geometry.RotationalProfile.PoleData in
#check oneFormDissipationPairing_rotationalAverage_selfAdjoint
open RicciFlowSharpEstimate.Geometry.RotationalProfile.PoleData in
#check oneFormDissipationPairing_average_sub_average
open RicciFlowSharpEstimate.Geometry.RotationalProfile.PoleData in
#check oneFormDissipation_haar_split
open RicciFlowSharpEstimate.Geometry in
#print axisRotation
open RicciFlowSharpEstimate.Geometry in
#print circleSphereDiffeo
open RicciFlowSharpEstimate.Geometry in
#print angleRotation
open RicciFlowSharpEstimate.Geometry in
#print tensorIntervalIntegral
open RicciFlowSharpEstimate.Geometry in
#print rotationalAverage
open RicciFlowSharpEstimate.Analysis in
#check exists_contDiff_mul_eq_on_Icc
open RicciFlowSharpEstimate.Analysis in
#check exists_contDiff_comp_sq_of_even
open RicciFlowSharpEstimate.Analysis in
#check exists_contDiff_mul_comp_sq_of_odd
open RicciFlowSharpEstimate.Analysis in
#print planeRotate
open RicciFlowSharpEstimate.Analysis in
#print IsRotationCovectorPair
open RicciFlowSharpEstimate.Analysis in
#check exists_smooth_radial_tangential_coefficients
open RicciFlowSharpEstimate.Geometry in
#print stereoDenominator
open RicciFlowSharpEstimate.Geometry in
#check stereoDenominator_pos
open RicciFlowSharpEstimate.Geometry in
#print stereoAmbient
open RicciFlowSharpEstimate.Geometry in
#print stereoPoint
open RicciFlowSharpEstimate.Geometry in
#check stereoPoint_contMDiff
open RicciFlowSharpEstimate.Geometry in
#check stereoPoint_coe
open RicciFlowSharpEstimate.Geometry in
#check sphereHeight_stereoPoint
open RicciFlowSharpEstimate.Geometry in
#check stereoPoint_height_denominator
open RicciFlowSharpEstimate.Geometry in
#check stereoPoint_planeRotate
open RicciFlowSharpEstimate.Geometry in
#print stereoInversePoint
open RicciFlowSharpEstimate.Geometry in
#check stereoInversePoint_stereoPoint
open RicciFlowSharpEstimate.Geometry in
#check stereoPoint_inverse
open RicciFlowSharpEstimate.Geometry in
#check stereoPoint_dIncl_mfderiv
open RicciFlowSharpEstimate.Geometry in
#check stereoPoint_mfderiv_injective
open RicciFlowSharpEstimate.Geometry in
#check stereoPoint_mfderiv_surjective
open RicciFlowSharpEstimate.Geometry in
#check heightOneForm_stereoPoint_mfderiv
open RicciFlowSharpEstimate.Geometry in
#check sphereAzimuthalOneForm_stereoPoint_mfderiv
open RicciFlowSharpEstimate.Geometry in
#check exists_smooth_stereographic_coefficients
open RicciFlowSharpEstimate.Geometry in
#check exists_smooth_height_azimuthal_profiles
open RicciFlowSharpEstimate.Geometry.RotationalProfile.PoleData in
#check exists_smooth_zonal_decomposition_of_rotationInvariant
open RicciFlowSharpEstimate.Geometry.RotationalProfile.PoleData in
#check exists_smooth_zonal_decomposition_rotationalAverage
open RicciFlowSharpEstimate.Geometry.RotationalProfile.PoleData in
#check exists_haar_zonal_dissipation
open RicciFlowSharpEstimate.Geometry in
#print oneFormTrace
open RicciFlowSharpEstimate.Geometry in
#print oneFormCurl
open RicciFlowSharpEstimate.Geometry in
#check oneFormTrace_contMDiff
open RicciFlowSharpEstimate.Geometry in
#check oneFormCurl_contMDiff
open RicciFlowSharpEstimate.Geometry in
#check inner0S_eq_sum_orthonormal
open RicciFlowSharpEstimate.Geometry in
#check normSq0S_eq_sum_sq_orthonormal
open RicciFlowSharpEstimate.Geometry in
#check twoTensor_eq_ahlforsPart_add_trace_add_curl
open RicciFlowSharpEstimate.Geometry in
#check normSq0S_twoTensor_eq_ahlforsPart_trace_curl
open RicciFlowSharpEstimate.Geometry in
#check inner0S_ahlforsPart_self
open RicciFlowSharpEstimate.Geometry in
#print compactTensor0S
open RicciFlowSharpEstimate.Geometry in
#check compactTensor0S_toSection
open RicciFlowSharpEstimate.Geometry in
#check compactTensor0S_toFun
open RicciFlowSharpEstimate.Geometry in
#check metricNabla0S_apply_section
open RicciFlowSharpEstimate.Geometry in
#check metricNabla0S_apply_cons
open RicciFlowSharpEstimate.Geometry in
#check covariantDerivative_compactTensor0S
open RicciFlowSharpEstimate.Geometry in
#check covGrad_compactTensor0S_toSection
open RicciFlowSharpEstimate.Geometry in
#check covDivergence_compactTensor0S_toSection
open RicciFlowSharpEstimate.Geometry in
#check tensorInnerPointwise_toRS0_eq_inner0S
open RicciFlowSharpEstimate.Geometry in
#check integral_inner0S_metricNabla0S_eq_neg_covDiv0SField
open RicciFlowSharpEstimate.Geometry in
#check integral_inner0S_metricNabla0S_eq_neg_roughLap0SField
open RicciFlowSharpEstimate.Geometry in
#check integral_inner0S_roughLap0SField_left_eq_right
open RicciFlowSharpEstimate.Geometry in
#check metricNabla0S_commutator
open RicciFlowSharpEstimate.Geometry in
#check covDiv0SField_gradSlotSwap_commutator_of_finrank_eq_two
open RicciFlowSharpEstimate.Geometry in
#check oneForm_secondDerivative_skew_pairing
open RicciFlowSharpEstimate.Geometry in
#check differential1FormFun_metricTrace_apply
open RicciFlowSharpEstimate.Geometry in
#check differential1FormFun_inner0S_two_apply
open RicciFlowSharpEstimate.Geometry in
#check metricNabla0S_ahlforsPart_apply
open RicciFlowSharpEstimate.Geometry in
#check normSq0S_metricNabla0S_twoTensor_split
open RicciFlowSharpEstimate.Geometry in
#check integral_inner0S_gradSlotSwap
open RicciFlowSharpEstimate.Geometry in
#check oneFormDissipation_scalarization
open RicciFlowSharpEstimate.Geometry.RotationalProfile.PoleData in
#check oneFormDissipation_scalarization
open RicciFlowSharpEstimate.Geometry in
#check inner0S_diffeomorphTensorPullback
open RicciFlowSharpEstimate.Geometry in
#check metricTracePair0SAt_diffeomorphTensorPullback
open RicciFlowSharpEstimate.Geometry in
#check oneFormTrace_diffeomorphTensorPullback
open RicciFlowSharpEstimate.Geometry in
#check oneFormCurl_diffeomorphTensorPullback
open RicciFlowSharpEstimate.Geometry in
#check diffeomorphTensorPullback_roundSphereAreaForm_circleSphereDiffeo
open RicciFlowSharpEstimate.Geometry in
#check diffeomorphTensorPullback_roundSphereAreaForm_angleRotation
open RicciFlowSharpEstimate.Geometry in
#check rotationalScalarAverage
open RicciFlowSharpEstimate.Geometry in
#check rotationalScalarAverage_contMDiff
open RicciFlowSharpEstimate.Geometry in
#check rotationalScalarAverage_add
open RicciFlowSharpEstimate.Geometry in
#check rotationalScalarAverage_sub
open RicciFlowSharpEstimate.Geometry in
#check rotationalScalarAverage_smul
open RicciFlowSharpEstimate.Geometry in
#check rotationalScalarAverage_const
open RicciFlowSharpEstimate.Geometry in
#check rotationalScalarAverage_zero
open RicciFlowSharpEstimate.Geometry in
#check rotationalScalarAverage_one
open RicciFlowSharpEstimate.Geometry in
#check rotationalScalarAverage_angleRotation
open RicciFlowSharpEstimate.Geometry in
#check rotationalScalarAverage_comp_angleRotation
open RicciFlowSharpEstimate.Geometry in
#check rotationalScalarAverage_eq_self_of_invariant
open RicciFlowSharpEstimate.Geometry in
#check rotationalScalarAverage_idempotent
open RicciFlowSharpEstimate.Geometry in
#check rotationalScalarAverage_eq_at_pole
open RicciFlowSharpEstimate.Geometry in
#check rotationalScalarAverage_eq_zero_at_pole
open RicciFlowSharpEstimate.Geometry.RotationalProfile.PoleData in
#check diffeomorphTensorPullback_areaForm_circleSphereDiffeo
open RicciFlowSharpEstimate.Geometry.RotationalProfile.PoleData in
#check diffeomorphTensorPullback_areaForm_angleRotation
open RicciFlowSharpEstimate.Geometry.RotationalProfile.PoleData in
#check metricTracePair0SAt_rotationalAverage
open RicciFlowSharpEstimate.Geometry.RotationalProfile.PoleData in
#check inner0S_areaForm_rotationalAverage
open RicciFlowSharpEstimate.Geometry.RotationalProfile.PoleData in
#check oneFormTrace_angleRotation
open RicciFlowSharpEstimate.Geometry.RotationalProfile.PoleData in
#check oneFormCurl_angleRotation
open RicciFlowSharpEstimate.Geometry.RotationalProfile.PoleData in
#check oneFormTrace_rotationalAverage
open RicciFlowSharpEstimate.Geometry.RotationalProfile.PoleData in
#check oneFormCurl_rotationalAverage
open RicciFlowSharpEstimate.Geometry.RotationalProfile.PoleData in
#check rotationalScalarAverage_oneFormTrace_remainder
open RicciFlowSharpEstimate.Geometry.RotationalProfile.PoleData in
#check rotationalScalarAverage_oneFormCurl_remainder
open RicciFlowSharpEstimate.Geometry.RotationalProfile.PoleData in
#check oneFormTrace_remainder_eq_zero_at_pole
open RicciFlowSharpEstimate.Geometry.RotationalProfile.PoleData in
#check oneFormCurl_remainder_eq_zero_at_pole
open RicciFlowSharpEstimate.Analysis in
#check integral_sq_le_deriv_sq_of_periodic_mean_zero
open RicciFlowSharpEstimate.Analysis in
#check contDiff_deriv_fst
open RicciFlowSharpEstimate.Analysis in
#check contDiff_deriv_snd
open RicciFlowSharpEstimate.Analysis in
#check exists_pos_polar_endpoint_bounds
open RicciFlowSharpEstimate.Analysis in
#check intervalIntegrable_polar_square
open RicciFlowSharpEstimate.Analysis in
#check integral_polar_square_completion
open RicciFlowSharpEstimate.Analysis in
#check integral_weighted_sin_sq_le_polar_energy
open RicciFlowSharpEstimate.Analysis in
#check integrable_polar_energy_terms
open RicciFlowSharpEstimate.Analysis in
#check integral_polar_energy_ge_of_angular_mean_zero
open RicciFlowSharpEstimate.Analysis in
#check tendsto_polar_boundary_at_endpoints
open RicciFlowSharpEstimate.Geometry in
#check polarSpherePoint
open RicciFlowSharpEstimate.Geometry in
#check polarSpherePoint_coe
open RicciFlowSharpEstimate.Geometry in
#check sphereHeight_polarSpherePoint
open RicciFlowSharpEstimate.Geometry in
#check polarSpherePoint_contMDiff
open RicciFlowSharpEstimate.Geometry in
#check polarSpherePoint_periodic
open RicciFlowSharpEstimate.Geometry in
#check angleRotation_polarSpherePoint
open RicciFlowSharpEstimate.Geometry in
#check polarSpherePoint_zero
open RicciFlowSharpEstimate.Geometry in
#check polarSpherePoint_pi
open RicciFlowSharpEstimate.Geometry in
#check polarRadialVelocity
open RicciFlowSharpEstimate.Geometry in
#check polarAngularVelocity
open RicciFlowSharpEstimate.Geometry in
#check polarRadialVelocity_dIncl
open RicciFlowSharpEstimate.Geometry in
#check polarAngularVelocity_dIncl
open RicciFlowSharpEstimate.Geometry in
#check polarVelocities_linearIndependent
open RicciFlowSharpEstimate.Geometry in
#check polarVelocities_span
open RicciFlowSharpEstimate.Geometry in
#check polarTangentBasis
open RicciFlowSharpEstimate.Geometry in
#check polarTangentBasis_zero
open RicciFlowSharpEstimate.Geometry in
#check polarTangentBasis_one
open RicciFlowSharpEstimate.Geometry in
#check exists_polarSpherePoint_arccos
open RicciFlowSharpEstimate.Geometry in
#check contDiff_scalar_polar
open RicciFlowSharpEstimate.Geometry in
#check differential1FormFun_polarRadialVelocity
open RicciFlowSharpEstimate.Geometry in
#check differential1FormFun_polarAngularVelocity
open RicciFlowSharpEstimate.Geometry in
#check scalar_polar_endpoint_bounds
open RicciFlowSharpEstimate.Geometry in
#check scalar_polar_boundary_limits
open RicciFlowSharpEstimate.Geometry.RotationalProfile.PoleData in
#check metric_inner_polarRadialVelocity
open RicciFlowSharpEstimate.Geometry.RotationalProfile.PoleData in
#check metric_inner_polarAngularVelocity
open RicciFlowSharpEstimate.Geometry.RotationalProfile.PoleData in
#check metric_inner_polarRadialAngular
open RicciFlowSharpEstimate.Geometry.RotationalProfile.PoleData in
#check normSq0S_polar_covector
open RicciFlowSharpEstimate.Geometry.RotationalProfile.PoleData in
#check normSq0S_differential1FormFun_polar
open RicciFlowSharpEstimate.Geometry.RotationalProfile.PoleData in
#check integral_polar_metric
open RicciFlowSharpEstimate.Geometry.RotationalProfile.PoleData in
#check integral_scalar_energy_ge_of_rotationalScalarAverage_eq_zero
open RicciFlowSharpEstimate.Geometry in
#check integral_weight_mul_normSq_eq_zero_iff
open RicciFlowSharpEstimate.Geometry in
#check integral_weight_mul_sq_eq_zero_iff
open RicciFlowSharpEstimate.Geometry in
#check metricNabla0S_zero
open RicciFlowSharpEstimate.Geometry in
#check metricNabla0S_second_eq_zero_of_first_eq_zero
open RicciFlowSharpEstimate.Geometry in
#check roughLap0SField_eq_zero_of_metricNabla0S_eq_zero
open RicciFlowSharpEstimate.Geometry in
#check metricNabla0S_eq_zero_of_ahlfors_trace_curl_eq_zero
open RicciFlowSharpEstimate.Geometry in
#check oneFormDissipation_eq_curvature_energy_of_metricNabla0S_eq_zero
open RicciFlowSharpEstimate.Geometry.RotationalProfile.PoleData in
#check oneFormDissipation_remainder_lower_bound
open RicciFlowSharpEstimate.Geometry.RotationalProfile.PoleData in
#check oneFormDissipation_remainder_nonneg
open RicciFlowSharpEstimate.Geometry.RotationalProfile.PoleData in
#check oneFormDissipation_remainder_eq_zero_iff
open RicciFlowSharpEstimate.Geometry.RotationalProfile.PoleData in
#check oneFormDissipation_remainder_pos_iff
open RicciFlowSharpEstimate.Geometry.RotationalProfile.PoleData in
#check oneFormDissipation_rotationalAverage_le
open RicciFlowSharpEstimate.Geometry.RotationalProfile.PoleData in
#check oneFormDissipation_eq_rotationalAverage_iff
open RicciFlowSharpEstimate.Geometry.RotationalProfile.PoleData in
#check oneFormDissipation_eq_rotationalAverage_iff_invariant
open RicciFlowSharpEstimate.Geometry.RotationalProfile.PoleData in
#check exists_haar_zonal_lower_bound
open RicciFlowSharpEstimate.Analysis in
#check continuousOn_log_reciprocal
open RicciFlowSharpEstimate.Analysis in
#check hasDerivAt_log_reciprocal
open RicciFlowSharpEstimate.Analysis in
#check log_reciprocal_bounds
open RicciFlowSharpEstimate.Variational in
#check pairFunctional_eq_forward_intervalIntegral
open RicciFlowSharpEstimate.Variational in
#check pairFunctional_log_reciprocal
open RicciFlowSharpEstimate.Variational in
#check criticalCap
open RicciFlowSharpEstimate.Variational in
#check one_lt_criticalCap
open RicciFlowSharpEstimate.Variational in
#check capParameter_criticalCap
open RicciFlowSharpEstimate.Variational in
#check capParameter_criticalCap_cube
open RicciFlowSharpEstimate.Variational in
#check upperContact_capParameter_criticalCap
open RicciFlowSharpEstimate.Variational in
#check pairFunctional_obstacleLogProfile_criticalCap
open RicciFlowSharpEstimate.Variational in
#check pairFunctional_obstacleLogProfile_ge_one_third_iff
open RicciFlowSharpEstimate.Variational in
#check pairFunctional_gt_one_third_of_differentiableOn
open RicciFlowSharpEstimate.Geometry in
#check IsConformalKillingOneForm
open RicciFlowSharpEstimate.Geometry in
#check isConformalKillingOneForm_iff
open RicciFlowSharpEstimate.Geometry in
#check isConformalKillingOneForm_iff_normSq_eq_zero
open RicciFlowSharpEstimate.Geometry in
#check IsConformalKillingOneForm.add
open RicciFlowSharpEstimate.Geometry in
#check IsConformalKillingOneForm.smul
open RicciFlowSharpEstimate.Geometry in
#check IsConformalKillingOneForm.neg
open RicciFlowSharpEstimate.Geometry in
#check IsConformalKillingOneForm.sub
open RicciFlowSharpEstimate.Geometry in
#check IsConformalKillingOneForm.diffeomorphTensorPullback
open RicciFlowSharpEstimate.Geometry in
#check IsConformalKillingOneForm.diffeomorphTensorPullback_of_isometry
open RicciFlowSharpEstimate.Geometry.RotationalProfile.PoleData in
#check northLogProfile_continuousOn
open RicciFlowSharpEstimate.Geometry.RotationalProfile.PoleData in
#check southLogProfile_continuousOn
open RicciFlowSharpEstimate.Geometry.RotationalProfile.PoleData in
#check northLogProfile_hasDerivAt
open RicciFlowSharpEstimate.Geometry.RotationalProfile.PoleData in
#check southLogProfile_hasDerivAt
open RicciFlowSharpEstimate.Geometry.RotationalProfile.PoleData in
#check northLogProfile_differentiableOn
open RicciFlowSharpEstimate.Geometry.RotationalProfile.PoleData in
#check southLogProfile_differentiableOn
open RicciFlowSharpEstimate.Geometry.RotationalProfile.PoleData in
#check reciprocalCap_parameters
open RicciFlowSharpEstimate.Geometry.RotationalProfile.PoleData in
#check northLogProfile_admissible
open RicciFlowSharpEstimate.Geometry.RotationalProfile.PoleData in
#check southLogProfile_admissible
open RicciFlowSharpEstimate.Geometry.RotationalProfile.PoleData in
#check warp_reflected
open RicciFlowSharpEstimate.Geometry.RotationalProfile.PoleData in
#check pairFunctional_northLogProfile
open RicciFlowSharpEstimate.Geometry.RotationalProfile.PoleData in
#check pairFunctional_southLogProfile
open RicciFlowSharpEstimate.Geometry.RotationalProfile.PoleData in
#check integral_meridionalWeight_eq_pairFunctional_sum
open RicciFlowSharpEstimate.Geometry.RotationalProfile.PoleData in
#check meridionalDensity_const
open RicciFlowSharpEstimate.Geometry.RotationalProfile.PoleData in
#check meridionalAction_const
open RicciFlowSharpEstimate.Geometry.RotationalProfile.PoleData in
#check oneFormDissipation_constant_zonal
open RicciFlowSharpEstimate.Geometry.RotationalProfile.PoleData in
#check oneFormDissipation_constant_zonal_eq_pair_sum
open RicciFlowSharpEstimate.Geometry.RotationalProfile.PoleData in
#check isConformalKillingOneForm_meridional_const
open RicciFlowSharpEstimate.Geometry.RotationalProfile.PoleData in
#check azimuthalOneForm_ahlfors_normSq
open RicciFlowSharpEstimate.Geometry.RotationalProfile.PoleData in
#check isConformalKillingOneForm_azimuthal_const
open RicciFlowSharpEstimate.Geometry.RotationalProfile.PoleData in
#check isConformalKillingOneForm_constant_zonal_sum
open RicciFlowSharpEstimate.Geometry.RotationalProfile.PoleData in
#check meridional_probe_eq_const_of_isConformalKillingOneForm
open RicciFlowSharpEstimate.Geometry.RotationalProfile.PoleData in
#check azimuthal_probe_eq_const_of_isConformalKillingOneForm
open RicciFlowSharpEstimate.Geometry.RotationalProfile.PoleData in
#check exists_constant_zonal_decomposition_of_rotationInvariant_of_isConformalKillingOneForm
open RicciFlowSharpEstimate.Geometry.RotationalProfile.PoleData in
#check rotationInvariant_isConformalKillingOneForm_iff_exists_constant_zonal_decomposition
open RicciFlowSharpEstimate.Geometry.RotationalProfile.PoleData in
#check isConformalKillingOneForm_rotationalAverage
open RicciFlowSharpEstimate.Geometry.RotationalProfile.PoleData in
#check exists_constant_zonal_decomposition_rotationalAverage_of_isConformalKillingOneForm
open RicciFlowSharpEstimate.Geometry.RotationalProfile.PoleData in
#check meridional_one_nonzero_conformalKilling
open RicciFlowSharpEstimate.Geometry.RotationalProfile.PoleData in
#check curvature_bounds_iff_profile_bounds
open RicciFlowSharpEstimate.Geometry.RotationalProfile.PoleData in
#check constant_zonal_coefficient_pos
open RicciFlowSharpEstimate.Geometry.RotationalProfile.PoleData in
#check oneFormDissipation_nonneg_of_conformalKilling_profile_bounds
open RicciFlowSharpEstimate.Geometry.RotationalProfile.PoleData in
#check oneFormDissipation_eq_zero_iff_of_conformalKilling_profile_bounds
open RicciFlowSharpEstimate.Geometry.RotationalProfile.PoleData in
#check oneFormDissipation_meridional_one_pos_of_profile_bounds
open RicciFlowSharpEstimate.Geometry.RotationalProfile.PoleData in
#check oneFormDissipation_nonneg_of_conformalKilling_curvature_bounds
open RicciFlowSharpEstimate.Geometry.RotationalProfile.PoleData in
#check oneFormDissipation_eq_zero_iff_of_conformalKilling_curvature_bounds
open RicciFlowSharpEstimate.Analysis in
#check exists_contDiff_even_sequence_Icc
open RicciFlowSharpEstimate.Variational in
#check evenReciprocalProfile
open RicciFlowSharpEstimate.Variational in
#check evenReciprocalProfile_eq
open RicciFlowSharpEstimate.Variational in
#check even_evenReciprocalProfile
open RicciFlowSharpEstimate.Variational in
#check uniformContinuous_evenReciprocalProfile
open RicciFlowSharpEstimate.Variational in
#check evenReciprocalProfile_bounds
open RicciFlowSharpEstimate.Geometry.RotationalProfile in
#check balance_eq_zero_of_even
open RicciFlowSharpEstimate.Geometry.RotationalProfile in
#check warp_reflected_of_balance
open RicciFlowSharpEstimate.Geometry.RotationalProfile in
#check integral_warp_div_eq_pairFunctional_sum
open RicciFlowSharpEstimate.Geometry.RotationalProfile in
#check integral_warp_div_evenReciprocalProfile
open RicciFlowSharpEstimate.Geometry.RotationalProfile in
#check constantProbeIntegral_evenReciprocalProfile
open RicciFlowSharpEstimate.Geometry.RotationalProfile in
#check continuousOn_warp
open RicciFlowSharpEstimate.Geometry.RotationalProfile in
#check intervalIntegrable_warp_div
open RicciFlowSharpEstimate.Geometry.RotationalProfile in
#check tendsto_integral_warp_div_of_tendstoUniformlyOn
open RicciFlowSharpEstimate.Geometry.RotationalProfile in
#check abs_integral_warp_div_sub_le
open RicciFlowSharpEstimate.Geometry.RotationalProfile.PoleData in
#check hemisphereDeficit_logProfile_eq_normalized_constant_zonal
open RicciFlowSharpEstimate.Geometry.RotationalProfile.PoleData in
#check oneFormDissipation_constant_zonal_controls_evenExtension
open RicciFlowSharpEstimate.Geometry.RotationalProfile.PoleData in
#check oneFormDissipation_constant_zonal_controls_reflection
open RicciFlowSharpEstimate.Geometry.RotationalProfile.PoleData in
#check oneFormDissipation_constant_zonal_controls_symmetrization
open RicciFlowSharpEstimate.Geometry.RotationalProfile.PoleData in
#check constant_zonal_zero_of_sq_sum_eq_zero
open RicciFlowSharpEstimate.Geometry.RotationalProfile in
#check exists_smooth_even_reciprocal_profiles
open RicciFlowSharpEstimate.Geometry.RotationalProfile.PoleData in
#check oneFormDissipation_meridional_one_eq_integral
open RicciFlowSharpEstimate.Geometry.RotationalProfile in
#check exists_poleData_unit_probe_recovery
open RicciFlowSharpEstimate.Geometry.RotationalProfile in
#check exists_negative_unit_meridional_of_criticalCap_lt
open RicciFlowSharpEstimate.Geometry.RotationalProfile in
#check exists_critical_unit_probe_recovery
open RicciFlowSharpEstimate.Geometry in
#check diffeomorphTensorPullback_zero
open RicciFlowSharpEstimate.Geometry in
#check diffeomorphTensorPullback_neg
open RicciFlowSharpEstimate.Geometry in
#check diffeomorphTensorPullback_sub
open RicciFlowSharpEstimate.Geometry in
#check diffeomorphTensorPullback_injective
open RicciFlowSharpEstimate.Geometry in
#check diffeomorphTensorPullback_eq_zero_iff
open RicciFlowSharpEstimate.Geometry in
#check pullbackMetric_symm_apply
open RicciFlowSharpEstimate.Geometry in
#check pullbackMetric_apply_symm
open RicciFlowSharpEstimate.Geometry in
#check conjugatedRotationalAverage
open RicciFlowSharpEstimate.Geometry in
#check conjugatedRotationalAverage_refl
open RicciFlowSharpEstimate.Geometry in
#check conjugatedRotationalAverage_diffeomorphTensorPullback
open RicciFlowSharpEstimate.Geometry in
#check diffeomorphTensorPullback_symm_conjugatedRotationalAverage
open RicciFlowSharpEstimate.Geometry in
#check conjugatedRotationalAverage_zero
open RicciFlowSharpEstimate.Geometry in
#check conjugatedRotationalAverage_add
open RicciFlowSharpEstimate.Geometry in
#check conjugatedRotationalAverage_smul
open RicciFlowSharpEstimate.Geometry in
#check conjugatedRotationalAverage_sub
open RicciFlowSharpEstimate.Geometry in
#check conjugatedRotationalAverage_idempotent
open RicciFlowSharpEstimate.Geometry in
#check conjugatedRotationalAverage_sub_average
open RicciFlowSharpEstimate.Geometry in
#check conjugatedRotationalAverage_eq_self_iff_pullback
open RicciFlowSharpEstimate.Geometry in
#check conjugatedCircleSphereDiffeo
open RicciFlowSharpEstimate.Geometry in
#check conjugatedCircleSphereDiffeo_apply
open RicciFlowSharpEstimate.Geometry in
#check conjugatedCircleSphereDiffeo_one
open RicciFlowSharpEstimate.Geometry in
#check conjugatedCircleSphereDiffeo_mul
open RicciFlowSharpEstimate.Geometry in
#check conjugatedCircleSphereAction
open RicciFlowSharpEstimate.Geometry in
#check conjugatedCircleSphereDiffeo_inv
open RicciFlowSharpEstimate.Geometry in
#check conjugatedAngleRotation
open RicciFlowSharpEstimate.Geometry in
#check conjugatedAngleRotation_apply
open RicciFlowSharpEstimate.Geometry in
#check conjugatedAngleRotation_zero
open RicciFlowSharpEstimate.Geometry in
#check conjugatedAngleRotation_add
open RicciFlowSharpEstimate.Geometry in
#check conjugatedAngleRotation_neg
open RicciFlowSharpEstimate.Geometry in
#check conjugatedAngleRotation_periodic
open RicciFlowSharpEstimate.Geometry in
#check conjugatedAngleRotation_contMDiff
open RicciFlowSharpEstimate.Geometry.RotationalProfile.PoleData in
#check pullbackMetric_conjugatedCircleSphereDiffeo
open RicciFlowSharpEstimate.Geometry.RotationalProfile.PoleData in
#check metric_inner_conjugatedCircleSphereDiffeo
open RicciFlowSharpEstimate.Geometry.RotationalProfile.PoleData in
#check pullbackMetric_conjugatedAngleRotation
open RicciFlowSharpEstimate.Geometry in
#check diffeomorphTensorPullback_conjugatedCircleSphereDiffeo
open RicciFlowSharpEstimate.Geometry in
#check contMDiff_diffeomorphTensorPullback_conjugatedAngleRotation
open RicciFlowSharpEstimate.Geometry in
#check intervalIntegrable_conjugatedAngleRotation_apply
open RicciFlowSharpEstimate.Geometry in
#check conjugatedRotationalAverage_eval
open RicciFlowSharpEstimate.Geometry in
#check conjugatedRotationalAverage_apply
open RicciFlowSharpEstimate.Geometry in
#check diffeomorphTensorPullback_conjugatedCircle_conjugatedRotationalAverage
open RicciFlowSharpEstimate.Geometry in
#check conjugatedRotationalAverage_eq_self_iff
open RicciFlowSharpEstimate.Geometry.RotationalProfile.PoleData in
#check metricNabla0S_conjugatedRotationalAverage
open RicciFlowSharpEstimate.Geometry.RotationalProfile.PoleData in
#check metricNabla0S_twice_conjugatedRotationalAverage
open RicciFlowSharpEstimate.Geometry.RotationalProfile.PoleData in
#check roughLap0SField_conjugatedRotationalAverage
open RicciFlowSharpEstimate.Geometry.RotationalProfile.PoleData in
#check ahlforsPart_conjugatedRotationalAverage
open RicciFlowSharpEstimate.Geometry.RotationalProfile.PoleData in
#check ahlforsPart_metricNabla0S_conjugatedRotationalAverage
open RicciFlowSharpEstimate.Geometry.RotationalProfile.PoleData in
#check oneFormDissipationPairing_conjugatedRotationalAverage_selfAdjoint
open RicciFlowSharpEstimate.Geometry.RotationalProfile.PoleData in
#check oneFormDissipationPairing_conjugated_average_sub_average
open RicciFlowSharpEstimate.Geometry.RotationalProfile.PoleData in
#check oneFormDissipation_conjugated_split
open RicciFlowSharpEstimate.Geometry.RotationalProfile.PoleData in
#check oneFormDissipation_conjugated_remainder_nonneg
open RicciFlowSharpEstimate.Geometry.RotationalProfile.PoleData in
#check oneFormDissipation_conjugated_remainder_eq_zero_iff
open RicciFlowSharpEstimate.Geometry in
#check IsRepresentedRotationalMetric
open RicciFlowSharpEstimate.Geometry.RotationalProfile.PoleData in
#check isRepresentedRotationalMetric
open RicciFlowSharpEstimate.Geometry.RotationalProfile.PoleData in
#check isRepresentedRotationalMetric_pullback
open RicciFlowSharpEstimate.Geometry.RotationalProfile.PoleData in
#check metricScalarAt_pullback
open RicciFlowSharpEstimate.Geometry.RotationalProfile.PoleData in
#check curvature_bounds_pullback_iff
open RicciFlowSharpEstimate.Geometry.RotationalProfile.PoleData in
#check riemannianVolume_measurePreserving_pullback
open RicciFlowSharpEstimate.Geometry.RotationalProfile.PoleData in
#check riemannianVolume_map_pullback
open RicciFlowSharpEstimate.Geometry.RotationalProfile.PoleData in
#check areaForm_pullback_apply
open RicciFlowSharpEstimate.Geometry.RotationalProfile.PoleData in
#check areaForm_pullback_normSq
open RicciFlowSharpEstimate.Geometry.RotationalProfile.PoleData in
#check metricNabla0S_areaForm_pullback
open RicciFlowSharpEstimate.Geometry.RotationalProfile.PoleData in
#check oneFormCurl_areaForm_pullback
open RicciFlowSharpEstimate.Geometry.RotationalProfile.PoleData in
#check oneFormDissipation_nonneg_pullback_of_conformalKilling_curvature_bounds
open RicciFlowSharpEstimate.Geometry.RotationalProfile.PoleData in
#check oneFormDissipation_eq_zero_iff_pullback_of_conformalKilling_curvature_bounds
open RicciFlowSharpEstimate.Geometry.IsRepresentedRotationalMetric in
#check pullback
open RicciFlowSharpEstimate.Geometry.IsRepresentedRotationalMetric in
#check oneFormDissipation_nonneg_of_conformalKilling_curvature_bounds
open RicciFlowSharpEstimate.Geometry.IsRepresentedRotationalMetric in
#check oneFormDissipation_eq_zero_iff_of_conformalKilling_curvature_bounds
open RicciFlowSharpEstimate.Geometry.RotationalProfile.PoleData in
#check oneFormDissipation_pullback_zonal
open RicciFlowSharpEstimate.Geometry.RotationalProfile.PoleData in
#check exists_smooth_zonal_decomposition_conjugatedRotationalAverage
open RicciFlowSharpEstimate.Geometry.RotationalProfile.PoleData in
#check exists_conjugated_haar_zonal_dissipation
open RicciFlowSharpEstimate.Geometry.RotationalProfile.PoleData in
#check oneFormDissipation_conjugatedRotationalAverage_le
open RicciFlowSharpEstimate.Geometry.RotationalProfile.PoleData in
#check oneFormDissipation_eq_conjugatedRotationalAverage_iff
open RicciFlowSharpEstimate.Geometry.RotationalProfile.PoleData in
#check oneFormDissipation_eq_conjugatedRotationalAverage_iff_invariant
open RicciFlowSharpEstimate.Geometry.RotationalProfile.PoleData in
#check exists_conjugated_haar_zonal_lower_bound
open RicciFlowSharpEstimate.Geometry.RotationalProfile.PoleData in
#check isConformalKillingOneForm_conjugatedRotationalAverage
open RicciFlowSharpEstimate.Geometry.RotationalProfile.PoleData in
#check exists_conjugated_constant_zonal_of_conformalKilling
open RicciFlowSharpEstimate.Geometry.IsRepresentedRotationalMetric in
#check exists_haar_representation
open RicciFlowSharpEstimate.Geometry.IsRepresentedRotationalMetric in
#check exists_haar_zonal_decomposition
open RicciFlowSharpEstimate.Geometry.RotationalProfile.PoleData in
#check hemisphereDeficit_logProfile_eq_normalized_pullback_constant_zonal
open RicciFlowSharpEstimate.Geometry.RotationalProfile.PoleData in
#check oneFormDissipation_pullback_constant_zonal_controls_evenExtension
open RicciFlowSharpEstimate.Geometry.RotationalProfile.PoleData in
#check oneFormDissipation_pullback_constant_zonal_controls_reflection
open RicciFlowSharpEstimate.Geometry.RotationalProfile.PoleData in
#check oneFormDissipation_pullback_constant_zonal_controls_symmetrization
open RicciFlowSharpEstimate.Geometry.RotationalProfile.PoleData in
#check pullback_constant_zonal_zero_of_sq_sum_eq_zero
open RicciFlowSharpEstimate.Geometry.IsRepresentedRotationalMetric in
#check exists_stability_representation
open RicciFlowSharpEstimate.Geometry in
#check conformalKillingSafeCaps
open RicciFlowSharpEstimate.Geometry in
#check conformalKillingSafeCaps_eq
open RicciFlowSharpEstimate.Geometry in
#check conformalKillingSafeCaps_nonempty
open RicciFlowSharpEstimate.Geometry in
#check conformalKillingSafeCaps_bddAbove
open RicciFlowSharpEstimate.Geometry in
#check conformalKillingThreshold
open RicciFlowSharpEstimate.Geometry in
#check conformalKillingThreshold_eq_criticalCap
open RicciFlowSharpEstimate.Geometry in
#check conformalKillingThreshold_closedForm
open RicciFlowSharpEstimate.Geometry.IsRepresentedRotationalMetric in
#check oneFormDissipation_pos_of_conformalKilling
open RicciFlowSharpEstimate.Geometry in
#check exists_represented_negative_unit_meridional
open RicciFlowSharpEstimate.Geometry in
#check exists_represented_critical_unit_probe_recovery
open RicciFlowSharpEstimate.Geometry.AreaProfile in
#check heightCoordinate
open RicciFlowSharpEstimate.Geometry.AreaProfile in
#check warp
open RicciFlowSharpEstimate.Geometry.AreaProfile in
#check warpSlope
open RicciFlowSharpEstimate.Geometry.AreaProfile in
#check meridionalActionDensity
open RicciFlowSharpEstimate.Geometry.AreaProfile in
#check meridionalAction
open RicciFlowSharpEstimate.Geometry.AreaProfile in
#check heightCoordinate_hasDerivAt
open RicciFlowSharpEstimate.Geometry.AreaProfile in
#check deriv_heightCoordinate
open RicciFlowSharpEstimate.Geometry.AreaProfile in
#check heightCoordinate_contDiff
open RicciFlowSharpEstimate.Geometry.AreaProfile in
#check heightCoordinate_zero
open RicciFlowSharpEstimate.Geometry.AreaProfile in
#check heightCoordinate_one
open RicciFlowSharpEstimate.Geometry.AreaProfile in
#check warp_zero
open RicciFlowSharpEstimate.Geometry.AreaProfile in
#check warpSlope_zero
open RicciFlowSharpEstimate.Geometry.AreaProfile in
#check warpSlope_eq_neg_two_height
open RicciFlowSharpEstimate.Analysis.SecondPrimitive in
#check integral_kernel_eq
open RicciFlowSharpEstimate.Analysis.SecondPrimitive in
#check integral_kernel_hasDerivAt
open RicciFlowSharpEstimate.Analysis.SecondPrimitive in
#check integral_contDiff
open RicciFlowSharpEstimate.Analysis.SecondPrimitive in
#check integral_kernel_contDiff
open RicciFlowSharpEstimate.Geometry.AreaProfile in
#check warp_hasDerivAt
open RicciFlowSharpEstimate.Geometry.AreaProfile in
#check warpSlope_hasDerivAt
open RicciFlowSharpEstimate.Geometry.AreaProfile in
#check deriv_warp
open RicciFlowSharpEstimate.Geometry.AreaProfile in
#check deriv_warpSlope
open RicciFlowSharpEstimate.Geometry.AreaProfile in
#check deriv_deriv_warp
open RicciFlowSharpEstimate.Geometry.AreaProfile in
#check warp_contDiff
open RicciFlowSharpEstimate.Geometry.AreaProfile in
#check warpSlope_contDiff
open RicciFlowSharpEstimate.Geometry.AreaProfile in
#check warp_one
open RicciFlowSharpEstimate.Geometry.AreaProfile in
#check warpSlope_one
open RicciFlowSharpEstimate.Geometry.AreaProfile in
#check heightCoordinate_continuous
open RicciFlowSharpEstimate.Geometry.AreaProfile in
#check warp_continuous
open RicciFlowSharpEstimate.Geometry.AreaProfile in
#check warpSlope_continuous
open RicciFlowSharpEstimate.Geometry.AreaProfile in
#check heightCoordinate_strictMonoOn
open RicciFlowSharpEstimate.Geometry.AreaProfile in
#check heightCoordinate_mapsTo
open RicciFlowSharpEstimate.Geometry.AreaProfile in
#check heightCoordinate_bijOn
open RicciFlowSharpEstimate.Geometry.AreaProfile in
#check warp_strictConcaveOn
open RicciFlowSharpEstimate.Geometry.AreaProfile in
#check warp_pos_of_moments
open RicciFlowSharpEstimate.Geometry.AreaProfile in
#check integral_heightCoordinate
open RicciFlowSharpEstimate.Analysis in
#check exists_contDiff_extension_Icc
open RicciFlowSharpEstimate.Analysis in
#check exists_contDiff_inverse_on_Icc
open RicciFlowSharpEstimate.Geometry.AreaProfile in
#check meridionalAction_integrand_continuous
open RicciFlowSharpEstimate.Geometry.AreaProfile in
#check meridionalAction_integrand_intervalIntegrable
open RicciFlowSharpEstimate.Geometry.AreaProfile in
#check warp_two
open RicciFlowSharpEstimate.Geometry.AreaProfile in
#check warpSlope_two
open RicciFlowSharpEstimate.Geometry.AreaProfile in
#check meridionalAction_two_one
open RicciFlowSharpEstimate.Geometry.AreaProfile in
#check profile_warp_heightCoordinate
open RicciFlowSharpEstimate.Geometry.AreaProfile in
#check deriv_profile_heightCoordinate
open RicciFlowSharpEstimate.Geometry.AreaProfile in
#check deriv_probe_heightCoordinate
open RicciFlowSharpEstimate.Geometry.AreaProfile in
#check deriv_deriv_probe_heightCoordinate
open RicciFlowSharpEstimate.Geometry.AreaProfile in
#check meridionalWeight_heightCoordinate
open RicciFlowSharpEstimate.Geometry.AreaProfile in
#check deriv_meridionalWeight_heightCoordinate
open RicciFlowSharpEstimate.Geometry.AreaProfile in
#check meridionalOperator_heightCoordinate
open RicciFlowSharpEstimate.Geometry.AreaProfile in
#check meridionalDensity_heightCoordinate_mul_curvature
open RicciFlowSharpEstimate.Geometry.AreaProfile in
#check oneFormDissipation_eq_areaAction_of_profile_probe
open RicciFlowSharpEstimate.Geometry.AreaProfile in
#check exists_smooth_geometric_realization
open RicciFlowSharpEstimate.Geometry.AreaProfile in
#check round_unit_probe_normalization
open RicciFlowSharpEstimate.Variational in
#check monotone_obstacleExponential
open RicciFlowSharpEstimate.Variational in
#check monotone_obstacleLogProfile
open RicciFlowSharpEstimate.Variational in
#check evenReciprocalProfile_eq_low
open RicciFlowSharpEstimate.Variational in
#check evenReciprocalProfile_eq_high
open RicciFlowSharpEstimate.Variational in
#check evenReciprocalProfile_at_zero
open RicciFlowSharpEstimate.Variational in
#check evenReciprocalProfile_at_one
open RicciFlowSharpEstimate.Variational in
#check evenReciprocalProfile_one
open RicciFlowSharpEstimate.Variational in
#check antitoneOn_evenReciprocalProfile
open RicciFlowSharpEstimate.Variational in
#check monotoneOn_evenReciprocalProfile
open RicciFlowSharpEstimate.Variational in
#check evenReciprocalProfile_central_plateau
open RicciFlowSharpEstimate.Variational in
#check evenReciprocalProfile_strict_average_bounds
open RicciFlowSharpEstimate.Analysis in
#print clampedIntervalInverse
open RicciFlowSharpEstimate.Analysis in
#check clampedIntervalInverse_mem
open RicciFlowSharpEstimate.Analysis in
#check clampedIntervalInverse_apply
open RicciFlowSharpEstimate.Analysis in
#check apply_clampedIntervalInverse
open RicciFlowSharpEstimate.Analysis in
#check clampedIntervalInverse_continuous
open RicciFlowSharpEstimate.Geometry.ReciprocalArea in
#print length
open RicciFlowSharpEstimate.Geometry.ReciprocalArea in
#print coordinate
open RicciFlowSharpEstimate.Geometry.ReciprocalArea in
#print inverse
open RicciFlowSharpEstimate.Geometry.ReciprocalArea in
#print curvature
open RicciFlowSharpEstimate.Geometry.ReciprocalArea in
#check length_pos
open RicciFlowSharpEstimate.Geometry.ReciprocalArea in
#check coordinate_hasDerivAt
open RicciFlowSharpEstimate.Geometry.ReciprocalArea in
#check coordinate_continuous
open RicciFlowSharpEstimate.Geometry.ReciprocalArea in
#check coordinate_neg_one
open RicciFlowSharpEstimate.Geometry.ReciprocalArea in
#check coordinate_one
open RicciFlowSharpEstimate.Geometry.ReciprocalArea in
#check coordinate_strictMonoOn
open RicciFlowSharpEstimate.Geometry.ReciprocalArea in
#check coordinate_mapsTo
open RicciFlowSharpEstimate.Geometry.ReciprocalArea in
#check coordinate_bijOn
open RicciFlowSharpEstimate.Geometry.ReciprocalArea in
#check inverse_mem
open RicciFlowSharpEstimate.Geometry.ReciprocalArea in
#check inverse_continuous
open RicciFlowSharpEstimate.Geometry.ReciprocalArea in
#check inverse_coordinate
open RicciFlowSharpEstimate.Geometry.ReciprocalArea in
#check coordinate_inverse
open RicciFlowSharpEstimate.Geometry.ReciprocalArea in
#check inverse_zero
open RicciFlowSharpEstimate.Geometry.ReciprocalArea in
#check inverse_one
open RicciFlowSharpEstimate.Geometry.ReciprocalArea in
#check inverse_strictMonoOn
open RicciFlowSharpEstimate.Geometry.ReciprocalArea in
#check curvature_continuous
open RicciFlowSharpEstimate.Geometry.ReciprocalArea in
#check curvature_pos
open RicciFlowSharpEstimate.Geometry.ReciprocalArea in
#check curvature_coordinate
open RicciFlowSharpEstimate.Geometry.ReciprocalArea in
#check integral_comp_coordinate
open RicciFlowSharpEstimate.Geometry.ReciprocalArea in
#check warpSlope_coordinate
open RicciFlowSharpEstimate.Geometry.ReciprocalArea in
#check heightCoordinate_coordinate
open RicciFlowSharpEstimate.Geometry.ReciprocalArea in
#check integral_curvature
open RicciFlowSharpEstimate.Geometry.ReciprocalArea in
#check warp_coordinate
open RicciFlowSharpEstimate.Geometry.ReciprocalArea in
#check integral_mul_curvature
open RicciFlowSharpEstimate.Geometry.ReciprocalArea in
#check curvature_mem_Icc
open RicciFlowSharpEstimate.Geometry.ReciprocalArea in
#check meridionalAction_one_eq_integral
open RicciFlowSharpEstimate.Geometry.ReciprocalArea in
#check meridionalAction_one
open RicciFlowSharpEstimate.Geometry.ReciprocalArea in
#check coordinate_reflection
open RicciFlowSharpEstimate.Geometry.ReciprocalArea in
#check coordinate_zero
open RicciFlowSharpEstimate.Geometry.ReciprocalArea in
#check inverse_half
open RicciFlowSharpEstimate.Geometry.ReciprocalArea in
#check inverse_reflection
open RicciFlowSharpEstimate.Geometry.ReciprocalArea in
#check curvature_reflection
open RicciFlowSharpEstimate.Geometry.ReciprocalArea in
#check curvature_antitoneOn_left
open RicciFlowSharpEstimate.Geometry.ReciprocalArea in
#check curvature_monotoneOn_right
open RicciFlowSharpEstimate.Analysis in
#check exists_contDiff_nonneg_tsupport_subset_integral_mul_pos
open RicciFlowSharpEstimate.Geometry.AreaProfile in
#print constantProbeVariationDensity
open RicciFlowSharpEstimate.Geometry.AreaProfile in
#check meridionalActionDensity_one_sub_mul
open RicciFlowSharpEstimate.Geometry.AreaProfile in
#print plateauFlux
open RicciFlowSharpEstimate.Geometry.AreaProfile in
#check plateauFlux_hasDerivAt
open RicciFlowSharpEstimate.Geometry.AreaProfile in
#check plateauFlux_endpoints
open RicciFlowSharpEstimate.Geometry.AreaProfile in
#check constantProbeVariation_integral_eq_plateau_pairing
open RicciFlowSharpEstimate.Geometry.AreaProfile in
#check meridionalAction_one_sub_mul_of_plateau
open RicciFlowSharpEstimate.Geometry.AreaProfile in
#check exists_smooth_plateau_probe
open RicciFlowSharpEstimate.Geometry.AreaProfile in
#check exists_smooth_probe_action_neg_of_constant_curvature_plateau
open RicciFlowSharpEstimate.Geometry.CriticalAreaProfile in
#print reciprocal
open RicciFlowSharpEstimate.Geometry.CriticalAreaProfile in
#print length
open RicciFlowSharpEstimate.Geometry.CriticalAreaProfile in
#print coordinate
open RicciFlowSharpEstimate.Geometry.CriticalAreaProfile in
#print inverse
open RicciFlowSharpEstimate.Geometry.CriticalAreaProfile in
#print curvature
open RicciFlowSharpEstimate.Geometry.CriticalAreaProfile in
#check length_pos
open RicciFlowSharpEstimate.Geometry.CriticalAreaProfile in
#check strict_average_bounds
open RicciFlowSharpEstimate.Geometry.CriticalAreaProfile in
#check coordinate_hasDerivAt
open RicciFlowSharpEstimate.Geometry.CriticalAreaProfile in
#check coordinate_neg_one
open RicciFlowSharpEstimate.Geometry.CriticalAreaProfile in
#check coordinate_one
open RicciFlowSharpEstimate.Geometry.CriticalAreaProfile in
#check inverse_zero
open RicciFlowSharpEstimate.Geometry.CriticalAreaProfile in
#check inverse_one
open RicciFlowSharpEstimate.Geometry.CriticalAreaProfile in
#check coordinate_bijOn
open RicciFlowSharpEstimate.Geometry.CriticalAreaProfile in
#check inverse_mem
open RicciFlowSharpEstimate.Geometry.CriticalAreaProfile in
#check inverse_coordinate
open RicciFlowSharpEstimate.Geometry.CriticalAreaProfile in
#check coordinate_inverse
open RicciFlowSharpEstimate.Geometry.CriticalAreaProfile in
#check inverse_continuous
open RicciFlowSharpEstimate.Geometry.CriticalAreaProfile in
#check curvature_continuous
open RicciFlowSharpEstimate.Geometry.CriticalAreaProfile in
#check curvature_pos
open RicciFlowSharpEstimate.Geometry.CriticalAreaProfile in
#check curvature_coordinate
open RicciFlowSharpEstimate.Geometry.CriticalAreaProfile in
#check curvature_bounds
open RicciFlowSharpEstimate.Geometry.CriticalAreaProfile in
#check curvature_moments
open RicciFlowSharpEstimate.Geometry.CriticalAreaProfile in
#check warp_coordinate
open RicciFlowSharpEstimate.Geometry.CriticalAreaProfile in
#check warpSlope_coordinate
open RicciFlowSharpEstimate.Geometry.CriticalAreaProfile in
#check heightCoordinate_eq_inverse
open RicciFlowSharpEstimate.Geometry.CriticalAreaProfile in
#check coordinate_reflection
open RicciFlowSharpEstimate.Geometry.CriticalAreaProfile in
#check coordinate_zero
open RicciFlowSharpEstimate.Geometry.CriticalAreaProfile in
#check inverse_half
open RicciFlowSharpEstimate.Geometry.CriticalAreaProfile in
#check curvature_reflection
open RicciFlowSharpEstimate.Geometry.CriticalAreaProfile in
#check curvature_antitoneOn_left
open RicciFlowSharpEstimate.Geometry.CriticalAreaProfile in
#check curvature_monotoneOn_right
open RicciFlowSharpEstimate.Geometry.CriticalAreaProfile in
#check warp_pos
open RicciFlowSharpEstimate.Geometry.CriticalAreaProfile in
#check exists_positive_constant_plateau
open RicciFlowSharpEstimate.Geometry.CriticalAreaProfile in
#check meridionalAction_one_eq_zero
open RicciFlowSharpEstimate.Geometry.CriticalAreaProfile in
#check exists_smooth_negative_probe_data
open RicciFlowSharpEstimate.Geometry.CriticalAreaProfile in
#check exists_smooth_negative_probe
open RicciFlowSharpEstimate.Analysis in
#print bernsteinPolynomialOfCoefficients
open RicciFlowSharpEstimate.Analysis in
#check eval_bernsteinPolynomialOfCoefficients
open RicciFlowSharpEstimate.Analysis in
#check eval_bernsteinPolynomialOfCoefficients_unitInterval
open RicciFlowSharpEstimate.Analysis in
#check derivative_bernsteinPolynomialOfCoefficients_succ
open RicciFlowSharpEstimate.Analysis in
#print sampledBernsteinPolynomial
open RicciFlowSharpEstimate.Analysis in
#check eval_sampledBernsteinPolynomial
open RicciFlowSharpEstimate.Analysis in
#check bernsteinPolynomialOfCoefficients_mem_Icc
open RicciFlowSharpEstimate.Analysis in
#check monotoneOn_sampledBernsteinPolynomial
open RicciFlowSharpEstimate.Analysis in
#check tendsto_sampledBernsteinPolynomial
open RicciFlowSharpEstimate.Analysis in
#print squaredMidpointRadius
open RicciFlowSharpEstimate.Analysis in
#check squaredMidpointRadius_mem_Icc
open RicciFlowSharpEstimate.Analysis in
#print upperRadialProfile
open RicciFlowSharpEstimate.Analysis in
#check upperRadialArgument_mem_Icc
open RicciFlowSharpEstimate.Analysis in
#check monotoneOn_upperRadialProfile
open RicciFlowSharpEstimate.Analysis in
#print symmetricBernsteinApproximation
open RicciFlowSharpEstimate.Analysis in
#print symmetricBernsteinPolynomial
open RicciFlowSharpEstimate.Analysis in
#check eval_symmetricBernsteinPolynomial
open RicciFlowSharpEstimate.Analysis in
#check contDiff_symmetricBernsteinApproximation
open RicciFlowSharpEstimate.Analysis in
#check symmetric_symmetricBernsteinApproximation
open RicciFlowSharpEstimate.Analysis in
#check monotoneOn_symmetricBernsteinApproximation
open RicciFlowSharpEstimate.Analysis in
#check antitoneOn_symmetricBernsteinApproximation
open RicciFlowSharpEstimate.Analysis in
#check symmetricBernsteinApproximation_mem_Icc
open RicciFlowSharpEstimate.Analysis in
#check upperRadialProfile_squaredMidpointRadius_eq
open RicciFlowSharpEstimate.Analysis.L1Subsequence in
#check exists_strictMono_ae_tendsto_of_integral_norm_tendsto_zero
open RicciFlowSharpEstimate.Analysis.SymmetricMomentRecovery in
#check firstMoment_eq_half_integral_of_reflection
open RicciFlowSharpEstimate.Analysis.SymmetricMomentRecovery in
#check exists_smooth_exactMoments_mem_box_l1_ae
open RicciFlowSharpEstimate.Geometry.AreaProfile in
#check abs_warp_sub_le_integral_abs
open RicciFlowSharpEstimate.Geometry.AreaProfile in
#check abs_warpSlope_sub_le_integral_abs
open RicciFlowSharpEstimate.Geometry.AreaProfile in
#check tendsto_warp_of_l1
open RicciFlowSharpEstimate.Geometry.AreaProfile in
#check tendsto_warpSlope_of_l1
open RicciFlowSharpEstimate.Geometry.AreaProfile in
#check tendstoUniformlyOn_warp_of_l1
open RicciFlowSharpEstimate.Geometry.AreaProfile in
#check tendstoUniformlyOn_warpSlope_of_l1
open RicciFlowSharpEstimate.Geometry.AreaProfile in
#check tendsto_meridionalAction_of_l1_of_ae
open RicciFlowSharpEstimate.Geometry.AreaProfile in
#check warp_affine_two
open RicciFlowSharpEstimate.Geometry.AreaProfile in
#check warpSlope_affine_two
open RicciFlowSharpEstimate.Geometry.AreaProfile in
#check continuous_meridionalAction_affine
open RicciFlowSharpEstimate.Geometry in
#check oneFormDissipation_squares_integrable
open RicciFlowSharpEstimate.Geometry in
#check oneFormDissipation_eq_integral_squares_of_constant_curvature
open RicciFlowSharpEstimate.Geometry in
#check oneFormDissipation_nonneg_of_constant_curvature
open RicciFlowSharpEstimate.Geometry.CriticalAreaProfile in
#print contractedCurvature
open RicciFlowSharpEstimate.Geometry.CriticalAreaProfile in
#print contractedLower
open RicciFlowSharpEstimate.Geometry.CriticalAreaProfile in
#print contractedUpper
open RicciFlowSharpEstimate.Geometry.CriticalAreaProfile in
#check contractedCurvature_continuous
open RicciFlowSharpEstimate.Geometry.CriticalAreaProfile in
#check contractedCurvature_moments
open RicciFlowSharpEstimate.Geometry.CriticalAreaProfile in
#check contractedCurvature_reflection
open RicciFlowSharpEstimate.Geometry.CriticalAreaProfile in
#check contractedCurvature_antitoneOn_left
open RicciFlowSharpEstimate.Geometry.CriticalAreaProfile in
#check contractedCurvature_monotoneOn_right
open RicciFlowSharpEstimate.Geometry.CriticalAreaProfile in
#check contractedCurvature_bounds
open RicciFlowSharpEstimate.Geometry.CriticalAreaProfile in
#check contracted_strict_bounds
open RicciFlowSharpEstimate.Geometry.CriticalAreaProfile in
#check contracted_ratio_deficit
open RicciFlowSharpEstimate.Geometry.CriticalAreaProfile in
#check contracted_ratio_deficit_pos
open RicciFlowSharpEstimate.Geometry.CriticalAreaProfile in
#check contracted_ratio_lt_criticalCap
open RicciFlowSharpEstimate.Geometry.CriticalAreaProfile in
#check exists_negative_contraction_parameter_of_negative_action
open RicciFlowSharpEstimate.Geometry.CriticalAreaProfile in
#check exists_smooth_negative_contraction
open RicciFlowSharpEstimate.Geometry.AreaProfile in
#check exists_smooth_negative_action_of_symmetric_box
open RicciFlowSharpEstimate.Geometry.CriticalAreaProfile in
#check exists_smooth_negative_area_data
open RicciFlowSharpEstimate.Geometry in
#check exists_smooth_negative_geometric_realization
open RicciFlowSharpEstimate.Geometry in
#check exists_negative_rotational_below_conformalKillingThreshold
open RicciFlowSharpEstimate.Geometry in
#print rotationalSafeCaps
open RicciFlowSharpEstimate.Geometry in
#check one_mem_rotationalSafeCaps
open RicciFlowSharpEstimate.Geometry in
#check rotationalSafeCaps_nonempty
open RicciFlowSharpEstimate.Geometry in
#check rotationalSafeCaps_downward
open RicciFlowSharpEstimate.Geometry in
#check exists_contracted_bound_for_rotationalSafeCaps
open RicciFlowSharpEstimate.Geometry in
#check rotationalSafeCaps_bddAbove
open RicciFlowSharpEstimate.Geometry in
#print rotationalThreshold
open RicciFlowSharpEstimate.Geometry in
#check one_le_rotationalThreshold
open RicciFlowSharpEstimate.Geometry in
#check exists_contracted_ratio_above_rotationalThreshold
open RicciFlowSharpEstimate.Geometry in
#check rotationalThreshold_lt_conformalKillingThreshold
#check RicciFlowSharpEstimate.Geometry.AreaProfile.meridionalOperator
#check RicciFlowSharpEstimate.Geometry.AreaProfile.meridionalOperator_contDiff
#check RicciFlowSharpEstimate.Geometry.AreaProfile.meridionalAction_eq_square_potential
#check RicciFlowSharpEstimate.Geometry.AreaProfile.meridionalGreenFlux
#check RicciFlowSharpEstimate.Geometry.AreaProfile.meridionalGreenFlux_hasDerivAt
#check RicciFlowSharpEstimate.Geometry.AreaProfile.meridionalGreenFlux_endpoints
#check RicciFlowSharpEstimate.Geometry.AreaProfile.integral_warp_mul_operator_mul
#check RicciFlowSharpEstimate.Geometry.AreaProfile.meridionalJacobiOperator
#check RicciFlowSharpEstimate.Geometry.AreaProfile.meridionalJacobiOperator_contDiff
#check RicciFlowSharpEstimate.Geometry.AreaProfile.integral_meridionalOperator_pair_eq_jacobi
#check RicciFlowSharpEstimate.Geometry.AreaProfile.meridionalOperator_add_mul
#check RicciFlowSharpEstimate.Geometry.AreaProfile.meridionalAction_add_mul
#check RicciFlowSharpEstimate.Geometry.AreaProfile.meridionalAction_hasDerivAt
#check RicciFlowSharpEstimate.Geometry.AreaProfile.integral_warp_mul_sq_pos
#check RicciFlowSharpEstimate.Geometry.AreaProfile.meridionalAction_stationary_iff
#check RicciFlowSharpEstimate.Geometry.AreaProfile.meridionalJacobiOperator_zero
#check RicciFlowSharpEstimate.Geometry.AreaProfile.meridionalJacobiOperator_one
#check RicciFlowSharpEstimate.Geometry.AreaProfile.meridionalAction_eq_integral_jacobi
#check RicciFlowSharpEstimate.Geometry.AreaProfile.meridionalAction_const_mul
#check RicciFlowSharpEstimate.Geometry.AreaProfile.exists_normalized_area_probe
#check
  RicciFlowSharpEstimate.Geometry.AreaProfile.oneFormDissipation_eq_integral_jacobi_of_profile_probe
#check RicciFlowSharpEstimate.Geometry.AreaProfile.oneFormDissipation_meridional_hasDerivAt
open RicciFlowSharpEstimate.Analysis.VolterraPairing in
#check integral_mul_primitive_eq
open RicciFlowSharpEstimate.Analysis.VolterraPairing in
#check integral_mul_kernel_eq
open RicciFlowSharpEstimate.Analysis in
#check exists_pos_add_mul_pos_of_isCompact
open RicciFlowSharpEstimate.Analysis in
#check exists_pos_add_mul_mem_Ioo_of_isCompact
open RicciFlowSharpEstimate.Analysis in
#check add_mul_sub_mem_Icc
open RicciFlowSharpEstimate.Analysis in
#check exists_pos_add_mul_mem_Icc_of_isCompact_of_free_support
open RicciFlowSharpEstimate.Geometry.AreaProfile in
#check warpVariation
open RicciFlowSharpEstimate.Geometry.AreaProfile in
#check warpSlopeVariation
open RicciFlowSharpEstimate.Geometry.AreaProfile in
#check warp_add_mul
open RicciFlowSharpEstimate.Geometry.AreaProfile in
#check warpSlope_add_mul
open RicciFlowSharpEstimate.Geometry.AreaProfile in
#check warpVariation_hasDerivAt
open RicciFlowSharpEstimate.Geometry.AreaProfile in
#check warpSlopeVariation_hasDerivAt
open RicciFlowSharpEstimate.Geometry.AreaProfile in
#check warpVariation_continuous
open RicciFlowSharpEstimate.Geometry.AreaProfile in
#check warpSlopeVariation_continuous
open RicciFlowSharpEstimate.Geometry.AreaProfile in
#check curvature_moments_add_mul
open RicciFlowSharpEstimate.Geometry.AreaProfile in
#check curvature_variation_endpoints
open RicciFlowSharpEstimate.Geometry.AreaProfile in
#check probeMass
open RicciFlowSharpEstimate.Geometry.AreaProfile in
#check rayleighQuotient
open RicciFlowSharpEstimate.Geometry.AreaProfile in
#check probeMass_add_mul
open RicciFlowSharpEstimate.Geometry.AreaProfile in
#check probeMass_hasDerivAt
open RicciFlowSharpEstimate.Geometry.AreaProfile in
#check rayleighQuotient_hasDerivAt
open RicciFlowSharpEstimate.Geometry.AreaProfile in
#check rayleighQuotient_stationary_iff
open RicciFlowSharpEstimate.Geometry.AreaProfile in
#check rayleighQuotient_eq_of_probeMass_eq_one
open RicciFlowSharpEstimate.Geometry.AreaProfile in
#check rayleighQuotient_stationary_iff_of_probeMass_eq_one
open RicciFlowSharpEstimate.Geometry.AreaProfile in
#check rayleighQuotient_stationary_iff_of_action_eq_zero
open RicciFlowSharpEstimate.Geometry.AreaProfile in
#check rayleighQuotient_euler_eq_of_isLocalMin
open RicciFlowSharpEstimate.Geometry.AreaProfile in
#check normalizedProbe
open RicciFlowSharpEstimate.Geometry.AreaProfile in
#check probeMass_normalizedProbe
open RicciFlowSharpEstimate.Geometry.AreaProfile in
#check meridionalAction_normalizedProbe
open RicciFlowSharpEstimate.Geometry.AreaProfile in
#check normalized_probe_action_hasDerivAt
open RicciFlowSharpEstimate.Geometry.AreaProfile in
#check normalized_probe_euler_eq_of_isLocalMin
open RicciFlowSharpEstimate.Geometry.AreaProfile in
#check curvatureWarpCoefficient
open RicciFlowSharpEstimate.Geometry.AreaProfile in
#check curvatureSlopeCoefficient
open RicciFlowSharpEstimate.Geometry.AreaProfile in
#check curvatureCoefficient
open RicciFlowSharpEstimate.Geometry.AreaProfile in
#check meridionalOperator_continuous
open RicciFlowSharpEstimate.Geometry.AreaProfile in
#check curvatureWarpCoefficient_continuous
open RicciFlowSharpEstimate.Geometry.AreaProfile in
#check curvatureSlopeCoefficient_continuous
open RicciFlowSharpEstimate.Geometry.AreaProfile in
#check curvatureCoefficient_continuous
open RicciFlowSharpEstimate.Geometry.AreaProfile in
#check curvatureFirstVariation
open RicciFlowSharpEstimate.Geometry.AreaProfile in
#check meridionalAction_curvature_hasDerivAt
open RicciFlowSharpEstimate.Geometry.AreaProfile in
#check curvatureSwitchingDensity
open RicciFlowSharpEstimate.Geometry.AreaProfile in
#check curvatureSwitchingDensity_continuous
open RicciFlowSharpEstimate.Geometry.AreaProfile in
#check curvatureFirstVariation_eq_integral_switching
open RicciFlowSharpEstimate.Geometry.AreaProfile in
#check meridionalAction_curvature_hasDerivAt_switching
open RicciFlowSharpEstimate.Geometry.AreaProfile in
#check probeMass_curvature_add_mul
open RicciFlowSharpEstimate.Geometry.AreaProfile in
#check probeMass_curvature_hasDerivAt
open RicciFlowSharpEstimate.Geometry.AreaProfile in
#check curvatureLagrangeDensity
open RicciFlowSharpEstimate.Geometry.AreaProfile in
#check action_sub_mass_curvature_hasDerivAt
open RicciFlowSharpEstimate.Geometry.AreaProfile in
#check rayleighQuotient_curvature_hasDerivAt
open RicciFlowSharpEstimate.Geometry.AreaProfile in
#check normalized_curvature_action_hasDerivAt
open RicciFlowSharpEstimate.Geometry.AreaProfile in
#check eventually_normalized_curvature_variation
open RicciFlowSharpEstimate.Geometry.AreaProfile in
#check isLocalMinOn_normalized_curvature_iff
open RicciFlowSharpEstimate.Geometry.AreaProfile in
#check curvatureParameters
open RicciFlowSharpEstimate.Geometry.AreaProfile in
#check mem_curvatureParameters_iff
open RicciFlowSharpEstimate.Geometry.AreaProfile in
#check Icc_subset_curvatureParameters_segment
open RicciFlowSharpEstimate.Geometry.AreaProfile in
#check curvatureParameters_mem_nhds_of_interior
open RicciFlowSharpEstimate.Geometry.AreaProfile in
#check curvature_pairing_nonneg_of_isLocalMinOn_segment
open RicciFlowSharpEstimate.Geometry.AreaProfile in
#check curvature_pairing_eq_zero_of_isLocalMinOn_interior
open RicciFlowSharpEstimate.Geometry.AreaProfile in
#check curvatureParameters_mem_nhds_of_free_support
open RicciFlowSharpEstimate.Geometry.AreaProfile in
#check curvature_pairing_eq_zero_of_isLocalMinOn_free_support
open RicciFlowSharpEstimate.Analysis in
#check eqOn_derivatives_Icc
open RicciFlowSharpEstimate.Geometry.ReciprocalArea in
#check coordinate_contDiff
open RicciFlowSharpEstimate.Geometry.RotationalProfile.PoleData in
#check AreaNormalization
open RicciFlowSharpEstimate.Geometry.RotationalProfile.PoleData in
#check nonempty_areaNormalization
open RicciFlowSharpEstimate.Geometry.RotationalProfile.PoleData in
#check areaNormalization
open RicciFlowSharpEstimate.Geometry.RotationalProfile.PoleData.AreaNormalization in
#check inverse
open RicciFlowSharpEstimate.Geometry.RotationalProfile.PoleData.AreaNormalization in
#check probe
open RicciFlowSharpEstimate.Geometry.RotationalProfile.PoleData.AreaNormalization in
#check curvature_pos
open RicciFlowSharpEstimate.Geometry.RotationalProfile.PoleData.AreaNormalization in
#check integral_curvature
open RicciFlowSharpEstimate.Geometry.RotationalProfile.PoleData.AreaNormalization in
#check integral_mul_curvature
open RicciFlowSharpEstimate.Geometry.RotationalProfile.PoleData.AreaNormalization in
#check inverse_contDiff
open RicciFlowSharpEstimate.Geometry.RotationalProfile.PoleData.AreaNormalization in
#check inverse_hasDerivAt
open RicciFlowSharpEstimate.Geometry.RotationalProfile.PoleData.AreaNormalization in
#check inverse_coordinate
open RicciFlowSharpEstimate.Geometry.RotationalProfile.PoleData.AreaNormalization in
#check inverse_eq
open RicciFlowSharpEstimate.Geometry.RotationalProfile.PoleData.AreaNormalization in
#check inverse_mem
open RicciFlowSharpEstimate.Geometry.RotationalProfile.PoleData.AreaNormalization in
#check coordinate_inverse
open RicciFlowSharpEstimate.Geometry.RotationalProfile.PoleData.AreaNormalization in
#check inverse_zero
open RicciFlowSharpEstimate.Geometry.RotationalProfile.PoleData.AreaNormalization in
#check inverse_one
open RicciFlowSharpEstimate.Geometry.RotationalProfile.PoleData.AreaNormalization in
#check curvature_coordinate
open RicciFlowSharpEstimate.Geometry.RotationalProfile.PoleData.AreaNormalization in
#check warp_coordinate
open RicciFlowSharpEstimate.Geometry.RotationalProfile.PoleData.AreaNormalization in
#check warpSlope_coordinate
open RicciFlowSharpEstimate.Geometry.RotationalProfile.PoleData in
#check meridionalOneForm_eq_zero_iff
open RicciFlowSharpEstimate.Geometry.RotationalProfile.PoleData in
#check meridionalOneForm_ne_zero_iff
open RicciFlowSharpEstimate.Geometry.RotationalProfile.PoleData in
#check azimuthalOneForm_eq_zero_iff
open RicciFlowSharpEstimate.Geometry.RotationalProfile.PoleData in
#check azimuthalOneForm_ne_zero_iff
open RicciFlowSharpEstimate.Geometry.AreaProfile in
#check meridionalAction_congr
open RicciFlowSharpEstimate.Geometry.RotationalProfile.PoleData.AreaNormalization in
#check probe_contDiff
open RicciFlowSharpEstimate.Geometry.RotationalProfile.PoleData.AreaNormalization in
#check probe_coordinate
open RicciFlowSharpEstimate.Geometry.RotationalProfile.PoleData.AreaNormalization in
#check deriv_probe
open RicciFlowSharpEstimate.Geometry.RotationalProfile.PoleData.AreaNormalization in
#check deriv_deriv_probe
open RicciFlowSharpEstimate.Geometry.RotationalProfile.PoleData.AreaNormalization in
#check curvature_deriv_coordinate
open RicciFlowSharpEstimate.Geometry.RotationalProfile.PoleData.AreaNormalization in
#check meridionalOperator_coordinate
open RicciFlowSharpEstimate.Geometry.RotationalProfile.PoleData.AreaNormalization in
#check meridionalDensity_coordinate
open RicciFlowSharpEstimate.Geometry.RotationalProfile.PoleData.AreaNormalization in
#check meridionalAction_eq
open RicciFlowSharpEstimate.Geometry.RotationalProfile.PoleData.AreaNormalization in
#check oneFormDissipation_meridional_eq
open RicciFlowSharpEstimate.Geometry.RotationalProfile.PoleData.AreaNormalization in
#check curvature_eq_on
open RicciFlowSharpEstimate.Geometry.RotationalProfile.PoleData.AreaNormalization in
#check curvature_deriv_eq_on
open RicciFlowSharpEstimate.Geometry.RotationalProfile.PoleData.AreaNormalization in
#check inverse_eq_on
open RicciFlowSharpEstimate.Geometry.RotationalProfile.PoleData.AreaNormalization in
#check probe_eq_on
open RicciFlowSharpEstimate.Geometry.RotationalProfile.PoleData.AreaNormalization in
#check probe_derivatives_eq_on
open RicciFlowSharpEstimate.Geometry.RotationalProfile.PoleData.AreaNormalization in
#check meridionalAction_extension_independent
open RicciFlowSharpEstimate.Geometry.RotationalProfile.PoleData.AreaNormalization in
#check probe_comp_coordinate
open RicciFlowSharpEstimate.Geometry.RotationalProfile.PoleData.AreaNormalization in
#check meridionalAction_comp_coordinate
open RicciFlowSharpEstimate.Geometry.RotationalProfile.PoleData.AreaNormalization in
#check inverse_mem_Ioo
open RicciFlowSharpEstimate.Geometry.RotationalProfile.PoleData.AreaNormalization in
#check probe_nonzero_iff
open RicciFlowSharpEstimate.Geometry.RotationalProfile.PoleData.AreaNormalization in
#check probeMass_pos_iff_meridional_ne_zero
open RicciFlowSharpEstimate.Geometry.RotationalProfile.PoleData.AreaNormalization in
#check probeMass_pos_iff_azimuthal_ne_zero
open RicciFlowSharpEstimate.Geometry.RotationalProfile.PoleData.AreaNormalization in
#check normalized_probe_action
open RicciFlowSharpEstimate.Geometry.RotationalProfile.PoleData.AreaNormalization in
#check integral_normSq_eq_probeMass
open RicciFlowSharpEstimate.Geometry.RotationalProfile.PoleData.AreaNormalization in
#check curvature_inverse
open RicciFlowSharpEstimate.Geometry.RotationalProfile.PoleData.AreaNormalization in
#check profile_mul_curvature
open RicciFlowSharpEstimate.Geometry.RotationalProfile.PoleData.AreaNormalization in
#check curvature_bounds_scaled
open RicciFlowSharpEstimate.Geometry.RotationalProfile.PoleData.AreaNormalization in
#check probeMass_pos_iff_pullback_meridional_ne_zero
open RicciFlowSharpEstimate.Geometry.RotationalProfile.PoleData.AreaNormalization in
#check probeMass_pos_iff_pullback_azimuthal_ne_zero
open RicciFlowSharpEstimate.Geometry.RotationalProfile.PoleData.AreaNormalization in
#check oneFormDissipation_pullback_meridional_eq
open RicciFlowSharpEstimate.Geometry.RotationalProfile.PoleData.AreaNormalization in
#check meridionalAction_nonneg_of_normalized_safety
open RicciFlowSharpEstimate.Geometry.RotationalProfile.PoleData.AreaNormalization in
#check exists_conjugated_haar_area_dissipation
open RicciFlowSharpEstimate.Geometry.RotationalProfile.PoleData.AreaNormalization in
#check oneFormDissipation_nonneg_of_normalized_safety
open RicciFlowSharpEstimate.Geometry.RotationalProfile.PoleData in
#check oneFormDissipation_eq_normalizedAreaAction
open RicciFlowSharpEstimate.Geometry.IsRepresentedRotationalMetric in
#check exists_normalized_area_representation
open RicciFlowSharpEstimate.Geometry in
#check rotationalSafeCaps_of_normalized_area_safety
open RicciFlowSharpEstimate.Geometry in
#check areaAction_nonneg_of_rotationalSafeCap
open RicciFlowSharpEstimate.Geometry.RotationalProfile.PoleData.AreaNormalization in
#check oneFormDissipation_meridional_hasDerivAt
open RicciFlowSharpEstimate.Geometry.RotationalProfile.PoleData.AreaNormalization in
#check oneFormDissipation_meridional_stationary_iff
open RicciFlowSharpEstimate.Geometry.RotationalProfile.PoleData.AreaNormalization in
#check oneFormDissipation_pullback_meridional_hasDerivAt
open RicciFlowSharpEstimate.Geometry.RotationalProfile.PoleData.AreaNormalization in
#check oneFormDissipation_div_normSq_eq
open RicciFlowSharpEstimate.Geometry.RotationalProfile.PoleData.AreaNormalization in
#check oneFormDissipation_div_normSq_hasDerivAt
open RicciFlowSharpEstimate.Geometry.RotationalProfile.PoleData.AreaNormalization in
#check oneFormDissipation_div_normSq_euler_eq_of_isLocalMin
open RicciFlowSharpEstimate.Analysis in
#check integral_sq_le_parabolic_weighted_energy
open RicciFlowSharpEstimate.Geometry.AreaProfile in
#check quadratic_le_warp_of_curvature_lower
open RicciFlowSharpEstimate.Geometry.AreaProfile in
#check warp_le_quadratic_of_curvature_upper
open RicciFlowSharpEstimate.Geometry.AreaProfile in
#check warp_bounds_of_curvature_bounds
open RicciFlowSharpEstimate.Geometry.AreaProfile in
#check abs_warpSlope_le_two
open RicciFlowSharpEstimate.Geometry.AreaProfile in
#check warp_nonneg_le_two_mul_min
open RicciFlowSharpEstimate.Geometry.AreaProfile in
#check curvature_bounds_of_ratio
open RicciFlowSharpEstimate.Geometry.AreaProfile in
#check probeOperatorEnergy
open RicciFlowSharpEstimate.Geometry.AreaProfile in
#check probeGradientEnergy
open RicciFlowSharpEstimate.Geometry.AreaProfile in
#check meridionalOperator_continuous_of_contDiff_two
open RicciFlowSharpEstimate.Geometry.AreaProfile in
#check integral_warp_mul_probe_operator
open RicciFlowSharpEstimate.Geometry.AreaProfile in
#check probeGradientEnergy_nonneg
open RicciFlowSharpEstimate.Geometry.AreaProfile in
#check probeOperatorEnergy_nonneg
open RicciFlowSharpEstimate.Geometry.AreaProfile in
#check probeGradientEnergy_interpolation
open RicciFlowSharpEstimate.Geometry.AreaProfile in
#check integral_sq_le_probeMass_gradient
open RicciFlowSharpEstimate.Geometry.AreaProfile in
#check polarProbeMass
open RicciFlowSharpEstimate.Geometry.AreaProfile in
#check polarProbeMass_nonneg
open RicciFlowSharpEstimate.Geometry.AreaProfile in
#check polarProbeMass_le_four_mul_radius
open RicciFlowSharpEstimate.Geometry.AreaProfile in
#check probeOperatorEnergy_sub_le_action
open RicciFlowSharpEstimate.Geometry.AreaProfile in
#check actionMassCorrection
open RicciFlowSharpEstimate.Geometry.AreaProfile in
#check actionMassCorrection_nonneg
open RicciFlowSharpEstimate.Geometry.AreaProfile in
#check meridionalAction_coercive
open RicciFlowSharpEstimate.Geometry.AreaProfile in
#check exists_uniform_action_coercivity
open RicciFlowSharpEstimate.Geometry.AreaProfile in
#check probe_energies_le_of_unit_mass_action_le
open RicciFlowSharpEstimate.Geometry.AreaProfile in
#check polarProbeMass_le_of_unit_mass_action_le
open RicciFlowSharpEstimate.Geometry.AreaProfile in
#check exists_uniform_polar_mass_radius
open RicciFlowSharpEstimate.Geometry.AreaProfile in
#check meridionalAction_coercive_of_curvature_ratio
open RicciFlowSharpEstimate.Geometry.AreaProfile in
#check exists_uniform_polar_mass_radius_of_ratio
open RicciFlowSharpEstimate.Analysis in
#check integral_parabolic_mul_sq_le
open RicciFlowSharpEstimate.Analysis in
#check integral_left_sq_le_parabolic_energy
open RicciFlowSharpEstimate.Analysis in
#check integral_polar_sq_le_parabolic_energy
open RicciFlowSharpEstimate.Geometry.AreaProfile in
#check integral_warp_operator_add_curvature_sq
open RicciFlowSharpEstimate.Geometry.AreaProfile in
#check integral_warp_cube_second_deriv_sq_le
open RicciFlowSharpEstimate.Geometry.AreaProfile in
#check integral_parabolic_deriv_sq_le
open RicciFlowSharpEstimate.Geometry.AreaProfile in
#check meridionalActionRemainder
open RicciFlowSharpEstimate.Geometry.AreaProfile in
#check meridionalActionRemainder_continuous
open RicciFlowSharpEstimate.Geometry.AreaProfile in
#check polarActionRemainder
open RicciFlowSharpEstimate.Geometry.AreaProfile in
#check polarActionRemainder_le
open RicciFlowSharpEstimate.Geometry.AreaProfile in
#check exists_uniform_probe_regularity_bound
open RicciFlowSharpEstimate.Geometry.AreaProfile in
#check exists_uniform_polar_action_radius
open RicciFlowSharpEstimate.Geometry.AreaProfile in
#check exists_uniform_polar_action_radius_of_ratio
open RicciFlowSharpEstimate.Analysis in
#check integrable_mul_of_ae_abs_le
open RicciFlowSharpEstimate.Analysis in
#check abs_integral_mul_sub_le_of_ae_abs_le
open RicciFlowSharpEstimate.Analysis in
#check tendsto_integral_mul_of_bounded_L2_pairings
open RicciFlowSharpEstimate.Analysis in
#check HilbertWeakSubsequence.norm_le_of_tendsto_inner
open RicciFlowSharpEstimate.Analysis in
#check HilbertWeakSubsequence.exists_subseq_tendsto_inner_of_norm_le
open RicciFlowSharpEstimate.Analysis in
#check exists_subseq_locallyUniform_of_local_derivative_energy
open RicciFlowSharpEstimate.Analysis in
#check mul_integral_sq_le_parabolic_energy
open RicciFlowSharpEstimate.Analysis in
#check exists_subseq_locallyUniform_probe_deriv_of_weighted_energy
open RicciFlowSharpEstimate.Analysis in
#check sq_sub_le_length_mul_integral_deriv_sq
open RicciFlowSharpEstimate.Analysis in
#check sq_sub_le_abs_mul_integral_deriv_sq
open RicciFlowSharpEstimate.Analysis in
#check length_mul_sq_le_integral_sq_add_integral_deriv_sq
open RicciFlowSharpEstimate.Analysis in
#check memLp_two_of_ae_tendsto_of_integral_sq_bound
open RicciFlowSharpEstimate.Analysis in
#check uniformIntegrable_two_of_sq_tails
open RicciFlowSharpEstimate.Analysis in
#check memLp_and_tendsto_eLpNorm_two_of_sq_tails
open RicciFlowSharpEstimate.Analysis in
#check L2WeakOrder.ae_nonneg_of_tendsto_inner
open RicciFlowSharpEstimate.Analysis in
#check L2WeakOrder.ae_bounds_of_tendsto_inner
open RicciFlowSharpEstimate.Analysis in
#check L2WeightedMassContinuity.tendsto_integral_mul_sq
open RicciFlowSharpEstimate.Analysis in
#check L2WeightedMassContinuity.tendsto_top_of_eventually_ae_abs_sub_le
open RicciFlowSharpEstimate.Analysis in
#check exists_subseq_tendstoLocallyUniformly_of_equicontinuous
open RicciFlowSharpEstimate.Analysis in
#check HasParabolicWeakDerivatives
open RicciFlowSharpEstimate.Analysis in
#print HasParabolicWeakDerivatives
open RicciFlowSharpEstimate.Analysis in
#check HasParabolicWeakDerivatives.integrable_sq
open RicciFlowSharpEstimate.Analysis in
#check HasParabolicWeakDerivatives.integrable_weighted_deriv_sq
open RicciFlowSharpEstimate.Analysis in
#check HasParabolicWeakDerivatives.integrable_weighted_secondDeriv_sq
open RicciFlowSharpEstimate.Analysis in
#check hasParabolicWeakDerivatives_of_contDiff
open RicciFlowSharpEstimate.Analysis in
#check HasParabolicWeakDerivatives.ae_unique
open RicciFlowSharpEstimate.Analysis in
#check HasParabolicWeakDerivatives.memLp_deriv_compact
open RicciFlowSharpEstimate.Analysis in
#check HasParabolicWeakDerivatives.memLp_secondDeriv_compact
open RicciFlowSharpEstimate.Analysis in
#check integrable_mul_of_locallyIntegrableOn
open RicciFlowSharpEstimate.Analysis in
#check HasWeakDerivOn
open RicciFlowSharpEstimate.Analysis in
#print HasWeakDerivOn
open RicciFlowSharpEstimate.Analysis in
#check HasWeakDerivOn.integrable_deriv_test_mul
open RicciFlowSharpEstimate.Analysis in
#check HasWeakDerivOn.integrable_test_mul_weakDeriv
open RicciFlowSharpEstimate.Analysis in
#check HasWeakDerivOn.ae_unique
open RicciFlowSharpEstimate.Analysis in
#check hasWeakDerivOn_of_contDiffOn
open RicciFlowSharpEstimate.Analysis in
#check hasWeakDerivOn_of_contDiff
open RicciFlowSharpEstimate.Analysis in
#check HasWeakDerivOn.congr_ae
open RicciFlowSharpEstimate.Analysis in
#check test_mul_integral_tendsto_of_locallyUniformlyOn
open RicciFlowSharpEstimate.Analysis in
#check HasWeakDerivOn.of_tendsto_test_pairings
open RicciFlowSharpEstimate.Analysis in
#check hasWeakDerivOn_of_locallyUniformlyOn
open RicciFlowSharpEstimate.Analysis in
#check locallyIntegrableOn_Ioo_div_weight
open RicciFlowSharpEstimate.Analysis in
#check memLp_two_Ioo_div_weight_on_compact
open RicciFlowSharpEstimate.Analysis in
#check memLp_two_Ioo_div_test
open RicciFlowSharpEstimate.Analysis in
#check ae_weight_mul_div_Ioo
open RicciFlowSharpEstimate.Analysis in
#check memLp_two_Ioo_weight_mul_div
open RicciFlowSharpEstimate.Analysis in
#check memLp_two_Ioo_weighted_deriv
open RicciFlowSharpEstimate.Analysis in
#check hasWeakDerivOn_Ioo_of_weighted_weak_L2_limit
open RicciFlowSharpEstimate.Geometry.AreaProfile in
#check exists_curvature_subsequence_of_ratio_bound
open RicciFlowSharpEstimate.Geometry.AreaProfile in
#check exists_normalized_joint_weak_limit
open RicciFlowSharpEstimate.Geometry.AreaProfile in
#check exists_subseq_locallyUniform_probe_deriv_of_action_bound
open RicciFlowSharpEstimate.Geometry.AreaProfile in
#check uniformIntegrable_probes_of_action_bound
open RicciFlowSharpEstimate.Geometry.AreaProfile in
#check exists_subseq_strong_probe_of_action_bound
open RicciFlowSharpEstimate.Geometry.AreaProfile in
#check exists_subseq_weak_probe_of_action_bound
open RicciFlowSharpEstimate.Geometry.AreaProfile in
#check tendstoUniformlyOn_warpSlope_of_weak_L2
open RicciFlowSharpEstimate.Geometry.AreaProfile in
#check tendstoUniformlyOn_warp_of_weak_L2
open RicciFlowSharpEstimate.Geometry.AreaProfile in
#check continuousOn_warpSlope_of_weak_L2
open RicciFlowSharpEstimate.Geometry.AreaProfile in
#check continuousOn_warp_of_weak_L2
open RicciFlowSharpEstimate.Geometry.AreaProfile in
#check warp_bounds_of_weak_L2
open RicciFlowSharpEstimate.Geometry.AreaProfile in
#check abs_warpSlope_le_two_of_weak_L2
open RicciFlowSharpEstimate.Geometry.AreaProfile in
#check warp_endpoints_of_weak_L2
open RicciFlowSharpEstimate.Geometry.AreaProfile in
#check hasWeakDerivOn_warp_of_weak_L2
open RicciFlowSharpEstimate.Geometry.AreaProfile in
#check hasWeakDerivOn_warpSlope_of_weak_L2
open RicciFlowSharpEstimate.Geometry.AreaProfile in
#check tendsto_warpSlope_of_weak_L2
open RicciFlowSharpEstimate.Geometry.AreaProfile in
#check tendsto_warp_of_weak_L2
open RicciFlowSharpEstimate.Geometry.AreaProfile in
#check weakMeridionalOperator
open RicciFlowSharpEstimate.Geometry.AreaProfile in
#check weakMeridionalAction
open RicciFlowSharpEstimate.Geometry.AreaProfile in
#check weakMeridionalAction_deriv
open RicciFlowSharpEstimate.Geometry.AreaProfile in
#check memLp_weak_operator_and_potential_of_warp_bounds
open RicciFlowSharpEstimate.Geometry.AreaProfile in
#check integrable_weakMeridionalActionDensity_of_warp_bounds
open RicciFlowSharpEstimate.Geometry.AreaProfile in
#check weakMeridionalAction_intervalIntegrable_of_warp_bounds
open RicciFlowSharpEstimate.Geometry.AreaProfile in
#check weakMeridionalAction_decomposition_of_warp_bounds
open RicciFlowSharpEstimate.Analysis in
#check HasWeakDerivOn.locallyIntegrable
open RicciFlowSharpEstimate.Analysis in
#check HasWeakDerivOn.locallyIntegrable_deriv
open RicciFlowSharpEstimate.Analysis in
#check HasWeakDerivOn.integral_deriv_mul
open RicciFlowSharpEstimate.Analysis in
#check HasParabolicWeakDerivatives.weakDeriv
open RicciFlowSharpEstimate.Analysis in
#check HasParabolicWeakDerivatives.weakDeriv_deriv
open RicciFlowSharpEstimate.Analysis in
#check HasParabolicWeakDerivatives.memLp
open RicciFlowSharpEstimate.Analysis in
#check HasParabolicWeakDerivatives.memLp_weighted_deriv
open RicciFlowSharpEstimate.Analysis in
#check HasParabolicWeakDerivatives.memLp_weighted_secondDeriv
open RicciFlowSharpEstimate.Analysis in
#check integrable_and_tendsto_mul_of_bounded_weak_pairing
open RicciFlowSharpEstimate.Analysis in
#check uniformIntegrable_mul_left_of_eLpNorm_two_bound
open RicciFlowSharpEstimate.Analysis in
#check tendsto_eLpNorm_one_mul_sub_of_ae_tendsto_of_integral_sq_bound
open RicciFlowSharpEstimate.Analysis in
#check tendsto_integral_abs_mul_sub_of_tendsto_eLpNorm_two
open RicciFlowSharpEstimate.Analysis in
#check tendsto_integral_abs_sub_of_ae_tendsto_of_integral_sq_bound
open RicciFlowSharpEstimate.Analysis in
#check tendsto_integral_mul_of_ae_tendsto_of_integral_sq_bound
open RicciFlowSharpEstimate.Analysis in
#check eventually_lt_integral_sq_of_weak_L2
open RicciFlowSharpEstimate.Analysis in
#check integral_sq_le_liminf_of_weak_L2
open RicciFlowSharpEstimate.Analysis in
#check eventually_lt_sum_integral_sq_sub_of_weak_L2
open RicciFlowSharpEstimate.Analysis in
#check memLp_mul_of_ae_abs_le
open RicciFlowSharpEstimate.Analysis in
#check tendsto_integral_mul_of_weak_L2_strong_L2
open RicciFlowSharpEstimate.Analysis in
#check tendsto_L2_mul_of_ae_tendsto
open RicciFlowSharpEstimate.Analysis in
#check weak_L2_mul_of_ae_tendsto_of_ae_abs_le
open RicciFlowSharpEstimate.Geometry.AreaProfile in
#check exists_uniform_parabolic_graph_bound
open RicciFlowSharpEstimate.Geometry.AreaProfile in
#check weak_derivative_part_of_area_limits
open RicciFlowSharpEstimate.Geometry.AreaProfile in
#check curvature_action_pairings_tendsto
open RicciFlowSharpEstimate.Geometry.AreaProfile in
#check weak_factors_and_action_liminf_of_area_limits
open RicciFlowSharpEstimate.Geometry.AreaProfile in
#check exists_normalized_joint_weak_limit_le_liminf_action
open RicciFlowSharpEstimate.Analysis in
#check exists_tail_convexCombination_tendsto_of_tendsto_inner
open RicciFlowSharpEstimate.Analysis in
#check exists_tail_convexCombination_tendsto_family
open RicciFlowSharpEstimate.Analysis in
#check strong_L2_mul_of_ae_tendsto_of_ae_abs_le
open RicciFlowSharpEstimate.Analysis in
#check tendsto_integral_mul_of_tendsto_eLpNorm_two
open RicciFlowSharpEstimate.Geometry.AreaProfile in
#check warp_sub_eq_integral_right_of_moments
open RicciFlowSharpEstimate.Geometry.AreaProfile in
#check abs_warp_sub_le_relative_integral_abs
open RicciFlowSharpEstimate.Geometry.AreaProfile in
#check abs_warpSlope_sub_le_integral_abs_of_integrableOn
open RicciFlowSharpEstimate.Geometry.AreaProfile in
#check smooth_area_pair_convexCombination
open RicciFlowSharpEstimate.Analysis in
#check exists_tail_convexCombination_tendsto_eLpNorm_two
open RicciFlowSharpEstimate.Geometry.AreaProfile in
#check exists_smooth_geometric_recovery_of_scalar_limits
open RicciFlowSharpEstimate.Geometry.AreaProfile in
#check exists_smooth_convex_recovery_of_weak_graph_pairings
open RicciFlowSharpEstimate.Geometry.AreaProfile in
#check action_mass_tendsto_of_strong_area_graph
open RicciFlowSharpEstimate.Geometry.AreaProfile in
#check exists_smooth_scalar_recovery_of_weak_graph_pairings
open RicciFlowSharpEstimate.Geometry.AreaProfile in
#check exists_joint_weak_limit_with_smooth_geometric_recovery
open RicciFlowSharpEstimate.Analysis in
#check strong_L2_const_mul_of_tendsto
open RicciFlowSharpEstimate.Analysis in
#check parabolicGraph_tendsto_const_mul
open RicciFlowSharpEstimate.Geometry.AreaProfile in
#check IsSmoothAreaCompetitor
open RicciFlowSharpEstimate.Geometry.AreaProfile in
#check smoothAreaActionValues
open RicciFlowSharpEstimate.Geometry.AreaProfile in
#check smoothAreaInfimum
open RicciFlowSharpEstimate.Geometry.AreaProfile in
#check IsSmoothAreaCompetitor.common_bounds
open RicciFlowSharpEstimate.Geometry.AreaProfile in
#check IsSmoothAreaCompetitor.memLp_curvature
open RicciFlowSharpEstimate.Geometry.AreaProfile in
#check probeMass_two_sqrt_three
open RicciFlowSharpEstimate.Geometry.AreaProfile in
#check meridionalAction_two_sqrt_three
open RicciFlowSharpEstimate.Geometry.AreaProfile in
#check isSmoothAreaCompetitor_round
open RicciFlowSharpEstimate.Geometry.AreaProfile in
#check IsSmoothAreaCompetitor.action_lower_bound
open RicciFlowSharpEstimate.Geometry.AreaProfile in
#check smoothAreaActionValues_nonempty
open RicciFlowSharpEstimate.Geometry.AreaProfile in
#check smoothAreaActionValues_bddBelow
open RicciFlowSharpEstimate.Geometry.AreaProfile in
#check smoothAreaInfimum_le_action
open RicciFlowSharpEstimate.Geometry.AreaProfile in
#check smoothAreaInfimum_le_four
open RicciFlowSharpEstimate.Geometry.AreaProfile in
#check neg_actionMassCorrection_le_smoothAreaInfimum
open RicciFlowSharpEstimate.Geometry.AreaProfile in
#check exists_smooth_area_minimizing_sequence
open RicciFlowSharpEstimate.Geometry.AreaProfile in
#check IsRecoverableAreaCompetitor
open RicciFlowSharpEstimate.Geometry.AreaProfile in
#check IsSmoothAreaCompetitor.recoverable
open RicciFlowSharpEstimate.Geometry.AreaProfile in
#check IsRecoverableAreaCompetitor.exists_action_recovery
open RicciFlowSharpEstimate.Geometry.AreaProfile in
#check IsRecoverableAreaCompetitor.infimum_le_action
open RicciFlowSharpEstimate.Geometry.AreaProfile in
#check exists_recoverable_area_minimizer
open RicciFlowSharpEstimate.Geometry.AreaProfile in
#check exists_area_minimizer_with_geometric_recovery
open RicciFlowSharpEstimate.Geometry.RotationalProfile.PoleData.AreaNormalization in
#check isSmoothAreaCompetitor_normalizedProbe
open RicciFlowSharpEstimate.Geometry.RotationalProfile.PoleData.AreaNormalization in
#check smoothAreaInfimum_le_length_sq_mul_oneFormDissipation_div_normSq
open RicciFlowSharpEstimate.Analysis in
#check HasWeakDerivOn.add
open RicciFlowSharpEstimate.Analysis in
#check HasWeakDerivOn.const_mul
open RicciFlowSharpEstimate.Analysis in
#check HasParabolicWeakDerivatives.add
open RicciFlowSharpEstimate.Analysis in
#check HasParabolicWeakDerivatives.const_mul
open RicciFlowSharpEstimate.Analysis in
#check parabolicGraph_tendsto_add_fixed_smooth
open RicciFlowSharpEstimate.Geometry.AreaProfile in
#check IsRecoverableAreaCompetitor.strong_curvature_subsequence
open RicciFlowSharpEstimate.Geometry.AreaProfile in
#check IsRecoverableAreaCompetitor.geometry_bounds
open RicciFlowSharpEstimate.Geometry.AreaProfile in
#check weakMeridionalPairingDensity
open RicciFlowSharpEstimate.Geometry.AreaProfile in
#check weakMeridionalPairing
open RicciFlowSharpEstimate.Geometry.AreaProfile in
#check weakMeridionalPairing_symm
open RicciFlowSharpEstimate.Geometry.AreaProfile in
#check weakMeridionalPairing_self
open RicciFlowSharpEstimate.Geometry.AreaProfile in
#check weakMeridionalAction_const_mul
open RicciFlowSharpEstimate.Geometry.AreaProfile in
#check integrable_weakMeridionalPairingDensity_of_warp_bounds
open RicciFlowSharpEstimate.Geometry.AreaProfile in
#check weakMeridionalPairing_intervalIntegrable_of_warp_bounds
open RicciFlowSharpEstimate.Geometry.AreaProfile in
#check weakMeridionalAction_add_mul
open RicciFlowSharpEstimate.Geometry.AreaProfile in
#check weakMeridionalAction_hasDerivAt
open RicciFlowSharpEstimate.Geometry.AreaProfile in
#check integrable_probeMassDensity_of_warp_bounds
open RicciFlowSharpEstimate.Geometry.AreaProfile in
#check probeMass_intervalIntegrable_of_warp_bounds
open RicciFlowSharpEstimate.Geometry.AreaProfile in
#check integrable_probeMassPairing_of_warp_bounds
open RicciFlowSharpEstimate.Geometry.AreaProfile in
#check probeMassPairing_intervalIntegrable_of_warp_bounds
open RicciFlowSharpEstimate.Geometry.AreaProfile in
#check probeMass_add_mul_of_warp_bounds
open RicciFlowSharpEstimate.Geometry.AreaProfile in
#check probeMass_hasDerivAt_of_warp_bounds
open RicciFlowSharpEstimate.Geometry.AreaProfile in
#check IsRecoverableAreaCompetitor.normalized_probe_add_mul
open RicciFlowSharpEstimate.Geometry.AreaProfile in
#check IsRecoverableAreaCompetitor.weak_probe_equation_of_minimum
open RicciFlowSharpEstimate.Geometry.AreaProfile in
#check exists_recoverable_area_minimizer_weak_probe_equation
open RicciFlowSharpEstimate.Geometry.AreaProfile in
#check warp_affine_of_integrableOn
open RicciFlowSharpEstimate.Geometry.AreaProfile in
#check warpSlope_affine_of_integrableOn
open RicciFlowSharpEstimate.Geometry.AreaProfile in
#check curvature_moments_affine_of_integrableOn
open RicciFlowSharpEstimate.Geometry.AreaProfile in
#check probeMass_affine_curvature_of_integrableOn
open RicciFlowSharpEstimate.Geometry.AreaProfile in
#check probeMass_curvature_difference_intervalIntegrable
open RicciFlowSharpEstimate.Geometry.AreaProfile in
#check probeMass_curvature_segment_hasDerivAt
open RicciFlowSharpEstimate.Geometry.AreaProfile in
#check IsSmoothAreaCurvature
open RicciFlowSharpEstimate.Geometry.AreaProfile in
#check IsSmoothAreaCompetitor.curvature_admissible
open RicciFlowSharpEstimate.Geometry.AreaProfile in
#check IsSmoothAreaCurvature.with_unit_probe
open RicciFlowSharpEstimate.Geometry.AreaProfile in
#check IsSmoothAreaCurvature.common_bounds
open RicciFlowSharpEstimate.Geometry.AreaProfile in
#check IsSmoothAreaCurvature.memLp_curvature
open RicciFlowSharpEstimate.Geometry.AreaProfile in
#check IsSmoothAreaCurvature.geometry_bounds
open RicciFlowSharpEstimate.Geometry.AreaProfile in
#check IsSmoothAreaCurvature.convex_combination
open RicciFlowSharpEstimate.Geometry.AreaProfile in
#check isSmoothAreaCurvature_round
open RicciFlowSharpEstimate.Geometry.AreaProfile in
#check weakCurvatureSegmentDensity
open RicciFlowSharpEstimate.Geometry.AreaProfile in
#check weakCurvatureSegmentVariation
open RicciFlowSharpEstimate.Geometry.AreaProfile in
#check weakCurvatureSegmentDensity_integrable
open RicciFlowSharpEstimate.Geometry.AreaProfile in
#check weakCurvatureSegmentDensity_intervalIntegrable
open RicciFlowSharpEstimate.Geometry.AreaProfile in
#check weakMeridionalAction_curvature_segment_hasDerivAt
open RicciFlowSharpEstimate.Geometry.AreaProfile in
#check IsRecoverableAreaCompetitor.probeMass_curvature_segment_pos
open RicciFlowSharpEstimate.Geometry.AreaProfile in
#check IsRecoverableAreaCompetitor.normalized_curvature_segment
open RicciFlowSharpEstimate.Geometry.AreaProfile in
#check IsRecoverableAreaCompetitor.curvature_segment_inequality_of_minimum
open RicciFlowSharpEstimate.Geometry.AreaProfile in
#check exists_recoverable_area_minimizer_weak_conditions
open RicciFlowSharpEstimate.Analysis in
#check unitDirichletKernel
open RicciFlowSharpEstimate.Analysis in
#check unitDirichletSlopeKernel
open RicciFlowSharpEstimate.Analysis in
#check continuous_unitDirichletKernel
open RicciFlowSharpEstimate.Analysis in
#check measurable_unitDirichletKernel
open RicciFlowSharpEstimate.Analysis in
#check measurable_unitDirichletSlopeKernel
open RicciFlowSharpEstimate.Analysis in
#check abs_unitDirichletKernel_le
open RicciFlowSharpEstimate.Analysis in
#check abs_unitDirichletSlopeKernel_le_one
open RicciFlowSharpEstimate.Analysis in
#check integral_unitDirichletKernel
open RicciFlowSharpEstimate.Analysis in
#check integral_unitDirichletSlopeKernel
open RicciFlowSharpEstimate.Analysis in
#check integrable_kernel_adjoint_of_weighted_integrable
open RicciFlowSharpEstimate.Analysis in
#check integral_kernel_pairing_of_weighted_integrable
open RicciFlowSharpEstimate.Geometry.AreaProfile in
#check weakCurvatureWarpCoefficient
open RicciFlowSharpEstimate.Geometry.AreaProfile in
#check weakCurvatureSlopeCoefficient
open RicciFlowSharpEstimate.Geometry.AreaProfile in
#check weakCurvatureCoefficient
open RicciFlowSharpEstimate.Geometry.AreaProfile in
#check weakCurvatureWarpCoefficient_deriv
open RicciFlowSharpEstimate.Geometry.AreaProfile in
#check weakCurvatureSlopeCoefficient_deriv
open RicciFlowSharpEstimate.Geometry.AreaProfile in
#check weakCurvatureCoefficient_deriv
open RicciFlowSharpEstimate.Geometry.AreaProfile in
#check IsRecoverableAreaCompetitor.curvature_coefficients_integrable
open RicciFlowSharpEstimate.Geometry.AreaProfile in
#check warp_sub_eq_integral_unitDirichletKernel
open RicciFlowSharpEstimate.Geometry.AreaProfile in
#check warpSlope_sub_eq_integral_unitDirichletSlopeKernel
open RicciFlowSharpEstimate.Geometry.AreaProfile in
#check weakCurvatureAdjoint
open RicciFlowSharpEstimate.Geometry.AreaProfile in
#check IsRecoverableAreaCompetitor.weakCurvatureAdjoint_integrable
open RicciFlowSharpEstimate.Geometry.AreaProfile in
#check IsRecoverableAreaCompetitor.curvature_variation_eq_integral_adjoint
open RicciFlowSharpEstimate.Geometry.AreaProfile in
#check IsRecoverableAreaCompetitor.curvature_adjoint_inequality_of_minimum
open RicciFlowSharpEstimate.Geometry.AreaProfile in
#check exists_recoverable_area_minimizer_with_curvature_adjoint
open RicciFlowSharpEstimate.Analysis in
#check exists_contDiff_approx_Icc_of_memLp
open RicciFlowSharpEstimate.Analysis in
#check exists_contDiff_interior_moment_basis
open RicciFlowSharpEstimate.Analysis in
#check exists_contDiff_exact_moments_of_memLp_of_interior_box
open RicciFlowSharpEstimate.Analysis in
#check exists_contDiff_Icc_exact_balanced_moments
open RicciFlowSharpEstimate.Analysis in
#check exists_contDiff_Icc_exact_balanced_moments_sequence
open RicciFlowSharpEstimate.Geometry.AreaProfile in
#check IsBoundedAreaCurvature
open RicciFlowSharpEstimate.Geometry.AreaProfile in
#check IsBoundedAreaCurvature.memLp_curvature
open RicciFlowSharpEstimate.Geometry.AreaProfile in
#check IsSmoothAreaCurvature.bounded
open RicciFlowSharpEstimate.Geometry.AreaProfile in
#check IsRecoverableAreaCompetitor.curvature_bounded
open RicciFlowSharpEstimate.Geometry.AreaProfile in
#check IsBoundedAreaCurvature.exists_smooth_recovery
open RicciFlowSharpEstimate.Geometry.AreaProfile in
#check IsRecoverableAreaCompetitor.bounded_curvature_adjoint_inequality_of_minimum
open RicciFlowSharpEstimate.Geometry.AreaProfile in
#check exists_recoverable_area_minimizer_with_bounded_curvature_adjoint
open RicciFlowSharpEstimate.Analysis in
#check box_variational_inequality_iff
open RicciFlowSharpEstimate.Analysis in
#check exists_box_moment_multipliers
open RicciFlowSharpEstimate.Geometry.AreaProfile in
#check IsBoundedAreaCurvature.exists_strict_box
open RicciFlowSharpEstimate.Geometry.AreaProfile in
#check IsBoundedAreaCurvature.ae_eq_round_of_cap_one
open RicciFlowSharpEstimate.Geometry.AreaProfile in
#check IsRecoverableAreaCompetitor.exists_curvature_moment_multipliers
open RicciFlowSharpEstimate.Geometry.AreaProfile in
#check exists_recoverable_area_minimizer_with_moment_multipliers
open RicciFlowSharpEstimate.Analysis in
#check second_order_weak_euler_flux
open RicciFlowSharpEstimate.Geometry.AreaProfile in
#check weakProbeSecondCoefficient
open RicciFlowSharpEstimate.Geometry.AreaProfile in
#check weakProbeFirstCoefficient
open RicciFlowSharpEstimate.Geometry.AreaProfile in
#check weakProbeZerothCoefficient
open RicciFlowSharpEstimate.Geometry.AreaProfile in
#check weakMeridionalPairingDensity_eq_probe_coefficients
open RicciFlowSharpEstimate.Geometry.AreaProfile in
#check IsRecoverableAreaCompetitor.weak_probe_euler_coefficients_integrable
open RicciFlowSharpEstimate.Geometry.AreaProfile in
#check weakProbeEulerFlux
open RicciFlowSharpEstimate.Geometry.AreaProfile in
#check weakProbeEulerMomentum
open RicciFlowSharpEstimate.Geometry.AreaProfile in
#check IsRecoverableAreaCompetitor.probe_euler_flux_of_minimum
open RicciFlowSharpEstimate.Geometry.AreaProfile in
#check exists_recoverable_area_minimizer_with_natural_flux
open RicciFlowSharpEstimate.Analysis in
#check HasParabolicWeakDerivatives.mul_contDiff
open RicciFlowSharpEstimate.Analysis in
#check parabolicGraph_tendsto_mul_contDiff
open RicciFlowSharpEstimate.Geometry.AreaProfile in
#check IsRecoverableAreaCompetitor.normalized_probe_mul
open RicciFlowSharpEstimate.Geometry.AreaProfile in
#check IsRecoverableAreaCompetitor.weak_probe_mul_equation_of_minimum
open RicciFlowSharpEstimate.Geometry.AreaProfile in
#check weakMeridionalPicone_density_identity
open RicciFlowSharpEstimate.Geometry.AreaProfile in
#check meridionalAction_mul_sub_pairing_eq_picone
open RicciFlowSharpEstimate.Geometry.AreaProfile in
#check meridionalAction_ge_mass_of_ground_state
open RicciFlowSharpEstimate.Geometry.AreaProfile in
#check IsRecoverableAreaCompetitor.picone_identity_of_minimum
open RicciFlowSharpEstimate.Analysis in
#check HasWeakDerivOn.exists_integral_representative_Ioo
open RicciFlowSharpEstimate.Analysis in
#check HasWeakDerivOn.exists_continuous_representative_Ioo
open RicciFlowSharpEstimate.Analysis in
#check HasWeakDerivOn.absolutelyContinuousOnInterval
open RicciFlowSharpEstimate.Analysis in
#check HasWeakDerivOn.integral_eq_sub_of_continuousOn
open RicciFlowSharpEstimate.Analysis in
#check HasWeakDerivOn.hasDerivAt_of_continuousOn
open RicciFlowSharpEstimate.Analysis in
#check HasWeakDerivOn.contDiffOn_one_of_continuousOn
open RicciFlowSharpEstimate.Analysis in
#check HasWeakDerivOn.ae_hasDerivAt_of_continuousOn
open RicciFlowSharpEstimate.Analysis in
#check HasParabolicWeakDerivatives.contDiffOn_one_of_continuousOn
open RicciFlowSharpEstimate.Analysis in
#check not_exists_parabolicWeakDerivatives_abs_sub
open RicciFlowSharpEstimate.Geometry.AreaProfile in
#check IsRecoverableAreaCompetitor.primitive_weak_derivatives
open RicciFlowSharpEstimate.Geometry.AreaProfile in
#check IsRecoverableAreaCompetitor.primitive_local_regularity
open RicciFlowSharpEstimate.Geometry.AreaProfile in
#check IsRecoverableAreaCompetitor.probe_first_order_system_of_minimum
open RicciFlowSharpEstimate.Geometry.AreaProfile in
#check nonneg_of_meridionalOperator_nonpos
open RicciFlowSharpEstimate.Geometry.AreaProfile in
#check pos_of_meridionalOperator_neg
open RicciFlowSharpEstimate.Geometry.AreaProfile in
#check meridionalAction_ge_mass_of_negative_source
open RicciFlowSharpEstimate.Analysis in
#check eq_zero_of_integrableOn_div_left
open RicciFlowSharpEstimate.Analysis in
#check eq_zero_of_integrableOn_div_right
open RicciFlowSharpEstimate.Analysis in
#check nonneg_of_divergence_inequality
open RicciFlowSharpEstimate.Geometry.AreaProfile in
#check weakProbeDerivativeFlux
open RicciFlowSharpEstimate.Geometry.AreaProfile in
#check IsRecoverableAreaCompetitor.derivative_flux_absolutelyContinuous
open RicciFlowSharpEstimate.Geometry.AreaProfile in
#check IsRecoverableAreaCompetitor.nonneg_of_weakMeridionalOperator_nonpos
open RicciFlowSharpEstimate.Analysis in
#check pos_of_divergence_inequality_of_nonneg
open RicciFlowSharpEstimate.Geometry.AreaProfile in
#check IsRecoverableAreaCompetitor.pos_of_weakMeridionalOperator_nonpos
open RicciFlowSharpEstimate.Geometry.AreaProfile in
#check probeMass_neg
open RicciFlowSharpEstimate.Geometry.AreaProfile in
#check weakMeridionalOperator_neg
open RicciFlowSharpEstimate.Geometry.AreaProfile in
#check weakMeridionalAction_neg
open RicciFlowSharpEstimate.Geometry.AreaProfile in
#check IsRecoverableAreaCompetitor.neg_probe
open RicciFlowSharpEstimate.Geometry.AreaProfile in
#check smoothAreaInfimum_nonneg_iff_rotationalSafeCap
open RicciFlowSharpEstimate.Geometry.AreaProfile in
#check smoothAreaInfimum_neg_of_rotationalThreshold_lt
open RicciFlowSharpEstimate.Geometry.AreaProfile in
#check IsRecoverableAreaCompetitor.of_curvature_cap
open RicciFlowSharpEstimate.Geometry in
#check mem_rotationalSafeCaps_of_lt_rotationalThreshold
open RicciFlowSharpEstimate.Geometry in
#check rotationalThreshold_mem_rotationalSafeCaps
open RicciFlowSharpEstimate.Geometry.AreaProfile in
#check smoothAreaInfimum_rotationalThreshold
open RicciFlowSharpEstimate.Geometry.AreaProfile in
#check exists_zero_action_recoverable_area_minimizer
"""


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output-dir", type=Path, required=True)
    parser.add_argument("--reuse-receipt", type=Path,
                        help="Reuse unchanged successful source elaborations from a prior receipt")
    args = parser.parse_args()
    output = args.output_dir.resolve()
    if args.reuse_receipt and args.reuse_receipt.resolve().parent == output:
        raise ValueError("Reuse requires a distinct output directory")
    output.mkdir(parents=True, exist_ok=True)
    (output / "receipt.json").unlink(missing_ok=True)
    inputs = [ROOT / "RicciFlowSharpEstimate.lean", ROOT / "lakefile.toml",
              ROOT / "lean-toolchain", ROOT / "lake-manifest.json", Path(__file__).resolve()]
    inputs += [ROOT / (module.replace(".", "/") + ".lean") for module in MODULES]
    hashes = {str(path.relative_to(ROOT)): digest(path) for path in inputs}
    commands = []

    def run(label, command, silent=False):
        result = subprocess.run(command, cwd=ROOT, text=True, stdout=subprocess.PIPE,
                                stderr=subprocess.STDOUT, timeout=180)
        (output / (label + ".txt")).write_text(result.stdout)
        commands.append({"label": label, "command": command, "exit_code": result.returncode,
                         "output_sha256": digest(output / (label + ".txt"))})
        if (result.returncode or "warning:" in result.stdout or "error:" in result.stdout
                or (silent and result.stdout.strip())):
            print(result.stdout, end="")
            raise RuntimeError(f"Native check failed: {label}")
        return result.stdout

    run("root-build", ["lake", "build"])
    version = run("lean-version", ["lake", "env", "lean", "--version"])
    lean_path = Path(run("lean-path", ["lake", "env", "which", "lean"]).strip())
    dependency_state = {}
    manifest = json.loads((ROOT / "lake-manifest.json").read_text())
    for package in manifest["packages"]:
        package_path = ROOT / manifest["packagesDir"] / package["name"]
        revision = subprocess.check_output(
            ["git", "-C", str(package_path), "rev-parse", "HEAD"], text=True).strip()
        if revision != package["rev"]:
            raise RuntimeError(f"Dependency revision mismatch: {package['name']}")
        subprocess.run(["git", "-C", str(package_path), "diff", "--quiet", "HEAD"], check=True)
        dependency_state[package["name"]] = {"revision": revision, "tracked_sources_clean": True}
    reusable = {}
    if args.reuse_receipt:
        prior_path = args.reuse_receipt.resolve()
        prior = json.loads(prior_path.read_text())
        fixed = ["lakefile.toml", "lean-toolchain", "lake-manifest.json"]
        prior_modules = [p for p in prior["source_hashes"]
                         if p.startswith("RicciFlowSharpEstimate/") and p.endswith(".lean")]
        if not prior_modules or any(hashes.get(p) != prior["source_hashes"][p]
                                    for p in fixed + prior_modules):
            raise RuntimeError("Reuse requires unchanged prior sources and configuration")
        if (prior["lean_binary_sha256"] != digest(lean_path)
                or prior["dependencies"] != dependency_state):
            raise RuntimeError("Reuse compiler or dependencies differ")
        for entry in prior["commands"]:
            command = entry["command"]
            if not command:
                continue
            source = Path(command[-1])
            if not source.is_relative_to(ROOT):
                continue
            relative = str(source.relative_to(ROOT))
            if relative not in prior_modules:
                continue
            if [x for x in command if x.startswith("-D")] != OPTIONS:
                raise RuntimeError("Reuse elaboration or linter options differ")
            raw = prior_path.parent / (entry["label"] + ".txt")
            if (entry["exit_code"] or digest(raw) != entry["output_sha256"]
                    or raw.read_text().strip()):
                raise RuntimeError("Reuse source evidence is not silent and successful")
            reusable[relative] = (entry, raw, prior_path, digest(prior_path))
    for module in MODULES:
        relative = module.replace(".", "/") + ".lean"
        if relative in reusable:
            entry, raw, prior_path, prior_hash = reusable[relative]
            target = output / (entry["label"] + ".txt")
            if raw.resolve() == target.resolve():
                raise RuntimeError("Reuse requires a distinct output directory")
            shutil.copyfile(raw, target)
            commands.append({**entry, "reused_from": {
                "receipt": (str(prior_path.relative_to(ROOT)) if prior_path.is_relative_to(ROOT)
                            else str(prior_path)), "sha256": prior_hash}})
            continue
        run(module.rsplit(".", 1)[1].lower(),
            ["lake", "env", "lean", *OPTIONS, str(ROOT / (module.replace(".", "/") + ".lean"))],
            silent=True)
    with tempfile.TemporaryDirectory(prefix="math-target-") as scratch:
        for label, source, silent in [
            ("linters", LINT_DRIVER, True), ("axioms", AXIOM_DRIVER, False),
            ("signatures", SIGNATURE_DRIVER, False),
        ]:
            path = Path(scratch) / (label.capitalize() + ".lean")
            path.write_text(source)
            run(label, ["lake", "env", "lean", *OPTIONS, str(path)], silent=silent)
            commands[-1]["driver_sha256"] = digest(path)
    if hashes != {str(path.relative_to(ROOT)): digest(path) for path in inputs}:
        raise RuntimeError("Inputs changed during native validation")
    receipt = {
        "source_hashes": hashes, "platform": platform.platform(), "lean_version": version.strip(),
        "lean_binary_sha256": digest(lean_path), "dependencies": dependency_state,
        "commands": commands, "allowed_axioms": ["propext", "Classical.choice", "Quot.sound"],
        "declaration_linters": ["unusedArguments", "simpNF", "synTaut"],
        "defLemma_replacement": "Native getConstInfo/Meta.isProp inspection of declaration kinds",
        "independent_review": "pending outer review; native evidence alone is not suite acceptance",
    }
    (output / "receipt.json").write_text(json.dumps(receipt, indent=2) + "\n")
    print(f"Native checks passed. Evidence: {output}")


if __name__ == "__main__":
    main()
