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
      poleData ++ `oneFormDissipation_eq_zero_iff_of_conformalKilling_curvature_bounds
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
