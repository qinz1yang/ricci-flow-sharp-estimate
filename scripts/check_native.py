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
      poleData ++ `oneFormDissipation_zonal
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
