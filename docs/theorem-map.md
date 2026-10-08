# Theorem-to-paper map

The working manuscript is [paper/exponential_pair.tex](../paper/exponential_pair.tex).
It contains the variational solution, explicit L² stability, hemisphere symmetry,
smooth balanced-profile metric construction, cylinder pullback and volume/height identities.
The Hodge/Haar, CK and separation
sections remain unwritten. This map does
not certify the full suite.
Names use namespace `RicciFlowSharpEstimate.Variational` unless stated otherwise.
The prefixes `Geometry` and `Analysis` below are relative to `RicciFlowSharpEstimate`.
The analytic statements and current manuscript passed scoped independent Round 1
review at `2302ad1`; the smooth metric producer passed Round 2 review at `76143bb`.
Subsequent geometric development requires its own review.

| Mathematical statement | Canonical Lean declaration | Role / acceptance |
|---|---|---|
| Existence and uniqueness of the cap parameter for every `C≥1` | `existsUnique_capParameter` in `Variational/Parameters.lean` | Native foundation; independent review passed. |
| Canonical parameter satisfies its equation; endpoint is exactly `C=1` | `capParameter_spec`, `capParameter_eq_one_iff` | Native producer and endpoint facts; independent review passed. |
| Exact deficit for two profiles continuous only on `[0,1]` | `pairFunctional_sub_eq_integral_marginal` in `Variational/PairFunctional.lean` | Native analytic engine with actual triangular kernel and derived marginal. |
| First variation is the actual marginal pairing | `pairFirstVariation_eq_integral_marginal` | Native Fubini bridge used by explicit calibration. |
| Exponential remainder is nonnegative | `pairRemainder_nonneg` | Native convexity fact; no cap or optimizer assumption. |
| First-order sign certifies a comparison | `pairFunctional_le_of_firstVariation_nonneg` | Conditional analytic criterion, not a solved optimizer headline. |
| Exterior values and additive constants do not alter the functional | `pairFunctional_congr`, `pairFunctional_add_const` | Native domain/invariance API. |
| Strict growth of the canonical parameter with the cap | `strictMonoOn_capParameter`, `one_lt_capParameter` | Native candidate dependency. |
| Actual contact ordering and exact matching identities | `contact_bounds`, `one_sub_upperContact_sq`, `lowerContact_div_parameter` in `Variational/Contacts.lean` | Native for the stated real parameter domains. |
| Actual free-arc primitives, endpoints and oriented integrals | `hasDerivAt_freeLeftPrimitive`, `hasDerivAt_freeRightPrimitive`, `integral_freeExponential`, `integral_two_mul_div_freeExponential` in `Variational/FreeArc.lean` | Native on positive scale/coordinate domains; endpoint identities retain their natural hypotheses. |
| Actual continuous candidate, its literal piecewise formula and cap bounds | `obstacleExponential_eq_piecewise`, `obstacleLogProfile_admissible` in `Variational/ObstacleProfile.lean` | Native admissibility; not a claim of optimality. |
| Candidate endpoint and exact strict-contact condition | `obstacleLogProfile_one`, `contact_separation_iff` | Native, including `C=1`. |
| Exponential remainder dominates a positive quadratic term | `RicciFlowSharpEstimate.Analysis.exp_tangent_quadratic_lower` in `Analysis/ExponentialRemainder.lean` | Native for `m≤x,y`, with both endpoint orders. Not the integrated L² stability bound. |
| Actual joined-profile prefix/tail integrals on all three regions | `obstaclePrefix_eq_low/free/high`, `obstacleTail_eq_low/free/high` in `Variational/ObstaclePrimitives.lean` | Native for all `q≥1`, including coincident contacts. |
| Actual triangle/interval correspondence and marginal support | `pairFunctional_eq_intervalIntegral`, `pairMarginal_eq_intervalIntegrals`, `pairMarginal_eq_zero_of_not_mem`, `integrable_pairMarginal` in `Variational/PairIteration.lean` | Native Fubini and endpoint-measure bridge; interval continuity supplies genuine integrability. |
| Three exact candidate marginals and obstacle signs | `pairMarginal_obstacleLogProfile_low/free/high`, `obstacle_marginal_mul_sub_nonneg` in `Variational/Calibration.lean` | Native formulas `3(α²−v²)`, `0`, `−3(v−β)(v+1/(3β))`. |
| Explicit candidate minimizes at every cap | `pairFunctional_obstacleLogProfile_le` | Native for every interval-continuous admissible competitor; the first-variation sign is proved. |
| Full exact all-cap value and direct `C=1` value | `pairFunctional_obstacleLogProfile_eq`, `pairFunctional_obstacleLogProfile_one` in `Variational/OptimalValue.lean` | Native evaluation of the actual triangular functional. |
| Vanishing actual remainder iff interval difference is constant | `pairRemainder_eq_zero_iff` in `Variational/PairRigidity.lean` | Native integrability, open-set positive measure and endpoint-continuity argument. |
| Four exact one-sided contact derivatives; both derivative jumps | `hasDerivWithinAt_obstacleLogProfile_lowerContact_Iic/Ici`, `hasDerivWithinAt_obstacleLogProfile_upperContact_Iic/Ici`, both `not_differentiableAt_...` in `Variational/ContactRegularity.lean` | Native for the actual profile. Inward derivatives and jumps require `C>1`. |
| Full bound and equality exactly on `[0,1]` | `pairFunctional_ge_closedForm`, `pairFunctional_eq_closedForm_iff` in `Variational/OptimizerRigidity.lean` | Native. The two obstacles force the actual remainder constant to be zero. |
| Strict bound for admissible competitors differentiable on `(0,1)` at `C>1` | `pairFunctional_obstacleLogProfile_lt_of_differentiableOn` | Native exclusion of attainment of the continuous-class minimum. It does not assert smooth approximation or a geometric equality classification. |
| Actual pair remainder controls the quadratic integral with coefficient `1/(2C)` | `pairRemainder_ge_quadratic_integral` in `Variational/RemainderCoercivity.lean` | Native for two continuous cap-admissible profiles; actual triangle integrability is proved. |
| Exact centered weighted variance and coercivity | `pairQuadratic_eq_centered_integrals`, `integral_unitCentered_sq_le_pairQuadratic` in `Variational/WeightedVariance.lean` | Native actual mean/primitive identity; no derivative of the competitor. |
| Full lower-obstacle weight has mass one and squared mass `6/(5α)` | `integral_lowerObstacleWeight`, `integral_lowerObstacleWeight_sq` in `Variational/ObstacleWeight.lean` | Native exact polynomial moments for `0<α≤1`. |
| Actual first variation controls the weighted error | `integral_lowerObstacleWeight_error_sq_le` in `Variational/ObstacleAnchoring.lean` | Native consequence of actual obstacle values and calibration, with no assumed anchor. |
| Variance plus a normalized weight controls the constant mode | `RicciFlowSharpEstimate.Analysis.integral_sq_le_of_variance_anchor` in `Analysis/WeightedAnchor.lean` | Native general compact-interval engine; continuity supplies all product integrability. |
| Explicit positive cap-dependent L² stability | `stabilityConstant_pos`, `pairFunctional_deficit_controls_L2` in `Variational/Stability.lean` | Native coefficient `[12C/(5α)+log C/(2α³)]⁻¹`; cap one handled directly. Independent review passed. |
| Full-interval even-extension, reflection and symmetrization bounds | `hemisphereDeficit_controls_evenExtension`, `hemisphereDeficit_controls_reflection`, `hemisphereDeficit_controls_symmetrization` in `Variational/HemisphereStability.lean` | Native bounds `D/c`, `4D/c`, `D/c`; no reflection or balance assumption. Geometry is a separate consumer. |
| Global smooth factor at the two distinct endpoints | `RicciFlowSharpEstimate.Analysis.exists_contDiff_one_sub_sq_factor_of_roots` in `Analysis/SmoothFactor.lean` | Two applications of released native Hadamard factorization; no new assumption. |
| Actual balance, moment coordinate and warping integral, smoothness and strict interior positivity | `RicciFlowSharpEstimate.Geometry.RotationalProfile.momentCoordinate_hasDerivAt`, `warp_hasDerivAt`, `momentCoordinate_strictMonoOn`, `warp_pos_of_balance`, `warp_contDiff` in `Geometry/RotationalProfile.lean` | Native analytic producer; pole derivative ratios and constant-profile formulas included. |
| Both globally smooth removable pole factors, positivity and endpoint values | `RicciFlowSharpEstimate.Geometry.RotationalProfile.exists_smooth_positive_warp_factor`, `exists_poleData` in `Geometry/RotationalPoleData.lean` | Native producer retains `D.a=a`; factors are proved from the original natural hypotheses. |
| Actual sphere height differential and its tangent bound | `RicciFlowSharpEstimate.Geometry.heightOneForm_apply`, `HeightMetricCoefficients.heightOneForm_sq_le` in `Geometry/RotationalSphereMetric.lean` | Actual unit sphere, derivative and round metric; no arbitrary covector or jet. |
| Genuine smooth metric and exact profile-specific tensor law | `RicciFlowSharpEstimate.Geometry.exists_metric_of_smooth_positive_balanced_profile`, `RotationalProfile.PoleData.metric_inner` in `Geometry/BalancedSphereMetric.lean` | Native positive metric with original profile and metric tying equations; independent review passed. |
| Positive constant profiles give the scaled round metric | `RicciFlowSharpEstimate.Geometry.RotationalProfile.PoleData.constant_metric_inner` | Actual tangent-vector evaluation law; nonvacuous family. |
| Actual smooth cylinder map, its differential and pullback tensor | `Geometry.cylinderMap_contMDiff`, `cylinderMap_dIncl_mfderiv`, `cylinderMap_mfderiv_injective`, `RotationalProfile.PoleData.cylinderMap_metric_inner` in `Geometry/RotationalCoordinates.lean` | Physical height and angle, actual manifold derivative, original metric. |
| Rank-one Gram determinant over a commutative ring | `LinearMap.det_smul_add_rankOne_gram_fin_two` in `LinearAlgebra/RankOneDeterminant.lean` | Natural algebraic engine; no nonsingularity assumption. |
| Actual metric determinant, density and volume measure | `Geometry.RotationalProfile.PoleData.det_chartGramMatrix_metric`, `chartDensity_metric`, `volume_metric_eq_withDensity`, `integral_volume_metric` in `Geometry/RotationalVolume.lean` | Original `D.metric` and `D.a(sphereHeight)` throughout. |
| Exact round and profile-weighted height disintegration | `Geometry.integral_round_height` in `Geometry/SphereHeightIntegral.lean`; `RotationalProfile.PoleData.integral_height_metric` in `Geometry/RotationalVolume.lean` | Actual Riemannian measures; `2*pi` factor; interval-local continuity. |
| Intrinsic scalar curvature from an actual radial diagonal chart two-jet | `Geometry.metricScalarAt_eq_radialDiagonalJet` in `Geometry/RotationalDiagonalCurvature.lean` | Genuine metric/jet engine with internal regularity and nonvanishing proofs; not yet the sphere-curvature headline. |
| Actual height-profile derivative substitution | `Geometry.RotationalProfile.PoleData.radial_curvature_identity` in `Geometry/RotationalCurvatureProfile.lean` | Actual derivatives of `warp a` and `a^2/warp a`; intrinsic geometric consumer remains next. |
| Intrinsic sphere curvature, canonical section jets, Haar split and equality | No native final declaration yet | Mandatory geometric dependencies. |
| Exact CK threshold, full smooth equality, smooth supercritical witnesses | No native declaration yet | Mandatory. |
| Plateau instability, correct recovery and strict threshold separation | No native declaration yet | Mandatory. |

The manuscript's current statements are tied to native proofs as follows:

| TeX label | Exact native coverage |
|---|---|
| `thm:minimum` | `existsUnique_capParameter`, `obstacleLogProfile_admissible`, `pairFunctional_ge_closedForm`, `pairFunctional_eq_closedForm_iff`, `pairFunctional_obstacleLogProfile_one` |
| `lem:parameter` | `strictMonoOn_capParameter`, `capParameter_eq_one_iff`, `contact_bounds`, `upperContact_sq_eq`, `one_sub_upperContact_sq`, `lowerContact_div_parameter`, `contact_separation_iff` |
| `lem:primitives` | All six `obstaclePrefix_eq_...` / `obstacleTail_eq_...` and three `pairMarginal_obstacleLogProfile_...` formulas |
| `lem:deficit` | `pairFunctional_sub_eq_integral_marginal`, `pairMarginal_eq_intervalIntegrals`, `pairMarginal_eq_zero_of_not_mem`, `pairRemainder_nonneg`, `pairRemainder_eq_zero_iff` |
| `thm:contacts` | Four one-sided derivative theorems, both contact nondifferentiability theorems, and `pairFunctional_obstacleLogProfile_lt_of_differentiableOn` |
| `lem:quadratic` | `RicciFlowSharpEstimate.Analysis.exp_tangent_quadratic_lower` |
| `lem:variance` | `pairQuadratic_eq_centered_integrals`, `integral_unitCentered_sq_le_pairQuadratic`, actual `unitMean`, `unitCentered`, `centeredPrimitive` |
| `thm:stability` | `stabilityConstant_pos`, `pairFunctional_deficit_controls_L2`, `pairRemainder_ge_quadratic_integral`, both obstacle-weight moments, `integral_lowerObstacleWeight_error_sq_le`, `RicciFlowSharpEstimate.Analysis.integral_sq_le_of_variance_anchor` |
| `cor:hemispheres` | All three `hemisphereDeficit_controls_...` theorems; actual `hemisphereDeficit`; substitution and squared-error identities in `Analysis/ReflectionEnergy.lean` |
| `lem:pole-factors` | `Analysis.exists_contDiff_one_sub_sq_factor_of_roots`; `Geometry.RotationalProfile` actual integral definitions, derivative/smoothness/monotonicity/endpoint/positivity theorems; `exists_poleData` and `PoleData.constant` |
| `thm:smooth-metric` | `Geometry.exists_metric_of_smooth_positive_balanced_profile`; actual `heightOneForm_apply`, `HeightMetricCoefficients.heightOneForm_sq_le`, `RotationalProfile.PoleData.metric_inner`, `radial_identity`, and `constant_metric_inner` |
| `lem:cylinder-metric` | `Geometry.cylinderMap_contMDiff`, `sphereHeight_cylinderMap`, `cylinderMap_dIncl_mfderiv`, `cylinderMap_round_inner`, `cylinderMap_mfderiv_injective`, `RotationalProfile.PoleData.cylinderMap_metric_inner` |
| `thm:volume-height` | `Geometry.round_grad_sphereHeight_inner_self`; `RotationalProfile.PoleData.volume_metric_eq_withDensity`; `Geometry.integral_round_height`; `RotationalProfile.PoleData.integral_height_metric` |

The manuscript uses real functions continuous only on `[0,1]` for the one-sided
problem and `[-1,1]` for the hemisphere consequences, with interval-local constraints
and equality, matching the native quantifiers. The metric construction requires
globally smooth profiles positive on `[-1,1]`, exactly as in the native producer. It does
not claim that the infimum over a smooth class is the same value without a smooth
approximation theorem. No TeX engine was available in the working environment, so
typesetting has not been validated.

Independent statement/manuscript acceptance of later geometric claims remains required. The conditional
first-order criterion is now specialized through the actual calibration, rather
than being presented alone as the minimum. Geometric claims must retain the same metric,
section producers, pullback maps, curvature bounds and quantifiers.
