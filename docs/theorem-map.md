# Theorem-to-paper map

The manuscript has not yet been written. This map distinguishes the native
foundation from prospective paper claims; it does not certify the full suite.
Names use namespace `RicciFlowSharpEstimate.Variational` unless stated otherwise.
The unchanged first-layer statements passed the Round 0 independent review;
new candidate-layer statements remain pending independent acceptance.

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
| Full exact optimal value | No native declaration yet | Mandatory next variational leaf. |
| Equality iff the canonical optimizer; contact nonsmoothness | No native declaration yet | Mandatory. |
| Explicit positive L² stability and hemisphere near-symmetry | No native declaration yet | Mandatory. Source-only derivation retained. |
| Smooth metric/pole producers, canonical section jets, Haar split and equality | No native declaration yet | Mandatory geometric dependencies. |
| Exact CK threshold, full smooth equality, smooth supercritical witnesses | No native declaration yet | Mandatory. |
| Plateau instability, correct recovery and strict threshold separation | No native declaration yet | Mandatory. |

Only matched, accepted statements may enter the eventual paper as established
results. The conditional first-order criterion must not be presented as the
explicit all-cap minimum. Geometric claims must retain the same metric,
section producers, pullback maps, curvature bounds and quantifiers.
