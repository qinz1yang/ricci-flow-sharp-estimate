# Theorem-to-paper map

The manuscript has not yet been written. This map distinguishes the native
foundation from prospective paper claims; it does not certify the full suite.
All names below use namespace `RicciFlowSharpEstimate.Variational`.

| Mathematical statement | Canonical Lean declaration | Role / acceptance |
|---|---|---|
| Existence and uniqueness of the cap parameter for every `C≥1` | `existsUnique_capParameter` in `Variational/Parameters.lean` | Native foundation; outer review pending. |
| Canonical parameter satisfies its equation; endpoint is exactly `C=1` | `capParameter_spec`, `capParameter_eq_one_iff` | Native producer and endpoint facts; outer review pending. |
| Exact deficit for two profiles continuous only on `[0,1]` | `pairFunctional_sub_eq_integral_marginal` in `Variational/PairFunctional.lean` | Native analytic engine with actual triangular kernel and derived marginal. |
| First variation is the actual marginal pairing | `pairFirstVariation_eq_integral_marginal` | Native Fubini bridge used by explicit calibration. |
| Exponential remainder is nonnegative | `pairRemainder_nonneg` | Native convexity fact; no cap or optimizer assumption. |
| First-order sign certifies a comparison | `pairFunctional_le_of_firstVariation_nonneg` | Conditional analytic criterion, not a solved optimizer headline. |
| Exterior values and additive constants do not alter the functional | `pairFunctional_congr`, `pairFunctional_add_const` | Native domain/invariance API. |
| Actual admissibility, explicit marginal, all-cap value | No native declaration yet | Mandatory next variational layer. |
| Equality iff the canonical optimizer; contact nonsmoothness | No native declaration yet | Mandatory. |
| Explicit positive L² stability and hemisphere near-symmetry | No native declaration yet | Mandatory. Source-only derivation retained. |
| Smooth metric/pole producers, canonical section jets, Haar split and equality | No native declaration yet | Mandatory geometric dependencies. |
| Exact CK threshold, full smooth equality, smooth supercritical witnesses | No native declaration yet | Mandatory. |
| Plateau instability, correct recovery and strict threshold separation | No native declaration yet | Mandatory. |

Only matched, accepted statements may enter the eventual paper as established
results. The conditional first-order criterion must not be presented as the
explicit all-cap minimum. Geometric claims must retain the same metric,
section producers, pullback maps, curvature bounds and quantifiers.
