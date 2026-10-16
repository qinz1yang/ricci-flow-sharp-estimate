# Round 26 bounded source simplifier advice

Scope: the exact additive delta from frozen `ParentAreaWarpCalibration.lean` to `AreaWarpCalibration.lean`, plus new `AreaSlopeMass.lean`, `AreaSlopeCalibration.lean` and `RotationalStrictPinching.lean`. Accepted parent proof bodies were not cleaned or independently re-reviewed. Global AGENTS.md, the frozen recovery contract/attempts/BitLesson and applicable theorem-suite skills were read.

## One minimal suggestion

In the new `AreaSlopeMass.lean` proof of `hmass0`, after the integral-domain rewrites, replace:

```lean
    simpa using integral_congr_ae hmassae
```

with:

```lean
    exact integral_eq_zero_of_ae hmassae
```

The goal is already that the actual mass integral vanishes, and `hmassae` is exactly its a.e. zero integrand. This uses the direct existing theorem instead of congruence followed by simplification. The patch contains only that line. NO CHANGE is proposed elsewhere; in particular, no consolidation with the accepted Bernstein proofs is suggested.

Every theorem statement, coefficient, weak-domain hypothesis and actual object/recovery binding is unchanged. The new comparison still uses genuine strong recovery of the displayed K/r and full action, without identifying separately chosen curvature boxes or assuming minimizing/stationary data. No concrete semantic or API concern was noticed in this focused inspection. The strict inequality `1+sqrt(3/2)<C_rot` remains a bound, not determination. The principal angular-family failure remains separate and receives no claimed positive-result credit.

Lessons preserved: flat-root-header (all private headers and final Root gates), qualified-name-search (no new name or declaration), recovery-limit-witness-ties (same original curvature/probe and recovery passage retained), and lp-tendsto-elaboration (the existing inferred-limit normalization is left intact). This is source advice, not the single configured outer acceptance review.

## Frozen input hashes

All eight bindings match `inputs.json`, checked before and after inspection:

- `AreaWarpCalibration.lean`: `2a042c966734963fa4952ee059b2e9a1c3acba130a52aa5b8796dc7794860eb0`
- `AreaSlopeMass.lean`: `1b2da2de49ab2e0eb5aecb08716aa47a024957dfeb1eab6900f294f38e164ab6`
- `AreaSlopeCalibration.lean`: `b4fb4f54a184ac89a36b1d2cea4ca59aae6e33a21d60e674f196ff969d599924`
- `RotationalStrictPinching.lean`: `31bcc7c01be749883a93d34bc53439b4de2731feadb5c204e43461162beaa717`
- `attempts.md`: `786e58ef2e613ee710b3a2d6d809e271dfd447e960786e7541e6fc81fe4f0f7f`
- `contract.md`: `d7cade72a5d755ca805db5b6ffbac9000175ab06b6bb69b7c5dc83565523030c`
- `bitlesson.md`: `48215551a10642e35fca9e2bcbb8dfa5fba713b266a62d43c5721903e1e83855`
- `ParentAreaWarpCalibration.lean`: `da2cf849ab9809eae696b101a1060fbdc24a68c6a483cee208bf4a985ebe4d0e`

Manifest SHA256: `4b87d5ed7aaa0eafc2e22a6d8460c6931be2e60ec90e70bc9294c06e030c23cd`.
Patch SHA256: `d125a0e637a57e5f542ef4d8ca7208932468b95fbcdd37baa7c6687579e00a0a`.

Status: PROVISIONAL source-only suggestion, uncompiled. No native type/linter/axiom or acceptance evidence is claimed. Root alone chooses/integrates the patch and runs all final gates. No descendants, compiler/Lean/Lake, Git/network, writable Root-cache or changing workspace access occurred.

Report and patch frozen after this write. Assignment and snapshot lease released: no processes or descendants remain, and no further accesses or edits are planned.
