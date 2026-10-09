# Native verification

From the repository root, using the pinned dependencies and toolchain:

```sh
python3 scripts/check_native.py --output-dir /tmp/rfse-native-evidence
```

The script first builds the root aggregate, then elaborates each canonical source
with the repository options,
runs declaration checks, queries exact statements, and checks actual transitive
axiom closure. It hashes all project sources in this layer, the root aggregate,
manifest, toolchain declaration, build configuration and verification script,
and rejects a source change during the run. It verifies dependency revisions and
clean tracked dependency sources, and records the Lean executable hash. A prior
success receipt is removed before a new run. Temporary Lean drivers are created
outside project source and deleted afterward. The explicit selectors must contain
the relevant headlines and at least two hundred declarations. Actual audit counts
are recorded at the start of each axiom log, including private/generated declarations.

`unusedArguments`, `simpNF`, and `synTaut` run through Batteries' native linter
engine. This release has no registered `defLemma`; a native declaration-kind
inspection checks that definitions are not propositions and theorems are not
data. No linter is disabled. Syntax/style linters are enabled in ordinary
compilation. The expected header license text is configured for this private,
unlicensed project; all header checks remain active.

The optional `--reuse-receipt` argument reuses successful source elaborations only
when every prior project source, configuration, dependency revision, compiler hash
and semantic `-D` option still matches. Each reused output is verified and records
its prior receipt and hash. Original resource flags remain in the original recorded
commands; they are not semantic Lean options. The aggregate, declaration linters,
signatures and transitive-axiom audit always run again. New or changed source must
be elaborated afresh. Use a distinct output directory for each checkpoint.

The root aggregate is a real consumer of all eighty-two current modules. Importing it is required
before the evidence drivers. A cached root build does not replace fresh leaf
elaboration, and successful native validation does not replace independent
mathematical review of the statements.

The first canonical build exposed missing file headers that scratch compilation
had not reported: the release's header linter tests membership in the flat root
aggregate. Both headers were supplied and the canonical layer was rebuilt.
The mathematical proofs and signatures were unchanged by that repair.

The [first-layer evidence](evidence/round-0/receipt.json) passed independent review.
The [candidate-layer receipt](evidence/round-1-candidate/receipt.json) covers its six-module checkpoint.
The [calibration receipt](evidence/round-1-calibration/receipt.json) covers its nine-module checkpoint.
The final [Round 1 receipt](evidence/round-1/receipt.json),
[axiom closure](evidence/round-1/axioms.txt), and
[elaborated statements](evidence/round-1/signatures.txt) cover all thirteen modules.
The [stability receipt](evidence/continuation-2/receipt.json),
[axiom closure](evidence/continuation-2/axioms.txt), and
[elaborated statements](evidence/continuation-2/signatures.txt) cover all twenty-one modules,
including the actual weighted variance, obstacle anchor, explicit coercivity and hemisphere bounds.
The analytic layers passed scoped independent Round 1 review at `2302ad1`.
The [smooth metric receipt](evidence/round-2/receipt.json),
[axiom closure](evidence/round-2/axioms.txt), and
[elaborated statements](evidence/round-2/signatures.txt) cover all twenty-six modules,
including the smooth balanced-profile pole factors and actual sphere metric.
That producer layer passed scoped independent Round 2 review at `76143bb`.
The [coordinate/volume receipt](evidence/round-3/receipt.json) adds the actual
cylinder pullback, determinant/density laws and exact height integral. Its source
checks reuse the unchanged 26-module receipt and freshly elaborate the six new
modules; declaration and transitive-axiom checks cover the complete aggregate.
The [curvature receipt](evidence/round-3-curvature/receipt.json) extends this to
the exact cylinder range and the intrinsic scalar/sectional curvature of the same
metric on the whole sphere. It reuses the unchanged 32 source checks and freshly
checks the two final modules, root aggregate and all declaration/axiom/signature drivers.
Those coordinate/curvature/volume layers passed scoped Round 3 independent review
at `0a0b115`. The [section/action receipt](evidence/round-4/receipt.json) reuses
the unchanged 34 source elaborations and freshly checks five new modules. The root,
declaration/signature drivers and all 691 transitive axiom closures are checked
for the complete 39-module aggregate. That section, derivative and action layer
passed Round 4 independent review at `4cb46f6`.
The [meridional/symmetry receipt](evidence/round-5-meridional/receipt.json) checks
the complete 50-module aggregate and 1004 defining-module declarations. It reuses
the unchanged 34 source checks from the curvature receipt and freshly elaborates
the remaining sixteen sources, including the comment-only section-extension
attribution correction. The aggregate and all declaration, signature and actual
transitive-axiom drivers run again. The [final zonal receipt](evidence/round-5/receipt.json) extends
that checkpoint to 55 modules and 1083 defining-module declarations. It verifies
the unchanged fifty-source reuse chain, freshly elaborates the final five sources,
and reruns the aggregate and all declaration/signature/axiom drivers. The actual
Hodge rotation, first/second derivative and rough-trace commutation, all four
norm contractions and complete zonal `2*pi*(J[r]+J[s])` identity pass these gates.
The final receipt binds 60 source/configuration/checker inputs and 61 command
outputs. Both Round 5 layers passed independent mathematical and manuscript
review at `da1dd90`. Typesetting and the remaining whole-suite gates stay open.
The [Haar receipt](evidence/round-6/receipt.json) covers the complete 65-module
aggregate and all 1279 defining-module declarations. Its 55 reused source checks
are tied to unchanged accepted bytes; all ten new sources are freshly elaborated.
The aggregate, declaration linters, 232 required selectors, 329 signature queries
and actual transitive-axiom driver run at the new checkpoint. All source and
declaration outputs are silent. The receipt binds 70 inputs and 71 command outputs.
The five conventional Haar claims and exact map passed Round 6 independent review at `43111f9`.
The [invariant-classification receipt](evidence/round-7/receipt.json) extends this
to 72 modules, reusing 65 unchanged accepted source checks and freshly elaborating
seven new sources. The root and all declaration/signature/axiom drivers run again.
All 1433 defining-module declarations, including 553 private declarations, have
permitted transitive axioms only. All 260 required selectors and 357 signature
queries are covered; 77 inputs and 78 command outputs are fingerprinted.
Source and declaration-linter outputs are silent. Those four conventional claims
and their exact mapping passed Round 7 independent review at `8765255`.
The [scalarization receipt](evidence/round-8/receipt.json) covers 82 modules,
reusing 72 unchanged accepted source elaborations and freshly checking ten new
sources. The root and all declaration/signature/axiom drivers run again. The
1543 defining-module declarations include 620 private declarations; every
transitive closure has only permitted foundational axioms. All 291 required
selectors and 388 signature queries are covered. The receipt binds 87 inputs,
88 command outputs and three generated drivers; source and declaration outputs
are silent. Six conventional scalarization claims and their mapping await
independent review. Scalar Haar compatibility and its positive estimate,
unconditional remainder sign/equality, the later CK/separation suite and final
typesetting remain open.
All mandatory open mathematics is recorded
in [the suite status](mathematical-status.md).
