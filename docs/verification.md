# Native verification

From the repository root, using the pinned dependencies and toolchain:

```sh
python3 scripts/check_native.py --output-dir /tmp/rfse-native-evidence
```

The script first builds the root aggregate, then elaborates each canonical source
afresh with the repository options,
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

The root aggregate is a real consumer of all twenty-one current modules. Importing it is required
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
Independent review of the new layers is pending. All mandatory open mathematics is recorded
in [the suite status](mathematical-status.md).
