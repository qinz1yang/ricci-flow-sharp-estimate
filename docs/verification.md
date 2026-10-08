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
the relevant headlines and at least seventy declarations. The candidate-layer
run selects 109 declarations, including all private and generated dependencies.

`unusedArguments`, `simpNF`, and `synTaut` run through Batteries' native linter
engine. This release has no registered `defLemma`; a native declaration-kind
inspection checks that definitions are not propositions and theorems are not
data. No linter is disabled. Syntax/style linters are enabled in ordinary
compilation. The expected header license text is configured for this private,
unlicensed project; all header checks remain active.

The root aggregate is a real consumer of all six current modules. Importing it is required
before the evidence drivers. A cached root build does not replace fresh leaf
elaboration, and successful native validation does not replace independent
mathematical review of the statements.

The first canonical build exposed missing file headers that scratch compilation
had not reported: the release's header linter tests membership in the flat root
aggregate. Both headers were supplied and the canonical layer was rebuilt.
The mathematical proofs and signatures were unchanged by that repair.

The [first-layer evidence](evidence/round-0/receipt.json) passed independent review.
See the newer [candidate-layer receipt](evidence/round-1-candidate/receipt.json),
[axiom closure](evidence/round-1-candidate/axioms.txt), and
[elaborated statements](evidence/round-1-candidate/signatures.txt).
Independent review of that new layer is pending. All mandatory open mathematics is recorded
in [the suite status](mathematical-status.md).
