# Blackbox and axiom registry

No mathematical blackbox or project axiom has been introduced.

All twenty-six current analytic, variational and geometric modules depend transitively only on
`propext`, `Classical.choice`, and `Quot.sound`. The native report checks every
project declaration selected by its defining module, including private/generated
declarations, using Lean's `collectAxioms` (the engine used by `#print axioms`).
It rejects any axiom outside that three-name allowlist. This evidence is bound to
source and dependency-manifest hashes; it is not a textual search for `sorry`.

The [current native report](evidence/round-2/axioms.txt) covers 404 declarations.
This includes the released Hadamard factorization and smooth metric construction
as actual transitive dependencies of the new pole and sphere-metric producers.

The unformalized derivations and historical reference statements are not
blackboxes and are not imported assumptions. Their native proof obligations
remain open. If a sourced blackbox becomes necessary, a separate registry entry
must preserve the exact source statement and citation, literal translation,
binder dictionary and explicit theorem dependencies; equivalences and
specializations require their own proofs.
