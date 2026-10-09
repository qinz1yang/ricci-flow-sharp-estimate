# Blackbox and axiom registry

No mathematical blackbox or project axiom has been introduced.

All eighty-two currently checked analytic, variational and geometric modules depend transitively only on
`propext`, `Classical.choice`, and `Quot.sound`. The native report checks every
project declaration selected by its defining module, including private/generated
declarations, using Lean's `collectAxioms` (the engine used by `#print axioms`).
It rejects any axiom outside that three-name allowlist. This evidence is bound to
source and dependency-manifest hashes; it is not a textual search for `sorry`.

The [current native report](evidence/round-8/axioms.txt) covers 1543 declarations.
This includes the released Hadamard factorization and smooth metric construction
as actual transitive dependencies of the pole and sphere-metric producers. It
also checks the actual curvature, local pullback, coordinate and measure dependencies.
The canonical total derivatives, section extension used for uniqueness, smooth
tensor contractions and complete-action dependencies are also in this closure.
The current closure additionally covers the actual meridional Hessian and rough
Laplacian, exact action reduction, smooth derivative pullback and volume naturality,
meridian reflection, and the constructed parallel area form. No historical
scalarization axiom is imported.
The final rotation layer additionally checks the actual smooth metric sharp,
both covariant-derivative commutation laws, rough trace, rotation contractions
and the full zonal identity. Parallelness is proved from the actual area tensor,
and no free first or second jet is accepted by these headlines.
The Haar layer checks the actual jointly smooth circle action, native tensor-fiber
integration, applied manifold derivative/interchange, all canonical operator
intertwining, product integrability and the full four-term self-adjoint split.
The average is tied to literal normalized derivative pullback, not supplied as
an abstract projection. All earlier accepted theorem sources remain unchanged.
The invariant-form layer additionally checks the native Hadamard and Borel
half-line extension route, the actual stereographic maps and their derivatives,
smooth radial/tangential factorization, both-pole height gluing and the final
original-section equality. The quotient extension requires nonvanishing only
on the physical interval. No pole regularity or representation is assumed in
the classification headline, and the Haar/zonal action retains the same probes.
The scalarization layer checks the actual canonical-to-tensor-connection and
metric-pairing bridges, closed-manifold integration by parts, the full covariant
Ricci identity, surface contractions, and the derivative norm splitting. These
prove the literal original-action identity; no scalarization datum or substitute
scalar action is assumed. The historical convenience scalarization axiom is not
imported or used. The rotational consumer derives its area and curvature from D.

The unformalized derivations and historical reference statements are not
blackboxes and are not imported assumptions. Their native proof obligations
remain open. If a sourced blackbox becomes necessary, a separate registry entry
must preserve the exact source statement and citation, literal translation,
binder dictionary and explicit theorem dependencies; equivalences and
specializations require their own proofs.
