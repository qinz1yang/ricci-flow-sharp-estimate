# Blackbox and axiom registry

No mathematical blackbox or project axiom has been introduced.

All 114 currently checked analytic, variational and geometric modules depend transitively only on
`propext`, `Classical.choice`, and `Quot.sound`. The native report checks every
project declaration selected by its defining module, including private/generated
declarations, using Lean's `collectAxioms` (the engine used by `#print axioms`).
It rejects any axiom outside that three-name allowlist. This evidence is bound to
source and dependency-manifest hashes; it is not a textual search for `sorry`.

The [current native report](evidence/round-12/axioms.txt) covers 1904 declarations,
including 735 private declarations and relevant generated constants.
The [accepted CK safety report](evidence/round-11/axioms.txt) covers the preceding
107-module, 1867-declaration layer at `ae5dc91`.
The [accepted original-remainder report](evidence/round-10/axioms.txt) covers
the preceding 98-module, 1777-declaration layer at `0473a6a`.
The [accepted positive-scalar report](evidence/round-9/axioms.txt) covers the
preceding 94-module, 1748-declaration layer at `da47567`.
The [accepted Round 8 continuation](evidence/round-8-haar-scalars/axioms.txt)
covers the preceding 86-module, 1609-declaration layer at `659006b`.
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
The accepted scalar Haar layer additionally checks same-map trace/curl naturality,
actual circle preservation of area, and literal scalar averaging, including
zero means and pole values of the original remainder.
The new positive scalar layer checks the native Fourier/Parseval dependency,
genuine polar maps and derivatives, metric inverse Gram matrix, actual volume
conversion, uniform C2 endpoint bounds, bounded-quotient integrability, the
weighted square completion and Fubini. The final scalar headline supplies no
coordinate, finite-energy or equivalent inequality premise.
The remainder layer checks the actual Riemannian volume's finiteness and positive
measure on nonempty open sets, continuity/integrability and pointwise rigidity
of weighted scalar/tensor energies. It uses the existing actual derivative
decomposition, differentiates the genuine zero section, and substitutes into
the original four-term action to obtain the positive curvature energy. The
final Haar-remainder equality and same-probe zonal bound accept no supplied
derivative vanishing, sign law, equality law or replacement measure.

The new CK layer checks actual triangular Fubini and reciprocal-log calculus,
the southern balance substitution, the canonical cap parameter and optimal-value
comparison, and the exact constant-zonal action. The CK predicate is the zero
Ahlfors part of the actual metric derivative. Its native linearity/naturality,
actual meridian reflection and parallel Hodge norm laws yield interval-only
probe constancy and genuine invariant CK classification. Haar preservation,
the accepted full split and original remainder equality give safety and full
zero equality for produced metrics at the derived cap. The curvature consumer
uses the same intrinsic curvature and actual height coverage. No equation,
classification or sign conclusion is supplied as an extra hypothesis.
That CK safety layer passed Round 11 independent review.

The new recovery layer checks the released normalized smooth convolution,
actual mass-one/convex-range and uniform-approximation proofs, and reflection
symmetrization. The interval clamp retains the original reciprocal optimizer,
with exact box/evenness and continuous balanced-profile integral identities.
The warp-ratio integral has genuine integrability, a common positive-box
domination proof and an explicit uniform Lipschitz estimate; no derivative
convergence is assumed. Each smooth approximant is tied to the existing
PoleData producer by D_n.a=a_n. Actual meridional action identities give the
limit, and the original critical comparison and CK safety give the negative
supercritical witness and positive fixed-probe critical sequence.
The stability layer is an exact consumer of the actual zonal action and all
three accepted hemisphere estimates, including factor four and zero coefficients.
No smooth metric is assigned to the nonsmooth limit. This source-bound evidence
still does not certify the missing conjugated class projector, full-class
safe-cap characterization or derivative-sensitive structural separation.

The manuscript cites David Jerison's MIT 18.103 Fall 2013 notes,
[*Fourier Series, Part 1*, Corollary 2, p. 5](https://ocw.mit.edu/courses/18-103-fourier-analysis-fall-2013/1c196caa6307e0be46456cf6dc76b543_MIT18_103F13_fseries1.pdf),
for the conventional Parseval formula. The exact source was inspected. This is
a literature citation, not a new formal blackbox: the native dependency is
Mathlib's proved `hasSum_sq_fourierCoeffOn`, with its actual transitive closure
included in the report.

The unformalized derivations and historical reference statements are not
blackboxes and are not imported assumptions. Their native proof obligations
remain open. If a sourced blackbox becomes necessary, a separate registry entry
must preserve the exact source statement and citation, literal translation,
binder dictionary and explicit theorem dependencies; equivalences and
specializations require their own proofs.
