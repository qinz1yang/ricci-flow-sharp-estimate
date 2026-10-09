# Ricci flow sharp estimates

A new pure mathematics and Lean project on sharp rotational curvature pinching
for one-form Hodge dissipation. The finite mathematical suite is natively proved
and passed independent whole-suite acceptance in Round 16 at `2bda267`.

The native variational development proves the explicit minimum for every
cap `C≥1`, uniqueness on `[0,1]`, the degenerate endpoint, exact contact
derivative jumps, and strictness for differentiable competitors at `C>1`.
It also proves explicit positive L² deficit coercivity, including constant-mode
anchoring, and quantitative near-equatorial symmetry without assuming symmetry.
The analytic, sphere-metric, curvature and volume layers passed independent review.
Global meridional/azimuthal forms, unique canonical covariant derivatives, and the
complete four-term action with integrability and polarization passed Round 4 review.
The actual meridional derivatives and complete zonal `2*pi*(J[r]+J[s])` reduction
now have native proofs, including the round value `8*pi/3`, genuine reflection
orthogonality and parallel Hodge rotation. The genuine smooth Haar projector,
canonical-derivative intertwining and complete action split are also native.
Global smooth invariant-form classification and its actual Haar/zonal action
consumer are now native, including both poles. Constructive trace/curl
scalarization of that same complete action and actual scalar Haar compatibility
passed Round 8 independent review at `659006b`.
The positive scalar Haar estimate, including polar endpoints and weighted
integrability, passed Round 9 independent review at `da47567`.
The original nonzonal remainder now has native nonnegativity and equality
exactly at zero remainder. Haar averaging decreases the action, with equality
exactly for invariant forms; the same smooth zonal probes give the corresponding
lower bound and equality case. That layer passed Round 10 review at `0473a6a`.
The actual northern/southern pair-functional substitutions, invariant CK
classification, exact variational critical cap and produced-metric CK safety
with equality only at the zero form now have native proofs. They include
actual curvature bounds and strict positivity of the fixed unit meridional
probe, and passed Round 11 review at `ae5dc91`.
Smooth even box-preserving recovery now produces genuine negative CK witnesses
below every larger cap and a critical sequence whose fixed unit-probe actions
are positive and tend to zero. The exact geometric hemisphere-stability
consumers passed Round 12 review at `58d5dbc`.
The same-map conjugated circle/projector, full Haar geometry, CK safety/equality
and stability now extend to the advertised diffeomorphic-pullback class.
The universal CK safe-cap set is natively exactly `[1,criticalCap]`, and its
supremum has the derived radical/exponential value. This layer passed Round 13
review at `70f0557`, closing AC4 and AC5.
Positive normalized area geometry, its complete action, and a fully tied smooth
geometric realization passed Round 14 native review at `a6843ea`.
The realization exposes
both inverse-coordinate laws, actual probe jets, curvature and the original
`2*pi` action identity. Its manuscript's physical-domain qualification passed Round 15 review.
The actual critical area curvature now has its exact moments, scaled box,
hemisphere shape, positive plateau and zero unit-probe action. A fixed smooth
probe supported as a variation inside that plateau gives negative complete area
action and equals one near both endpoints. That native layer passed Round 15 review.
Strict contraction, symmetric monotone exact-moment recovery and convergence of
the complete action now give a genuine smooth negative original-metric witness
below the CK threshold. Universal all-form cap-one safety and real supremum laws
prove `rotationalThreshold < conformalKillingThreshold` for the same represented
class. This final layer passed independent Round 16 review at `2bda267`.
The complete manuscript is typeset in a [47-page PDF](paper/exponential_pair.pdf),
with no remaining TeX diagnostics. Its new proofs and the global-continuity
qualification of the reciprocal-coordinate lemma passed Round 16 review,
completing independent acceptance of all seven mandatory criteria.

Lean/Mathlib: `v4.35.0-rc3`. DifferentialGeometry: released `v0.1.4`, with the
resolved revision pinned in `lake-manifest.json`.

- [Mathematical scope, dependencies and exact frontier](docs/mathematical-status.md)
- [Theorem-to-paper map](docs/theorem-map.md)
- [Working manuscript](paper/exponential_pair.tex)
- [Typeset manuscript](paper/exponential_pair.pdf)
- [Native verification and reproduction](docs/verification.md)
- [Blackbox and axiom registry](docs/blackbox-registry.md)

```sh
python3 scripts/check_native.py --output-dir /tmp/rfse-native-evidence
```
