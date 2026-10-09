# Ricci flow sharp estimates

A new pure mathematics and Lean project on sharp rotational curvature pinching
for one-form Hodge dissipation. The complete theorem suite is still open.

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
scalarization of that same complete action is now native as well. Scalar Haar
compatibility and its positive gap, nonzonal positivity/equality, geometric
sharpness and separation remain open.

Lean/Mathlib: `v4.35.0-rc3`. DifferentialGeometry: released `v0.1.4`, with the
resolved revision pinned in `lake-manifest.json`.

- [Mathematical scope, dependencies and exact frontier](docs/mathematical-status.md)
- [Theorem-to-paper map](docs/theorem-map.md)
- [Working manuscript](paper/exponential_pair.tex)
- [Native verification and reproduction](docs/verification.md)
- [Blackbox and axiom registry](docs/blackbox-registry.md)

```sh
python3 scripts/check_native.py --output-dir /tmp/rfse-native-evidence
```
