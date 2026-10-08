# Ricci flow sharp estimates

A new pure mathematics and Lean project on sharp rotational curvature pinching
for one-form Hodge dissipation. The complete theorem suite is still open.

The native variational development proves the explicit minimum for every
cap `C≥1`, uniqueness on `[0,1]`, the degenerate endpoint, exact contact
derivative jumps, and strictness for differentiable competitors at `C>1`.
It also proves the quadratic exponential estimate needed for stability.
The L² stability and geometric sharpness theorems remain open. The first
foundation layer passed independent review; the new results await review.

Lean/Mathlib: `v4.35.0-rc3`. DifferentialGeometry: released `v0.1.4`, with the
resolved revision pinned in `lake-manifest.json`.

- [Mathematical scope, dependencies and exact frontier](docs/mathematical-status.md)
- [Theorem-to-paper map](docs/theorem-map.md)
- [Working variational manuscript](paper/exponential_pair.tex)
- [Native verification and reproduction](docs/verification.md)
- [Blackbox and axiom registry](docs/blackbox-registry.md)

```sh
python3 scripts/check_native.py --output-dir /tmp/rfse-native-evidence
```
