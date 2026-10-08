# Ricci flow sharp estimates

A new pure mathematics and Lean project on sharp rotational curvature pinching
for one-form Hodge dissipation. The complete theorem suite is still open.

The first native layer proves existence and uniqueness of the all-cap
variational parameter, its endpoint characterization, and the exact convex
deficit identity for the actual exponential pair integral, including its
marginal/Fubini formula. It does not yet prove the explicit optimizer or the
geometric sharpness theorems. Independent outer acceptance is pending.

Lean/Mathlib: `v4.35.0-rc3`. DifferentialGeometry: released `v0.1.4`, with the
resolved revision pinned in `lake-manifest.json`.

- [Mathematical scope, dependencies and exact frontier](docs/mathematical-status.md)
- [Theorem-to-paper map](docs/theorem-map.md)
- [Native verification and reproduction](docs/verification.md)
- [Blackbox and axiom registry](docs/blackbox-registry.md)

```sh
python3 scripts/check_native.py --output-dir /tmp/rfse-native-evidence
```
