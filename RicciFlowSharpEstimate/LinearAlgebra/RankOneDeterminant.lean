/-
Copyright (c) 2026 Ziyang Qin. All rights reserved.
No license is granted by this file.
Authors: Ziyang Qin
-/
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Basis.Defs
import Mathlib.Tactic.Ring

/-!
# Two-dimensional Gram determinants under rank-one perturbations

The polynomial identity does not require positivity or nonsingularity.
Adapted from Ziyang Qin's historical `RotationalSphereVolumeDensity.lean`.
-/

namespace LinearMap

/-- In dimension two, a scalar plus rank-one perturbation of a symmetric bilinear
form multiplies its Gram determinant by `b * (b + q * g Z Z)`. This polynomial
identity also applies to degenerate forms. -/
theorem det_smul_add_rankOne_gram_fin_two
    {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V]
    (g : V →ₗ[R] V →ₗ[R] R) (hsym : ∀ v w : V, g v w = g w v)
    (B : Module.Basis (Fin 2) R V) (Z : V) (b q : R) :
    (Matrix.of fun i j => b * g (B i) (B j) + q * (g Z (B i) * g Z (B j))).det =
      b * (b + q * g Z Z) * (Matrix.of fun i j => g (B i) (B j)).det := by
  let c : Fin 2 → R := B.repr Z
  have hZ : Z = c 0 • B 0 + c 1 • B 1 := by
    rw [← B.sum_repr Z]
    simp only [Fin.sum_univ_two, c]
  have hu0 : g Z (B 0) = c 0 * g (B 0) (B 0) + c 1 * g (B 1) (B 0) := by
    rw [hZ]
    simp only [map_add, LinearMap.add_apply, map_smul, LinearMap.smul_apply, smul_eq_mul]
  have hu1 : g Z (B 1) = c 0 * g (B 0) (B 1) + c 1 * g (B 1) (B 1) := by
    rw [hZ]
    simp only [map_add, LinearMap.add_apply, map_smul, LinearMap.smul_apply, smul_eq_mul]
  have hZZ : g Z Z = c 0 ^ 2 * g (B 0) (B 0) +
      2 * c 0 * c 1 * g (B 0) (B 1) + c 1 ^ 2 * g (B 1) (B 1) := by
    rw [hZ]
    simp only [map_add, LinearMap.add_apply, map_smul, LinearMap.smul_apply, smul_eq_mul]
    rw [hsym (B 1) (B 0)]
    ring
  simp only [Matrix.det_fin_two, Matrix.of_apply]
  rw [hu0, hu1, hZZ, hsym (B 1) (B 0)]
  ring

end LinearMap
