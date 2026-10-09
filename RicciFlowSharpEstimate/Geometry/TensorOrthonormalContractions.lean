/-
Copyright (c) 2026 Ziyang Qin. All rights reserved.
No license is granted by this file.
Authors: Ziyang Qin
-/
import DifferentialGeometry.Geometry.Metric.TensorInner.FiberMetric.Tensor0SMetricIneq

/-!
# Covariant tensor contractions in an orthonormal basis

The actual metric tensor pairing becomes the finite diagonal sum of components.
This applies to every covariant rank, including scalars.
-/

namespace RicciFlowSharpEstimate.Geometry

open DifferentialGeometry DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Tensor.Coordinates
open scoped Manifold ContDiff BigOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- The native tensor metric is the diagonal component pairing in any orthonormal basis. -/
theorem inner0S_eq_sum_orthonormal {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (g : SmoothRiemannianMetric I M) (x : M) (s : ℕ)
    (B : Module.Basis Idx ℝ (TangentSpace I x))
    (hB : ∀ i j, g.inner x (B i) (B j) = if i = j then 1 else 0)
    (T U : Tensor0SSpace (𝕜 := ℝ) (I := I) s x) :
    inner0S g x s T U =
      ∑ v : Fin s → Idx, T (fun i => B (v i)) * U (fun i => B (v i)) := by
  classical
  let gInv : Idx → Idx → ℝ := fun i j => if i = j then 1 else 0
  have hinv : MetricInverseInBasis g x B gInv := by
    intro i j
    constructor <;> simp [gInv, hB]
  rw [inner0S_eq_coord g x s B gInv hinv]
  have hprod (v w : Fin s → Idx) :
      (∏ i : Fin s, gInv (v i) (w i)) = if v = w then (1 : ℝ) else 0 := by
    by_cases h : v = w
    · subst w
      simp [gInv]
    · rw [ite_eq_right h]
      obtain ⟨i, hi⟩ := not_forall.mp (fun hAll => h (funext hAll))
      exact Finset.prod_eq_zero (Finset.mem_univ i)
        (by simp [gInv, hi])
  simp [coordInner0S, hprod, tensor0SComponent_apply, ite_mul]

/-- The native squared tensor norm is the sum of squared orthonormal components. -/
theorem normSq0S_eq_sum_sq_orthonormal {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (g : SmoothRiemannianMetric I M) (x : M) (s : ℕ)
    (B : Module.Basis Idx ℝ (TangentSpace I x))
    (hB : ∀ i j, g.inner x (B i) (B j) = if i = j then 1 else 0)
    (T : Tensor0SSpace (𝕜 := ℝ) (I := I) s x) :
    normSq0S g x s T = ∑ v : Fin s → Idx, T (fun i => B (v i)) ^ 2 := by
  rw [normSq0S_eq_inner, inner0S_eq_sum_orthonormal g x s B hB]
  simp only [pow_two]

end RicciFlowSharpEstimate.Geometry
