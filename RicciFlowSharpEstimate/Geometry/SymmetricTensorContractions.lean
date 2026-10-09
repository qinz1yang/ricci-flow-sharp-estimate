/-
Copyright (c) 2026 Ziyang Qin. All rights reserved.
No license is granted by this file.
Authors: Ziyang Qin
-/
import RicciFlowSharpEstimate.Geometry.TraceFreeSymmetric
import DifferentialGeometry.Geometry.Metric.TensorInner.FiberMetric.Tensor0SMetricIneq

/-!
# Contractions of rank-one symmetric tensors

The trace and norm formulas use the canonical metric contractions and tensor product.
-/

set_option autoImplicit false

noncomputable section

namespace RicciFlowSharpEstimate.Geometry

open Bundle DifferentialGeometry DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Geometry.Operator DifferentialGeometry.Tensor.RSTensor
open DifferentialGeometry.Tensor.Coordinates
open scoped Manifold ContDiff BigOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

omit [FiniteDimensional Real E] in
private theorem product_one_apply {x : M}
    (α β : Tensor0SSpace (𝕜 := Real) (I := I) 1 x)
    (v : Fin 2 → TangentSpace I x) :
    α.product β v = α (fun _ => v 0) * β (fun _ => v 1) := by
  rw [Tensor0SSpace.product_apply]
  congr 1 <;> congr 1 <;> funext i <;> fin_cases i <;> rfl

/-- The metric trace of a product of covectors is their metric pairing. -/
theorem metricTracePair0SAt_product_one
    (g : SmoothRiemannianMetric I M) (x : M)
    (α β : Tensor0SSpace (𝕜 := Real) (I := I) 1 x) :
    metricTracePair0SAt g (α.product β) = inner0S g x 1 α β := by
  classical
  let basis := coordinateFrameAtToBasis (I := I) x
  let gInv : CoordinateIdx (𝕜 := Real) E → CoordinateIdx (𝕜 := Real) E → Real :=
    fun i j => inverseMetricFlatModelInChartComponent (I := I) g x i j (extChartAt I x x)
  have hinv := inverseMetricFlatModelInChart_metricInverseInBasis_center (I := I) g x
  rw [metricTracePair0SAt_eq_sum_basis g basis gInv hinv,
    inner0S_one_eq_cotangent, cotangentInner_eq_coord g x basis gInv hinv]
  simp only [product_one_apply, Geometry.Curvature.vec2, cotangentToDual_apply]
  simp only [ite_true, one_ne_zero, ite_false]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- The metric pairing of two covector products factors into the two pairings. -/
theorem inner0S_product_one
    (g : SmoothRiemannianMetric I M) (x : M)
    (α β γ δ : Tensor0SSpace (𝕜 := Real) (I := I) 1 x) :
    inner0S g x 2 (α.product β) (γ.product δ) =
      inner0S g x 1 α γ * inner0S g x 1 β δ := by
  classical
  let basis := coordinateFrameAtToBasis (I := I) x
  let gInv : CoordinateIdx (𝕜 := Real) E → CoordinateIdx (𝕜 := Real) E → Real :=
    fun i j => inverseMetricFlatModelInChartComponent (I := I) g x i j (extChartAt I x x)
  have hinv := inverseMetricFlatModelInChart_metricInverseInBasis_center (I := I) g x
  rw [inner0S_two_eq_coord g x basis gInv hinv,
    inner0S_one_eq_cotangent, inner0S_one_eq_cotangent,
    cotangentInner_eq_coord g x basis gInv hinv,
    cotangentInner_eq_coord g x basis gInv hinv]
  simp only [product_one_apply, cotangentToDual_apply, ite_true, one_ne_zero, ite_false]
  simp_rw [Finset.sum_mul]
  simp_rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro l _
  ring

/-- Trace of a scaled rank-one tensor plus a multiple of the metric. -/
theorem metricTracePair0SAt_smul_product_self_add_metric
    (g : SmoothRiemannianMetric I M) (x : M)
    (α : Tensor0SSpace (𝕜 := Real) (I := I) 1 x) (u c : Real) :
    metricTracePair0SAt g (u • α.product α + c • metricTensor0S g x) =
      u * normSq0S g x 1 α + c * (Module.finrank Real E : Real) := by
  rw [metricTracePair0SAt_add, metricTracePair0SAt_smul,
    metricTracePair0SAt_smul, metricTracePair0SAt_product_one, metricTracePair0SAt_metric]
  rfl

/-- Squared norm of a scaled rank-one tensor plus a multiple of the metric. -/
theorem normSq0S_smul_product_self_add_metric
    (g : SmoothRiemannianMetric I M) (x : M)
    (α : Tensor0SSpace (𝕜 := Real) (I := I) 1 x) (u c : Real) :
    normSq0S g x 2 (u • α.product α + c • metricTensor0S g x) =
      u ^ 2 * (normSq0S g x 1 α) ^ 2 +
        2 * u * c * normSq0S g x 1 α + c ^ 2 * (Module.finrank Real E : Real) := by
  rw [normSq0S_add]
  simp only [normSq0S, inner0S_smul_left, inner0S_smul_right, inner0S_product_one]
  rw [inner0S_symm g x (α.product α) (metricTensor0S g x)]
  change u * (u * (inner0S g x 1 α α * inner0S g x 1 α α)) +
      2 * (c * (u * metricTracePair0SAt g (α.product α))) +
      c * (c * metricTracePair0SAt g (metricTensor0S g x)) = _
  rw [metricTracePair0SAt_product_one, metricTracePair0SAt_metric]
  ring

private theorem eq_smul_product_self_add_metric_of_apply {x : M}
    (g : SmoothRiemannianMetric I M)
    (T : Tensor0SSpace (𝕜 := Real) (I := I) 2 x)
    (α : Tensor0SSpace (𝕜 := Real) (I := I) 1 x) (u c : Real)
    (hT : ∀ v : Fin 2 → TangentSpace I x,
      T v = u * α (fun _ => v 0) * α (fun _ => v 1) + c * g.inner x (v 0) (v 1)) :
    T = u • α.product α + c • metricTensor0S g x := by
  ext v
  simp only [Tensor0SSpace.add_apply, Tensor0SSpace.smul_apply,
    product_one_apply, metricTensor0S_apply, smul_eq_mul, hT]
  ring

/-- Pointwise trace from a tensor's rank-one and metric evaluation formula. -/
theorem metricTracePair0SAt_of_apply_eq_rankOne_add_metric
    (g : SmoothRiemannianMetric I M) (x : M)
    (T : Tensor0SSpace (𝕜 := Real) (I := I) 2 x)
    (α : Tensor0SSpace (𝕜 := Real) (I := I) 1 x) (u c : Real)
    (hT : ∀ v : Fin 2 → TangentSpace I x,
      T v = u * α (fun _ => v 0) * α (fun _ => v 1) + c * g.inner x (v 0) (v 1)) :
    metricTracePair0SAt g T =
      u * normSq0S g x 1 α + c * (Module.finrank Real E : Real) := by
  rw [eq_smul_product_self_add_metric_of_apply g T α u c hT]
  exact metricTracePair0SAt_smul_product_self_add_metric g x α u c

/-- Pointwise squared norm from a tensor's rank-one and metric evaluation formula. -/
theorem normSq0S_of_apply_eq_rankOne_add_metric
    (g : SmoothRiemannianMetric I M) (x : M)
    (T : Tensor0SSpace (𝕜 := Real) (I := I) 2 x)
    (α : Tensor0SSpace (𝕜 := Real) (I := I) 1 x) (u c : Real)
    (hT : ∀ v : Fin 2 → TangentSpace I x,
      T v = u * α (fun _ => v 0) * α (fun _ => v 1) + c * g.inner x (v 0) (v 1)) :
    normSq0S g x 2 T =
      u ^ 2 * (normSq0S g x 1 α) ^ 2 +
        2 * u * c * normSq0S g x 1 α + c ^ 2 * (Module.finrank Real E : Real) := by
  rw [eq_smul_product_self_add_metric_of_apply g T α u c hT]
  exact normSq0S_smul_product_self_add_metric g x α u c

/-- On a surface, the Ahlfors projection removes the metric summand entirely. -/
theorem normSq0S_ahlforsPart_of_apply_eq_rankOne_add_metric
    (hdim : Module.finrank Real E = 2)
    (g : SmoothRiemannianMetric I M) (x : M)
    (T : Tensor0SField (𝕜 := Real) (I := I) (M := M) (n := ∞) 2)
    (α : Tensor0SSpace (𝕜 := Real) (I := I) 1 x) (u c : Real)
    (hT : ∀ v : Fin 2 → TangentSpace I x,
      T x v = u * α (fun _ => v 0) * α (fun _ => v 1) + c * g.inner x (v 0) (v 1)) :
    normSq0S g x 2 (ahlforsPart g T x) =
      (u ^ 2 / 2) * (normSq0S g x 1 α) ^ 2 := by
  have htrace := metricTracePair0SAt_of_apply_eq_rankOne_add_metric g x (T x) α u c hT
  rw [hdim] at htrace
  have hA : ahlforsPart g T x =
      u • α.product α + (-(u * normSq0S g x 1 α) / 2) • metricTensor0S g x := by
    ext v
    rw [ahlforsPart_apply_of_finrank_eq_two hdim]
    simp only [Tensor0SSpace.sub_apply, Tensor0SSpace.smul_apply,
      Tensor0SSpace.add_apply, product_one_apply, metricTensor0S_apply, smul_eq_mul]
    change (2 : Real)⁻¹ *
        (T x v + T x (fun i => v ((Equiv.swap (0 : Fin 2) 1).symm i))) -
        metricTracePair0SAt g (T x) / 2 * g.inner x (v 0) (v 1) = _
    rw [hT, hT, htrace, Equiv.symm_swap]
    simp only [Equiv.swap_apply_left, Equiv.swap_apply_right]
    rw [g.symm x (v 1) (v 0)]
    norm_num
    ring
  rw [hA, normSq0S_smul_product_self_add_metric, hdim]
  norm_num
  ring

end RicciFlowSharpEstimate.Geometry
