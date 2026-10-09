/-
Copyright (c) 2026 Ziyang Qin. All rights reserved.
No license is granted by this file.
Authors: Ziyang Qin
-/
import DifferentialGeometry.Geometry.Connection.MetricTrace.Connection
import DifferentialGeometry.Tensor.Multilinear.Bundle.DomainPermutation

/-!
# Trace-free symmetric covariant tensors

The Ahlfors projection is constructed as a smooth section from the original metric and tensor.

The trace and slot-swap algebra adapts Ziyang Qin's historical
`TensorTraceFree.lean` and `CurvatureEnergyIdentity.lean`.
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
private theorem swap_apply {x : M}
    (T : Tensor0SSpace (𝕜 := Real) (I := I) 2 x)
    (v : Fin 2 → TangentSpace I x) :
    T.domDomCongr (Equiv.swap (0 : Fin 2) 1) v =
      T (fun i => v (Equiv.swap (0 : Fin 2) 1 i)) := by
  change T (fun i => v ((Equiv.swap (0 : Fin 2) 1).symm i)) = _
  rw [Equiv.symm_swap]

omit [FiniteDimensional Real E] in
private theorem swap_apply_basis {x : M}
    (T : Tensor0SSpace (𝕜 := Real) (I := I) 2 x)
    (X Y : TangentSpace I x) :
    T.domDomCongr (Equiv.swap (0 : Fin 2) 1)
        (fun i : Fin 2 => if i = 0 then X else Y) =
      T (fun i : Fin 2 => if i = 0 then Y else X) := by
  rw [swap_apply]
  congr 1
  funext i
  fin_cases i <;> simp

private theorem inner_swap_left {x : M}
    (g : SmoothRiemannianMetric I M)
    (S T : Tensor0SSpace (𝕜 := Real) (I := I) 2 x) :
    inner0S (I := I) g x 2 (S.domDomCongr (Equiv.swap (0 : Fin 2) 1)) T =
      inner0S (I := I) g x 2 S (T.domDomCongr (Equiv.swap (0 : Fin 2) 1)) := by
  classical
  let basis := coordinateFrameAtToBasis (I := I) x
  let gInv : CoordinateIdx (𝕜 := Real) E → CoordinateIdx (𝕜 := Real) E → Real :=
    fun i j => inverseMetricFlatModelInChartComponent (I := I) g x i j (extChartAt I x x)
  have hinv := inverseMetricFlatModelInChart_metricInverseInBasis_center (I := I) g x
  rw [inner0S_two_eq_coord (I := I) g x basis gInv hinv,
    inner0S_two_eq_coord (I := I) g x basis gInv hinv]
  simp only [swap_apply_basis]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  refine Finset.sum_congr rfl (fun l _ => ?_)
  ring

private theorem swap_metric (g : SmoothRiemannianMetric I M) (x : M) :
    (metricTensor0S (I := I) g x).domDomCongr (Equiv.swap (0 : Fin 2) 1) =
      metricTensor0S (I := I) g x := by
  ext v
  rw [swap_apply, metricTensor0S_apply, metricTensor0S_apply]
  simp only [Equiv.swap_apply_left, Equiv.swap_apply_right]
  exact g.symm x (v 1) (v 0)

private theorem trace_swap {x : M}
    (g : SmoothRiemannianMetric I M)
    (T : Tensor0SSpace (𝕜 := Real) (I := I) 2 x) :
    metricTracePair0SAt (I := I) g (T.domDomCongr (Equiv.swap (0 : Fin 2) 1)) =
      metricTracePair0SAt (I := I) g T := by
  unfold metricTracePair0SAt
  rw [← inner_swap_left, swap_metric]

private theorem metricTensorField_eq_metricTensor0S
    (g : SmoothRiemannianMetric I M) (x : M) :
    metricTensorField (I := I) g x = metricTensor0S (I := I) g x := by
  ext v
  rw [metricTensorField_apply, metricTensor0S_apply]

/-- The smooth trace-free symmetric part of a covariant two-tensor. -/
def ahlforsPart (g : SmoothRiemannianMetric I M)
    (T : Tensor0SField (𝕜 := Real) (I := I) (M := M) (n := ∞) 2) :
    Tensor0SField (𝕜 := Real) (I := I) (M := M) (n := ∞) 2 :=
  let S : Tensor0SField (𝕜 := Real) (I := I) (M := M) (n := ∞) 2 :=
    MultilinearSection.domDomCongr (𝕜 := Real) (F := E) (IB := I)
      (E := TangentSpace I) (∞ : WithTop ℕ∞) (Equiv.swap (0 : Fin 2) 1) T
  (2 : Real)⁻¹ • (T + S) -
    tensor0SFieldSmulByFun (∞ : WithTop ℕ∞)
      (fun x => metricTracePair0SAt (I := I) g (T x) / (Module.finrank Real E : Real))
      ((trace02_smooth (I := I) g T).div_const _)
      (metricTensorField (I := I) g)

@[simp] theorem ahlforsPart_apply (g : SmoothRiemannianMetric I M)
    (T : Tensor0SField (𝕜 := Real) (I := I) (M := M) (n := ∞) 2) (x : M) :
    ahlforsPart g T x =
      (2 : Real)⁻¹ • (T x + (T x).domDomCongr (Equiv.swap (0 : Fin 2) 1)) -
        (metricTracePair0SAt (I := I) g (T x) / (Module.finrank Real E : Real)) •
          metricTensor0S (I := I) g x := by
  change (2 : Real)⁻¹ • (T x + (T x).domDomCongr (Equiv.swap (0 : Fin 2) 1)) -
    (metricTracePair0SAt (I := I) g (T x) / (Module.finrank Real E : Real)) •
      metricTensorField (I := I) g x = _
  rw [metricTensorField_eq_metricTensor0S]

theorem ahlforsPart_apply_of_finrank_eq_two
    (hdim : Module.finrank Real E = 2) (g : SmoothRiemannianMetric I M)
    (T : Tensor0SField (𝕜 := Real) (I := I) (M := M) (n := ∞) 2) (x : M) :
    ahlforsPart g T x =
      (2 : Real)⁻¹ • (T x + (T x).domDomCongr (Equiv.swap (0 : Fin 2) 1)) -
        (metricTracePair0SAt (I := I) g (T x) / 2) • metricTensor0S (I := I) g x := by
  rw [ahlforsPart_apply, hdim]
  norm_num

theorem ahlforsPart_symmetric (g : SmoothRiemannianMetric I M)
    (T : Tensor0SField (𝕜 := Real) (I := I) (M := M) (n := ∞) 2) (x : M) :
    (ahlforsPart g T x).domDomCongr (Equiv.swap (0 : Fin 2) 1) =
      ahlforsPart g T x := by
  ext v
  rw [swap_apply, ahlforsPart_apply]
  simp only [Tensor0SSpace.sub_apply, Tensor0SSpace.smul_apply,
    Tensor0SSpace.add_apply, swap_apply, smul_eq_mul, metricTensor0S_apply,
    Equiv.swap_apply_left, Equiv.swap_apply_right, Equiv.swap_apply_self]
  rw [g.symm x (v 1) (v 0)]
  ring

theorem ahlforsPart_trace_eq_zero
    (hdim : Module.finrank Real E ≠ 0) (g : SmoothRiemannianMetric I M)
    (T : Tensor0SField (𝕜 := Real) (I := I) (M := M) (n := ∞) 2) (x : M) :
    metricTracePair0SAt (I := I) g (ahlforsPart g T x) = 0 := by
  rw [ahlforsPart_apply, metricTracePair0SAt_sub, metricTracePair0SAt_smul,
    metricTracePair0SAt_add, trace_swap, metricTracePair0SAt_smul,
    metricTracePair0SAt_metric]
  have hdim' : (Module.finrank Real E : Real) ≠ 0 := Nat.cast_ne_zero.mpr hdim
  rw [div_mul_cancel₀ _ hdim']
  ring

theorem ahlforsPart_add (g : SmoothRiemannianMetric I M)
    (S T : Tensor0SField (𝕜 := Real) (I := I) (M := M) (n := ∞) 2) :
    ahlforsPart g (S + T) = ahlforsPart g S + ahlforsPart g T := by
  refine DFunLike.ext _ _ fun x => ?_
  ext v
  simp only [ahlforsPart_apply, ContMDiffSection.coe_add, Pi.add_apply,
    Tensor0SSpace.sub_apply, Tensor0SSpace.smul_apply,
    Tensor0SSpace.add_apply, swap_apply, metricTracePair0SAt_add, smul_eq_mul]
  ring

theorem ahlforsPart_smul (g : SmoothRiemannianMetric I M) (c : Real)
    (T : Tensor0SField (𝕜 := Real) (I := I) (M := M) (n := ∞) 2) :
    ahlforsPart g (c • T) = c • ahlforsPart g T := by
  refine DFunLike.ext _ _ fun x => ?_
  ext v
  simp only [ahlforsPart_apply, ContMDiffSection.coe_smul, Pi.smul_apply,
    Tensor0SSpace.sub_apply, Tensor0SSpace.smul_apply,
    Tensor0SSpace.add_apply, swap_apply, metricTracePair0SAt_smul, smul_eq_mul]
  ring

end RicciFlowSharpEstimate.Geometry
