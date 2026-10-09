/-
Copyright (c) 2026 Ziyang Qin. All rights reserved.
No license is granted by this file.
Authors: Ziyang Qin
-/
import RicciFlowSharpEstimate.Geometry.TensorIntervalIntegral
import RicciFlowSharpEstimate.Geometry.TraceFreeSymmetric
import DifferentialGeometry.Geometry.Metric.TensorInner.FiberMetric.Tensor0SMetricIneq

/-!
# Linear metric contractions of tensor interval integrals

Native tensor inner products, metric traces, and the Ahlfors projection commute
with integration of jointly smooth covariant tensor fields. The proofs integrate
in the original tensor fiber and use its existing norm and genuine integrability.
-/

noncomputable section

namespace RicciFlowSharpEstimate.Geometry

open Bundle DifferentialGeometry DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Geometry.Operator
open MeasureTheory
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

@[instance_reducible]
private def tensorFiberENormedAddMonoid (s : ℕ) (x : M) :
    ENormedAddMonoid (Tensor0SSpace (𝕜 := ℝ) (E := E) (I := I) s x) :=
  @NormedAddGroup.toENormedAddMonoid _
    (tensor0SSpaceNormedAddCommGroup (𝕜 := ℝ) (E := E) (I := I) s x).toNormedAddGroup

attribute [local instance] tensorFiberENormedAddMonoid

private def tensorInnerLeftCLM (g : SmoothRiemannianMetric I M) (s : ℕ) (x : M)
    (β : Tensor0SSpace (𝕜 := ℝ) (E := E) (I := I) s x) :
    Tensor0SSpace (𝕜 := ℝ) (E := E) (I := I) s x →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun T => inner0S g x s T β
      map_add' := fun A B => inner0S_add_left g x s A B β
      map_smul' := fun c T => inner0S_smul_left g x s c T β }

private def tensorTracePairCLM (g : SmoothRiemannianMetric I M) (x : M) :
    Tensor0SSpace (𝕜 := ℝ) (E := E) (I := I) 2 x →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun T => metricTracePair0SAt g T
      map_add' := fun A B => metricTracePair0SAt_add g A B
      map_smul' := fun c T => metricTracePair0SAt_smul g c T }

private def tensorTraceFirstTwoCLM (g : SmoothRiemannianMetric I M)
    {s : ℕ} (x : M) (tail : Fin s → TangentSpace I x) :
    Tensor0SSpace (𝕜 := ℝ) (E := E) (I := I) (s + 2) x →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun T => metricTraceFirstTwo0SAt g T tail
      map_add' := fun A B => metricTraceFirstTwo0SAt_add g A B tail
      map_smul' := fun c T => metricTraceFirstTwo0SAt_smul g c T tail }

private def ahlforsEvaluationCLM (g : SmoothRiemannianMetric I M)
    (x : M) (v : Fin 2 → TangentSpace I x) :
    Tensor0SSpace (𝕜 := ℝ) (E := E) (I := I) 2 x →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun T => (2 : ℝ)⁻¹ *
        (T v + T (fun i => v ((Equiv.swap (0 : Fin 2) 1).symm i))) -
        metricTracePair0SAt g T / (Module.finrank ℝ E : ℝ) * metricTensor0S g x v
      map_add' := by
        intro A B
        simp only [Tensor0SSpace.add_apply, metricTracePair0SAt_add]
        ring
      map_smul' := by
        intro c T
        simp only [Tensor0SSpace.smul_apply, metricTracePair0SAt_smul,
          RingHom.id_apply, smul_eq_mul]
        ring }

/-- Pairing a jointly smooth tensor family with a fixed native tensor gives an
integrable scalar function on every finite parameter interval. -/
theorem intervalIntegrable_inner0S_tensorFamily_left {s : ℕ}
    (g : SmoothRiemannianMetric I M)
    (A : ℝ → Tensor0SField (𝕜 := ℝ) (I := I) (M := M) (n := ∞) s)
    (hA : ContMDiff (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, Tensor0SModel s ℝ E)) ∞
      (fun p : ℝ × M => TotalSpace.mk' (Tensor0SModel s ℝ E) p.2 (A p.1 p.2)))
    (a b : ℝ) (x : M) (β : Tensor0SSpace (𝕜 := ℝ) (E := E) (I := I) s x) :
    IntervalIntegrable (fun t => inner0S g x s (A t x) β) volume a b :=
  ((tensorInnerLeftCLM g s x β).continuous.comp
    (continuous_tensorFamily_at A hA x)).intervalIntegrable a b

variable [I.Boundaryless]

/-- Pairing the tensor interval integral with a fixed native tensor commutes with
integration in its first argument. -/
theorem inner0S_tensorIntervalIntegral_left {s : ℕ} (g : SmoothRiemannianMetric I M)
    (A : ℝ → Tensor0SField (𝕜 := ℝ) (I := I) (M := M) (n := ∞) s)
    (hA : ContMDiff (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, Tensor0SModel s ℝ E)) ∞
      (fun p : ℝ × M => TotalSpace.mk' (Tensor0SModel s ℝ E) p.2 (A p.1 p.2)))
    (a b : ℝ) (x : M) (β : Tensor0SSpace (𝕜 := ℝ) (E := E) (I := I) s x) :
    inner0S g x s (tensorIntervalIntegral A hA a b x) β =
      ∫ t in a..b, inner0S g x s (A t x) β :=
  ((tensorInnerLeftCLM g s x β).intervalIntegral_comp_comm
    (intervalIntegrable_tensorFamily_at A hA x a b)).symm

/-- The native metric trace of a two-tensor integral is the integral of its traces. -/
theorem metricTracePair0SAt_tensorIntervalIntegral (g : SmoothRiemannianMetric I M)
    (A : ℝ → Tensor0SField (𝕜 := ℝ) (I := I) (M := M) (n := ∞) 2)
    (hA : ContMDiff (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, Tensor0SModel 2 ℝ E)) ∞
      (fun p : ℝ × M => TotalSpace.mk' (Tensor0SModel 2 ℝ E) p.2 (A p.1 p.2)))
    (a b : ℝ) (x : M) :
    metricTracePair0SAt g (tensorIntervalIntegral A hA a b x) =
      ∫ t in a..b, metricTracePair0SAt g (A t x) :=
  ((tensorTracePairCLM g x).intervalIntegral_comp_comm
    (intervalIntegrable_tensorFamily_at A hA x a b)).symm

/-- Contracting the first two tensor slots against the metric commutes with the
actual tensor interval integral, with the remaining slots fixed. -/
theorem metricTraceFirstTwo0SAt_tensorIntervalIntegral {s : ℕ}
    (g : SmoothRiemannianMetric I M)
    (A : ℝ → Tensor0SField (𝕜 := ℝ) (I := I) (M := M) (n := ∞) (s + 2))
    (hA : ContMDiff (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, Tensor0SModel (s + 2) ℝ E)) ∞
      (fun p : ℝ × M => TotalSpace.mk' (Tensor0SModel (s + 2) ℝ E) p.2 (A p.1 p.2)))
    (a b : ℝ) (x : M) (tail : Fin s → TangentSpace I x) :
    metricTraceFirstTwo0SAt g (tensorIntervalIntegral A hA a b x) tail =
      ∫ t in a..b, metricTraceFirstTwo0SAt g (A t x) tail :=
  ((tensorTraceFirstTwoCLM g x tail).intervalIntegral_comp_comm
    (intervalIntegrable_tensorFamily_at A hA x a b)).symm

/-- The native rough-Laplacian contraction commutes with tensor interval
integration when evaluated on the remaining slots. -/
theorem roughLap0STensor_tensorIntervalIntegral_apply {s : ℕ}
    (g : SmoothRiemannianMetric I M)
    (A : ℝ → Tensor0SField (𝕜 := ℝ) (I := I) (M := M) (n := ∞) (s + 2))
    (hA : ContMDiff (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, Tensor0SModel (s + 2) ℝ E)) ∞
      (fun p : ℝ × M => TotalSpace.mk' (Tensor0SModel (s + 2) ℝ E) p.2 (A p.1 p.2)))
    (a b : ℝ) (x : M) (tail : Fin s → TangentSpace I x) :
    roughLap0STensor g (tensorIntervalIntegral A hA a b x) tail =
      ∫ t in a..b, roughLap0STensor g (A t x) tail := by
  simpa only [roughLap0STensor_apply] using
    metricTraceFirstTwo0SAt_tensorIntervalIntegral g A hA a b x tail

/-- The actual Ahlfors projection commutes with tensor interval integration in
arbitrary finite dimension. -/
theorem ahlforsPart_tensorIntervalIntegral_apply (g : SmoothRiemannianMetric I M)
    (A : ℝ → Tensor0SField (𝕜 := ℝ) (I := I) (M := M) (n := ∞) 2)
    (hA : ContMDiff (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, Tensor0SModel 2 ℝ E)) ∞
      (fun p : ℝ × M => TotalSpace.mk' (Tensor0SModel 2 ℝ E) p.2 (A p.1 p.2)))
    (a b : ℝ) (x : M) (v : Fin 2 → TangentSpace I x) :
    ahlforsPart g (tensorIntervalIntegral A hA a b) x v =
      ∫ t in a..b, ahlforsPart g (A t) x v := by
  simp only [ahlforsPart_apply, Tensor0SSpace.sub_apply, Tensor0SSpace.smul_apply,
    Tensor0SSpace.add_apply, smul_eq_mul]
  exact ((ahlforsEvaluationCLM g x v).intervalIntegral_comp_comm
    (intervalIntegrable_tensorFamily_at A hA x a b)).symm

end RicciFlowSharpEstimate.Geometry
