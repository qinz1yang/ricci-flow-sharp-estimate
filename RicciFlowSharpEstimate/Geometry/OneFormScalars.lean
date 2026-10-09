/-
Copyright (c) 2026 Ziyang Qin. All rights reserved.
No license is granted by this file.
Authors: Ziyang Qin
-/
import RicciFlowSharpEstimate.Geometry.CanonicalDerivatives
import RicciFlowSharpEstimate.Geometry.TraceFreeSymmetric
import DifferentialGeometry.Geometry.Metric.TensorInner.FiberMetric.Tensor0SMetricIneq

/-!
# Trace and oriented curl of the actual covariant derivative

Both scalar functions are literal contractions of the canonical metric derivative.
When the supplied tensor is the unit area form, its contraction is the oriented curl.
-/

noncomputable section

namespace RicciFlowSharpEstimate.Geometry

open DifferentialGeometry DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Tensor.RicciIdentity DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.Tensor.RSTensor
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]

/-- The trace of the genuine first metric derivative of a smooth one-form. -/
def oneFormTrace (g : SmoothRiemannianMetric I M)
    (h : OneFormSection (I := I) (M := M)) (x : M) : ℝ :=
  metricTracePair0SAt g (metricNabla0S g h x)

/-- The curl obtained by contracting the genuine first derivative with the chosen area tensor. -/
def oneFormCurl (g : SmoothRiemannianMetric I M)
    (Ω : TwoTensorSection (I := I) (M := M))
    (h : OneFormSection (I := I) (M := M)) (x : M) : ℝ :=
  inner0S g x 2 (Ω x) (metricNabla0S g h x)

/-- The actual trace scalar is smooth. -/
theorem oneFormTrace_contMDiff (g : SmoothRiemannianMetric I M)
    (h : OneFormSection (I := I) (M := M)) :
    ContMDiff I 𝓘(ℝ, ℝ) ∞ (oneFormTrace g h) :=
  trace02_smooth g (metricNabla0S g h)

/-- Contraction with a smooth area tensor makes the actual curl scalar smooth. -/
theorem oneFormCurl_contMDiff (g : SmoothRiemannianMetric I M)
    (Ω : TwoTensorSection (I := I) (M := M))
    (h : OneFormSection (I := I) (M := M)) :
    ContMDiff I 𝓘(ℝ, ℝ) ∞ (oneFormCurl g Ω h) := by
  have heq : oneFormCurl g Ω h = fun x =>
      (normSq0S g x 2 ((Ω + metricNabla0S g h) x) - normSq0S g x 2 (Ω x) -
        normSq0S g x 2 (metricNabla0S g h x)) / 2 := by
    funext x
    change inner0S g x 2 (Ω x) (metricNabla0S g h x) =
      (normSq0S g x 2 (Ω x + metricNabla0S g h x) - normSq0S g x 2 (Ω x) -
        normSq0S g x 2 (metricNabla0S g h x)) / 2
    rw [normSq0S_add]
    ring
  rw [heq]
  exact (((normSq0S_smooth g (Ω + metricNabla0S g h)).sub (normSq0S_smooth g Ω)).sub
    (normSq0S_smooth g (metricNabla0S g h))).div_const 2

end RicciFlowSharpEstimate.Geometry
