/-
Copyright (c) 2026 Ziyang Qin. All rights reserved.
No license is granted by this file.
Authors: Ziyang Qin
-/
import RicciFlowSharpEstimate.Geometry.OneFormScalars
import RicciFlowSharpEstimate.Geometry.OneFormDissipationNaturality

/-!
# Naturality of the genuine trace and curl

The metric, form and oriented area tensor are pulled back by the same actual
diffeomorphism. No orientation restriction is required when the area is transported.
-/

noncomputable section

namespace RicciFlowSharpEstimate.Geometry

open Bundle DifferentialGeometry DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Geometry.Operator DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.Tensor.RicciIdentity
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]

/-- The actual tensor metric pairing is natural under simultaneous pullback. -/
theorem inner0S_diffeomorphTensorPullback
    (g : SmoothRiemannianMetric I M) (f : M ≃ₘ⟮I, I⟯ M) {s : ℕ}
    (A B : Tensor0SField (𝕜 := ℝ) (I := I) (M := M) (n := ∞) s) (x : M) :
    inner0S (Diffeomorph.pullbackMetric g f) x s
      (diffeomorphTensorPullback f A x) (diffeomorphTensorPullback f B x) =
        inner0S g (f x) s (A (f x)) (B (f x)) := by
  apply inner0S_tensor0SPullbackCLE
  intro u v
  exact (Diffeomorph.pullbackMetric_inner g f x u v).symm

private theorem metricTensor0S_pullback
    (g : SmoothRiemannianMetric I M) (f : M ≃ₘ⟮I, I⟯ M) (x : M) :
    metricTensor0S (Diffeomorph.pullbackMetric g f) x =
      tensor0SPullbackCLE 2
        (Diffeomorph.mfderivToContinuousLinearEquiv f (by simp) x).toLinearEquiv
        (metricTensor0S g (f x)) := by
  ext slots
  simp only [tensor0SPullbackCLE_apply, tensor0SPullbackCLM_apply, metricTensor0S_apply]
  exact Diffeomorph.pullbackMetric_inner g f x (slots 0) (slots 1)

/-- Metric trace commutes with actual simultaneous metric and tensor pullback. -/
theorem metricTracePair0SAt_diffeomorphTensorPullback
    (g : SmoothRiemannianMetric I M) (f : M ≃ₘ⟮I, I⟯ M)
    (A : Tensor0SField (𝕜 := ℝ) (I := I) (M := M) (n := ∞) 2) (x : M) :
    metricTracePair0SAt (Diffeomorph.pullbackMetric g f)
      (diffeomorphTensorPullback f A x) = metricTracePair0SAt g (A (f x)) := by
  unfold metricTracePair0SAt
  rw [metricTensor0S_pullback]
  apply inner0S_tensor0SPullbackCLE
  intro u v
  exact (Diffeomorph.pullbackMetric_inner g f x u v).symm

/-- The trace of the actual covariant derivative is natural under pullback. -/
theorem oneFormTrace_diffeomorphTensorPullback
    (g : SmoothRiemannianMetric I M) (f : M ≃ₘ⟮I, I⟯ M)
    (h : OneFormSection (I := I) (M := M)) (x : M) :
    oneFormTrace (Diffeomorph.pullbackMetric g f) (diffeomorphTensorPullback f h) x =
      oneFormTrace g h (f x) := by
  unfold oneFormTrace
  rw [metricNabla0S_diffeomorphTensorPullback, metricTracePair0SAt_diffeomorphTensorPullback]

/-- Curl is natural when the original area tensor, metric and one-form are
transported by the same diffeomorphism, including orientation reversal. -/
theorem oneFormCurl_diffeomorphTensorPullback
    (g : SmoothRiemannianMetric I M) (f : M ≃ₘ⟮I, I⟯ M)
    (Ω : TwoTensorSection (I := I) (M := M))
    (h : OneFormSection (I := I) (M := M)) (x : M) :
    oneFormCurl (Diffeomorph.pullbackMetric g f) (diffeomorphTensorPullback f Ω)
      (diffeomorphTensorPullback f h) x = oneFormCurl g Ω h (f x) := by
  unfold oneFormCurl
  rw [metricNabla0S_diffeomorphTensorPullback, inner0S_diffeomorphTensorPullback]

end RicciFlowSharpEstimate.Geometry
