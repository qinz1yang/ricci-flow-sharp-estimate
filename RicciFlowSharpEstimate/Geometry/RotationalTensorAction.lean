/-
Copyright (c) 2026 Ziyang Qin. All rights reserved.
No license is granted by this file.
Authors: Ziyang Qin
-/
import RicciFlowSharpEstimate.Geometry.RotationalCircleAction
import RicciFlowSharpEstimate.Geometry.TensorPullbackFamily

/-!
# The actual rotation action on smooth covariant tensors

These laws use the existing derivative pullback and the original metric. They
provide the smooth periodic tensor families used in Haar integration.
-/

noncomputable section

namespace RicciFlowSharpEstimate.Geometry

open Bundle DifferentialGeometry DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.PDE.RicciFlow
open scoped Manifold ContDiff

local instance : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 2 + 1) :=
  ⟨finrank_euclideanSpace_fin⟩

/-- Zero angle acts as the identity on the original smooth tensor. -/
@[simp] theorem diffeomorphTensorPullback_angleRotation_zero {s : ℕ}
    (A : Tensor0SField (𝕜 := ℝ) (I := 𝓡 2) (M := RotationalSphere) (n := ∞) s) :
    diffeomorphTensorPullback (angleRotation 0) A = A := by
  have h : angleRotation 0 = _root_.Diffeomorph.refl (𝓡 2) RotationalSphere ∞ := by
    apply Diffeomorph.ext
    exact angleRotation_zero
  rw [h, diffeomorphTensorPullback_refl]

/-- Pullback by angle addition is composition of the genuine tensor actions. -/
theorem diffeomorphTensorPullback_angleRotation_add (θ φ : ℝ) {s : ℕ}
    (A : Tensor0SField (𝕜 := ℝ) (I := 𝓡 2) (M := RotationalSphere) (n := ∞) s) :
    diffeomorphTensorPullback (angleRotation (θ + φ)) A =
      diffeomorphTensorPullback (angleRotation θ)
        (diffeomorphTensorPullback (angleRotation φ) A) := by
  have h : angleRotation (θ + φ) = (angleRotation θ).trans (angleRotation φ) := by
    apply Diffeomorph.ext
    intro x
    rw [add_comm, angleRotation_add]
    rfl
  rw [h, diffeomorphTensorPullback_trans]

/-- Every genuine tensor orbit is `2*pi` periodic. -/
theorem diffeomorphTensorPullback_angleRotation_periodic {s : ℕ}
    (A : Tensor0SField (𝕜 := ℝ) (I := 𝓡 2) (M := RotationalSphere) (n := ∞) s) :
    Function.Periodic (fun θ => diffeomorphTensorPullback (angleRotation θ) A) (2 * Real.pi) := by
  intro θ
  change diffeomorphTensorPullback (angleRotation (θ + 2 * Real.pi)) A = _
  rw [angleRotation_periodic θ]

/-- The original tensor orbit is jointly smooth, including over the poles. -/
theorem contMDiff_diffeomorphTensorPullback_angleRotation {s : ℕ}
    (A : Tensor0SField (𝕜 := ℝ) (I := 𝓡 2) (M := RotationalSphere) (n := ∞) s) :
    ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 2))
      ((𝓡 2).prod 𝓘(ℝ, Tensor0SModel s ℝ (EuclideanSpace ℝ (Fin 2)))) ∞
      (fun p : ℝ × RotationalSphere => TotalSpace.mk'
        (Tensor0SModel s ℝ (EuclideanSpace ℝ (Fin 2))) p.2
        (diffeomorphTensorPullback (angleRotation p.1) A p.2)) :=
  contMDiff_diffeomorphTensorPullback_family angleRotation angleRotation_contMDiff A

namespace RotationalProfile.PoleData

/-- The actual metric derivative intertwines every isometric rotation. -/
theorem metricNabla0S_angleRotation (D : PoleData) (θ : ℝ) {s : ℕ}
    (A : Tensor0SField (𝕜 := ℝ) (I := 𝓡 2) (M := RotationalSphere) (n := ∞) s) :
    metricNabla0S D.metric (diffeomorphTensorPullback (angleRotation θ) A) =
      diffeomorphTensorPullback (angleRotation θ) (metricNabla0S D.metric A) := by
  simpa only [D.pullbackMetric_angleRotation] using
    metricNabla0S_diffeomorphTensorPullback D.metric (angleRotation θ) A

/-- The first canonical derivative of a genuine tensor orbit is jointly smooth. -/
theorem contMDiff_metricNabla0S_angleRotation (D : PoleData) {s : ℕ}
    (A : Tensor0SField (𝕜 := ℝ) (I := 𝓡 2) (M := RotationalSphere) (n := ∞) s) :
    ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 2))
      ((𝓡 2).prod 𝓘(ℝ, Tensor0SModel (s + 1) ℝ (EuclideanSpace ℝ (Fin 2)))) ∞
      (fun p : ℝ × RotationalSphere => TotalSpace.mk'
        (Tensor0SModel (s + 1) ℝ (EuclideanSpace ℝ (Fin 2))) p.2
        (metricNabla0S D.metric (diffeomorphTensorPullback (angleRotation p.1) A) p.2)) := by
  simpa only [D.metricNabla0S_angleRotation] using
    contMDiff_diffeomorphTensorPullback_angleRotation (metricNabla0S D.metric A)

end RotationalProfile.PoleData

end RicciFlowSharpEstimate.Geometry
