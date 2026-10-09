/-
Copyright (c) 2026 Ziyang Qin. All rights reserved.
No license is granted by this file.
Authors: Ziyang Qin
-/
import RicciFlowSharpEstimate.Geometry.RotationalCircleAction
import RicciFlowSharpEstimate.Geometry.RotationalAreaForm
import RicciFlowSharpEstimate.Geometry.OneFormDissipationNaturality

/-!
# Rotation invariance of the actual sphere area form

The genuine circle rotations preserve the ambient determinant defining the round
sphere area form. Their fixed height coordinate then preserves the original
profile-scaled metric area form, including at both poles.
-/

noncomputable section

namespace RicciFlowSharpEstimate.Geometry

open Bundle DifferentialGeometry DifferentialGeometry.Geometry
open DifferentialGeometry.Tensor0SBundle DifferentialGeometry.Tensor.RSTensor
open DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff

local instance : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 2 + 1) :=
  ⟨finrank_euclideanSpace_fin⟩

/-- The actual derivative pullback by a circle rotation preserves the round area form. -/
theorem diffeomorphTensorPullback_roundSphereAreaForm_circleSphereDiffeo (z : Circle) :
    diffeomorphTensorPullback (circleSphereDiffeo z) roundSphereAreaForm =
      roundSphereAreaForm := by
  have hz : (z : ℂ).re ^ 2 + (z : ℂ).im ^ 2 = 1 := by
    simpa [Complex.normSq_apply, pow_two] using Circle.normSq_coe z
  refine DFunLike.ext _ _ fun x => ?_
  ext slots
  have hslots : slots = vec2 (slots 0) (slots 1) := by
    funext i
    fin_cases i <;> rfl
  rw [diffeomorphTensorPullback_apply]
  have hrot : (fun i => mfderiv (𝓡 2) (𝓡 2) (circleSphereDiffeo z) x (slots i)) =
      vec2 (mfderiv (𝓡 2) (𝓡 2) (circleSphereDiffeo z) x (slots 0))
        (mfderiv (𝓡 2) (𝓡 2) (circleSphereDiffeo z) x (slots 1)) := by
    funext i
    fin_cases i <;> rfl
  rw [hrot, hslots, roundSphereAreaForm_apply, roundSphereAreaForm_apply,
    circleSphereDiffeo_dIncl_mfderiv, circleSphereDiffeo_dIncl_mfderiv,
    circleSphereDiffeo_coe]
  simp only [axisRotation_apply]
  convert congrArg (fun t : ℝ => t *
    ((x : EuclideanSpace ℝ (Fin 3)) 2 *
      ((dIncl (n := 2) x (slots 0)) 0 * (dIncl (n := 2) x (slots 1)) 1 -
        (dIncl (n := 2) x (slots 0)) 1 * (dIncl (n := 2) x (slots 1)) 0) +
    (x : EuclideanSpace ℝ (Fin 3)) 0 *
      ((dIncl (n := 2) x (slots 0)) 1 * (dIncl (n := 2) x (slots 1)) 2 -
        (dIncl (n := 2) x (slots 0)) 2 * (dIncl (n := 2) x (slots 1)) 1) +
    (x : EuclideanSpace ℝ (Fin 3)) 1 *
      ((dIncl (n := 2) x (slots 0)) 2 * (dIncl (n := 2) x (slots 1)) 0 -
        (dIncl (n := 2) x (slots 0)) 0 * (dIncl (n := 2) x (slots 1)) 2))) hz using 1
  · simp [vec2]
    ring
  · simp

/-- The genuine angle rotations preserve the round area form. -/
theorem diffeomorphTensorPullback_roundSphereAreaForm_angleRotation (θ : ℝ) :
    diffeomorphTensorPullback (angleRotation θ) roundSphereAreaForm = roundSphereAreaForm :=
  diffeomorphTensorPullback_roundSphereAreaForm_circleSphereDiffeo (Circle.exp θ)

namespace RotationalProfile.PoleData

/-- The actual circle action preserves the same profile-scaled metric area form. -/
theorem diffeomorphTensorPullback_areaForm_circleSphereDiffeo (D : PoleData) (z : Circle) :
    diffeomorphTensorPullback (circleSphereDiffeo z) D.areaForm = D.areaForm := by
  refine DFunLike.ext _ _ fun x => ?_
  ext slots
  rw [diffeomorphTensorPullback_apply, D.areaForm_apply, D.areaForm_apply,
    sphereHeight_circleSphereDiffeo]
  congr 1
  have h := congrArg (fun A => A x slots)
    (diffeomorphTensorPullback_roundSphereAreaForm_circleSphereDiffeo z)
  simpa only [diffeomorphTensorPullback_apply] using h

/-- The actual angle action preserves the metric area form on the entire sphere. -/
theorem diffeomorphTensorPullback_areaForm_angleRotation (D : PoleData) (θ : ℝ) :
    diffeomorphTensorPullback (angleRotation θ) D.areaForm = D.areaForm :=
  D.diffeomorphTensorPullback_areaForm_circleSphereDiffeo (Circle.exp θ)

end RotationalProfile.PoleData

end RicciFlowSharpEstimate.Geometry
