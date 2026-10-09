/-
Copyright (c) 2026 Ziyang Qin. All rights reserved.
No license is granted by this file.
Authors: Ziyang Qin
-/
import RicciFlowSharpEstimate.Geometry.RotationalAverage
import RicciFlowSharpEstimate.Geometry.TensorIntegralContractions

/-!
# Covariant operators and the genuine rotational average

The actual metric covariant derivatives, rough Laplacian, and Ahlfors projection
commute with the normalized rotational Haar projection of native smooth tensor
fields, including at the poles.
-/

noncomputable section

namespace RicciFlowSharpEstimate.Geometry

open Bundle DifferentialGeometry DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Tensor.RSTensor DifferentialGeometry.Tensor.RicciIdentity
open DifferentialGeometry.Integral.Connection DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Geometry.Operator
open scoped Manifold ContDiff

local instance : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 2 + 1) :=
  ⟨finrank_euclideanSpace_fin⟩

namespace RotationalProfile.PoleData

/-- The actual first metric covariant derivative commutes with rotational averaging. -/
theorem metricNabla0S_rotationalAverage (D : PoleData) {s : ℕ}
    (A : Tensor0SField (𝕜 := ℝ) (I := 𝓡 2) (M := RotationalSphere) (n := ∞) s) :
    metricNabla0S D.metric (rotationalAverage A) =
      rotationalAverage (metricNabla0S D.metric A) := by
  unfold rotationalAverage
  rw [metricNabla0S_smul]
  apply congrArg (fun B => (2 * Real.pi)⁻¹ • B)
  apply DFunLike.ext
  intro x
  ext v
  rw [metricNabla0S_tensorIntervalIntegral, tensorIntervalIntegral_eval]
  apply intervalIntegral.integral_congr
  intro θ _
  exact congrArg (fun B => B x v) (D.metricNabla0S_angleRotation θ A)

/-- The actual second metric covariant derivative commutes with rotational averaging. -/
theorem metricNabla0S_twice_rotationalAverage (D : PoleData) {s : ℕ}
    (A : Tensor0SField (𝕜 := ℝ) (I := 𝓡 2) (M := RotationalSphere) (n := ∞) s) :
    metricNabla0S D.metric (metricNabla0S D.metric (rotationalAverage A)) =
      rotationalAverage (metricNabla0S D.metric (metricNabla0S D.metric A)) := by
  rw [D.metricNabla0S_rotationalAverage, D.metricNabla0S_rotationalAverage]

/-- The actual rough Laplacian commutes with rotational averaging in every tensor rank. -/
theorem roughLap0SField_rotationalAverage (D : PoleData) {s : ℕ}
    (A : Tensor0SField (𝕜 := ℝ) (I := 𝓡 2) (M := RotationalSphere) (n := ∞) s) :
    roughLap0SField D.metric (rotationalAverage A) =
      rotationalAverage (roughLap0SField D.metric A) := by
  change metricTraceFirstTwoField D.metric
      (metricNabla0S D.metric (metricNabla0S D.metric (rotationalAverage A))) =
    rotationalAverage (roughLap0SField D.metric A)
  rw [D.metricNabla0S_twice_rotationalAverage]
  unfold rotationalAverage
  rw [metricTraceFirstTwoField_smul]
  apply congrArg (fun B => (2 * Real.pi)⁻¹ • B)
  apply DFunLike.ext
  intro x
  ext v
  change roughLap0STensor D.metric
      (tensorIntervalIntegral
        (fun θ => diffeomorphTensorPullback (angleRotation θ)
          (metricNabla0S D.metric (metricNabla0S D.metric A)))
        (contMDiff_diffeomorphTensorPullback_angleRotation _) 0 (2 * Real.pi) x) v =
    tensorIntervalIntegral
      (fun θ => diffeomorphTensorPullback (angleRotation θ) (roughLap0SField D.metric A))
      (contMDiff_diffeomorphTensorPullback_angleRotation _) 0 (2 * Real.pi) x v
  rw [roughLap0STensor_tensorIntervalIntegral_apply, tensorIntervalIntegral_eval]
  apply intervalIntegral.integral_congr
  intro θ _
  dsimp only
  rw [← D.metricNabla0S_angleRotation θ (metricNabla0S D.metric A),
    ← D.metricNabla0S_angleRotation θ A]
  change roughLap0SField D.metric (diffeomorphTensorPullback (angleRotation θ) A) x v =
    diffeomorphTensorPullback (angleRotation θ) (roughLap0SField D.metric A) x v
  have hnat := roughLap0SField_diffeomorphTensorPullback D.metric (angleRotation θ) A
  simpa only [D.pullbackMetric_angleRotation] using congrArg (fun B => B x v) hnat

/-- The actual trace-free symmetric projection commutes with rotational averaging. -/
theorem ahlforsPart_rotationalAverage (D : PoleData)
    (A : Tensor0SField (𝕜 := ℝ) (I := 𝓡 2) (M := RotationalSphere) (n := ∞) 2) :
    ahlforsPart D.metric (rotationalAverage A) =
      rotationalAverage (ahlforsPart D.metric A) := by
  unfold rotationalAverage
  rw [ahlforsPart_smul]
  apply congrArg (fun B => (2 * Real.pi)⁻¹ • B)
  apply DFunLike.ext
  intro x
  ext v
  rw [ahlforsPart_tensorIntervalIntegral_apply, tensorIntervalIntegral_eval]
  apply intervalIntegral.integral_congr
  intro θ _
  have hnat := ahlforsPart_diffeomorphTensorPullback D.metric (angleRotation θ) A
  simpa only [D.pullbackMetric_angleRotation] using congrArg (fun B => B x v) hnat

/-- The Ahlfors part of the genuine first derivative of a smooth one-form
commutes with rotational averaging. -/
theorem ahlforsPart_metricNabla0S_rotationalAverage (D : PoleData)
    (h : OneFormSection (I := 𝓡 2) (M := RotationalSphere)) :
    ahlforsPart D.metric (metricNabla0S D.metric (rotationalAverage h)) =
      rotationalAverage (ahlforsPart D.metric (metricNabla0S D.metric h)) := by
  rw [D.metricNabla0S_rotationalAverage, D.ahlforsPart_rotationalAverage]

end RotationalProfile.PoleData

end RicciFlowSharpEstimate.Geometry
