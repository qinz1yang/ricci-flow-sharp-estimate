/-
Copyright (c) 2026 Ziyang Qin. All rights reserved.
No license is granted by this file.
Authors: Ziyang Qin
-/
import RicciFlowSharpEstimate.Geometry.OneFormScalarNaturality
import RicciFlowSharpEstimate.Geometry.RotationalAreaInvariance
import RicciFlowSharpEstimate.Geometry.RotationalScalarAverage
import RicciFlowSharpEstimate.Geometry.RotationalAverageDerivatives

/-!
# Scalar contractions of the actual Haar remainder

Trace and oriented curl of the canonical first derivative commute with the
genuine rotational average. Both actual scalars of the complementary one-form
therefore have zero angular mean everywhere, including the poles.
-/

noncomputable section

namespace RicciFlowSharpEstimate.Geometry

open Bundle DifferentialGeometry DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Tensor.RicciIdentity DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.PDE.RicciFlow
open scoped Manifold ContDiff

local instance : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 2 + 1) :=
  ⟨finrank_euclideanSpace_fin⟩

namespace RotationalProfile.PoleData

/-- Metric trace commutes with the genuine normalized circle average. -/
theorem metricTracePair0SAt_rotationalAverage (D : PoleData)
    (T : TwoTensorSection (I := 𝓡 2) (M := RotationalSphere)) (x : RotationalSphere) :
    metricTracePair0SAt D.metric (rotationalAverage T x) =
      rotationalScalarAverage (fun y => metricTracePair0SAt D.metric (T y)) x := by
  unfold rotationalAverage rotationalScalarAverage
  change metricTracePair0SAt D.metric ((2 * Real.pi)⁻¹ •
    tensorIntervalIntegral (fun θ => diffeomorphTensorPullback (angleRotation θ) T)
      (contMDiff_diffeomorphTensorPullback_angleRotation T) 0 (2 * Real.pi) x) = _
  rw [metricTracePair0SAt_smul, metricTracePair0SAt_tensorIntervalIntegral]
  apply congrArg (fun t : ℝ => (2 * Real.pi)⁻¹ * t)
  apply intervalIntegral.integral_congr
  intro θ _
  have hnat := metricTracePair0SAt_diffeomorphTensorPullback D.metric (angleRotation θ) T x
  simpa only [D.pullbackMetric_angleRotation] using hnat

/-- Contraction with the actual invariant area form commutes with Haar averaging. -/
theorem inner0S_areaForm_rotationalAverage (D : PoleData)
    (T : TwoTensorSection (I := 𝓡 2) (M := RotationalSphere)) (x : RotationalSphere) :
    inner0S D.metric x 2 (D.areaForm x) (rotationalAverage T x) =
      rotationalScalarAverage (fun y => inner0S D.metric y 2 (D.areaForm y) (T y)) x := by
  unfold rotationalAverage rotationalScalarAverage
  change inner0S D.metric x 2 (D.areaForm x)
    ((2 * Real.pi)⁻¹ •
      tensorIntervalIntegral (fun θ => diffeomorphTensorPullback (angleRotation θ) T)
        (contMDiff_diffeomorphTensorPullback_angleRotation T) 0 (2 * Real.pi) x) = _
  rw [inner0S_smul_right, inner0S_symm, inner0S_tensorIntervalIntegral_left]
  apply congrArg (fun t : ℝ => (2 * Real.pi)⁻¹ * t)
  apply intervalIntegral.integral_congr
  intro θ _
  dsimp only
  rw [inner0S_symm]
  have hnat := inner0S_diffeomorphTensorPullback D.metric (angleRotation θ) D.areaForm T x
  simpa only [D.pullbackMetric_angleRotation, D.diffeomorphTensorPullback_areaForm_angleRotation]
    using hnat

/-- The actual trace scalar has the usual scalar pullback law under rotation. -/
theorem oneFormTrace_angleRotation (D : PoleData) (θ : ℝ)
    (h : OneFormSection (I := 𝓡 2) (M := RotationalSphere)) (x : RotationalSphere) :
    oneFormTrace D.metric (diffeomorphTensorPullback (angleRotation θ) h) x =
      oneFormTrace D.metric h (angleRotation θ x) := by
  simpa only [D.pullbackMetric_angleRotation] using
    oneFormTrace_diffeomorphTensorPullback D.metric (angleRotation θ) h x

/-- The actual oriented curl has the scalar pullback law for the same rotations. -/
theorem oneFormCurl_angleRotation (D : PoleData) (θ : ℝ)
    (h : OneFormSection (I := 𝓡 2) (M := RotationalSphere)) (x : RotationalSphere) :
    oneFormCurl D.metric D.areaForm (diffeomorphTensorPullback (angleRotation θ) h) x =
      oneFormCurl D.metric D.areaForm h (angleRotation θ x) := by
  simpa only [D.pullbackMetric_angleRotation, D.diffeomorphTensorPullback_areaForm_angleRotation]
    using oneFormCurl_diffeomorphTensorPullback D.metric (angleRotation θ) D.areaForm h x

/-- Trace of the averaged original one-form equals the scalar average of its actual trace. -/
theorem oneFormTrace_rotationalAverage (D : PoleData)
    (h : OneFormSection (I := 𝓡 2) (M := RotationalSphere)) :
    oneFormTrace D.metric (rotationalAverage h) =
      rotationalScalarAverage (oneFormTrace D.metric h) := by
  funext x
  unfold oneFormTrace
  rw [D.metricNabla0S_rotationalAverage, D.metricTracePair0SAt_rotationalAverage]

/-- Curl of the averaged original one-form equals the scalar average of its actual curl. -/
theorem oneFormCurl_rotationalAverage (D : PoleData)
    (h : OneFormSection (I := 𝓡 2) (M := RotationalSphere)) :
    oneFormCurl D.metric D.areaForm (rotationalAverage h) =
      rotationalScalarAverage (oneFormCurl D.metric D.areaForm h) := by
  funext x
  unfold oneFormCurl
  rw [D.metricNabla0S_rotationalAverage, D.inner0S_areaForm_rotationalAverage]

private theorem metricNabla0S_zero_oneForm (D : PoleData) :
    metricNabla0S D.metric
      (0 : OneFormSection (I := 𝓡 2) (M := RotationalSphere)) = 0 := by
  simpa only [zero_smul] using metricNabla0S_smul D.metric 0
    (0 : OneFormSection (I := 𝓡 2) (M := RotationalSphere))

/-- The trace of the genuine complementary form has zero angular mean. -/
theorem rotationalScalarAverage_oneFormTrace_remainder (D : PoleData)
    (h : OneFormSection (I := 𝓡 2) (M := RotationalSphere)) :
    rotationalScalarAverage (oneFormTrace D.metric (h - rotationalAverage h)) = 0 := by
  rw [← D.oneFormTrace_rotationalAverage, rotationalAverage_sub_average]
  funext x
  unfold oneFormTrace
  rw [D.metricNabla0S_zero_oneForm]
  change metricTracePair0SAt D.metric (0 : Tensor0SSpace (I := 𝓡 2) 2 x) = 0
  have hz := metricTracePair0SAt_smul D.metric 0
    (0 : Tensor0SSpace (I := 𝓡 2) 2 x)
  simpa only [zero_smul, zero_mul] using hz

/-- The oriented curl of the genuine complementary form has zero angular mean. -/
theorem rotationalScalarAverage_oneFormCurl_remainder (D : PoleData)
    (h : OneFormSection (I := 𝓡 2) (M := RotationalSphere)) :
    rotationalScalarAverage (oneFormCurl D.metric D.areaForm (h - rotationalAverage h)) = 0 := by
  rw [← D.oneFormCurl_rotationalAverage, rotationalAverage_sub_average]
  funext x
  unfold oneFormCurl
  rw [D.metricNabla0S_zero_oneForm]
  change inner0S D.metric x 2 (D.areaForm x) 0 = 0
  have hz := inner0S_smul_right D.metric x 2 0 (D.areaForm x) 0
  simpa only [zero_smul, zero_mul] using hz

/-- The actual remainder's trace vanishes at both poles. -/
theorem oneFormTrace_remainder_eq_zero_at_pole (D : PoleData)
    (h : OneFormSection (I := 𝓡 2) (M := RotationalSphere))
    (x : RotationalSphere) (hx : sphereHeight x ^ 2 = 1) :
    oneFormTrace D.metric (h - rotationalAverage h) x = 0 :=
  rotationalScalarAverage_eq_zero_at_pole
    (D.rotationalScalarAverage_oneFormTrace_remainder h) x hx

/-- The actual remainder's curl vanishes at both poles. -/
theorem oneFormCurl_remainder_eq_zero_at_pole (D : PoleData)
    (h : OneFormSection (I := 𝓡 2) (M := RotationalSphere))
    (x : RotationalSphere) (hx : sphereHeight x ^ 2 = 1) :
    oneFormCurl D.metric D.areaForm (h - rotationalAverage h) x = 0 :=
  rotationalScalarAverage_eq_zero_at_pole
    (D.rotationalScalarAverage_oneFormCurl_remainder h) x hx

end RotationalProfile.PoleData

end RicciFlowSharpEstimate.Geometry
