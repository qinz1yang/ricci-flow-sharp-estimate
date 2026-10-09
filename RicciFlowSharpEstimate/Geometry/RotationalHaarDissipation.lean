/-
Copyright (c) 2026 Ziyang Qin. All rights reserved.
No license is granted by this file.
Authors: Ziyang Qin
-/
import RicciFlowSharpEstimate.Geometry.RotationalAverageDerivatives
import RicciFlowSharpEstimate.Geometry.RotationalPairingIntegral

/-!
# The full Haar dissipation split

The actual normalized covector-pullback projector is self-adjoint for the entire
four-term polarization. Its invariant and zero-average parts are orthogonal for
that same pairing; no positivity assumption enters the resulting action identity.
-/

noncomputable section

namespace RicciFlowSharpEstimate.Geometry

open Bundle DifferentialGeometry DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.PDE.RicciFlow DifferentialGeometry.Tensor.RicciIdentity
open DifferentialGeometry.Integral.Measure MeasureTheory
open scoped Manifold ContDiff

local instance : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 2 + 1) :=
  ⟨finrank_euclideanSpace_fin⟩
local instance : CompactSpace RotationalSphere := Metric.sphere.compactSpace _ _
private local instance : MeasurableSpace RotationalSphere := borel RotationalSphere
private local instance : BorelSpace RotationalSphere := ⟨rfl⟩

namespace RotationalProfile.PoleData

private theorem inner_average (D : PoleData) {s : ℕ}
    (A B : Tensor0SField (𝕜 := ℝ) (I := 𝓡 2) (M := RotationalSphere) (n := ∞) s)
    (x : RotationalSphere) :
    inner0S D.metric x s (rotationalAverage A x) (B x) =
      (2 * Real.pi)⁻¹ * ∫ θ in (0 : ℝ)..2 * Real.pi,
        inner0S D.metric x s (diffeomorphTensorPullback (angleRotation θ) A x) (B x) := by
  change inner0S D.metric x s ((2 * Real.pi)⁻¹ •
    tensorIntervalIntegral (fun θ => diffeomorphTensorPullback (angleRotation θ) A)
      (contMDiff_diffeomorphTensorPullback_angleRotation A) 0 (2 * Real.pi) x) (B x) = _
  rw [inner0S_smul_left, inner0S_tensorIntervalIntegral_left]

private theorem inner_orbit_integrable (D : PoleData) {s : ℕ}
    (A B : Tensor0SField (𝕜 := ℝ) (I := 𝓡 2) (M := RotationalSphere) (n := ∞) s)
    (x : RotationalSphere) :
    IntervalIntegrable (fun θ => inner0S D.metric x s
      (diffeomorphTensorPullback (angleRotation θ) A x) (B x)) volume 0 (2 * Real.pi) :=
  intervalIntegrable_inner0S_tensorFamily_left D.metric
    (fun θ => diffeomorphTensorPullback (angleRotation θ) A)
    (contMDiff_diffeomorphTensorPullback_angleRotation A) 0 (2 * Real.pi) x (B x)

/-- The complete polarized density pairs an averaged form by averaging the
original rotated density, including both second- and first-derivative terms. -/
theorem oneFormDissipationPairingDensity_rotationalAverage (D : PoleData)
    (h k : OneFormSection (I := 𝓡 2) (M := RotationalSphere)) (x : RotationalSphere) :
    oneFormDissipationPairingDensity D.metric (rotationalAverage h) k x =
      (2 * Real.pi)⁻¹ * ∫ θ in (0 : ℝ)..2 * Real.pi,
        oneFormDissipationPairingDensity D.metric
          (diffeomorphTensorPullback (angleRotation θ) h) k x := by
  have hR (θ : ℝ) : roughLap0SField D.metric
      (diffeomorphTensorPullback (angleRotation θ) h) =
        diffeomorphTensorPullback (angleRotation θ) (roughLap0SField D.metric h) := by
    simpa only [D.pullbackMetric_angleRotation] using
      roughLap0SField_diffeomorphTensorPullback D.metric (angleRotation θ) h
  have hA (θ : ℝ) : ahlforsPart D.metric
      (diffeomorphTensorPullback (angleRotation θ) (metricNabla0S D.metric h)) =
        diffeomorphTensorPullback (angleRotation θ)
          (ahlforsPart D.metric (metricNabla0S D.metric h)) := by
    simpa only [D.pullbackMetric_angleRotation] using
      ahlforsPart_diffeomorphTensorPullback D.metric (angleRotation θ) (metricNabla0S D.metric h)
  simp only [oneFormDissipationPairingDensity, D.roughLap0SField_rotationalAverage,
    D.metricNabla0S_rotationalAverage, D.ahlforsPart_rotationalAverage, D.inner_average,
    hR, D.metricNabla0S_angleRotation, hA]
  have hIR := D.inner_orbit_integrable (roughLap0SField D.metric h) (roughLap0SField D.metric k) x
  have hI0 := (D.inner_orbit_integrable h k x).const_mul ((metricScalarAt D.metric x / 2) ^ 2)
  have hI1 := (D.inner_orbit_integrable (metricNabla0S D.metric h)
    (metricNabla0S D.metric k) x).const_mul (metricScalarAt D.metric x / 2)
  have hIA := (D.inner_orbit_integrable (ahlforsPart D.metric (metricNabla0S D.metric h))
    (ahlforsPart D.metric (metricNabla0S D.metric k)) x).const_mul
      (2 * (metricScalarAt D.metric x / 2))
  rw [intervalIntegral.integral_add ((hIR.add hI0).sub hI1) hIA,
    intervalIntegral.integral_sub (hIR.add hI0) hI1,
    intervalIntegral.integral_add hIR hI0]
  simp only [intervalIntegral.integral_const_mul]
  ring

/-- Averaging the first argument of the original full pairing is its normalized
angular integral, with genuine product integrability supplied internally. -/
theorem oneFormDissipationPairing_rotationalAverage (D : PoleData)
    (h k : OneFormSection (I := 𝓡 2) (M := RotationalSphere)) :
    oneFormDissipationPairing D.metric (rotationalAverage h) k =
      (2 * Real.pi)⁻¹ * ∫ θ in (0 : ℝ)..2 * Real.pi,
        oneFormDissipationPairing D.metric (diffeomorphTensorPullback (angleRotation θ) h) k := by
  unfold oneFormDissipationPairing
  simp_rw [D.oneFormDissipationPairingDensity_rotationalAverage]
  rw [MeasureTheory.integral_const_mul]
  congr 1
  exact D.integral_intervalIntegral_oneFormDissipationPairingDensity_angleRotation h k 0 _

private theorem pairing_inverse_rotation (D : PoleData)
    (h k : OneFormSection (I := 𝓡 2) (M := RotationalSphere)) (θ : ℝ) :
    oneFormDissipationPairing D.metric (diffeomorphTensorPullback (angleRotation θ) h) k =
      oneFormDissipationPairing D.metric h (diffeomorphTensorPullback (angleRotation (-θ)) k) := by
  have hi := oneFormDissipationPairing_diffeomorphTensorPullback_of_isometry D.metric
    (angleRotation θ) (D.pullbackMetric_angleRotation θ) h
    (diffeomorphTensorPullback (angleRotation (-θ)) k)
  simpa only [angleRotation_neg, diffeomorphTensorPullback_apply_symm] using hi

private theorem integral_periodic_neg (f : ℝ → ℝ) (hf : Function.Periodic f (2 * Real.pi)) :
    (∫ θ in (0 : ℝ)..2 * Real.pi, f (-θ)) = ∫ θ in (0 : ℝ)..2 * Real.pi, f θ := by
  rw [intervalIntegral.integral_comp_neg]
  simpa only [neg_zero, neg_add_cancel, zero_add] using
    hf.intervalIntegral_add_eq (-(2 * Real.pi)) 0

/-- The genuine Haar projection is self-adjoint for the full four-term polarization. -/
theorem oneFormDissipationPairing_rotationalAverage_selfAdjoint (D : PoleData)
    (h k : OneFormSection (I := 𝓡 2) (M := RotationalSphere)) :
    oneFormDissipationPairing D.metric (rotationalAverage h) k =
      oneFormDissipationPairing D.metric h (rotationalAverage k) := by
  rw [D.oneFormDissipationPairing_rotationalAverage,
    oneFormDissipationPairing_symm D.metric h (rotationalAverage k),
    D.oneFormDissipationPairing_rotationalAverage]
  simp_rw [D.pairing_inverse_rotation h k, oneFormDissipationPairing_symm D.metric h]
  apply congrArg ((2 * Real.pi)⁻¹ * ·)
  apply integral_periodic_neg
    (fun θ => oneFormDissipationPairing D.metric
      (diffeomorphTensorPullback (angleRotation θ) k) h)
  intro θ
  change oneFormDissipationPairing D.metric
    (diffeomorphTensorPullback (angleRotation (θ + 2 * Real.pi)) k) h = _
  rw [angleRotation_periodic θ]

/-- Every averaged form is orthogonal to every actual zero-average remainder
for the original complete pairing. -/
theorem oneFormDissipationPairing_average_sub_average (D : PoleData)
    (h k : OneFormSection (I := 𝓡 2) (M := RotationalSphere)) :
    oneFormDissipationPairing D.metric (rotationalAverage h) (k - rotationalAverage k) = 0 := by
  rw [D.oneFormDissipationPairing_rotationalAverage_selfAdjoint, rotationalAverage_sub_average]
  simpa only [zero_smul, zero_mul] using
    oneFormDissipationPairing_smul_right D.metric 0 h k

/-- The exact Haar split of the original complete one-form dissipation. -/
theorem oneFormDissipation_haar_split (D : PoleData)
    (h : OneFormSection (I := 𝓡 2) (M := RotationalSphere)) :
    oneFormDissipation D.metric h =
      oneFormDissipation D.metric (rotationalAverage h) +
        oneFormDissipation D.metric (h - rotationalAverage h) := by
  calc
    oneFormDissipation D.metric h =
        oneFormDissipation D.metric (rotationalAverage h + (h - rotationalAverage h)) := by
      congr 1
      module
    _ = _ := by
      rw [oneFormDissipation_add, D.oneFormDissipationPairing_average_sub_average]
      ring

end RotationalProfile.PoleData

end RicciFlowSharpEstimate.Geometry
