/-
Copyright (c) 2026 Ziyang Qin. All rights reserved.
No license is granted by this file.
Authors: Ziyang Qin
-/
import RicciFlowSharpEstimate.Geometry.ConjugatedRotationalAverage
import RicciFlowSharpEstimate.Geometry.RotationalRemainder

/-!
# Covariant operators and dissipation of the conjugated Haar projector

The actual metric derivatives, rough Laplacian and Ahlfors projection commute
with the same-map conjugated projector. The full four-term pairing, Haar split
and strict remainder rigidity transport to every original smooth one-form for
the actual pulled-back metric, with no orientation or curvature pinching premise.
-/

noncomputable section

namespace RicciFlowSharpEstimate.Geometry

open DifferentialGeometry DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Tensor.RicciIdentity DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.PDE.RicciFlow
open scoped Manifold ContDiff

local instance : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 2 + 1) :=
  ⟨finrank_euclideanSpace_fin⟩
local instance : CompactSpace RotationalSphere := Metric.sphere.compactSpace _ _

namespace RotationalProfile.PoleData

/-- The actual first derivative of the pulled-back metric commutes with its
same-map conjugated Haar projector in every tensor rank. -/
theorem metricNabla0S_conjugatedRotationalAverage (D : PoleData)
    (F : RotationalSphere ≃ₘ⟮𝓡 2, 𝓡 2⟯ RotationalSphere) {s : ℕ}
    (A : Tensor0SField (𝕜 := ℝ) (I := 𝓡 2) (M := RotationalSphere) (n := ∞) s) :
    metricNabla0S (Diffeomorph.pullbackMetric D.metric F)
        (conjugatedRotationalAverage F A) =
      conjugatedRotationalAverage F
        (metricNabla0S (Diffeomorph.pullbackMetric D.metric F) A) := by
  unfold conjugatedRotationalAverage
  rw [metricNabla0S_diffeomorphTensorPullback, D.metricNabla0S_rotationalAverage]
  apply congrArg (diffeomorphTensorPullback F)
  apply congrArg rotationalAverage
  simpa only [pullbackMetric_symm_apply] using
    metricNabla0S_diffeomorphTensorPullback (Diffeomorph.pullbackMetric D.metric F) F.symm A

/-- The repeated actual derivative also commutes with the conjugated projector. -/
theorem metricNabla0S_twice_conjugatedRotationalAverage (D : PoleData)
    (F : RotationalSphere ≃ₘ⟮𝓡 2, 𝓡 2⟯ RotationalSphere) {s : ℕ}
    (A : Tensor0SField (𝕜 := ℝ) (I := 𝓡 2) (M := RotationalSphere) (n := ∞) s) :
    metricNabla0S (Diffeomorph.pullbackMetric D.metric F)
        (metricNabla0S (Diffeomorph.pullbackMetric D.metric F)
          (conjugatedRotationalAverage F A)) =
      conjugatedRotationalAverage F
        (metricNabla0S (Diffeomorph.pullbackMetric D.metric F)
          (metricNabla0S (Diffeomorph.pullbackMetric D.metric F) A)) := by
  rw [D.metricNabla0S_conjugatedRotationalAverage,
    D.metricNabla0S_conjugatedRotationalAverage]

/-- The actual rough Laplacian commutes with the conjugated Haar projector. -/
theorem roughLap0SField_conjugatedRotationalAverage (D : PoleData)
    (F : RotationalSphere ≃ₘ⟮𝓡 2, 𝓡 2⟯ RotationalSphere) {s : ℕ}
    (A : Tensor0SField (𝕜 := ℝ) (I := 𝓡 2) (M := RotationalSphere) (n := ∞) s) :
    roughLap0SField (Diffeomorph.pullbackMetric D.metric F)
        (conjugatedRotationalAverage F A) =
      conjugatedRotationalAverage F
        (roughLap0SField (Diffeomorph.pullbackMetric D.metric F) A) := by
  unfold conjugatedRotationalAverage
  rw [roughLap0SField_diffeomorphTensorPullback, D.roughLap0SField_rotationalAverage]
  apply congrArg (diffeomorphTensorPullback F)
  apply congrArg rotationalAverage
  simpa only [pullbackMetric_symm_apply] using
    roughLap0SField_diffeomorphTensorPullback (Diffeomorph.pullbackMetric D.metric F) F.symm A

/-- The trace-free symmetric projection commutes for every original smooth
two-tensor and the actual pulled-back metric. -/
theorem ahlforsPart_conjugatedRotationalAverage (D : PoleData)
    (F : RotationalSphere ≃ₘ⟮𝓡 2, 𝓡 2⟯ RotationalSphere)
    (A : Tensor0SField (𝕜 := ℝ) (I := 𝓡 2) (M := RotationalSphere) (n := ∞) 2) :
    ahlforsPart (Diffeomorph.pullbackMetric D.metric F)
        (conjugatedRotationalAverage F A) =
      conjugatedRotationalAverage F
        (ahlforsPart (Diffeomorph.pullbackMetric D.metric F) A) := by
  unfold conjugatedRotationalAverage
  rw [ahlforsPart_diffeomorphTensorPullback, D.ahlforsPart_rotationalAverage]
  apply congrArg (diffeomorphTensorPullback F)
  apply congrArg rotationalAverage
  simpa only [pullbackMetric_symm_apply] using
    ahlforsPart_diffeomorphTensorPullback (Diffeomorph.pullbackMetric D.metric F) F.symm A

/-- The Ahlfors part of the genuine first derivative commutes with the same
conjugated projector on arbitrary original smooth one-forms. -/
theorem ahlforsPart_metricNabla0S_conjugatedRotationalAverage (D : PoleData)
    (F : RotationalSphere ≃ₘ⟮𝓡 2, 𝓡 2⟯ RotationalSphere)
    (h : OneFormSection (I := 𝓡 2) (M := RotationalSphere)) :
    ahlforsPart (Diffeomorph.pullbackMetric D.metric F)
        (metricNabla0S (Diffeomorph.pullbackMetric D.metric F)
          (conjugatedRotationalAverage F h)) =
      conjugatedRotationalAverage F
        (ahlforsPart (Diffeomorph.pullbackMetric D.metric F)
          (metricNabla0S (Diffeomorph.pullbackMetric D.metric F) h)) := by
  rw [D.metricNabla0S_conjugatedRotationalAverage, D.ahlforsPart_conjugatedRotationalAverage]

private theorem dissipation_inverse (D : PoleData)
    (F : RotationalSphere ≃ₘ⟮𝓡 2, 𝓡 2⟯ RotationalSphere)
    (h : OneFormSection (I := 𝓡 2) (M := RotationalSphere)) :
    oneFormDissipation (Diffeomorph.pullbackMetric D.metric F) h =
      oneFormDissipation D.metric (diffeomorphTensorPullback F.symm h) := by
  symm
  simpa only [pullbackMetric_symm_apply] using
    oneFormDissipation_diffeomorphTensorPullback (Diffeomorph.pullbackMetric D.metric F) F.symm h

private theorem pairing_inverse (D : PoleData)
    (F : RotationalSphere ≃ₘ⟮𝓡 2, 𝓡 2⟯ RotationalSphere)
    (h k : OneFormSection (I := 𝓡 2) (M := RotationalSphere)) :
    oneFormDissipationPairing (Diffeomorph.pullbackMetric D.metric F) h k =
      oneFormDissipationPairing D.metric
        (diffeomorphTensorPullback F.symm h) (diffeomorphTensorPullback F.symm k) := by
  symm
  simpa only [pullbackMetric_symm_apply] using
    oneFormDissipationPairing_diffeomorphTensorPullback
      (Diffeomorph.pullbackMetric D.metric F) F.symm h k

/-- The conjugated projector is self-adjoint for the entire four-term pairing
of the same pulled-back metric. -/
theorem oneFormDissipationPairing_conjugatedRotationalAverage_selfAdjoint (D : PoleData)
    (F : RotationalSphere ≃ₘ⟮𝓡 2, 𝓡 2⟯ RotationalSphere)
    (h k : OneFormSection (I := 𝓡 2) (M := RotationalSphere)) :
    oneFormDissipationPairing (Diffeomorph.pullbackMetric D.metric F)
        (conjugatedRotationalAverage F h) k =
      oneFormDissipationPairing (Diffeomorph.pullbackMetric D.metric F)
        h (conjugatedRotationalAverage F k) := by
  rw [D.pairing_inverse F, D.pairing_inverse F,
    diffeomorphTensorPullback_symm_conjugatedRotationalAverage,
    diffeomorphTensorPullback_symm_conjugatedRotationalAverage]
  exact D.oneFormDissipationPairing_rotationalAverage_selfAdjoint _ _

/-- The actual averaged part and actual remainder are orthogonal for the full
four-term pairing of the pulled-back metric. -/
theorem oneFormDissipationPairing_conjugated_average_sub_average (D : PoleData)
    (F : RotationalSphere ≃ₘ⟮𝓡 2, 𝓡 2⟯ RotationalSphere)
    (h k : OneFormSection (I := 𝓡 2) (M := RotationalSphere)) :
    oneFormDissipationPairing (Diffeomorph.pullbackMetric D.metric F)
        (conjugatedRotationalAverage F h) (k - conjugatedRotationalAverage F k) = 0 := by
  rw [D.pairing_inverse F, diffeomorphTensorPullback_sub,
    diffeomorphTensorPullback_symm_conjugatedRotationalAverage,
    diffeomorphTensorPullback_symm_conjugatedRotationalAverage]
  exact D.oneFormDissipationPairing_average_sub_average _ _

/-- The exact full-action split retains the arbitrary original smooth form,
its actual conjugated average and the same pulled-back metric. -/
theorem oneFormDissipation_conjugated_split (D : PoleData)
    (F : RotationalSphere ≃ₘ⟮𝓡 2, 𝓡 2⟯ RotationalSphere)
    (h : OneFormSection (I := 𝓡 2) (M := RotationalSphere)) :
    oneFormDissipation (Diffeomorph.pullbackMetric D.metric F) h =
      oneFormDissipation (Diffeomorph.pullbackMetric D.metric F)
          (conjugatedRotationalAverage F h) +
        oneFormDissipation (Diffeomorph.pullbackMetric D.metric F)
          (h - conjugatedRotationalAverage F h) := by
  simp only [D.dissipation_inverse F, diffeomorphTensorPullback_sub,
    diffeomorphTensorPullback_symm_conjugatedRotationalAverage]
  exact D.oneFormDissipation_haar_split _

/-- The genuine conjugated Haar remainder has nonnegative complete action
without a curvature pinching hypothesis. -/
theorem oneFormDissipation_conjugated_remainder_nonneg (D : PoleData)
    (F : RotationalSphere ≃ₘ⟮𝓡 2, 𝓡 2⟯ RotationalSphere)
    (h : OneFormSection (I := 𝓡 2) (M := RotationalSphere)) :
    0 ≤ oneFormDissipation (Diffeomorph.pullbackMetric D.metric F)
      (h - conjugatedRotationalAverage F h) := by
  rw [D.dissipation_inverse F, diffeomorphTensorPullback_sub,
    diffeomorphTensorPullback_symm_conjugatedRotationalAverage]
  exact D.oneFormDissipation_remainder_nonneg _

/-- Zero complete action of the original conjugated Haar remainder is
equivalent to vanishing of that same original remainder. -/
theorem oneFormDissipation_conjugated_remainder_eq_zero_iff (D : PoleData)
    (F : RotationalSphere ≃ₘ⟮𝓡 2, 𝓡 2⟯ RotationalSphere)
    (h : OneFormSection (I := 𝓡 2) (M := RotationalSphere)) :
    oneFormDissipation (Diffeomorph.pullbackMetric D.metric F)
        (h - conjugatedRotationalAverage F h) = 0 ↔
      h - conjugatedRotationalAverage F h = 0 := by
  rw [D.dissipation_inverse F, diffeomorphTensorPullback_sub,
    diffeomorphTensorPullback_symm_conjugatedRotationalAverage,
    D.oneFormDissipation_remainder_eq_zero_iff]
  rw [← diffeomorphTensorPullback_symm_conjugatedRotationalAverage F h,
    ← diffeomorphTensorPullback_sub, diffeomorphTensorPullback_eq_zero_iff]

end RotationalProfile.PoleData

end RicciFlowSharpEstimate.Geometry
