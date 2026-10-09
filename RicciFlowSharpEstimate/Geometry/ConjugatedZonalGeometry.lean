/-
Copyright (c) 2026 Ziyang Qin. All rights reserved.
No license is granted by this file.
Authors: Ziyang Qin
-/
import RicciFlowSharpEstimate.Geometry.ConjugatedCircleAction
import RicciFlowSharpEstimate.Geometry.ConjugatedHaarDissipation

/-!
# Exact zonal geometry for the conjugated action

The globally smooth probes and their original generators are transported by
the same representing diffeomorphism. The original full action retains its
exact angular factor and strict remainder equality.
-/

noncomputable section

namespace RicciFlowSharpEstimate.Geometry.RotationalProfile.PoleData

open DifferentialGeometry DifferentialGeometry.Tensor.RicciIdentity
open scoped Manifold ContDiff

local instance : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 2 + 1) :=
  ⟨finrank_euclideanSpace_fin⟩
local instance : CompactSpace RotationalSphere := Metric.sphere.compactSpace _ _

/-- The same pulled-back meridional and azimuthal generators retain the exact zonal action. -/
theorem oneFormDissipation_pullback_zonal (D : PoleData)
    (F : RotationalSphere ≃ₘ⟮𝓡 2, 𝓡 2⟯ RotationalSphere)
    (r : ℝ → ℝ) (hr : ContDiff ℝ ∞ r) (s : ℝ → ℝ) (hs : ContDiff ℝ ∞ s) :
    oneFormDissipation (Diffeomorph.pullbackMetric D.metric F)
      (diffeomorphTensorPullback F (D.meridionalOneForm r hr) +
        diffeomorphTensorPullback F (D.azimuthalOneForm s hs)) =
      2 * Real.pi * (D.meridionalAction r + D.meridionalAction s) := by
  rw [← diffeomorphTensorPullback_add, oneFormDissipation_diffeomorphTensorPullback]
  exact D.oneFormDissipation_zonal r s hr hs

/-- The actual conjugated average is represented by the same transported
generators and globally smooth real probes. -/
theorem exists_smooth_zonal_decomposition_conjugatedRotationalAverage (D : PoleData)
    (F : RotationalSphere ≃ₘ⟮𝓡 2, 𝓡 2⟯ RotationalSphere)
    (h : OneFormSection (I := 𝓡 2) (M := RotationalSphere)) :
    ∃ r s : ℝ → ℝ, ∃ hr : ContDiff ℝ ∞ r, ∃ hs : ContDiff ℝ ∞ s,
      conjugatedRotationalAverage F h =
        diffeomorphTensorPullback F (D.meridionalOneForm r hr) +
          diffeomorphTensorPullback F (D.azimuthalOneForm s hs) := by
  obtain ⟨r, s, hr, hs, heq⟩ :=
    D.exists_smooth_zonal_decomposition_rotationalAverage (diffeomorphTensorPullback F.symm h)
  refine ⟨r, s, hr, hs, ?_⟩
  simp only [conjugatedRotationalAverage, heq, diffeomorphTensorPullback_add]

/-- The full original action equals the transported zonal contribution plus
the same original conjugated remainder action. -/
theorem exists_conjugated_haar_zonal_dissipation (D : PoleData)
    (F : RotationalSphere ≃ₘ⟮𝓡 2, 𝓡 2⟯ RotationalSphere)
    (h : OneFormSection (I := 𝓡 2) (M := RotationalSphere)) :
    ∃ r s : ℝ → ℝ, ∃ hr : ContDiff ℝ ∞ r, ∃ hs : ContDiff ℝ ∞ s,
      conjugatedRotationalAverage F h =
        diffeomorphTensorPullback F (D.meridionalOneForm r hr) +
          diffeomorphTensorPullback F (D.azimuthalOneForm s hs) ∧
      oneFormDissipation (Diffeomorph.pullbackMetric D.metric F) h =
        2 * Real.pi * (D.meridionalAction r + D.meridionalAction s) +
          oneFormDissipation (Diffeomorph.pullbackMetric D.metric F)
            (h - conjugatedRotationalAverage F h) := by
  obtain ⟨r, s, hr, hs, heq⟩ :=
    D.exists_smooth_zonal_decomposition_conjugatedRotationalAverage F h
  refine ⟨r, s, hr, hs, heq, ?_⟩
  rw [D.oneFormDissipation_conjugated_split F h, heq, D.oneFormDissipation_pullback_zonal]

/-- The genuine conjugated average decreases the original action without pinching. -/
theorem oneFormDissipation_conjugatedRotationalAverage_le (D : PoleData)
    (F : RotationalSphere ≃ₘ⟮𝓡 2, 𝓡 2⟯ RotationalSphere)
    (h : OneFormSection (I := 𝓡 2) (M := RotationalSphere)) :
    oneFormDissipation (Diffeomorph.pullbackMetric D.metric F)
        (conjugatedRotationalAverage F h) ≤
      oneFormDissipation (Diffeomorph.pullbackMetric D.metric F) h := by
  have hsplit := D.oneFormDissipation_conjugated_split F h
  have hnonneg := D.oneFormDissipation_conjugated_remainder_nonneg F h
  linarith

/-- Equality in the transported Haar comparison means the original form is fixed. -/
theorem oneFormDissipation_eq_conjugatedRotationalAverage_iff (D : PoleData)
    (F : RotationalSphere ≃ₘ⟮𝓡 2, 𝓡 2⟯ RotationalSphere)
    (h : OneFormSection (I := 𝓡 2) (M := RotationalSphere)) :
    oneFormDissipation (Diffeomorph.pullbackMetric D.metric F) h =
        oneFormDissipation (Diffeomorph.pullbackMetric D.metric F)
          (conjugatedRotationalAverage F h) ↔ h = conjugatedRotationalAverage F h := by
  constructor
  · intro heq
    have hz : oneFormDissipation (Diffeomorph.pullbackMetric D.metric F)
        (h - conjugatedRotationalAverage F h) = 0 := by
      linarith [D.oneFormDissipation_conjugated_split F h]
    exact sub_eq_zero.mp ((D.oneFormDissipation_conjugated_remainder_eq_zero_iff F h).mp hz)
  · exact congrArg (oneFormDissipation (Diffeomorph.pullbackMetric D.metric F))

/-- Equality is invariance under the actual conjugated circle, including both poles. -/
theorem oneFormDissipation_eq_conjugatedRotationalAverage_iff_invariant (D : PoleData)
    (F : RotationalSphere ≃ₘ⟮𝓡 2, 𝓡 2⟯ RotationalSphere)
    (h : OneFormSection (I := 𝓡 2) (M := RotationalSphere)) :
    oneFormDissipation (Diffeomorph.pullbackMetric D.metric F) h =
        oneFormDissipation (Diffeomorph.pullbackMetric D.metric F)
          (conjugatedRotationalAverage F h) ↔
      ∀ z : Circle, diffeomorphTensorPullback (conjugatedCircleSphereDiffeo F z) h = h := by
  rw [D.oneFormDissipation_eq_conjugatedRotationalAverage_iff]
  exact eq_comm.trans (conjugatedRotationalAverage_eq_self_iff F h)

/-- The transported globally smooth probes give the sharp Haar comparison
and equality at that same original zonal form. -/
theorem exists_conjugated_haar_zonal_lower_bound (D : PoleData)
    (F : RotationalSphere ≃ₘ⟮𝓡 2, 𝓡 2⟯ RotationalSphere)
    (h : OneFormSection (I := 𝓡 2) (M := RotationalSphere)) :
    ∃ r s : ℝ → ℝ, ∃ hr : ContDiff ℝ ∞ r, ∃ hs : ContDiff ℝ ∞ s,
      conjugatedRotationalAverage F h =
        diffeomorphTensorPullback F (D.meridionalOneForm r hr) +
          diffeomorphTensorPullback F (D.azimuthalOneForm s hs) ∧
      2 * Real.pi * (D.meridionalAction r + D.meridionalAction s) ≤
        oneFormDissipation (Diffeomorph.pullbackMetric D.metric F) h ∧
      (oneFormDissipation (Diffeomorph.pullbackMetric D.metric F) h =
          2 * Real.pi * (D.meridionalAction r + D.meridionalAction s) ↔
        h = diffeomorphTensorPullback F (D.meridionalOneForm r hr) +
          diffeomorphTensorPullback F (D.azimuthalOneForm s hs)) := by
  obtain ⟨r, s, hr, hs, heq⟩ :=
    D.exists_smooth_zonal_decomposition_conjugatedRotationalAverage F h
  have hv : oneFormDissipation (Diffeomorph.pullbackMetric D.metric F)
      (conjugatedRotationalAverage F h) =
        2 * Real.pi * (D.meridionalAction r + D.meridionalAction s) := by
    rw [heq, D.oneFormDissipation_pullback_zonal]
  refine ⟨r, s, hr, hs, heq, ?_, ?_⟩
  · rw [← hv]
    exact D.oneFormDissipation_conjugatedRotationalAverage_le F h
  · rw [← hv, D.oneFormDissipation_eq_conjugatedRotationalAverage_iff, heq]

end RicciFlowSharpEstimate.Geometry.RotationalProfile.PoleData
