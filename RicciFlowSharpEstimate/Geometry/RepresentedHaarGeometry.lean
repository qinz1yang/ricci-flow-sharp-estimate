/-
Copyright (c) 2026 Ziyang Qin. All rights reserved.
No license is granted by this file.
Authors: Ziyang Qin
-/
import RicciFlowSharpEstimate.Geometry.RepresentedRotationalMetric
import RicciFlowSharpEstimate.Geometry.ConjugatedZonalGeometry

/-!
# Haar geometry for every represented rotational metric

Each class-level conclusion retains one actual representing profile and
diffeomorphism. Every original smooth form is handled by its genuine
conjugated projector and the same transported zonal sections.
-/

noncomputable section

namespace RicciFlowSharpEstimate.Geometry

open DifferentialGeometry DifferentialGeometry.Tensor.RicciIdentity
open DifferentialGeometry.PDE.RicciFlow
open scoped Manifold ContDiff

local instance : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 2 + 1) :=
  ⟨finrank_euclideanSpace_fin⟩

namespace RotationalProfile.PoleData

/-- The actual conjugated projector preserves the CK equation of the same metric. -/
theorem isConformalKillingOneForm_conjugatedRotationalAverage (D : PoleData)
    (F : RotationalSphere ≃ₘ⟮𝓡 2, 𝓡 2⟯ RotationalSphere)
    (h : OneFormSection (I := 𝓡 2) (M := RotationalSphere))
    (hCK : IsConformalKillingOneForm (Diffeomorph.pullbackMetric D.metric F) h) :
    IsConformalKillingOneForm (Diffeomorph.pullbackMetric D.metric F)
      (conjugatedRotationalAverage F h) := by
  unfold IsConformalKillingOneForm at hCK ⊢
  rw [D.ahlforsPart_metricNabla0S_conjugatedRotationalAverage,
    hCK, conjugatedRotationalAverage_zero]

/-- The original CK form's conjugated average has constant transported probes. -/
theorem exists_conjugated_constant_zonal_of_conformalKilling (D : PoleData)
    (F : RotationalSphere ≃ₘ⟮𝓡 2, 𝓡 2⟯ RotationalSphere)
    (h : OneFormSection (I := 𝓡 2) (M := RotationalSphere))
    (hCK : IsConformalKillingOneForm (Diffeomorph.pullbackMetric D.metric F) h) :
    ∃ c d : ℝ, conjugatedRotationalAverage F h =
      diffeomorphTensorPullback F (D.meridionalOneForm (fun _ => c) contDiff_const) +
        diffeomorphTensorPullback F (D.azimuthalOneForm (fun _ => d) contDiff_const) := by
  have hCK' : IsConformalKillingOneForm D.metric (diffeomorphTensorPullback F.symm h) := by
    simpa only [pullbackMetric_symm_apply] using hCK.diffeomorphTensorPullback F.symm
  obtain ⟨c, d, heq⟩ :=
    D.exists_constant_zonal_decomposition_rotationalAverage_of_isConformalKillingOneForm
      (diffeomorphTensorPullback F.symm h) hCK'
  refine ⟨c, d, ?_⟩
  simp only [conjugatedRotationalAverage, heq, diffeomorphTensorPullback_add]

end RotationalProfile.PoleData

namespace IsRepresentedRotationalMetric

/-- One actual representation supplies the full Haar split, unconditional
remainder rigidity and exact zonal action for every original smooth form. -/
theorem exists_haar_representation
    {g : SmoothRiemannianMetric (𝓡 2) RotationalSphere}
    (hg : IsRepresentedRotationalMetric g) :
    ∃ D : RotationalProfile.PoleData,
      ∃ F : RotationalSphere ≃ₘ⟮𝓡 2, 𝓡 2⟯ RotationalSphere,
      g = Diffeomorph.pullbackMetric D.metric F ∧
      (∀ h : OneFormSection (I := 𝓡 2) (M := RotationalSphere),
        oneFormDissipation g h =
          oneFormDissipation g (conjugatedRotationalAverage F h) +
            oneFormDissipation g (h - conjugatedRotationalAverage F h) ∧
        0 ≤ oneFormDissipation g (h - conjugatedRotationalAverage F h) ∧
        (oneFormDissipation g (h - conjugatedRotationalAverage F h) = 0 ↔
          h - conjugatedRotationalAverage F h = 0) ∧
        (oneFormDissipation g h =
            oneFormDissipation g (conjugatedRotationalAverage F h) ↔
          ∀ z : Circle,
            diffeomorphTensorPullback (conjugatedCircleSphereDiffeo F z) h = h)) ∧
      (∀ r s : ℝ → ℝ, ∀ hr : ContDiff ℝ ∞ r, ∀ hs : ContDiff ℝ ∞ s,
        oneFormDissipation g
          (diffeomorphTensorPullback F (D.meridionalOneForm r hr) +
            diffeomorphTensorPullback F (D.azimuthalOneForm s hs)) =
          2 * Real.pi * (D.meridionalAction r + D.meridionalAction s)) := by
  obtain ⟨D, F, rfl⟩ := hg
  refine ⟨D, F, rfl, ?_, ?_⟩
  · intro h
    exact ⟨D.oneFormDissipation_conjugated_split F h,
      D.oneFormDissipation_conjugated_remainder_nonneg F h,
      D.oneFormDissipation_conjugated_remainder_eq_zero_iff F h,
      D.oneFormDissipation_eq_conjugatedRotationalAverage_iff_invariant F h⟩
  · intro r s hr hs
    exact D.oneFormDissipation_pullback_zonal F r hr s hs

/-- Every original form on a represented metric has a smooth transported
zonal average with its exact complete action, lower bound and equality case. -/
theorem exists_haar_zonal_decomposition
    {g : SmoothRiemannianMetric (𝓡 2) RotationalSphere}
    (hg : IsRepresentedRotationalMetric g)
    (h : OneFormSection (I := 𝓡 2) (M := RotationalSphere)) :
    ∃ D : RotationalProfile.PoleData,
      ∃ F : RotationalSphere ≃ₘ⟮𝓡 2, 𝓡 2⟯ RotationalSphere,
      ∃ r s : ℝ → ℝ, ∃ hr : ContDiff ℝ ∞ r, ∃ hs : ContDiff ℝ ∞ s,
      g = Diffeomorph.pullbackMetric D.metric F ∧
      conjugatedRotationalAverage F h =
        diffeomorphTensorPullback F (D.meridionalOneForm r hr) +
          diffeomorphTensorPullback F (D.azimuthalOneForm s hs) ∧
      oneFormDissipation g h =
        2 * Real.pi * (D.meridionalAction r + D.meridionalAction s) +
          oneFormDissipation g (h - conjugatedRotationalAverage F h) ∧
      2 * Real.pi * (D.meridionalAction r + D.meridionalAction s) ≤
        oneFormDissipation g h ∧
      (oneFormDissipation g h =
          2 * Real.pi * (D.meridionalAction r + D.meridionalAction s) ↔
        h = diffeomorphTensorPullback F (D.meridionalOneForm r hr) +
          diffeomorphTensorPullback F (D.azimuthalOneForm s hs)) := by
  obtain ⟨D, F, rfl⟩ := hg
  obtain ⟨r, s, hr, hs, heq, hle, hzero⟩ := D.exists_conjugated_haar_zonal_lower_bound F h
  refine ⟨D, F, r, s, hr, hs, rfl, heq, ?_, hle, hzero⟩
  rw [D.oneFormDissipation_conjugated_split F h, heq, D.oneFormDissipation_pullback_zonal]

end IsRepresentedRotationalMetric

end RicciFlowSharpEstimate.Geometry
