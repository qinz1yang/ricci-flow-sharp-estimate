/-
Copyright (c) 2026 Ziyang Qin. All rights reserved.
No license is granted by this file.
Authors: Ziyang Qin
-/
import RicciFlowSharpEstimate.Geometry.ConformalKillingStability
import RicciFlowSharpEstimate.Geometry.RepresentedRotationalMetric

/-!
# Hemisphere stability under actual diffeomorphic pullback

The original profile's logarithm is controlled by the actual action of the
same-map pullbacks of its constant meridional and azimuthal forms. A represented
metric has one representation supporting all parameter choices simultaneously.
-/

noncomputable section

namespace RicciFlowSharpEstimate.Geometry

open DifferentialGeometry DifferentialGeometry.Tensor0SBundle
open Set Variational RicciFlowSharpEstimate.Analysis
open scoped Manifold ContDiff

local instance : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 2 + 1) :=
  ⟨finrank_euclideanSpace_fin⟩
local instance : CompactSpace RotationalSphere := Metric.sphere.compactSpace _ _

namespace RotationalProfile.PoleData

/-- The actual hemisphere deficit is the same-map pulled-back constant-zonal action with its
exact geometric normalization and the canonical optimal pair value. -/
theorem hemisphereDeficit_logProfile_eq_normalized_pullback_constant_zonal (D : PoleData)
    (F : RotationalSphere ≃ₘ⟮𝓡 2, 𝓡 2⟯ RotationalSphere)
    (m M : ℝ) (hm : 0 < m)
    (hb : ∀ v ∈ Icc (-1 : ℝ) 1, m ≤ D.a v ∧ D.a v ≤ M)
    (c d : ℝ) (hcd : 0 < c ^ 2 + d ^ 2) :
    hemisphereDeficit (M / m) (fun v => Real.log (M / D.a v)) =
      oneFormDissipation (Diffeomorph.pullbackMetric D.metric F)
        (diffeomorphTensorPullback F (D.meridionalOneForm (fun _ => c) contDiff_const) +
          diffeomorphTensorPullback F (D.azimuthalOneForm (fun _ => d) contDiff_const)) /
        (4 * Real.pi * (c ^ 2 + d ^ 2)) + 2 / 3 -
          2 * pairFunctional (obstacleLogProfile (M / m)) := by
  simpa only [← diffeomorphTensorPullback_add,
    oneFormDissipation_diffeomorphTensorPullback] using
    D.hemisphereDeficit_logProfile_eq_normalized_constant_zonal m M hm hb c d hcd

/-- The normalized pulled-back action controls the full logarithm's distance from
the even extension of the canonical obstacle optimizer. -/
theorem oneFormDissipation_pullback_constant_zonal_controls_evenExtension (D : PoleData)
    (F : RotationalSphere ≃ₘ⟮𝓡 2, 𝓡 2⟯ RotationalSphere)
    (m M : ℝ) (hm : 0 < m)
    (hb : ∀ v ∈ Icc (-1 : ℝ) 1, m ≤ D.a v ∧ D.a v ≤ M)
    (c d : ℝ) (hcd : 0 < c ^ 2 + d ^ 2) :
    (∫ v in (-1 : ℝ)..1,
      (Real.log (M / D.a v) - obstacleLogProfile (M / m) |v|) ^ 2) ≤
      (oneFormDissipation (Diffeomorph.pullbackMetric D.metric F)
        (diffeomorphTensorPullback F (D.meridionalOneForm (fun _ => c) contDiff_const) +
          diffeomorphTensorPullback F (D.azimuthalOneForm (fun _ => d) contDiff_const)) /
        (4 * Real.pi * (c ^ 2 + d ^ 2)) + 2 / 3 -
          2 * pairFunctional (obstacleLogProfile (M / m))) / stabilityConstant (M / m) := by
  simpa only [← diffeomorphTensorPullback_add,
    oneFormDissipation_diffeomorphTensorPullback] using
    D.oneFormDissipation_constant_zonal_controls_evenExtension m M hm hb c d hcd

/-- The normalized pulled-back action controls equatorial reflection error with the
same factor four as the two-hemisphere stability theorem. -/
theorem oneFormDissipation_pullback_constant_zonal_controls_reflection (D : PoleData)
    (F : RotationalSphere ≃ₘ⟮𝓡 2, 𝓡 2⟯ RotationalSphere)
    (m M : ℝ) (hm : 0 < m)
    (hb : ∀ v ∈ Icc (-1 : ℝ) 1, m ≤ D.a v ∧ D.a v ≤ M)
    (c d : ℝ) (hcd : 0 < c ^ 2 + d ^ 2) :
    (∫ v in (-1 : ℝ)..1,
      (Real.log (M / D.a v) - Real.log (M / D.a (-v))) ^ 2) ≤
      4 * (oneFormDissipation (Diffeomorph.pullbackMetric D.metric F)
        (diffeomorphTensorPullback F (D.meridionalOneForm (fun _ => c) contDiff_const) +
          diffeomorphTensorPullback F (D.azimuthalOneForm (fun _ => d) contDiff_const)) /
        (4 * Real.pi * (c ^ 2 + d ^ 2)) + 2 / 3 -
          2 * pairFunctional (obstacleLogProfile (M / m))) / stabilityConstant (M / m) := by
  simpa only [← diffeomorphTensorPullback_add,
    oneFormDissipation_diffeomorphTensorPullback] using
    D.oneFormDissipation_constant_zonal_controls_reflection m M hm hb c d hcd

/-- The normalized pulled-back action controls the full logarithm's error from its
actual equatorial symmetrization. -/
theorem oneFormDissipation_pullback_constant_zonal_controls_symmetrization (D : PoleData)
    (F : RotationalSphere ≃ₘ⟮𝓡 2, 𝓡 2⟯ RotationalSphere)
    (m M : ℝ) (hm : 0 < m)
    (hb : ∀ v ∈ Icc (-1 : ℝ) 1, m ≤ D.a v ∧ D.a v ≤ M)
    (c d : ℝ) (hcd : 0 < c ^ 2 + d ^ 2) :
    (∫ v in (-1 : ℝ)..1,
      (Real.log (M / D.a v) -
        (Real.log (M / D.a v) + Real.log (M / D.a (-v))) / 2) ^ 2) ≤
      (oneFormDissipation (Diffeomorph.pullbackMetric D.metric F)
        (diffeomorphTensorPullback F (D.meridionalOneForm (fun _ => c) contDiff_const) +
          diffeomorphTensorPullback F (D.azimuthalOneForm (fun _ => d) contDiff_const)) /
        (4 * Real.pi * (c ^ 2 + d ^ 2)) + 2 / 3 -
          2 * pairFunctional (obstacleLogProfile (M / m))) / stabilityConstant (M / m) := by
  simpa only [← diffeomorphTensorPullback_add,
    oneFormDissipation_diffeomorphTensorPullback] using
    D.oneFormDissipation_constant_zonal_controls_symmetrization m M hm hb c d hcd

/-- Zero coefficients give a zero pulled-back section and action, without division
or any profile conclusion. -/
theorem pullback_constant_zonal_zero_of_sq_sum_eq_zero (D : PoleData)
    (F : RotationalSphere ≃ₘ⟮𝓡 2, 𝓡 2⟯ RotationalSphere)
    (c d : ℝ) (hcd : c ^ 2 + d ^ 2 = 0) :
    c = 0 ∧ d = 0 ∧
      diffeomorphTensorPullback F (D.meridionalOneForm (fun _ => c) contDiff_const) +
        diffeomorphTensorPullback F (D.azimuthalOneForm (fun _ => d) contDiff_const) = 0 ∧
      oneFormDissipation (Diffeomorph.pullbackMetric D.metric F)
        (diffeomorphTensorPullback F (D.meridionalOneForm (fun _ => c) contDiff_const) +
          diffeomorphTensorPullback F (D.azimuthalOneForm (fun _ => d) contDiff_const)) = 0 := by
  obtain ⟨hc, hd, hsection, hQ⟩ := D.constant_zonal_zero_of_sq_sum_eq_zero c d hcd
  refine ⟨hc, hd, ?_, ?_⟩
  · rw [← diffeomorphTensorPullback_add, hsection, diffeomorphTensorPullback_zero]
  · simpa only [← diffeomorphTensorPullback_add,
      oneFormDissipation_diffeomorphTensorPullback] using hQ

end RotationalProfile.PoleData

namespace IsRepresentedRotationalMetric

/-- One actual representation gives the exact deficit budget and all three errors
for every positive profile box and nonzero constant-zonal coefficient pair.
The separate zero case has no normalization or profile conclusion. -/
theorem exists_stability_representation
    {g : SmoothRiemannianMetric (𝓡 2) RotationalSphere}
    (hg : IsRepresentedRotationalMetric g) :
    ∃ D : RotationalProfile.PoleData,
      ∃ F : RotationalSphere ≃ₘ⟮𝓡 2, 𝓡 2⟯ RotationalSphere,
        g = Diffeomorph.pullbackMetric D.metric F ∧
        (∀ (m M : ℝ), 0 < m →
          (∀ v ∈ Icc (-1 : ℝ) 1, m ≤ D.a v ∧ D.a v ≤ M) →
          ∀ (c d : ℝ), 0 < c ^ 2 + d ^ 2 →
          let B := oneFormDissipation g
            (diffeomorphTensorPullback F (D.meridionalOneForm (fun _ => c) contDiff_const) +
              diffeomorphTensorPullback F (D.azimuthalOneForm (fun _ => d) contDiff_const)) /
            (4 * Real.pi * (c ^ 2 + d ^ 2)) + 2 / 3 -
              2 * pairFunctional (obstacleLogProfile (M / m))
          hemisphereDeficit (M / m) (fun v => Real.log (M / D.a v)) = B ∧
          (∫ v in (-1 : ℝ)..1,
            (Real.log (M / D.a v) - obstacleLogProfile (M / m) |v|) ^ 2) ≤
              B / stabilityConstant (M / m) ∧
          (∫ v in (-1 : ℝ)..1,
            (Real.log (M / D.a v) - Real.log (M / D.a (-v))) ^ 2) ≤
              4 * B / stabilityConstant (M / m) ∧
          (∫ v in (-1 : ℝ)..1,
            (Real.log (M / D.a v) -
              (Real.log (M / D.a v) + Real.log (M / D.a (-v))) / 2) ^ 2) ≤
              B / stabilityConstant (M / m)) ∧
        (∀ (c d : ℝ), c ^ 2 + d ^ 2 = 0 →
          diffeomorphTensorPullback F (D.meridionalOneForm (fun _ => c) contDiff_const) +
            diffeomorphTensorPullback F (D.azimuthalOneForm (fun _ => d) contDiff_const) = 0 ∧
          oneFormDissipation g
            (diffeomorphTensorPullback F (D.meridionalOneForm (fun _ => c) contDiff_const) +
              diffeomorphTensorPullback F
                (D.azimuthalOneForm (fun _ => d) contDiff_const)) = 0) := by
  obtain ⟨D, F, rfl⟩ := hg
  refine ⟨D, F, rfl, ?_, ?_⟩
  · intro m M hm hb c d hcd
    exact ⟨D.hemisphereDeficit_logProfile_eq_normalized_pullback_constant_zonal
        F m M hm hb c d hcd,
      D.oneFormDissipation_pullback_constant_zonal_controls_evenExtension F m M hm hb c d hcd,
      D.oneFormDissipation_pullback_constant_zonal_controls_reflection F m M hm hb c d hcd,
      D.oneFormDissipation_pullback_constant_zonal_controls_symmetrization F m M hm hb c d hcd⟩
  · intro c d hcd
    exact (D.pullback_constant_zonal_zero_of_sq_sum_eq_zero F c d hcd).2.2

end IsRepresentedRotationalMetric
end RicciFlowSharpEstimate.Geometry
