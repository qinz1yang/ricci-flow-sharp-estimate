/-
Copyright (c) 2026 Ziyang Qin. All rights reserved.
No license is granted by this file.
Authors: Ziyang Qin
-/
import RicciFlowSharpEstimate.Geometry.NormalizedAreaRayleigh
import RicciFlowSharpEstimate.Geometry.SmoothAreaInfimum

/-!
# The smooth area infimum and the original geometric quotient

Every nonzero original meridional form in an original positive curvature box
gives an actual smooth normalized area competitor. The smooth area infimum
therefore bounds the complete physical quotient after multiplication by the
square of the original profile's actual area scale.
-/

noncomputable section

namespace RicciFlowSharpEstimate.Geometry.RotationalProfile.PoleData.AreaNormalization

open Set MeasureTheory
open DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Tensor0SBundle DifferentialGeometry.Integral.Measure
open scoped ContDiff Manifold

variable {D : RotationalProfile.PoleData}

private local instance : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 2 + 1) :=
  ⟨finrank_euclideanSpace_fin⟩

private local instance : MeasurableSpace RotationalSphere := borel RotationalSphere
private local instance : BorelSpace RotationalSphere := ⟨rfl⟩

/-- The original curvature box and actual nonzero physical form produce a smooth
unit-mass competitor with the same pinching ratio and both exact moments. -/
theorem isSmoothAreaCompetitor_normalizedProbe (N : AreaNormalization D)
    (C κ Λ : ℝ) (hκ : 0 < κ)
    (hbox : ∀ p : RotationalSphere, κ ≤ metricScalarAt D.metric p / 2 ∧
      metricScalarAt D.metric p / 2 ≤ Λ)
    (hratio : Λ / κ ≤ C) (R : ℝ → ℝ) (hR : ContDiff ℝ ∞ R)
    (hne : D.meridionalOneForm R hR ≠ 0) :
    AreaProfile.IsSmoothAreaCompetitor C N.curvature
      (AreaProfile.normalizedProbe N.curvature (N.probe R)) := by
  have hm := (N.probeMass_pos_iff_meridional_ne_zero R hR).mpr hne
  obtain ⟨hlo, hb, hrat⟩ := N.curvature_bounds_scaled κ Λ hκ hbox
  refine ⟨N.curvature_contDiff, contDiff_const.mul (N.probe_contDiff R hR),
    ?_, N.integral_curvature, N.integral_mul_curvature,
    AreaProfile.probeMass_normalizedProbe _ _ hm⟩
  refine ⟨ReciprocalArea.length D.a * κ, ReciprocalArea.length D.a * Λ,
    hlo, hb, ?_⟩
  rw [hrat]
  exact hratio

/-- The smooth normalized infimum bounds the complete quotient of the same
original nonzero form and metric, with their exact squared area-scale factor. -/
theorem smoothAreaInfimum_le_length_sq_mul_oneFormDissipation_div_normSq
    (N : AreaNormalization D) (C : ℝ) (hC : 1 ≤ C)
    (κ Λ : ℝ) (hκ : 0 < κ)
    (hbox : ∀ p : RotationalSphere, κ ≤ metricScalarAt D.metric p / 2 ∧
      metricScalarAt D.metric p / 2 ≤ Λ)
    (hratio : Λ / κ ≤ C) (R : ℝ → ℝ) (hR : ContDiff ℝ ∞ R)
    (hne : D.meridionalOneForm R hR ≠ 0) :
    AreaProfile.smoothAreaInfimum C ≤ (ReciprocalArea.length D.a) ^ 2 *
      (oneFormDissipation D.metric (D.meridionalOneForm R hR) /
        (∫ p : RotationalSphere, normSq0S D.metric p 1 (D.meridionalOneForm R hR p)
          ∂(riemannianVolumeMeasure (I := 𝓡 2) (M := RotationalSphere) D.metric))) := by
  have hm := (N.probeMass_pos_iff_meridional_ne_zero R hR).mpr hne
  have hL := ReciprocalArea.length_pos D.a D.a_contDiff.continuous D.a_pos
  calc
    AreaProfile.smoothAreaInfimum C ≤
        AreaProfile.meridionalAction N.curvature
          (AreaProfile.normalizedProbe N.curvature (N.probe R)) :=
      AreaProfile.smoothAreaInfimum_le_action C hC _ _
        (N.isSmoothAreaCompetitor_normalizedProbe C κ Λ hκ hbox hratio R hR hne)
    _ = AreaProfile.rayleighQuotient N.curvature (N.probe R) :=
      AreaProfile.meridionalAction_normalizedProbe _ _ N.curvature_contDiff
        (N.probe_contDiff R hR) N.integral_curvature N.integral_mul_curvature hm
    _ = _ := by
      rw [N.oneFormDissipation_div_normSq_eq R hR]
      field_simp [hL.ne']

end RicciFlowSharpEstimate.Geometry.RotationalProfile.PoleData.AreaNormalization
