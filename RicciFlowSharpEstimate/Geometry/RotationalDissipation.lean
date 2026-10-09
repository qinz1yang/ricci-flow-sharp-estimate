/-
Copyright (c) 2026 Ziyang Qin. All rights reserved.
No license is granted by this file.
Authors: Ziyang Qin
-/
import RicciFlowSharpEstimate.Geometry.OneFormDissipation
import RicciFlowSharpEstimate.Geometry.RotationalCurvature
import RicciFlowSharpEstimate.Geometry.RotationalVolume

/-!
# The complete action for the produced rotational metric

The actual curvature and volume identities specialize the canonical four-term
action without replacing the section or either of its covariant derivatives.
-/

noncomputable section

namespace RicciFlowSharpEstimate.Geometry

open DifferentialGeometry DifferentialGeometry.Geometry DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Tensor.RicciIdentity
open DifferentialGeometry.PDE.RicciFlow DifferentialGeometry.Integral.Measure
open MeasureTheory
open scoped Manifold ContDiff

local instance : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 2 + 1) :=
  ⟨finrank_euclideanSpace_fin⟩
local instance : CompactSpace RotationalSphere := Metric.sphere.compactSpace _ _
private local instance : MeasurableSpace RotationalSphere := borel RotationalSphere
private local instance : BorelSpace RotationalSphere := ⟨rfl⟩

namespace RotationalProfile.PoleData

/-- The complete density uses the actual reciprocal profile as Gauss curvature. -/
theorem oneFormDissipationDensity_metric (D : PoleData)
    (h : OneFormSection (I := 𝓡 2) (M := RotationalSphere)) (x : RotationalSphere) :
    oneFormDissipationDensity D.metric h x =
      normSq0S D.metric x 1 (roughLap0SField D.metric h x) +
        (1 / D.a (sphereHeight x)) ^ 2 * normSq0S D.metric x 1 (h x) -
        (1 / D.a (sphereHeight x)) * normSq0S D.metric x 2 (metricNabla0S D.metric h x) +
        2 * (1 / D.a (sphereHeight x)) *
          normSq0S D.metric x 2 (ahlforsPart D.metric (metricNabla0S D.metric h) x) := by
  have hK : metricScalarAt D.metric x / 2 = 1 / D.a (sphereHeight x) := by
    rw [D.metricScalarAt_metric]
    ring
  simp only [oneFormDissipationDensity, hK]

/-- The full action expressed against the same actual round volume measure. -/
theorem oneFormDissipation_eq_weightedRoundIntegral (D : PoleData)
    (h : OneFormSection (I := 𝓡 2) (M := RotationalSphere)) :
    oneFormDissipation D.metric h =
      ∫ x : RotationalSphere, D.a (sphereHeight x) * oneFormDissipationDensity D.metric h x
        ∂(riemannianVolumeMeasure (𝓡 2) RotationalSphere HeightMetricCoefficients.round) := by
  exact D.integral_volume_metric (oneFormDissipationDensity D.metric h)

/-- The weighted round integrand is genuinely integrable for every smooth form. -/
theorem weighted_dissipationDensity_integrable (D : PoleData)
    (h : OneFormSection (I := 𝓡 2) (M := RotationalSphere)) :
    Integrable (fun x : RotationalSphere =>
      D.a (sphereHeight x) * oneFormDissipationDensity D.metric h x)
      (riemannianVolumeMeasure (𝓡 2) RotationalSphere HeightMetricCoefficients.round) := by
  let := riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace HeightMetricCoefficients.round
  exact ((D.a_contDiff.continuous.comp sphereHeight_contMDiff.continuous).mul
    (oneFormDissipationDensity_smooth D.metric h).continuous).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)

end RotationalProfile.PoleData

end RicciFlowSharpEstimate.Geometry
