/-
Copyright (c) 2026 Ziyang Qin. All rights reserved.
No license is granted by this file.
Authors: Ziyang Qin
-/
import RicciFlowSharpEstimate.Geometry.OneFormScalarization
import RicciFlowSharpEstimate.Geometry.RotationalAreaForm
import RicciFlowSharpEstimate.Geometry.RotationalCurvature

/-!
# Scalarization for the produced rotational metric

The area tensor and curvature in the surface identity are those already produced
from the same balanced profile. The only inputs are the original data and form.
-/

noncomputable section

namespace RicciFlowSharpEstimate.Geometry

open MeasureTheory DifferentialGeometry DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Tensor.RicciIdentity DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.Integral.Measure
open scoped Manifold ContDiff

local instance : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 2 + 1) :=
  ⟨finrank_euclideanSpace_fin⟩
local instance : CompactSpace RotationalSphere := Metric.sphere.compactSpace _ _
private local instance : MeasurableSpace RotationalSphere := borel RotationalSphere
private local instance : BorelSpace RotationalSphere := ⟨rfl⟩

namespace RotationalProfile.PoleData

/-- Literal scalarization of the original complete action, with the produced area
tensor and actual reciprocal-profile curvature, for every smooth one-form. -/
theorem oneFormDissipation_scalarization (D : PoleData)
    (h : OneFormSection (I := 𝓡 2) (M := RotationalSphere)) :
    oneFormDissipation D.metric h =
      (∫ x, normSq0S D.metric x 3
          (metricNabla0S D.metric (ahlforsPart D.metric (metricNabla0S D.metric h)) x)
        ∂(riemannianVolumeMeasure (I := 𝓡 2) (M := RotationalSphere) D.metric)) +
      3 * (∫ x, (1 / D.a (sphereHeight x)) *
          normSq0S D.metric x 2 (ahlforsPart D.metric (metricNabla0S D.metric h) x)
        ∂(riemannianVolumeMeasure (I := 𝓡 2) (M := RotationalSphere) D.metric)) +
      (1 / 2 : ℝ) *
        ((∫ x, normSq0S D.metric x 1 (differential1FormFun (oneFormTrace D.metric h) x) -
            (1 / D.a (sphereHeight x)) * oneFormTrace D.metric h x ^ 2
          ∂(riemannianVolumeMeasure (I := 𝓡 2) (M := RotationalSphere) D.metric)) +
        ∫ x, normSq0S D.metric x 1
            (differential1FormFun (oneFormCurl D.metric D.areaForm h) x) -
            (1 / D.a (sphereHeight x)) * oneFormCurl D.metric D.areaForm h x ^ 2
          ∂(riemannianVolumeMeasure (I := 𝓡 2) (M := RotationalSphere) D.metric)) := by
  have hK (x : RotationalSphere) : metricScalarAt D.metric x / 2 =
      1 / D.a (sphereHeight x) := by
    rw [D.metricScalarAt_metric]
    ring
  simpa only [hK] using
    RicciFlowSharpEstimate.Geometry.oneFormDissipation_scalarization
      D.metric D.areaForm h D.areaForm_alternating D.areaForm_normSq

end RotationalProfile.PoleData
end RicciFlowSharpEstimate.Geometry
