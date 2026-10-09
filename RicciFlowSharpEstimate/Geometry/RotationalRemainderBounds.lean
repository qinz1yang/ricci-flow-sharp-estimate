/-
Copyright (c) 2026 Ziyang Qin. All rights reserved.
No license is granted by this file.
Authors: Ziyang Qin
-/
import RicciFlowSharpEstimate.Geometry.RotationalScalarization
import RicciFlowSharpEstimate.Geometry.RotationalScalarGap
import RicciFlowSharpEstimate.Geometry.RotationalScalarCompatibility

/-!
# Positive terms controlled by the original Haar remainder action

The scalar gap applies to the actual trace and curl of the canonical first
derivative. Combined with the original scalarization it controls three positive
weighted integrals, without a curvature pinching assumption.
-/

noncomputable section

namespace RicciFlowSharpEstimate.Geometry

open MeasureTheory DifferentialGeometry DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Tensor.RicciIdentity DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.PDE.RicciFlow DifferentialGeometry.Integral.Measure
open scoped Manifold ContDiff

local instance : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 2 + 1) :=
  ⟨finrank_euclideanSpace_fin⟩
local instance : CompactSpace RotationalSphere := Metric.sphere.compactSpace _ _
private local instance : MeasurableSpace RotationalSphere := borel RotationalSphere
private local instance : BorelSpace RotationalSphere := ⟨rfl⟩

namespace RotationalProfile.PoleData

/-- The original remainder action controls its actual Ahlfors, trace and curl energies. -/
theorem oneFormDissipation_remainder_lower_bound (D : PoleData)
    (h : OneFormSection (I := 𝓡 2) (M := RotationalSphere)) :
    let k := h - rotationalAverage h
    let μ := riemannianVolumeMeasure (I := 𝓡 2) (M := RotationalSphere) D.metric
    3 * (∫ x, (1 / D.a (sphereHeight x)) *
        normSq0S D.metric x 2 (ahlforsPart D.metric (metricNabla0S D.metric k) x) ∂μ) +
      (1 / 2 : ℝ) * ((∫ x, oneFormTrace D.metric k x ^ 2 / D.b (sphereHeight x) ∂μ) +
        ∫ x, oneFormCurl D.metric D.areaForm k x ^ 2 / D.b (sphereHeight x) ∂μ) ≤
      oneFormDissipation D.metric k := by
  let k := h - rotationalAverage h
  let μ := riemannianVolumeMeasure (I := 𝓡 2) (M := RotationalSphere) D.metric
  have htrace := D.integral_scalar_energy_ge_of_rotationalScalarAverage_eq_zero
    (oneFormTrace_contMDiff D.metric k) (D.rotationalScalarAverage_oneFormTrace_remainder h)
  have hcurl := D.integral_scalar_energy_ge_of_rotationalScalarAverage_eq_zero
    (oneFormCurl_contMDiff D.metric D.areaForm k)
    (D.rotationalScalarAverage_oneFormCurl_remainder h)
  have hgrad : 0 ≤ ∫ x, normSq0S D.metric x 3
      (metricNabla0S D.metric (ahlforsPart D.metric (metricNabla0S D.metric k)) x) ∂μ :=
    integral_nonneg (fun x => normSq0S_nonneg D.metric x 3 _)
  have hsplit := D.oneFormDissipation_scalarization k
  dsimp only [k, μ] at hgrad hsplit htrace hcurl ⊢
  linarith

/-- The genuine nonzonal complement has nonnegative original complete dissipation,
without any curvature pinching hypothesis. -/
theorem oneFormDissipation_remainder_nonneg (D : PoleData)
    (h : OneFormSection (I := 𝓡 2) (M := RotationalSphere)) :
    0 ≤ oneFormDissipation D.metric (h - rotationalAverage h) := by
  have hbound := D.oneFormDissipation_remainder_lower_bound h
  dsimp only at hbound
  have hA : 0 ≤ ∫ x, (1 / D.a (sphereHeight x)) *
      normSq0S D.metric x 2
        (ahlforsPart D.metric (metricNabla0S D.metric (h - rotationalAverage h)) x)
      ∂(riemannianVolumeMeasure (I := 𝓡 2) (M := RotationalSphere) D.metric) :=
    integral_nonneg (fun x => mul_nonneg
      (one_div_pos.mpr (D.a_pos _ (sphereHeight_mem_Icc x))).le
      (normSq0S_nonneg D.metric x 2 _))
  have htrace : 0 ≤ ∫ x, oneFormTrace D.metric (h - rotationalAverage h) x ^ 2 /
      D.b (sphereHeight x)
      ∂(riemannianVolumeMeasure (I := 𝓡 2) (M := RotationalSphere) D.metric) :=
    integral_nonneg (fun x => div_nonneg (sq_nonneg _) (D.b_pos _ (sphereHeight_mem_Icc x)).le)
  have hcurl : 0 ≤ ∫ x, oneFormCurl D.metric D.areaForm (h - rotationalAverage h) x ^ 2 /
      D.b (sphereHeight x)
      ∂(riemannianVolumeMeasure (I := 𝓡 2) (M := RotationalSphere) D.metric) :=
    integral_nonneg (fun x => div_nonneg (sq_nonneg _) (D.b_pos _ (sphereHeight_mem_Icc x)).le)
  linarith

end RotationalProfile.PoleData
end RicciFlowSharpEstimate.Geometry
