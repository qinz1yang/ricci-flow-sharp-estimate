/-
Copyright (c) 2026 Ziyang Qin. All rights reserved.
No license is granted by this file.
Authors: Ziyang Qin
-/
import RicciFlowSharpEstimate.Geometry.RotationalVolume
import RicciFlowSharpEstimate.Geometry.RotationalOneForms
import DifferentialGeometry.Geometry.Metric.TensorInner.Cotangent.InverseMetric
import DifferentialGeometry.Geometry.Metric.TensorInner.Tensor0S.Scaling

/-!
# The metric dual and norm of the height differential

The formulas use the actual cotangent metric, including at both poles.
Adapted from Ziyang Qin's historical `RotationalSphereCometric.lean`.
-/

noncomputable section

namespace RicciFlowSharpEstimate.Geometry

open Bundle DifferentialGeometry DifferentialGeometry.Geometry
open DifferentialGeometry.Geometry.Operator DifferentialGeometry.Tensor0SBundle
open scoped Manifold ContDiff

local instance : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 2 + 1) :=
  ⟨finrank_euclideanSpace_fin⟩

namespace RotationalProfile.PoleData

/-- The metric dual of height is the scaled round height gradient. -/
theorem inverseMetricSharpFib_heightOneForm (D : PoleData) (x : RotationalSphere) :
    inverseMetricSharpFib D.metric x (heightOneForm x) =
      (D.b (sphereHeight x) / D.a (sphereHeight x) ^ 2) •
        gradFun HeightMetricCoefficients.round sphereHeight x := by
  apply metricFlatLinear_injective D.metric x
  ext w
  change D.metric.inner x (inverseMetricSharpFib D.metric x (heightOneForm x)) w = _
  rw [inverseMetricSharpFib_inner, cotangentToDualLinear_apply, cotangentToDual_apply]
  rw [metricFlatLinear_apply, D.metric_inner]
  simp only [map_smul, smul_apply, smul_eq_mul]
  have hheight (v : TangentSpace (𝓡 2) x) :
      heightOneForm x (fun _ : Fin 1 => v) =
        HeightMetricCoefficients.round.inner x
          (gradFun HeightMetricCoefficients.round sphereHeight x) v := by
    change mfderiv (𝓡 2) 𝓘(ℝ, ℝ) sphereHeight x v = _
    exact (inner_gradFun _ _ _ _).symm
  simp_rw [hheight]
  rw [map_smul, smul_eq_mul, round_grad_sphereHeight_inner_self]
  have ha := (D.a_pos _ (sphereHeight_mem_Icc x)).ne'
  have hb := (D.b_pos _ (sphereHeight_mem_Icc x)).ne'
  have hrad := D.radial_factor (sphereHeight x)
  field_simp [ha, hb]
  rw [show D.a (sphereHeight x) ^ 2 = D.b (sphereHeight x) ^ 2 +
    D.c (sphereHeight x) * (1 - sphereHeight x ^ 2) by nlinarith [hrad]]

/-- Exact norm of the genuine height covector for the produced metric. -/
theorem heightOneForm_normSq (D : PoleData) (x : RotationalSphere) :
    normSq0S D.metric x 1 (heightOneForm x) =
      warp D.a (sphereHeight x) / D.a (sphereHeight x) ^ 2 := by
  rw [normSq0S_eq_inner, inner0S_one_eq_cotangent, cotangentInner_eq_sharp]
  change cometricBilin D.metric x (heightOneForm x) (heightOneForm x) = _
  rw [cometricBilin_eq_dual_sharp, D.inverseMetricSharpFib_heightOneForm,
    cotangentToDualLinear_apply, cotangentToDual_apply]
  rw [heightOneForm_apply, map_smul, smul_eq_mul, mvfderiv_real_eq_mfderiv,
    ← inner_gradFun, round_grad_sphereHeight_inner_self, D.warp_factor]
  change D.b (sphereHeight x) / D.a (sphereHeight x) ^ 2 * (1 - sphereHeight x ^ 2) = _
  ring

/-- The meridional form has the actual pointwise norm `f r²`. -/
theorem meridionalOneForm_normSq (D : PoleData) (r : ℝ → ℝ)
    (hr : ContDiff ℝ ∞ r) (x : RotationalSphere) :
    normSq0S D.metric x 1 (D.meridionalOneForm r hr x) =
      warp D.a (sphereHeight x) * r (sphereHeight x) ^ 2 := by
  change normSq0S D.metric x 1
    ((D.a (sphereHeight x) * r (sphereHeight x)) • heightOneForm x) = _
  rw [normSq0S_smul, D.heightOneForm_normSq]
  field_simp [(D.a_pos _ (sphereHeight_mem_Icc x)).ne']

end RotationalProfile.PoleData

end RicciFlowSharpEstimate.Geometry
