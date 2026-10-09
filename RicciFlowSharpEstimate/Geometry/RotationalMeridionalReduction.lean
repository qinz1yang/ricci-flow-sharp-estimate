/-
Copyright (c) 2026 Ziyang Qin. All rights reserved.
No license is granted by this file.
Authors: Ziyang Qin
-/
import RicciFlowSharpEstimate.Geometry.RotationalMeridionalHessian
import RicciFlowSharpEstimate.Geometry.ExactOneFormRoughLaplacian
import RicciFlowSharpEstimate.Geometry.SymmetricTensorContractions
import RicciFlowSharpEstimate.Geometry.RotationalCometric
import RicciFlowSharpEstimate.Geometry.RotationalDissipation
import RicciFlowSharpEstimate.Geometry.MeridionalAction

/-!
# Exact meridional reduction of the complete geometric action

All contractions refer to the canonical derivatives of the original global section.
The formulas include both poles, and height disintegration supplies the factor `2*pi`.
-/

noncomputable section

namespace RicciFlowSharpEstimate.Geometry

open Bundle DifferentialGeometry DifferentialGeometry.Geometry DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Geometry.Operator DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Geometry.Connection DifferentialGeometry.Integral.Connection
open MeasureTheory Set
open scoped Manifold ContDiff

local instance : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 2 + 1) :=
  ⟨finrank_euclideanSpace_fin⟩
local instance : CompactSpace RotationalSphere := Metric.sphere.compactSpace _ _
private local instance : MeasurableSpace RotationalSphere := borel RotationalSphere
private local instance : BorelSpace RotationalSphere := ⟨rfl⟩

namespace RotationalProfile.PoleData

private theorem meridional_nabla_eval (D : PoleData) (r : ℝ → ℝ)
    (hr : ContDiff ℝ ∞ r) (x : RotationalSphere) (v : Fin 2 → TangentSpace (𝓡 2) x) :
    metricNabla0S D.metric (D.meridionalOneForm r hr) x v =
      (D.a (sphereHeight x) * deriv r (sphereHeight x)) *
        heightOneForm x (fun _ => v 0) * heightOneForm x (fun _ => v 1) +
      (-sphereHeight x * r (sphereHeight x)) * D.metric.inner x (v 0) (v 1) := by
  rw [D.metricNabla0S_meridionalOneForm]
  ring

/-- The exact trace of the canonical meridional derivative. -/
theorem meridionalOneForm_nabla_trace (D : PoleData) (r : ℝ → ℝ)
    (hr : ContDiff ℝ ∞ r) (x : RotationalSphere) :
    metricTracePair0SAt D.metric (metricNabla0S D.metric (D.meridionalOneForm r hr) x) =
      D.meridionalWeight (sphereHeight x) * deriv r (sphereHeight x) -
        2 * sphereHeight x * r (sphereHeight x) := by
  rw [metricTracePair0SAt_of_apply_eq_rankOne_add_metric D.metric x _ _ _ _
    (meridional_nabla_eval D r hr x), D.heightOneForm_normSq, finrank_euclideanSpace_fin]
  dsimp [meridionalWeight]
  field_simp [(D.a_pos _ (sphereHeight_mem_Icc x)).ne']
  ring

/-- The two principal values give the full first-derivative norm. -/
theorem meridionalOneForm_nabla_normSq (D : PoleData) (r : ℝ → ℝ)
    (hr : ContDiff ℝ ∞ r) (x : RotationalSphere) :
    normSq0S D.metric x 2 (metricNabla0S D.metric (D.meridionalOneForm r hr) x) =
      (D.meridionalWeight (sphereHeight x) * deriv r (sphereHeight x) -
        sphereHeight x * r (sphereHeight x)) ^ 2 +
      (sphereHeight x * r (sphereHeight x)) ^ 2 := by
  rw [normSq0S_of_apply_eq_rankOne_add_metric D.metric x _ _ _ _
    (meridional_nabla_eval D r hr x), D.heightOneForm_normSq, finrank_euclideanSpace_fin]
  dsimp [meridionalWeight]
  field_simp [(D.a_pos _ (sphereHeight_mem_Icc x)).ne']
  ring

/-- The Ahlfors term retains precisely the trace-free part of the actual Hessian. -/
theorem meridionalOneForm_ahlfors_normSq (D : PoleData) (r : ℝ → ℝ)
    (hr : ContDiff ℝ ∞ r) (x : RotationalSphere) :
    normSq0S D.metric x 2
      (ahlforsPart D.metric (metricNabla0S D.metric (D.meridionalOneForm r hr)) x) =
        (D.meridionalWeight (sphereHeight x) * deriv r (sphereHeight x)) ^ 2 / 2 := by
  rw [normSq0S_ahlforsPart_of_apply_eq_rankOne_add_metric finrank_euclideanSpace_fin
    D.metric x _ _ _ _ (meridional_nabla_eval D r hr x), D.heightOneForm_normSq]
  dsimp [meridionalWeight]
  field_simp [(D.a_pos _ (sphereHeight_mem_Icc x)).ne']

/-- The actual scalar Laplacian of the global potential is its Hessian trace. -/
theorem laplacian_meridionalPotential (D : PoleData) (r : ℝ → ℝ)
    (hr : ContDiff ℝ ∞ r) (x : RotationalSphere) :
    laplacian (metricCov D.metric) D.metric (D.meridionalPotential r) x =
      D.meridionalWeight (sphereHeight x) * deriv r (sphereHeight x) -
        2 * sphereHeight x * r (sphereHeight x) := by
  have h := (scalarLap_smooth (metricCov D.metric) (metricCov_smooth D.metric) D.metric
    (leviCivitaConnectionOfMetric_isMetricCompatible D.metric)
    (D.meridionalPotential r) (D.meridionalPotential_contMDiff r hr) (x := x)).eq_trace
      (metricCov D.metric) D.metric (D.meridionalPotential r) _
  rw [h, scalarLapTraceAt_eq_pair]
  change metricTracePair0SAt D.metric
    (leviHessSec D.metric (D.meridionalPotential r) (D.meridionalPotential_contMDiff r hr) x) = _
  rw [← D.metricNabla0S_meridionalOneForm_eq_leviHessSec]
  exact D.meridionalOneForm_nabla_trace r hr x

private theorem traceProfile_hasDerivAt (D : PoleData) (r : ℝ → ℝ)
    (hr : ContDiff ℝ ∞ r) (v : ℝ) (hv : v ∈ Icc (-1 : ℝ) 1) :
    HasDerivAt (fun z => D.meridionalWeight z * deriv r z - 2 * z * r z)
      (D.meridionalOperator r v - r v) v := by
  have hH := (D.meridionalWeight_hasDerivAt v hv).differentiableAt.hasDerivAt
  have hr₁ := (hr.differentiable (by simp) v).hasDerivAt
  have hr₂ := ((contDiff_infty_iff_deriv.mp hr).2.differentiable (by simp) v).hasDerivAt
  convert (hH.mul hr₂).sub (((hasDerivAt_id v).const_mul 2).mul hr₁) using 1
  · funext z
    dsimp
  · dsimp [meridionalOperator]
    ring

/-- The rough Laplacian is the claimed scalar operator times the actual height differential. -/
theorem roughLap0SField_meridionalOneForm (D : PoleData) (r : ℝ → ℝ)
    (hr : ContDiff ℝ ∞ r) (x : RotationalSphere) :
    roughLap0SField D.metric (D.meridionalOneForm r hr) x =
      D.meridionalOperator r (sphereHeight x) • heightOneForm x := by
  have hfun : laplacian (metricCov D.metric) D.metric (D.meridionalPotential r) =
      fun y => D.meridionalWeight (sphereHeight y) * deriv r (sphereHeight y) -
        2 * sphereHeight y * r (sphereHeight y) := funext (D.laplacian_meridionalPotential r hr)
  have h := roughLap0SField_duSec_of_finrank_eq_two D.metric finrank_euclideanSpace_fin
    (D.meridionalPotential r) (D.meridionalPotential_contMDiff r hr) x
  rw [D.duSec_meridionalPotential r hr, hfun, D.metricScalarAt_metric] at h
  rw [h]
  ext slots
  have hs : slots = fun _ : Fin 1 => slots 0 := by funext i; exact congrArg slots (Fin.eq_zero i)
  rw [hs]
  simp only [Tensor0SSpace.add_apply, Tensor0SSpace.smul_apply, smul_eq_mul]
  rw [differential1FormFun_apply_eq_mvfderiv, D.meridionalOneForm_apply]
  let t := fun z => D.meridionalWeight z * deriv r z - 2 * z * r z
  have ht := traceProfile_hasDerivAt D r hr (sphereHeight x) (sphereHeight_mem_Icc x)
  change mvfderiv (𝓡 2) (t ∘ sphereHeight) x (slots 0) + _ = _
  rw [mvfderiv_comp_apply x ht.differentiableAt.mdifferentiableAt
    (sphereHeight_contMDiff.mdifferentiableAt (by simp)), mvfderiv_real_model_eq_fderiv,
    ht.hasFDerivAt.fderiv]
  simp only [ContinuousLinearMap.toSpanSingleton_apply, smul_eq_mul]
  change heightOneForm x (fun _ : Fin 1 => slots 0) *
    (D.meridionalOperator r (sphereHeight x) - r (sphereHeight x)) + _ = _
  field_simp [(D.a_pos _ (sphereHeight_mem_Icc x)).ne']
  ring

/-- All four terms of the complete geometric density reduce to the scalar density. -/
theorem oneFormDissipationDensity_meridional (D : PoleData) (r : ℝ → ℝ)
    (hr : ContDiff ℝ ∞ r) (x : RotationalSphere) :
    D.a (sphereHeight x) * oneFormDissipationDensity D.metric (D.meridionalOneForm r hr) x =
      D.meridionalDensity r (sphereHeight x) := by
  rw [D.oneFormDissipationDensity_metric, D.roughLap0SField_meridionalOneForm,
    normSq0S_smul, D.heightOneForm_normSq, D.meridionalOneForm_normSq,
    D.meridionalOneForm_nabla_normSq, D.meridionalOneForm_ahlfors_normSq]
  dsimp [meridionalDensity, meridionalWeight]
  field_simp [(D.a_pos _ (sphereHeight_mem_Icc x)).ne']
  ring

/-- Exact meridional reduction for the original global form and metric. -/
theorem oneFormDissipation_meridional (D : PoleData) (r : ℝ → ℝ)
    (hr : ContDiff ℝ ∞ r) :
    oneFormDissipation D.metric (D.meridionalOneForm r hr) =
      2 * Real.pi * D.meridionalAction r := by
  rw [D.oneFormDissipation_eq_weightedRoundIntegral]
  simp_rw [D.oneFormDissipationDensity_meridional]
  exact integral_round_height (D.meridionalDensity_continuousOn r hr)

/-- The actual round unit probe has dissipation `8*pi/3` at every positive scale. -/
theorem oneFormDissipation_constant_meridional_one (c : ℝ) (hc : 0 < c) :
    oneFormDissipation (constant c hc).metric
      ((constant c hc).meridionalOneForm (fun _ => 1) contDiff_const) = 8 * Real.pi / 3 := by
  rw [oneFormDissipation_meridional, meridionalAction_constant_one]
  ring

end RotationalProfile.PoleData

end RicciFlowSharpEstimate.Geometry
