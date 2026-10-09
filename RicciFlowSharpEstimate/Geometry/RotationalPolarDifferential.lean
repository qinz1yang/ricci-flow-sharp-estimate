/-
Copyright (c) 2026 Ziyang Qin. All rights reserved.
No license is granted by this file.
Authors: Ziyang Qin
-/
import RicciFlowSharpEstimate.Geometry.RotationalPolarCoordinates
import RicciFlowSharpEstimate.Geometry.RotationalCometric
import DifferentialGeometry.Geometry.Operator.Hessian.Trace.Realization

/-!
# The actual scalar differential in polar coordinates

The genuine radial and angular derivatives form a metric-orthogonal basis off
the poles. Its inverse Gram matrix gives the norm of the original differential.
-/

noncomputable section

namespace RicciFlowSharpEstimate.Geometry

open Bundle DifferentialGeometry DifferentialGeometry.Geometry
open DifferentialGeometry.Tensor0SBundle DifferentialGeometry.Geometry.Operator
open scoped Manifold ContDiff

local instance : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 2 + 1) :=
  ⟨finrank_euclideanSpace_fin⟩

/-- The original scalar composed with the actual global polar parametrization is smooth. -/
theorem contDiff_scalar_polar {u : RotationalSphere → ℝ}
    (hu : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ u) :
    ContDiff ℝ ∞ (fun p : ℝ × ℝ => u (polarSpherePoint p.1 p.2)) := by
  have hid : ContMDiff 𝓘(ℝ, ℝ × ℝ) (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) ∞
      (fun p : ℝ × ℝ => (p.1, p.2)) :=
    contDiff_fst.contMDiff.prodMk contDiff_snd.contMDiff
  exact (hu.comp (polarSpherePoint_contMDiff.comp hid)).contDiff

private theorem radialCurve_contMDiff (θ : ℝ) :
    ContMDiff 𝓘(ℝ, ℝ) (𝓡 2) ∞ (fun s => polarSpherePoint s θ) := by
  have hslice : ContMDiff 𝓘(ℝ, ℝ) (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) ∞
      (fun s : ℝ => (s, θ)) := contMDiff_id.prodMk contMDiff_const
  simpa only [Function.comp_def] using! polarSpherePoint_contMDiff.comp hslice

private theorem angularCurve_contMDiff (s : ℝ) :
    ContMDiff 𝓘(ℝ, ℝ) (𝓡 2) ∞ (polarSpherePoint s) := by
  have hslice : ContMDiff 𝓘(ℝ, ℝ) (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) ∞
      (fun θ : ℝ => (s, θ)) := contMDiff_const.prodMk contMDiff_id
  simpa only [Function.comp_def] using! polarSpherePoint_contMDiff.comp hslice

/-- Evaluation of the genuine differential on the actual radial derivative. -/
theorem differential1FormFun_polarRadialVelocity {u : RotationalSphere → ℝ}
    (hu : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ u) (s θ : ℝ) :
    differential1FormFun u (polarSpherePoint s θ)
      (fun _ : Fin 1 => polarRadialVelocity s θ) =
        deriv (fun t => u (polarSpherePoint t θ)) s := by
  rw [differential1FormFun_apply_eq_mvfderiv]
  unfold polarRadialVelocity
  rw [← mvfderiv_comp_apply s (hu.mdifferentiableAt (by simp))
    ((radialCurve_contMDiff θ).mdifferentiableAt (by simp)) 1, mvfderiv_eq_fderiv]
  rfl

/-- Evaluation of the genuine differential on the actual angular derivative. -/
theorem differential1FormFun_polarAngularVelocity {u : RotationalSphere → ℝ}
    (hu : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ u) (s θ : ℝ) :
    differential1FormFun u (polarSpherePoint s θ)
      (fun _ : Fin 1 => polarAngularVelocity s θ) =
        deriv (fun t => u (polarSpherePoint s t)) θ := by
  rw [differential1FormFun_apply_eq_mvfderiv]
  unfold polarAngularVelocity
  rw [← mvfderiv_comp_apply θ (hu.mdifferentiableAt (by simp))
    ((angularCurve_contMDiff s).mdifferentiableAt (by simp)) 1, mvfderiv_eq_fderiv]
  rfl

namespace RotationalProfile.PoleData

/-- The actual covector norm in the genuine polar tangent basis. -/
theorem normSq0S_polar_covector (D : PoleData) (s θ : ℝ) (hs : Real.sin s ≠ 0)
    (α : Tensor0SSpace (I := 𝓡 2) 1 (polarSpherePoint s θ)) :
    normSq0S D.metric (polarSpherePoint s θ) 1 α =
      (D.b (Real.cos s) / D.a (Real.cos s) ^ 2) *
        α (fun _ : Fin 1 => polarRadialVelocity s θ) ^ 2 +
      (1 / (D.b (Real.cos s) * Real.sin s ^ 2)) *
        α (fun _ : Fin 1 => polarAngularVelocity s θ) ^ 2 := by
  let B := polarTangentBasis s θ hs
  let G : Fin 2 → Fin 2 → ℝ :=
    ![![D.b (Real.cos s) / D.a (Real.cos s) ^ 2, 0],
      ![0, 1 / (D.b (Real.cos s) * Real.sin s ^ 2)]]
  have ha := (D.a_pos _ (Real.cos_mem_Icc s)).ne'
  have hb := (D.b_pos _ (Real.cos_mem_Icc s)).ne'
  have hcross : D.metric.inner (polarSpherePoint s θ)
      (polarAngularVelocity s θ) (polarRadialVelocity s θ) = 0 := by
    rw [D.metric.symm, D.metric_inner_polarRadialAngular]
  have hG : MetricInverseInBasis D.metric (polarSpherePoint s θ) B G := by
    intro i j
    fin_cases i <;> fin_cases j <;>
      simp [B, G, Fin.sum_univ_succ, D.metric_inner_polarRadialVelocity,
        D.metric_inner_polarAngularVelocity, D.metric_inner_polarRadialAngular, hcross] <;>
      field_simp [ha, hb, hs] <;> simp
  rw [normSq0S_eq_inner, inner0S_one_eq_cotangent,
    cotangentInner_eq_coord D.metric (polarSpherePoint s θ) B G hG]
  simp only [B, G, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero,
    Matrix.cons_val_succ, zero_mul, zero_add, add_zero, polarTangentBasis_zero,
    cotangentToDual_apply]
  change D.b (Real.cos s) / D.a (Real.cos s) ^ 2 *
      α (fun _ : Fin 1 => polarRadialVelocity s θ) *
      α (fun _ : Fin 1 => polarRadialVelocity s θ) +
    (1 / (D.b (Real.cos s) * Real.sin s ^ 2)) *
      α (fun _ : Fin 1 => polarTangentBasis s θ hs 1) *
      α (fun _ : Fin 1 => polarTangentBasis s θ hs 1) = _
  rw [polarTangentBasis_one]
  ring

/-- Polar expression for the norm of the original smooth scalar differential. -/
theorem normSq0S_differential1FormFun_polar (D : PoleData) {u : RotationalSphere → ℝ}
    (hu : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ u) (s θ : ℝ) (hs : Real.sin s ≠ 0) :
    normSq0S D.metric (polarSpherePoint s θ) 1 (differential1FormFun u (polarSpherePoint s θ)) =
      (D.b (Real.cos s) / D.a (Real.cos s) ^ 2) *
        (deriv (fun t => u (polarSpherePoint t θ)) s) ^ 2 +
      (1 / (D.b (Real.cos s) * Real.sin s ^ 2)) *
        (deriv (fun t => u (polarSpherePoint s t)) θ) ^ 2 := by
  rw [D.normSq0S_polar_covector s θ hs,
    differential1FormFun_polarRadialVelocity hu, differential1FormFun_polarAngularVelocity hu]

end RotationalProfile.PoleData
end RicciFlowSharpEstimate.Geometry
