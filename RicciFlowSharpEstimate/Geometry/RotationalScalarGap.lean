/-
Copyright (c) 2026 Ziyang Qin. All rights reserved.
No license is granted by this file.
Authors: Ziyang Qin
-/
import RicciFlowSharpEstimate.Analysis.PolarScalarGap
import RicciFlowSharpEstimate.Geometry.RotationalPolarDifferential
import RicciFlowSharpEstimate.Geometry.RotationalPolarIntegration
import RicciFlowSharpEstimate.Geometry.RotationalScalarAverage

/-!
# A positive scalar gap for the genuine Haar complement

Smoothness on the original sphere supplies the polar endpoint and integrability
conditions. The sharp angular comparison and radial square completion retain
the positive weighted scalar norm for the same metric and differential.
-/

noncomputable section

namespace RicciFlowSharpEstimate.Geometry

open Bundle DifferentialGeometry DifferentialGeometry.Geometry
open DifferentialGeometry.Tensor0SBundle DifferentialGeometry.Tensor.RSTensor
open DifferentialGeometry.Geometry.Operator DifferentialGeometry.Integral.Measure
open Set MeasureTheory Filter
open scoped Manifold ContDiff Topology

local instance : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 2 + 1) :=
  ⟨finrank_euclideanSpace_fin⟩

private local instance : MeasurableSpace RotationalSphere := borel RotationalSphere
private local instance : BorelSpace RotationalSphere := ⟨rfl⟩

private theorem scalar_polar_zero {u : RotationalSphere → ℝ}
    (hmean : rotationalScalarAverage u = 0) (θ : ℝ) :
    u (polarSpherePoint 0 θ) = 0 :=
  rotationalScalarAverage_eq_zero_at_pole hmean _ (by
    rw [sphereHeight_polarSpherePoint]
    norm_num)

private theorem scalar_polar_pi {u : RotationalSphere → ℝ}
    (hmean : rotationalScalarAverage u = 0) (θ : ℝ) :
    u (polarSpherePoint Real.pi θ) = 0 :=
  rotationalScalarAverage_eq_zero_at_pole hmean _ (by
    rw [sphereHeight_polarSpherePoint]
    norm_num)

/-- Uniform sine decay and derivative bounds for the actual polar pullback of
a smooth scalar with zero angular mean. -/
theorem scalar_polar_endpoint_bounds {u : RotationalSphere → ℝ}
    (hu : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ u) (hmean : rotationalScalarAverage u = 0)
    (a b : ℝ) :
    ∃ C > 0, ∀ s ∈ Icc 0 Real.pi, ∀ θ ∈ Icc a b,
      |u (polarSpherePoint s θ)| ≤ C * Real.sin s ∧
      |deriv (fun t => u (polarSpherePoint t θ)) s| ≤ C ∧
      |deriv (fun t => u (polarSpherePoint s t)) θ| ≤ C * Real.sin s :=
  Analysis.exists_pos_polar_endpoint_bounds _ ((contDiff_scalar_polar hu).of_le (by simp))
    (scalar_polar_zero hmean) (scalar_polar_pi hmean) a b

/-- The actual boundary primitive tends to zero at both poles. -/
theorem scalar_polar_boundary_limits {u : RotationalSphere → ℝ}
    (hu : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ u) (hmean : rotationalScalarAverage u = 0)
    (θ : ℝ) :
    Tendsto (fun s => Real.cos s * u (polarSpherePoint s θ) ^ 2) (𝓝 0) (𝓝 0) ∧
      Tendsto (fun s => Real.cos s * u (polarSpherePoint s θ) ^ 2)
        (𝓝 Real.pi) (𝓝 0) :=
  Analysis.tendsto_polar_boundary_at_endpoints _ (contDiff_scalar_polar hu).continuous
    (scalar_polar_zero hmean) (scalar_polar_pi hmean) θ

namespace RotationalProfile.PoleData

/-- Positive scalar energy estimate for the actual mean-zero angular sector.
All coordinate regularity and weighted integrability are derived from smoothness. -/
theorem integral_scalar_energy_ge_of_rotationalScalarAverage_eq_zero (D : PoleData)
    {u : RotationalSphere → ℝ} (hu : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ u)
    (hmean : rotationalScalarAverage u = 0) :
    (∫ x, u x ^ 2 / D.b (sphereHeight x)
      ∂(riemannianVolumeMeasure (I := 𝓡 2) (M := RotationalSphere) D.metric)) ≤
      ∫ x, normSq0S D.metric x 1 (differential1FormFun u x) -
        (1 / D.a (sphereHeight x)) * u x ^ 2
        ∂(riemannianVolumeMeasure (I := 𝓡 2) (M := RotationalSphere) D.metric) := by
  let q : ℝ × ℝ → ℝ := fun p => u (polarSpherePoint p.1 p.2)
  let w : ℝ → ℝ := fun s => D.b (Real.cos s) / D.a (Real.cos s)
  have hq : ContDiff ℝ 2 q := (contDiff_scalar_polar hu).of_le (by simp)
  have hzero : ∀ θ, q (0, θ) = 0 := scalar_polar_zero hmean
  have hpi : ∀ θ, q (Real.pi, θ) = 0 := scalar_polar_pi hmean
  have hperiod (s : ℝ) : q (s, 2 * Real.pi) = q (s, 0) := by
    simpa only [q, zero_add] using congrArg u (polarSpherePoint_periodic s 0)
  have hmean' (s : ℝ) : (∫ θ in (0 : ℝ)..2 * Real.pi, q (s, θ)) = 0 := by
    have h := congrFun hmean (polarSpherePoint s 0)
    simp only [rotationalScalarAverage, angleRotation_polarSpherePoint, add_zero,
      Pi.zero_apply] at h
    exact (mul_eq_zero.mp h).resolve_left (inv_ne_zero (by positivity))
  have hw : Continuous w :=
    (D.b_contDiff.continuous.comp Real.continuous_cos).div
      (D.a_contDiff.continuous.comp Real.continuous_cos)
      (fun s => (D.a_pos _ (Real.cos_mem_Icc s)).ne')
  have hwpos : ∀ s ∈ Icc 0 Real.pi, 0 < w s := fun s _ =>
    div_pos (D.b_pos _ (Real.cos_mem_Icc s)) (D.a_pos _ (Real.cos_mem_Icc s))
  have hgap := Analysis.integral_polar_energy_ge_of_angular_mean_zero
    q w hq hzero hpi hperiod hmean' hw hwpos
  have ha : Continuous (fun x : RotationalSphere => D.a (sphereHeight x)) :=
    D.a_contDiff.continuous.comp sphereHeight_contMDiff.continuous
  have hb : Continuous (fun x : RotationalSphere => D.b (sphereHeight x)) :=
    D.b_contDiff.continuous.comp sphereHeight_contMDiff.continuous
  have hv : Continuous (fun x : RotationalSphere => u x ^ 2 / D.b (sphereHeight x)) :=
    (hu.continuous.pow 2).div hb (fun x => (D.b_pos _ (sphereHeight_mem_Icc x)).ne')
  have he : Continuous (fun x : RotationalSphere =>
      normSq0S D.metric x 1 (differential1FormFun u x) -
        (1 / D.a (sphereHeight x)) * u x ^ 2) :=
    (normSq0S_smooth D.metric (duSec u hu)).continuous.sub
      ((continuous_const.div ha (fun x => (D.a_pos _ (sphereHeight_mem_Icc x)).ne')).mul
        (hu.continuous.pow 2))
  rw [D.integral_polar_metric hv, D.integral_polar_metric he]
  have hleft : (∫ s in (0 : ℝ)..Real.pi, ∫ θ in (0 : ℝ)..2 * Real.pi,
      D.a (Real.cos s) * Real.sin s *
        (u (polarSpherePoint s θ) ^ 2 / D.b (sphereHeight (polarSpherePoint s θ)))) =
      ∫ s in (0 : ℝ)..Real.pi, ∫ θ in (0 : ℝ)..2 * Real.pi,
        Real.sin s ^ 2 * q (s, θ) ^ 2 / (Real.sin s * w s) := by
    apply intervalIntegral.integral_congr_uIoo
    intro s hs
    have hs' : s ∈ Ioo 0 Real.pi := by simpa only [uIoo_of_le Real.pi_pos.le] using hs
    have hsin := (Real.sin_pos_of_pos_of_lt_pi hs'.1 hs'.2).ne'
    apply intervalIntegral.integral_congr
    intro θ _
    simp only [q, w, sphereHeight_polarSpherePoint]
    field_simp [(D.a_pos _ (Real.cos_mem_Icc s)).ne',
      (D.b_pos _ (Real.cos_mem_Icc s)).ne', hsin]
  have hright : (∫ s in (0 : ℝ)..Real.pi, ∫ θ in (0 : ℝ)..2 * Real.pi,
      D.a (Real.cos s) * Real.sin s *
        (normSq0S D.metric (polarSpherePoint s θ) 1
            (differential1FormFun u (polarSpherePoint s θ)) -
          (1 / D.a (sphereHeight (polarSpherePoint s θ))) * u (polarSpherePoint s θ) ^ 2)) =
      ∫ s in (0 : ℝ)..Real.pi, ∫ θ in (0 : ℝ)..2 * Real.pi,
        (Real.sin s * w s) * (deriv (fun t => q (t, θ)) s) ^ 2 +
          (deriv (fun t => q (s, t)) θ) ^ 2 / (Real.sin s * w s) -
          Real.sin s * q (s, θ) ^ 2 := by
    apply intervalIntegral.integral_congr_uIoo
    intro s hs
    have hs' : s ∈ Ioo 0 Real.pi := by simpa only [uIoo_of_le Real.pi_pos.le] using hs
    have hsin := (Real.sin_pos_of_pos_of_lt_pi hs'.1 hs'.2).ne'
    apply intervalIntegral.integral_congr
    intro θ _
    dsimp only
    rw [D.normSq0S_differential1FormFun_polar hu s θ hsin]
    simp only [q, w, sphereHeight_polarSpherePoint]
    field_simp [(D.a_pos _ (Real.cos_mem_Icc s)).ne',
      (D.b_pos _ (Real.cos_mem_Icc s)).ne', hsin]
  rw [hleft, hright]
  exact hgap

end RotationalProfile.PoleData
end RicciFlowSharpEstimate.Geometry
