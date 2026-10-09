/-
Copyright (c) 2026 Ziyang Qin. All rights reserved.
No license is granted by this file.
Authors: Ziyang Qin
-/
import RicciFlowSharpEstimate.Geometry.RotationalPolarCoordinates
import RicciFlowSharpEstimate.Geometry.RotationalScalarAverage
import RicciFlowSharpEstimate.Geometry.RotationalVolume
import DifferentialGeometry.Analysis.Integration.Measure.Riemannian.Naturality
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Polar integration for the rotational sphere metric

The actual metric volume is disintegrated in the genuine polar parametrization.
Rotation invariance and compact Fubini reduce a continuous scalar to its angular
average, then the accepted height formula gives the polar Jacobian.

The averaging and change-of-variables argument adapts Ziyang Qin's historical
round-sphere polar integration argument to continuous inputs and the original
balanced metric.
-/

noncomputable section

namespace RicciFlowSharpEstimate.Geometry

open DifferentialGeometry DifferentialGeometry.Geometry
open DifferentialGeometry.Integral.Measure MeasureTheory Set
open scoped Manifold ContDiff

local instance : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 2 + 1) :=
  ⟨finrank_euclideanSpace_fin⟩

private local instance : MeasurableSpace RotationalSphere := borel RotationalSphere
private local instance : BorelSpace RotationalSphere := ⟨rfl⟩
private local instance : CompactSpace RotationalSphere := Metric.sphere.compactSpace _ _
private local instance : Nonempty RotationalSphere := ⟨polarSpherePoint 0 0⟩

private theorem scalarAverage_continuous {F : RotationalSphere → ℝ} (hF : Continuous F) :
    Continuous (rotationalScalarAverage F) := by
  have hJoint : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 2)) 𝓘(ℝ, ℝ) 0
      (fun p : ℝ × RotationalSphere => F (angleRotation p.1 p.2)) :=
    contMDiff_zero_iff.mpr (hF.comp angleRotation_contMDiff.continuous)
  exact continuous_const.mul
    (Analysis.contMDiff_intervalIntegral 0 0 (2 * Real.pi) hJoint).continuous

private def averagedHeightProfile (F : RotationalSphere → ℝ) (v : ℝ) : ℝ :=
  rotationalScalarAverage F (polarSpherePoint (Real.arccos v) 0)

private theorem averagedHeightProfile_continuous {F : RotationalSphere → ℝ}
    (hF : Continuous F) : Continuous (averagedHeightProfile F) := by
  have hPolar : Continuous (fun p : ℝ × ℝ => polarSpherePoint p.1 p.2) :=
    polarSpherePoint_contMDiff.continuous
  have hPair : Continuous (fun v : ℝ => (Real.arccos v, (0 : ℝ))) :=
    Real.continuous_arccos.prodMk continuous_const
  have hPoint : Continuous (fun v : ℝ => polarSpherePoint (Real.arccos v) 0) := by
    simpa only [Function.comp_def] using! hPolar.comp hPair
  simpa only [averagedHeightProfile, Function.comp_def] using!
    (scalarAverage_continuous hF).comp hPoint

private theorem scalarAverage_eq_heightProfile (F : RotationalSphere → ℝ)
    (x : RotationalSphere) :
    rotationalScalarAverage F x = averagedHeightProfile F (sphereHeight x) := by
  obtain ⟨θ, hθ⟩ := exists_polarSpherePoint_arccos x
  have hrot : angleRotation θ (polarSpherePoint (Real.arccos (sphereHeight x)) 0) = x := by
    simpa only [angleRotation_polarSpherePoint, add_zero] using hθ
  have h := rotationalScalarAverage_angleRotation F θ
    (polarSpherePoint (Real.arccos (sphereHeight x)) 0)
  rw [hrot] at h
  exact h

private theorem two_pi_mul_averagedHeightProfile_cos (F : RotationalSphere → ℝ)
    {s : ℝ} (hs : s ∈ Icc (0 : ℝ) Real.pi) :
    2 * Real.pi * averagedHeightProfile F (Real.cos s) =
      ∫ θ in (0 : ℝ)..2 * Real.pi, F (polarSpherePoint s θ) := by
  simp only [averagedHeightProfile, Real.arccos_cos hs.1 hs.2,
    rotationalScalarAverage, angleRotation_polarSpherePoint, add_zero]
  field_simp [Real.pi_ne_zero]

namespace RotationalProfile.PoleData

private theorem integral_comp_rotation (D : PoleData) (θ : ℝ) (F : RotationalSphere → ℝ) :
    (∫ x, F (angleRotation θ x)
      ∂riemannianVolumeMeasure (I := 𝓡 2) (M := RotationalSphere) D.metric) =
      ∫ x, F x ∂riemannianVolumeMeasure (I := 𝓡 2) (M := RotationalSphere) D.metric := by
  have hmap := Riemannian.VolumeComparison.riemannianVolumeMeasure_map_pullback
    D.metric (angleRotation θ)
  rw [D.pullbackMetric_angleRotation] at hmap
  have hpres : MeasurePreserving (angleRotation θ)
      (riemannianVolumeMeasure (I := 𝓡 2) (M := RotationalSphere) D.metric)
      (riemannianVolumeMeasure (I := 𝓡 2) (M := RotationalSphere) D.metric) :=
    ⟨(angleRotation θ).continuous.measurable, hmap⟩
  exact hpres.integral_comp (angleRotation θ).toHomeomorph.measurableEmbedding F

private theorem integral_average (D : PoleData) {F : RotationalSphere → ℝ}
    (hF : Continuous F) :
    (∫ x, rotationalScalarAverage F x
      ∂riemannianVolumeMeasure (I := 𝓡 2) (M := RotationalSphere) D.metric) =
      ∫ x, F x ∂riemannianVolumeMeasure (I := 𝓡 2) (M := RotationalSphere) D.metric := by
  let μ := riemannianVolumeMeasure (I := 𝓡 2) (M := RotationalSphere) D.metric
  have : IsFiniteMeasure μ := riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace D.metric
  let G : ℝ → RotationalSphere → ℝ := fun θ x => F (angleRotation θ x)
  have hG : Continuous (Function.uncurry G) := hF.comp angleRotation_contMDiff.continuous
  have hIntOn : IntegrableOn (Function.uncurry G)
      (Icc (0 : ℝ) (2 * Real.pi) ×ˢ (univ : Set RotationalSphere)) (volume.prod μ) :=
    hG.continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_univ)
  have hProd : (volume.restrict (uIoc (0 : ℝ) (2 * Real.pi))).prod μ =
      (volume.prod μ).restrict (uIoc (0 : ℝ) (2 * Real.pi) ×ˢ (univ : Set RotationalSphere)) := by
    conv_lhs => rw [← Measure.restrict_univ (μ := μ)]
    rw [Measure.prod_restrict]
  have hInt : Integrable (Function.uncurry G)
      ((volume.restrict (uIoc (0 : ℝ) (2 * Real.pi))).prod μ) := by
    rw [hProd]
    apply hIntOn.mono_set
    rw [uIoc_of_le (by positivity : (0 : ℝ) ≤ 2 * Real.pi)]
    exact prod_mono Ioc_subset_Icc_self Subset.rfl
  have hSwap := (intervalIntegral_integral_swap (μ := μ) (f := G) hInt).symm
  change (∫ x, (2 * Real.pi)⁻¹ * (∫ θ in (0 : ℝ)..2 * Real.pi, G θ x) ∂μ) = _
  rw [integral_const_mul, hSwap]
  simp only [G, μ, D.integral_comp_rotation, intervalIntegral.integral_const,
    sub_zero, smul_eq_mul]
  field_simp [Real.pi_ne_zero]

/-- Polar integration of a continuous scalar with respect to the original metric volume. -/
theorem integral_polar_metric (D : PoleData) {F : RotationalSphere → ℝ} (hF : Continuous F) :
    (∫ x, F x ∂riemannianVolumeMeasure (I := 𝓡 2) (M := RotationalSphere) D.metric) =
      ∫ s in (0 : ℝ)..Real.pi, ∫ θ in (0 : ℝ)..2 * Real.pi,
        D.a (Real.cos s) * Real.sin s * F (polarSpherePoint s θ) := by
  let G : ℝ → ℝ := fun v => D.a v * averagedHeightProfile F v
  have hG : Continuous G := D.a_contDiff.continuous.mul (averagedHeightProfile_continuous hF)
  have hheight : (∫ x, F x
      ∂riemannianVolumeMeasure (I := 𝓡 2) (M := RotationalSphere) D.metric) =
      2 * Real.pi * ∫ v in (-1 : ℝ)..1, G v := by
    rw [← D.integral_average hF]
    simp only [scalarAverage_eq_heightProfile]
    exact D.integral_height_metric (averagedHeightProfile_continuous hF).continuousOn
  have hSubst := intervalIntegral.integral_comp_mul_deriv
    (a := (0 : ℝ)) (b := Real.pi) (f := Real.cos) (f' := fun s => -Real.sin s)
    (g := G) (fun s _ => Real.hasDerivAt_cos s) Real.continuous_sin.neg.continuousOn hG
  rw [Real.cos_zero, Real.cos_pi, intervalIntegral.integral_symm (f := G)] at hSubst
  have hfun : (fun s => (G ∘ Real.cos) s * -Real.sin s) =
      fun s => -(Real.sin s * G (Real.cos s)) := by funext s; dsimp; ring
  rw [hfun, intervalIntegral.integral_neg] at hSubst
  have hSubst' := neg_injective hSubst
  rw [hheight, ← hSubst', ← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro s hs
  have hs' : s ∈ Icc (0 : ℝ) Real.pi := by simpa [uIcc_of_le Real.pi_pos.le] using hs
  change 2 * Real.pi * (Real.sin s * G (Real.cos s)) =
    ∫ θ in (0 : ℝ)..2 * Real.pi, (D.a (Real.cos s) * Real.sin s) * F (polarSpherePoint s θ)
  rw [intervalIntegral.integral_const_mul]
  dsimp only [G]
  rw [show 2 * Real.pi * (Real.sin s * (D.a (Real.cos s) * averagedHeightProfile F (Real.cos s))) =
      D.a (Real.cos s) * Real.sin s * (2 * Real.pi * averagedHeightProfile F (Real.cos s)) by ring,
    two_pi_mul_averagedHeightProfile_cos F hs']

end RotationalProfile.PoleData

end RicciFlowSharpEstimate.Geometry
