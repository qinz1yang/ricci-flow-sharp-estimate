/-
Copyright (c) 2026 Ziyang Qin. All rights reserved.
No license is granted by this file.
Authors: Ziyang Qin
-/
import RicciFlowSharpEstimate.Geometry.NormalizedAreaAction
import RicciFlowSharpEstimate.Geometry.PhysicalProbeNonzero
import RicciFlowSharpEstimate.Geometry.AreaProbeRayleigh

/-!
# Physical nonzero normalization and the original one-form mass

The normalization applies precisely to nonzero physical components. The original
L² mass retains its exact positive geometry-scale factor.
-/

noncomputable section

namespace RicciFlowSharpEstimate.Geometry.RotationalProfile.PoleData.AreaNormalization

open Set MeasureTheory
open scoped ContDiff Manifold

variable {D : RotationalProfile.PoleData}

/-- The same smooth inverse sends interior area points to interior physical heights. -/
theorem inverse_mem_Ioo (N : AreaNormalization D) (x : ℝ) (hx : x ∈ Ioo (0 : ℝ) 1) :
    N.inverse x ∈ Ioo (-1 : ℝ) 1 := by
  have hm := ReciprocalArea.inverse_strictMonoOn D.a D.a_contDiff.continuous D.a_pos
  have hxc : x ∈ Icc (0 : ℝ) 1 := ⟨hx.1.le, hx.2.le⟩
  rw [N.inverse_eq x hxc]
  constructor
  · have h := hm (by norm_num : (0 : ℝ) ∈ Icc (0 : ℝ) 1) hxc hx.1
    simpa only [ReciprocalArea.inverse_zero D.a D.a_contDiff.continuous D.a_pos] using h
  · have h := hm hxc (by norm_num : (1 : ℝ) ∈ Icc (0 : ℝ) 1) hx.2
    simpa only [ReciprocalArea.inverse_one D.a D.a_contDiff.continuous D.a_pos] using h

/-- Nonvanishing is transported on the physical interiors, not on arbitrary extensions. -/
theorem probe_nonzero_iff (N : AreaNormalization D) (R : ℝ → ℝ) :
    (∃ x ∈ Ioo (0 : ℝ) 1, N.probe R x ≠ 0) ↔
      ∃ v ∈ Ioo (-1 : ℝ) 1, R v ≠ 0 := by
  constructor
  · rintro ⟨x, hx, hne⟩
    exact ⟨N.inverse x, N.inverse_mem_Ioo x hx, hne⟩
  · rintro ⟨v, hv, hne⟩
    have hm := ReciprocalArea.coordinate_strictMonoOn D.a D.a_contDiff.continuous D.a_pos
    have hvc : v ∈ Icc (-1 : ℝ) 1 := ⟨hv.1.le, hv.2.le⟩
    have hl := hm (by norm_num : (-1 : ℝ) ∈ Icc (-1 : ℝ) 1) hvc hv.1
    have hu := hm hvc (by norm_num : (1 : ℝ) ∈ Icc (-1 : ℝ) 1) hv.2
    simp only [ReciprocalArea.coordinate_neg_one] at hl
    simp only [ReciprocalArea.coordinate_one D.a D.a_contDiff.continuous D.a_pos] at hu
    refine ⟨ReciprocalArea.coordinate D.a v, ⟨hl, hu⟩, ?_⟩
    rwa [N.probe_coordinate R v hvc]

/-- The actual original meridional form is nonzero exactly when its transported mass is positive. -/
theorem probeMass_pos_iff_meridional_ne_zero (N : AreaNormalization D)
    (R : ℝ → ℝ) (hR : ContDiff ℝ ∞ R) :
    0 < AreaProfile.probeMass N.curvature (N.probe R) ↔ D.meridionalOneForm R hR ≠ 0 := by
  rw [D.meridionalOneForm_ne_zero_iff R hR, ← N.probe_nonzero_iff R]
  constructor
  · intro hm
    by_contra hn
    have hz : ∀ x ∈ Ioo (0 : ℝ) 1, N.probe R x = 0 := by
      intro x hx
      by_contra hne
      exact hn ⟨x, hx, hne⟩
    have hc : EqOn (N.probe R) (fun _ => 0) (Icc (0 : ℝ) 1) := by
      have h : EqOn (N.probe R) (fun _ => 0) (Ioo (0 : ℝ) 1) := hz
      have h' := h.closure (N.probe_contDiff R hR).continuous continuous_const
      simpa only [closure_Ioo (by norm_num : (0 : ℝ) ≠ 1)] using h'
    have hmass : AreaProfile.probeMass N.curvature (N.probe R) = 0 := by
      unfold AreaProfile.probeMass
      calc
        _ = ∫ _x in (0 : ℝ)..1, (0 : ℝ) := by
          apply intervalIntegral.integral_congr
          intro x hx
          have hx' : x ∈ Icc (0 : ℝ) 1 := by simpa using hx
          dsimp only
          rw [hc hx', zero_pow (by norm_num : (2 : ℕ) ≠ 0), mul_zero]
        _ = 0 := by simp
    rw [hmass] at hm
    exact lt_irrefl _ hm
  · intro hne
    exact AreaProfile.integral_warp_mul_sq_pos N.curvature (N.probe R)
      N.curvature_contDiff.continuous (N.probe_contDiff R hR).continuous
      N.curvature_pos N.integral_curvature N.integral_mul_curvature hne

/-- The same physical criterion handles the azimuthal component without normalizing zero forms. -/
theorem probeMass_pos_iff_azimuthal_ne_zero (N : AreaNormalization D)
    (R : ℝ → ℝ) (hR : ContDiff ℝ ∞ R) :
    0 < AreaProfile.probeMass N.curvature (N.probe R) ↔ D.azimuthalOneForm R hR ≠ 0 := by
  rw [N.probeMass_pos_iff_meridional_ne_zero R hR,
    D.meridionalOneForm_ne_zero_iff R hR, D.azimuthalOneForm_ne_zero_iff R hR]

/-- Every nonzero original meridional form supplies an actual normalized probe and
its original complete action is the positive mass times that normalized action. -/
theorem normalized_probe_action (N : AreaNormalization D) (R : ℝ → ℝ)
    (hR : ContDiff ℝ ∞ R) (hne : D.meridionalOneForm R hR ≠ 0) :
    AreaProfile.probeMass N.curvature
      (AreaProfile.normalizedProbe N.curvature (N.probe R)) = 1 ∧
    oneFormDissipation D.metric (D.meridionalOneForm R hR) =
      2 * Real.pi * AreaProfile.probeMass N.curvature (N.probe R) *
        AreaProfile.meridionalAction N.curvature
          (AreaProfile.normalizedProbe N.curvature (N.probe R)) := by
  have hm := (N.probeMass_pos_iff_meridional_ne_zero R hR).mpr hne
  refine ⟨AreaProfile.probeMass_normalizedProbe _ _ hm, ?_⟩
  rw [N.oneFormDissipation_meridional_eq R hR,
    AreaProfile.meridionalAction_normalizedProbe N.curvature (N.probe R)
      N.curvature_contDiff (N.probe_contDiff R hR) N.integral_curvature
      N.integral_mul_curvature hm, AreaProfile.rayleighQuotient]
  field_simp [hm.ne']

open DifferentialGeometry.Tensor0SBundle DifferentialGeometry.Integral.Measure

private local instance : MeasurableSpace RotationalSphere := borel RotationalSphere
private local instance : BorelSpace RotationalSphere := ⟨rfl⟩

/-- The original one-form's actual squared L² norm has the exact area-scale
factor relative to its transported weighted probe mass. -/
theorem integral_normSq_eq_probeMass (N : AreaNormalization D) (R : ℝ → ℝ)
    (hR : ContDiff ℝ ∞ R) :
    (∫ p : RotationalSphere, normSq0S D.metric p 1 (D.meridionalOneForm R hR p)
      ∂(riemannianVolumeMeasure (I := 𝓡 2) (M := RotationalSphere) D.metric)) =
      2 * Real.pi * (ReciprocalArea.length D.a) ^ 2 *
        AreaProfile.probeMass N.curvature (N.probe R) := by
  have hF : Continuous (fun v => warp D.a v * R v ^ 2) :=
    (warp_contDiff D.a D.a_contDiff).continuous.mul (hR.continuous.pow 2)
  have hG : Continuous (fun x => AreaProfile.warp N.curvature x * N.probe R x ^ 2) :=
    (AreaProfile.warp_continuous N.curvature N.curvature_contDiff.continuous).mul
      ((N.probe_contDiff R hR).continuous.pow 2)
  have hsub := ReciprocalArea.integral_comp_coordinate D.a D.a_contDiff.continuous D.a_pos _ hG
  simp_rw [D.meridionalOneForm_normSq R hR]
  rw [D.integral_height_metric hF.continuousOn]
  have hm : (∫ v in (-1 : ℝ)..1, D.a v * (warp D.a v * R v ^ 2)) =
      (ReciprocalArea.length D.a) ^ 2 * AreaProfile.probeMass N.curvature (N.probe R) := by
    unfold AreaProfile.probeMass
    rw [← hsub, ← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro v hv
    have hv' : v ∈ Icc (-1 : ℝ) 1 := by simpa using hv
    dsimp only
    rw [N.warp_coordinate v hv', N.probe_coordinate R v hv']
    field_simp [(ReciprocalArea.length_pos D.a D.a_contDiff.continuous D.a_pos).ne']
  rw [hm]
  ring

end RicciFlowSharpEstimate.Geometry.RotationalProfile.PoleData.AreaNormalization
