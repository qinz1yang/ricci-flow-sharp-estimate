/-
Copyright (c) 2026 Ziyang Qin. All rights reserved.
No license is granted by this file.
Authors: Ziyang Qin
-/
import RicciFlowSharpEstimate.Geometry.NormalizedAreaMass
import RicciFlowSharpEstimate.Geometry.RepresentedHaarGeometry
import RicciFlowSharpEstimate.Geometry.RotationalThreshold
import RicciFlowSharpEstimate.Geometry.AreaGeometricRealization

/-!
# Exhaustive normalized-area reduction for represented rotational metrics

A single geometry normalization precedes all original form/probe quantifiers.
The same original Haar action and remainder, scaled curvature boxes and exact
ratios give scalar safety transfer in both directions, without identifying a cap.
-/

noncomputable section

namespace RicciFlowSharpEstimate.Geometry.RotationalProfile.PoleData.AreaNormalization

open Set MeasureTheory
open scoped ContDiff

variable {D : RotationalProfile.PoleData}

open DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open scoped Manifold

local instance : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 2 + 1) :=
  ⟨finrank_euclideanSpace_fin⟩

/-- The actual curvature coefficient is tied to the same smooth inverse and original profile. -/
theorem curvature_inverse (N : AreaNormalization D) (x : ℝ) (hx : x ∈ Icc (0 : ℝ) 1) :
    N.curvature x = ReciprocalArea.length D.a / D.a (N.inverse x) := by
  have h := N.curvature_coordinate (N.inverse x) (N.inverse_mem x hx)
  rwa [N.coordinate_inverse x hx] at h

/-- The scale is the original profile's actual total length, with no free coefficient. -/
theorem profile_mul_curvature (N : AreaNormalization D) (x : ℝ) (hx : x ∈ Icc (0 : ℝ) 1) :
    D.a (N.inverse x) * N.curvature x = ReciprocalArea.length D.a := by
  rw [N.curvature_inverse x hx]
  field_simp [(D.a_pos _ (N.inverse_mem x hx)).ne']

/-- Every actual original curvature box scales by the same positive length;
its pinching ratio is unchanged. -/
theorem curvature_bounds_scaled (N : AreaNormalization D) (κ Λ : ℝ) (hκ : 0 < κ)
    (hbox : ∀ p : RotationalSphere, κ ≤ metricScalarAt D.metric p / 2 ∧
      metricScalarAt D.metric p / 2 ≤ Λ) :
    0 < ReciprocalArea.length D.a * κ ∧
    (∀ x ∈ Icc (0 : ℝ) 1,
      N.curvature x ∈ Icc (ReciprocalArea.length D.a * κ) (ReciprocalArea.length D.a * Λ)) ∧
    (ReciprocalArea.length D.a * Λ) / (ReciprocalArea.length D.a * κ) = Λ / κ := by
  have hL := ReciprocalArea.length_pos D.a D.a_contDiff.continuous D.a_pos
  refine ⟨mul_pos hL hκ, ?_, ?_⟩
  · intro x hx
    have hv := N.inverse_mem x hx
    have hval : metricScalarAt D.metric (polarSpherePoint (Real.arccos (N.inverse x)) 0) / 2 =
        1 / D.a (N.inverse x) := by
      rw [D.metricScalarAt_metric, sphereHeight_polarSpherePoint, Real.cos_arccos hv.1 hv.2]
      ring
    have hb := hbox (polarSpherePoint (Real.arccos (N.inverse x)) 0)
    rw [hval] at hb
    rw [N.curvature_inverse x hx, div_eq_mul_one_div]
    exact ⟨mul_le_mul_of_nonneg_left hb.1 hL.le, mul_le_mul_of_nonneg_left hb.2 hL.le⟩
  · field_simp [hL.ne', hκ.ne']

open DifferentialGeometry.Tensor.RicciIdentity DifferentialGeometry.PDE.RicciFlow

/-- Physical nonzero normalization is unchanged by the actual representing pullback. -/
theorem probeMass_pos_iff_pullback_meridional_ne_zero (N : AreaNormalization D)
    (F : RotationalSphere ≃ₘ⟮𝓡 2, 𝓡 2⟯ RotationalSphere)
    (R : ℝ → ℝ) (hR : ContDiff ℝ ∞ R) :
    0 < AreaProfile.probeMass N.curvature (N.probe R) ↔
      diffeomorphTensorPullback F (D.meridionalOneForm R hR) ≠ 0 := by
  exact (N.probeMass_pos_iff_meridional_ne_zero R hR).trans
    (not_congr (diffeomorphTensorPullback_eq_zero_iff F (D.meridionalOneForm R hR))).symm

/-- The azimuthal represented component has the same physical positive-mass criterion. -/
theorem probeMass_pos_iff_pullback_azimuthal_ne_zero (N : AreaNormalization D)
    (F : RotationalSphere ≃ₘ⟮𝓡 2, 𝓡 2⟯ RotationalSphere)
    (R : ℝ → ℝ) (hR : ContDiff ℝ ∞ R) :
    0 < AreaProfile.probeMass N.curvature (N.probe R) ↔
      diffeomorphTensorPullback F (D.azimuthalOneForm R hR) ≠ 0 := by
  exact (N.probeMass_pos_iff_azimuthal_ne_zero R hR).trans
    (not_congr (diffeomorphTensorPullback_eq_zero_iff F (D.azimuthalOneForm R hR))).symm

/-- The same original represented metric and pulled-back meridional form retain
all action factors under geometry normalization. -/
theorem oneFormDissipation_pullback_meridional_eq (N : AreaNormalization D)
    (F : RotationalSphere ≃ₘ⟮𝓡 2, 𝓡 2⟯ RotationalSphere)
    (R : ℝ → ℝ) (hR : ContDiff ℝ ∞ R) :
    oneFormDissipation (Diffeomorph.pullbackMetric D.metric F)
      (diffeomorphTensorPullback F (D.meridionalOneForm R hR)) =
      2 * Real.pi * AreaProfile.meridionalAction N.curvature (N.probe R) := by
  rw [oneFormDissipation_diffeomorphTensorPullback, N.oneFormDissipation_meridional_eq R hR]

/-- Safety on unit-mass probes for this normalized geometry controls every original
meridional form, with the zero component handled separately. -/
theorem meridionalAction_nonneg_of_normalized_safety (N : AreaNormalization D)
    (hsafe : ∀ r : ℝ → ℝ, ContDiff ℝ ∞ r →
      AreaProfile.probeMass N.curvature r = 1 → 0 ≤ AreaProfile.meridionalAction N.curvature r)
    (R : ℝ → ℝ) (hR : ContDiff ℝ ∞ R) : 0 ≤ D.meridionalAction R := by
  by_cases hz : D.meridionalOneForm R hR = 0
  · have h := D.oneFormDissipation_meridional R hR
    rw [hz, oneFormDissipation_zero] at h
    have hpi : 0 < 2 * Real.pi := mul_pos (by norm_num) Real.pi_pos
    nlinarith
  · have hm := (N.probeMass_pos_iff_meridional_ne_zero R hR).mpr hz
    have hnorm : ContDiff ℝ ∞ (AreaProfile.normalizedProbe N.curvature (N.probe R)) :=
      contDiff_const.mul (N.probe_contDiff R hR)
    have hp := hsafe (AreaProfile.normalizedProbe N.curvature (N.probe R)) hnorm
      (AreaProfile.probeMass_normalizedProbe _ _ hm)
    rw [AreaProfile.meridionalAction_normalizedProbe _ _ N.curvature_contDiff
      (N.probe_contDiff R hR) N.integral_curvature N.integral_mul_curvature hm,
      AreaProfile.rayleighQuotient] at hp
    have h := (le_div_iff₀ hm).mp hp
    rw [zero_mul, N.meridionalAction_eq R hR] at h
    exact h

/-- One normalization of the represented geometry supplies the exact original
Haar/area action split for every original form. -/
theorem exists_conjugated_haar_area_dissipation (N : AreaNormalization D)
    (F : RotationalSphere ≃ₘ⟮𝓡 2, 𝓡 2⟯ RotationalSphere)
    (h : OneFormSection (I := 𝓡 2) (M := RotationalSphere)) :
    ∃ R S : ℝ → ℝ, ∃ hR : ContDiff ℝ ∞ R, ∃ hS : ContDiff ℝ ∞ S,
      conjugatedRotationalAverage F h =
        diffeomorphTensorPullback F (D.meridionalOneForm R hR) +
          diffeomorphTensorPullback F (D.azimuthalOneForm S hS) ∧
      oneFormDissipation (Diffeomorph.pullbackMetric D.metric F) h =
        2 * Real.pi * (AreaProfile.meridionalAction N.curvature (N.probe R) +
          AreaProfile.meridionalAction N.curvature (N.probe S)) +
          oneFormDissipation (Diffeomorph.pullbackMetric D.metric F)
            (h - conjugatedRotationalAverage F h) ∧
      0 ≤ oneFormDissipation (Diffeomorph.pullbackMetric D.metric F)
        (h - conjugatedRotationalAverage F h) ∧
      (oneFormDissipation (Diffeomorph.pullbackMetric D.metric F)
        (h - conjugatedRotationalAverage F h) = 0 ↔ h - conjugatedRotationalAverage F h = 0) := by
  obtain ⟨R, S, hR, hS, heq, hQ⟩ := D.exists_conjugated_haar_zonal_dissipation F h
  refine ⟨R, S, hR, hS, heq, ?_, D.oneFormDissipation_conjugated_remainder_nonneg F h,
    D.oneFormDissipation_conjugated_remainder_eq_zero_iff F h⟩
  rwa [N.meridionalAction_eq R hR, N.meridionalAction_eq S hS]

/-- Unit-mass scalar safety for the normalized geometry transfers to all original
smooth one-forms on this same represented metric. -/
theorem oneFormDissipation_nonneg_of_normalized_safety (N : AreaNormalization D)
    (F : RotationalSphere ≃ₘ⟮𝓡 2, 𝓡 2⟯ RotationalSphere)
    (hsafe : ∀ r : ℝ → ℝ, ContDiff ℝ ∞ r →
      AreaProfile.probeMass N.curvature r = 1 → 0 ≤ AreaProfile.meridionalAction N.curvature r)
    (h : OneFormSection (I := 𝓡 2) (M := RotationalSphere)) :
    0 ≤ oneFormDissipation (Diffeomorph.pullbackMetric D.metric F) h := by
  obtain ⟨R, S, hR, hS, _heq, hQ⟩ := D.exists_conjugated_haar_zonal_dissipation F h
  rw [hQ]
  exact add_nonneg (mul_nonneg (mul_nonneg (by norm_num) Real.pi_pos.le)
    (add_nonneg (N.meridionalAction_nonneg_of_normalized_safety hsafe R hR)
      (N.meridionalAction_nonneg_of_normalized_safety hsafe S hS)))
    (D.oneFormDissipation_conjugated_remainder_nonneg F h)

end RicciFlowSharpEstimate.Geometry.RotationalProfile.PoleData.AreaNormalization

namespace RicciFlowSharpEstimate.Geometry

open Set MeasureTheory DifferentialGeometry DifferentialGeometry.Tensor.RicciIdentity
open DifferentialGeometry.PDE.RicciFlow DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff

local instance : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 2 + 1) :=
  ⟨finrank_euclideanSpace_fin⟩

namespace RotationalProfile.PoleData

/-- An original profile alone supplies the normalized complete action for every
original smooth meridional form. No compatibility equations are requested. -/
theorem oneFormDissipation_eq_normalizedAreaAction (D : PoleData) (R : ℝ → ℝ)
    (hR : ContDiff ℝ ∞ R) :
    oneFormDissipation D.metric (D.meridionalOneForm R hR) =
      2 * Real.pi * AreaProfile.meridionalAction D.areaNormalization.curvature
        (D.areaNormalization.probe R) :=
  D.areaNormalization.oneFormDissipation_meridional_eq R hR

end RotationalProfile.PoleData

namespace IsRepresentedRotationalMetric

/-- One original representation and one normalization are chosen before all forms
and curvature boxes. The original Haar remainder and exact full action are retained. -/
theorem exists_normalized_area_representation
    {g : SmoothRiemannianMetric (𝓡 2) RotationalSphere}
    (hg : IsRepresentedRotationalMetric g) :
    ∃ D : RotationalProfile.PoleData,
      ∃ F : RotationalSphere ≃ₘ⟮𝓡 2, 𝓡 2⟯ RotationalSphere,
      ∃ N : D.AreaNormalization,
      g = Diffeomorph.pullbackMetric D.metric F ∧
      (∀ h : OneFormSection (I := 𝓡 2) (M := RotationalSphere),
        ∃ R S : ℝ → ℝ, ∃ hR : ContDiff ℝ ∞ R, ∃ hS : ContDiff ℝ ∞ S,
        conjugatedRotationalAverage F h =
          diffeomorphTensorPullback F (D.meridionalOneForm R hR) +
            diffeomorphTensorPullback F (D.azimuthalOneForm S hS) ∧
        oneFormDissipation g h =
          2 * Real.pi * (AreaProfile.meridionalAction N.curvature (N.probe R) +
            AreaProfile.meridionalAction N.curvature (N.probe S)) +
            oneFormDissipation g (h - conjugatedRotationalAverage F h) ∧
        0 ≤ oneFormDissipation g (h - conjugatedRotationalAverage F h) ∧
        (oneFormDissipation g (h - conjugatedRotationalAverage F h) = 0 ↔
          h - conjugatedRotationalAverage F h = 0)) ∧
      (∀ κ Λ : ℝ, 0 < κ →
        (∀ p : RotationalSphere, κ ≤ metricScalarAt g p / 2 ∧
          metricScalarAt g p / 2 ≤ Λ) →
        0 < ReciprocalArea.length D.a * κ ∧
        (∀ x ∈ Icc (0 : ℝ) 1,
          N.curvature x ∈ Icc (ReciprocalArea.length D.a * κ) (ReciprocalArea.length D.a * Λ)) ∧
        (ReciprocalArea.length D.a * Λ) / (ReciprocalArea.length D.a * κ) = Λ / κ) := by
  obtain ⟨D, F, hg', _, _⟩ := hg.exists_haar_representation
  refine ⟨D, F, D.areaNormalization, hg', ?_, ?_⟩
  · intro h
    rw [hg']
    exact D.areaNormalization.exists_conjugated_haar_area_dissipation F h
  · intro κ Λ hκ hbox
    have hb : ∀ p : RotationalSphere, κ ≤ metricScalarAt D.metric p / 2 ∧
        metricScalarAt D.metric p / 2 ≤ Λ := by
      apply (D.curvature_bounds_pullback_iff F κ Λ).mp
      simpa only [hg'] using hbox
    exact D.areaNormalization.curvature_bounds_scaled κ Λ hκ hb

end IsRepresentedRotationalMetric

/-- A universal normalized scalar safety theorem transfers to the original
all-form safe-cap predicate. This is a reduction criterion, not a new safe value. -/
theorem rotationalSafeCaps_of_normalized_area_safety (C : ℝ) (hC : 1 ≤ C)
    (hsafe : ∀ K : ℝ → ℝ, ContDiff ℝ ∞ K →
      (∀ x ∈ Icc (0 : ℝ) 1, 0 < K x) →
      (∫ x in (0 : ℝ)..1, K x) = 2 →
      (∫ x in (0 : ℝ)..1, x * K x) = 1 →
      ∀ κ Λ : ℝ, 0 < κ → (∀ x ∈ Icc (0 : ℝ) 1, K x ∈ Icc κ Λ) → Λ / κ ≤ C →
      ∀ r : ℝ → ℝ, ContDiff ℝ ∞ r → AreaProfile.probeMass K r = 1 →
        0 ≤ AreaProfile.meridionalAction K r) : C ∈ rotationalSafeCaps := by
  refine ⟨hC, ?_⟩
  intro g hg
  obtain ⟨D, F, N, rfl, _, hbounds⟩ := hg.exists_normalized_area_representation
  intro κ Λ hκ hbox hratio h
  obtain ⟨hlo, hb, hrat⟩ := hbounds κ Λ hκ hbox
  apply N.oneFormDissipation_nonneg_of_normalized_safety F ?_ h
  intro r hr hm
  exact hsafe N.curvature N.curvature_contDiff N.curvature_pos
    N.integral_curvature N.integral_mul_curvature
    (ReciprocalArea.length D.a * κ) (ReciprocalArea.length D.a * Λ) hlo hb
    (by rw [hrat]; exact hratio) r hr hm

/-- Original safe caps control the complete normalized area action of every
smooth probe, by the existing fully tied geometric realizer. -/
theorem areaAction_nonneg_of_rotationalSafeCap (C : ℝ) (hC : C ∈ rotationalSafeCaps)
    (K r : ℝ → ℝ) (hK : ContDiff ℝ ∞ K) (hr : ContDiff ℝ ∞ r)
    (hpos : ∀ x ∈ Icc (0 : ℝ) 1, 0 < K x)
    (hzero : (∫ x in (0 : ℝ)..1, K x) = 2)
    (hone : (∫ x in (0 : ℝ)..1, x * K x) = 1)
    (κ Λ : ℝ) (hκ : 0 < κ) (hbox : ∀ x ∈ Icc (0 : ℝ) 1, K x ∈ Icc κ Λ)
    (hratio : Λ / κ ≤ C) : 0 ≤ AreaProfile.meridionalAction K r := by
  obtain ⟨X, D, R, hR, _hX, _hV0, _hV1, _hX0, _hX1, _hVmap, hXmap,
    _hforward, _hbackward, _hR, _hjets, hcurv, haction⟩ :=
    AreaProfile.exists_smooth_geometric_realization K r hK hr hpos hzero hone
  have hgeom : ∀ p : RotationalSphere, κ ≤ metricScalarAt D.metric p / 2 ∧
      metricScalarAt D.metric p / 2 ≤ Λ := by
    intro p
    rw [hcurv p]
    exact hbox _ (hXmap (sphereHeight_mem_Icc p))
  have h := hC.2 D.metric D.isRepresentedRotationalMetric κ Λ hκ hgeom hratio
    (D.meridionalOneForm R hR)
  rw [haction] at h
  exact (mul_nonneg_iff_of_pos_left (mul_pos (by norm_num : (0 : ℝ) < 2) Real.pi_pos)).mp h

end RicciFlowSharpEstimate.Geometry
