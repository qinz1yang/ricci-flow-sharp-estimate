/-
Copyright (c) 2026 Ziyang Qin. All rights reserved.
No license is granted by this file.
Authors: Ziyang Qin
-/
import RicciFlowSharpEstimate.Geometry.ConstantZonalAction
import RicciFlowSharpEstimate.Geometry.RotationalConformalKilling
import RicciFlowSharpEstimate.Geometry.RotationalRemainder
import RicciFlowSharpEstimate.Geometry.RotationalCurvatureBounds
import RicciFlowSharpEstimate.Variational.CriticalCap

/-!
# The explicit conformal Killing safe cap for produced metrics

The literal hemisphere identities, differentiable-profile strictness, invariant
CK classification and original Haar remainder prove full smooth equality. The
zero-average case is included through the same remainder theorem.
-/

noncomputable section

namespace RicciFlowSharpEstimate.Geometry

open Bundle DifferentialGeometry DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Tensor.RicciIdentity DifferentialGeometry.Geometry.Curvature
open Set Variational
open scoped Manifold ContDiff

local instance : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 2 + 1) :=
  ⟨finrank_euclideanSpace_fin⟩
local instance : CompactSpace RotationalSphere := Metric.sphere.compactSpace _ _

namespace RotationalProfile.PoleData

/-- Every smooth produced profile in a safe box has a strictly positive
actual constant-zonal coefficient, including the critical cap. -/
theorem constant_zonal_coefficient_pos (D : PoleData) (m M : ℝ) (hm : 0 < m)
    (hb : ∀ v ∈ Icc (-1 : ℝ) 1, m ≤ D.a v ∧ D.a v ≤ M)
    (hcap : M / m ≤ criticalCap) :
    0 < 2 * (pairFunctional (fun v => Real.log (M / D.a v)) +
      pairFunctional (fun v => Real.log (M / D.a (-v)))) - 4 / 3 := by
  obtain ⟨hM, hC⟩ := D.reciprocalCap_parameters m M hm hb
  obtain ⟨hkn, hbn⟩ := D.northLogProfile_admissible m M hm hb
  obtain ⟨hks, hbs⟩ := D.southLogProfile_admissible m M hm hb
  have hn := pairFunctional_gt_one_third_of_differentiableOn (M / m) hC hcap _ hkn
    (D.northLogProfile_differentiableOn M hM) hbn
  have hs := pairFunctional_gt_one_third_of_differentiableOn (M / m) hC hcap _ hks
    (D.southLogProfile_differentiableOn M hM) hbs
  linarith

private theorem constant_zonal_safe (D : PoleData) (m M : ℝ) (hm : 0 < m)
    (hb : ∀ v ∈ Icc (-1 : ℝ) 1, m ≤ D.a v ∧ D.a v ≤ M)
    (hcap : M / m ≤ criticalCap) (c d : ℝ) :
    let h := D.meridionalOneForm (fun _ => c) contDiff_const +
      D.azimuthalOneForm (fun _ => d) contDiff_const
    0 ≤ oneFormDissipation D.metric h ∧ (oneFormDissipation D.metric h = 0 → h = 0) := by
  have hM := (D.reciprocalCap_parameters m M hm hb).1
  have hc := D.constant_zonal_coefficient_pos m M hm hb hcap
  have hp : 0 < 2 * Real.pi *
      (2 * (pairFunctional (fun v => Real.log (M / D.a v)) +
        pairFunctional (fun v => Real.log (M / D.a (-v)))) - 4 / 3) :=
    mul_pos (mul_pos (by norm_num) Real.pi_pos) hc
  have hvalue := D.oneFormDissipation_constant_zonal_eq_pair_sum M hM c d
  dsimp only
  constructor
  · rw [hvalue]
    exact mul_nonneg hp.le (add_nonneg (sq_nonneg c) (sq_nonneg d))
  · intro hz
    rw [hvalue] at hz
    have hcd : c ^ 2 + d ^ 2 = 0 := (mul_eq_zero.mp hz).resolve_left hp.ne'
    have hc0 : c = 0 := by nlinarith [sq_nonneg d]
    have hd0 : d = 0 := by nlinarith [sq_nonneg c]
    subst c d
    ext x slots
    simp [meridionalOneForm, azimuthalOneForm, tensor0SField_smulByFun_apply]

private theorem conformalKilling_safe_profile (D : PoleData) (m M : ℝ) (hm : 0 < m)
    (hb : ∀ v ∈ Icc (-1 : ℝ) 1, m ≤ D.a v ∧ D.a v ≤ M)
    (hcap : M / m ≤ criticalCap)
    (h : OneFormSection (I := 𝓡 2) (M := RotationalSphere))
    (hCK : IsConformalKillingOneForm D.metric h) :
    0 ≤ oneFormDissipation D.metric h ∧ (oneFormDissipation D.metric h = 0 ↔ h = 0) := by
  obtain ⟨c, d, hrepr⟩ :=
    D.exists_constant_zonal_decomposition_rotationalAverage_of_isConformalKillingOneForm h hCK
  have havg := constant_zonal_safe D m M hm hb hcap c d
  rw [← hrepr] at havg
  have hrem := D.oneFormDissipation_remainder_nonneg h
  have hsplit := D.oneFormDissipation_haar_split h
  refine ⟨by linarith [havg.1], ?_⟩
  constructor
  · intro hz
    have hpzero : oneFormDissipation D.metric (rotationalAverage h) = 0 := by
      linarith [havg.1]
    have hrzero : oneFormDissipation D.metric (h - rotationalAverage h) = 0 := by
      linarith [havg.1]
    have hP := havg.2 hpzero
    have hR := (D.oneFormDissipation_remainder_eq_zero_iff h).mp hrzero
    exact (sub_eq_zero.mp hR).trans hP
  · rintro rfl
    exact oneFormDissipation_zero D.metric

/-- The original complete action is nonnegative for every smooth CK form
whose actual produced profile lies in the explicit safe box. -/
theorem oneFormDissipation_nonneg_of_conformalKilling_profile_bounds (D : PoleData)
    (m M : ℝ) (hm : 0 < m)
    (hb : ∀ v ∈ Icc (-1 : ℝ) 1, m ≤ D.a v ∧ D.a v ≤ M)
    (hcap : M / m ≤ criticalCap)
    (h : OneFormSection (I := 𝓡 2) (M := RotationalSphere))
    (hCK : IsConformalKillingOneForm D.metric h) :
    0 ≤ oneFormDissipation D.metric h :=
  (conformalKilling_safe_profile D m M hm hb hcap h hCK).1

/-- Full smooth CK equality is exactly the zero form, even when its Haar average is zero. -/
theorem oneFormDissipation_eq_zero_iff_of_conformalKilling_profile_bounds (D : PoleData)
    (m M : ℝ) (hm : 0 < m)
    (hb : ∀ v ∈ Icc (-1 : ℝ) 1, m ≤ D.a v ∧ D.a v ≤ M)
    (hcap : M / m ≤ criticalCap)
    (h : OneFormSection (I := 𝓡 2) (M := RotationalSphere))
    (hCK : IsConformalKillingOneForm D.metric h) :
    oneFormDissipation D.metric h = 0 ↔ h = 0 :=
  (conformalKilling_safe_profile D m M hm hb hcap h hCK).2

private theorem curvature_safe (D : PoleData) (κ Λ : ℝ) (hκ : 0 < κ)
    (hb : ∀ x : RotationalSphere, κ ≤ metricScalarAt D.metric x / 2 ∧
      metricScalarAt D.metric x / 2 ≤ Λ)
    (hcap : Λ / κ ≤ criticalCap)
    (h : OneFormSection (I := 𝓡 2) (M := RotationalSphere))
    (hCK : IsConformalKillingOneForm D.metric h) :
    0 ≤ oneFormDissipation D.metric h ∧ (oneFormDissipation D.metric h = 0 ↔ h = 0) := by
  have hbound := hb (polarSpherePoint 0 0)
  have hΛ : 0 < Λ := hκ.trans_le (hbound.1.trans hbound.2)
  have hprofile := (D.curvature_bounds_iff_profile_bounds κ Λ hκ hΛ).mp hb
  have hratio : (1 / κ) / (1 / Λ) = Λ / κ := by field_simp
  exact conformalKilling_safe_profile D (1 / Λ) (1 / κ) (one_div_pos.mpr hΛ)
    hprofile (by simpa only [hratio] using hcap) h hCK

/-- The fixed scalar probe `r=1` has positive actual action in every smooth safe
profile; this is not an infimum obtained by scaling arbitrary forms. -/
theorem oneFormDissipation_meridional_one_pos_of_profile_bounds (D : PoleData)
    (m M : ℝ) (hm : 0 < m)
    (hb : ∀ v ∈ Icc (-1 : ℝ) 1, m ≤ D.a v ∧ D.a v ≤ M)
    (hcap : M / m ≤ criticalCap) :
    0 < oneFormDissipation D.metric (D.meridionalOneForm (fun _ => 1) contDiff_const) := by
  have hCK := D.isConformalKillingOneForm_meridional_const 1
  have hn := D.oneFormDissipation_nonneg_of_conformalKilling_profile_bounds
    m M hm hb hcap _ hCK
  have heq := D.oneFormDissipation_eq_zero_iff_of_conformalKilling_profile_bounds
    m M hm hb hcap _ hCK
  refine (lt_iff_le_and_ne).2 ⟨hn, ?_⟩
  intro hz
  exact D.meridionalOneForm_one_ne_zero (heq.mp hz.symm)

/-- The geometric safe-cap theorem uses the same metric's actual Gauss curvature bounds. -/
theorem oneFormDissipation_nonneg_of_conformalKilling_curvature_bounds (D : PoleData)
    (κ Λ : ℝ) (hκ : 0 < κ)
    (hb : ∀ x : RotationalSphere, κ ≤ metricScalarAt D.metric x / 2 ∧
      metricScalarAt D.metric x / 2 ≤ Λ)
    (hcap : Λ / κ ≤ criticalCap)
    (h : OneFormSection (I := 𝓡 2) (M := RotationalSphere))
    (hCK : IsConformalKillingOneForm D.metric h) :
    0 ≤ oneFormDissipation D.metric h :=
  (curvature_safe D κ Λ hκ hb hcap h hCK).1

/-- At every safe curvature cap, the original smooth CK action vanishes exactly at zero. -/
theorem oneFormDissipation_eq_zero_iff_of_conformalKilling_curvature_bounds (D : PoleData)
    (κ Λ : ℝ) (hκ : 0 < κ)
    (hb : ∀ x : RotationalSphere, κ ≤ metricScalarAt D.metric x / 2 ∧
      metricScalarAt D.metric x / 2 ≤ Λ)
    (hcap : Λ / κ ≤ criticalCap)
    (h : OneFormSection (I := 𝓡 2) (M := RotationalSphere))
    (hCK : IsConformalKillingOneForm D.metric h) :
    oneFormDissipation D.metric h = 0 ↔ h = 0 :=
  (curvature_safe D κ Λ hκ hb hcap h hCK).2

end RotationalProfile.PoleData
end RicciFlowSharpEstimate.Geometry
