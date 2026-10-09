/-
Copyright (c) 2026 Ziyang Qin. All rights reserved.
No license is granted by this file.
Authors: Ziyang Qin
-/
import RicciFlowSharpEstimate.Analysis.SmoothIntervalInverse
import RicciFlowSharpEstimate.Analysis.SmoothQuotient
import RicciFlowSharpEstimate.Geometry.AreaActionBridge

/-!
# Fully tied smooth realization of the normalized area action

The actual curvature primitive has a smooth physical inverse. Its reciprocal
curvature and the original scalar probe produce the existing smooth sphere
metric and section. All endpoint, inverse, coefficient and action equations
are retained publicly.

Adapted from Ziyang Qin's historical smooth meridian sphere realization,
retaining the coordinate/probe equations in the public conclusion.
-/

noncomputable section

namespace RicciFlowSharpEstimate.Geometry.AreaProfile

open Set MeasureTheory DifferentialGeometry.Geometry.Curvature
open scoped ContDiff

/-- Smooth positive exact-moment area data are realized by the original sphere
metric and meridional form, with all physical maps, derivatives and action tied
to the prescribed curvature and probe. -/
theorem exists_smooth_geometric_realization (K r : ℝ → ℝ)
    (hK : ContDiff ℝ ∞ K) (hr : ContDiff ℝ ∞ r)
    (hpos : ∀ x ∈ Icc (0 : ℝ) 1, 0 < K x)
    (hzero : (∫ x in (0 : ℝ)..1, K x) = 2)
    (hone : (∫ x in (0 : ℝ)..1, x * K x) = 1) :
    ∃ X : ℝ → ℝ, ∃ D : RotationalProfile.PoleData,
      ∃ R : ℝ → ℝ, ∃ hR : ContDiff ℝ ∞ R,
      ContDiff ℝ ∞ X ∧
      heightCoordinate K 0 = -1 ∧ heightCoordinate K 1 = 1 ∧
      X (-1) = 0 ∧ X 1 = 1 ∧
      MapsTo (heightCoordinate K) (Icc (0 : ℝ) 1) (Icc (-1 : ℝ) 1) ∧
      MapsTo X (Icc (-1 : ℝ) 1) (Icc (0 : ℝ) 1) ∧
      (∀ x ∈ Icc (0 : ℝ) 1,
        X (heightCoordinate K x) = x ∧
        D.a (heightCoordinate K x) = 1 / K x ∧
        R (heightCoordinate K x) = r x ∧
        RotationalProfile.warp D.a (heightCoordinate K x) = warp K x) ∧
      (∀ v ∈ Icc (-1 : ℝ) 1,
        heightCoordinate K (X v) = v ∧ deriv X v * K (X v) = 1) ∧
      R = r ∘ X ∧
      (∀ x ∈ Icc (0 : ℝ) 1,
        deriv D.a (heightCoordinate K x) = -deriv K x / K x ^ 3 ∧
        deriv R (heightCoordinate K x) = deriv r x / K x ∧
        deriv (deriv R) (heightCoordinate K x) =
          deriv (deriv r) x / K x ^ 2 - deriv r x * deriv K x / K x ^ 3) ∧
      (∀ p : RotationalSphere,
        metricScalarAt D.metric p / 2 = K (X (sphereHeight p))) ∧
      oneFormDissipation D.metric (D.meridionalOneForm R hR) =
        2 * Real.pi * meridionalAction K r := by
  have hV := heightCoordinate_contDiff K hK
  have hVpos (x : ℝ) (hx : x ∈ Icc (0 : ℝ) 1) :
      0 < deriv (heightCoordinate K) x := by
    rw [deriv_heightCoordinate K hK.continuous]
    exact hpos x hx
  obtain ⟨X, hX, hXmap, hXV, hVX, hXleft, hXright, hXd⟩ :=
    Analysis.exists_contDiff_inverse_on_Icc (heightCoordinate K) 0 1
      zero_lt_one hV hVpos
  simp only [heightCoordinate_zero, heightCoordinate_one K hzero] at hXmap hVX hXleft hXright hXd
  rw [deriv_heightCoordinate K hK.continuous] at hXd
  have hVmap := heightCoordinate_mapsTo K hK.continuous hpos hzero
  obtain ⟨a, ha, hmul⟩ := Analysis.exists_contDiff_mul_eq_on_Icc
    (-1) 1 (by norm_num) (fun v => K (X v)) (fun _ => 1)
    (hK.comp hX) contDiff_const (fun v hv => (hpos (X v) (hXmap hv)).ne')
  have havalue (v : ℝ) (hv : v ∈ Icc (-1 : ℝ) 1) :
      a v = 1 / K (X v) := by
    apply (eq_div_iff (hpos (X v) (hXmap hv)).ne').mpr
    simpa only [mul_comm] using hmul v hv
  have hapos (v : ℝ) (hv : v ∈ Icc (-1 : ℝ) 1) : 0 < a v := by
    rw [havalue v hv]
    exact one_div_pos.mpr (hpos (X v) (hXmap hv))
  have haat (x : ℝ) (hx : x ∈ Icc (0 : ℝ) 1) :
      a (heightCoordinate K x) = 1 / K x := by
    rw [havalue _ (hVmap hx), hXV x hx]
  have hSub := intervalIntegral.integral_comp_mul_deriv
    (f := heightCoordinate K) (f' := K) (g := fun v => v * a v) (a := 0) (b := 1)
    (fun x _ => heightCoordinate_hasDerivAt K hK.continuous x)
    hK.continuous.continuousOn (continuous_id.mul ha.continuous)
  rw [heightCoordinate_zero, heightCoordinate_one K hzero] at hSub
  have hbalance : RotationalProfile.balance a = 0 := by
    unfold RotationalProfile.balance
    rw [← hSub]
    calc
      (∫ x in (0 : ℝ)..1, ((fun v => v * a v) ∘ heightCoordinate K) x * K x) =
          ∫ x in (0 : ℝ)..1, heightCoordinate K x := by
        apply intervalIntegral.integral_congr
        intro x hx
        rw [uIcc_of_le zero_le_one] at hx
        dsimp only [Function.comp_apply]
        rw [haat x hx]
        field_simp [(hpos x hx).ne']
      _ = 0 := integral_heightCoordinate K hK.continuous hzero hone
  obtain ⟨D, hDa, _⟩ := RotationalProfile.exists_poleData a ha hapos hbalance
  let R : ℝ → ℝ := r ∘ X
  have hR : ContDiff ℝ ∞ R := hr.comp hX
  have hDaat (x : ℝ) (hx : x ∈ Icc (0 : ℝ) 1) :
      D.a (heightCoordinate K x) = 1 / K x := by
    rw [hDa]
    exact haat x hx
  have hprobe (x : ℝ) (hx : x ∈ Icc (0 : ℝ) 1) :
      R (heightCoordinate K x) = r x := by
    change r (X (heightCoordinate K x)) = r x
    rw [hXV x hx]
  refine ⟨X, D, R, hR, hX, heightCoordinate_zero K, heightCoordinate_one K hzero,
    hXleft, hXright, hVmap, hXmap, ?_, ?_, rfl, ?_, ?_, ?_⟩
  · intro x hx
    exact ⟨hXV x hx, hDaat x hx, hprobe x hx,
      profile_warp_heightCoordinate K hK.continuous hpos D hDaat x hx⟩
  · intro v hv
    exact ⟨hVX v hv, hXd v hv⟩
  · intro x hx
    exact ⟨deriv_profile_heightCoordinate K hK hpos D hDaat x hx,
      deriv_probe_heightCoordinate K r hK.continuous hr hpos R hR hprobe x hx,
      deriv_deriv_probe_heightCoordinate K r hK hr hpos R hR hprobe x hx⟩
  · intro p
    have hv := sphereHeight_mem_Icc p
    have hvx := hVX (sphereHeight p) hv
    have hvalue := hDaat (X (sphereHeight p)) (hXmap hv)
    rw [hvx] at hvalue
    calc
      metricScalarAt D.metric p / 2 = 1 / D.a (sphereHeight p) := by
        rw [D.metricScalarAt_metric]
        ring
      _ = K (X (sphereHeight p)) := by
        rw [hvalue, one_div_one_div]
  · exact oneFormDissipation_eq_areaAction_of_profile_probe
      K r hK hr hpos hzero D R hR hDaat hprobe

/-- The actual positive round metric and its nonzero unit probe verify both
the area-action normalization and the original geometric value. -/
theorem round_unit_probe_normalization :
    let D := RotationalProfile.PoleData.constant (1 / 2) (by norm_num)
    D.meridionalOneForm (fun _ => 1) contDiff_const ≠ 0 ∧
      oneFormDissipation D.metric (D.meridionalOneForm (fun _ => 1) contDiff_const) =
        2 * Real.pi * meridionalAction (fun _ => 2) (fun _ => 1) ∧
      oneFormDissipation D.metric (D.meridionalOneForm (fun _ => 1) contDiff_const) =
        8 * Real.pi / 3 := by
  dsimp only
  let D := RotationalProfile.PoleData.constant (1 / 2) (by norm_num)
  have hQ := oneFormDissipation_eq_areaAction_of_profile_probe
    (fun _ => 2) (fun _ => 1) contDiff_const contDiff_const
    (fun _ _ => by norm_num) (by norm_num)
    D (fun _ => 1) contDiff_const (fun _ _ => rfl) (fun _ _ => rfl)
  refine ⟨D.meridionalOneForm_one_ne_zero, hQ, ?_⟩
  rw [hQ, meridionalAction_two_one]
  ring

end RicciFlowSharpEstimate.Geometry.AreaProfile
