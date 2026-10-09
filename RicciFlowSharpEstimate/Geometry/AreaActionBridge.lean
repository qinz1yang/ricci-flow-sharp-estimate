/-
Copyright (c) 2026 Ziyang Qin. All rights reserved.
No license is granted by this file.
Authors: Ziyang Qin
-/
import RicciFlowSharpEstimate.Geometry.AreaAction
import RicciFlowSharpEstimate.Geometry.RotationalMeridionalReduction
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

/-!
# The complete area action and the original sphere dissipation

Physical coefficient and probe equations determine the actual derivatives,
including at both closed-interval endpoints. Their chain rules identify every
term of the complete density and its exact curvature Jacobian. Adapted from
Ziyang Qin's historical smooth meridian realization and action bridge.
-/

noncomputable section

namespace RicciFlowSharpEstimate.Geometry.AreaProfile

open MeasureTheory Set
open scoped ContDiff

/-- The physical reciprocal-curvature equation ties the actual two warping integrals. -/
theorem profile_warp_heightCoordinate (K : ℝ → ℝ) (hK : Continuous K)
    (hpos : ∀ x ∈ Icc (0 : ℝ) 1, 0 < K x) (D : RotationalProfile.PoleData)
    (ha : ∀ x ∈ Icc (0 : ℝ) 1, D.a (heightCoordinate K x) = 1 / K x)
    (x : ℝ) (hx : x ∈ Icc (0 : ℝ) 1) :
    RotationalProfile.warp D.a (heightCoordinate K x) = warp K x := by
  have hLeft : ∀ y ∈ Icc (0 : ℝ) 1,
      HasDerivAt (fun z => RotationalProfile.warp D.a (heightCoordinate K z))
        (-2 * heightCoordinate K y) y := by
    intro y hy
    have h := (RotationalProfile.warp_hasDerivAt D.a D.a_contDiff.continuous
      (heightCoordinate K y)).comp y (heightCoordinate_hasDerivAt K hK y)
    rw [ha y hy] at h
    convert h using 1
    · rfl
    · field_simp [(hpos y hy).ne']
  have hRight (y : ℝ) : HasDerivAt (warp K) (-2 * heightCoordinate K y) y := by
    rw [← warpSlope_eq_neg_two_height]
    exact warp_hasDerivAt K hK y
  apply eq_of_has_deriv_right_eq (a := (0 : ℝ)) (b := 1)
    (f' := fun y => -2 * heightCoordinate K y) ?_ ?_ ?_ ?_ ?_ x hx
  · intro y hy
    exact (hLeft y ⟨hy.1, hy.2.le⟩).hasDerivWithinAt
  · intro y _
    exact (hRight y).hasDerivWithinAt
  · exact ((RotationalProfile.warp_contDiff D.a D.a_contDiff).continuous.comp
      (heightCoordinate_continuous K hK)).continuousOn
  · exact (warp_continuous K hK).continuousOn
  · rw [heightCoordinate_zero, RotationalProfile.warp_neg_one_eq_zero_of_balance
      D.a D.balance_eq, warp_zero]

/-- Differentiating the physical coefficient equation gives the actual profile derivative,
including at both physical endpoints. -/
theorem deriv_profile_heightCoordinate (K : ℝ → ℝ) (hK : ContDiff ℝ ∞ K)
    (hpos : ∀ x ∈ Icc (0 : ℝ) 1, 0 < K x) (D : RotationalProfile.PoleData)
    (ha : ∀ x ∈ Icc (0 : ℝ) 1, D.a (heightCoordinate K x) = 1 / K x)
    (x : ℝ) (hx : x ∈ Icc (0 : ℝ) 1) :
    deriv D.a (heightCoordinate K x) = -deriv K x / K x ^ 3 := by
  have hne := (hpos x hx).ne'
  have hLeft := ((D.a_contDiff.differentiable (by simp)
    (heightCoordinate K x)).hasDerivAt).comp x
      (heightCoordinate_hasDerivAt K hK.continuous x)
  have hRight : HasDerivAt (fun y => 1 / K y) (-deriv K x / K x ^ 2) x := by
    convert (hasDerivAt_const x (1 : ℝ)).div
      ((hK.differentiable (by simp) x).hasDerivAt) hne using 1
    ring
  have hEq := (uniqueDiffOn_Icc_zero_one x hx).eq_deriv _
    (hLeft.hasDerivWithinAt.congr_of_mem (fun y hy => (ha y hy).symm) hx)
    hRight.hasDerivWithinAt
  field_simp [hne] at hEq ⊢
  nlinarith [hEq]

/-- The actual first probe derivative obeys the reciprocal-curvature chain rule
on the full closed physical interval. -/
theorem deriv_probe_heightCoordinate (K r : ℝ → ℝ) (hK : Continuous K)
    (hr : ContDiff ℝ ∞ r) (hpos : ∀ x ∈ Icc (0 : ℝ) 1, 0 < K x)
    (R : ℝ → ℝ) (hR : ContDiff ℝ ∞ R)
    (hprobe : ∀ x ∈ Icc (0 : ℝ) 1, R (heightCoordinate K x) = r x)
    (x : ℝ) (hx : x ∈ Icc (0 : ℝ) 1) :
    deriv R (heightCoordinate K x) = deriv r x / K x := by
  have hLeft := ((hR.differentiable (by simp)
    (heightCoordinate K x)).hasDerivAt).comp x (heightCoordinate_hasDerivAt K hK x)
  have hRight := (hr.differentiable (by simp) x).hasDerivAt
  have hEq := (uniqueDiffOn_Icc_zero_one x hx).eq_deriv _
    (hLeft.hasDerivWithinAt.congr_of_mem (fun y hy => (hprobe y hy).symm) hx)
    hRight.hasDerivWithinAt
  exact (eq_div_iff (hpos x hx).ne').mpr hEq

/-- Differentiating the derived first chain rule supplies the genuine second probe jet,
including at both endpoints. -/
theorem deriv_deriv_probe_heightCoordinate (K r : ℝ → ℝ) (hK : ContDiff ℝ ∞ K)
    (hr : ContDiff ℝ ∞ r) (hpos : ∀ x ∈ Icc (0 : ℝ) 1, 0 < K x)
    (R : ℝ → ℝ) (hR : ContDiff ℝ ∞ R)
    (hprobe : ∀ x ∈ Icc (0 : ℝ) 1, R (heightCoordinate K x) = r x)
    (x : ℝ) (hx : x ∈ Icc (0 : ℝ) 1) :
    deriv (deriv R) (heightCoordinate K x) =
      deriv (deriv r) x / K x ^ 2 - deriv r x * deriv K x / K x ^ 3 := by
  have hne := (hpos x hx).ne'
  have hR1 := (contDiff_infty_iff_deriv.mp hR).2
  have hr1 := (contDiff_infty_iff_deriv.mp hr).2
  have hLeft := ((hR1.differentiable (by simp)
    (heightCoordinate K x)).hasDerivAt).comp x
      (heightCoordinate_hasDerivAt K hK.continuous x)
  have hRight := ((hr1.differentiable (by simp) x).hasDerivAt).div
    ((hK.differentiable (by simp) x).hasDerivAt) hne
  have hEq := (uniqueDiffOn_Icc_zero_one x hx).eq_deriv _
    (hLeft.hasDerivWithinAt.congr_of_mem (fun y hy =>
      (deriv_probe_heightCoordinate K r hK.continuous hr hpos R hR hprobe y hy).symm) hx)
    hRight.hasDerivWithinAt
  field_simp [hne] at hEq ⊢
  nlinarith [hEq]

/-- The geometric meridional weight is the area warp times curvature. -/
theorem meridionalWeight_heightCoordinate (K : ℝ → ℝ) (hK : Continuous K)
    (hpos : ∀ x ∈ Icc (0 : ℝ) 1, 0 < K x) (D : RotationalProfile.PoleData)
    (ha : ∀ x ∈ Icc (0 : ℝ) 1, D.a (heightCoordinate K x) = 1 / K x)
    (x : ℝ) (hx : x ∈ Icc (0 : ℝ) 1) :
    D.meridionalWeight (heightCoordinate K x) = warp K x * K x := by
  rw [RotationalProfile.PoleData.meridionalWeight,
    profile_warp_heightCoordinate K hK hpos D ha x hx, ha x hx]
  field_simp

/-- The derivative of the actual geometric weight carries the curvature derivative. -/
theorem deriv_meridionalWeight_heightCoordinate (K : ℝ → ℝ) (hK : ContDiff ℝ ∞ K)
    (hpos : ∀ x ∈ Icc (0 : ℝ) 1, 0 < K x)
    (hzero : (∫ x in (0 : ℝ)..1, K x) = 2) (D : RotationalProfile.PoleData)
    (ha : ∀ x ∈ Icc (0 : ℝ) 1, D.a (heightCoordinate K x) = 1 / K x)
    (x : ℝ) (hx : x ∈ Icc (0 : ℝ) 1) :
    deriv D.meridionalWeight (heightCoordinate K x) =
      warpSlope K x + warp K x * deriv K x / K x := by
  rw [(D.meridionalWeight_hasDerivAt (heightCoordinate K x)
    (heightCoordinate_mapsTo K hK.continuous hpos hzero hx)).deriv,
    meridionalWeight_heightCoordinate K hK.continuous hpos D ha x hx,
    deriv_profile_heightCoordinate K hK hpos D ha x hx, ha x hx,
    warpSlope_eq_neg_two_height]
  field_simp [(hpos x hx).ne']
  ring

/-- The curvature derivative cancels in the actual second-order geometric operator. -/
theorem meridionalOperator_heightCoordinate (K r : ℝ → ℝ) (hK : ContDiff ℝ ∞ K)
    (hr : ContDiff ℝ ∞ r) (hpos : ∀ x ∈ Icc (0 : ℝ) 1, 0 < K x)
    (hzero : (∫ x in (0 : ℝ)..1, K x) = 2) (D : RotationalProfile.PoleData)
    (R : ℝ → ℝ) (hR : ContDiff ℝ ∞ R)
    (ha : ∀ x ∈ Icc (0 : ℝ) 1, D.a (heightCoordinate K x) = 1 / K x)
    (hprobe : ∀ x ∈ Icc (0 : ℝ) 1, R (heightCoordinate K x) = r x)
    (x : ℝ) (hx : x ∈ Icc (0 : ℝ) 1) :
    D.meridionalOperator R (heightCoordinate K x) =
      (warp K x * deriv (deriv r) x + 2 * warpSlope K x * deriv r x - K x * r x) /
        K x := by
  rw [RotationalProfile.PoleData.meridionalOperator,
    meridionalWeight_heightCoordinate K hK.continuous hpos D ha x hx,
    deriv_meridionalWeight_heightCoordinate K hK hpos hzero D ha x hx,
    deriv_probe_heightCoordinate K r hK.continuous hr hpos R hR hprobe x hx,
    deriv_deriv_probe_heightCoordinate K r hK hr hpos R hR hprobe x hx,
    hprobe x hx, warpSlope_eq_neg_two_height]
  field_simp [(hpos x hx).ne']
  ring

/-- Multiplication by the actual height Jacobian recovers every term of the area density. -/
theorem meridionalDensity_heightCoordinate_mul_curvature (K r : ℝ → ℝ)
    (hK : ContDiff ℝ ∞ K) (hr : ContDiff ℝ ∞ r)
    (hpos : ∀ x ∈ Icc (0 : ℝ) 1, 0 < K x)
    (hzero : (∫ x in (0 : ℝ)..1, K x) = 2) (D : RotationalProfile.PoleData)
    (R : ℝ → ℝ) (hR : ContDiff ℝ ∞ R)
    (ha : ∀ x ∈ Icc (0 : ℝ) 1, D.a (heightCoordinate K x) = 1 / K x)
    (hprobe : ∀ x ∈ Icc (0 : ℝ) 1, R (heightCoordinate K x) = r x)
    (x : ℝ) (hx : x ∈ Icc (0 : ℝ) 1) :
    D.meridionalDensity R (heightCoordinate K x) * K x =
      meridionalActionDensity (warp K x) (warpSlope K x) (K x) (r x)
        (deriv r x) (deriv (deriv r) x) := by
  rw [RotationalProfile.PoleData.meridionalDensity,
    meridionalWeight_heightCoordinate K hK.continuous hpos D ha x hx,
    meridionalOperator_heightCoordinate K r hK hr hpos hzero D R hR ha hprobe x hx,
    hprobe x hx,
    deriv_probe_heightCoordinate K r hK.continuous hr hpos R hR hprobe x hx]
  unfold meridionalActionDensity
  rw [warpSlope_eq_neg_two_height]
  field_simp [(hpos x hx).ne']
  ring

/-- Physical profile and probe equations identify the original sphere dissipation
with the complete area action, with its canonical angular factor. -/
theorem oneFormDissipation_eq_areaAction_of_profile_probe (K r : ℝ → ℝ)
    (hK : ContDiff ℝ ∞ K) (hr : ContDiff ℝ ∞ r)
    (hpos : ∀ x ∈ Icc (0 : ℝ) 1, 0 < K x)
    (hzero : (∫ x in (0 : ℝ)..1, K x) = 2) (D : RotationalProfile.PoleData)
    (R : ℝ → ℝ) (hR : ContDiff ℝ ∞ R)
    (ha : ∀ x ∈ Icc (0 : ℝ) 1, D.a (heightCoordinate K x) = 1 / K x)
    (hprobe : ∀ x ∈ Icc (0 : ℝ) 1, R (heightCoordinate K x) = r x) :
    oneFormDissipation D.metric (D.meridionalOneForm R hR) =
      2 * Real.pi * meridionalAction K r := by
  have hImage : heightCoordinate K '' uIcc (0 : ℝ) 1 ⊆ Icc (-1 : ℝ) 1 := by
    rintro _ ⟨x, hx, rfl⟩
    apply heightCoordinate_mapsTo K hK.continuous hpos hzero
    simpa only [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using hx
  have hSubst := intervalIntegral.integral_comp_mul_deriv'
    (f := heightCoordinate K) (f' := K) (g := D.meridionalDensity R)
    (a := 0) (b := 1) (fun x _ => heightCoordinate_hasDerivAt K hK.continuous x)
    hK.continuous.continuousOn ((D.meridionalDensity_continuousOn R hR).mono hImage)
  rw [heightCoordinate_zero, heightCoordinate_one K hzero] at hSubst
  rw [D.oneFormDissipation_meridional R hR]
  congr 1
  rw [RotationalProfile.PoleData.meridionalAction, meridionalAction, ← hSubst]
  apply intervalIntegral.integral_congr
  intro x hx
  apply meridionalDensity_heightCoordinate_mul_curvature K r hK hr hpos hzero D R hR ha hprobe
  simpa only [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using hx

end RicciFlowSharpEstimate.Geometry.AreaProfile
