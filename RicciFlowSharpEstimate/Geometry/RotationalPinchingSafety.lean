/-
Copyright (c) 2026 Ziyang Qin. All rights reserved.
No license is granted by this file.
Authors: Ziyang Qin
-/
import RicciFlowSharpEstimate.Geometry.AreaPinchingCalibration
import RicciFlowSharpEstimate.Geometry.NormalizedAreaHaar

/-! # Independent all-form safety at curvature ratio two -/

noncomputable section
namespace RicciFlowSharpEstimate.Geometry
open Set MeasureTheory AreaProfile
open scoped ContDiff

/-- The complete-action calibration proves safety for every original smooth
one-form on every represented rotational metric of curvature ratio at most
two. No reference zero mode, stationary branch or minimum is supplied. -/
theorem two_mem_rotationalSafeCaps : (2 : ℝ) ∈ rotationalSafeCaps := by
  apply rotationalSafeCaps_of_normalized_area_safety 2 (by norm_num)
  intro K hK _ hzero hone κ Λ hκ hbox hratio r hr hmass
  have hΛ : Λ ≤ 2 * κ := (div_le_iff₀ hκ).mp hratio
  have hbound := meridionalAction_ge_pinching_mass K r hK.continuous
    (hr.of_le (by simp)) hzero hone κ Λ hκ hbox hΛ
  rw [hmass, mul_one] at hbound
  exact (mul_nonneg hκ.le (sub_nonneg.mpr hΛ)).trans hbound

/-- The independent original all-form comparison gives an explicit lower
bound for the unrestricted rotational threshold. Equality is not asserted. -/
theorem two_le_rotationalThreshold : (2 : ℝ) ≤ rotationalThreshold :=
  le_csSup rotationalSafeCaps_bddAbove two_mem_rotationalSafeCaps

end RicciFlowSharpEstimate.Geometry
