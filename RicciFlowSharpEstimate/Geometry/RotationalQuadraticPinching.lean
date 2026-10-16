/-
Copyright (c) 2026 Ziyang Qin. All rights reserved.
No license is granted by this file.
Authors: Ziyang Qin
-/
import RicciFlowSharpEstimate.Geometry.AreaWarpCalibration
import RicciFlowSharpEstimate.Geometry.NormalizedAreaHaar

/-! # All-form safety from the warp-dependent quadratic pinching comparison -/

noncomputable section
namespace RicciFlowSharpEstimate.Geometry
open Set MeasureTheory AreaProfile
open scoped ContDiff

/-- The produced warp-dependent field proves safety for every original smooth
one-form at the displayed cap. This is an independent lower bound, not an
identification of the unrestricted sharp value. -/
theorem quadratic_pinching_mem_rotationalSafeCaps :
    (1 + Real.sqrt (3 / 2) : ℝ) ∈ rotationalSafeCaps := by
  let C : ℝ := 1 + Real.sqrt (3 / 2)
  have hs : (Real.sqrt (3 / 2 : ℝ)) ^ 2 = 3 / 2 := Real.sq_sqrt (by norm_num)
  have hs0 : 0 ≤ Real.sqrt (3 / 2 : ℝ) := Real.sqrt_nonneg _
  have hC : C ^ 2 = 2 * C + 1 / 2 := by dsimp [C]; nlinarith
  have hC1 : 1 ≤ C := by dsimp [C]; linarith
  apply rotationalSafeCaps_of_normalized_area_safety C hC1
  intro K hK _ hzero hone κ Λ hκ hbox hratio r hr _
  have hΛ : Λ ≤ C * κ := (div_le_iff₀ hκ).mp hratio
  have hκΛ : κ ≤ Λ := (hbox 0 (by norm_num)).1.trans (hbox 0 (by norm_num)).2
  have hCκ : κ ≤ C * κ := by nlinarith [mul_nonneg hκ.le (sub_nonneg.mpr hC1)]
  have hCsq : (C * κ) ^ 2 = 2 * κ * (C * κ) + κ ^ 2 / 2 := by
    have h := congrArg (fun y : ℝ => y * κ ^ 2) hC
    nlinarith
  have hpinch : Λ ^ 2 ≤ 2 * κ * Λ + κ ^ 2 / 2 := by
    have h := mul_nonneg (sub_nonneg.mpr hΛ) (show 0 ≤ C * κ + Λ - 2 * κ by linarith)
    nlinarith
  exact meridionalAction_nonneg_of_quadratic_pinching K r hK.continuous
    (hr.of_le (by simp)) hzero hone κ Λ hκ hbox hpinch

/-- The full original rotational threshold is at least the explicit cap
selected by the quadratic flux comparison. Equality is not asserted. -/
theorem quadratic_pinching_le_rotationalThreshold :
    (1 + Real.sqrt (3 / 2) : ℝ) ≤ rotationalThreshold :=
  le_csSup rotationalSafeCaps_bddAbove quadratic_pinching_mem_rotationalSafeCaps

end RicciFlowSharpEstimate.Geometry
