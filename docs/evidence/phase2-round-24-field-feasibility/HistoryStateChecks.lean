/-
Copyright (c) 2026 Ziyang Qin. All rights reserved.
No license is granted by this file.
Authors: Ziyang Qin
-/
import RicciFlowSharpEstimate.Geometry.AreaWarpBounds
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# An explicit normalized nonconstant curvature with positive history defect

Every state below is obtained from the original warp and slope primitives
of the displayed curvature. The example is an original curvature-state
realization, with no independently supplied slope or warp values.
-/

noncomputable section

namespace RicciFlowSharpEstimate.Geometry.AreaProfile

open MeasureTheory Set
open scoped ContDiff

private def historyWeight : ℝ := 15 / 256

private def historyIntegral : ℝ :=
  1 / 630 - historyWeight / 70 + historyWeight ^ 2 / 30

private def historyCurvature (x : ℝ) : ℝ :=
  5 / 2 - (x * (1 - x)) ^ 2 * (x * (1 - x) - historyWeight) ^ 2 /
    (2 * historyIntegral)

private theorem history_integral_value : historyIntegral = 35701 / 41287680 := by
  norm_num [historyIntegral, historyWeight]

private theorem history_smooth : ContDiff ℝ ∞ historyCurvature := by
  have h : ContDiff ℝ ∞ (fun x : ℝ =>
      (x * (1 - x)) ^ 2 * (x * (1 - x) - historyWeight) ^ 2) := by fun_prop
  have h0 : ContDiff ℝ ∞ (fun _ : ℝ => (5 / 2 : ℝ)) := contDiff_const
  exact h0.sub (h.div_const (2 * historyIntegral))

private def historyCoeff : ℕ → ℝ
  | 0 => 5 / 2
  | 2 => -70875 / 35701
  | 3 => 2560950 / 35701
  | 4 => -27972315 / 35701
  | 5 => 89832960 / 35701
  | 6 => -126282240 / 35701
  | 7 => 82575360 / 35701
  | 8 => -20643840 / 35701
  | _ => 0

private theorem history_polynomial (x : ℝ) :
    historyCurvature x = ∑ n ∈ Finset.range 9, historyCoeff n * x ^ n := by
  norm_num [historyCurvature, historyIntegral, historyWeight, historyCoeff,
    Finset.sum_range_succ]
  ring

private theorem history_monomial_integral (m : ℕ) (y : ℝ) :
    (∫ x in (0 : ℝ)..y, x ^ m * historyCurvature x) =
      ∑ n ∈ Finset.range 9,
        historyCoeff n * (y ^ (n + m + 1) / ((n + m : ℕ) + 1 : ℝ)) := by
  calc
    (∫ x in (0 : ℝ)..y, x ^ m * historyCurvature x) =
        ∫ x in (0 : ℝ)..y, ∑ n ∈ Finset.range 9, historyCoeff n * x ^ (n + m) := by
      apply intervalIntegral.integral_congr
      intro x _
      dsimp only
      rw [history_polynomial, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro n _
      rw [pow_add]
      ring
    _ = ∑ n ∈ Finset.range 9, ∫ x in (0 : ℝ)..y, historyCoeff n * x ^ (n + m) :=
      intervalIntegral.integral_finsetSum fun n _ =>
        (continuous_const.mul (continuous_id.pow (n + m))).intervalIntegrable 0 y
    _ = _ := by
      apply Finset.sum_congr rfl
      intro n _
      rw [intervalIntegral.integral_const_mul, integral_pow]
      simp

private theorem history_zeroth_primitive (y : ℝ) :
    (∫ x in (0 : ℝ)..y, historyCurvature x) =
      ∑ n ∈ Finset.range 9, historyCoeff n * (y ^ (n + 1) / (n + 1 : ℝ)) := by
  simpa only [Nat.add_zero, pow_zero, one_mul] using history_monomial_integral 0 y

private theorem history_first_primitive (y : ℝ) :
    (∫ x in (0 : ℝ)..y, x * historyCurvature x) =
      ∑ n ∈ Finset.range 9,
        historyCoeff n * (y ^ (n + 1 + 1) / ((n + 1 : ℕ) + 1 : ℝ)) := by
  simpa only [pow_one] using history_monomial_integral 1 y

private theorem history_zeroth_moment : (∫ x in (0 : ℝ)..1, historyCurvature x) = 2 := by
  rw [history_zeroth_primitive]
  norm_num [historyCoeff, Finset.sum_range_succ]

private theorem history_first_moment : (∫ x in (0 : ℝ)..1, x * historyCurvature x) = 1 := by
  rw [history_first_primitive]
  norm_num [historyCoeff, Finset.sum_range_succ]

private theorem history_box (x : ℝ) (hx : x ∈ Icc (0 : ℝ) 1) :
    (25 / 24 : ℝ) ≤ historyCurvature x ∧ historyCurvature x ≤ 5 / 2 := by
  let s := x * (1 - x)
  have hs0 : 0 ≤ s := mul_nonneg hx.1 (sub_nonneg.mpr hx.2)
  have hs1 : s ≤ (1 / 4 : ℝ) := by
    dsimp only [s]
    nlinarith [sq_nonneg (x - 1 / 2)]
  have habs : |s - historyWeight| ≤ (49 / 256 : ℝ) := by
    change |s - (15 / 256 : ℝ)| ≤ (49 / 256 : ℝ)
    apply abs_le.mpr
    constructor <;> linarith
  have hprod0 : 0 ≤ s * |s - historyWeight| := mul_nonneg hs0 (abs_nonneg _)
  have hprod : s * |s - historyWeight| ≤ (49 / 1024 : ℝ) := by
    calc
      _ ≤ (1 / 4 : ℝ) * (49 / 256 : ℝ) :=
        mul_le_mul hs1 habs (abs_nonneg _) (by norm_num)
      _ = _ := by norm_num
  have hsquare : s ^ 2 * (s - historyWeight) ^ 2 ≤ (49 / 1024 : ℝ) ^ 2 := by
    calc
      _ = (s * |s - historyWeight|) ^ 2 := by simp only [mul_pow, sq_abs]
      _ ≤ _ := by
        simpa only [pow_two] using mul_self_le_mul_self hprod0 hprod
  have hI : 0 < 2 * historyIntegral := by rw [history_integral_value]; norm_num
  have hquot0 : 0 ≤ s ^ 2 * (s - historyWeight) ^ 2 / (2 * historyIntegral) :=
    div_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _)) hI.le
  have hquot : s ^ 2 * (s - historyWeight) ^ 2 / (2 * historyIntegral) ≤
      (49 / 1024 : ℝ) ^ 2 / (2 * historyIntegral) :=
    div_le_div_of_nonneg_right hsquare hI.le
  have hnum : (25 / 24 : ℝ) ≤ 5 / 2 - (49 / 1024 : ℝ) ^ 2 / (2 * historyIntegral) := by
    rw [history_integral_value]
    norm_num
  change (25 / 24 : ℝ) ≤ 5 / 2 - s ^ 2 * (s - historyWeight) ^ 2 / (2 * historyIntegral) ∧
    5 / 2 - s ^ 2 * (s - historyWeight) ^ 2 / (2 * historyIntegral) ≤ 5 / 2
  constructor <;> linarith

private theorem history_upper_contact : historyCurvature (1 / 16) = 5 / 2 := by
  norm_num [historyCurvature, historyWeight]

private theorem history_nonconstant : historyCurvature 0 ≠ historyCurvature (1 / 2) := by
  norm_num [historyCurvature, historyIntegral, historyWeight]

private theorem history_slope_value :
    warpSlope historyCurvature (1 / 16) = 3948311353 / 2339700736 := by
  rw [warpSlope, history_zeroth_primitive]
  norm_num [historyCoeff, Finset.sum_range_succ]

private theorem history_warp_value :
    warp historyCurvature (1 / 16) = 138043425435 / 1197926776832 := by
  rw [warp, Analysis.SecondPrimitive.integral_kernel_eq historyCurvature
    history_smooth.continuous 0 (1 / 16), history_zeroth_primitive, history_first_primitive]
  norm_num [historyCoeff, Finset.sum_range_succ]

private theorem history_defect_value :
    (warpSlope historyCurvature (1 / 16)) ^ 2 + 10 * warp historyCurvature (1 / 16) - 4 =
      573468335240625 / 5474199534038941696 := by
  rw [history_slope_value, history_warp_value]
  norm_num

/-- Every displayed state is produced by the same original explicit curvature. -/
example :
    ContDiff ℝ ∞ historyCurvature ∧
    (∫ x in (0 : ℝ)..1, historyCurvature x) = 2 ∧
    (∫ x in (0 : ℝ)..1, x * historyCurvature x) = 1 ∧
    (∀ x ∈ Icc (0 : ℝ) 1, (25 / 24 : ℝ) ≤ historyCurvature x ∧ historyCurvature x ≤ 5 / 2) ∧
    historyCurvature 0 ≠ historyCurvature (1 / 2) ∧
    historyCurvature (1 / 16) = 5 / 2 ∧
    0 < warpSlope historyCurvature (1 / 16) ∧
    4 < (warpSlope historyCurvature (1 / 16)) ^ 2 + 10 * warp historyCurvature (1 / 16) := by
  refine ⟨history_smooth, history_zeroth_moment, history_first_moment, history_box,
    history_nonconstant, history_upper_contact, ?_, ?_⟩
  · rw [history_slope_value]
    norm_num
  · have h := history_defect_value
    norm_num at h ⊢
    linarith

end RicciFlowSharpEstimate.Geometry.AreaProfile
