/-
Copyright (c) 2026 Ziyang Qin. All rights reserved.
No license is granted by this file.
Authors: Ziyang Qin
-/
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# The normalized lower-obstacle weight

The full lower-obstacle calibration density, divided by its mass, gives a
continuous nonnegative weight. Its first two moments determine the constant
in the cap-dependent stability estimate.
-/

open Set

namespace RicciFlowSharpEstimate.Variational

/-- The normalized polynomial weight on the entire lower obstacle. -/
noncomputable def lowerObstacleWeight (a v : ℝ) : ℝ :=
  3 * max (a ^ 2 - v ^ 2) 0 / (2 * a ^ 3)

theorem continuous_lowerObstacleWeight (a : ℝ) : Continuous (lowerObstacleWeight a) := by
  unfold lowerObstacleWeight
  fun_prop

theorem lowerObstacleWeight_nonneg (a v : ℝ) (ha : 0 < a) :
    0 ≤ lowerObstacleWeight a v := by
  unfold lowerObstacleWeight
  positivity

theorem lowerObstacleWeight_eq_low (a v : ℝ) (hv : v ∈ Icc 0 a) :
    lowerObstacleWeight a v = 3 * (a ^ 2 - v ^ 2) / (2 * a ^ 3) := by
  have hs : 0 ≤ a ^ 2 - v ^ 2 := by nlinarith [hv.1, hv.2]
  simp only [lowerObstacleWeight, max_eq_left hs]

theorem lowerObstacleWeight_eq_zero (a v : ℝ) (ha : 0 ≤ a) (hv : a ≤ v) :
    lowerObstacleWeight a v = 0 := by
  have hs : a ^ 2 - v ^ 2 ≤ 0 := by nlinarith
  simp [lowerObstacleWeight, max_eq_right hs]

private theorem integral_obstacle_polynomial (a : ℝ) :
    (∫ v in 0..a, 3 * (a ^ 2 - v ^ 2) / (2 * a ^ 3)) =
      (3 * a ^ 2 * a - a ^ 3) / (2 * a ^ 3) := by
  calc
    (∫ v in 0..a, 3 * (a ^ 2 - v ^ 2) / (2 * a ^ 3)) =
        ((3 * a ^ 2 * a - a ^ 3) / (2 * a ^ 3)) -
          ((3 * a ^ 2 * 0 - (0 : ℝ) ^ 3) / (2 * a ^ 3)) := by
      apply intervalIntegral.integral_eq_sub_of_hasDerivAt
        (f := fun v => (3 * a ^ 2 * v - v ^ 3) / (2 * a ^ 3))
      · intro v _
        convert! (((hasDerivAt_id v).const_mul (3 * a ^ 2)).sub
          ((hasDerivAt_id v).pow 3)).div_const (2 * a ^ 3) using 1
        norm_num
        ring
      · exact (by fun_prop : Continuous (fun v : ℝ =>
          3 * (a ^ 2 - v ^ 2) / (2 * a ^ 3))).intervalIntegrable 0 a
    _ = _ := by simp

private theorem integral_obstacle_polynomial_sq (a : ℝ) :
    (∫ v in 0..a, (3 * (a ^ 2 - v ^ 2) / (2 * a ^ 3)) ^ 2) =
      9 / (4 * a ^ 6) * (a ^ 4 * a - (2 / 3 : ℝ) * a ^ 2 * a ^ 3 + a ^ 5 / 5) := by
  calc
    (∫ v in 0..a, (3 * (a ^ 2 - v ^ 2) / (2 * a ^ 3)) ^ 2) =
        (9 / (4 * a ^ 6) *
          (a ^ 4 * a - (2 / 3 : ℝ) * a ^ 2 * a ^ 3 + a ^ 5 / 5)) -
        (9 / (4 * a ^ 6) *
          (a ^ 4 * 0 - (2 / 3 : ℝ) * a ^ 2 * 0 ^ 3 + 0 ^ 5 / 5)) := by
      apply intervalIntegral.integral_eq_sub_of_hasDerivAt
        (f := fun v => 9 / (4 * a ^ 6) *
          (a ^ 4 * v - (2 / 3 : ℝ) * a ^ 2 * v ^ 3 + v ^ 5 / 5))
      · intro v _
        convert! ((((hasDerivAt_id v).const_mul (a ^ 4)).sub
          (((hasDerivAt_id v).pow 3).const_mul ((2 / 3 : ℝ) * a ^ 2))).add
          (((hasDerivAt_id v).pow 5).div_const 5)).const_mul (9 / (4 * a ^ 6))
          using 1
        norm_num
        ring
      · exact (by fun_prop : Continuous (fun v : ℝ =>
          (3 * (a ^ 2 - v ^ 2) / (2 * a ^ 3)) ^ 2)).intervalIntegrable 0 a
    _ = _ := by simp

/-- The complete lower-obstacle weight has mass one. -/
theorem integral_lowerObstacleWeight (a : ℝ) (ha : 0 < a) (ha1 : a ≤ 1) :
    (∫ v in (0 : ℝ)..1, lowerObstacleWeight a v) = 1 := by
  have hc := continuous_lowerObstacleWeight a
  have hlow : (∫ v in 0..a, lowerObstacleWeight a v) = 1 := by
    calc
      (∫ v in 0..a, lowerObstacleWeight a v) =
          ∫ v in 0..a, 3 * (a ^ 2 - v ^ 2) / (2 * a ^ 3) := by
        apply intervalIntegral.integral_congr
        intro v hv
        rw [uIcc_of_le ha.le] at hv
        exact lowerObstacleWeight_eq_low a v hv
      _ = 1 := by
        rw [integral_obstacle_polynomial]
        field_simp [ha.ne']
        ring
  have hhigh : (∫ v in a..1, lowerObstacleWeight a v) = 0 := by
    calc
      (∫ v in a..1, lowerObstacleWeight a v) = ∫ v in a..1, (0 : ℝ) := by
        apply intervalIntegral.integral_congr
        intro v hv
        rw [uIcc_of_le ha1] at hv
        exact lowerObstacleWeight_eq_zero a v ha.le hv.1
      _ = 0 := by simp
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (hc.intervalIntegrable 0 a) (hc.intervalIntegrable a 1), hlow, hhigh, add_zero]

/-- The exact squared mass of the normalized full obstacle weight. -/
theorem integral_lowerObstacleWeight_sq (a : ℝ) (ha : 0 < a) (ha1 : a ≤ 1) :
    (∫ v in (0 : ℝ)..1, lowerObstacleWeight a v ^ 2) = 6 / (5 * a) := by
  have hc : Continuous (fun v => lowerObstacleWeight a v ^ 2) :=
    (continuous_lowerObstacleWeight a).pow 2
  have hlow : (∫ v in 0..a, lowerObstacleWeight a v ^ 2) = 6 / (5 * a) := by
    calc
      (∫ v in 0..a, lowerObstacleWeight a v ^ 2) =
          ∫ v in 0..a, (3 * (a ^ 2 - v ^ 2) / (2 * a ^ 3)) ^ 2 := by
        apply intervalIntegral.integral_congr
        intro v hv
        rw [uIcc_of_le ha.le] at hv
        dsimp only
        rw [lowerObstacleWeight_eq_low a v hv]
      _ = 6 / (5 * a) := by
        rw [integral_obstacle_polynomial_sq]
        field_simp [ha.ne']
        ring
  have hhigh : (∫ v in a..1, lowerObstacleWeight a v ^ 2) = 0 := by
    calc
      (∫ v in a..1, lowerObstacleWeight a v ^ 2) = ∫ v in a..1, (0 : ℝ) := by
        apply intervalIntegral.integral_congr
        intro v hv
        rw [uIcc_of_le ha1] at hv
        dsimp only
        rw [lowerObstacleWeight_eq_zero a v ha.le hv.1, zero_pow (by decide)]
      _ = 0 := by simp
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (hc.intervalIntegrable 0 a) (hc.intervalIntegrable a 1), hlow, hhigh, add_zero]

end RicciFlowSharpEstimate.Variational
