/-
Copyright (c) 2026 Ziyang Qin. All rights reserved.
No license is granted by this file.
Authors: Ziyang Qin
-/
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Derivative energy estimates on real intervals

The square integral of the actual derivative controls endpoint increments
and all two-point increments of a real `C¹` function. Combining this with the
square integral of the function gives a pointwise bound without boundary
conditions.
-/

noncomputable section

namespace RicciFlowSharpEstimate.Analysis

open MeasureTheory Set

/-- The squared endpoint increment is bounded by the interval length times
the square integral of the derivative. No endpoint conditions are imposed. -/
theorem sq_sub_le_length_mul_integral_deriv_sq
    (r : ℝ → ℝ) (hr : ContDiff ℝ 1 r) (a b : ℝ) (hab : a ≤ b) :
    (r b - r a) ^ 2 ≤ (b - a) * (∫ t in a..b, deriv r t ^ 2) := by
  by_cases heq : a = b
  · subst b
    simp
  have hpos : 0 < b - a := sub_pos.mpr (lt_of_le_of_ne hab heq)
  have hd : Continuous (deriv r) := hr.continuous_deriv_one
  have hFTC : (∫ t in a..b, deriv r t) = r b - r a :=
    intervalIntegral.integral_deriv_eq_sub
      (fun t _ ↦ hr.differentiable (by norm_num) t) (hd.intervalIntegrable a b)
  have hA : IntervalIntegrable
      (fun t ↦ (b - a) ^ 2 * deriv r t ^ 2) volume a b :=
    ((hd.pow 2).const_mul ((b - a) ^ 2)).intervalIntegrable a b
  have hB : IntervalIntegrable
      (fun t ↦ (2 * (b - a) * (r b - r a)) * deriv r t) volume a b :=
    (hd.const_mul (2 * (b - a) * (r b - r a))).intervalIntegrable a b
  have hidentity :
      (∫ t in a..b, ((b - a) * deriv r t - (r b - r a)) ^ 2) =
        (b - a) * ((b - a) * (∫ t in a..b, deriv r t ^ 2) - (r b - r a) ^ 2) := by
    calc
      _ = ∫ t in a..b,
          ((b - a) ^ 2 * deriv r t ^ 2 -
            (2 * (b - a) * (r b - r a)) * deriv r t) + (r b - r a) ^ 2 := by
        apply intervalIntegral.integral_congr
        intro t _
        ring
      _ = _ := by
        rw [intervalIntegral.integral_add (hA.sub hB) intervalIntegrable_const,
          intervalIntegral.integral_sub hA hB,
          intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
          intervalIntegral.integral_const, hFTC]
        simp only [smul_eq_mul]
        ring
  have hnonneg : 0 ≤ ∫ t in a..b,
      ((b - a) * deriv r t - (r b - r a)) ^ 2 :=
    intervalIntegral.integral_nonneg_of_forall hab (fun t ↦ sq_nonneg _)
  rw [hidentity] at hnonneg
  have hmul :
      (b - a) * (r b - r a) ^ 2 ≤
        (b - a) * ((b - a) * (∫ t in a..b, deriv r t ^ 2)) := by
    nlinarith only [hnonneg]
  exact le_of_mul_le_mul_left hmul hpos

/-- On a closed interval, each squared two-point increment is bounded by the
distance between the points times the derivative energy of the whole interval. -/
theorem sq_sub_le_abs_mul_integral_deriv_sq
    (r : ℝ → ℝ) (hr : ContDiff ℝ 1 r) (a b x y : ℝ)
    (hx : x ∈ Icc a b) (hy : y ∈ Icc a b) :
    (r x - r y) ^ 2 ≤ |x - y| * (∫ t in a..b, deriv r t ^ 2) := by
  have hd : Continuous (fun t ↦ deriv r t ^ 2) := hr.continuous_deriv_one.pow 2
  rcases le_total x y with hxy | hyx
  · have hmono : (∫ t in x..y, deriv r t ^ 2) ≤ ∫ t in a..b, deriv r t ^ 2 :=
      intervalIntegral.integral_mono_interval hx.1 hxy hy.2
        (Filter.Eventually.of_forall (fun t ↦ sq_nonneg (deriv r t)))
        (hd.intervalIntegrable a b)
    calc
      (r x - r y) ^ 2 = (r y - r x) ^ 2 := by ring
      _ ≤ (y - x) * (∫ t in x..y, deriv r t ^ 2) :=
        sq_sub_le_length_mul_integral_deriv_sq r hr x y hxy
      _ ≤ (y - x) * (∫ t in a..b, deriv r t ^ 2) :=
        mul_le_mul_of_nonneg_left hmono (sub_nonneg.mpr hxy)
      _ = |x - y| * (∫ t in a..b, deriv r t ^ 2) := by
        rw [abs_of_nonpos (sub_nonpos.mpr hxy)]
        ring
  · have hmono : (∫ t in y..x, deriv r t ^ 2) ≤ ∫ t in a..b, deriv r t ^ 2 :=
      intervalIntegral.integral_mono_interval hy.1 hyx hx.2
        (Filter.Eventually.of_forall (fun t ↦ sq_nonneg (deriv r t)))
        (hd.intervalIntegrable a b)
    calc
      (r x - r y) ^ 2 ≤ (x - y) * (∫ t in y..x, deriv r t ^ 2) :=
        sq_sub_le_length_mul_integral_deriv_sq r hr y x hyx
      _ ≤ (x - y) * (∫ t in a..b, deriv r t ^ 2) :=
        mul_le_mul_of_nonneg_left hmono (sub_nonneg.mpr hyx)
      _ = |x - y| * (∫ t in a..b, deriv r t ^ 2) := by
        rw [abs_of_nonneg (sub_nonneg.mpr hyx)]

/-- The square integrals of a function and its derivative control every
point value on a nondegenerate closed interval, without boundary conditions. -/
theorem length_mul_sq_le_integral_sq_add_integral_deriv_sq
    (r : ℝ → ℝ) (hr : ContDiff ℝ 1 r) (a b x : ℝ)
    (hab : a < b) (hx : x ∈ Icc a b) :
    (b - a) * r x ^ 2 ≤ 2 * (∫ t in a..b, r t ^ 2) +
      2 * (b - a) ^ 2 * (∫ t in a..b, deriv r t ^ 2) := by
  have hE : 0 ≤ ∫ t in a..b, deriv r t ^ 2 :=
    intervalIntegral.integral_nonneg_of_forall hab.le (fun t ↦ sq_nonneg _)
  have hpoint : ∀ y ∈ Icc a b,
      r x ^ 2 ≤ 2 * r y ^ 2 + 2 * (b - a) * (∫ t in a..b, deriv r t ^ 2) := by
    intro y hy
    have hxy : |x - y| ≤ b - a := by
      apply abs_le.mpr
      constructor <;> linarith [hx.1, hx.2, hy.1, hy.2]
    have hdiff : (r x - r y) ^ 2 ≤
        (b - a) * (∫ t in a..b, deriv r t ^ 2) :=
      (sq_sub_le_abs_mul_integral_deriv_sq r hr a b x y hx hy).trans
        (mul_le_mul_of_nonneg_right hxy hE)
    nlinarith only [hdiff, sq_nonneg (r x - 2 * r y)]
  have hvalue : IntervalIntegrable (fun t ↦ 2 * r t ^ 2) volume a b :=
    ((hr.continuous.pow 2).const_mul 2).intervalIntegrable a b
  have hbound := intervalIntegral.integral_mono_on (μ := volume) hab.le
    (f := fun _ ↦ r x ^ 2)
    (g := fun y ↦ 2 * r y ^ 2 +
      2 * (b - a) * (∫ t in a..b, deriv r t ^ 2))
    intervalIntegrable_const (hvalue.add intervalIntegrable_const) hpoint
  calc
    (b - a) * r x ^ 2 = ∫ _ in a..b, r x ^ 2 := by
      rw [intervalIntegral.integral_const, smul_eq_mul]
    _ ≤ ∫ y in a..b,
        2 * r y ^ 2 + 2 * (b - a) * (∫ t in a..b, deriv r t ^ 2) := hbound
    _ = 2 * (∫ t in a..b, r t ^ 2) +
        2 * (b - a) ^ 2 * (∫ t in a..b, deriv r t ^ 2) := by
      rw [intervalIntegral.integral_add hvalue intervalIntegrable_const,
        intervalIntegral.integral_const_mul, intervalIntegral.integral_const]
      simp only [smul_eq_mul]
      ring

end RicciFlowSharpEstimate.Analysis
