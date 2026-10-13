/-
Copyright (c) 2026 Ziyang Qin. All rights reserved.
No license is granted by this file.
Authors: Ziyang Qin
-/
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# A Hardy estimate for the parabolic weight on the unit interval

The weight `x * (1 - x)` controls the ordinary square integral together with
its square times the derivative energy. The endpoint terms vanish because
the integration-by-parts flux contains the weight, so the function and its
derivative need not satisfy endpoint conditions.
-/

noncomputable section

namespace RicciFlowSharpEstimate.Analysis

open MeasureTheory Set

private theorem parabolic_mixed_term_le (w b u v : ℝ) (hb : b ^ 2 ≤ 1) :
    -2 * w * b * u * v ≤ u ^ 2 / 2 + 2 * w ^ 2 * v ^ 2 := by
  have hbu : b ^ 2 * u ^ 2 ≤ u ^ 2 := by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hb (sq_nonneg u)
  nlinarith only [hbu, sq_nonneg (b * u + 2 * w * v)]

private theorem integral_parabolic_boundary_eq_zero
    (r : ℝ → ℝ) (hr : ContDiff ℝ 1 r) :
    (∫ x in (0 : ℝ)..1,
      (r x ^ 2 - 6 * (x * (1 - x) * r x ^ 2)) +
        2 * (x * (1 - x) * (1 - 2 * x) * r x * deriv r x)) = 0 := by
  have hw : Continuous (fun x : ℝ => x * (1 - x)) :=
    continuous_id.mul (continuous_const.sub continuous_id)
  have hb : Continuous (fun x : ℝ => 1 - 2 * x) :=
    continuous_const.sub (continuous_const.mul continuous_id)
  have hcont : Continuous (fun x : ℝ =>
      (r x ^ 2 - 6 * (x * (1 - x) * r x ^ 2)) +
        2 * (x * (1 - x) * (1 - 2 * x) * r x * deriv r x)) :=
    ((hr.continuous.pow 2).sub (continuous_const.mul (hw.mul (hr.continuous.pow 2)))).add
      (continuous_const.mul (((hw.mul hb).mul hr.continuous).mul hr.continuous_deriv_one))
  have hderiv (x : ℝ) :
      HasDerivAt (fun t : ℝ => t * (1 - t) * (1 - 2 * t) * r t ^ 2)
        ((r x ^ 2 - 6 * (x * (1 - x) * r x ^ 2)) +
          2 * (x * (1 - x) * (1 - 2 * x) * r x * deriv r x)) x := by
    have hw' : HasDerivAt (fun t : ℝ => t * (1 - t)) (1 - 2 * x) x := by
      convert (hasDerivAt_id x).mul ((hasDerivAt_id x).const_sub 1) using 1
      · rfl
      · simp only [id_eq]
        ring
    have hb' : HasDerivAt (fun t : ℝ => 1 - 2 * t) (-2) x := by
      simpa only [id_eq, mul_one] using
        ((hasDerivAt_id x).const_mul 2).const_sub 1
    convert (hw'.mul hb').mul
      (((hr.differentiable (by norm_num)) x).hasDerivAt.pow 2) using 1
    simp only [Pi.mul_apply, Pi.pow_apply]
    ring
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun x _ => hderiv x) (hcont.intervalIntegrable 0 1)
  simpa using h

/-- The parabolic weight and its squared derivative energy control the square
integral of a `C¹` function, without endpoint conditions. -/
theorem integral_sq_le_parabolic_weighted_energy
    (r : ℝ → ℝ) (hr : ContDiff ℝ 1 r) :
    (∫ x in (0 : ℝ)..1, r x ^ 2) ≤
      12 * (∫ x in (0 : ℝ)..1, x * (1 - x) * r x ^ 2) +
        4 * (∫ x in (0 : ℝ)..1, (x * (1 - x)) ^ 2 * (deriv r x) ^ 2) := by
  have hw : Continuous (fun x : ℝ => x * (1 - x)) :=
    continuous_id.mul (continuous_const.sub continuous_id)
  have hb : Continuous (fun x : ℝ => 1 - 2 * x) :=
    continuous_const.sub (continuous_const.mul continuous_id)
  have hU : IntervalIntegrable (fun x => r x ^ 2) volume 0 1 :=
    (hr.continuous.pow 2).intervalIntegrable 0 1
  have hM : IntervalIntegrable (fun x => x * (1 - x) * r x ^ 2) volume 0 1 :=
    (hw.mul (hr.continuous.pow 2)).intervalIntegrable 0 1
  have hD : IntervalIntegrable
      (fun x => (x * (1 - x)) ^ 2 * (deriv r x) ^ 2) volume 0 1 :=
    ((hw.pow 2).mul (hr.continuous_deriv_one.pow 2)).intervalIntegrable 0 1
  have hC : IntervalIntegrable
      (fun x => x * (1 - x) * (1 - 2 * x) * r x * deriv r x) volume 0 1 :=
    (((hw.mul hb).mul hr.continuous).mul hr.continuous_deriv_one).intervalIntegrable 0 1
  have hflux := integral_parabolic_boundary_eq_zero r hr
  rw [intervalIntegral.integral_add (hU.sub (hM.const_mul 6)) (hC.const_mul 2),
    intervalIntegral.integral_sub hU (hM.const_mul 6),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul] at hflux
  have hpoint (x : ℝ) (hx : x ∈ Icc (0 : ℝ) 1) :
      -2 * (x * (1 - x) * (1 - 2 * x) * r x * deriv r x) ≤
        (1 / 2 : ℝ) * r x ^ 2 + 2 * ((x * (1 - x)) ^ 2 * (deriv r x) ^ 2) := by
    have hw_nonneg : 0 ≤ x * (1 - x) := mul_nonneg hx.1 (sub_nonneg.mpr hx.2)
    have hb_sq : (1 - 2 * x) ^ 2 ≤ 1 := by
      nlinarith only [hw_nonneg]
    have h := parabolic_mixed_term_le (x * (1 - x)) (1 - 2 * x)
      (r x) (deriv r x) hb_sq
    nlinarith only [h]
  have hbound := intervalIntegral.integral_mono_on
    (by norm_num : (0 : ℝ) ≤ 1) (hC.const_mul (-2))
    ((hU.const_mul (1 / 2)).add (hD.const_mul 2)) hpoint
  rw [intervalIntegral.integral_add (hU.const_mul (1 / 2)) (hD.const_mul 2),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul] at hbound
  linarith only [hflux, hbound]

end RicciFlowSharpEstimate.Analysis
