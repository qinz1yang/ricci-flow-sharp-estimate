/-
Copyright (c) 2026 Ziyang Qin. All rights reserved.
No license is granted by this file.
Authors: Ziyang Qin
-/
import RicciFlowSharpEstimate.Analysis.ParabolicWeightedHardy

/-!
# Interpolation between parabolic derivative weights

A boundary-vanishing polynomial flux controls the first power of the parabolic
weight using its second power and a derivative term with its third power.
-/

noncomputable section

namespace RicciFlowSharpEstimate.Analysis

open MeasureTheory Set

/-- A weighted interpolation estimate without any endpoint conditions. -/
theorem integral_parabolic_mul_sq_le (p : ℝ → ℝ) (hp : ContDiff ℝ 1 p) :
    (∫ x in (0 : ℝ)..1, x * (1 - x) * p x ^ 2) ≤
      10 * (∫ x in (0 : ℝ)..1, (x * (1 - x)) ^ 2 * p x ^ 2) +
        ∫ x in (0 : ℝ)..1, (x * (1 - x)) ^ 3 * deriv p x ^ 2 := by
  have hw : Continuous (fun x : ℝ => x * (1 - x)) := by fun_prop
  have hb : Continuous (fun x : ℝ => 1 - 2 * x) := by fun_prop
  have hp0 := hp.continuous
  have hp1 := hp.continuous_deriv_one
  have hH : Continuous (fun x : ℝ => x * (1 - x) * p x ^ 2) := by fun_prop
  have hG : Continuous (fun x : ℝ => (x * (1 - x)) ^ 2 * p x ^ 2) := by fun_prop
  have hJ : Continuous (fun x : ℝ => (x * (1 - x)) ^ 3 * deriv p x ^ 2) := by fun_prop
  have hC : Continuous (fun x : ℝ =>
      (x * (1 - x)) ^ 2 * (1 - 2 * x) * p x * deriv p x) := by fun_prop
  have hderiv (x : ℝ) :
      HasDerivAt (fun y : ℝ => (y * (1 - y)) ^ 2 * (1 - 2 * y) * p y ^ 2)
        (2 * (x * (1 - x) * p x ^ 2) - 10 * ((x * (1 - x)) ^ 2 * p x ^ 2) +
          2 * ((x * (1 - x)) ^ 2 * (1 - 2 * x) * p x * deriv p x)) x := by
    have hw' : HasDerivAt (fun y : ℝ => y * (1 - y)) (1 - 2 * x) x := by
      convert (hasDerivAt_id x).mul ((hasDerivAt_id x).const_sub 1) using 1
      · rfl
      · simp only [id_eq]
        ring
    have hb' : HasDerivAt (fun y : ℝ => 1 - 2 * y) (-2) x := by
      simpa only [id_eq, mul_one] using ((hasDerivAt_id x).const_mul 2).const_sub 1
    convert ((hw'.pow 2).mul hb').mul
      ((hp.differentiable (by norm_num) x).hasDerivAt.pow 2) using 1
    simp only [Pi.mul_apply, Pi.pow_apply]
    ring
  have hflux := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun x _ => hderiv x)
    ((((hH.const_mul 2).sub (hG.const_mul 10)).add (hC.const_mul 2)).intervalIntegrable 0 1)
  have hHG : IntervalIntegrable (fun x : ℝ =>
      2 * (x * (1 - x) * p x ^ 2) - 10 * ((x * (1 - x)) ^ 2 * p x ^ 2)) volume 0 1 :=
    ((hH.const_mul 2).sub (hG.const_mul 10)).intervalIntegrable 0 1
  rw [intervalIntegral.integral_add hHG
      ((hC.const_mul 2).intervalIntegrable 0 1),
    intervalIntegral.integral_sub ((hH.const_mul 2).intervalIntegrable 0 1)
      ((hG.const_mul 10).intervalIntegrable 0 1),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul] at hflux
  simp only [sub_zero, mul_zero, zero_mul, zero_pow (by norm_num : (2 : ℕ) ≠ 0),
    sub_self] at hflux
  have hpoint (x : ℝ) (hx : x ∈ Icc (0 : ℝ) 1) :
      -2 * ((x * (1 - x)) ^ 2 * (1 - 2 * x) * p x * deriv p x) ≤
        x * (1 - x) * p x ^ 2 + (x * (1 - x)) ^ 3 * deriv p x ^ 2 := by
    have hw0 : 0 ≤ x * (1 - x) := mul_nonneg hx.1 (sub_nonneg.mpr hx.2)
    have hb2 : (1 - 2 * x) ^ 2 ≤ 1 := by nlinarith [mul_nonneg hx.1 (sub_nonneg.mpr hx.2)]
    have hsq := mul_nonneg hw0 (sq_nonneg ((1 - 2 * x) * p x + x * (1 - x) * deriv p x))
    have hrem := mul_nonneg hw0 (mul_nonneg (sub_nonneg.mpr hb2) (sq_nonneg (p x)))
    nlinarith only [hsq, hrem]
  have hint := intervalIntegral.integral_mono_on (μ := volume) zero_le_one
    ((hC.const_mul (-2)).intervalIntegrable 0 1) ((hH.add hJ).intervalIntegrable 0 1) hpoint
  simp only [Pi.add_apply] at hint
  rw [intervalIntegral.integral_const_mul,
    intervalIntegral.integral_add (hH.intervalIntegrable 0 1) (hJ.intervalIntegrable 0 1)] at hint
  linarith

end RicciFlowSharpEstimate.Analysis
