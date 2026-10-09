/-
Copyright (c) 2026 Ziyang Qin. All rights reserved.
No license is granted by this file.
Authors: Ziyang Qin
-/
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Weighted square completion in polar coordinates

Only positivity in the open polar interval and finite weighted energy are
required of the weight. The square's integrability follows from an algebraic
expansion; the mixed term is handled by the fundamental theorem of calculus
for the actual function `cos(s) * y(s)^2`.
-/

noncomputable section

namespace RicciFlowSharpEstimate.Analysis

open MeasureTheory Set

private theorem continuous_polar_cross (y : ℝ → ℝ) (hy : ContDiff ℝ 1 y) :
    Continuous (fun s => 2 * Real.cos s * y s * deriv y s) :=
  ((continuous_const.mul Real.continuous_cos).mul hy.continuous).mul hy.continuous_deriv_one

private theorem continuous_polar_boundary (y : ℝ → ℝ) (hy : ContDiff ℝ 1 y) :
    Continuous (fun s => -Real.sin s * y s ^ 2 + 2 * Real.cos s * y s * deriv y s) :=
  (Real.continuous_sin.neg.mul (hy.continuous.pow 2)).add (continuous_polar_cross y hy)

private theorem polar_square_expand {w a b c : ℝ} (hw : w ≠ 0) :
    (w * b - c * a) ^ 2 / w = w * b ^ 2 + c ^ 2 * (a ^ 2 / w) - 2 * c * a * b := by
  field_simp
  ring

/-- Finite weighted energy gives integrability of the completed square, without
any regularity assumption on the positive interior weight. -/
theorem intervalIntegrable_polar_square (W y : ℝ → ℝ)
    (hW : ∀ s ∈ Ioo (0 : ℝ) Real.pi, 0 < W s) (hy : ContDiff ℝ 1 y)
    (hR : IntervalIntegrable (fun s => W s * (deriv y s) ^ 2) volume 0 Real.pi)
    (hV : IntervalIntegrable (fun s => y s ^ 2 / W s) volume 0 Real.pi) :
    IntervalIntegrable (fun s => (W s * deriv y s - Real.cos s * y s) ^ 2 / W s)
      volume 0 Real.pi := by
  have hcos : IntervalIntegrable
      (fun s => Real.cos s ^ 2 * (y s ^ 2 / W s)) volume 0 Real.pi := by
    simpa only [Pi.pow_apply] using
      hV.continuousOn_mul (Real.continuous_cos.pow 2).continuousOn
  have hcross := (continuous_polar_cross y hy).intervalIntegrable (μ := volume) 0 Real.pi
  refine ((hR.add hcos).sub hcross).congr_uIoo ?_
  intro s hs
  have hs' : s ∈ Ioo (0 : ℝ) Real.pi := by
    simpa only [uIoo_of_le Real.pi_pos.le] using hs
  exact (polar_square_expand (ne_of_gt (hW s hs'))).symm

private theorem intervalIntegrable_polar_remainder (W y : ℝ → ℝ)
    (hV : IntervalIntegrable (fun s => y s ^ 2 / W s) volume 0 Real.pi) :
    IntervalIntegrable (fun s => Real.sin s ^ 2 * y s ^ 2 / W s) volume 0 Real.pi := by
  simpa only [mul_div_assoc, Pi.pow_apply] using
    hV.continuousOn_mul (Real.continuous_sin.pow 2).continuousOn

private theorem integral_polar_boundary_eq_zero (y : ℝ → ℝ) (hy : ContDiff ℝ 1 y)
    (h0 : y 0 = 0) (hpi : y Real.pi = 0) :
    (∫ s in (0 : ℝ)..Real.pi,
      -Real.sin s * y s ^ 2 + 2 * Real.cos s * y s * deriv y s) = 0 := by
  have hderiv (s : ℝ) : HasDerivAt (fun t => Real.cos t * y t ^ 2)
      (-Real.sin s * y s ^ 2 + 2 * Real.cos s * y s * deriv y s) s := by
    convert (Real.hasDerivAt_cos s).mul
      (((hy.differentiable (by norm_num)) s).hasDerivAt.pow 2) using 1
    simp only [Pi.pow_apply]
    ring
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun s _ => hderiv s) ((continuous_polar_boundary y hy).intervalIntegrable 0 Real.pi)
  simpa only [h0, hpi, zero_pow (by norm_num : 2 ≠ 0), mul_zero, sub_self] using h

private theorem polar_square_identity (W y : ℝ → ℝ) (s : ℝ) (hW : W s ≠ 0) :
    W s * (deriv y s) ^ 2 + y s ^ 2 / W s - Real.sin s * y s ^ 2 =
      (W s * deriv y s - Real.cos s * y s) ^ 2 / W s +
        Real.sin s ^ 2 * y s ^ 2 / W s +
        (-Real.sin s * y s ^ 2 + 2 * Real.cos s * y s * deriv y s) := by
  rw [polar_square_expand hW]
  have htrig := congrArg (fun t : ℝ => t * (y s ^ 2 / W s)) (Real.sin_sq_add_cos_sq s)
  linear_combination -htrig

/-- Completing the polar square for a `C¹` function vanishing at both poles. -/
theorem integral_polar_square_completion (W y : ℝ → ℝ)
    (hW : ∀ s ∈ Ioo (0 : ℝ) Real.pi, 0 < W s) (hy : ContDiff ℝ 1 y)
    (h0 : y 0 = 0) (hpi : y Real.pi = 0)
    (hR : IntervalIntegrable (fun s => W s * (deriv y s) ^ 2) volume 0 Real.pi)
    (hV : IntervalIntegrable (fun s => y s ^ 2 / W s) volume 0 Real.pi) :
    (∫ s in (0 : ℝ)..Real.pi,
      W s * (deriv y s) ^ 2 + y s ^ 2 / W s - Real.sin s * y s ^ 2) =
      (∫ s in (0 : ℝ)..Real.pi, (W s * deriv y s - Real.cos s * y s) ^ 2 / W s) +
      ∫ s in (0 : ℝ)..Real.pi, Real.sin s ^ 2 * y s ^ 2 / W s := by
  have hsq := intervalIntegrable_polar_square W y hW hy hR hV
  have hrem := intervalIntegrable_polar_remainder W y hV
  have hboundary := (continuous_polar_boundary y hy).intervalIntegrable (μ := volume) 0 Real.pi
  calc
    _ = ∫ s in (0 : ℝ)..Real.pi,
        ((W s * deriv y s - Real.cos s * y s) ^ 2 / W s +
          Real.sin s ^ 2 * y s ^ 2 / W s) +
          (-Real.sin s * y s ^ 2 + 2 * Real.cos s * y s * deriv y s) := by
      apply intervalIntegral.integral_congr_uIoo
      intro s hs
      have hs' : s ∈ Ioo (0 : ℝ) Real.pi := by
        simpa only [uIoo_of_le Real.pi_pos.le] using hs
      exact polar_square_identity W y s (ne_of_gt (hW s hs'))
    _ = _ := by
      rw [intervalIntegral.integral_add (hsq.add hrem) hboundary,
        intervalIntegral.integral_add hsq hrem, integral_polar_boundary_eq_zero y hy h0 hpi,
        add_zero]

/-- Dropping the completed square leaves a nonnegative weighted sine-square lower bound. -/
theorem integral_weighted_sin_sq_le_polar_energy (W y : ℝ → ℝ)
    (hW : ∀ s ∈ Ioo (0 : ℝ) Real.pi, 0 < W s) (hy : ContDiff ℝ 1 y)
    (h0 : y 0 = 0) (hpi : y Real.pi = 0)
    (hR : IntervalIntegrable (fun s => W s * (deriv y s) ^ 2) volume 0 Real.pi)
    (hV : IntervalIntegrable (fun s => y s ^ 2 / W s) volume 0 Real.pi) :
    (∫ s in (0 : ℝ)..Real.pi, Real.sin s ^ 2 * y s ^ 2 / W s) ≤
      ∫ s in (0 : ℝ)..Real.pi,
        W s * (deriv y s) ^ 2 + y s ^ 2 / W s - Real.sin s * y s ^ 2 := by
  have hsq : 0 ≤ ∫ s in (0 : ℝ)..Real.pi,
      (W s * deriv y s - Real.cos s * y s) ^ 2 / W s := by
    rw [intervalIntegral.integral_of_le Real.pi_pos.le, ← restrict_Ioo_eq_restrict_Ioc]
    apply MeasureTheory.integral_nonneg_of_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
    exact div_nonneg (sq_nonneg _) (hW s hs).le
  rw [integral_polar_square_completion W y hW hy h0 hpi hR hV]
  exact le_add_of_nonneg_left hsq

end RicciFlowSharpEstimate.Analysis
