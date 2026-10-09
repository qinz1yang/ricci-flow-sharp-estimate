/-
Copyright (c) 2026 Ziyang Qin. All rights reserved.
No license is granted by this file.
Authors: Ziyang Qin
-/
import RicciFlowSharpEstimate.Geometry.AreaProfileCalculus
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Tactic.FunProp

/-!
# Regularity and round normalization of the complete area action

The full six-entry density is integrated using the actual curvature primitives
and actual probe derivatives. Its constant-curvature unit-probe value is `4/3`.
-/

noncomputable section

namespace RicciFlowSharpEstimate.Geometry.AreaProfile

open MeasureTheory
open scoped ContDiff

/-- The actual complete density is continuous for continuous curvature and a smooth probe. -/
theorem meridionalAction_integrand_continuous (K r : ℝ → ℝ)
    (hK : Continuous K) (hr : ContDiff ℝ ∞ r) :
    Continuous (fun x => meridionalActionDensity (warp K x) (warpSlope K x)
      (K x) (r x) (deriv r x) (deriv (deriv r) x)) := by
  have hf := warp_continuous K hK
  have hf1 := warpSlope_continuous K hK
  have hr1 := hr.continuous_deriv (by simp)
  have hr2 := (contDiff_infty_iff_deriv.mp hr).2.continuous_deriv (by simp)
  unfold meridionalActionDensity
  fun_prop

/-- The complete area action uses a genuinely integrable integrand. -/
theorem meridionalAction_integrand_intervalIntegrable (K r : ℝ → ℝ)
    (hK : Continuous K) (hr : ContDiff ℝ ∞ r) :
    IntervalIntegrable (fun x => meridionalActionDensity (warp K x) (warpSlope K x)
      (K x) (r x) (deriv r x) (deriv (deriv r) x)) volume 0 1 :=
  (meridionalAction_integrand_continuous K r hK hr).intervalIntegrable 0 1

/-- The curvature-two warp is the actual round quadratic area profile. -/
theorem warp_two (x : ℝ) : warp (fun _ => 2) x = 2 * x - 2 * x ^ 2 := by
  rw [warp, Analysis.SecondPrimitive.integral_kernel_eq
    (fun _ => 2) continuous_const 0 x, intervalIntegral.integral_mul_const]
  simp only [intervalIntegral.integral_const, sub_zero, smul_eq_mul, integral_id]
  ring

/-- Its actual slope has the two smooth-pole values `2` and `-2`. -/
theorem warpSlope_two (x : ℝ) : warpSlope (fun _ => 2) x = 2 - 4 * x := by
  simp only [warpSlope, intervalIntegral.integral_const, sub_zero, smul_eq_mul]
  ring

/-- The nonzero unit probe gives the normalized round complete action. -/
theorem meridionalAction_two_one : meridionalAction (fun _ => 2) (fun _ => 1) = 4 / 3 := by
  have hd : (fun x => meridionalActionDensity (warp (fun _ => 2) x)
      (warpSlope (fun _ => 2) x) 2 1 (deriv (fun _ : ℝ => (1 : ℝ)) x)
      (deriv (deriv (fun _ : ℝ => (1 : ℝ))) x)) =
      fun x => 32 * x - 32 * x ^ 2 - 4 := by
    funext x
    simp only [meridionalActionDensity, warp_two, warpSlope_two, deriv_const', deriv_const]
    ring
  rw [meridionalAction, hd]
  have hi1 : IntervalIntegrable (fun x : ℝ => 32 * x) volume 0 1 :=
    (continuous_const.mul continuous_id).intervalIntegrable 0 1
  have hi2 : IntervalIntegrable (fun x : ℝ => 32 * x ^ 2) volume 0 1 :=
    (continuous_const.mul (continuous_id.pow 2)).intervalIntegrable 0 1
  rw [intervalIntegral.integral_sub (hi1.sub hi2) intervalIntegrable_const,
    intervalIntegral.integral_sub hi1 hi2]
  rw [intervalIntegral.integral_const_mul (32 : ℝ) (fun x => x)]
  norm_num [intervalIntegral.integral_const_mul, integral_pow, integral_id]

end RicciFlowSharpEstimate.Geometry.AreaProfile
