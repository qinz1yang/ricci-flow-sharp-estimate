/-
Copyright (c) 2026 Ziyang Qin. All rights reserved.
No license is granted by this file.
Authors: Ziyang Qin
-/
import RicciFlowSharpEstimate.Geometry.RotationalPoleData
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# The meridional interval action

The scalar operator and integral in the geometric reduction use the original
profile and its actual warping integral. Regularity is proved on the closed
physical interval; no extension of the reciprocal profile is assumed.
-/

noncomputable section

namespace RicciFlowSharpEstimate.Geometry.RotationalProfile.PoleData

open Set MeasureTheory intervalIntegral
open scoped ContDiff

/-- The coefficient `H=f/a` in the meridional operator. -/
def meridionalWeight (D : PoleData) (v : ℝ) : ℝ := warp D.a v / D.a v

/-- The actual second-order scalar operator associated to a meridional probe. -/
def meridionalOperator (D : PoleData) (r : ℝ → ℝ) (v : ℝ) : ℝ :=
  D.meridionalWeight v * deriv (deriv r) v +
    (deriv D.meridionalWeight v - 2 * v) * deriv r v - r v

/-- The complete meridional interval density. -/
def meridionalDensity (D : PoleData) (r : ℝ → ℝ) (v : ℝ) : ℝ :=
  D.meridionalWeight v * (D.meridionalOperator r v) ^ 2 +
    (D.meridionalWeight v - 2 * v ^ 2) * r v ^ 2 +
    2 * v * D.meridionalWeight v * r v * deriv r v

/-- The interval action, before the sphere's angular factor `2*pi`. -/
def meridionalAction (D : PoleData) (r : ℝ → ℝ) : ℝ :=
  ∫ v in (-1 : ℝ)..1, D.meridionalDensity r v

/-- Differentiation of `f/a` is valid at every point of the closed physical interval. -/
theorem meridionalWeight_hasDerivAt (D : PoleData) (v : ℝ)
    (hv : v ∈ Icc (-1 : ℝ) 1) :
    HasDerivAt D.meridionalWeight
      (-2 * v - D.meridionalWeight v * deriv D.a v / D.a v) v := by
  have ha := (D.a_pos v hv).ne'
  convert (warp_hasDerivAt D.a D.a_contDiff.continuous v).div
    (D.a_contDiff.differentiable (by simp)).differentiableAt.hasDerivAt ha using 1
  · rfl
  · dsimp [meridionalWeight]
    field_simp

/-- The weight is continuous through both poles. -/
theorem meridionalWeight_continuousOn (D : PoleData) :
    ContinuousOn D.meridionalWeight (Icc (-1 : ℝ) 1) :=
  (warp_contDiff D.a D.a_contDiff).continuous.continuousOn.div
    D.a_contDiff.continuous.continuousOn (fun v hv => (D.a_pos v hv).ne')

/-- The derivative in the operator is also continuous through both poles. -/
theorem deriv_meridionalWeight_continuousOn (D : PoleData) :
    ContinuousOn (deriv D.meridionalWeight) (Icc (-1 : ℝ) 1) := by
  have hc : ContinuousOn
      (fun v => -2 * v - D.meridionalWeight v * deriv D.a v / D.a v)
      (Icc (-1 : ℝ) 1) :=
    ((continuousOn_const.mul continuousOn_id).sub
      ((D.meridionalWeight_continuousOn.mul
        (D.a_contDiff.continuous_deriv (by simp)).continuousOn).div
          D.a_contDiff.continuous.continuousOn (fun v hv => (D.a_pos v hv).ne')))
  exact hc.congr (fun v hv => (D.meridionalWeight_hasDerivAt v hv).deriv)

/-- A globally smooth probe gives a genuinely continuous complete density. -/
theorem meridionalDensity_continuousOn (D : PoleData) (r : ℝ → ℝ)
    (hr : ContDiff ℝ ∞ r) :
    ContinuousOn (D.meridionalDensity r) (Icc (-1 : ℝ) 1) := by
  have hr' := (contDiff_infty_iff_deriv.mp hr).2
  have hL : ContinuousOn (D.meridionalOperator r) (Icc (-1 : ℝ) 1) :=
    ((D.meridionalWeight_continuousOn.mul
      (hr'.continuous_deriv (by simp)).continuousOn).add
        ((D.deriv_meridionalWeight_continuousOn.sub
          (continuousOn_const.mul continuousOn_id)).mul hr'.continuous.continuousOn)).sub
            hr.continuous.continuousOn
  exact ((D.meridionalWeight_continuousOn.mul (hL.pow 2)).add
    ((D.meridionalWeight_continuousOn.sub
      (continuousOn_const.mul (continuousOn_id.pow 2))).mul
        (hr.continuous.continuousOn.pow 2))).add
          ((((continuousOn_const.mul continuousOn_id).mul D.meridionalWeight_continuousOn).mul
            hr.continuous.continuousOn).mul hr'.continuous.continuousOn)

/-- In particular the action does not rely on a totalized nonintegrable integral. -/
theorem meridionalDensity_intervalIntegrable (D : PoleData) (r : ℝ → ℝ)
    (hr : ContDiff ℝ ∞ r) : IntervalIntegrable (D.meridionalDensity r) volume (-1) 1 :=
  (D.meridionalDensity_continuousOn r hr).intervalIntegrable_of_Icc (by norm_num)

/-- Every positive constant profile has the same weight `1-v²`. -/
theorem meridionalWeight_constant (c : ℝ) (hc : 0 < c) :
    (constant c hc).meridionalWeight = fun v => 1 - v ^ 2 := by
  funext v
  dsimp [meridionalWeight, constant]
  rw [warp_const]
  field_simp [hc.ne']

/-- The unit-probe round interval action is `4/3`, independent of metric scale. -/
theorem meridionalAction_constant_one (c : ℝ) (hc : 0 < c) :
    (constant c hc).meridionalAction (fun _ => 1) = 4 / 3 := by
  have hd : (constant c hc).meridionalDensity (fun _ => 1) =
      fun v => 2 - 4 * v ^ 2 := by
    funext v
    simp only [meridionalDensity, meridionalOperator, deriv_const', deriv_const,
      mul_zero, add_zero, zero_sub, one_pow, neg_sq, mul_one,
      meridionalWeight_constant]
    ring
  rw [meridionalAction, hd]
  norm_num [intervalIntegral.integral_sub, intervalIntegral.integral_const_mul, integral_pow]

end RicciFlowSharpEstimate.Geometry.RotationalProfile.PoleData
