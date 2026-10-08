/-
Copyright (c) 2026 Ziyang Qin. All rights reserved.
No license is granted by this file.
Authors: Ziyang Qin
-/
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith

/-!
# The exponential free arc and its two primitives

The positive free arc has elementary primitives for both `E(v)` and `2v / E(v)`.
All derivative statements are on the positive half-line; the interval formulas
allow either orientation between positive endpoints.

The primitive formulas and derivative proofs adapt Ziyang Qin's owner-provided
historical `PureRotationSharpThreshold` source. No historical module is imported.
-/

namespace RicciFlowSharpEstimate.Variational

/-- The exponential profile along a free arc with scale `a`. -/
noncomputable def freeExponential (a v : ℝ) : ℝ :=
  Real.sqrt (v / a) * Real.exp ((2 / 3 : ℝ) * (Real.sqrt (v / a) ^ 3 - 1))

/-- An antiderivative of the free-arc exponential profile. -/
noncomputable def freeLeftPrimitive (a v : ℝ) : ℝ :=
  a * Real.exp ((2 / 3 : ℝ) * (Real.sqrt (v / a) ^ 3 - 1))

/-- An antiderivative of the weighted reciprocal free-arc profile. -/
noncomputable def freeRightPrimitive (a v : ℝ) : ℝ :=
  -2 * a ^ 2 * Real.exp (-((2 / 3 : ℝ) * (Real.sqrt (v / a) ^ 3 - 1)))

/-- The free-arc exponential is strictly positive on its natural domain. -/
theorem freeExponential_pos (a v : ℝ) (ha : 0 < a) (hv : 0 < v) :
    0 < freeExponential a v :=
  mul_pos (Real.sqrt_pos.2 (div_pos hv ha)) (Real.exp_pos _)

/-- Continuity of the totalized free-arc formula. -/
theorem continuous_freeExponential (a : ℝ) : Continuous (freeExponential a) := by
  unfold freeExponential
  fun_prop

private theorem hasDerivAt_freePhase (a v : ℝ) (ha : 0 < a) (hv : 0 < v) :
    HasDerivAt (fun x : ℝ => (2 / 3 : ℝ) * (Real.sqrt (x / a) ^ 3 - 1))
      (Real.sqrt (v / a) / a) v := by
  have hroot : HasDerivAt (fun x : ℝ => Real.sqrt (x / a))
      (1 / a / (2 * Real.sqrt (v / a))) v := by
    simpa only [id_eq] using
      ((hasDerivAt_id v).div_const a).sqrt (ne_of_gt (div_pos hv ha))
  apply (((hroot.pow 3).sub_const 1).const_mul (2 / 3 : ℝ)).congr_deriv
  have hrootPos : 0 < Real.sqrt (v / a) := Real.sqrt_pos.2 (div_pos hv ha)
  norm_num
  field_simp [ha.ne', hrootPos.ne']

/-- The first primitive differentiates to the actual free exponential. -/
theorem hasDerivAt_freeLeftPrimitive (a v : ℝ) (ha : 0 < a) (hv : 0 < v) :
    HasDerivAt (freeLeftPrimitive a) (freeExponential a v) v := by
  have hphase := hasDerivAt_freePhase a v ha hv
  apply (hphase.exp.const_mul a).congr_deriv
  dsimp [freeExponential]
  field_simp [ha.ne']

private theorem two_mul_div_freeExponential (a v : ℝ) (ha : 0 < a) (hv : 0 < v) :
    2 * v / freeExponential a v =
      2 * a * Real.sqrt (v / a) *
        Real.exp (-((2 / 3 : ℝ) * (Real.sqrt (v / a) ^ 3 - 1))) := by
  have hsquare : Real.sqrt (v / a) ^ 2 = v / a := Real.sq_sqrt (div_nonneg hv.le ha.le)
  have hrootPos : 0 < Real.sqrt (v / a) := Real.sqrt_pos.2 (div_pos hv ha)
  rw [Real.exp_neg]
  dsimp [freeExponential]
  have hexp : Real.exp ((2 / 3 : ℝ) * (Real.sqrt (v / a) ^ 3 - 1)) ≠ 0 :=
    ne_of_gt (Real.exp_pos _)
  have hvEq : v = a * Real.sqrt (v / a) ^ 2 := by
    rw [hsquare]
    field_simp [ha.ne']
  field_simp [hrootPos.ne', hexp, ha.ne']
  nlinarith

/-- The second primitive differentiates to `2v / E(v)`, using the same profile. -/
theorem hasDerivAt_freeRightPrimitive (a v : ℝ) (ha : 0 < a) (hv : 0 < v) :
    HasDerivAt (freeRightPrimitive a) (2 * v / freeExponential a v) v := by
  rw [two_mul_div_freeExponential a v ha hv]
  have hphase := hasDerivAt_freePhase a v ha hv
  apply (hphase.neg.exp.const_mul (-2 * a ^ 2)).congr_deriv
  dsimp
  field_simp [ha.ne']

@[simp] theorem freeExponential_self (a : ℝ) (ha : a ≠ 0) :
    freeExponential a a = 1 := by
  simp [freeExponential, div_self ha]

@[simp] theorem freeLeftPrimitive_self (a : ℝ) :
    freeLeftPrimitive a a = a := by
  by_cases ha : a = 0
  · simp [ha, freeLeftPrimitive]
  · simp [freeLeftPrimitive, div_self ha]

@[simp] theorem freeRightPrimitive_self (a : ℝ) :
    freeRightPrimitive a a = -2 * a ^ 2 := by
  by_cases ha : a = 0
  · simp [ha, freeRightPrimitive]
  · simp [freeRightPrimitive, div_self ha]

private theorem sqrt_mul_sq_div (a q : ℝ) (ha : a ≠ 0) (hq : 0 ≤ q) :
    Real.sqrt (a * q ^ 2 / a) = q := by
  rw [mul_div_cancel_left₀ (q ^ 2) ha]
  exact (Real.sqrt_sq_eq_abs q).trans (abs_of_nonneg hq)

/-- The right endpoint value of the exponential free arc. -/
theorem freeExponential_mul_sq (a q : ℝ) (ha : a ≠ 0) (hq : 0 ≤ q) :
    freeExponential a (a * q ^ 2) = q * Real.exp ((2 / 3 : ℝ) * (q ^ 3 - 1)) := by
  simp only [freeExponential, sqrt_mul_sq_div a q ha hq]

/-- The right endpoint value of the left primitive. -/
theorem freeLeftPrimitive_mul_sq (a q : ℝ) (hq : 0 ≤ q) :
    freeLeftPrimitive a (a * q ^ 2) = a * Real.exp ((2 / 3 : ℝ) * (q ^ 3 - 1)) := by
  by_cases ha : a = 0
  · simp [ha, freeLeftPrimitive]
  · simp only [freeLeftPrimitive, sqrt_mul_sq_div a q ha hq]

/-- The right endpoint value of the right primitive. -/
theorem freeRightPrimitive_mul_sq (a q : ℝ) (hq : 0 ≤ q) :
    freeRightPrimitive a (a * q ^ 2) =
      -2 * a ^ 2 * Real.exp (-((2 / 3 : ℝ) * (q ^ 3 - 1))) := by
  by_cases ha : a = 0
  · simp [ha, freeRightPrimitive]
  · simp only [freeRightPrimitive, sqrt_mul_sq_div a q ha hq]

/-- Exact integral of the free exponential between positive endpoints. -/
theorem integral_freeExponential (a c d : ℝ) (ha : 0 < a) (hc : 0 < c) (hd : 0 < d) :
    (∫ x in c..d, freeExponential a x) = freeLeftPrimitive a d - freeLeftPrimitive a c := by
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt
  · intro x hx
    exact hasDerivAt_freeLeftPrimitive a x ha ((lt_min hc hd).trans_le hx.1)
  · exact (continuous_freeExponential a).intervalIntegrable c d

/-- Exact integral of the weighted reciprocal free exponential between positive endpoints. -/
theorem integral_two_mul_div_freeExponential (a c d : ℝ)
    (ha : 0 < a) (hc : 0 < c) (hd : 0 < d) :
    (∫ x in c..d, 2 * x / freeExponential a x) =
      freeRightPrimitive a d - freeRightPrimitive a c := by
  have hpos : ∀ x ∈ Set.uIcc c d, 0 < x := fun _ hx => (lt_min hc hd).trans_le hx.1
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt
  · intro x hx
    exact hasDerivAt_freeRightPrimitive a x ha (hpos x hx)
  · apply ContinuousOn.intervalIntegrable
    exact (continuous_const.mul continuous_id).continuousOn.div
      (continuous_freeExponential a).continuousOn
      (fun x hx => (freeExponential_pos a x ha (hpos x hx)).ne')

end RicciFlowSharpEstimate.Variational
