/-
Copyright (c) 2026 Ziyang Qin. All rights reserved.
No license is granted by this file.
Authors: Ziyang Qin
-/
import RicciFlowSharpEstimate.Variational.ObstacleProfile
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic.Ring

/-!
# Exact derivative jumps at the obstacle contacts

The logarithmic free arc has positive derivative at both contacts. The actual
clamped profile has derivative zero on the outward half-lines, so it is not
differentiable at either contact for every cap strictly greater than one.
-/

open Set Filter
open scoped Topology

namespace RicciFlowSharpEstimate.Variational

/-- The logarithm of the actual free exponential has this derivative on the positive domain. -/
theorem hasDerivAt_log_freeExponential (a v : ℝ) (ha : 0 < a) (hv : 0 < v) :
    HasDerivAt (fun x => Real.log (freeExponential a x))
      (1 / (2 * v) + Real.sqrt (v / a) / a) v := by
  have hrootPos : 0 < Real.sqrt (v / a) := Real.sqrt_pos.2 (div_pos hv ha)
  have hroot : HasDerivAt (fun x : ℝ => Real.sqrt (x / a))
      (1 / a / (2 * Real.sqrt (v / a))) v := by
    simpa only [id_eq] using
      ((hasDerivAt_id v).div_const a).sqrt (ne_of_gt (div_pos hv ha))
  have hphase : HasDerivAt (fun x : ℝ => (2 / 3 : ℝ) * (Real.sqrt (x / a) ^ 3 - 1))
      (Real.sqrt (v / a) / a) v := by
    apply (((hroot.pow 3).sub_const 1).const_mul (2 / 3 : ℝ)).congr_deriv
    norm_num
    field_simp [ha.ne', hrootPos.ne']
  have hsquare : a * Real.sqrt (v / a) ^ 2 = v := by
    rw [Real.sq_sqrt (div_nonneg hv.le ha.le)]
    field_simp [ha.ne']
  have hhalf : (1 / a / (2 * Real.sqrt (v / a))) / Real.sqrt (v / a) =
      1 / (2 * v) := by
    field_simp [ha.ne', hv.ne', hrootPos.ne']
    nlinarith
  apply ((hroot.mul hphase.exp).log (freeExponential_pos a v ha hv).ne').congr_deriv
  calc
    (1 / a / (2 * Real.sqrt (v / a)) *
          Real.exp ((2 / 3 : ℝ) * (Real.sqrt (v / a) ^ 3 - 1)) +
        Real.sqrt (v / a) *
          (Real.exp ((2 / 3 : ℝ) * (Real.sqrt (v / a) ^ 3 - 1)) *
            (Real.sqrt (v / a) / a))) /
        (Real.sqrt (v / a) * Real.exp ((2 / 3 : ℝ) * (Real.sqrt (v / a) ^ 3 - 1))) =
        (1 / a / (2 * Real.sqrt (v / a))) / Real.sqrt (v / a) +
          Real.sqrt (v / a) / a := by
      field_simp [ha.ne', hrootPos.ne', Real.exp_ne_zero]
    _ = 1 / (2 * v) + Real.sqrt (v / a) / a := by rw [hhalf]

/-- The actual profile has zero derivative to the left of its lower contact. -/
theorem hasDerivWithinAt_obstacleLogProfile_lowerContact_Iic (C : ℝ) :
    HasDerivWithinAt (obstacleLogProfile C) 0
      (Iic (lowerContact (capParameter C))) (lowerContact (capParameter C)) := by
  apply (hasDerivWithinAt_const (x := lowerContact (capParameter C))
    (s := Iic (lowerContact (capParameter C))) (c := (0 : ℝ))).congr_of_mem
  · intro v hv
    exact obstacleLogProfile_eq_low C v hv
  · exact self_mem_Iic

/-- At every nondegenerate cap the free side of the lower contact has derivative `3/(2a)`. -/
theorem hasDerivWithinAt_obstacleLogProfile_lowerContact_Ici (C : ℝ) (hC : 1 < C) :
    HasDerivWithinAt (obstacleLogProfile C) (3 / (2 * lowerContact (capParameter C)))
      (Ici (lowerContact (capParameter C))) (lowerContact (capParameter C)) := by
  let q := capParameter C
  let a := lowerContact q
  let b := upperContact q
  have hq : 0 < q := lt_trans zero_lt_one (one_lt_capParameter C hC)
  have ha : 0 < a := lowerContact_pos q hq
  have hab : a < b := lowerContact_lt_upperContact q (one_lt_capParameter C hC)
  have hfree : HasDerivAt (fun v => Real.log (freeExponential a v)) (3 / (2 * a)) a := by
    apply (hasDerivAt_log_freeExponential a a ha ha).congr_deriv
    rw [div_self ha.ne', Real.sqrt_one]
    ring
  have heq : obstacleLogProfile C =ᶠ[𝓝[Ici a] a]
      (fun v => Real.log (freeExponential a v)) := by
    filter_upwards [self_mem_nhdsWithin,
      (gt_mem_nhds hab).filter_mono nhdsWithin_le_nhds] with v hv hvb
    exact congrArg Real.log (obstacleExponential_eq_free q v hv hvb.le)
  exact hfree.hasDerivWithinAt.congr_of_eventuallyEq_of_mem heq self_mem_Ici

/-- The free side of the upper contact has derivative `1/(2b)+q/a` at nondegenerate caps. -/
theorem hasDerivWithinAt_obstacleLogProfile_upperContact_Iic (C : ℝ) (hC : 1 < C) :
    HasDerivWithinAt (obstacleLogProfile C)
      (1 / (2 * upperContact (capParameter C)) + capParameter C / lowerContact (capParameter C))
      (Iic (upperContact (capParameter C))) (upperContact (capParameter C)) := by
  let q := capParameter C
  let a := lowerContact q
  let b := upperContact q
  have hq : 0 < q := lt_trans zero_lt_one (one_lt_capParameter C hC)
  have ha : 0 < a := lowerContact_pos q hq
  have hb : 0 < b := upperContact_pos q hq
  have hab : a < b := lowerContact_lt_upperContact q (one_lt_capParameter C hC)
  have hsqrt : Real.sqrt (b / a) = q := by
    change Real.sqrt ((a * q ^ 2) / a) = q
    rw [mul_div_cancel_left₀ (q ^ 2) ha.ne', Real.sqrt_sq_eq_abs, abs_of_pos hq]
  have hfree : HasDerivAt (fun v => Real.log (freeExponential a v))
      (1 / (2 * b) + q / a) b := by
    simpa only [hsqrt] using hasDerivAt_log_freeExponential a b ha hb
  have heq : obstacleLogProfile C =ᶠ[𝓝[Iic b] b]
      (fun v => Real.log (freeExponential a v)) := by
    filter_upwards [self_mem_nhdsWithin,
      (lt_mem_nhds hab).filter_mono nhdsWithin_le_nhds] with v hv hva
    exact congrArg Real.log (obstacleExponential_eq_free q v hva.le hv)
  exact hfree.hasDerivWithinAt.congr_of_eventuallyEq_of_mem heq self_mem_Iic

/-- The actual profile has zero derivative to the right of its upper contact. -/
theorem hasDerivWithinAt_obstacleLogProfile_upperContact_Ici (C : ℝ) :
    HasDerivWithinAt (obstacleLogProfile C) 0
      (Ici (upperContact (capParameter C))) (upperContact (capParameter C)) := by
  apply (hasDerivWithinAt_const (x := upperContact (capParameter C))
    (s := Ici (upperContact (capParameter C))) (c := logCap (capParameter C))).congr_of_mem
  · intro v hv
    rw [obstacleLogProfile, obstacleExponential_eq_high _ v (one_le_capParameter C) hv,
      Real.log_exp]
  · exact self_mem_Ici

private theorem not_differentiableAt_of_halfline_derivatives {f : ℝ → ℝ} {x l r : ℝ}
    (hl : HasDerivWithinAt f l (Iic x) x) (hr : HasDerivWithinAt f r (Ici x) x)
    (hne : l ≠ r) : ¬ DifferentiableAt ℝ f x := by
  intro hf
  have hl' : l = deriv f x := (uniqueDiffWithinAt_Iic x).eq_deriv _
    hl hf.hasDerivAt.hasDerivWithinAt
  have hr' : r = deriv f x := (uniqueDiffWithinAt_Ici x).eq_deriv _
    hr hf.hasDerivAt.hasDerivWithinAt
  exact hne (hl'.trans hr'.symm)

/-- Above cap one, the actual candidate is not differentiable at the lower contact. -/
theorem not_differentiableAt_obstacleLogProfile_lowerContact (C : ℝ) (hC : 1 < C) :
    ¬ DifferentiableAt ℝ (obstacleLogProfile C) (lowerContact (capParameter C)) := by
  apply not_differentiableAt_of_halfline_derivatives
    (hasDerivWithinAt_obstacleLogProfile_lowerContact_Iic C)
    (hasDerivWithinAt_obstacleLogProfile_lowerContact_Ici C hC)
  have ha := lowerContact_pos (capParameter C)
    (lt_trans zero_lt_one (one_lt_capParameter C hC))
  exact (div_pos (by norm_num) (mul_pos (by norm_num) ha)).ne

/-- Above cap one, the actual candidate is not differentiable at the upper contact. -/
theorem not_differentiableAt_obstacleLogProfile_upperContact (C : ℝ) (hC : 1 < C) :
    ¬ DifferentiableAt ℝ (obstacleLogProfile C) (upperContact (capParameter C)) := by
  apply not_differentiableAt_of_halfline_derivatives
    (hasDerivWithinAt_obstacleLogProfile_upperContact_Iic C hC)
    (hasDerivWithinAt_obstacleLogProfile_upperContact_Ici C)
  have hq : 0 < capParameter C := lt_trans zero_lt_one (one_lt_capParameter C hC)
  have ha := lowerContact_pos (capParameter C) hq
  have hb := upperContact_pos (capParameter C) hq
  exact (add_pos (div_pos (by norm_num) (mul_pos (by norm_num) hb))
    (div_pos hq ha)).ne'

end RicciFlowSharpEstimate.Variational
