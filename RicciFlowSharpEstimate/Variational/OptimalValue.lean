/-
Copyright (c) 2026 Ziyang Qin. All rights reserved.
No license is granted by this file.
Authors: Ziyang Qin
-/
import RicciFlowSharpEstimate.Variational.ObstaclePrimitives
import RicciFlowSharpEstimate.Variational.PairIteration
import Mathlib.Tactic.Ring

/-!
# Exact value of the obstacle candidate

The actual triangular pair functional is evaluated at the canonical logarithmic
candidate. Its backward integral splits at the two contacts into polynomial,
square-root, and polynomial contributions. The computation includes the
coincident contacts and constant candidate at cap one.
-/

namespace RicciFlowSharpEstimate.Variational

private theorem integral_two_mul_shift (a b d : ℝ) :
    (∫ x in a..b, 2 * x * (x - d)) =
      (2 / 3 : ℝ) * (b ^ 3 - a ^ 3) - d * (b ^ 2 - a ^ 2) := by
  calc
    (∫ x in a..b, 2 * x * (x - d)) =
        ((2 / 3 : ℝ) * b ^ 3 - d * b ^ 2) -
          ((2 / 3 : ℝ) * a ^ 3 - d * a ^ 2) := by
      apply intervalIntegral.integral_eq_sub_of_hasDerivAt
      · intro x _
        convert! (((hasDerivAt_id x).pow 3).const_mul (2 / 3 : ℝ)).sub
          (((hasDerivAt_id x).pow 2).const_mul d) using 1
        norm_num
        ring
      · exact (by fun_prop : Continuous (fun x : ℝ => 2 * x * (x - d))).intervalIntegrable a b
    _ = _ := by ring

private theorem integral_scaled_sqrt (a c d : ℝ) (ha : 0 < a)
    (hc : 0 < c) (hd : 0 < d) :
    (∫ v in c..d, 2 * a ^ 2 * Real.sqrt (v / a)) =
      (4 / 3 : ℝ) * a ^ 3 * (Real.sqrt (d / a) ^ 3 - Real.sqrt (c / a) ^ 3) := by
  have hderiv (v : ℝ) (hv : 0 < v) :
      HasDerivAt (fun x : ℝ => (4 / 3 : ℝ) * a ^ 3 * Real.sqrt (x / a) ^ 3)
        (2 * a ^ 2 * Real.sqrt (v / a)) v := by
    have hr : HasDerivAt (fun x : ℝ => Real.sqrt (x / a))
        (1 / a / (2 * Real.sqrt (v / a))) v := by
      simpa only [id_eq] using
        ((hasDerivAt_id v).div_const a).sqrt (ne_of_gt (div_pos hv ha))
    apply ((hr.pow 3).const_mul ((4 / 3 : ℝ) * a ^ 3)).congr_deriv
    have hroot : 0 < Real.sqrt (v / a) := Real.sqrt_pos.2 (div_pos hv ha)
    norm_num
    field_simp [ha.ne', hroot.ne']
    ring
  calc
    (∫ v in c..d, 2 * a ^ 2 * Real.sqrt (v / a)) =
        (4 / 3 : ℝ) * a ^ 3 * Real.sqrt (d / a) ^ 3 -
          (4 / 3 : ℝ) * a ^ 3 * Real.sqrt (c / a) ^ 3 := by
      apply intervalIntegral.integral_eq_sub_of_hasDerivAt
      · intro v hv
        exact hderiv v ((lt_min hc hd).trans_le hv.1)
      · exact (by fun_prop : Continuous (fun v : ℝ =>
          2 * a ^ 2 * Real.sqrt (v / a))).intervalIntegrable c d
    _ = _ := by ring

private theorem free_backward_integrand (a v : ℝ) (ha : 0 < a) (hv : 0 < v) :
    (2 * v / freeExponential a v) * freeLeftPrimitive a v =
      2 * a ^ 2 * Real.sqrt (v / a) := by
  have hroot : 0 < Real.sqrt (v / a) := Real.sqrt_pos.2 (div_pos hv ha)
  have hexp : Real.exp ((2 / 3 : ℝ) * (Real.sqrt (v / a) ^ 3 - 1)) ≠ 0 :=
    (Real.exp_pos _).ne'
  have hvroot : v = a * Real.sqrt (v / a) ^ 2 := by
    rw [Real.sq_sqrt (div_nonneg hv.le ha.le)]
    field_simp [ha.ne']
  have hdiv : v / Real.sqrt (v / a) = a * Real.sqrt (v / a) := by
    apply (div_eq_iff hroot.ne').2
    calc
      v = a * Real.sqrt (v / a) ^ 2 := hvroot
      _ = a * Real.sqrt (v / a) * Real.sqrt (v / a) := by ring
  calc
    (2 * v / freeExponential a v) * freeLeftPrimitive a v =
        2 * a * (v / Real.sqrt (v / a)) := by
      dsimp [freeExponential, freeLeftPrimitive]
      field_simp [hroot.ne', hexp]
    _ = 2 * a ^ 2 * Real.sqrt (v / a) := by rw [hdiv]; ring

private theorem candidate_value_contact_algebra (q : ℝ) (hq : 0 < q) :
    (2 / 3 : ℝ) * lowerContact q ^ 3 +
        (4 / 3 : ℝ) * lowerContact q ^ 3 * (q ^ 3 - 1) +
        (2 / 3 : ℝ) * (1 - upperContact q ^ 3) -
        (upperContact q - lowerContact q / q) * (1 - upperContact q ^ 2) =
      (2 / 3 : ℝ) - upperContact q + 1 / (3 * upperContact q) := by
  have hb := upperContact_pos q hq
  have hc : 2 * lowerContact q ^ 3 =
      (lowerContact q / q) * (1 - upperContact q ^ 2) := by
    rw [one_sub_upperContact_sq q hq]
    field_simp [hq.ne']
  have hf : lowerContact q ^ 3 * q ^ 3 =
      (lowerContact q / q) * upperContact q ^ 2 := by
    rw [upperContact]
    field_simp [hq.ne']
  calc
    _ = (2 / 3 : ℝ) - upperContact q +
        (upperContact q ^ 3 +
          2 * (lowerContact q / q) * (1 + upperContact q ^ 2)) / 3 := by
      nlinarith only [hc, hf]
    _ = _ := by
      rw [lowerContact_div_parameter q hq]
      field_simp [hb.ne']
      ring

private theorem integral_obstacle_backward (q : ℝ) (hq : 1 ≤ q) :
    (∫ v in 0..1, (2 * v / obstacleExponential q v) * obstaclePrefix q v) =
      (2 / 3 : ℝ) - upperContact q + 1 / (3 * upperContact q) := by
  have hqpos : 0 < q := lt_of_lt_of_le zero_lt_one hq
  have ha := lowerContact_pos q hqpos
  have hb := upperContact_pos q hqpos
  have hab := lowerContact_le_upperContact q hq
  have hb1 := upperContact_lt_one q hqpos
  let F : ℝ → ℝ := fun v => (2 * v / obstacleExponential q v) * obstaclePrefix q v
  have hp : Continuous (obstaclePrefix q) := by
    apply continuous_iff_continuousAt.2
    intro v
    exact ((continuous_obstacleExponential q).integral_hasStrictDerivAt 0 v).hasDerivAt.continuousAt
  have hF : Continuous F :=
    ((continuous_const.mul continuous_id).div (continuous_obstacleExponential q)
      (fun v => (obstacleExponential_pos q v hq).ne')).mul hp
  have hlow : (∫ v in 0..lowerContact q, F v) = (2 / 3 : ℝ) * lowerContact q ^ 3 := by
    calc
      (∫ v in 0..lowerContact q, F v) =
          ∫ v in 0..lowerContact q, 2 * v * (v - 0) := by
        apply intervalIntegral.integral_congr
        intro v hv
        rw [Set.uIcc_of_le ha.le] at hv
        dsimp [F]
        rw [obstacleExponential_eq_low q v hq hv.2, obstaclePrefix_eq_low q v hq hv.2]
        ring
      _ = _ := by rw [integral_two_mul_shift]; norm_num
  have hfree : (∫ v in lowerContact q..upperContact q, F v) =
      (4 / 3 : ℝ) * lowerContact q ^ 3 * (q ^ 3 - 1) := by
    have hsqrt : Real.sqrt (upperContact q / lowerContact q) = q := by
      rw [upperContact, mul_div_cancel_left₀ (q ^ 2) ha.ne']
      exact (Real.sqrt_sq_eq_abs q).trans (abs_of_nonneg hqpos.le)
    calc
      (∫ v in lowerContact q..upperContact q, F v) =
          ∫ v in lowerContact q..upperContact q,
            2 * lowerContact q ^ 2 * Real.sqrt (v / lowerContact q) := by
        apply intervalIntegral.integral_congr
        intro v hv
        rw [Set.uIcc_of_le hab] at hv
        dsimp [F]
        rw [obstacleExponential_eq_free q v hv.1 hv.2,
          obstaclePrefix_eq_free q v hq hv.1 hv.2]
        exact free_backward_integrand _ v ha (ha.trans_le hv.1)
      _ = _ := by
        rw [integral_scaled_sqrt _ _ _ ha ha hb, hsqrt]
        simp [div_self ha.ne']
  have hhigh : (∫ v in upperContact q..1, F v) =
      (2 / 3 : ℝ) * (1 - upperContact q ^ 3) -
        (upperContact q - lowerContact q / q) * (1 - upperContact q ^ 2) := by
    calc
      (∫ v in upperContact q..1, F v) =
          ∫ v in upperContact q..1, 2 * v * (v - (upperContact q - lowerContact q / q)) := by
        apply intervalIntegral.integral_congr
        intro v hv
        rw [Set.uIcc_of_le hb1.le] at hv
        dsimp [F]
        rw [obstacleExponential_eq_high q v hq hv.1, obstaclePrefix_eq_high q v hq hv.1]
        field_simp [(Real.exp_pos (logCap q)).ne']
        ring
      _ = _ := by rw [integral_two_mul_shift]; norm_num
  calc
    (∫ v in 0..1, (2 * v / obstacleExponential q v) * obstaclePrefix q v) =
        ((∫ v in 0..lowerContact q, F v) + (∫ v in lowerContact q..upperContact q, F v)) +
          (∫ v in upperContact q..1, F v) := by
      rw [intervalIntegral.integral_add_adjacent_intervals
        (hF.intervalIntegrable 0 (lowerContact q))
        (hF.intervalIntegrable (lowerContact q) (upperContact q)),
        intervalIntegral.integral_add_adjacent_intervals
          (hF.intervalIntegrable 0 (upperContact q))
          (hF.intervalIntegrable (upperContact q) 1)]
    _ = _ := by
      rw [hlow, hfree, hhigh]
      simpa only [add_sub_assoc] using candidate_value_contact_algebra q hqpos

/-- The canonical obstacle candidate has the explicit value at every admissible cap. -/
theorem pairFunctional_obstacleLogProfile_eq (C : ℝ) (hC : 1 ≤ C) :
    pairFunctional (obstacleLogProfile C) =
      (2 / 3 : ℝ) - upperContact (capParameter C) +
        1 / (3 * upperContact (capParameter C)) := by
  rw [pairFunctional_eq_intervalIntegral (obstacleLogProfile C)
    (continuous_obstacleLogProfile C).continuousOn]
  simp_rw [exp_obstacleLogProfile]
  exact integral_obstacle_backward (capParameter C) (capParameter_spec C hC).1

/-- At cap one the actual constant candidate has pair value `2/3`. -/
@[simp] theorem pairFunctional_obstacleLogProfile_one :
    pairFunctional (obstacleLogProfile 1) = (2 / 3 : ℝ) := by
  calc
    pairFunctional (obstacleLogProfile 1) = ∫ v in (0 : ℝ)..1, 2 * v * (v - 0) := by
      rw [pairFunctional_eq_intervalIntegral (obstacleLogProfile 1)
        (continuous_obstacleLogProfile 1).continuousOn]
      apply intervalIntegral.integral_congr
      intro v _
      simp
    _ = (2 / 3 : ℝ) := by rw [integral_two_mul_shift]; norm_num

end RicciFlowSharpEstimate.Variational
