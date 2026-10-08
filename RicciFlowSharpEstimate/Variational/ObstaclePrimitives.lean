/-
Copyright (c) 2026 Ziyang Qin. All rights reserved.
No license is granted by this file.
Authors: Ziyang Qin
-/
import RicciFlowSharpEstimate.Variational.ObstacleProfile

/-!
# Actual primitives of the joined obstacle profile

The prefix integral of the profile and the tail integral of its weighted
reciprocal have exact lower/free/upper formulas. The proof splits the actual
interval integrals at the contact points and matches the free-arc primitives.
All statements include the coincident contacts at `q = 1`.
-/

namespace RicciFlowSharpEstimate.Variational

/-- The actual prefix integral of the joined exponential candidate. -/
noncomputable def obstaclePrefix (q v : ℝ) : ℝ :=
  ∫ x in 0..v, obstacleExponential q x

/-- The actual weighted reciprocal tail of the joined exponential candidate. -/
noncomputable def obstacleTail (q v : ℝ) : ℝ :=
  ∫ x in v..1, 2 * x / obstacleExponential q x

private theorem continuous_weightedReciprocal (q : ℝ) (hq : 1 ≤ q) :
    Continuous (fun x : ℝ => 2 * x / obstacleExponential q x) :=
  (continuous_const.mul continuous_id).div (continuous_obstacleExponential q)
    (fun x => (obstacleExponential_pos q x hq).ne')

private theorem integral_two_mul_div_const (a b c : ℝ) :
    (∫ x in a..b, 2 * x / c) = (b ^ 2 - a ^ 2) / c := by
  calc
    (∫ x in a..b, 2 * x / c) = b ^ 2 / c - a ^ 2 / c := by
      apply intervalIntegral.integral_eq_sub_of_hasDerivAt
      · intro x _
        simpa using ((hasDerivAt_id x).pow 2).div_const c
      · exact ((continuous_const.mul continuous_id).div_const c).intervalIntegrable a b
    _ = (b ^ 2 - a ^ 2) / c := (sub_div _ _ _).symm

private theorem freeLeftPrimitive_at_upperContact (q : ℝ) (hq : 0 < q) :
    freeLeftPrimitive (lowerContact q) (upperContact q) =
      Real.exp (logCap q) * (lowerContact q / q) := by
  rw [upperContact, freeLeftPrimitive_mul_sq _ q hq.le, exp_logCap q hq]
  field_simp [hq.ne']

private theorem freeRightPrimitive_at_upperContact (q : ℝ) (hq : 0 < q) :
    freeRightPrimitive (lowerContact q) (upperContact q) =
      -((1 - upperContact q ^ 2) / Real.exp (logCap q)) := by
  rw [one_sub_upperContact_sq q hq, upperContact,
    freeRightPrimitive_mul_sq _ q hq.le, exp_logCap q hq, Real.exp_neg]
  field_simp [hq.ne']

/-- The prefix integral equals the coordinate on the lower obstacle. -/
theorem obstaclePrefix_eq_low (q v : ℝ) (hq : 1 ≤ q) (hv : v ≤ lowerContact q) :
    obstaclePrefix q v = v := by
  have ha := lowerContact_pos q (lt_of_lt_of_le zero_lt_one hq)
  calc
    obstaclePrefix q v = ∫ x in 0..v, (1 : ℝ) := by
      apply intervalIntegral.integral_congr
      intro x hx
      exact obstacleExponential_eq_low q x hq (hx.2.trans (max_le ha.le hv))
    _ = v := by simp

/-- Between the contacts the actual prefix is the free-arc left primitive. -/
theorem obstaclePrefix_eq_free (q v : ℝ) (hq : 1 ≤ q)
    (hl : lowerContact q ≤ v) (hu : v ≤ upperContact q) :
    obstaclePrefix q v = freeLeftPrimitive (lowerContact q) v := by
  have ha := lowerContact_pos q (lt_of_lt_of_le zero_lt_one hq)
  have hvpos : 0 < v := ha.trans_le hl
  have hfree : (∫ x in lowerContact q..v, obstacleExponential q x) =
      freeLeftPrimitive (lowerContact q) v -
        freeLeftPrimitive (lowerContact q) (lowerContact q) := by
    calc
      (∫ x in lowerContact q..v, obstacleExponential q x) =
          ∫ x in lowerContact q..v, freeExponential (lowerContact q) x := by
        apply intervalIntegral.integral_congr
        intro x hx
        rw [Set.uIcc_of_le hl] at hx
        exact obstacleExponential_eq_free q x hx.1 (hx.2.trans hu)
      _ = _ := integral_freeExponential _ _ _ ha ha hvpos
  calc
    obstaclePrefix q v = obstaclePrefix q (lowerContact q) +
        ∫ x in lowerContact q..v, obstacleExponential q x := by
      exact (intervalIntegral.integral_add_adjacent_intervals
        ((continuous_obstacleExponential q).intervalIntegrable 0 (lowerContact q))
        ((continuous_obstacleExponential q).intervalIntegrable (lowerContact q) v)).symm
    _ = lowerContact q + (freeLeftPrimitive (lowerContact q) v -
        freeLeftPrimitive (lowerContact q) (lowerContact q)) := by
      rw [obstaclePrefix_eq_low q (lowerContact q) hq le_rfl, hfree]
    _ = freeLeftPrimitive (lowerContact q) v := by
      rw [freeLeftPrimitive_self]
      ring

/-- On the upper obstacle the prefix continues by the exact affine formula. -/
theorem obstaclePrefix_eq_high (q v : ℝ) (hq : 1 ≤ q) (hv : upperContact q ≤ v) :
    obstaclePrefix q v =
      Real.exp (logCap q) * (v - upperContact q + lowerContact q / q) := by
  have hqpos : 0 < q := lt_of_lt_of_le zero_lt_one hq
  have hhigh : (∫ x in upperContact q..v, obstacleExponential q x) =
      (v - upperContact q) * Real.exp (logCap q) := by
    calc
      (∫ x in upperContact q..v, obstacleExponential q x) =
          ∫ x in upperContact q..v, Real.exp (logCap q) := by
        apply intervalIntegral.integral_congr
        intro x hx
        rw [Set.uIcc_of_le hv] at hx
        exact obstacleExponential_eq_high q x hq hx.1
      _ = _ := by simp
  calc
    obstaclePrefix q v = obstaclePrefix q (upperContact q) +
        ∫ x in upperContact q..v, obstacleExponential q x := by
      exact (intervalIntegral.integral_add_adjacent_intervals
        ((continuous_obstacleExponential q).intervalIntegrable 0 (upperContact q))
        ((continuous_obstacleExponential q).intervalIntegrable (upperContact q) v)).symm
    _ = freeLeftPrimitive (lowerContact q) (upperContact q) +
        (v - upperContact q) * Real.exp (logCap q) := by
      rw [obstaclePrefix_eq_free q (upperContact q) hq
        (lowerContact_le_upperContact q hq) le_rfl, hhigh]
    _ = Real.exp (logCap q) * (v - upperContact q + lowerContact q / q) := by
      rw [freeLeftPrimitive_at_upperContact q hqpos]
      ring

/-- The upper-obstacle tail formula holds on the full upper half-line. -/
theorem obstacleTail_eq_high (q v : ℝ) (hq : 1 ≤ q) (hv : upperContact q ≤ v) :
    obstacleTail q v = (1 - v ^ 2) / Real.exp (logCap q) := by
  have hb := upperContact_lt_one q (lt_of_lt_of_le zero_lt_one hq)
  calc
    obstacleTail q v = ∫ x in v..1, 2 * x / Real.exp (logCap q) := by
      apply intervalIntegral.integral_congr
      intro x hx
      dsimp only
      rw [obstacleExponential_eq_high q x hq ((le_min hv hb.le).trans hx.1)]
    _ = (1 - v ^ 2) / Real.exp (logCap q) := by
      simpa using integral_two_mul_div_const v 1 (Real.exp (logCap q))

/-- Between the contacts the actual tail is minus the free-arc right primitive. -/
theorem obstacleTail_eq_free (q v : ℝ) (hq : 1 ≤ q)
    (hl : lowerContact q ≤ v) (hu : v ≤ upperContact q) :
    obstacleTail q v = -freeRightPrimitive (lowerContact q) v := by
  have hqpos : 0 < q := lt_of_lt_of_le zero_lt_one hq
  have ha := lowerContact_pos q hqpos
  have hb := upperContact_pos q hqpos
  have hvpos : 0 < v := ha.trans_le hl
  have hfree : (∫ x in v..upperContact q, 2 * x / obstacleExponential q x) =
      freeRightPrimitive (lowerContact q) (upperContact q) -
        freeRightPrimitive (lowerContact q) v := by
    calc
      (∫ x in v..upperContact q, 2 * x / obstacleExponential q x) =
          ∫ x in v..upperContact q, 2 * x / freeExponential (lowerContact q) x := by
        apply intervalIntegral.integral_congr
        intro x hx
        rw [Set.uIcc_of_le hu] at hx
        dsimp only
        rw [obstacleExponential_eq_free q x (hl.trans hx.1) hx.2]
      _ = _ := integral_two_mul_div_freeExponential _ _ _ ha hvpos hb
  calc
    obstacleTail q v =
        (∫ x in v..upperContact q, 2 * x / obstacleExponential q x) +
          obstacleTail q (upperContact q) := by
      exact (intervalIntegral.integral_add_adjacent_intervals
        ((continuous_weightedReciprocal q hq).intervalIntegrable v (upperContact q))
        ((continuous_weightedReciprocal q hq).intervalIntegrable (upperContact q) 1)).symm
    _ = (freeRightPrimitive (lowerContact q) (upperContact q) -
        freeRightPrimitive (lowerContact q) v) +
          (1 - upperContact q ^ 2) / Real.exp (logCap q) := by
      rw [hfree, obstacleTail_eq_high q (upperContact q) hq le_rfl]
    _ = -freeRightPrimitive (lowerContact q) v := by
      rw [freeRightPrimitive_at_upperContact q hqpos]
      ring

/-- On the lower obstacle the actual tail has the exact quadratic formula. -/
theorem obstacleTail_eq_low (q v : ℝ) (hq : 1 ≤ q) (hv : v ≤ lowerContact q) :
    obstacleTail q v = 3 * lowerContact q ^ 2 - v ^ 2 := by
  have hlow : (∫ x in v..lowerContact q, 2 * x / obstacleExponential q x) =
      lowerContact q ^ 2 - v ^ 2 := by
    calc
      (∫ x in v..lowerContact q, 2 * x / obstacleExponential q x) =
          ∫ x in v..lowerContact q, 2 * x / (1 : ℝ) := by
        apply intervalIntegral.integral_congr
        intro x hx
        rw [Set.uIcc_of_le hv] at hx
        dsimp only
        rw [obstacleExponential_eq_low q x hq hx.2]
      _ = _ := by simpa using integral_two_mul_div_const v (lowerContact q) 1
  calc
    obstacleTail q v =
        (∫ x in v..lowerContact q, 2 * x / obstacleExponential q x) +
          obstacleTail q (lowerContact q) := by
      exact (intervalIntegral.integral_add_adjacent_intervals
        ((continuous_weightedReciprocal q hq).intervalIntegrable v (lowerContact q))
        ((continuous_weightedReciprocal q hq).intervalIntegrable (lowerContact q) 1)).symm
    _ = (lowerContact q ^ 2 - v ^ 2) -
        freeRightPrimitive (lowerContact q) (lowerContact q) := by
      rw [hlow, obstacleTail_eq_free q (lowerContact q) hq le_rfl
        (lowerContact_le_upperContact q hq)]
      ring
    _ = 3 * lowerContact q ^ 2 - v ^ 2 := by
      rw [freeRightPrimitive_self]
      ring

end RicciFlowSharpEstimate.Variational
