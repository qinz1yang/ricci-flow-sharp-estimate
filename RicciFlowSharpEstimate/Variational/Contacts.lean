/-
Copyright (c) 2026 Ziyang Qin. All rights reserved.
No license is granted by this file.
Authors: Ziyang Qin
-/
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

/-!
# Contact points for the constrained exponential pair problem

The parameter `q ≥ 1` determines the lower and upper obstacle contacts.
The contacts coincide at `q = 1` and are distinct for every `q > 1`.
-/

namespace RicciFlowSharpEstimate.Variational

/-- The lower obstacle contact associated with the parameter `q`. -/
noncomputable def lowerContact (q : ℝ) : ℝ := 1 / Real.sqrt (q ^ 4 + 2 * q)

/-- The upper obstacle contact associated with the parameter `q`. -/
noncomputable def upperContact (q : ℝ) : ℝ := lowerContact q * q ^ 2

private theorem contactDenominator_pos (q : ℝ) (hq : 0 < q) :
    0 < q ^ 4 + 2 * q := by
  positivity

/-- The lower contact is positive for every positive parameter. -/
theorem lowerContact_pos (q : ℝ) (hq : 0 < q) : 0 < lowerContact q := by
  unfold lowerContact
  exact one_div_pos.mpr (Real.sqrt_pos.2 (contactDenominator_pos q hq))

/-- The upper contact is positive for every positive parameter. -/
theorem upperContact_pos (q : ℝ) (hq : 0 < q) : 0 < upperContact q := by
  unfold upperContact
  exact mul_pos (lowerContact_pos q hq) (sq_pos_of_pos hq)

/-- The squared lower contact has a rational expression in the parameter. -/
theorem lowerContact_sq_eq (q : ℝ) (hq : 0 < q) :
    lowerContact q ^ 2 = 1 / (q ^ 4 + 2 * q) := by
  unfold lowerContact
  rw [div_pow, one_pow, Real.sq_sqrt (contactDenominator_pos q hq).le]

private theorem lowerContact_sq_mul (q : ℝ) (hq : 0 < q) :
    lowerContact q ^ 2 * (q ^ 4 + 2 * q) = 1 := by
  rw [lowerContact_sq_eq q hq]
  exact one_div_mul_cancel (ne_of_gt (contactDenominator_pos q hq))

/-- The squared upper contact has a rational expression in the parameter. -/
theorem upperContact_sq_eq (q : ℝ) (hq : 0 < q) :
    upperContact q ^ 2 = q ^ 3 / (q ^ 3 + 2) := by
  have hden : q ^ 4 + 2 * q ≠ 0 := ne_of_gt (contactDenominator_pos q hq)
  have hden' : q ^ 3 + 2 ≠ 0 := ne_of_gt (by positivity : 0 < q ^ 3 + 2)
  unfold upperContact
  rw [mul_pow, lowerContact_sq_eq q hq]
  field_simp [hden, hden']

/-- The two contacts satisfy the complementary-square normalization. -/
theorem one_sub_upperContact_sq (q : ℝ) (hq : 0 < q) :
    1 - upperContact q ^ 2 = 2 * lowerContact q ^ 2 * q := by
  have hnorm := lowerContact_sq_mul q hq
  unfold upperContact
  nlinarith

/-- The upper contact remains strictly inside the interval for positive parameters. -/
theorem upperContact_lt_one (q : ℝ) (hq : 0 < q) : upperContact q < 1 := by
  have hpos := lowerContact_pos q hq
  have hgap : 0 < 2 * lowerContact q ^ 2 * q := by positivity
  have hid := one_sub_upperContact_sq q hq
  nlinarith [sq_nonneg (upperContact q - 1)]

/-- Parameters at least one put the lower contact before the upper contact. -/
theorem lowerContact_le_upperContact (q : ℝ) (hq : 1 ≤ q) :
    lowerContact q ≤ upperContact q := by
  have hsq : (1 : ℝ) ≤ q ^ 2 := by nlinarith [sq_nonneg (q - 1)]
  have hpos := lowerContact_pos q (lt_of_lt_of_le zero_lt_one hq)
  simpa [upperContact] using mul_le_mul_of_nonneg_left hsq hpos.le

/-- The free arc has positive length for every nondegenerate parameter. -/
theorem lowerContact_lt_upperContact (q : ℝ) (hq : 1 < q) :
    lowerContact q < upperContact q := by
  have hsq : (1 : ℝ) < q ^ 2 := by nlinarith [sq_nonneg (q - 1)]
  have hpos := lowerContact_pos q (lt_trans zero_lt_one hq)
  simpa [upperContact] using mul_lt_mul_of_pos_left hsq hpos

/-- The two contacts coincide precisely at the degenerate parameter. -/
theorem lowerContact_eq_upperContact_iff (q : ℝ) (hq : 1 ≤ q) :
    lowerContact q = upperContact q ↔ q = 1 := by
  constructor
  · intro heq
    by_contra hqne
    have hlt : 1 < q := lt_of_le_of_ne hq (Ne.symm hqne)
    exact (ne_of_lt (lowerContact_lt_upperContact q hlt)) heq
  · rintro rfl
    simp [upperContact]

/-- The contact locations lie in the stated order inside the unit interval. -/
theorem contact_bounds (q : ℝ) (hq : 1 ≤ q) :
    0 < lowerContact q ∧ lowerContact q ≤ upperContact q ∧ upperContact q < 1 := by
  have hpos : 0 < q := lt_of_lt_of_le zero_lt_one hq
  exact ⟨lowerContact_pos q hpos, lowerContact_le_upperContact q hq,
    upperContact_lt_one q hpos⟩

/-- An equivalent contact normalization used in the free-arc moment formulas. -/
theorem lowerContact_div_parameter (q : ℝ) (hq : 0 < q) :
    lowerContact q / q = (1 - upperContact q ^ 2) / (2 * upperContact q) := by
  rw [one_sub_upperContact_sq q hq]
  unfold upperContact
  have hqne := ne_of_gt hq
  have hane := ne_of_gt (lowerContact_pos q hq)
  field_simp [hqne, hane]

@[simp] theorem lowerContact_one : lowerContact 1 = 1 / Real.sqrt 3 := by
  norm_num [lowerContact]

@[simp] theorem upperContact_one : upperContact 1 = 1 / Real.sqrt 3 := by
  simp [upperContact]

end RicciFlowSharpEstimate.Variational
