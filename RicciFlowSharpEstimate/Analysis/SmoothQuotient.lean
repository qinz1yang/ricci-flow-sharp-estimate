/-
Copyright (c) 2026 Ziyang Qin. All rights reserved.
No license is granted by this file.
Authors: Ziyang Qin
-/
import Mathlib.Analysis.SpecialFunctions.SmoothTransition

/-!
# Smooth quotients on a closed interval

A coefficient need only be nonzero on the physical interval. A smooth positive
correction outside that interval allows its quotient to extend to the whole line.
The denominator construction adapts Ziyang Qin's historical
`RotationalInvariantOneFormClassification.lean` to arbitrary closed intervals.
-/

namespace RicciFlowSharpEstimate.Analysis

open Set
open scoped ContDiff

/-- Division by a smooth coefficient nonzero on a closed interval has a globally
smooth extension, retaining its multiplication law on that interval. -/
theorem exists_contDiff_mul_eq_on_Icc (a b : ℝ) (hab : a ≤ b) (c p : ℝ → ℝ)
    (hc : ContDiff ℝ ∞ c) (hp : ContDiff ℝ ∞ p)
    (hne : ∀ x ∈ Icc a b, c x ≠ 0) :
    ∃ r : ℝ → ℝ, ContDiff ℝ ∞ r ∧ ∀ x ∈ Icc a b, c x * r x = p x := by
  let bump : ℝ → ℝ := fun x => Real.smoothTransition ((x - a) * (x - b))
  have hbump : ContDiff ℝ ∞ bump :=
    Real.smoothTransition.contDiff.comp (by fun_prop)
  have hzero (x : ℝ) (hx : x ∈ Icc a b) : bump x = 0 := by
    apply Real.smoothTransition.zero_of_nonpos
    exact mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr hx.1) (sub_nonpos.mpr hx.2)
  have hden (x : ℝ) : 0 < c x ^ 2 + bump x := by
    by_cases hx : x ∈ Icc a b
    · rw [hzero x hx, add_zero]
      exact sq_pos_of_ne_zero (hne x hx)
    · have hout : x < a ∨ b < x := by
        simpa only [mem_Icc, not_and_or, not_le] using hx
      have hprod : 0 < (x - a) * (x - b) := by
        rcases hout with hx | hx
        · exact mul_pos_of_neg_of_neg (sub_neg.mpr hx) (sub_neg.mpr (hx.trans_le hab))
        · exact mul_pos (sub_pos.mpr (hab.trans_lt hx)) (sub_pos.mpr hx)
      exact add_pos_of_nonneg_of_pos (sq_nonneg _) (Real.smoothTransition.pos_of_pos hprod)
  refine ⟨fun x => p x * c x / (c x ^ 2 + bump x),
    (hp.mul hc).div ((hc.pow 2).add hbump) (fun x => (hden x).ne'), ?_⟩
  intro x hx
  change c x * (p x * c x / (c x ^ 2 + bump x)) = p x
  rw [hzero x hx, add_zero]
  field_simp [hne x hx]

end RicciFlowSharpEstimate.Analysis
