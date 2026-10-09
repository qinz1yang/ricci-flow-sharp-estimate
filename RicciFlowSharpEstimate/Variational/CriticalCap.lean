/-
Copyright (c) 2026 Ziyang Qin. All rights reserved.
No license is granted by this file.
Authors: Ziyang Qin
-/
import RicciFlowSharpEstimate.Variational.OptimalValue
import RicciFlowSharpEstimate.Variational.OptimizerRigidity
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# The exact critical cap of the pair functional

The accepted obstacle value reaches `1/3` exactly when its upper contact solves
`3 * β ^ 2 - β - 1 = 0`. The positive root determines the explicit cap below.
The final comparison concerns the actual pair functional at every cap at least one.
-/

namespace RicciFlowSharpEstimate.Variational

/-- The cap at which the optimal pair-functional value is `1/3`. -/
noncomputable def criticalCap : ℝ :=
  ((5 + Real.sqrt 13) / 3) ^ (1 / 3 : ℝ) * Real.exp ((4 + 2 * Real.sqrt 13) / 9)

private noncomputable def criticalParameter : ℝ :=
  ((5 + Real.sqrt 13) / 3) ^ (1 / 3 : ℝ)

private theorem one_lt_criticalParameter : 1 < criticalParameter := by
  apply Real.one_lt_rpow
  · nlinarith [Real.sqrt_nonneg (13 : ℝ)]
  · norm_num

private theorem criticalParameter_cube :
    criticalParameter ^ 3 = (5 + Real.sqrt 13) / 3 := by
  unfold criticalParameter
  simpa only [one_div, Nat.cast_ofNat] using Real.rpow_inv_natCast_pow
    (show (0 : ℝ) ≤ (5 + Real.sqrt 13) / 3 by positivity) (by norm_num : (3 : ℕ) ≠ 0)

/-- The critical cap belongs to the nondegenerate admissible range. -/
theorem one_lt_criticalCap : 1 < criticalCap := by
  have hq := one_lt_criticalParameter
  have he : 1 < Real.exp ((4 + 2 * Real.sqrt 13) / 9) := by
    apply Real.one_lt_exp_iff.mpr
    positivity
  exact hq.trans (lt_mul_of_one_lt_right (zero_lt_one.trans hq) he)

/-- The cap parameter at the critical cap is the explicit positive cube root. -/
theorem capParameter_criticalCap :
    capParameter criticalCap = ((5 + Real.sqrt 13) / 3) ^ (1 / 3 : ℝ) := by
  apply capParameter_eq_of_eq criticalCap criticalParameter one_lt_criticalCap.le
    one_lt_criticalParameter.le
  change Real.log criticalParameter + (2 / 3 : ℝ) * (criticalParameter ^ 3 - 1) =
    Real.log (criticalParameter * Real.exp ((4 + 2 * Real.sqrt 13) / 9))
  rw [criticalParameter_cube,
    Real.log_mul (zero_lt_one.trans one_lt_criticalParameter).ne' (Real.exp_pos _).ne',
    Real.log_exp]
  ring

/-- The critical parameter satisfies the exact cubic relation. -/
theorem capParameter_criticalCap_cube :
    capParameter criticalCap ^ 3 = (5 + Real.sqrt 13) / 3 := by
  rw [capParameter_criticalCap]
  exact criticalParameter_cube

/-- The critical upper contact is the positive root of `3 * β ^ 2 - β - 1`. -/
theorem upperContact_capParameter_criticalCap :
    upperContact (capParameter criticalCap) = (1 + Real.sqrt 13) / 6 := by
  have hq : 0 < capParameter criticalCap := zero_lt_one.trans_le (one_le_capParameter _)
  have hb := upperContact_pos (capParameter criticalCap) hq
  have hs := Real.sq_sqrt (show (0 : ℝ) ≤ 13 by norm_num)
  have hr : (0 : ℝ) < (1 + Real.sqrt 13) / 6 := by positivity
  have hrsq : ((1 + Real.sqrt 13) / 6) ^ 2 = (7 + Real.sqrt 13) / 18 := by
    nlinarith
  have hsq : upperContact (capParameter criticalCap) ^ 2 =
      ((1 + Real.sqrt 13) / 6) ^ 2 := by
    rw [upperContact_sq_eq _ hq, capParameter_criticalCap_cube, hrsq]
    have hd : (5 + Real.sqrt 13) / 3 + 2 ≠ (0 : ℝ) := by positivity
    field_simp [hd]
    nlinarith
  nlinarith

private theorem value_eq_one_third_iff_quadratic (b : ℝ) (hb : 0 < b) :
    (2 / 3 : ℝ) - b + 1 / (3 * b) = 1 / 3 ↔ 3 * b ^ 2 - b - 1 = 0 := by
  have hden : 3 * b ≠ 0 := by positivity
  constructor <;> intro h
  · field_simp [hden] at h
    nlinarith
  · field_simp [hden]
    nlinarith

/-- At the explicit critical cap, the actual obstacle candidate has value `1/3`. -/
theorem pairFunctional_obstacleLogProfile_criticalCap :
    pairFunctional (obstacleLogProfile criticalCap) = (1 / 3 : ℝ) := by
  rw [pairFunctional_obstacleLogProfile_eq criticalCap one_lt_criticalCap.le]
  apply (value_eq_one_third_iff_quadratic _
    (upperContact_pos _ (zero_lt_one.trans_le (one_le_capParameter _)))).2
  rw [upperContact_capParameter_criticalCap]
  nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 13 by norm_num)]

private theorem strictMonoOn_upperContact : StrictMonoOn upperContact (Set.Ioi 0) := by
  intro q hq r hr hqr
  have hqpos : 0 < q := hq
  have hrpos : 0 < r := hr
  have hq3 : q ^ 3 < r ^ 3 := pow_lt_pow_left₀ hqr hqpos.le (by norm_num)
  have hdenq : 0 < q ^ 3 + 2 := by positivity
  have hdenr : 0 < r ^ 3 + 2 := by positivity
  have hsq : upperContact q ^ 2 < upperContact r ^ 2 := by
    rw [upperContact_sq_eq q hqpos, upperContact_sq_eq r hrpos]
    apply (div_lt_div_iff₀ hdenq hdenr).2
    nlinarith
  have hbq := upperContact_pos q hqpos
  have hbr := upperContact_pos r hrpos
  nlinarith

private theorem strictAntiOn_candidateValue :
    StrictAntiOn (fun C => pairFunctional (obstacleLogProfile C)) (Set.Ici 1) := by
  intro C hC D hD hCD
  have hqC : 0 < capParameter C := zero_lt_one.trans_le (one_le_capParameter C)
  have hqD : 0 < capParameter D := zero_lt_one.trans_le (one_le_capParameter D)
  have hbC := upperContact_pos _ hqC
  have hbD := upperContact_pos _ hqD
  have hb : upperContact (capParameter C) < upperContact (capParameter D) :=
    strictMonoOn_upperContact hqC hqD (strictMonoOn_capParameter hC hD hCD)
  have hinv : 1 / (3 * upperContact (capParameter D)) <
      1 / (3 * upperContact (capParameter C)) := by
    apply one_div_lt_one_div_of_lt
    · positivity
    · linarith
  change pairFunctional (obstacleLogProfile D) < pairFunctional (obstacleLogProfile C)
  rw [pairFunctional_obstacleLogProfile_eq C hC, pairFunctional_obstacleLogProfile_eq D hD]
  linarith

/-- The actual optimal value is at least `1/3` exactly up to the critical cap. -/
theorem pairFunctional_obstacleLogProfile_ge_one_third_iff (C : ℝ) (hC : 1 ≤ C) :
    (1 / 3 : ℝ) ≤ pairFunctional (obstacleLogProfile C) ↔ C ≤ criticalCap := by
  constructor
  · intro h
    by_contra hCcrit
    have hlt := strictAntiOn_candidateValue one_lt_criticalCap.le hC (lt_of_not_ge hCcrit)
    change pairFunctional (obstacleLogProfile C) <
      pairFunctional (obstacleLogProfile criticalCap) at hlt
    rw [pairFunctional_obstacleLogProfile_criticalCap] at hlt
    exact (not_lt_of_ge h) hlt
  · intro hCcrit
    have hle := strictAntiOn_candidateValue.antitoneOn hC one_lt_criticalCap.le hCcrit
    simpa only [pairFunctional_obstacleLogProfile_criticalCap] using hle

/-- Every differentiable admissible profile in a safe cap has value strictly
above `1/3`, including the direct degenerate-cap case. -/
theorem pairFunctional_gt_one_third_of_differentiableOn (C : ℝ) (hC : 1 ≤ C)
    (hcap : C ≤ criticalCap) (k : ℝ → ℝ) (hk : ContinuousOn k (Set.Icc 0 1))
    (hd : DifferentiableOn ℝ k (Set.Ioo 0 1))
    (hbox : ∀ v ∈ Set.Icc (0 : ℝ) 1, 0 ≤ k v ∧ k v ≤ Real.log C) :
    (1 / 3 : ℝ) < pairFunctional k := by
  by_cases hone : C = 1
  · subst C
    have h := pairFunctional_obstacleLogProfile_le 1 le_rfl k hk hbox
    rw [pairFunctional_obstacleLogProfile_one] at h
    linarith
  · have hlt : 1 < C := lt_of_le_of_ne hC (Ne.symm hone)
    exact lt_of_le_of_lt ((pairFunctional_obstacleLogProfile_ge_one_third_iff C hC).mpr hcap)
      (pairFunctional_obstacleLogProfile_lt_of_differentiableOn C hlt k hk hd hbox)

end RicciFlowSharpEstimate.Variational
