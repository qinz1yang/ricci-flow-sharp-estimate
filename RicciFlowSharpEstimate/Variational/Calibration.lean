/-
Copyright (c) 2026 Ziyang Qin. All rights reserved.
No license is granted by this file.
Authors: Ziyang Qin
-/
import RicciFlowSharpEstimate.Variational.ObstaclePrimitives
import RicciFlowSharpEstimate.Variational.PairIteration

/-!
# Exact obstacle calibration and optimality

The marginal of the actual candidate is computed from its actual prefix and
tail integrals. Its signs on the active obstacles prove minimization of the
triangular exponential functional at every admissible cap.
-/

namespace RicciFlowSharpEstimate.Variational

open Set MeasureTheory

private theorem free_marginal_zero (a v : ℝ) (ha : 0 < a) (hv : 0 < v) :
    freeExponential a v * (-freeRightPrimitive a v) -
      (2 * v / freeExponential a v) * freeLeftPrimitive a v = 0 := by
  have hr := Real.sqrt_pos.2 (div_pos hv ha)
  have hs := Real.sq_sqrt (div_nonneg hv.le ha.le)
  have he := (Real.exp_pos ((2 / 3 : ℝ) * (Real.sqrt (v / a) ^ 3 - 1))).ne'
  unfold freeExponential freeRightPrimitive freeLeftPrimitive
  rw [Real.exp_neg]
  field_simp [hr.ne', he, ha.ne']
  have hvEq : v = a * Real.sqrt (v / a) ^ 2 := by
    rw [hs]
    field_simp [ha.ne']
  nlinarith

/-- The marginal is expressed using the prefix and tail of the very same candidate. -/
theorem pairMarginal_obstacleLogProfile (C v : ℝ) (hv : v ∈ Icc (0 : ℝ) 1) :
    pairMarginal (obstacleLogProfile C) v =
      obstacleExponential (capParameter C) v * obstacleTail (capParameter C) v -
      (2 * v / obstacleExponential (capParameter C) v) * obstaclePrefix (capParameter C) v := by
  rw [pairMarginal_eq_intervalIntegrals (obstacleLogProfile C) v hv]
  simp only [exp_obstacleLogProfile, obstaclePrefix, obstacleTail]

/-- The exact marginal on the lower obstacle. -/
theorem pairMarginal_obstacleLogProfile_low (C v : ℝ) (hv : 0 ≤ v)
    (hl : v ≤ lowerContact (capParameter C)) :
    pairMarginal (obstacleLogProfile C) v = 3 * (lowerContact (capParameter C) ^ 2 - v ^ 2) := by
  have hq := one_le_capParameter C
  have hb := (contact_bounds (capParameter C) hq)
  rw [pairMarginal_obstacleLogProfile C v ⟨hv, hl.trans (hb.2.1.trans hb.2.2.le)⟩,
    obstacleExponential_eq_low _ v hq hl, obstacleTail_eq_low _ v hq hl,
    obstaclePrefix_eq_low _ v hq hl]
  ring

/-- The exact marginal vanishes throughout the free arc, including its endpoints. -/
theorem pairMarginal_obstacleLogProfile_free (C v : ℝ)
    (hl : lowerContact (capParameter C) ≤ v) (hu : v ≤ upperContact (capParameter C)) :
    pairMarginal (obstacleLogProfile C) v = 0 := by
  have hq := one_le_capParameter C
  have hb := contact_bounds (capParameter C) hq
  have hvpos : 0 < v := hb.1.trans_le hl
  rw [pairMarginal_obstacleLogProfile C v ⟨hvpos.le, hu.trans hb.2.2.le⟩,
    obstacleExponential_eq_free _ v hl hu, obstacleTail_eq_free _ v hq hl hu,
    obstaclePrefix_eq_free _ v hq hl hu]
  exact free_marginal_zero _ v hb.1 hvpos

/-- The exact marginal on the upper obstacle. -/
theorem pairMarginal_obstacleLogProfile_high (C v : ℝ)
    (hu : upperContact (capParameter C) ≤ v) (hv : v ≤ 1) :
    pairMarginal (obstacleLogProfile C) v =
      -3 * (v - upperContact (capParameter C)) *
        (v + 1 / (3 * upperContact (capParameter C))) := by
  have hq := one_le_capParameter C
  have hqpos : 0 < capParameter C := lt_of_lt_of_le zero_lt_one hq
  have hb := upperContact_pos (capParameter C) hqpos
  rw [pairMarginal_obstacleLogProfile C v ⟨hb.le.trans hu, hv⟩,
    obstacleExponential_eq_high _ v hq hu, obstacleTail_eq_high _ v hq hu,
    obstaclePrefix_eq_high _ v hq hu,
    lowerContact_div_parameter _ hqpos]
  field_simp [hb.ne', (Real.exp_pos (logCap (capParameter C))).ne']
  ring

/-- The actual marginal pairs nonnegatively with every admissible perturbation. -/
theorem obstacle_marginal_mul_sub_nonneg (C : ℝ) (hC : 1 ≤ C) (k : ℝ → ℝ)
    (hk : ∀ v ∈ Icc (0 : ℝ) 1, 0 ≤ k v ∧ k v ≤ Real.log C) (v : ℝ) :
    0 ≤ pairMarginal (obstacleLogProfile C) v * (k v - obstacleLogProfile C v) := by
  by_cases hv : v ∈ Icc (0 : ℝ) 1
  · by_cases hl : v ≤ lowerContact (capParameter C)
    · rw [pairMarginal_obstacleLogProfile_low C v hv.1 hl, obstacleLogProfile_eq_low C v hl,
        sub_zero]
      apply mul_nonneg _ (hk v hv).1
      have hs := pow_le_pow_left₀ hv.1 hl 2
      nlinarith
    · by_cases hu : v ≤ upperContact (capParameter C)
      · rw [pairMarginal_obstacleLogProfile_free C v (le_of_not_ge hl) hu, zero_mul]
      · have hhigh := le_of_not_ge hu
        rw [pairMarginal_obstacleLogProfile_high C v hhigh hv.2,
          obstacleLogProfile_eq_high C v hC hhigh]
        apply mul_nonneg_of_nonpos_of_nonpos
        · have hb := upperContact_pos (capParameter C)
            (lt_of_lt_of_le zero_lt_one (one_le_capParameter C))
          have hp : 0 ≤ v + 1 / (3 * upperContact (capParameter C)) :=
            add_nonneg hv.1 (by positivity)
          exact mul_nonpos_of_nonpos_of_nonneg
            (mul_nonpos_of_nonpos_of_nonneg (by norm_num) (sub_nonneg.mpr hhigh)) hp
        · exact sub_nonpos.mpr (hk v hv).2
  · rw [pairMarginal_eq_zero_of_not_mem (obstacleLogProfile C) v hv, zero_mul]

/-- The explicit obstacle candidate minimizes the actual triangular functional at every cap. -/
theorem pairFunctional_obstacleLogProfile_le (C : ℝ) (hC : 1 ≤ C) (k : ℝ → ℝ)
    (hk : ContinuousOn k (Icc 0 1))
    (hbox : ∀ v ∈ Icc (0 : ℝ) 1, 0 ≤ k v ∧ k v ≤ Real.log C) :
    pairFunctional (obstacleLogProfile C) ≤ pairFunctional k := by
  apply pairFunctional_le_of_firstVariation_nonneg k (obstacleLogProfile C) hk
    (continuous_obstacleLogProfile C).continuousOn
  rw [pairFirstVariation_eq_integral_marginal k (obstacleLogProfile C) hk
    (continuous_obstacleLogProfile C).continuousOn]
  exact integral_nonneg (obstacle_marginal_mul_sub_nonneg C hC k hbox)

end RicciFlowSharpEstimate.Variational
