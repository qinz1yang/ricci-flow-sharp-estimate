/-
Copyright (c) 2026 Ziyang Qin. All rights reserved.
No license is granted by this file.
Authors: Ziyang Qin
-/
import RicciFlowSharpEstimate.Variational.WeightedVariance
import RicciFlowSharpEstimate.Analysis.WeightedAnchor
import RicciFlowSharpEstimate.Variational.ObstacleAnchoring
import RicciFlowSharpEstimate.Variational.RemainderCoercivity

/-!
# Quantitative stability of the constrained exponential pair problem

The exact calibrated deficit controls both the centered variance and the
constant mode. The constant below uses the full lower-obstacle weight and
depends only on the cap through its canonical contact parameter.
-/

open MeasureTheory Set

namespace RicciFlowSharpEstimate.Variational

/-- An explicit coercivity constant from the complete lower-obstacle calibration. -/
noncomputable def stabilityConstant (C : ℝ) : ℝ :=
  (12 * C / (5 * lowerContact (capParameter C)) +
    Real.log C / (2 * lowerContact (capParameter C) ^ 3))⁻¹

/-- The stability constant is strictly positive, including at cap one. -/
theorem stabilityConstant_pos (C : ℝ) (hC : 1 ≤ C) : 0 < stabilityConstant C := by
  have hCp : 0 < C := lt_of_lt_of_le zero_lt_one hC
  have ha : 0 < lowerContact (capParameter C) :=
    lowerContact_pos _ (lt_of_lt_of_le zero_lt_one (one_le_capParameter C))
  have hlog : 0 ≤ Real.log C := Real.log_nonneg hC
  unfold stabilityConstant
  apply inv_pos.2
  exact add_pos_of_pos_of_nonneg (div_pos (by positivity) (by positivity))
    (div_nonneg hlog (by positivity))

/-- The actual deficit controls squared L2 distance to the unique canonical optimizer. -/
theorem pairFunctional_deficit_controls_L2 (C : ℝ) (hC : 1 ≤ C)
    (k : ℝ → ℝ) (hk : ContinuousOn k (Icc 0 1))
    (hbox : ∀ v ∈ Icc (0 : ℝ) 1, 0 ≤ k v ∧ k v ≤ Real.log C) :
    stabilityConstant C * (∫ v in (0 : ℝ)..1, (k v - obstacleLogProfile C v) ^ 2) ≤
      pairFunctional k - pairFunctional (obstacleLogProfile C) := by
  by_cases hC1 : C = 1
  · subst C
    have he : (∫ v in (0 : ℝ)..1, (k v - obstacleLogProfile 1 v) ^ 2) = 0 := by
      calc
        _ = ∫ v in (0 : ℝ)..1, (0 : ℝ) := by
          apply intervalIntegral.integral_congr
          intro v hv
          rw [uIcc_of_le (show (0 : ℝ) ≤ 1 by norm_num)] at hv
          have hkv : k v = 0 := by
            have hi := hbox v hv
            rw [Real.log_one] at hi
            exact le_antisymm hi.2 hi.1
          simp [hkv]
        _ = 0 := by simp
    rw [he, mul_zero]
    exact sub_nonneg.2 (pairFunctional_obstacleLogProfile_le 1 le_rfl k hk hbox)
  let g := obstacleLogProfile C
  let δ := fun v => k v - g v
  let α := lowerContact (capParameter C)
  let a := 1 / (2 * C)
  let b := Real.log C / (2 * α ^ 3)
  let P := pairFirstVariation k g
  let D := pairFunctional k - pairFunctional g
  have hCp : 0 < C := lt_of_lt_of_le zero_lt_one hC
  have hα : 0 < α := lowerContact_pos _ (lt_of_lt_of_le zero_lt_one (one_le_capParameter C))
  have hα1 : α ≤ 1 :=
    (lowerContact_le_upperContact _ (one_le_capParameter C)).trans
      (upperContact_lt_one _ (lt_of_lt_of_le zero_lt_one (one_le_capParameter C))).le
  have ha : 0 < a := one_div_pos.2 (mul_pos (by norm_num) hCp)
  have hb : 0 ≤ b := div_nonneg (Real.log_nonneg hC) (by positivity)
  have hg : ContinuousOn g (Icc 0 1) := (continuous_obstacleLogProfile C).continuousOn
  have hδ : ContinuousOn δ (Icc 0 1) := hk.sub hg
  have hP : 0 ≤ P := pairFirstVariation_obstacleLogProfile_nonneg C hC k hk hbox
  have hquad : a * pairQuadratic δ ≤ pairRemainder k g :=
    pairRemainder_ge_quadratic_integral C hC k g hk hg hbox
      (fun v _ => obstacleLogProfile_bounds C v hC)
  have hvar := integral_unitCentered_sq_le_pairQuadratic δ hδ
  change (∫ v in (0 : ℝ)..1, (δ v - (∫ x in (0 : ℝ)..1, δ x)) ^ 2) ≤
    pairQuadratic δ at hvar
  have hbudget : P + a * (∫ v in (0 : ℝ)..1,
      (δ v - (∫ x in (0 : ℝ)..1, δ x)) ^ 2) ≤ D := by
    have hdef : D = P + pairRemainder k g := pairFunctional_sub_eq k g hk hg
    have hv := mul_le_mul_of_nonneg_left hvar ha.le
    linarith
  have hanchor : (∫ v in (0 : ℝ)..1, lowerObstacleWeight α v * (δ v) ^ 2) ≤ b * P :=
    integral_lowerObstacleWeight_error_sq_le C hC k hk hbox
  have hbound := Analysis.integral_sq_le_of_variance_anchor hδ
    (continuous_lowerObstacleWeight α).continuousOn
    (fun v _ => lowerObstacleWeight_nonneg α v hα)
    (integral_lowerObstacleWeight α hα hα1) hP ha hb hbudget hanchor
  rw [integral_lowerObstacleWeight_sq α hα hα1] at hbound
  have hcoef : (6 / (5 * α)) / a + b =
      12 * C / (5 * α) + Real.log C / (2 * α ^ 3) := by
    dsimp [a, b]
    field_simp [hα.ne', hCp.ne']
    ring
  rw [hcoef] at hbound
  have hpos : 0 < 12 * C / (5 * α) + Real.log C / (2 * α ^ 3) := by
    exact add_pos_of_pos_of_nonneg (div_pos (by positivity) (by positivity)) hb
  calc
    stabilityConstant C * (∫ v in (0 : ℝ)..1, (k v - obstacleLogProfile C v) ^ 2) ≤
        stabilityConstant C *
          ((12 * C / (5 * α) + Real.log C / (2 * α ^ 3)) * D) :=
      mul_le_mul_of_nonneg_left hbound (stabilityConstant_pos C hC).le
    _ = D := by
      change (12 * C / (5 * α) + Real.log C / (2 * α ^ 3))⁻¹ *
        ((12 * C / (5 * α) + Real.log C / (2 * α ^ 3)) * D) = D
      rw [← mul_assoc, inv_mul_cancel₀ hpos.ne', one_mul]

end RicciFlowSharpEstimate.Variational
