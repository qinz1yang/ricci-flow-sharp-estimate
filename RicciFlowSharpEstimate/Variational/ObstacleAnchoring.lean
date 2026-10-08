/-
Copyright (c) 2026 Ziyang Qin. All rights reserved.
No license is granted by this file.
Authors: Ziyang Qin
-/
import RicciFlowSharpEstimate.Variational.ObstacleWeight
import RicciFlowSharpEstimate.Variational.Calibration

/-!
# The lower obstacle anchors the calibrated deficit

The normalized obstacle weight controls the squared profile error through the
actual first variation. All integrability follows from interval continuity;
neither a calibration sign nor an anchoring inequality is assumed.
-/

open MeasureTheory Set

namespace RicciFlowSharpEstimate.Variational

private theorem continuousOn_obstacleMarginal (C : ℝ) :
    ContinuousOn (pairMarginal (obstacleLogProfile C)) (Icc 0 1) := by
  let q := capParameter C
  have hq := one_le_capParameter C
  have hE := continuous_obstacleExponential q
  have hP : Continuous (obstaclePrefix q) := by
    apply continuous_iff_continuousAt.2
    intro v
    exact ((hE.integral_hasStrictDerivAt 0 v).hasDerivAt).continuousAt
  have hF : Continuous (fun v : ℝ => 2 * v / obstacleExponential q v) :=
    (continuous_const.mul continuous_id).div hE
      (fun v => (obstacleExponential_pos q v hq).ne')
  have hT : Continuous (obstacleTail q) := by
    have ht : obstacleTail q = fun v => -(∫ s in 1..v, 2 * s / obstacleExponential q s) := by
      funext v
      exact intervalIntegral.integral_symm 1 v
    rw [ht]
    apply continuous_iff_continuousAt.2
    intro v
    exact ((hF.integral_hasStrictDerivAt 1 v).hasDerivAt.neg).continuousAt
  have hcont := (hE.mul hT).sub (hF.mul hP)
  apply hcont.continuousOn.congr
  intro v hv
  exact pairMarginal_obstacleLogProfile C v hv

/-- The calibrated first variation is nonnegative for every admissible profile. -/
theorem pairFirstVariation_obstacleLogProfile_nonneg (C : ℝ) (hC : 1 ≤ C)
    (k : ℝ → ℝ) (hk : ContinuousOn k (Icc 0 1))
    (hbox : ∀ v ∈ Icc (0 : ℝ) 1, 0 ≤ k v ∧ k v ≤ Real.log C) :
    0 ≤ pairFirstVariation k (obstacleLogProfile C) := by
  rw [pairFirstVariation_eq_integral_marginal k (obstacleLogProfile C) hk
    (continuous_obstacleLogProfile C).continuousOn]
  exact integral_nonneg (obstacle_marginal_mul_sub_nonneg C hC k hbox)

/-- The full lower obstacle controls its weighted squared error through the first variation. -/
theorem integral_lowerObstacleWeight_error_sq_le (C : ℝ) (hC : 1 ≤ C)
    (k : ℝ → ℝ) (hk : ContinuousOn k (Icc 0 1))
    (hbox : ∀ v ∈ Icc (0 : ℝ) 1, 0 ≤ k v ∧ k v ≤ Real.log C) :
    (∫ v in (0 : ℝ)..1, lowerObstacleWeight (lowerContact (capParameter C)) v *
      (k v - obstacleLogProfile C v) ^ 2) ≤
      (Real.log C / (2 * lowerContact (capParameter C) ^ 3)) *
        pairFirstVariation k (obstacleLogProfile C) := by
  let a := lowerContact (capParameter C)
  let g := obstacleLogProfile C
  have ha : 0 < a := lowerContact_pos _ (lt_of_lt_of_le zero_lt_one (one_le_capParameter C))
  have hlog : 0 ≤ Real.log C := Real.log_nonneg hC
  have hb : 0 ≤ Real.log C / (2 * a ^ 3) := div_nonneg hlog (by positivity)
  have hg : ContinuousOn g (Icc 0 1) := (continuous_obstacleLogProfile C).continuousOn
  have hd : ContinuousOn (fun v => k v - g v) (Icc 0 1) := hk.sub hg
  have hleft : ContinuousOn (fun v => lowerObstacleWeight a v * (k v - g v) ^ 2)
      (Icc 0 1) := (continuous_lowerObstacleWeight a).continuousOn.mul (hd.pow 2)
  have hright : ContinuousOn (fun v => (Real.log C / (2 * a ^ 3)) *
      (pairMarginal g v * (k v - g v))) (Icc 0 1) :=
    continuousOn_const.mul ((continuousOn_obstacleMarginal C).mul hd)
  have hpoint (v : ℝ) (hv : v ∈ Icc (0 : ℝ) 1) :
      lowerObstacleWeight a v * (k v - g v) ^ 2 ≤
        (Real.log C / (2 * a ^ 3)) * (pairMarginal g v * (k v - g v)) := by
    by_cases hva : v ≤ a
    · have hlow : g v = 0 := obstacleLogProfile_eq_low C v hva
      have hm : pairMarginal g v = 3 * (a ^ 2 - v ^ 2) :=
        pairMarginal_obstacleLogProfile_low C v hv.1 hva
      have hsq : (k v) ^ 2 ≤ Real.log C * k v := by
        nlinarith [mul_nonneg (hbox v hv).1 (sub_nonneg.2 (hbox v hv).2)]
      calc
        lowerObstacleWeight a v * (k v - g v) ^ 2 =
            lowerObstacleWeight a v * (k v) ^ 2 := by rw [hlow, sub_zero]
        _ ≤ lowerObstacleWeight a v * (Real.log C * k v) :=
          mul_le_mul_of_nonneg_left hsq (lowerObstacleWeight_nonneg a v ha)
        _ = (Real.log C / (2 * a ^ 3)) * (pairMarginal g v * (k v - g v)) := by
          rw [lowerObstacleWeight_eq_low a v ⟨hv.1, hva⟩, hm, hlow]
          ring
    · rw [lowerObstacleWeight_eq_zero a v ha.le (le_of_not_ge hva), zero_mul]
      exact mul_nonneg hb (obstacle_marginal_mul_sub_nonneg C hC k hbox v)
  have hi := intervalIntegral.integral_mono_on (μ := volume)
    (show (0 : ℝ) ≤ 1 by norm_num)
    (hleft.intervalIntegrable_of_Icc (by norm_num))
    (hright.intervalIntegrable_of_Icc (by norm_num)) hpoint
  rw [intervalIntegral.integral_const_mul,
    ← pairFirstVariation_eq_intervalIntegral_marginal k g hk hg] at hi
  exact hi

end RicciFlowSharpEstimate.Variational
