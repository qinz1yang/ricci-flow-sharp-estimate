/-
Copyright (c) 2026 Ziyang Qin. All rights reserved.
No license is granted by this file.
Authors: Ziyang Qin
-/
import RicciFlowSharpEstimate.Variational.EvenReciprocalProfile
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# Shape and strict average bounds of the reciprocal optimizer

The actual clamped optimizer is monotone on each hemisphere and constant on
its central and outer contact regions. Its strict average bounds hold exactly
in the nondegenerate range of caps; at cap one the profile is constant.

The monotonicity argument adapts the free-arc comparison in Ziyang Qin's
historical `PureRotationCriticalMonotonicity` to the current clamped profile.
-/

open MeasureTheory Set

namespace RicciFlowSharpEstimate.Variational

/-- The actual clamped exponential is nondecreasing for every positive parameter. -/
theorem monotone_obstacleExponential (q : ℝ) (hq : 0 < q) :
    Monotone (obstacleExponential q) := by
  intro x y hxy
  have ha := lowerContact_pos q hq
  have hclamp := max_le_max_left (lowerContact q) (min_le_min_right (upperContact q) hxy)
  have hs := Real.sqrt_le_sqrt (div_le_div_of_nonneg_right hclamp ha.le)
  have hp := pow_le_pow_left₀ (Real.sqrt_nonneg
    (max (lowerContact q) (min x (upperContact q)) / lowerContact q)) hs 3
  have he : Real.exp ((2 / 3 : ℝ) *
      (Real.sqrt (max (lowerContact q) (min x (upperContact q)) / lowerContact q) ^ 3 - 1)) ≤
      Real.exp ((2 / 3 : ℝ) *
      (Real.sqrt (max (lowerContact q) (min y (upperContact q)) / lowerContact q) ^ 3 - 1)) := by
    apply Real.exp_le_exp.mpr
    linarith
  exact mul_le_mul hs he (Real.exp_pos _).le (Real.sqrt_nonneg _)

/-- The logarithmic obstacle optimizer is nondecreasing on the real line. -/
theorem monotone_obstacleLogProfile (C : ℝ) : Monotone (obstacleLogProfile C) := by
  intro x y hxy
  apply Real.log_le_log (obstacleExponential_pos _ x (one_le_capParameter C))
  exact monotone_obstacleExponential _ (zero_lt_one.trans_le (one_le_capParameter C)) hxy

/-- The central contact region has reciprocal value one. -/
theorem evenReciprocalProfile_eq_low (C v : ℝ)
    (hv : |v| ≤ lowerContact (capParameter C)) : evenReciprocalProfile C v = 1 := by
  have hb := contact_bounds (capParameter C) (one_le_capParameter C)
  have hv1 : |v| ≤ 1 := hv.trans (hb.2.1.trans hb.2.2.le)
  rw [evenReciprocalProfile_eq C v (abs_le.mp hv1), obstacleLogProfile_eq_low C |v| hv]
  simp

/-- The outer contact regions, including the constant extension, have reciprocal value `1 / C`. -/
theorem evenReciprocalProfile_eq_high (C v : ℝ) (hC : 1 ≤ C)
    (hv : upperContact (capParameter C) ≤ |v|) : evenReciprocalProfile C v = 1 / C := by
  have hb := contact_bounds (capParameter C) (one_le_capParameter C)
  have hproj : upperContact (capParameter C) ≤
      (projIcc 0 1 (by norm_num) |v| : ℝ) := by
    rw [coe_projIcc]
    exact (le_min hb.2.2.le hv).trans (le_max_right _ _)
  rw [evenReciprocalProfile, obstacleLogProfile_eq_high C _ hC hproj,
    Real.exp_neg, Real.exp_log (zero_lt_one.trans_le hC), one_div]

/-- The reciprocal optimizer takes value one at the equator. -/
@[simp] theorem evenReciprocalProfile_at_zero (C : ℝ) : evenReciprocalProfile C 0 = 1 := by
  apply evenReciprocalProfile_eq_low
  simpa using (lowerContact_pos (capParameter C)
    (zero_lt_one.trans_le (one_le_capParameter C))).le

/-- The reciprocal optimizer takes value `1 / C` at the positive pole. -/
@[simp] theorem evenReciprocalProfile_at_one (C : ℝ) (hC : 1 ≤ C) :
    evenReciprocalProfile C 1 = 1 / C := by
  apply evenReciprocalProfile_eq_high C 1 hC
  simpa using (upperContact_lt_one (capParameter C)
    (zero_lt_one.trans_le (one_le_capParameter C))).le

/-- At cap one the reciprocal optimizer is constant, so its average bounds are equalities. -/
@[simp] theorem evenReciprocalProfile_one (v : ℝ) : evenReciprocalProfile 1 v = 1 := by
  simp [evenReciprocalProfile]

/-- The reciprocal optimizer is nonincreasing on the positive hemisphere. -/
theorem antitoneOn_evenReciprocalProfile (C : ℝ) :
    AntitoneOn (evenReciprocalProfile C) (Icc 0 1) := by
  intro x hx y hy hxy
  rw [evenReciprocalProfile_eq C x ⟨by linarith [hx.1], hx.2⟩,
    evenReciprocalProfile_eq C y ⟨by linarith [hy.1], hy.2⟩,
    abs_of_nonneg hx.1, abs_of_nonneg hy.1]
  exact Real.exp_le_exp.mpr (neg_le_neg (monotone_obstacleLogProfile C hxy))

/-- The reciprocal optimizer is nondecreasing on the negative hemisphere. -/
theorem monotoneOn_evenReciprocalProfile (C : ℝ) :
    MonotoneOn (evenReciprocalProfile C) (Icc (-1) 0) := by
  intro x hx y hy hxy
  rw [evenReciprocalProfile_eq C x ⟨hx.1, by linarith [hx.2]⟩,
    evenReciprocalProfile_eq C y ⟨hy.1, by linarith [hy.2]⟩,
    abs_of_nonpos hx.2, abs_of_nonpos hy.2]
  exact Real.exp_le_exp.mpr (neg_le_neg (monotone_obstacleLogProfile C (neg_le_neg hxy)))

/-- The literal lower contact gives a strictly positive central plateau inside the poles. -/
theorem evenReciprocalProfile_central_plateau (C : ℝ) :
    0 < lowerContact (capParameter C) ∧ lowerContact (capParameter C) < 1 ∧
      EqOn (evenReciprocalProfile C) (fun _ => 1)
        (Icc (-lowerContact (capParameter C)) (lowerContact (capParameter C))) := by
  have hb := contact_bounds (capParameter C) (one_le_capParameter C)
  exact ⟨hb.1, hb.2.1.trans_lt hb.2.2,
    fun v hv => evenReciprocalProfile_eq_low C v (abs_le.mpr hv)⟩

/-- Every nondegenerate cap gives strict average bounds for the actual reciprocal optimizer. -/
theorem evenReciprocalProfile_strict_average_bounds (C : ℝ) (hC : 1 < C) :
    (∫ v in (-1 : ℝ)..1, evenReciprocalProfile C v) < 2 ∧
      2 < (∫ v in (-1 : ℝ)..1, evenReciprocalProfile C v) * C := by
  have hcont : ContinuousOn (evenReciprocalProfile C) (Icc (-1) 1) :=
    (uniformContinuous_evenReciprocalProfile C).continuous.continuousOn
  have hinv : 1 / C < 1 := (div_lt_one (zero_lt_one.trans hC)).mpr hC
  have hupper := intervalIntegral.integral_lt_integral_of_continuousOn_of_le_of_exists_lt
    (by norm_num : (-1 : ℝ) < 1) hcont continuousOn_const
    (fun v _ => (evenReciprocalProfile_bounds C hC.le v).2)
    ⟨1, by norm_num, by simpa only [evenReciprocalProfile_at_one C hC.le] using hinv⟩
  have hlower := intervalIntegral.integral_lt_integral_of_continuousOn_of_le_of_exists_lt
    (by norm_num : (-1 : ℝ) < 1) continuousOn_const hcont
    (fun v _ => (evenReciprocalProfile_bounds C hC.le v).1)
    ⟨0, by norm_num, by simpa using hinv⟩
  constructor
  · norm_num at hupper
    exact hupper
  · have h := mul_lt_mul_of_pos_right hlower (zero_lt_one.trans hC)
    norm_num [intervalIntegral.integral_const, (zero_lt_one.trans hC).ne'] at h
    exact h

end RicciFlowSharpEstimate.Variational
