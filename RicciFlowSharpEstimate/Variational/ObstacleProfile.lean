/-
Copyright (c) 2026 Ziyang Qin. All rights reserved.
No license is granted by this file.
Authors: Ziyang Qin
-/
import RicciFlowSharpEstimate.Variational.Parameters
import RicciFlowSharpEstimate.Variational.Contacts
import RicciFlowSharpEstimate.Variational.FreeArc

/-!
# The admissible obstacle profile

Clamping the free arc between its two contact points gives the continuous
lower/free/upper candidate. Its exact three-piece formula is proved below,
including the collapsed free arc at the cap one.
-/

namespace RicciFlowSharpEstimate.Variational

/-- The exponential obstacle candidate with parameter `q`.
The clamped formula is equal to the explicit lower/free/upper pieces for `q ≥ 1`. -/
noncomputable def obstacleExponential (q v : ℝ) : ℝ :=
  freeExponential (lowerContact q) (max (lowerContact q) (min v (upperContact q)))

/-- The logarithmic candidate at the given cap. -/
noncomputable def obstacleLogProfile (C v : ℝ) : ℝ :=
  Real.log (obstacleExponential (capParameter C) v)

private theorem freeExponential_mono (a : ℝ) (ha : 0 < a) :
    Monotone (freeExponential a) := by
  intro x y hxy
  have hs := Real.sqrt_le_sqrt (div_le_div_of_nonneg_right hxy ha.le)
  have hp := pow_le_pow_left₀ (Real.sqrt_nonneg (x / a)) hs 3
  have he : Real.exp ((2 / 3 : ℝ) * (Real.sqrt (x / a) ^ 3 - 1)) ≤
      Real.exp ((2 / 3 : ℝ) * (Real.sqrt (y / a) ^ 3 - 1)) := by
    apply Real.exp_le_exp.mpr
    linarith
  exact mul_le_mul hs he (Real.exp_pos _).le (Real.sqrt_nonneg _)

/-- The upper endpoint value of the free exponential is its parametrized cap. -/
theorem exp_logCap (q : ℝ) (hq : 0 < q) :
    Real.exp (logCap q) = q * Real.exp ((2 / 3 : ℝ) * (q ^ 3 - 1)) := by
  rw [logCap, Real.exp_add, Real.exp_log hq]

/-- On the lower obstacle the exponential candidate equals one. -/
theorem obstacleExponential_eq_low (q v : ℝ) (hq : 1 ≤ q)
    (hv : v ≤ lowerContact q) : obstacleExponential q v = 1 := by
  have ha := lowerContact_pos q (lt_of_lt_of_le zero_lt_one hq)
  rw [obstacleExponential, max_eq_left ((min_le_left v (upperContact q)).trans hv)]
  exact freeExponential_self _ ha.ne'

/-- Between the contacts the candidate is the actual free-arc exponential. -/
theorem obstacleExponential_eq_free (q v : ℝ)
    (hl : lowerContact q ≤ v) (hu : v ≤ upperContact q) :
    obstacleExponential q v = freeExponential (lowerContact q) v := by
  rw [obstacleExponential, min_eq_left hu, max_eq_right hl]

/-- On the upper obstacle the exponential candidate equals the parametrized cap. -/
theorem obstacleExponential_eq_high (q v : ℝ) (hq : 1 ≤ q)
    (hv : upperContact q ≤ v) : obstacleExponential q v = Real.exp (logCap q) := by
  have hqpos : 0 < q := lt_of_lt_of_le zero_lt_one hq
  rw [obstacleExponential, min_eq_right hv, max_eq_right (lowerContact_le_upperContact q hq),
    upperContact, freeExponential_mul_sq _ q (lowerContact_pos q hqpos).ne' hqpos.le,
    exp_logCap q hqpos]

/-- The clamped definition has exactly the claimed piecewise formula. -/
theorem obstacleExponential_eq_piecewise (q v : ℝ) (hq : 1 ≤ q) :
    obstacleExponential q v = if v ≤ lowerContact q then 1
      else if v ≤ upperContact q then freeExponential (lowerContact q) v
      else Real.exp (logCap q) := by
  split_ifs with hl hu
  · exact obstacleExponential_eq_low q v hq hl
  · exact obstacleExponential_eq_free q v (le_of_not_ge hl) hu
  · exact obstacleExponential_eq_high q v hq (le_of_not_ge hu)

/-- The joined exponential profile is continuous, including both contacts. -/
theorem continuous_obstacleExponential (q : ℝ) : Continuous (obstacleExponential q) := by
  apply (continuous_freeExponential (lowerContact q)).comp
  fun_prop

/-- The exponential candidate remains between its two active obstacle values. -/
theorem obstacleExponential_bounds (q v : ℝ) (hq : 1 ≤ q) :
    1 ≤ obstacleExponential q v ∧ obstacleExponential q v ≤ Real.exp (logCap q) := by
  have hqpos : 0 < q := lt_of_lt_of_le zero_lt_one hq
  have hm := freeExponential_mono (lowerContact q) (lowerContact_pos q hqpos)
  have hl := hm (le_max_left (lowerContact q) (min v (upperContact q)))
  have hu := hm (max_le (lowerContact_le_upperContact q hq) (min_le_right v (upperContact q)))
  rw [freeExponential_self _ (lowerContact_pos q hqpos).ne'] at hl
  have hend : freeExponential (lowerContact q) (upperContact q) = Real.exp (logCap q) := by
    rw [upperContact, freeExponential_mul_sq _ q (lowerContact_pos q hqpos).ne' hqpos.le,
      exp_logCap q hqpos]
  rw [hend] at hu
  exact ⟨hl, hu⟩

/-- In particular the entire exponential candidate is strictly positive. -/
theorem obstacleExponential_pos (q v : ℝ) (hq : 1 ≤ q) :
    0 < obstacleExponential q v :=
  lt_of_lt_of_le zero_lt_one (obstacleExponential_bounds q v hq).1

/-- The logarithmic candidate is continuous on the real line. -/
theorem continuous_obstacleLogProfile (C : ℝ) : Continuous (obstacleLogProfile C) := by
  apply (continuous_obstacleExponential (capParameter C)).log
  intro v
  exact (obstacleExponential_pos _ v (one_le_capParameter C)).ne'

/-- The logarithmic candidate satisfies the actual cap constraints. -/
theorem obstacleLogProfile_bounds (C v : ℝ) (hC : 1 ≤ C) :
    0 ≤ obstacleLogProfile C v ∧ obstacleLogProfile C v ≤ Real.log C := by
  have h := obstacleExponential_bounds (capParameter C) v (one_le_capParameter C)
  have hpos := obstacleExponential_pos (capParameter C) v (one_le_capParameter C)
  refine ⟨Real.log_nonneg h.1, ?_⟩
  change Real.log (obstacleExponential (capParameter C) v) ≤ Real.log C
  apply Real.log_le_log hpos
  simpa [logCap_capParameter C hC, Real.exp_log (lt_of_lt_of_le zero_lt_one hC)] using h.2

/-- Admissibility is proved for the explicit continuous candidate at every cap. -/
theorem obstacleLogProfile_admissible (C : ℝ) (hC : 1 ≤ C) :
    ContinuousOn (obstacleLogProfile C) (Set.Icc 0 1) ∧
      ∀ v ∈ Set.Icc (0 : ℝ) 1, 0 ≤ obstacleLogProfile C v ∧
        obstacleLogProfile C v ≤ Real.log C := by
  exact ⟨(continuous_obstacleLogProfile C).continuousOn,
    fun v _ => obstacleLogProfile_bounds C v hC⟩

/-- The degenerate cap has the constant zero logarithmic candidate. -/
@[simp] theorem obstacleLogProfile_one (v : ℝ) : obstacleLogProfile 1 v = 0 := by
  have h := obstacleLogProfile_bounds 1 v le_rfl
  exact le_antisymm (by simpa using h.2) h.1

/-- Exponentiating the logarithmic candidate recovers the same exponential profile. -/
theorem exp_obstacleLogProfile (C v : ℝ) :
    Real.exp (obstacleLogProfile C v) = obstacleExponential (capParameter C) v := by
  exact Real.exp_log (obstacleExponential_pos _ v (one_le_capParameter C))

/-- The lower obstacle is attained by the logarithmic candidate. -/
theorem obstacleLogProfile_eq_low (C v : ℝ) (hv : v ≤ lowerContact (capParameter C)) :
    obstacleLogProfile C v = 0 := by
  simp [obstacleLogProfile, obstacleExponential_eq_low _ v (one_le_capParameter C) hv]

/-- The upper obstacle is attained by the logarithmic candidate, including at cap one. -/
theorem obstacleLogProfile_eq_high (C v : ℝ) (hC : 1 ≤ C)
    (hv : upperContact (capParameter C) ≤ v) : obstacleLogProfile C v = Real.log C := by
  rw [obstacleLogProfile, obstacleExponential_eq_high _ v (one_le_capParameter C) hv,
    Real.log_exp, logCap_capParameter C hC]

/-- The candidate has a nonempty free arc exactly at the nondegenerate caps. -/
theorem contact_separation_iff (C : ℝ) (hC : 1 ≤ C) :
    lowerContact (capParameter C) < upperContact (capParameter C) ↔ 1 < C := by
  constructor
  · intro h
    by_contra hnot
    have hEq : C = 1 := le_antisymm (le_of_not_gt hnot) hC
    simp [hEq] at h
  · intro h
    exact lowerContact_lt_upperContact _ (one_lt_capParameter C h)

end RicciFlowSharpEstimate.Variational
