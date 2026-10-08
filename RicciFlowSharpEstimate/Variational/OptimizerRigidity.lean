/-
Copyright (c) 2026 Ziyang Qin. All rights reserved.
No license is granted by this file.
Authors: Ziyang Qin
-/
import RicciFlowSharpEstimate.Variational.Calibration
import RicciFlowSharpEstimate.Variational.PairRigidity
import RicciFlowSharpEstimate.Variational.OptimalValue
import RicciFlowSharpEstimate.Variational.ContactRegularity

/-!
# Uniqueness and smooth nonattainment in the constrained pair problem

The actual remainder first forces a constant difference. Both active obstacles
anchor this constant to zero. The exact contact derivative jump then excludes
equality for competitors differentiable throughout the interior when `C > 1`.
-/

namespace RicciFlowSharpEstimate.Variational

open Set MeasureTheory

/-- Equality in the constrained minimum holds exactly on the interval at the canonical profile. -/
theorem pairFunctional_eq_obstacleLogProfile_iff (C : ℝ) (hC : 1 ≤ C) (k : ℝ → ℝ)
    (hk : ContinuousOn k (Icc 0 1))
    (hbox : ∀ v ∈ Icc (0 : ℝ) 1, 0 ≤ k v ∧ k v ≤ Real.log C) :
    pairFunctional k = pairFunctional (obstacleLogProfile C) ↔
      EqOn k (obstacleLogProfile C) (Icc 0 1) := by
  constructor
  · intro heq
    have hg : ContinuousOn (obstacleLogProfile C) (Icc 0 1) :=
      (continuous_obstacleLogProfile C).continuousOn
    have hdef := pairFunctional_sub_eq_integral_marginal k (obstacleLogProfile C) hk hg
    have hlin : 0 ≤ (∫ v : ℝ, pairMarginal (obstacleLogProfile C) v *
        (k v - obstacleLogProfile C v)) :=
      integral_nonneg (obstacle_marginal_mul_sub_nonneg C hC k hbox)
    have hr := pairRemainder_nonneg k (obstacleLogProfile C)
    have hzero : pairRemainder k (obstacleLogProfile C) = 0 := by
      rw [heq] at hdef
      linarith
    obtain ⟨c, hc⟩ := (pairRemainder_eq_zero_iff k (obstacleLogProfile C) hk hg).mp hzero
    have hqpos : 0 < capParameter C := lt_of_lt_of_le zero_lt_one (one_le_capParameter C)
    have h0 := hc 0 ⟨le_rfl, zero_le_one⟩
    have h1 := hc 1 ⟨zero_le_one, le_rfl⟩
    rw [obstacleLogProfile_eq_low C 0 (lowerContact_pos _ hqpos).le, sub_zero] at h0
    rw [obstacleLogProfile_eq_high C 1 hC (upperContact_lt_one _ hqpos).le] at h1
    have hc0 : c = 0 := by
      have hk0 := (hbox 0 ⟨le_rfl, zero_le_one⟩).1
      have hk1 := (hbox 1 ⟨zero_le_one, le_rfl⟩).2
      linarith
    intro v hv
    have h := hc v hv
    rw [hc0] at h
    exact sub_eq_zero.mp h
  · intro h
    exact pairFunctional_congr k (obstacleLogProfile C) h

/-- The full closed-form bound for every continuous admissible competitor. -/
theorem pairFunctional_ge_closedForm (C : ℝ) (hC : 1 ≤ C) (k : ℝ → ℝ)
    (hk : ContinuousOn k (Icc 0 1))
    (hbox : ∀ v ∈ Icc (0 : ℝ) 1, 0 ≤ k v ∧ k v ≤ Real.log C) :
    2 / 3 - upperContact (capParameter C) + 1 / (3 * upperContact (capParameter C)) ≤
      pairFunctional k := by
  rw [← pairFunctional_obstacleLogProfile_eq C hC]
  exact pairFunctional_obstacleLogProfile_le C hC k hk hbox

/-- Equality in the closed-form bound characterizes the same interval profile. -/
theorem pairFunctional_eq_closedForm_iff (C : ℝ) (hC : 1 ≤ C) (k : ℝ → ℝ)
    (hk : ContinuousOn k (Icc 0 1))
    (hbox : ∀ v ∈ Icc (0 : ℝ) 1, 0 ≤ k v ∧ k v ≤ Real.log C) :
    pairFunctional k = 2 / 3 - upperContact (capParameter C) +
      1 / (3 * upperContact (capParameter C)) ↔ EqOn k (obstacleLogProfile C) (Icc 0 1) := by
  rw [← pairFunctional_obstacleLogProfile_eq C hC]
  exact pairFunctional_eq_obstacleLogProfile_iff C hC k hk hbox

/-- A differentiable interior competitor cannot attain the nondegenerate constrained minimum. -/
theorem pairFunctional_obstacleLogProfile_lt_of_differentiableOn (C : ℝ) (hC : 1 < C)
    (k : ℝ → ℝ) (hk : ContinuousOn k (Icc 0 1))
    (hd : DifferentiableOn ℝ k (Ioo 0 1))
    (hbox : ∀ v ∈ Icc (0 : ℝ) 1, 0 ≤ k v ∧ k v ≤ Real.log C) :
    pairFunctional (obstacleLogProfile C) < pairFunctional k := by
  apply lt_of_le_of_ne (pairFunctional_obstacleLogProfile_le C hC.le k hk hbox)
  intro heq
  have heqOn := (pairFunctional_eq_obstacleLogProfile_iff C hC.le k hk hbox).mp heq.symm
  have hb := contact_bounds (capParameter C) (one_le_capParameter C)
  have ha1 : lowerContact (capParameter C) < 1 := hb.2.1.trans_lt hb.2.2
  have hmem : lowerContact (capParameter C) ∈ Ioo (0 : ℝ) 1 := ⟨hb.1, ha1⟩
  have hevent : k =ᶠ[nhds (lowerContact (capParameter C))] obstacleLogProfile C := by
    filter_upwards [Ioo_mem_nhds hb.1 ha1] with v hv
    exact heqOn ⟨hv.1.le, hv.2.le⟩
  have hdiff := (hd _ hmem).differentiableAt (Ioo_mem_nhds hb.1 ha1)
  exact not_differentiableAt_obstacleLogProfile_lowerContact C hC
    (hdiff.congr_of_eventuallyEq hevent.symm)

end RicciFlowSharpEstimate.Variational
