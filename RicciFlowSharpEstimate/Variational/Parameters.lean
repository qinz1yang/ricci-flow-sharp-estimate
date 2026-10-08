/-
Copyright (c) 2026 Ziyang Qin. All rights reserved.
No license is granted by this file.
Authors: Ziyang Qin
-/
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# The cap parameter for the exponential pair functional

For each cap `C ≥ 1`, the equation
`log q + (2 / 3) * (q ^ 3 - 1) = log C` has exactly one solution `q ≥ 1`.
This parameter determines the contact points of the constrained optimizer.
-/

namespace RicciFlowSharpEstimate.Variational

/-- The logarithm of the cap corresponding to the free-arc parameter `q`. -/
noncomputable def logCap (q : ℝ) : ℝ := Real.log q + (2 / 3 : ℝ) * (q ^ 3 - 1)

@[simp] theorem logCap_one : logCap 1 = 0 := by
  simp [logCap]

/-- The cap parametrization is continuous on its natural domain. -/
theorem continuousOn_logCap : ContinuousOn logCap (Set.Ici 1) := by
  unfold logCap
  apply ContinuousOn.add
  · exact Real.continuousOn_log.mono (by
      intro q hq
      exact ne_of_gt (lt_of_lt_of_le zero_lt_one hq))
  · fun_prop

/-- The cap parametrization is strictly increasing on its natural domain. -/
theorem strictMonoOn_logCap : StrictMonoOn logCap (Set.Ici 1) := by
  intro q hq r hr hqr
  have hqpos : 0 < q := lt_of_lt_of_le zero_lt_one hq
  have hrpos : 0 < r := lt_of_lt_of_le zero_lt_one hr
  have hlog : Real.log q < Real.log r := Real.strictMonoOn_log hqpos hrpos hqr
  have hpow : q ^ 3 ≤ r ^ 3 := pow_le_pow_left₀ hqpos.le hqr.le 3
  dsimp [logCap]
  nlinarith

/-- Every cap at least one has exactly one parameter on the natural branch. -/
theorem existsUnique_capParameter (C : ℝ) (hC : 1 ≤ C) :
    ∃! q : ℝ, 1 ≤ q ∧ Real.log q + (2 / 3 : ℝ) * (q ^ 3 - 1) = Real.log C := by
  have hpow : (1 : ℝ) ≤ C ^ 3 := by
    simpa using pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1) hC 3
  have hlow : logCap 1 ≤ Real.log C := by
    simpa using Real.log_nonneg hC
  have hupp : Real.log C ≤ logCap C := by
    dsimp [logCap]
    nlinarith
  obtain ⟨q, hq, heq⟩ := intermediate_value_Icc hC
    (continuousOn_logCap.mono (by intro x hx; exact hx.1)) ⟨hlow, hupp⟩
  refine ⟨q, ⟨hq.1, heq⟩, ?_⟩
  intro r hr
  apply strictMonoOn_logCap.injOn hr.1 hq.1
  exact hr.2.trans heq.symm

/-- The uniquely determined cap parameter. Values below the admissible cap
range are set to one; all variational results use `C ≥ 1`. -/
noncomputable def capParameter (C : ℝ) : ℝ :=
  if hC : 1 ≤ C then Classical.choose (existsUnique_capParameter C hC) else 1

/-- The cap parameter lies on the natural branch and satisfies its defining equation. -/
theorem capParameter_spec (C : ℝ) (hC : 1 ≤ C) :
    1 ≤ capParameter C ∧
      Real.log (capParameter C) + (2 / 3 : ℝ) * (capParameter C ^ 3 - 1) =
        Real.log C := by
  unfold capParameter
  rw [dite_eq_left hC]
  exact (Classical.choose_spec (existsUnique_capParameter C hC)).1

theorem one_le_capParameter (C : ℝ) : 1 ≤ capParameter C := by
  by_cases hC : 1 ≤ C
  · exact (capParameter_spec C hC).1
  · simp [capParameter, hC]

theorem logCap_capParameter (C : ℝ) (hC : 1 ≤ C) :
    logCap (capParameter C) = Real.log C :=
  (capParameter_spec C hC).2

/-- The cap parameter is unique among values on the natural branch. -/
theorem capParameter_eq_of_eq (C q : ℝ) (hC : 1 ≤ C) (hq : 1 ≤ q)
    (heq : Real.log q + (2 / 3 : ℝ) * (q ^ 3 - 1) = Real.log C) :
    capParameter C = q := by
  apply strictMonoOn_logCap.injOn (one_le_capParameter C) hq
  exact (logCap_capParameter C hC).trans heq.symm

@[simp] theorem capParameter_one : capParameter 1 = 1 := by
  apply capParameter_eq_of_eq
  · rfl
  · rfl
  · simp

/-- Only the degenerate cap has parameter one. -/
theorem capParameter_eq_one_iff (C : ℝ) (hC : 1 ≤ C) :
    capParameter C = 1 ↔ C = 1 := by
  constructor
  · intro hq
    have hlog : Real.log C = Real.log 1 := by
      simpa [hq] using (capParameter_spec C hC).2.symm
    exact Real.strictMonoOn_log.injOn (lt_of_lt_of_le zero_lt_one hC) (by norm_num) hlog
  · rintro rfl
    exact capParameter_one

end RicciFlowSharpEstimate.Variational
