/-
Copyright (c) 2026 Ziyang Qin. All rights reserved.
No license is granted by this file.
Authors: Ziyang Qin
-/
import RicciFlowSharpEstimate.Variational.ObstacleProfile
import Mathlib.Topology.Order.ProjIcc
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Topology.UniformSpace.HeineCantor

/-!
# The even reciprocal obstacle profile

The actual reciprocal optimizer is extended constantly outside its physical
interval by the native interval projection. This continuous profile is the
limit of smooth metrics, not itself a claimed smooth metric.
-/

namespace RicciFlowSharpEstimate.Variational

open Set

/-- The even reciprocal optimizer, with constant extension beyond the poles. -/
noncomputable def evenReciprocalProfile (C v : ℝ) : ℝ :=
  Real.exp (-obstacleLogProfile C (projIcc 0 1 (by norm_num) |v|))

/-- The extension retains the literal reciprocal optimizer on the physical interval. -/
theorem evenReciprocalProfile_eq (C v : ℝ) (hv : v ∈ Icc (-1 : ℝ) 1) :
    evenReciprocalProfile C v = Real.exp (-obstacleLogProfile C |v|) := by
  have habs : |v| ∈ Icc (0 : ℝ) 1 :=
    ⟨abs_nonneg v, abs_le.mpr hv⟩
  simp only [evenReciprocalProfile, projIcc_of_mem _ habs]

/-- Reflection preserves the extended reciprocal profile on the entire real line. -/
theorem even_evenReciprocalProfile (C : ℝ) : Function.Even (evenReciprocalProfile C) := by
  intro v
  simp only [evenReciprocalProfile, abs_neg]

/-- The actual extended profile is uniformly continuous. -/
theorem uniformContinuous_evenReciprocalProfile (C : ℝ) :
    UniformContinuous (evenReciprocalProfile C) := by
  have hf : Continuous (fun v : Icc (0 : ℝ) 1 =>
      Real.exp (-obstacleLogProfile C v)) :=
    Real.continuous_exp.comp
      ((continuous_obstacleLogProfile C).comp continuous_subtype_val).neg
  have hu := CompactSpace.uniformContinuous_of_continuous hf
  have ha : UniformContinuous (fun v : ℝ => |v|) := by
    rw [show (fun v : ℝ => |v|) = (fun v : ℝ => ‖v‖) from
      funext (fun v => (Real.norm_eq_abs v).symm)]
    exact uniformContinuous_norm
  exact hu.comp ((LipschitzWith.projIcc (by norm_num : (0 : ℝ) ≤ 1)).uniformContinuous.comp ha)

/-- The continuous limit satisfies the same global reciprocal box as its approximants. -/
theorem evenReciprocalProfile_bounds (C : ℝ) (hC : 1 ≤ C) (v : ℝ) :
    1 / C ≤ evenReciprocalProfile C v ∧ evenReciprocalProfile C v ≤ 1 := by
  have hpos : 0 < C := zero_lt_one.trans_le hC
  have hb := obstacleLogProfile_bounds C (projIcc 0 1 (by norm_num) |v|) hC
  constructor
  · calc
      1 / C = Real.exp (-Real.log C) := by rw [Real.exp_neg, Real.exp_log hpos, one_div]
      _ ≤ evenReciprocalProfile C v := Real.exp_le_exp.mpr (neg_le_neg hb.2)
  · exact (Real.exp_le_one_iff).mpr (neg_nonpos.mpr hb.1)

end RicciFlowSharpEstimate.Variational
