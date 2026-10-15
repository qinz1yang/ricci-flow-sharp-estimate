/-
Copyright (c) 2026 Ziyang Qin. All rights reserved.
No license is granted by this file.
Authors: Ziyang Qin
-/
import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Reflection of an absolutely continuous real function

Reflection of the interval preserves absolute continuity. The reflected
function is identified with the primitive of the reflected actual derivative,
with no restriction on the orientation of the original interval.
-/

noncomputable section

namespace RicciFlowSharpEstimate.Analysis

open MeasureTheory Set

/-- Reflecting the argument of an absolutely continuous real function reflects
its interval of absolute continuity, for either ordering of the endpoints. -/
theorem absolutelyContinuousOnInterval_comp_sub_left
    {u : ℝ → ℝ} {a b c : ℝ} (h : AbsolutelyContinuousOnInterval u a b) :
    AbsolutelyContinuousOnInterval (fun x => u (c - x)) (c - b) (c - a) := by
  have hder : IntervalIntegrable (fun x => -deriv u (c - x)) volume (c - b) (c - a) :=
    (h.intervalIntegrable_deriv.comp_sub_left c).symm.neg
  have hconst : AbsolutelyContinuousOnInterval (fun _ : ℝ => u b) (c - b) (c - a) :=
    (contDiff_const : ContDiff ℝ 1 (fun _ : ℝ => u b)).contDiffOn.absolutelyContinuousOnInterval
  have hprimitive := hder.absolutelyContinuousOnInterval_intervalIntegral
    (c := c - b) left_mem_uIcc
  apply (hconst.fun_add hprimitive).congr
  intro x hx
  have hcx : c - x ∈ uIcc a b := by
    rcases mem_uIcc.mp hx with hx | hx
    · apply mem_uIcc.mpr
      left
      constructor <;> linarith [hx.1, hx.2]
    · apply mem_uIcc.mpr
      right
      constructor <;> linarith [hx.1, hx.2]
  have hchange : (∫ t in (c - b)..x, -deriv u (c - t)) =
      -(∫ t in (c - x)..b, deriv u t) := by
    rw [intervalIntegral.integral_neg, intervalIntegral.integral_comp_sub_left,
      sub_sub_cancel]
  have hFTC := (h.mono (uIcc_subset_uIcc hcx right_mem_uIcc)).integral_deriv_eq_sub
  change u b + (∫ t in (c - b)..x, -deriv u (c - t)) = u (c - x)
  rw [hchange, hFTC]
  ring

end RicciFlowSharpEstimate.Analysis
