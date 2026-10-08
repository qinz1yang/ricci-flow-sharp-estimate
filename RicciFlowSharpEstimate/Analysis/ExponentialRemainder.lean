/-
Copyright (c) 2026 Ziyang Qin. All rights reserved.
No license is granted by this file.
Authors: Ziyang Qin
-/
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# A quadratic lower bound for the exponential remainder

On a half-line bounded below, the exponential lies above each of its tangent lines by
at least half the minimum second derivative times the squared displacement.
-/

namespace RicciFlowSharpEstimate.Analysis

open Set

/-- The exponential tangent remainder controls squared displacement when both endpoints
lie above `m`. The bound applies in either order of the two endpoints. -/
theorem exp_tangent_quadratic_lower (m x y : ℝ) (hx : m ≤ x) (hy : m ≤ y) :
    Real.exp m / 2 * (x - y) ^ 2 ≤
      Real.exp x - Real.exp y - Real.exp y * (x - y) := by
  let f : ℝ → ℝ := fun t => Real.exp t - Real.exp m / 2 * t ^ 2
  have hf (t : ℝ) : HasDerivAt f (Real.exp t - Real.exp m * t) t := by
    convert! (Real.hasDerivAt_exp t).sub
      (((hasDerivAt_id t).pow 2).const_mul (Real.exp m / 2)) using 1
    dsimp [f]
    ring
  have hf' (t : ℝ) :
      HasDerivAt (fun u => Real.exp u - Real.exp m * u) (Real.exp t - Real.exp m) t := by
    simpa using! (Real.hasDerivAt_exp t).sub ((hasDerivAt_id t).const_mul (Real.exp m))
  have hconv : ConvexOn ℝ (Ici m) f := by
    refine convexOn_of_hasDerivWithinAt2_nonneg (convex_Ici m)
      (fun t _ => (hf t).continuousAt.continuousWithinAt)
      (fun t _ => (hf t).hasDerivWithinAt)
      (fun t _ => (hf' t).hasDerivWithinAt) ?_
    intro t ht
    exact sub_nonneg.mpr (Real.exp_le_exp.mpr (interior_subset ht))
  rcases lt_trichotomy x y with hxy | rfl | hyx
  · have hs := hconv.slope_le_of_hasDerivAt hx hy hxy (hf y)
    rw [slope_def_field, div_le_iff₀ (sub_pos.mpr hxy)] at hs
    dsimp [f] at hs
    nlinarith only [hs]
  · simp
  · have hs := hconv.le_slope_of_hasDerivAt hy hx hyx (hf y)
    rw [slope_def_field, le_div_iff₀ (sub_pos.mpr hyx)] at hs
    dsimp [f] at hs
    nlinarith only [hs]

end RicciFlowSharpEstimate.Analysis
