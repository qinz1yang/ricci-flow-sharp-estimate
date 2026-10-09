/-
Copyright (c) 2026 Ziyang Qin. All rights reserved.
No license is granted by this file.
Authors: Ziyang Qin
-/
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Normalized reciprocal logarithms

Continuity, differentiation and obstacle bounds of log(M/a) on their actual domains.
-/

namespace RicciFlowSharpEstimate.Analysis

open Set

/-- Positive reciprocal profiles give continuous logarithms on their domain. -/
theorem continuousOn_log_reciprocal (a : ℝ → ℝ) (M : ℝ) (hM : 0 < M)
    (s : Set ℝ) (ha : ContinuousOn a s) (hpos : ∀ v ∈ s, 0 < a v) :
    ContinuousOn (fun v => Real.log (M / a v)) s :=
  (continuousOn_const.div ha (fun v hv => (hpos v hv).ne')).log
    (fun v hv => (div_pos hM (hpos v hv)).ne')

/-- Differentiation of the normalized reciprocal logarithm cancels the normalization. -/
theorem hasDerivAt_log_reciprocal (a : ℝ → ℝ) (M v a' : ℝ)
    (hM : 0 < M) (ha : HasDerivAt a a' v) (hpos : 0 < a v) :
    HasDerivAt (fun x => Real.log (M / a x)) (-a' / a v) v := by
  convert ((hasDerivAt_const v M).div ha hpos.ne').log (div_pos hM hpos).ne' using 1
  dsimp only [Pi.div_apply]
  field_simp [hM.ne', hpos.ne']
  ring

/-- Actual positive lower and upper bounds imply the logarithmic obstacle bounds. -/
theorem log_reciprocal_bounds (m M x : ℝ) (hm : 0 < m)
    (hl : m ≤ x) (hu : x ≤ M) :
    0 ≤ Real.log (M / x) ∧ Real.log (M / x) ≤ Real.log (M / m) := by
  have hx : 0 < x := hm.trans_le hl
  have hM : 0 < M := hx.trans_le hu
  exact ⟨Real.log_nonneg ((le_div_iff₀ hx).2 (by simpa using hu)),
    Real.log_le_log (div_pos hM hx) (div_le_div_of_nonneg_left hM.le hm hl)⟩

end RicciFlowSharpEstimate.Analysis
