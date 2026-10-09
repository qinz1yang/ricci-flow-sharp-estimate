/-
Copyright (c) 2026 Ziyang Qin. All rights reserved.
No license is granted by this file.
Authors: Ziyang Qin
-/
import RicciFlowSharpEstimate.Geometry.CriticalAreaProfile
import RicciFlowSharpEstimate.Geometry.AreaPlateauInstability

/-!
# Plateau instability of the actual critical area curvature

The actual critical zero action and positive plateau produce one fixed smooth
negative probe. The explicit bump, step size, original derivatives and endpoint
data survive for subsequent strict contraction and smooth curvature recovery.

Adapted from Ziyang Qin's historical critical meridian instability application.
-/

noncomputable section

namespace RicciFlowSharpEstimate.Geometry.CriticalAreaProfile

open MeasureTheory Set
open scoped ContDiff Topology

/-- A genuine bump in the actual critical plateau gives a fixed negative probe,
with its exact coefficient, quadratic remainder, step size and derivatives. -/
theorem exists_smooth_negative_probe_data :
    ∃ χ : ℝ → ℝ,
      ContDiff ℝ ∞ χ ∧ HasCompactSupport χ ∧ tsupport χ ⊆ Ioo (0 : ℝ) 1 ∧
      (∀ x ∈ tsupport χ, curvature x = length) ∧
      (∀ x, χ x ∈ Icc (0 : ℝ) 1) ∧
      0 < ∫ x in (0 : ℝ)..1, AreaProfile.warp curvature x * χ x ∧
      let A := length ^ 2 * ∫ x in (0 : ℝ)..1, AreaProfile.warp curvature x * χ x
      let B := AreaProfile.meridionalAction curvature χ
      let ε := A / (|B| + 1)
      let r := fun x => 1 - ε * χ x
      0 < A ∧ 0 < ε ∧ ContDiff ℝ ∞ r ∧
      deriv r = (fun x => -ε * deriv χ x) ∧
      deriv (deriv r) = (fun x => -ε * deriv (deriv χ) x) ∧
      r 0 = 1 ∧ deriv r 0 = 0 ∧
      r =ᶠ[𝓝 0] (fun _ => 1) ∧ r =ᶠ[𝓝 1] (fun _ => 1) ∧
      (∃ x ∈ Ioo (0 : ℝ) 1, r x ≠ 1) ∧
      AreaProfile.meridionalAction curvature r = -2 * ε * A + ε ^ 2 * B ∧
      AreaProfile.meridionalAction curvature r < 0 := by
  obtain ⟨l, u, hl, hlu, hu, hPlateau, hfpos⟩ := exists_positive_constant_plateau
  obtain ⟨χ, hχ, hcompact, hsupport, hbox, hpair, hrest⟩ :=
    AreaProfile.exists_smooth_plateau_probe curvature curvature_continuous length l u
      length_pos hl hlu hu (fun x hx => hPlateau x ⟨hx.1.le, hx.2.le⟩)
      (fun x hx => hfpos x ⟨hx.1.le, hx.2.le⟩) meridionalAction_one_eq_zero
  refine ⟨χ, hχ, hcompact, ?_, ?_, hbox, hpair, hrest⟩
  · intro x hx
    exact ⟨hl.trans (hsupport hx).1, (hsupport hx).2.trans hu⟩
  · intro x hx
    exact hPlateau x ⟨(hsupport hx).1.le, (hsupport hx).2.le⟩

/-- The actual critical curvature is unstable under a smooth probe variation,
with the same probe constant near both physical endpoints. -/
theorem exists_smooth_negative_probe :
    ∃ r : ℝ → ℝ, ContDiff ℝ ∞ r ∧ r 0 = 1 ∧ deriv r 0 = 0 ∧
      r =ᶠ[𝓝 0] (fun _ => 1) ∧ r =ᶠ[𝓝 1] (fun _ => 1) ∧
      (∃ x ∈ Ioo (0 : ℝ) 1, r x ≠ 1) ∧ AreaProfile.meridionalAction curvature r < 0 := by
  obtain ⟨χ, _, _, _, _, _, _, _, _, hr, _, _, hr0, hrd0, hn0, hn1, hnz, _, hneg⟩ :=
    exists_smooth_negative_probe_data
  exact ⟨_, hr, hr0, hrd0, hn0, hn1, hnz, hneg⟩

end RicciFlowSharpEstimate.Geometry.CriticalAreaProfile
