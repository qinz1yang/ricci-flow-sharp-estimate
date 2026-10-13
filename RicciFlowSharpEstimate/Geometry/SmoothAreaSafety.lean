/-
Copyright (c) 2026 Ziyang Qin. All rights reserved.
No license is granted by this file.
Authors: Ziyang Qin
-/
import RicciFlowSharpEstimate.Geometry.NormalizedAreaHaar
import RicciFlowSharpEstimate.Geometry.SmoothAreaInfimum

/-!
# The sign of the actual joint value and original safe caps

The existing all-form transfer and tied geometric realization identify the sign
of the smooth normalized infimum with the original universal safety predicate.
Consequently every strictly superthreshold cap has an actually negative joint
value. This supplies a relevant regime for the sign research; it does not
determine the threshold or produce an operator orientation.
-/

noncomputable section
namespace RicciFlowSharpEstimate.Geometry.AreaProfile
open Set MeasureTheory
open scoped ContDiff

/-- The normalized smooth joint value is nonnegative exactly when the original
cap is safe for every smooth one-form on every represented rotational geometry. -/
theorem smoothAreaInfimum_nonneg_iff_rotationalSafeCap (C : ℝ) (hC : 1 ≤ C) :
    0 ≤ smoothAreaInfimum C ↔ C ∈ rotationalSafeCaps := by
  constructor
  · intro hm
    apply rotationalSafeCaps_of_normalized_area_safety C hC
    intro K hK _hpos hzero hone κ Λ hκ hbox hratio r hr hmass
    exact hm.trans (smoothAreaInfimum_le_action C hC K r
      ⟨hK, hr, ⟨κ, Λ, hκ, hbox, hratio⟩, hzero, hone, hmass⟩)
  · intro hsafe
    apply le_csInf (smoothAreaActionValues_nonempty C hC)
    rintro a ⟨K, r, h, rfl⟩
    obtain ⟨hK, hr, ⟨κ, Λ, hκ, hbox, hratio⟩, hzero, hone, _⟩ := h
    exact areaAction_nonneg_of_rotationalSafeCap C hsafe K r hK hr
      (fun x hx => hκ.trans_le (hbox x hx).1) hzero hone κ Λ hκ hbox hratio

/-- Above the original unrestricted threshold, the actual joint infimum is
strictly negative. No unknown zero eigenvalue or selected branch is assumed. -/
theorem smoothAreaInfimum_neg_of_rotationalThreshold_lt {C : ℝ}
    (hC : rotationalThreshold < C) : smoothAreaInfimum C < 0 := by
  have hCone : 1 ≤ C := one_le_rotationalThreshold.trans hC.le
  by_contra hn
  have hsafe := (smoothAreaInfimum_nonneg_iff_rotationalSafeCap C hCone).mp
    (le_of_not_gt hn)
  have hle : C ≤ rotationalThreshold :=
    le_csSup rotationalSafeCaps_bddAbove hsafe
  exact (not_lt_of_ge hle) hC

end RicciFlowSharpEstimate.Geometry.AreaProfile
