/-
Copyright (c) 2026 Ziyang Qin. All rights reserved.
No license is granted by this file.
Authors: Ziyang Qin
-/
import RicciFlowSharpEstimate.Geometry.AreaWarpBounds
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Weighted probe mass near both physical poles

The normalized warp is bounded by twice the distance to either pole. Thus
the sum of the actual probe masses in two polar intervals is controlled by
their radius times the ordinary square integral. The intervals may overlap.
-/

noncomputable section

namespace RicciFlowSharpEstimate.Geometry.AreaProfile

open MeasureTheory Set

/-- The sum of the weighted probe masses in the radius-`δ` intervals at both
physical poles. Overlap, when present, is counted in each interval. -/
def polarProbeMass (K r : ℝ → ℝ) (δ : ℝ) : ℝ :=
  (∫ x in (0 : ℝ)..δ, warp K x * r x ^ 2) +
    ∫ x in (1 - δ)..1, warp K x * r x ^ 2

/-- The actual two-pole mass is nonnegative for a radius in the unit interval. -/
theorem polarProbeMass_nonneg (K r : ℝ → ℝ) (hK : Continuous K)
    (hnonneg : ∀ x ∈ Icc (0 : ℝ) 1, 0 ≤ K x)
    (hzero : (∫ x in (0 : ℝ)..1, K x) = 2)
    (hone : (∫ x in (0 : ℝ)..1, x * K x) = 1)
    (δ : ℝ) (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1) :
    0 ≤ polarProbeMass K r δ := by
  unfold polarProbeMass
  apply add_nonneg
  · apply intervalIntegral.integral_nonneg hδ0
    intro x hx
    exact mul_nonneg (warp_nonneg_le_two_mul_min K hK hnonneg hzero hone x
      ⟨hx.1, hx.2.trans hδ1⟩).1 (sq_nonneg _)
  · apply intervalIntegral.integral_nonneg (sub_le_self 1 hδ0)
    intro x hx
    exact mul_nonneg (warp_nonneg_le_two_mul_min K hK hnonneg hzero hone x
      ⟨(sub_nonneg.mpr hδ1).trans hx.1, hx.2⟩).1 (sq_nonneg _)

/-- The weighted mass near both poles is at most four times the radius times
the unweighted square integral of the same probe. No endpoint condition on
the probe, or disjointness assumption on the polar intervals, is needed. -/
theorem polarProbeMass_le_four_mul_radius (K r : ℝ → ℝ) (hK : Continuous K)
    (hr : Continuous r) (hnonneg : ∀ x ∈ Icc (0 : ℝ) 1, 0 ≤ K x)
    (hzero : (∫ x in (0 : ℝ)..1, K x) = 2)
    (hone : (∫ x in (0 : ℝ)..1, x * K x) = 1)
    (δ : ℝ) (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1) :
    polarProbeMass K r δ ≤ 4 * δ * (∫ x in (0 : ℝ)..1, r x ^ 2) := by
  have hcont : Continuous (fun x => warp K x * r x ^ 2) :=
    (warp_continuous K hK).mul (hr.pow 2)
  have hscale : 0 ≤ 2 * δ := mul_nonneg (by norm_num) hδ0
  have hwarp (x : ℝ) (hx : x ∈ Icc (0 : ℝ) 1) :
      warp K x ≤ 2 * min x (1 - x) :=
    (warp_nonneg_le_two_mul_min K hK hnonneg hzero hone x hx).2
  have htail (a b : ℝ) (ha0 : 0 ≤ a) (hab : a ≤ b) (hb1 : b ≤ 1)
      (hbound : ∀ x ∈ Icc a b, warp K x ≤ 2 * δ) :
      (∫ x in a..b, warp K x * r x ^ 2) ≤
        2 * δ * (∫ x in (0 : ℝ)..1, r x ^ 2) := by
    have hfull : (∫ x in a..b, r x ^ 2) ≤ ∫ x in (0 : ℝ)..1, r x ^ 2 :=
      intervalIntegral.integral_mono_interval ha0 hab hb1
        (Filter.Eventually.of_forall fun x => sq_nonneg (r x))
        ((hr.pow 2).intervalIntegrable 0 1)
    calc
      (∫ x in a..b, warp K x * r x ^ 2) ≤
          ∫ x in a..b, (2 * δ) * r x ^ 2 :=
        intervalIntegral.integral_mono_on hab (hcont.intervalIntegrable a b)
          (((hr.pow 2).intervalIntegrable a b).const_mul (2 * δ))
          (fun x hx => mul_le_mul_of_nonneg_right (hbound x hx) (sq_nonneg (r x)))
      _ = (2 * δ) * (∫ x in a..b, r x ^ 2) :=
        intervalIntegral.integral_const_mul (2 * δ) (fun x => r x ^ 2)
      _ ≤ 2 * δ * (∫ x in (0 : ℝ)..1, r x ^ 2) :=
        mul_le_mul_of_nonneg_left hfull hscale
  have hleft : (∫ x in (0 : ℝ)..δ, warp K x * r x ^ 2) ≤
      2 * δ * (∫ x in (0 : ℝ)..1, r x ^ 2) := by
    apply htail 0 δ le_rfl hδ0 hδ1
    intro x hx
    calc
      warp K x ≤ 2 * min x (1 - x) := hwarp x ⟨hx.1, hx.2.trans hδ1⟩
      _ ≤ 2 * x := mul_le_mul_of_nonneg_left (min_le_left _ _) (by norm_num)
      _ ≤ 2 * δ := mul_le_mul_of_nonneg_left hx.2 (by norm_num)
  have hright : (∫ x in (1 - δ)..1, warp K x * r x ^ 2) ≤
      2 * δ * (∫ x in (0 : ℝ)..1, r x ^ 2) := by
    apply htail (1 - δ) 1 (sub_nonneg.mpr hδ1) (sub_le_self 1 hδ0) le_rfl
    intro x hx
    calc
      warp K x ≤ 2 * min x (1 - x) :=
        hwarp x ⟨(sub_nonneg.mpr hδ1).trans hx.1, hx.2⟩
      _ ≤ 2 * (1 - x) := mul_le_mul_of_nonneg_left (min_le_right _ _) (by norm_num)
      _ ≤ 2 * δ := by linarith only [hx.1]
  calc
    polarProbeMass K r δ ≤
        2 * δ * (∫ x in (0 : ℝ)..1, r x ^ 2) +
          2 * δ * (∫ x in (0 : ℝ)..1, r x ^ 2) := add_le_add hleft hright
    _ = 4 * δ * (∫ x in (0 : ℝ)..1, r x ^ 2) := by ring

end RicciFlowSharpEstimate.Geometry.AreaProfile
