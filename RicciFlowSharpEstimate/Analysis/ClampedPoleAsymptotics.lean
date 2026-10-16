/-
Copyright (c) 2026 Ziyang Qin. All rights reserved.
No license is granted by this file.
Authors: Ziyang Qin
-/
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Order.LeftRightNhds
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Obstacle saturation from a negative quadratic endpoint remainder

A cubic positive denominator and a negative quadratic numerator remainder
force an eventual obstacle value of the literal divided clamp. The first
nonzero numerator coefficient selects the obstacle, including double cancellation.
-/

noncomputable section

namespace RicciFlowSharpEstimate.Analysis

open Filter Set Topology

private theorem lower_obstacle_of_scaled_limits
    {H D K w : ℝ → ℝ} {lo hi l : ℝ} (hl : 0 < l)
    (hw : ∀ᶠ x in 𝓝[>] (0 : ℝ), 0 < w x)
    (hH : Tendsto (fun x => H x / w x) (𝓝[>] (0 : ℝ)) (𝓝 l))
    (hD : Tendsto (fun x => D x / w x) (𝓝[>] (0 : ℝ)) (𝓝 0))
    (hDpos : ∀ᶠ x in 𝓝[>] (0 : ℝ), 0 < D x)
    (hclip : ∀ᶠ x in 𝓝[>] (0 : ℝ), K x = max lo (min hi (-H x / D x))) :
    ∀ᶠ x in 𝓝[>] (0 : ℝ), K x = lo := by
  have hsum : Tendsto (fun x => H x / w x + lo * (D x / w x))
      (𝓝[>] (0 : ℝ)) (𝓝 l) := by
    simpa only [mul_zero, add_zero] using hH.add (hD.const_mul lo)
  filter_upwards [hsum.eventually (lt_mem_nhds hl), hw, hDpos, hclip]
    with x hx hwx hDx hcx
  have heq : (H x + lo * D x) / w x = H x / w x + lo * (D x / w x) := by ring
  rw [← heq] at hx
  have hnum : 0 < H x + lo * D x := by
    simpa only [zero_mul] using (lt_div_iff₀ hwx).mp hx
  have hquot : -H x / D x ≤ lo := (div_le_iff₀ hDx).mpr (by linarith)
  rw [hcx]
  exact max_eq_left ((min_le_right _ _).trans hquot)

private theorem upper_obstacle_of_scaled_limits
    {H D K w : ℝ → ℝ} {lo hi l : ℝ} (hlohi : lo ≤ hi) (hl : l < 0)
    (hw : ∀ᶠ x in 𝓝[>] (0 : ℝ), 0 < w x)
    (hH : Tendsto (fun x => H x / w x) (𝓝[>] (0 : ℝ)) (𝓝 l))
    (hD : Tendsto (fun x => D x / w x) (𝓝[>] (0 : ℝ)) (𝓝 0))
    (hDpos : ∀ᶠ x in 𝓝[>] (0 : ℝ), 0 < D x)
    (hclip : ∀ᶠ x in 𝓝[>] (0 : ℝ), K x = max lo (min hi (-H x / D x))) :
    ∀ᶠ x in 𝓝[>] (0 : ℝ), K x = hi := by
  have hsum : Tendsto (fun x => H x / w x + hi * (D x / w x))
      (𝓝[>] (0 : ℝ)) (𝓝 l) := by
    simpa only [mul_zero, add_zero] using hH.add (hD.const_mul hi)
  filter_upwards [hsum.eventually (gt_mem_nhds hl), hw, hDpos, hclip]
    with x hx hwx hDx hcx
  have heq : (H x + hi * D x) / w x = H x / w x + hi * (D x / w x) := by ring
  rw [← heq] at hx
  have hnum : H x + hi * D x < 0 := by
    simpa only [zero_mul] using (div_lt_iff₀ hwx).mp hx
  have hquot : hi ≤ -H x / D x := (le_div_iff₀ hDx).mpr (by linarith)
  rw [hcx, min_eq_left hquot, max_eq_right hlohi]

/-- A negative quadratic remainder and a positive cubic denominator select
the eventual obstacle of the literal clamp. The sign of the first nonzero
constant or linear coefficient takes precedence; double cancellation gives
the upper obstacle. Denominator positivity is derived from its cubic limit. -/
theorem eventually_eq_obstacle_of_negative_quadratic_remainder
    {H D K : ℝ → ℝ} {lo hi h0 h1 A δ : ℝ}
    (hlohi : lo ≤ hi) (hA : A < 0) (hδ : 0 < δ)
    (hRem : Tendsto (fun x => (H x - h0 - h1 * x) / x ^ 2)
      (𝓝[>] (0 : ℝ)) (𝓝 A))
    (hD : Tendsto (fun x => D x / x ^ 3) (𝓝[>] (0 : ℝ)) (𝓝 δ))
    (hclip : ∀ᶠ x in 𝓝[>] (0 : ℝ), K x = max lo (min hi (-H x / D x))) :
    ((0 < h0 ∨ h0 = 0 ∧ 0 < h1) → ∀ᶠ x in 𝓝[>] (0 : ℝ), K x = lo) ∧
    ((h0 < 0 ∨ h0 = 0 ∧ h1 ≤ 0) → ∀ᶠ x in 𝓝[>] (0 : ℝ), K x = hi) := by
  have hxpos : ∀ᶠ x in 𝓝[>] (0 : ℝ), 0 < x := self_mem_nhdsWithin
  have hxlim : Tendsto (fun x : ℝ => x) (𝓝[>] (0 : ℝ)) (𝓝 0) :=
    tendsto_id.mono_left nhdsWithin_le_nhds
  have hDpos : ∀ᶠ x in 𝓝[>] (0 : ℝ), 0 < D x := by
    filter_upwards [hxpos, hD.eventually (lt_mem_nhds hδ)] with x hx hDx
    simpa only [zero_mul] using (lt_div_iff₀ (pow_pos hx 3)).mp hDx
  have hD0 : Tendsto D (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have ht : Tendsto (fun x => (D x / x ^ 3) * x ^ 3)
        (𝓝[>] (0 : ℝ)) (𝓝 0) := by
      simpa only [zero_pow (by decide : 3 ≠ 0), mul_zero] using hD.mul (hxlim.pow 3)
    apply ht.congr'
    filter_upwards [hxpos] with x hx
    field_simp [hx.ne']
  have hD1 : Tendsto (fun x => D x / x) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have ht : Tendsto (fun x => (D x / x ^ 3) * x ^ 2)
        (𝓝[>] (0 : ℝ)) (𝓝 0) := by
      simpa only [zero_pow (by decide : 2 ≠ 0), mul_zero] using hD.mul (hxlim.pow 2)
    apply ht.congr'
    filter_upwards [hxpos] with x hx
    field_simp [hx.ne']
  have hD2 : Tendsto (fun x => D x / x ^ 2) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have ht : Tendsto (fun x => (D x / x ^ 3) * x)
        (𝓝[>] (0 : ℝ)) (𝓝 0) := by
      simpa only [mul_zero] using hD.mul hxlim
    apply ht.congr'
    filter_upwards [hxpos] with x hx
    field_simp [hx.ne']
  have hH0 : Tendsto H (𝓝[>] (0 : ℝ)) (𝓝 h0) := by
    have ht : Tendsto
        (fun x => (h1 * x + ((H x - h0 - h1 * x) / x ^ 2) * x ^ 2) + h0)
        (𝓝[>] (0 : ℝ)) (𝓝 h0) := by
      simpa only [zero_pow (by decide : 2 ≠ 0), mul_zero, zero_add] using
        ((hxlim.const_mul h1).add (hRem.mul (hxlim.pow 2))).add_const h0
    apply ht.congr'
    filter_upwards [hxpos] with x hx
    field_simp [hx.ne']
    ring
  have hH1 (hz : h0 = 0) :
      Tendsto (fun x => H x / x) (𝓝[>] (0 : ℝ)) (𝓝 h1) := by
    have ht : Tendsto (fun x => ((H x - h0 - h1 * x) / x ^ 2) * x + h1)
        (𝓝[>] (0 : ℝ)) (𝓝 h1) := by
      simpa only [mul_zero, zero_add] using (hRem.mul hxlim).add_const h1
    apply ht.congr'
    filter_upwards [hxpos] with x hx
    rw [hz]
    field_simp [hx.ne']
    ring
  have hH2 (hz0 : h0 = 0) (hz1 : h1 = 0) :
      Tendsto (fun x => H x / x ^ 2) (𝓝[>] (0 : ℝ)) (𝓝 A) := by
    simpa only [hz0, hz1, zero_mul, sub_zero] using hRem
  have hOne : ∀ᶠ x in 𝓝[>] (0 : ℝ), 0 < (1 : ℝ) :=
    Eventually.of_forall fun _ => zero_lt_one
  constructor
  · rintro (hh0 | ⟨hh0, hh1⟩)
    · exact lower_obstacle_of_scaled_limits (w := fun _ => 1) hh0 hOne
        (by simpa only [div_one] using hH0) (by simpa only [div_one] using hD0) hDpos hclip
    · exact lower_obstacle_of_scaled_limits hh1 hxpos (hH1 hh0) hD1 hDpos hclip
  · rintro (hh0 | ⟨hh0, hh1⟩)
    · exact upper_obstacle_of_scaled_limits (w := fun _ => 1) hlohi hh0 hOne
        (by simpa only [div_one] using hH0) (by simpa only [div_one] using hD0) hDpos hclip
    · rcases lt_or_eq_of_le hh1 with hh1 | hh1
      · exact upper_obstacle_of_scaled_limits hlohi hh1 hxpos (hH1 hh0) hD1 hDpos hclip
      · exact upper_obstacle_of_scaled_limits hlohi hA
          (hxpos.mono fun _ hx => sq_pos_of_pos hx) (hH2 hh0 hh1) hD2 hDpos hclip

end RicciFlowSharpEstimate.Analysis
