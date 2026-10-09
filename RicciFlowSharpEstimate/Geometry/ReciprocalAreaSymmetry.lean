/-
Copyright (c) 2026 Ziyang Qin. All rights reserved.
No license is granted by this file.
Authors: Ziyang Qin
-/
import RicciFlowSharpEstimate.Geometry.ReciprocalAreaGeometry

/-!
# Reflection and hemisphere monotonicity in reciprocal area coordinates

Even reciprocal profiles put the equator at half area. Their genuine physical
inverse transports reflection and reverses reciprocal-profile monotonicity on
each hemisphere through the actual normalized curvature.
-/

noncomputable section

namespace RicciFlowSharpEstimate.Geometry.ReciprocalArea

open MeasureTheory Set

/-- An even reciprocal profile reflects the actual normalized primitive about half area. -/
theorem coordinate_reflection (a : ℝ → ℝ) (ha : Continuous a)
    (hpos : ∀ v ∈ Icc (-1 : ℝ) 1, 0 < a v) (heven : Function.Even a) (v : ℝ) :
    coordinate a (-v) = 1 - coordinate a v := by
  have hflip : (∫ s in (-1 : ℝ)..(-v), a s) = ∫ s in v..1, a s := by
    calc
      (∫ s in (-1 : ℝ)..(-v), a s) = ∫ s in (-1 : ℝ)..(-v), a (-s) := by
        apply intervalIntegral.integral_congr
        intro s _
        exact (heven s).symm
      _ = ∫ s in v..1, a s := by
        simpa only [neg_neg] using
          intervalIntegral.integral_comp_neg (a := (-1 : ℝ)) (b := -v) a
  have hadd := intervalIntegral.integral_add_adjacent_intervals
    (ha.intervalIntegrable (-1) v (μ := volume)) (ha.intervalIntegrable v 1)
  change (∫ s in (-1 : ℝ)..v, a s) + (∫ s in v..1, a s) = length a at hadd
  rw [coordinate, coordinate, hflip]
  apply (div_eq_iff (length_pos a ha hpos).ne').mpr
  field_simp [(length_pos a ha hpos).ne']
  linarith

/-- An even profile places the physical equator at exactly half area. -/
theorem coordinate_zero (a : ℝ → ℝ) (ha : Continuous a)
    (hpos : ∀ v ∈ Icc (-1 : ℝ) 1, 0 < a v) (heven : Function.Even a) :
    coordinate a 0 = 1 / 2 := by
  have h := coordinate_reflection a ha hpos heven 0
  rw [neg_zero] at h
  linarith

/-- The genuine inverse sends half area to the physical equator. -/
theorem inverse_half (a : ℝ → ℝ) (ha : Continuous a)
    (hpos : ∀ v ∈ Icc (-1 : ℝ) 1, 0 < a v) (heven : Function.Even a) :
    inverse a (1 / 2) = 0 := by
  simpa only [coordinate_zero a ha hpos heven] using
    inverse_coordinate a ha hpos 0 (by norm_num)

/-- The actual physical inverse intertwines area and height reflection. -/
theorem inverse_reflection (a : ℝ → ℝ) (ha : Continuous a)
    (hpos : ∀ v ∈ Icc (-1 : ℝ) 1, 0 < a v) (heven : Function.Even a)
    (x : ℝ) (hx : x ∈ Icc (0 : ℝ) 1) : inverse a (1 - x) = -inverse a x := by
  have hv := inverse_mem a ha hpos x
  have hneg : -inverse a x ∈ Icc (-1 : ℝ) 1 := by
    constructor <;> linarith [hv.1, hv.2]
  have hcoord : coordinate a (-inverse a x) = 1 - x := by
    rw [coordinate_reflection a ha hpos heven, coordinate_inverse a ha hpos x hx]
  rw [← hcoord, inverse_coordinate a ha hpos (-inverse a x) hneg]

/-- The actual transported curvature is invariant under physical equatorial reflection. -/
theorem curvature_reflection (a : ℝ → ℝ) (ha : Continuous a)
    (hpos : ∀ v ∈ Icc (-1 : ℝ) 1, 0 < a v) (heven : Function.Even a)
    (x : ℝ) (hx : x ∈ Icc (0 : ℝ) 1) : curvature a (1 - x) = curvature a x := by
  rw [curvature, curvature, inverse_reflection a ha hpos heven x hx, heven]

/-- Increasing reciprocal curvature on the southern height hemisphere gives decreasing
actual curvature on the southern area hemisphere. -/
theorem curvature_antitoneOn_left (a : ℝ → ℝ) (ha : Continuous a)
    (hpos : ∀ v ∈ Icc (-1 : ℝ) 1, 0 < a v) (heven : Function.Even a)
    (hmono : MonotoneOn a (Icc (-1 : ℝ) 0)) :
    AntitoneOn (curvature a) (Icc (0 : ℝ) (1 / 2)) := by
  have hmonoInv := (inverse_strictMonoOn a ha hpos).monotoneOn
  have hleft : ∀ z ∈ Icc (0 : ℝ) (1 / 2), inverse a z ∈ Icc (-1 : ℝ) 0 := by
    intro z hz
    refine ⟨(inverse_mem a ha hpos z).1, ?_⟩
    have hz01 : z ∈ Icc (0 : ℝ) 1 := ⟨hz.1, by linarith [hz.2]⟩
    have h := hmonoInv hz01 (by norm_num : (1 / 2 : ℝ) ∈ Icc (0 : ℝ) 1) hz.2
    simpa only [inverse_half a ha hpos heven] using h
  intro x hx y hy hxy
  have hx01 : x ∈ Icc (0 : ℝ) 1 := ⟨hx.1, by linarith [hx.2]⟩
  have hy01 : y ∈ Icc (0 : ℝ) 1 := ⟨hy.1, by linarith [hy.2]⟩
  exact div_le_div_of_nonneg_left (length_pos a ha hpos).le
    (hpos _ (inverse_mem a ha hpos x))
    (hmono (hleft x hx) (hleft y hy) (hmonoInv hx01 hy01 hxy))

/-- Decreasing reciprocal curvature on the northern height hemisphere gives increasing
actual curvature on the northern area hemisphere. -/
theorem curvature_monotoneOn_right (a : ℝ → ℝ) (ha : Continuous a)
    (hpos : ∀ v ∈ Icc (-1 : ℝ) 1, 0 < a v) (heven : Function.Even a)
    (hanti : AntitoneOn a (Icc (0 : ℝ) 1)) :
    MonotoneOn (curvature a) (Icc (1 / 2 : ℝ) 1) := by
  have hmonoInv := (inverse_strictMonoOn a ha hpos).monotoneOn
  have hright : ∀ z ∈ Icc (1 / 2 : ℝ) 1, inverse a z ∈ Icc (0 : ℝ) 1 := by
    intro z hz
    refine ⟨?_, (inverse_mem a ha hpos z).2⟩
    have hz01 : z ∈ Icc (0 : ℝ) 1 := ⟨by linarith [hz.1], hz.2⟩
    have h := hmonoInv (by norm_num : (1 / 2 : ℝ) ∈ Icc (0 : ℝ) 1) hz01 hz.1
    simpa only [inverse_half a ha hpos heven] using h
  intro x hx y hy hxy
  have hx01 : x ∈ Icc (0 : ℝ) 1 := ⟨by linarith [hx.1], hx.2⟩
  have hy01 : y ∈ Icc (0 : ℝ) 1 := ⟨by linarith [hy.1], hy.2⟩
  exact div_le_div_of_nonneg_left (length_pos a ha hpos).le
    (hpos _ (inverse_mem a ha hpos y))
    (hanti (hright x hx) (hright y hy) (hmonoInv hx01 hy01 hxy))

end RicciFlowSharpEstimate.Geometry.ReciprocalArea
