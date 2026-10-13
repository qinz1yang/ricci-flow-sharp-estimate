/-
Copyright (c) 2026 Ziyang Qin. All rights reserved.
No license is granted by this file.
Authors: Ziyang Qin
-/
import RicciFlowSharpEstimate.Geometry.AreaProfile

/-!
# Relative stability of the actual area warp at both poles

Integrable curvature coefficients with equal zeroth and first moments have
warping differences controlled by the product of the two pole distances.
The right-pole formula follows from both moment cancellations in the original
triangular curvature primitive. No continuity of curvature is required.
-/

noncomputable section

namespace RicciFlowSharpEstimate.Geometry.AreaProfile

open MeasureTheory Set

private theorem area_intervalIntegrable_of_integrableOn
    (u : ℝ → ℝ) (hu : IntegrableOn u (Ioo (0 : ℝ) 1)) :
    IntervalIntegrable u volume 0 1 :=
  (intervalIntegrable_iff_integrableOn_Ioo_of_le (by norm_num : (0 : ℝ) ≤ 1)).2 hu

private theorem area_intervalIntegrable_subinterval
    (u : ℝ → ℝ) (hu : IntervalIntegrable u volume 0 1)
    (a b : ℝ) (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1) :
    IntervalIntegrable u volume a b := by
  apply hu.mono_set
  rw [uIcc_of_le hab, uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
  exact Icc_subset_Icc ha hb

private theorem area_abs_integral_weight_subinterval_le
    (u w : ℝ → ℝ) (hu : IntervalIntegrable u volume 0 1)
    (hw : Continuous w) (a b B : ℝ)
    (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1) (hB : 0 ≤ B)
    (hbound : ∀ s ∈ Icc a b, |w s| ≤ B) :
    |∫ s in a..b, w s * u s| ≤ B * ∫ s in (0 : ℝ)..1, |u s| := by
  have huab := area_intervalIntegrable_subinterval u hu a b ha hab hb
  have huw : IntervalIntegrable (fun s => w s * u s) volume a b :=
    huab.continuousOn_mul hw.continuousOn
  calc
    |∫ s in a..b, w s * u s| ≤ ∫ s in a..b, |w s * u s| :=
      intervalIntegral.abs_integral_le_integral_abs hab
    _ ≤ ∫ s in a..b, B * |u s| := by
      apply intervalIntegral.integral_mono_on hab huw.abs (huab.abs.const_mul B)
      intro s hs
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_right (hbound s hs) (abs_nonneg _)
    _ = B * ∫ s in a..b, |u s| := intervalIntegral.integral_const_mul B _
    _ ≤ B * ∫ s in (0 : ℝ)..1, |u s| := by
      apply mul_le_mul_of_nonneg_left _ hB
      exact intervalIntegral.integral_mono_interval ha hab hb
        (Filter.Eventually.of_forall fun _ => abs_nonneg _) hu.abs

private theorem area_warp_sub_eq_integral_left
    (K L : ℝ → ℝ) (hK : IntervalIntegrable K volume 0 1)
    (hL : IntervalIntegrable L volume 0 1)
    (x : ℝ) (hx : x ∈ Icc (0 : ℝ) 1) :
    warp K x - warp L x =
      -2 * ∫ s in (0 : ℝ)..x, (x - s) * (K s - L s) := by
  have hiK : IntervalIntegrable (fun s : ℝ => (x - s) * K s) volume 0 x :=
    (area_intervalIntegrable_subinterval K hK 0 x le_rfl hx.1 hx.2).continuousOn_mul
      (continuous_const.sub continuous_id).continuousOn
  have hiL : IntervalIntegrable (fun s : ℝ => (x - s) * L s) volume 0 x :=
    (area_intervalIntegrable_subinterval L hL 0 x le_rfl hx.1 hx.2).continuousOn_mul
      (continuous_const.sub continuous_id).continuousOn
  simp only [mul_sub, intervalIntegral.integral_sub hiK hiL, warp]
  ring

/-- Equality of both curvature moments gives the exact right-pole formula
for the difference of the original warping primitives. -/
theorem warp_sub_eq_integral_right_of_moments
    (K L : ℝ → ℝ)
    (hK : IntegrableOn K (Ioo (0 : ℝ) 1))
    (hL : IntegrableOn L (Ioo (0 : ℝ) 1))
    (hzero : (∫ s in (0 : ℝ)..1, K s) = ∫ s in (0 : ℝ)..1, L s)
    (hfirst : (∫ s in (0 : ℝ)..1, s * K s) = ∫ s in (0 : ℝ)..1, s * L s)
    (x : ℝ) (hx : x ∈ Icc (0 : ℝ) 1) :
    warp K x - warp L x =
      -2 * ∫ s in x..1, (s - x) * (K s - L s) := by
  have hiK := area_intervalIntegrable_of_integrableOn K hK
  have hiL := area_intervalIntegrable_of_integrableOn L hL
  have hu : IntervalIntegrable (fun s => K s - L s) volume 0 1 := hiK.sub hiL
  have hiKs : IntervalIntegrable (fun s : ℝ => s * K s) volume 0 1 :=
    hiK.continuousOn_mul continuous_id.continuousOn
  have hiLs : IntervalIntegrable (fun s : ℝ => s * L s) volume 0 1 :=
    hiL.continuousOn_mul continuous_id.continuousOn
  have hzerod : (∫ s in (0 : ℝ)..1, K s - L s) = 0 := by
    rw [intervalIntegral.integral_sub hiK hiL, hzero, sub_self]
  have hfirstd : (∫ s in (0 : ℝ)..1, s * (K s - L s)) = 0 := by
    simp only [mul_sub, intervalIntegral.integral_sub hiKs hiLs, hfirst, sub_self]
  have htotal : (∫ s in (0 : ℝ)..1, (x - s) * (K s - L s)) = 0 := by
    calc
      _ = ∫ s in (0 : ℝ)..1, x * (K s - L s) - s * (K s - L s) := by
        apply intervalIntegral.integral_congr
        intro s _
        ring
      _ = x * (∫ s in (0 : ℝ)..1, K s - L s) -
          ∫ s in (0 : ℝ)..1, s * (K s - L s) := by
        have hi : IntervalIntegrable (fun s : ℝ => s * (K s - L s)) volume 0 1 :=
          hu.continuousOn_mul continuous_id.continuousOn
        rw [intervalIntegral.integral_sub (hu.const_mul x) hi,
          intervalIntegral.integral_const_mul]
      _ = 0 := by rw [hzerod, hfirstd]; ring
  have htri : IntervalIntegrable (fun s => (x - s) * (K s - L s)) volume 0 1 :=
    hu.continuousOn_mul (continuous_const.sub continuous_id).continuousOn
  have hsplit := intervalIntegral.integral_add_adjacent_intervals
    (area_intervalIntegrable_subinterval _ htri 0 x le_rfl hx.1 hx.2)
    (area_intervalIntegrable_subinterval _ htri x 1 hx.1 hx.2 le_rfl)
  have hright : (∫ s in x..1, (x - s) * (K s - L s)) =
      -(∫ s in x..1, (s - x) * (K s - L s)) := by
    calc
      _ = ∫ s in x..1, -((s - x) * (K s - L s)) := by
        apply intervalIntegral.integral_congr
        intro s _
        ring
      _ = _ := intervalIntegral.integral_neg
  rw [htotal, hright] at hsplit
  rw [area_warp_sub_eq_integral_left K L hiK hiL x hx]
  linarith

/-- Equal curvature moments control the actual warp relative to both pole
distances, even for merely integrable curvature coefficients. -/
theorem abs_warp_sub_le_relative_integral_abs
    (K L : ℝ → ℝ)
    (hK : IntegrableOn K (Ioo (0 : ℝ) 1))
    (hL : IntegrableOn L (Ioo (0 : ℝ) 1))
    (hzero : (∫ s in (0 : ℝ)..1, K s) = ∫ s in (0 : ℝ)..1, L s)
    (hfirst : (∫ s in (0 : ℝ)..1, s * K s) = ∫ s in (0 : ℝ)..1, s * L s)
    (x : ℝ) (hx : x ∈ Icc (0 : ℝ) 1) :
    |warp K x - warp L x| ≤
      4 * x * (1 - x) * ∫ s in (0 : ℝ)..1, |K s - L s| := by
  have hiK := area_intervalIntegrable_of_integrableOn K hK
  have hiL := area_intervalIntegrable_of_integrableOn L hL
  have hu : IntervalIntegrable (fun s => K s - L s) volume 0 1 := hiK.sub hiL
  have hleft : |warp K x - warp L x| ≤
      2 * x * ∫ s in (0 : ℝ)..1, |K s - L s| := by
    rw [area_warp_sub_eq_integral_left K L hiK hiL x hx, abs_mul]
    norm_num only [abs_neg, abs_of_nonneg (show (0 : ℝ) ≤ 2 by norm_num)]
    have hb := area_abs_integral_weight_subinterval_le (fun s => K s - L s)
      (fun s => x - s) hu (continuous_const.sub continuous_id)
      0 x x le_rfl hx.1 hx.2 hx.1 (by
        intro s hs
        rw [abs_of_nonneg (sub_nonneg.mpr hs.2)]
        linarith [hs.1])
    calc
      _ ≤ 2 * (x * ∫ s in (0 : ℝ)..1, |K s - L s|) :=
        mul_le_mul_of_nonneg_left hb (by norm_num)
      _ = _ := by ring
  have hright : |warp K x - warp L x| ≤
      2 * (1 - x) * ∫ s in (0 : ℝ)..1, |K s - L s| := by
    rw [warp_sub_eq_integral_right_of_moments K L hK hL hzero hfirst x hx, abs_mul]
    norm_num only [abs_neg, abs_of_nonneg (show (0 : ℝ) ≤ 2 by norm_num)]
    have hb := area_abs_integral_weight_subinterval_le (fun s => K s - L s)
      (fun s => s - x) hu (continuous_id.sub continuous_const)
      x 1 (1 - x) hx.1 hx.2 le_rfl (sub_nonneg.mpr hx.2) (by
        intro s hs
        rw [abs_of_nonneg (sub_nonneg.mpr hs.1)]
        linarith [hs.2])
    calc
      _ ≤ 2 * ((1 - x) * ∫ s in (0 : ℝ)..1, |K s - L s|) :=
        mul_le_mul_of_nonneg_left hb (by norm_num)
      _ = _ := by ring
  calc
    |warp K x - warp L x| =
        (1 - x) * |warp K x - warp L x| + x * |warp K x - warp L x| := by ring
    _ ≤ (1 - x) * (2 * x * ∫ s in (0 : ℝ)..1, |K s - L s|) +
        x * (2 * (1 - x) * ∫ s in (0 : ℝ)..1, |K s - L s|) :=
      add_le_add (mul_le_mul_of_nonneg_left hleft (sub_nonneg.mpr hx.2))
        (mul_le_mul_of_nonneg_left hright hx.1)
    _ = _ := by ring

/-- The actual first curvature primitive is Lipschitz in the curvature
`L¹` distance under integrability alone. -/
theorem abs_warpSlope_sub_le_integral_abs_of_integrableOn
    (K L : ℝ → ℝ)
    (hK : IntegrableOn K (Ioo (0 : ℝ) 1))
    (hL : IntegrableOn L (Ioo (0 : ℝ) 1))
    (x : ℝ) (hx : x ∈ Icc (0 : ℝ) 1) :
    |warpSlope K x - warpSlope L x| ≤
      2 * ∫ s in (0 : ℝ)..1, |K s - L s| := by
  have hiK := area_intervalIntegrable_of_integrableOn K hK
  have hiL := area_intervalIntegrable_of_integrableOn L hL
  have hu : IntervalIntegrable (fun s => K s - L s) volume 0 1 := hiK.sub hiL
  have heq : warpSlope K x - warpSlope L x =
      -2 * ∫ s in (0 : ℝ)..x, K s - L s := by
    rw [intervalIntegral.integral_sub
      (area_intervalIntegrable_subinterval K hiK 0 x le_rfl hx.1 hx.2)
      (area_intervalIntegrable_subinterval L hiL 0 x le_rfl hx.1 hx.2)]
    simp only [warpSlope]
    ring
  have hb : |∫ s in (0 : ℝ)..x, K s - L s| ≤
      ∫ s in (0 : ℝ)..1, |K s - L s| := by
    simpa only [one_mul] using
      area_abs_integral_weight_subinterval_le (fun s => K s - L s)
        (fun _ => 1) hu continuous_const 0 x 1 le_rfl hx.1 hx.2
        (by norm_num) (by intro s hs; norm_num)
  rw [heq, abs_mul]
  norm_num only [abs_neg, abs_of_nonneg (show (0 : ℝ) ≤ 2 by norm_num)]
  exact mul_le_mul_of_nonneg_left hb (by norm_num)

end RicciFlowSharpEstimate.Geometry.AreaProfile
