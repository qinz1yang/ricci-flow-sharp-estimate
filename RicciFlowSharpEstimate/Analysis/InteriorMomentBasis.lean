/-
Copyright (c) 2026 Ziyang Qin. All rights reserved.
No license is granted by this file.
Authors: Ziyang Qin
-/
import RicciFlowSharpEstimate.Analysis.PositiveSmoothBump
import Mathlib.Analysis.Normed.Group.Bounded

/-!
# Interior smooth moment basis

Two smooth compactly supported functions in the open unit interval give the
standard basis for the zeroth and first integral moments.
-/

noncomputable section

open Set Function MeasureTheory
open scoped ContDiff Topology

namespace RicciFlowSharpEstimate.Analysis

/-- There are fixed smooth interior corrections for the zeroth and first
moments, with a common positive uniform bound. -/
theorem exists_contDiff_interior_moment_basis :
    ∃ (ψ0 ψ1 : ℝ → ℝ) (B : ℝ),
      0 < B ∧
      ContDiff ℝ ∞ ψ0 ∧ ContDiff ℝ ∞ ψ1 ∧
      HasCompactSupport ψ0 ∧ HasCompactSupport ψ1 ∧
      tsupport ψ0 ⊆ Ioo (0 : ℝ) 1 ∧ tsupport ψ1 ⊆ Ioo (0 : ℝ) 1 ∧
      (∀ x, |ψ0 x| ≤ B ∧ |ψ1 x| ≤ B) ∧
      (∫ x in (0 : ℝ)..1, ψ0 x) = 1 ∧
      (∫ x in (0 : ℝ)..1, x * ψ0 x) = 0 ∧
      (∫ x in (0 : ℝ)..1, ψ1 x) = 0 ∧
      (∫ x in (0 : ℝ)..1, x * ψ1 x) = 1 := by
  obtain ⟨χ0, hχ0smooth, hχ0compact, hχ0support, hχ0box, hχ0mass⟩ :=
    exists_contDiff_nonneg_tsupport_subset_integral_mul_pos
      (fun _ : ℝ => 1) 0 1 (1 / 8) (3 / 8)
      continuous_const.continuousOn (by norm_num) (by norm_num) (by norm_num)
      (by intro x hx; norm_num)
  obtain ⟨χ1, hχ1smooth, hχ1compact, hχ1support, hχ1box, hχ1mass⟩ :=
    exists_contDiff_nonneg_tsupport_subset_integral_mul_pos
      (fun _ : ℝ => 1) 0 1 (5 / 8) (7 / 8)
      continuous_const.continuousOn (by norm_num) (by norm_num) (by norm_num)
      (by intro x hx; norm_num)
  let m0 : ℝ := ∫ x in (0 : ℝ)..1, χ0 x
  let m1 : ℝ := ∫ x in (0 : ℝ)..1, χ1 x
  let n0 : ℝ := ∫ x in (0 : ℝ)..1, x * χ0 x
  let n1 : ℝ := ∫ x in (0 : ℝ)..1, x * χ1 x
  have hm0 : 0 < m0 := by simpa only [m0, one_mul] using hχ0mass
  have hm1 : 0 < m1 := by simpa only [m1, one_mul] using hχ1mass
  have hi0 : IntervalIntegrable χ0 volume 0 1 :=
    hχ0smooth.continuous.intervalIntegrable 0 1
  have hi1 : IntervalIntegrable χ1 volume 0 1 :=
    hχ1smooth.continuous.intervalIntegrable 0 1
  have hiw0 : IntervalIntegrable (fun x : ℝ => x * χ0 x) volume 0 1 :=
    (continuous_id.mul hχ0smooth.continuous).intervalIntegrable 0 1
  have hiw1 : IntervalIntegrable (fun x : ℝ => x * χ1 x) volume 0 1 :=
    (continuous_id.mul hχ1smooth.continuous).intervalIntegrable 0 1
  have hn0 : n0 ≤ (3 / 8 : ℝ) * m0 := by
    have hpoint : ∀ x ∈ Icc (0 : ℝ) 1,
        x * χ0 x ≤ (3 / 8 : ℝ) * χ0 x := by
      intro x _
      by_cases hx : χ0 x = 0
      · simp only [hx, mul_zero, le_refl]
      · have hxs := hχ0support (subset_tsupport χ0 (mem_support.mpr hx))
        exact mul_le_mul_of_nonneg_right hxs.2.le (hχ0box x).1
    have h := intervalIntegral.integral_mono_on zero_le_one
      hiw0 (hi0.const_mul (3 / 8)) hpoint
    simpa only [intervalIntegral.integral_const_mul, m0, n0] using h
  have hn1 : (5 / 8 : ℝ) * m1 ≤ n1 := by
    have hpoint : ∀ x ∈ Icc (0 : ℝ) 1,
        (5 / 8 : ℝ) * χ1 x ≤ x * χ1 x := by
      intro x _
      by_cases hx : χ1 x = 0
      · simp only [hx, mul_zero, le_refl]
      · have hxs := hχ1support (subset_tsupport χ1 (mem_support.mpr hx))
        exact mul_le_mul_of_nonneg_right hxs.1.le (hχ1box x).1
    have h := intervalIntegral.integral_mono_on zero_le_one
      (hi1.const_mul (5 / 8)) hiw1 hpoint
    simpa only [intervalIntegral.integral_const_mul, m1, n1] using h
  let d : ℝ := m0 * n1 - m1 * n0
  have hd : 0 < d := by
    have hupper := mul_le_mul_of_nonneg_left hn0 hm1.le
    have hlower := mul_le_mul_of_nonneg_left hn1 hm0.le
    have hmass := mul_pos hm0 hm1
    dsimp only [d]
    nlinarith
  let ψ0 : ℝ → ℝ := fun x => (n1 * χ0 x - n0 * χ1 x) / d
  let ψ1 : ℝ → ℝ := fun x => (m0 * χ1 x - m1 * χ0 x) / d
  have hψ0smooth : ContDiff ℝ ∞ ψ0 :=
    (((contDiff_const (c := n1)).mul hχ0smooth).sub
      ((contDiff_const (c := n0)).mul hχ1smooth)).div_const d
  have hψ1smooth : ContDiff ℝ ∞ ψ1 :=
    (((contDiff_const (c := m0)).mul hχ1smooth).sub
      ((contDiff_const (c := m1)).mul hχ0smooth)).div_const d
  have hψ0union : tsupport ψ0 ⊆ tsupport χ0 ∪ tsupport χ1 :=
    tsupport_binop_subset (fun u v : ℝ => (n1 * u - n0 * v) / d)
      (by simp) χ0 χ1
  have hψ1union : tsupport ψ1 ⊆ tsupport χ0 ∪ tsupport χ1 :=
    tsupport_binop_subset (fun u v : ℝ => (m0 * v - m1 * u) / d)
      (by simp) χ0 χ1
  have hcompactUnion : IsCompact (tsupport χ0 ∪ tsupport χ1) :=
    hχ0compact.isCompact.union hχ1compact.isCompact
  have hψ0compact : HasCompactSupport ψ0 :=
    hcompactUnion.of_isClosed_subset (isClosed_tsupport ψ0) hψ0union
  have hψ1compact : HasCompactSupport ψ1 :=
    hcompactUnion.of_isClosed_subset (isClosed_tsupport ψ1) hψ1union
  have hsupportUnion : tsupport χ0 ∪ tsupport χ1 ⊆ Ioo (0 : ℝ) 1 := by
    intro x hx
    rcases hx with hx | hx
    · obtain ⟨hl, hu⟩ := hχ0support hx
      constructor <;> linarith
    · obtain ⟨hl, hu⟩ := hχ1support hx
      constructor <;> linarith
  obtain ⟨B, hBpos, hB⟩ :=
    ((hψ0compact.isCompact_range hψ0smooth.continuous).union
      (hψ1compact.isCompact_range hψ1smooth.continuous)).isBounded.exists_pos_norm_le
  have hbound : ∀ x, |ψ0 x| ≤ B ∧ |ψ1 x| ≤ B := by
    intro x
    constructor
    · simpa only [Real.norm_eq_abs] using hB (ψ0 x) (Or.inl (mem_range_self x))
    · simpa only [Real.norm_eq_abs] using hB (ψ1 x) (Or.inr (mem_range_self x))
  have hlin (f g : ℝ → ℝ)
      (hf : IntervalIntegrable f volume 0 1) (hg : IntervalIntegrable g volume 0 1)
      (a b : ℝ) :
      (∫ x in (0 : ℝ)..1, (a * f x - b * g x) / d) =
        (a * (∫ x in (0 : ℝ)..1, f x) - b * (∫ x in (0 : ℝ)..1, g x)) / d := by
    rw [intervalIntegral.integral_div,
      intervalIntegral.integral_sub (hf.const_mul a) (hg.const_mul b),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
  refine ⟨ψ0, ψ1, B, hBpos, hψ0smooth, hψ1smooth, hψ0compact, hψ1compact,
    hψ0union.trans hsupportUnion, hψ1union.trans hsupportUnion, hbound, ?_, ?_, ?_, ?_⟩
  · calc
      (∫ x in (0 : ℝ)..1, ψ0 x) = (n1 * m0 - n0 * m1) / d :=
        hlin χ0 χ1 hi0 hi1 n1 n0
      _ = d / d := by congr 1; dsimp only [d]; ring
      _ = 1 := div_self hd.ne'
  · calc
      (∫ x in (0 : ℝ)..1, x * ψ0 x) =
          ∫ x in (0 : ℝ)..1, (n1 * (x * χ0 x) - n0 * (x * χ1 x)) / d := by
        apply intervalIntegral.integral_congr
        intro x _
        dsimp only [ψ0]
        ring
      _ = (n1 * n0 - n0 * n1) / d :=
        hlin (fun x => x * χ0 x) (fun x => x * χ1 x) hiw0 hiw1 n1 n0
      _ = 0 := by ring
  · calc
      (∫ x in (0 : ℝ)..1, ψ1 x) = (m0 * m1 - m1 * m0) / d :=
        hlin χ1 χ0 hi1 hi0 m0 m1
      _ = 0 := by ring
  · calc
      (∫ x in (0 : ℝ)..1, x * ψ1 x) =
          ∫ x in (0 : ℝ)..1, (m0 * (x * χ1 x) - m1 * (x * χ0 x)) / d := by
        apply intervalIntegral.integral_congr
        intro x _
        dsimp only [ψ1]
        ring
      _ = d / d :=
        hlin (fun x => x * χ1 x) (fun x => x * χ0 x) hiw1 hiw0 m0 m1
      _ = 1 := div_self hd.ne'

end RicciFlowSharpEstimate.Analysis
