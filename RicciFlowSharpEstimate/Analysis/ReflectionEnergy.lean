/-
Copyright (c) 2026 Ziyang Qin. All rights reserved.
No license is granted by this file.
Authors: Ziyang Qin
-/
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Hemisphere error and reflection energy

Errors against a common hemisphere reference control the full reflection error.
The reference is extended evenly by composition with absolute value; no symmetry
hypothesis is imposed on the original function. Averaging a function with its
reflection reduces its squared error by the exact factor one quarter.
-/

namespace RicciFlowSharpEstimate.Analysis

open Set

private theorem integral_split_reflection (f : ℝ → ℝ)
    (hf : ContinuousOn f (Icc (-1) 1)) :
    (∫ v in (-1 : ℝ)..1, f v) =
      (∫ v in (0 : ℝ)..1, f v) + (∫ v in (0 : ℝ)..1, f (-v)) := by
  have hl : IntervalIntegrable f MeasureTheory.volume (-1) 0 := by
    apply ContinuousOn.intervalIntegrable_of_Icc (by norm_num)
    exact hf.mono (fun v hv => ⟨hv.1, hv.2.trans zero_le_one⟩)
  have hr : IntervalIntegrable f MeasureTheory.volume 0 1 := by
    apply ContinuousOn.intervalIntegrable_of_Icc zero_le_one
    exact hf.mono (fun v hv => ⟨(by linarith [hv.1]), hv.2⟩)
  have hneg : (∫ v in (0 : ℝ)..1, f (-v)) = ∫ v in (-1 : ℝ)..0, f v := by
    simpa only [neg_zero] using (intervalIntegral.integral_comp_neg f (a := 0) (b := 1))
  calc
    (∫ v in (-1 : ℝ)..1, f v) =
        (∫ v in (-1 : ℝ)..0, f v) + (∫ v in (0 : ℝ)..1, f v) :=
      (intervalIntegral.integral_add_adjacent_intervals hl hr).symm
    _ = _ := by rw [← hneg, add_comm]

/-- The error against an even extension is exactly the sum of the two actual hemisphere errors. -/
theorem integral_evenExtension_error_sq_eq (h e : ℝ → ℝ)
    (hh : ContinuousOn h (Icc (-1) 1)) (he : ContinuousOn e (Icc 0 1)) :
    (∫ v in (-1 : ℝ)..1, (h v - e |v|) ^ 2) =
      (∫ v in (0 : ℝ)..1, (h v - e v) ^ 2) +
        (∫ v in (0 : ℝ)..1, (h (-v) - e v) ^ 2) := by
  have heven : ContinuousOn (fun v : ℝ => e |v|) (Icc (-1) 1) :=
    he.comp continuous_abs.continuousOn (fun v hv => ⟨abs_nonneg v, abs_le.mpr hv⟩)
  have herr : ContinuousOn (fun v : ℝ => (h v - e |v|) ^ 2) (Icc (-1) 1) := by
    simpa only [Pi.pow_apply, Pi.sub_apply] using! (hh.sub heven).pow 2
  rw [integral_split_reflection _ herr]
  congr 1
  · apply intervalIntegral.integral_congr
    intro v hv
    rw [uIcc_of_le zero_le_one] at hv
    dsimp only
    rw [abs_of_nonneg hv.1]
  · apply intervalIntegral.integral_congr
    intro v hv
    rw [uIcc_of_le zero_le_one] at hv
    dsimp only
    rw [abs_neg, abs_of_nonneg hv.1]

/-- Two hemisphere errors against one reference control reflection error without a symmetry
assumption on either input function. -/
theorem integral_reflection_error_sq_le (h e : ℝ → ℝ)
    (hh : ContinuousOn h (Icc (-1) 1)) (he : ContinuousOn e (Icc 0 1)) :
    (∫ v in (-1 : ℝ)..1, (h v - h (-v)) ^ 2) ≤
      4 * ((∫ v in (0 : ℝ)..1, (h v - e v) ^ 2) +
        (∫ v in (0 : ℝ)..1, (h (-v) - e v) ^ 2)) := by
  have hn : ContinuousOn (fun v : ℝ => h (-v)) (Icc (-1) 1) := by
    apply hh.comp continuous_neg.continuousOn
    intro v hv
    constructor <;> linarith [hv.1, hv.2]
  have hh0 : ContinuousOn h (Icc 0 1) :=
    hh.mono (fun v hv => ⟨(by linarith [hv.1]), hv.2⟩)
  have hn0 : ContinuousOn (fun v : ℝ => h (-v)) (Icc 0 1) :=
    hn.mono (fun v hv => ⟨(by linarith [hv.1]), hv.2⟩)
  have ha : ContinuousOn (fun v : ℝ => (h v - e v) ^ 2) (Icc 0 1) := by
    simpa only [Pi.pow_apply, Pi.sub_apply] using! (hh0.sub he).pow 2
  have hb : ContinuousOn (fun v : ℝ => (h (-v) - e v) ^ 2) (Icc 0 1) := by
    simpa only [Pi.pow_apply, Pi.sub_apply] using! (hn0.sub he).pow 2
  have hr : ContinuousOn (fun v : ℝ => (h v - h (-v)) ^ 2) (Icc 0 1) := by
    simpa only [Pi.pow_apply, Pi.sub_apply] using! (hh0.sub hn0).pow 2
  have hR : ContinuousOn (fun v : ℝ => (h v - h (-v)) ^ 2) (Icc (-1) 1) := by
    simpa only [Pi.pow_apply, Pi.sub_apply] using! (hh.sub hn).pow 2
  have hsum : ContinuousOn
      (fun v : ℝ => 2 * ((h v - e v) ^ 2 + (h (-v) - e v) ^ 2)) (Icc 0 1) := by
    simpa only [Pi.add_apply] using! (ha.add hb).const_mul 2
  have hfull : (∫ v in (-1 : ℝ)..1, (h v - h (-v)) ^ 2) =
      2 * (∫ v in (0 : ℝ)..1, (h v - h (-v)) ^ 2) := by
    rw [integral_split_reflection _ hR]
    have hswap : (∫ v in (0 : ℝ)..1, (h (-v) - h (-(-v))) ^ 2) =
        ∫ v in (0 : ℝ)..1, (h v - h (-v)) ^ 2 := by
      apply intervalIntegral.integral_congr
      intro v _
      simp only [neg_neg]
      ring
    rw [hswap]
    ring
  have hhalf : (∫ v in (0 : ℝ)..1, (h v - h (-v)) ^ 2) ≤
      2 * ((∫ v in (0 : ℝ)..1, (h v - e v) ^ 2) +
        (∫ v in (0 : ℝ)..1, (h (-v) - e v) ^ 2)) := by
    calc
      (∫ v in (0 : ℝ)..1, (h v - h (-v)) ^ 2) ≤
          ∫ v in (0 : ℝ)..1, 2 * ((h v - e v) ^ 2 + (h (-v) - e v) ^ 2) := by
        apply intervalIntegral.integral_mono_on zero_le_one
          (hr.intervalIntegrable_of_Icc zero_le_one)
          (hsum.intervalIntegrable_of_Icc zero_le_one)
        intro v _
        nlinarith only [sq_nonneg (h v + h (-v) - 2 * e v)]
      _ = _ := by
        rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_add
          (ha.intervalIntegrable_of_Icc zero_le_one) (hb.intervalIntegrable_of_Icc zero_le_one)]
  rw [hfull]
  linarith only [hhalf]

/-- The squared error of symmetrization is exactly one quarter of the squared reflection error.
The algebraic integral identity requires no regularity hypothesis. -/
theorem integral_symmetrization_error_sq_eq (h : ℝ → ℝ) :
    (∫ v in (-1 : ℝ)..1, (h v - (h v + h (-v)) / 2) ^ 2) =
      (1 / 4 : ℝ) * (∫ v in (-1 : ℝ)..1, (h v - h (-v)) ^ 2) := by
  calc
    (∫ v in (-1 : ℝ)..1, (h v - (h v + h (-v)) / 2) ^ 2) =
        ∫ v in (-1 : ℝ)..1, (1 / 4 : ℝ) * (h v - h (-v)) ^ 2 := by
      apply intervalIntegral.integral_congr
      intro v _
      ring
    _ = _ := intervalIntegral.integral_const_mul _ _

end RicciFlowSharpEstimate.Analysis
