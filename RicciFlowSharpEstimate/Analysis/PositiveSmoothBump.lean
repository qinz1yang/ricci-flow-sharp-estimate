/-
Copyright (c) 2026 Ziyang Qin. All rights reserved.
No license is granted by this file.
Authors: Ziyang Qin
-/
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# Positive smooth test functions

A continuous positive weight has positive integral against a nonnegative smooth
function supported in any prescribed open subinterval.

Adapted from Ziyang Qin's historical positive smooth bump construction.
-/

noncomputable section

open Set Function
open scoped ContDiff Topology

namespace RicciFlowSharpEstimate.Analysis

/-- A continuous weight which is positive on an open subinterval has a
positive pairing with a nonnegative smooth function supported there. -/
theorem exists_contDiff_nonneg_tsupport_subset_integral_mul_pos
    (f : ℝ → ℝ) (a b l u : ℝ)
    (hf : ContinuousOn f (Icc a b))
    (hal : a ≤ l) (hlu : l < u) (hub : u ≤ b)
    (hfpos : ∀ x ∈ Ioo l u, 0 < f x) :
    ∃ χ : ℝ → ℝ,
      ContDiff ℝ ∞ χ ∧
      HasCompactSupport χ ∧
      tsupport χ ⊆ Ioo l u ∧
      (∀ x, χ x ∈ Icc (0 : ℝ) 1) ∧
      0 < ∫ x in a..b, f x * χ x := by
  let m : ℝ := (l + u) / 2
  have hm : m ∈ Ioo l u := by dsimp [m]; constructor <;> linarith
  obtain ⟨χ, hsupport, hcompact, hsmooth, hbox, hχm⟩ :=
    exists_contDiff_tsupport_subset (n := (⊤ : ℕ∞)) (isOpen_Ioo.mem_nhds hm)
  have hχbox : ∀ x, χ x ∈ Icc (0 : ℝ) 1 :=
    fun x => hbox (mem_range_self x)
  refine ⟨χ, hsmooth, hcompact, hsupport, hχbox, ?_⟩
  apply intervalIntegral.integral_pos (hal.trans_lt (hlu.trans_le hub))
    (hf.mul hsmooth.continuous.continuousOn)
  · intro x _
    change 0 ≤ f x * χ x
    by_cases hx : χ x = 0
    · simp only [hx, mul_zero, le_refl]
    · have hxmem : x ∈ Ioo l u :=
        hsupport (subset_tsupport χ (mem_support.mpr hx))
      exact mul_nonneg (hfpos x hxmem).le (hχbox x).1
  · refine ⟨m, ⟨hal.trans hm.1.le, hm.2.le.trans hub⟩, ?_⟩
    change 0 < f m * χ m
    rw [hχm, mul_one]
    exact hfpos m hm

end RicciFlowSharpEstimate.Analysis
