/-
Copyright (c) 2026 Ziyang Qin. All rights reserved.
No license is granted by this file.
Authors: Ziyang Qin
-/
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Topology.Order.ProjIcc

/-!
# Extension of finite differentiability from a closed real interval

Continuous data extend by projection onto the interval. At each successor
order, extend the within derivative and integrate it, matching the value at
the left endpoint. Thus finite differentiability does not require a smooth
extension of the original finite-order data.
-/

noncomputable section

namespace RicciFlowSharpEstimate.Analysis

open Set MeasureTheory
open scoped ContDiff

/-- Integrating a globally C^n real function gains one derivative. -/
theorem integral_contDiff_succ (n : ℕ) (f : ℝ → ℝ)
    (hf : ContDiff ℝ n f) (a : ℝ) :
    ContDiff ℝ (n + 1 : ℕ) (fun x => ∫ t in a..x, f t) := by
  have hD (x : ℝ) : HasDerivAt (fun y => ∫ t in a..y, f t) (f x) x :=
    (hf.continuous.integral_hasStrictDerivAt a x).hasDerivAt
  have hderiv : deriv (fun x => ∫ t in a..x, f t) = f := by
    funext x
    exact (hD x).deriv
  change ContDiff ℝ ((n : ℕ∞ω) + 1) (fun x => ∫ t in a..x, f t)
  rw [contDiff_succ_iff_deriv]
  refine ⟨fun x => (hD x).differentiableAt, ?_, ?_⟩
  · simp
  · rw [hderiv]
    exact hf

/-- A C^n function on a nondegenerate closed real interval has a globally
C^n extension agreeing on the entire interval. This is a finite-order result;
the extension may depend on n. -/
theorem exists_contDiff_nat_extension_Icc (n : ℕ) (f : ℝ → ℝ)
    (a b : ℝ) (hab : a < b) (hf : ContDiffOn ℝ n f (Icc a b)) :
    ∃ F : ℝ → ℝ, ContDiff ℝ n F ∧ EqOn F f (Icc a b) := by
  induction n generalizing f with
  | zero =>
      let F : ℝ → ℝ := IccExtend hab.le (fun x : Icc a b => f x)
      have hFc : Continuous F := by
        apply continuous_IccExtend_iff.mpr
        exact continuousOn_iff_continuous_domRestrict.mp hf.continuousOn
      refine ⟨F, contDiff_zero.mpr hFc, ?_⟩
      intro x hx
      exact IccExtend_of_mem hab.le (fun y : Icc a b => f y) hx
  | succ n ih =>
      have hfn : ContDiffOn ℝ ((n : ℕ∞ω) + 1) f (Icc a b) := by
        simpa only [Nat.cast_add, Nat.cast_one] using hf
      have hq : ContDiffOn ℝ n (derivWithin f (Icc a b)) (Icc a b) :=
        ((contDiffOn_succ_iff_derivWithin (uniqueDiffOn_Icc hab)).mp hfn).2.2
      obtain ⟨Q, hQ, hQeq⟩ := ih (derivWithin f (Icc a b)) hq
      let F : ℝ → ℝ := fun x => f a + ∫ t in a..x, Q t
      have hF : ContDiff ℝ (n + 1 : ℕ) F :=
        contDiff_const.add (integral_contDiff_succ n Q hQ a)
      refine ⟨F, hF, ?_⟩
      intro x hx
      have hFTC : (∫ t in a..x, Q t) = f x - f a := by
        apply intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hx.1
          (hf.continuousOn.mono (Icc_subset_Icc le_rfl hx.2))
        · intro y hy
          have hyab : y ∈ Icc a b := ⟨hy.1.le, hy.2.le.trans hx.2⟩
          have hyb : y < b := hy.2.trans_le hx.2
          have hd : DifferentiableWithinAt ℝ f (Icc a b) y :=
            (hfn.differentiableOn (by simp)) y hyab
          rw [hQeq hyab]
          exact hd.hasDerivWithinAt.hasDerivAt (Icc_mem_nhds hy.1 hyb)
        · exact hQ.continuous.intervalIntegrable a x
      change f a + (∫ t in a..x, Q t) = f x
      rw [hFTC]
      ring

end RicciFlowSharpEstimate.Analysis
