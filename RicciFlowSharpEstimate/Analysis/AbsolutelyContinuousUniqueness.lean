/-
Copyright (c) 2026 Ziyang Qin. All rights reserved.
No license is granted by this file.
Authors: Ziyang Qin
-/
import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.ContDiff.Operations

/-! # Zero propagation for absolutely continuous differential inequalities -/

noncomputable section
namespace RicciFlowSharpEstimate.Analysis
open Set MeasureTheory Filter

private theorem ac_le_right_of_deriv_nonneg {f : ℝ → ℝ} {a b : ℝ}
    (hab : a ≤ b) (hf : AbsolutelyContinuousOnInterval f a b)
    (hd : ∀ᵐ x ∂volume, x ∈ Icc a b → 0 ≤ deriv f x) : f a ≤ f b := by
  have hi : 0 ≤ ∫ x in a..b, deriv f x := by
    apply intervalIntegral.integral_nonneg_of_ae_restrict hab
    filter_upwards [ae_restrict_of_ae hd, ae_restrict_mem measurableSet_Icc] with x hx hxI
    exact hx hxI
  rw [hf.integral_deriv_eq_sub] at hi
  linarith

/-- A nonnegative absolutely continuous function with bounded logarithmic
derivative cannot emerge from an interior or endpoint zero. The derivative
bound is almost everywhere; no everywhere differentiability is required. -/
theorem AbsolutelyContinuousOnInterval.eq_zero_of_abs_deriv_le
    {f : ℝ → ℝ} {a b c B : ℝ}
    (hf : AbsolutelyContinuousOnInterval f a b)
    (hn : ∀ x ∈ uIcc a b, 0 ≤ f x)
    (hd : ∀ᵐ x ∂volume, x ∈ uIcc a b → |deriv f x| ≤ B * f x)
    (hc : c ∈ uIcc a b) (hz : f c = 0) :
    ∀ x ∈ uIcc a b, f x = 0 := by
  intro x hx
  have hcx : uIcc c x ⊆ uIcc a b := uIcc_subset_uIcc hc hx
  have hac : AbsolutelyContinuousOnInterval f c x := hf.mono hcx
  have he (D : ℝ) : AbsolutelyContinuousOnInterval (fun t : ℝ => Real.exp (D * t)) c x := by
    exact ((Real.contDiff_exp.comp (contDiff_const.mul contDiff_id)).contDiffOn
      (n := 1)).absolutelyContinuousOnInterval
  have hdE (D t : ℝ) : HasDerivAt (fun y : ℝ => Real.exp (D * y))
      (Real.exp (D * t) * D) t := by
    convert ((hasDerivAt_id t).const_mul D).exp using 1 <;> simp [mul_comm]
  rcases le_total c x with hle | hle
  · have hfac := hac.fun_mul (he (-B))
    have hneg : ∀ᵐ t ∂volume, t ∈ Icc c x →
        0 ≤ deriv (fun y => -(f y * Real.exp (-B * y))) t := by
      filter_upwards [hd, hac.ae_differentiableAt] with t ht hdt htI
      have htU : t ∈ uIcc c x := by simpa only [uIcc_of_le hle] using htI
      have hb := (abs_le.mp (ht (hcx htU))).2
      have hder := ((hdt htU).hasDerivAt.fun_mul (hdE (-B) t)).fun_neg
      rw [hder.deriv]
      nlinarith [Real.exp_pos (-B * t)]
    have hi := ac_le_right_of_deriv_nonneg hle hfac.fun_neg hneg
    simp only [hz, zero_mul, neg_zero] at hi
    have hprod : f x * Real.exp (-B * x) ≤ 0 := by linarith
    exact le_antisymm (nonpos_of_mul_nonpos_left hprod (Real.exp_pos _)) (hn x hx)
  · have hfac := hac.fun_mul (he B)
    have hpos : ∀ᵐ t ∂volume, t ∈ Icc x c →
        0 ≤ deriv (fun y => f y * Real.exp (B * y)) t := by
      filter_upwards [hd, hac.ae_differentiableAt] with t ht hdt htI
      have htU : t ∈ uIcc c x := by simpa only [uIcc_of_ge hle] using htI
      have hb := (abs_le.mp (ht (hcx htU))).1
      have hder := (hdt htU).hasDerivAt.fun_mul (hdE B t)
      rw [hder.deriv]
      nlinarith [Real.exp_pos (B * t)]
    have hi := ac_le_right_of_deriv_nonneg hle hfac.symm hpos
    simp only [hz, zero_mul] at hi
    exact le_antisymm (nonpos_of_mul_nonpos_left hi (Real.exp_pos _)) (hn x hx)

end RicciFlowSharpEstimate.Analysis
