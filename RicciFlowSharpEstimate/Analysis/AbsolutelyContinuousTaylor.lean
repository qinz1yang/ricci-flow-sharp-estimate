/-
Copyright (c) 2026 Ziyang Qin. All rights reserved.
No license is granted by this file.
Authors: Ziyang Qin
-/
import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-! # A second-order bound with an absolutely continuous first derivative -/

noncomputable section
namespace RicciFlowSharpEstimate.Analysis
open Set MeasureTheory Filter

private theorem ac_increment_bound {g : ℝ → ℝ} {a b D : ℝ}
    (hg : AbsolutelyContinuousOnInterval g a b)
    (hd : ∀ᵐ t ∂volume, t ∈ uIcc a b → |deriv g t| ≤ D) :
    |g b - g a| ≤ D * |b - a| := by
  rw [← hg.integral_deriv_eq_sub]
  have hi := intervalIntegral.norm_integral_le_of_norm_le_const_ae (f := deriv g)
    (hd.mono (fun t ht htI => by
      simpa only [Real.norm_eq_abs] using ht (uIoc_subset_uIcc htI)))
  simpa only [Real.norm_eq_abs] using hi

/-- The usual quadratic Taylor bound requires only absolute continuity of
the function and its genuine first derivative, with an a.e. second derivative
bound. The expansion point may be any point of the closed joining interval. -/
theorem AbsolutelyContinuousOnInterval.abs_sub_linear_le_of_deriv_bound
    {f g : ℝ → ℝ} {a b c x D : ℝ}
    (hf : AbsolutelyContinuousOnInterval f a b)
    (hg : AbsolutelyContinuousOnInterval g a b)
    (hfg : ∀ᵐ t ∂volume, t ∈ uIcc a b → HasDerivAt f (g t) t)
    (hd : ∀ᵐ t ∂volume, t ∈ uIcc a b → |deriv g t| ≤ D)
    (hc : c ∈ uIcc a b) (hx : x ∈ uIcc a b) :
    |f x - f c - g c * (x - c)| ≤ D / 2 * (x - c) ^ 2 := by
  have hsub : uIcc c x ⊆ uIcc a b := uIcc_subset_uIcc hc hx
  have hint : (∫ t in c..x, g t - g c) = f x - f c - g c * (x - c) := by
    rw [intervalIntegral.integral_sub
      (hg.continuousOn.mono hsub).intervalIntegrable intervalIntegrable_const,
      intervalIntegral.integral_const]
    have heq : (∫ t in c..x, g t) = ∫ t in c..x, deriv f t := by
      apply intervalIntegral.integral_congr_ae
      filter_upwards [hfg] with t ht htI
      exact (ht (hsub (uIoc_subset_uIcc htI))).deriv.symm
    rw [heq, (hf.mono hsub).integral_deriv_eq_sub]
    simp only [smul_eq_mul]
    ring
  have hgbound (t : ℝ) (ht : t ∈ uIcc c x) : |g t - g c| ≤ D * |t - c| := by
    apply ac_increment_bound (hg.mono (uIcc_subset_uIcc hc (hsub ht)))
    filter_upwards [hd] with y hy hyI
    exact hy ((uIcc_subset_uIcc hc (hsub ht)) hyI)
  rw [← hint]
  rcases le_total c x with hcx | hxc
  · have hdom : IntervalIntegrable (fun t : ℝ => D * (t - c)) volume c x :=
      (continuous_const.mul (continuous_id.sub continuous_const)).intervalIntegrable c x
    have hi := intervalIntegral.norm_integral_le_of_norm_le hcx
      (f := fun t => g t - g c) (g := fun t => D * (t - c)) ?_ hdom
    · have heval : (∫ t in c..x, D * (t - c)) = D / 2 * (x - c) ^ 2 := by
        rw [intervalIntegral.integral_const_mul,
          intervalIntegral.integral_sub (f := fun t : ℝ => t) (g := fun _ => c)
            (continuous_id.intervalIntegrable c x) intervalIntegrable_const,
          integral_id, intervalIntegral.integral_const]
        simp only [smul_eq_mul]
        ring
      simpa only [Real.norm_eq_abs, heval] using hi
    · filter_upwards [] with t ht
      have htU : t ∈ uIcc c x := by
        simpa only [uIcc_of_le hcx] using Ioc_subset_Icc_self ht
      simpa only [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr ht.1.le)] using
        hgbound t htU
  · rw [intervalIntegral.integral_symm, abs_neg]
    have hdom : IntervalIntegrable (fun t : ℝ => D * (c - t)) volume x c :=
      (continuous_const.mul (continuous_const.sub continuous_id)).intervalIntegrable x c
    have hi := intervalIntegral.norm_integral_le_of_norm_le hxc
      (f := fun t => g t - g c) (g := fun t => D * (c - t)) ?_ hdom
    · have heval : (∫ t in x..c, D * (c - t)) = D / 2 * (x - c) ^ 2 := by
        rw [intervalIntegral.integral_const_mul,
          intervalIntegral.integral_sub (f := fun _ : ℝ => c) (g := fun t : ℝ => t)
            intervalIntegrable_const (continuous_id.intervalIntegrable x c),
          intervalIntegral.integral_const, integral_id]
        simp only [smul_eq_mul]
        ring
      simpa only [Real.norm_eq_abs, heval] using hi
    · filter_upwards [] with t ht
      have htU : t ∈ uIcc c x := by
        simpa only [uIcc_of_ge hxc] using Ioc_subset_Icc_self ht
      have habs : |t - c| = c - t := by
        simpa only [neg_sub] using abs_of_nonpos (sub_nonpos.mpr ht.2)
      simpa only [Real.norm_eq_abs, habs] using hgbound t htU

end RicciFlowSharpEstimate.Analysis
