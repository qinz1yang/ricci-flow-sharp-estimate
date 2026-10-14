/-
Copyright (c) 2026 Ziyang Qin. All rights reserved.
No license is granted by this file.
Authors: Ziyang Qin
-/
import RicciFlowSharpEstimate.Analysis.ParabolicBoundary
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.MeasureTheory.Function.Holder

/-!
# Zero traces of the parabolic square-energy flux

A linearly vanishing weight with bounded weak derivative makes the literal
product `f * r^2` absolutely continuous through both endpoints. Its derivative
is integrable under the first parabolic graph bounds on `r`. No L² graph
bound on `r^2`, probe trace, or boundedness of the probe is assumed.

The private global primitive and reciprocal-trace argument is adapted from
the accepted `ParabolicBoundary` proof without changing its public API.
-/

noncomputable section

namespace RicciFlowSharpEstimate.Analysis

open Set MeasureTheory Filter Topology

local notation "areaμ" => volume.restrict (Ioo (0 : ℝ) 1)

private theorem energy_interior_interval_subset {a b : ℝ}
    (ha : a ∈ Ioo (0 : ℝ) 1) (hb : b ∈ Ioo (0 : ℝ) 1) :
    uIcc a b ⊆ Ioo (0 : ℝ) 1 := by
  intro x hx
  rcases mem_uIcc.mp hx with hx | hx
  · exact ⟨ha.1.trans_le hx.1, hx.2.trans_lt hb.2⟩
  · exact ⟨hb.1.trans_le hx.1, hx.2.trans_lt ha.2⟩

private theorem energy_global_ac_of_integrable_traces {F S : ℝ → ℝ}
    (hlocal : ∀ a ∈ Ioo (0 : ℝ) 1, ∀ b ∈ Ioo (0 : ℝ) 1,
      AbsolutelyContinuousOnInterval F a b)
    (hD : ∀ᵐ x ∂areaμ, HasDerivAt F (S x) x)
    (hS : Integrable S areaμ)
    (hL : Integrable (fun x => F x / x) areaμ)
    (hR : Integrable (fun x => F x / (1 - x)) areaμ)
    (h0 : F 0 = 0) (h1 : F 1 = 0) : AbsolutelyContinuousOnInterval F 0 1 := by
  let c : ℝ := 1 / 2
  have hc : c ∈ Ioo (0 : ℝ) 1 := by norm_num [c]
  have hSI : IntervalIntegrable S volume 0 1 :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le zero_le_one).mpr hS
  let G := fun x => F c + ∫ t in c..x, S t
  have hGAC : AbsolutelyContinuousOnInterval G 0 1 := by
    have hConst : AbsolutelyContinuousOnInterval (fun _ : ℝ => F c) 0 1 :=
      ((contDiff_const : ContDiff ℝ 1 (fun _ : ℝ => F c)).contDiffOn).absolutelyContinuousOnInterval
    exact hConst.fun_add (hSI.absolutelyContinuousOnInterval_intervalIntegral (by norm_num [c]))
  have hEq (x : ℝ) (hx : x ∈ Ioo (0 : ℝ) 1) : G x = F x := by
    have hi := (hlocal c hc x hx).integral_deriv_eq_sub
    have hInt : (∫ t in c..x, deriv F t) = ∫ t in c..x, S t := by
      apply intervalIntegral.integral_congr_ae
      filter_upwards [ae_imp_of_ae_restrict hD] with t ht htI
      exact (ht (energy_interior_interval_subset hc hx (uIoc_subset_uIcc htI))).deriv
    rw [hInt] at hi
    dsimp only [G]
    linarith
  have hGL : IntegrableOn (fun x => G x / (x - 0)) (Ioo (0 : ℝ) 1) := by
    apply hL.congr
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
    simp only [sub_zero, hEq x hx]
  have hGR : IntegrableOn (fun x => G x / (1 - x)) (Ioo (0 : ℝ) 1) := by
    apply hR.congr
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
    rw [hEq x hx]
  have hGC : ContinuousOn G (Icc (0 : ℝ) 1) := by
    simpa only [uIcc_of_le zero_le_one] using hGAC.continuousOn
  have hG0 := eq_zero_of_integrableOn_div_left zero_lt_one hGC hGL
  have hG1 := eq_zero_of_integrableOn_div_right zero_lt_one hGC hGR
  apply hGAC.congr
  rw [uIcc_of_le zero_le_one]
  intro x hx
  by_cases hx0 : x = 0
  · simp only [hx0, hG0, h0]
  by_cases hx1 : x = 1
  · simp only [hx1, hG1, h1]
  exact hEq x ⟨lt_of_le_of_ne hx.1 (Ne.symm hx0), lt_of_le_of_ne hx.2 hx1⟩

private theorem energy_div_bound (f r w d B : ℝ)
    (hB : 0 ≤ B) (hd : 0 < d) (hwd : w ≤ d) (hf : |f| ≤ B * w) :
    |f * r ^ 2 / d| ≤ B * r ^ 2 := by
  rw [abs_div, abs_mul, abs_of_pos hd, abs_of_nonneg (sq_nonneg r)]
  apply (div_le_iff₀ hd).mpr
  have hfd := hf.trans (mul_le_mul_of_nonneg_left hwd hB)
  nlinarith only [mul_le_mul_of_nonneg_right hfd (sq_nonneg r)]

/-- The literal square-energy flux has global absolute continuity on the
physical closed interval, zero endpoint values, an integrable derivative and
the actual almost-everywhere product derivative. Only the original first
parabolic graph bounds are assumed; the square of the probe need not have
an L² derivative graph, and no trace of the probe is prescribed. -/
theorem HasWeakDerivOn.absolutelyContinuous_mul_sq_of_parabolic_bounds
    {r p f b : ℝ → ℝ} {B : ℝ}
    (hr : HasWeakDerivOn (Ioo (0 : ℝ) 1) r p)
    (hf : HasWeakDerivOn (Ioo (0 : ℝ) 1) f b)
    (hrc : ContinuousOn r (Ioo (0 : ℝ) 1))
    (hfc : ContinuousOn f (Ioo (0 : ℝ) 1))
    (hr2 : MemLp r 2 areaμ)
    (hp2 : MemLp (fun x => Real.sqrt (x * (1 - x)) * p x) 2 areaμ)
    (hfb : ∀ x ∈ Icc (0 : ℝ) 1, |f x| ≤ B * (x * (1 - x)))
    (hbb : ∀ᵐ x ∂areaμ, |b x| ≤ B) :
    AbsolutelyContinuousOnInterval (fun x => f x * r x ^ 2) 0 1 ∧
      f 0 * r 0 ^ 2 = 0 ∧ f 1 * r 1 ^ 2 = 0 ∧
      Integrable (fun x => b x * r x ^ 2 + 2 * f x * r x * p x) areaμ ∧
      (∀ᵐ x ∂areaμ, HasDerivAt (fun y => f y * r y ^ 2)
        (b x * r x ^ 2 + 2 * f x * r x * p x) x) := by
  have hB : 0 ≤ B := by
    have hh := hfb (1 / 2) (by norm_num)
    norm_num at hh
    nlinarith [abs_nonneg (f (1 / 2))]
  have hfm := hf.locallyIntegrable.aestronglyMeasurable
  have hbm := hf.locallyIntegrable_deriv.aestronglyMeasurable
  have hrm := hr2.aestronglyMeasurable
  have hpm := hr.locallyIntegrable_deriv.aestronglyMeasurable
  have hrsq : Integrable (fun x => r x ^ 2) areaμ := hr2.integrable_sq
  have hbrsq : Integrable (fun x => b x * r x ^ 2) areaμ :=
    hrsq.bdd_mul (c := B) hbm (by simpa only [Real.norm_eq_abs] using hbb)
  have hfp : MemLp (fun x => f x * p x) 2 areaμ := by
    apply hp2.of_le_mul (c := B) (hfm.mul hpm)
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
    have hw0 : 0 ≤ x * (1 - x) := mul_nonneg hx.1.le (sub_nonneg.mpr hx.2.le)
    have hw1 : x * (1 - x) ≤ 1 := by nlinarith [sq_nonneg x]
    have hs0 := Real.sqrt_nonneg (x * (1 - x))
    have hs2 := Real.sq_sqrt hw0
    have hs1 : Real.sqrt (x * (1 - x)) ≤ 1 := by nlinarith
    have hws : x * (1 - x) ≤ Real.sqrt (x * (1 - x)) := by
      nlinarith [mul_nonneg hs0 (sub_nonneg.mpr hs1)]
    have hfs := (hfb x ⟨hx.1.le, hx.2.le⟩).trans
      (mul_le_mul_of_nonneg_left hws hB)
    simpa only [Pi.mul_apply, Real.norm_eq_abs, abs_mul, abs_of_nonneg hs0, mul_assoc] using
      mul_le_mul_of_nonneg_right hfs (abs_nonneg (p x))
  have hcross0 : Integrable (fun x => (f x * p x) * r x) areaμ :=
    hfp.integrable_mul hr2
  have hcross : Integrable (fun x => f x * r x * p x) areaμ := by
    apply hcross0.congr
    filter_upwards [] with x
    ring
  have hS : Integrable (fun x => b x * r x ^ 2 + 2 * f x * r x * p x) areaμ := by
    apply (hbrsq.add (hcross.const_mul 2)).congr
    filter_upwards [] with x
    simp only [Pi.add_apply]
    ring
  have hL : Integrable (fun x => f x * r x ^ 2 / x) areaμ := by
    apply (hrsq.const_mul B).mono'
      ((hfm.mul (hrm.pow 2)).div₀ continuous_id.aestronglyMeasurable)
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
    simpa only [Pi.div_apply, Pi.mul_apply, Pi.pow_apply, id_eq, Real.norm_eq_abs] using
      energy_div_bound (f x) (r x) (x * (1 - x)) x B hB hx.1
        (by nlinarith [sq_nonneg x]) (hfb x ⟨hx.1.le, hx.2.le⟩)
  have hR : Integrable (fun x => f x * r x ^ 2 / (1 - x)) areaμ := by
    apply (hrsq.const_mul B).mono'
      ((hfm.mul (hrm.pow 2)).div₀
        (show Continuous (fun x : ℝ => 1 - x) from
          continuous_const.sub continuous_id).aestronglyMeasurable)
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
    simpa only [Pi.div_apply, Pi.mul_apply, Pi.pow_apply, id_eq, Real.norm_eq_abs] using
      energy_div_bound (f x) (r x) (x * (1 - x)) (1 - x) B hB (sub_pos.mpr hx.2)
        (by nlinarith [sq_nonneg (1 - x)]) (hfb x ⟨hx.1.le, hx.2.le⟩)
  have h0 : f 0 * r 0 ^ 2 = 0 := by
    have hh := hfb 0 (by norm_num)
    have hf0 : f 0 = 0 := by simpa only [zero_mul, mul_zero, abs_nonpos_iff] using hh
    simp only [hf0, zero_mul]
  have h1 : f 1 * r 1 ^ 2 = 0 := by
    have hh := hfb 1 (by norm_num)
    have hf1 : f 1 = 0 := by
      simpa only [sub_self, mul_zero, abs_nonpos_iff] using hh
    simp only [hf1, zero_mul]
  have hD : ∀ᵐ x ∂areaμ, HasDerivAt (fun y => f y * r y ^ 2)
      (b x * r x ^ 2 + 2 * f x * r x * p x) x := by
    filter_upwards [hf.ae_hasDerivAt_of_continuousOn hfc,
      hr.ae_hasDerivAt_of_continuousOn hrc] with x hfx hrx
    have hprod := hfx.mul (hrx.fun_pow 2)
    convert hprod using 1
    ring
  refine ⟨?_, h0, h1, hS, hD⟩
  apply energy_global_ac_of_integrable_traces ?_ hD hS hL hR h0 h1
  intro a ha c hc
  have hrAC := hr.absolutelyContinuousOnInterval hrc ha hc
  have hprod := (hf.absolutelyContinuousOnInterval hfc ha hc).mul (hrAC.mul hrAC)
  simpa only [Pi.mul_def, pow_two] using hprod

end RicciFlowSharpEstimate.Analysis
