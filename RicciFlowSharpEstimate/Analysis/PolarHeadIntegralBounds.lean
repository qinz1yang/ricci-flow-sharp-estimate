/-
Copyright (c) 2026 Ziyang Qin. All rights reserved.
No license is granted by this file.
Authors: Ziyang Qin
-/
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Integrability of polar head integrals

The coordinate-weighted primitive of an integrable source remains integrable
after division by the square of the coordinate. Its triangular kernel has
integrated rows bounded by the absolute value of the original source.
-/

noncomputable section

namespace RicciFlowSharpEstimate.Analysis

open Filter MeasureTheory Set

private theorem inverse_sq_interval {t b : ℝ} (ht : 0 < t) (htb : t ≤ b) :
    IntervalIntegrable (fun x : ℝ => (x ^ 2)⁻¹) volume t b ∧
      (∫ x in t..b, (x ^ 2)⁻¹) = t⁻¹ - b⁻¹ := by
  have hc : ContinuousOn (fun x : ℝ => (x ^ 2)⁻¹) (Icc t b) :=
    (continuousOn_id.pow 2).inv₀ fun x hx =>
      pow_ne_zero _ (ne_of_gt (lt_of_lt_of_le ht hx.1))
  have hi : IntervalIntegrable (fun x : ℝ => (x ^ 2)⁻¹) volume t b :=
    ContinuousOn.intervalIntegrable_of_Icc htb hc
  refine ⟨hi, ?_⟩
  have hd : ∀ x ∈ uIcc t b,
      HasDerivAt (fun y : ℝ => -y⁻¹) (x ^ 2)⁻¹ x := by
    intro x hx
    rw [uIcc_of_le htb] at hx
    have hd := (hasDerivAt_inv (ne_of_gt (lt_of_lt_of_le ht hx.1))).neg
    change HasDerivAt (fun y : ℝ => -y⁻¹) _ x at hd
    simpa only [neg_neg] using hd
  simpa only [neg_sub_neg] using
    intervalIntegral.integral_eq_sub_of_hasDerivAt hd hi

/-- The coordinate-weighted primitive of an integrable source, divided by the
square of the coordinate, is integrable on the same positive interval. -/
theorem integrableOn_div_sq_primitive_of_integrable {b : ℝ} {g : ℝ → ℝ}
    (hg : IntegrableOn g (Ioo 0 b) volume) :
    IntegrableOn (fun x => (∫ t in 0..x, t * g t) / x ^ 2) (Ioo 0 b) volume := by
  let μ : Measure ℝ := volume.restrict (Ioo 0 b)
  let K : ℝ × ℝ → ℝ :=
    {v : ℝ × ℝ | v.1 < v.2}.indicator (fun v => v.1 * g v.1 / v.2 ^ 2)
  have hfst : AEStronglyMeasurable (fun v : ℝ × ℝ => v.1) (μ.prod μ) :=
    measurable_fst.aestronglyMeasurable
  have hsnd : AEStronglyMeasurable (fun v : ℝ × ℝ => v.2) (μ.prod μ) :=
    measurable_snd.aestronglyMeasurable
  have hKm : AEStronglyMeasurable K (μ.prod μ) :=
    ((hfst.mul hg.aestronglyMeasurable.comp_fst).div₀ (hsnd.pow 2)).indicator
      (measurableSet_lt measurable_fst measurable_snd)
  have hset (t : ℝ) (ht : t ∈ Ioo 0 b) : Ioo 0 b ∩ Ioi t = Ioo t b := by
    ext x
    constructor
    · rintro ⟨⟨_, hxb⟩, htx⟩
      exact ⟨htx, hxb⟩
    · rintro ⟨htx, hxb⟩
      exact ⟨⟨ht.1.trans htx, hxb⟩, htx⟩
  have hrow (t : ℝ) (ht : t ∈ Ioo 0 b) :
      Integrable (fun x => K (t, x)) μ := by
    change IntegrableOn ((Ioi t).indicator (fun x : ℝ => t * g t / x ^ 2))
      (Ioo 0 b) volume
    rw [integrableOn_indicator_iff measurableSet_Ioi, inter_comm (Ioi t), hset t ht]
    have hi : IntegrableOn (fun x : ℝ => (x ^ 2)⁻¹) (Ioo t b) volume :=
      (intervalIntegrable_iff_integrableOn_Ioo_of_le ht.2.le).mp
        (inverse_sq_interval ht.1 ht.2.le).1
    change Integrable (fun x : ℝ => t * g t / x ^ 2) (volume.restrict (Ioo t b))
    simpa only [div_eq_mul_inv] using hi.const_mul (t * g t)
  have hrow_bound (t : ℝ) (ht : t ∈ Ioo 0 b) :
      (∫ x, ‖K (t, x)‖ ∂μ) ≤ |g t| := by
    have hnorm : (fun x => ‖K (t, x)‖) =
        (Ioi t).indicator (fun x : ℝ => |t * g t| * (x ^ 2)⁻¹) := by
      funext x
      by_cases htx : t < x <;>
        simp [K, indicator, htx, Real.norm_eq_abs, div_eq_mul_inv]
    have heq : (∫ x, ‖K (t, x)‖ ∂μ) = |t * g t| * (t⁻¹ - b⁻¹) := by
      change (∫ x in Ioo 0 b, ‖K (t, x)‖) = |t * g t| * (t⁻¹ - b⁻¹)
      rw [hnorm, setIntegral_indicator measurableSet_Ioi, hset t ht, integral_const_mul,
        ← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le ht.2.le,
        (inverse_sq_interval ht.1 ht.2.le).2]
    rw [heq]
    calc
      |t * g t| * (t⁻¹ - b⁻¹) ≤ |t * g t| * t⁻¹ :=
        mul_le_mul_of_nonneg_left
          (sub_le_self _ (inv_nonneg.mpr (ht.1.trans ht.2).le)) (abs_nonneg _)
      _ = |g t| := by
        rw [abs_mul, abs_of_pos ht.1, mul_right_comm, mul_inv_cancel₀ ht.1.ne', one_mul]
  have hK : Integrable K (μ.prod μ) := by
    apply (integrable_prod_iff hKm).mpr
    constructor
    · filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
      exact hrow t ht
    · refine hg.norm.mono_nonneg hKm.norm.integral_prod_right'
        (Eventually.of_forall fun t => integral_nonneg fun x => norm_nonneg (K (t, x))) ?_
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
      simpa only [Real.norm_eq_abs] using hrow_bound t ht
  refine hK.integral_prod_right.congr ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
  have hset' : Ioo 0 b ∩ Iio x = Ioo 0 x := by
    ext t
    constructor
    · rintro ⟨⟨ht0, _⟩, htx⟩
      exact ⟨ht0, htx⟩
    · rintro ⟨ht0, htx⟩
      exact ⟨⟨ht0, htx.trans hx.2⟩, htx⟩
  change (∫ t in Ioo 0 b, (Iio x).indicator (fun t => t * g t / x ^ 2) t) =
    (∫ t in 0..x, t * g t) / x ^ 2
  rw [setIntegral_indicator measurableSet_Iio, hset', integral_div,
    intervalIntegral.integral_of_le hx.1.le, integral_Ioc_eq_integral_Ioo]

end RicciFlowSharpEstimate.Analysis
