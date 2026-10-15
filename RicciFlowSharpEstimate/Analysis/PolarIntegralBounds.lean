/-
Copyright (c) 2026 Ziyang Qin. All rights reserved.
No license is granted by this file.
Authors: Ziyang Qin
-/
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Integrability of polar tail integrals

An integrable coordinate-weighted source has an integrable tail primitive.
The source need not be integrable at the origin. The proof integrates its
triangular kernel on a product, whose row lengths supply the coordinate weight.
-/

noncomputable section

namespace RicciFlowSharpEstimate.Analysis

open Filter MeasureTheory Set

/-- An integrable coordinate-weighted source has an integrable tail primitive
on the positive interval. No unweighted integrability or separate measurability
assumption on the source is required. -/
theorem integrableOn_tail_integral_of_coordinate_mul_integrable
    {b : ℝ} {S : ℝ → ℝ}
    (hS : IntegrableOn (fun t => t * S t) (Ioo 0 b) volume) :
    IntegrableOn (fun x => ∫ t in x..b, S t) (Ioo 0 b) volume := by
  let μ : Measure ℝ := volume.restrict (Ioo 0 b)
  have hSm : AEStronglyMeasurable S μ := by
    have hi : AEStronglyMeasurable (fun t : ℝ => t⁻¹) μ :=
      measurable_inv.aestronglyMeasurable
    refine (hi.mul hS.aestronglyMeasurable).congr ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    change t⁻¹ * (t * S t) = S t
    rw [← mul_assoc, inv_mul_cancel₀ ht.1.ne', one_mul]
  let K : ℝ × ℝ → ℝ :=
    {v : ℝ × ℝ | v.2 < v.1}.indicator (fun v => S v.1)
  have hKm : AEStronglyMeasurable K (μ.prod μ) :=
    hSm.comp_fst.indicator (measurableSet_lt measurable_snd measurable_fst)
  have hrow (t : ℝ) : Integrable (fun x => K (t, x)) μ := by
    change Integrable ((Iio t).indicator (fun _ : ℝ => S t)) μ
    exact (integrable_const (S t)).indicator measurableSet_Iio
  have hrow_norm (t : ℝ) (ht : t ∈ Ioo 0 b) :
      (∫ x, ‖K (t, x)‖ ∂μ) = ‖t * S t‖ := by
    have hset : Ioo 0 b ∩ Iio t = Ioo 0 t := by
      ext x
      constructor
      · rintro ⟨⟨hx0, _⟩, hxt⟩
        exact ⟨hx0, hxt⟩
      · rintro ⟨hx0, hxt⟩
        exact ⟨⟨hx0, hxt.trans ht.2⟩, hxt⟩
    have hnorm : (fun x => ‖K (t, x)‖) =
        (Iio t).indicator (fun _ : ℝ => ‖S t‖) := by
      funext x
      by_cases hxt : x < t <;> simp [K, indicator, hxt]
    change (∫ x in Ioo 0 b, ‖K (t, x)‖) = ‖t * S t‖
    rw [hnorm, setIntegral_indicator measurableSet_Iio, hset, setIntegral_const,
      Real.volume_real_Ioo_of_le ht.1.le]
    simp only [sub_zero, smul_eq_mul, Real.norm_eq_abs, abs_mul, abs_of_pos ht.1]
  have hK : Integrable K (μ.prod μ) := by
    apply (integrable_prod_iff hKm).mpr
    refine ⟨Eventually.of_forall hrow, hS.norm.congr ?_⟩
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    exact (hrow_norm t ht).symm
  refine hK.integral_prod_right.congr ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
  have hset : Ioo 0 b ∩ Ioi x = Ioo x b := by
    ext t
    constructor
    · rintro ⟨⟨_, htb⟩, hxt⟩
      exact ⟨hxt, htb⟩
    · rintro ⟨hxt, htb⟩
      exact ⟨⟨hx.1.trans hxt, htb⟩, hxt⟩
  change (∫ t in Ioo 0 b, (Ioi x).indicator S t) = ∫ t in x..b, S t
  rw [setIntegral_indicator measurableSet_Ioi, hset,
    intervalIntegral.integral_of_le hx.2.le, integral_Ioc_eq_integral_Ioo]

end RicciFlowSharpEstimate.Analysis
