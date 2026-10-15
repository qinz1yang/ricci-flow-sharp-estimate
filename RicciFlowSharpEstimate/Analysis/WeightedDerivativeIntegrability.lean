/-
Copyright (c) 2026 Ziyang Qin. All rights reserved.
No license is granted by this file.
Authors: Ziyang Qin
-/
import RicciFlowSharpEstimate.Analysis.PolarIntegralBounds
import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun

/-! # Unweighted integrability from a parabolically weighted genuine derivative -/

noncomputable section
namespace RicciFlowSharpEstimate.Analysis
open Set MeasureTheory Filter
local notation "areaμ" => volume.restrict (Ioo (0 : ℝ) 1)

private theorem reflect_integrable {g : ℝ → ℝ} (hg : Integrable g areaμ) :
    Integrable (fun x => g (1 - x)) areaμ := by
  have hi := (intervalIntegrable_iff_integrableOn_Ioo_of_le zero_le_one).mpr hg
  have hr := (hi.comp_sub_left 1).symm
  have hr' : IntervalIntegrable (fun x => g (1 - x)) volume 0 1 := by
    simpa only [sub_self, sub_zero] using hr
  exact (intervalIntegrable_iff_integrableOn_Ioo_of_le zero_le_one).mp hr'

private theorem coordinate_source_left {v : ℝ → ℝ}
    (hv : Integrable (fun x => x * (1 - x) * v x) areaμ) :
    IntegrableOn (fun x => x * v x) (Ioo (0 : ℝ) (1 / 2)) volume := by
  let μ := volume.restrict (Ioo (0 : ℝ) (1 / 2))
  have hsub : Ioo (0 : ℝ) (1 / 2) ⊆ Ioo (0 : ℝ) 1 :=
    fun x hx => ⟨hx.1, by linarith [hx.2]⟩
  have hvs : Integrable (fun x => x * (1 - x) * v x) μ :=
    hv.mono_measure (Measure.restrict_mono hsub le_rfl)
  have hm : AEStronglyMeasurable (fun x : ℝ => (1 - x)⁻¹) μ :=
    (measurable_const.sub measurable_id).inv.aestronglyMeasurable
  have hb : ∀ᵐ x ∂μ, ‖(1 - x)⁻¹‖ ≤ (2 : ℝ) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
    have hd : 0 < 1 - x := by linarith [hx.2]
    rw [Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hd)]
    rw [inv_eq_one_div]
    apply (div_le_iff₀ hd).mpr
    linarith [hx.2]
  apply (hvs.bdd_mul hm hb).congr
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
  change (1 - x)⁻¹ * (x * (1 - x) * v x) = x * v x
  field_simp [(show (1 : ℝ) - x ≠ 0 by linarith [hx.2])]

private theorem local_integral_eq_sub {u v : ℝ → ℝ}
    (hu : ∀ a ∈ Ioo (0 : ℝ) 1, ∀ b ∈ Ioo (0 : ℝ) 1,
      AbsolutelyContinuousOnInterval u a b)
    (hd : ∀ᵐ x ∂areaμ, HasDerivAt u (v x) x)
    {a b : ℝ} (ha : a ∈ Ioo (0 : ℝ) 1) (hb : b ∈ Ioo (0 : ℝ) 1) :
    (∫ t in a..b, v t) = u b - u a := by
  have hi := (hu a ha b hb).integral_deriv_eq_sub
  have heq : (∫ t in a..b, deriv u t) = ∫ t in a..b, v t := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards [ae_imp_of_ae_restrict hd] with x hx hxI
    exact (hx (ordConnected_Ioo.uIcc_subset ha hb (uIoc_subset_uIcc hxI))).deriv
  rwa [heq] at hi

/-- Local absolute continuity and an integrable parabolically weighted
genuine derivative imply unweighted integrability on the full open interval.
The function itself may have no finite endpoint trace. -/
theorem integrable_of_parabolic_weighted_derivative
    {u v : ℝ → ℝ}
    (hu : ∀ a ∈ Ioo (0 : ℝ) 1, ∀ b ∈ Ioo (0 : ℝ) 1,
      AbsolutelyContinuousOnInterval u a b)
    (hd : ∀ᵐ x ∂areaμ, HasDerivAt u (v x) x)
    (hv : Integrable (fun x => x * (1 - x) * v x) areaμ) :
    Integrable u areaμ := by
  let c : ℝ := 1 / 2
  have hc : c ∈ Ioo (0 : ℝ) 1 := by norm_num [c]
  have hcc : 1 - c = c := by norm_num [c]
  have htail := integrableOn_tail_integral_of_coordinate_mul_integrable
    (coordinate_source_left hv)
  have hL : IntegrableOn u (Ioo (0 : ℝ) c) volume := by
    apply ((integrable_const (u c)).sub htail).congr
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
    have heq := local_integral_eq_sub hu hd ⟨hx.1, hx.2.trans hc.2⟩ hc
    change u c - (∫ t in x..c, v t) = u x
    linarith only [heq]
  have hvr : Integrable (fun x => x * (1 - x) * (-v (1 - x))) areaμ := by
    apply (reflect_integrable hv).neg.congr
    filter_upwards [] with x
    change -((1 - x) * (1 - (1 - x)) * v (1 - x)) = x * (1 - x) * (-v (1 - x))
    ring
  have hrtail := integrableOn_tail_integral_of_coordinate_mul_integrable
    (coordinate_source_left hvr)
  have hR : IntegrableOn (fun x => u (1 - x)) (Ioo (0 : ℝ) c) volume := by
    apply ((integrable_const (u c)).sub hrtail).congr
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
    have hxI : 1 - x ∈ Ioo (0 : ℝ) 1 := by constructor <;> linarith [hx.1, hx.2, hc.2]
    have heq := local_integral_eq_sub hu hd hc hxI
    have hchange : (∫ t in x..c, -v (1 - t)) = -(∫ t in c..(1 - x), v t) := by
      rw [intervalIntegral.integral_neg, intervalIntegral.integral_comp_sub_left, hcc]
    change u c - (∫ t in x..c, -v (1 - t)) = u (1 - x)
    rw [hchange, heq]
    ring
  have hLI : IntervalIntegrable u volume 0 c :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le hc.1.le).mpr hL
  have hRI := ((intervalIntegrable_iff_integrableOn_Ioo_of_le hc.1.le).mpr hR).comp_sub_left 1
  have hRI' : IntervalIntegrable u volume c 1 := by
    simpa only [sub_sub_cancel, sub_zero, hcc] using hRI.symm
  exact (intervalIntegrable_iff_integrableOn_Ioo_of_le zero_le_one).mp (hLI.trans hRI')

end RicciFlowSharpEstimate.Analysis
