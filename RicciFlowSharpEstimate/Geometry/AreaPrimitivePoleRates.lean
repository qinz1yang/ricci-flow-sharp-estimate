/-
Copyright (c) 2026 Ziyang Qin. All rights reserved.
No license is granted by this file.
Authors: Ziyang Qin
-/
import RicciFlowSharpEstimate.Geometry.AreaSlopePoleBounds
import Mathlib.Analysis.Calculus.LHopital
import Mathlib.MeasureTheory.Integral.IntervalAverage

/-! # First-order pole rates and actual curvature averages -/

noncomputable section
namespace RicciFlowSharpEstimate.Geometry.AreaProfile
open Set MeasureTheory Filter Topology
local notation "areaμ" => volume.restrict (Ioo (0 : ℝ) 1)

private theorem zero_mul_bounded {α : Type*} {l : Filter α} {u v : α → ℝ} {B : ℝ}
    (hu : Tendsto u l (𝓝 0)) (hv : ∀ᶠ x in l, |v x| ≤ B) :
    Tendsto (fun x => u x * v x) l (𝓝 0) := by
  apply squeeze_zero_norm'
  · filter_upwards [hv] with x hx
    simp only [norm_mul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left hx (abs_nonneg _)
  · simpa only [norm_zero, zero_mul, Real.norm_eq_abs] using hu.norm.mul_const B

/-- The original primitive has its physical first-order warp rate at both
poles, without any curvature pole limit or smoothness assumption. -/
theorem IsRecoverableAreaCompetitor.primitive_first_order_pole_rates
    {C : ℝ} {K r p z : ℝ → ℝ} (hC : 1 ≤ C)
    (h : IsRecoverableAreaCompetitor C K r p z) :
    Tendsto (fun x => warp K x / x) (𝓝[>] 0) (𝓝 2) ∧
      Tendsto (fun x => warp K x / (1 - x)) (𝓝[<] 1) (𝓝 2) := by
  have hg := h.geometry_bounds hC
  have hD := (h.primitive_local_regularity hC).1
  have hfL : Tendsto (warp K) (𝓝[>] 0) (𝓝 0) := by
    simpa only [hg.2.2.2.1.1] using
      ((hg.1.continuousWithinAt ⟨le_rfl, zero_le_one⟩).mono_of_mem_nhdsWithin
        (Icc_mem_nhdsGT zero_lt_one)).tendsto
  have hfR : Tendsto (warp K) (𝓝[<] 1) (𝓝 0) := by
    simpa only [hg.2.2.2.1.2.1] using
      ((hg.1.continuousWithinAt ⟨zero_le_one, le_rfl⟩).mono_of_mem_nhdsWithin
        (Icc_mem_nhdsLT zero_lt_one)).tendsto
  have hbL : Tendsto (warpSlope K) (𝓝[>] 0) (𝓝 2) := by
    simpa only [hg.2.2.2.1.2.2.1] using
      ((hg.2.1.continuousWithinAt ⟨le_rfl, zero_le_one⟩).mono_of_mem_nhdsWithin
        (Icc_mem_nhdsGT zero_lt_one)).tendsto
  have hbR : Tendsto (warpSlope K) (𝓝[<] 1) (𝓝 (-2)) := by
    simpa only [hg.2.2.2.1.2.2.2] using
      ((hg.2.1.continuousWithinAt ⟨zero_le_one, le_rfl⟩).mono_of_mem_nhdsWithin
        (Icc_mem_nhdsLT zero_lt_one)).tendsto
  constructor
  · exact HasDerivAt.lhopital_zero_right_on_Ioo zero_lt_one hD
      (fun x _ => hasDerivAt_id x) (fun _ _ => one_ne_zero) hfL
      (tendsto_id.mono_left nhdsWithin_le_nhds) (by simpa only [div_one] using hbL)
  · have hgb : Tendsto (fun x : ℝ => 1 - x) (𝓝[<] 1) (𝓝 0) := by
      simpa only [sub_self] using
        (tendsto_const_nhds.sub (tendsto_id.mono_left nhdsWithin_le_nhds) :
          Tendsto (fun x : ℝ => 1 - x) (𝓝[<] 1) (𝓝 (1 - 1)))
    have hdiv : Tendsto (fun x => warpSlope K x / (-1 : ℝ)) (𝓝[<] 1) (𝓝 2) := by
      simpa only [neg_div_neg_eq, div_one] using hbR.div_const (-1)
    exact HasDerivAt.lhopital_zero_left_on_Ioo zero_lt_one hD
      (fun x _ => by simpa only [zero_sub, id_eq] using
        (hasDerivAt_const x (1 : ℝ)).fun_sub (hasDerivAt_id x))
      (fun _ _ => by norm_num) hfR hgb hdiv

/-- The singular slope/warp terms differ from the true one-sided curvature
averages by quantities tending to zero. The averages need not have limits. -/
theorem IsRecoverableAreaCompetitor.primitive_curvature_average_pole_rates
    {C : ℝ} {K r p z : ℝ → ℝ} (hC : 1 ≤ C)
    (h : IsRecoverableAreaCompetitor C K r p z) :
    Tendsto (fun x => (2 - warpSlope K x) / warp K x -
      (⨍ t in (0 : ℝ)..x, K t)) (𝓝[>] 0) (𝓝 0) ∧
    Tendsto (fun x => (2 + warpSlope K x) / warp K x -
      (⨍ t in x..(1 : ℝ), K t)) (𝓝[<] 1) (𝓝 0) := by
  have hg := h.geometry_bounds hC
  have hfRates := h.primitive_first_order_pole_rates hC
  have hC0 : 0 < C := zero_lt_one.trans_le hC
  have hKB : ∀ᵐ t ∂volume, t ∈ Ioo (0 : ℝ) 1 → |K t| ≤ 2 * C := by
    filter_upwards [ae_imp_of_ae_restrict hg.2.2.2.2] with t ht hti
    rw [abs_of_nonneg ((by positivity : (0 : ℝ) ≤ 2 / C).trans (ht hti).1)]
    exact (ht hti).2
  have hmeanB (a d : ℝ) (ha : 0 ≤ a) (had : a < d) (hd : d ≤ 1) :
      |⨍ t in a..d, K t| ≤ 2 * C := by
    have hb := intervalIntegral.norm_integral_le_of_norm_le_const_ae
      (f := K) (a := a) (b := d) (C := 2 * C) (by
        filter_upwards [hKB, volume.ae_ne (1 : ℝ)] with t ht ht1 htI
        have htC : t ∈ Ioc a d := by simpa only [uIoc_of_le had.le] using htI
        rw [Real.norm_eq_abs]
        exact ht ⟨ha.trans_lt htC.1, lt_of_le_of_ne (htC.2.trans hd) ht1⟩)
    rw [interval_average_eq_div, abs_div, abs_of_pos (sub_pos.mpr had)]
    apply (div_le_iff₀ (sub_pos.mpr had)).mpr
    simpa only [Real.norm_eq_abs, abs_of_pos (sub_pos.mpr had)] using hb
  have hLI : IntervalIntegrable K volume 0 1 :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le zero_le_one).mpr
      (h.1.integrable (by norm_num : (1 : ENNReal) ≤ 2))
  have htail (x : ℝ) (hx : x ∈ Ioo (0 : ℝ) 1) :
      2 + warpSlope K x = 2 * ∫ t in x..(1 : ℝ), K t := by
    have hL : IntervalIntegrable K volume 0 x := hLI.mono_set (by
      rw [uIcc_of_le hx.1.le, uIcc_of_le zero_le_one]
      exact Icc_subset_Icc le_rfl hx.2.le)
    have hR : IntervalIntegrable K volume x 1 := hLI.mono_set (by
      rw [uIcc_of_le hx.2.le, uIcc_of_le zero_le_one]
      exact Icc_subset_Icc hx.1.le le_rfl)
    have hh := intervalIntegral.integral_add_adjacent_intervals hL hR
    rw [h.2.2.2.1] at hh
    dsimp only [warpSlope]
    linarith only [hh]
  have hfpos (x : ℝ) (hx : x ∈ Ioo (0 : ℝ) 1) : 0 < warp K x :=
    (mul_pos (mul_pos (by positivity : (0 : ℝ) < 2 / C) hx.1)
      (sub_pos.mpr hx.2)).trans_le (hg.2.2.1 x ⟨hx.1.le, hx.2.le⟩).1
  have hLfactor : Tendsto (fun x => 2 / (warp K x / x) - 1) (𝓝[>] 0) (𝓝 0) := by
    have ht : Tendsto (fun x => 2 / (warp K x / x)) (𝓝[>] 0) (𝓝 (2 / 2 : ℝ)) :=
      tendsto_const_nhds.div hfRates.1 (by norm_num)
    simpa only [div_self (by norm_num : (2 : ℝ) ≠ 0), sub_self] using
      ht.sub_const 1
  have hRfactor : Tendsto (fun x => 2 / (warp K x / (1 - x)) - 1)
      (𝓝[<] 1) (𝓝 0) := by
    have ht : Tendsto (fun x => 2 / (warp K x / (1 - x)))
        (𝓝[<] 1) (𝓝 (2 / 2 : ℝ)) :=
      tendsto_const_nhds.div hfRates.2 (by norm_num)
    simpa only [div_self (by norm_num : (2 : ℝ) ≠ 0), sub_self] using
      ht.sub_const 1
  have hLDom : ∀ᶠ x in 𝓝[>] (0 : ℝ), x ∈ Ioo (0 : ℝ) 1 :=
    Ioo_mem_nhdsGT zero_lt_one
  have hRDom : ∀ᶠ x in 𝓝[<] (1 : ℝ), x ∈ Ioo (0 : ℝ) 1 :=
    Ioo_mem_nhdsLT zero_lt_one
  constructor
  · apply (zero_mul_bounded hLfactor
      (hLDom.mono fun x hx => hmeanB 0 x le_rfl hx.1 hx.2.le)).congr'
    filter_upwards [hLDom] with x hx
    rw [interval_average_eq_div, sub_zero]
    dsimp only [warpSlope]
    field_simp [hx.1.ne', (hfpos x hx).ne']
    ring
  · apply (zero_mul_bounded hRfactor
      (hRDom.mono fun x hx => hmeanB x 1 hx.1.le hx.2 le_rfl)).congr'
    filter_upwards [hRDom] with x hx
    rw [htail x hx, interval_average_eq_div]
    field_simp [(sub_pos.mpr hx.2).ne', (hfpos x hx).ne']

end RicciFlowSharpEstimate.Geometry.AreaProfile
