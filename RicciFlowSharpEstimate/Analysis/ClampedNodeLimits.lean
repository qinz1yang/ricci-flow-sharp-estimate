/-
Copyright (c) 2026 Ziyang Qin. All rights reserved.
No license is granted by this file.
Authors: Ziyang Qin
-/
import RicciFlowSharpEstimate.Analysis.ClampedSecondOrderFeedback
import Mathlib.Analysis.Calculus.Deriv.Slope

/-! # One-sided traces of a clamped control at a quadratic zero -/

noncomputable section
namespace RicciFlowSharpEstimate.Analysis
open Set MeasureTheory Filter Topology

private theorem clip_eq_lo {lo hi H D : ℝ} (hD : 0 < D) (hH : 0 ≤ H + lo * D) :
    max lo (min hi (-H / D)) = lo := by
  apply max_eq_left
  apply (min_le_right _ _).trans
  apply (div_le_iff₀ hD).mpr
  linarith

private theorem clip_eq_hi {lo hi H D : ℝ} (hlohi : lo ≤ hi)
    (hD : 0 < D) (hH : H + hi * D ≤ 0) :
    max lo (min hi (-H / D)) = hi := by
  have hh : hi ≤ -H / D := (le_div_iff₀ hD).mpr (by linarith)
  rw [min_eq_left hh, max_eq_right hlohi]

private theorem first_order_clip_limits
    {H D K : ℝ → ℝ} {c lo hi g : ℝ} (hlohi : lo ≤ hi)
    (hH : HasDerivAt H g c) (hD : HasDerivAt D 0 c) (hD0 : D c = 0)
    (hDp : ∀ᶠ x in 𝓝[≠] c, 0 < D x)
    (hclip : ∀ᶠ x in 𝓝[≠] c, K x = max lo (min hi (-H x / D x)))
    (hnz : H c ≠ 0 ∨ g ≠ 0) :
    ∃ kl kr : ℝ, Tendsto K (𝓝[<] c) (𝓝 kl) ∧ Tendsto K (𝓝[>] c) (𝓝 kr) := by
  have hcont (v : ℝ) : Tendsto (fun x => H x + v * D x) (𝓝 c) (𝓝 (H c)) := by
    simpa only [hD0, mul_zero, add_zero] using
      hH.continuousAt.tendsto.add (hD.continuousAt.tendsto.const_mul v)
  by_cases hz : H c = 0
  · have hg : g ≠ 0 := hnz.resolve_left (not_not.mpr hz)
    have hslope (v : ℝ) :
        Tendsto (fun x => (H x + v * D x) / (x - c)) (𝓝[≠] c) (𝓝 g) := by
      have hh := (hH.fun_add (hD.const_mul v)).tendsto_slope
      change Tendsto (fun x => slope (fun y => H y + v * D y) c x)
        (𝓝[≠] c) (𝓝 (g + v * 0)) at hh
      simpa only [slope_def_field, hz, hD0, mul_zero, add_zero, sub_zero] using hh
    rcases lt_or_gt_of_ne hg with hg | hg
    · have hslo := (hslope lo).eventually (gt_mem_nhds hg)
      have hshi := (hslope hi).eventually (gt_mem_nhds hg)
      have hl : ∀ᶠ x in 𝓝[<] c, K x = lo := by
        filter_upwards [hslo.filter_mono (nhdsLT_le_nhdsNE c),
          hDp.filter_mono (nhdsLT_le_nhdsNE c), hclip.filter_mono (nhdsLT_le_nhdsNE c),
          self_mem_nhdsWithin] with x hs hd hk hx
        rw [hk]
        apply clip_eq_lo hd
        have hh := (div_lt_iff_of_neg (sub_neg.mpr hx)).mp hs
        simpa only [zero_mul] using hh.le
      have hr : ∀ᶠ x in 𝓝[>] c, K x = hi := by
        filter_upwards [hshi.filter_mono (nhdsGT_le_nhdsNE c),
          hDp.filter_mono (nhdsGT_le_nhdsNE c), hclip.filter_mono (nhdsGT_le_nhdsNE c),
          self_mem_nhdsWithin] with x hs hd hk hx
        rw [hk]
        apply clip_eq_hi hlohi hd
        simpa only [zero_mul] using ((div_lt_iff₀ (sub_pos.mpr hx)).mp hs).le
      exact ⟨lo, hi, tendsto_const_nhds.congr' (Filter.EventuallyEq.symm hl),
        tendsto_const_nhds.congr' (Filter.EventuallyEq.symm hr)⟩
    · have hslo := (hslope lo).eventually (lt_mem_nhds hg)
      have hshi := (hslope hi).eventually (lt_mem_nhds hg)
      have hl : ∀ᶠ x in 𝓝[<] c, K x = hi := by
        filter_upwards [hshi.filter_mono (nhdsLT_le_nhdsNE c),
          hDp.filter_mono (nhdsLT_le_nhdsNE c), hclip.filter_mono (nhdsLT_le_nhdsNE c),
          self_mem_nhdsWithin] with x hs hd hk hx
        rw [hk]
        apply clip_eq_hi hlohi hd
        simpa only [zero_mul] using ((lt_div_iff_of_neg (sub_neg.mpr hx)).mp hs).le
      have hr : ∀ᶠ x in 𝓝[>] c, K x = lo := by
        filter_upwards [hslo.filter_mono (nhdsGT_le_nhdsNE c),
          hDp.filter_mono (nhdsGT_le_nhdsNE c), hclip.filter_mono (nhdsGT_le_nhdsNE c),
          self_mem_nhdsWithin] with x hs hd hk hx
        rw [hk]
        apply clip_eq_lo hd
        simpa only [zero_mul] using ((lt_div_iff₀ (sub_pos.mpr hx)).mp hs).le
      exact ⟨hi, lo, tendsto_const_nhds.congr' (Filter.EventuallyEq.symm hl),
        tendsto_const_nhds.congr' (Filter.EventuallyEq.symm hr)⟩
  · rcases lt_or_gt_of_ne hz with hh | hh
    · have heq : ∀ᶠ x in 𝓝[≠] c, K x = hi := by
        filter_upwards [((hcont hi).eventually (gt_mem_nhds hh)).filter_mono
          nhdsWithin_le_nhds, hDp, hclip] with x hx hd hk
        rw [hk]
        exact clip_eq_hi hlohi hd hx.le
      exact ⟨hi, hi,
        (tendsto_const_nhds.congr' (Filter.EventuallyEq.symm heq)).mono_left (nhdsLT_le_nhdsNE c),
        (tendsto_const_nhds.congr' (Filter.EventuallyEq.symm heq)).mono_left (nhdsGT_le_nhdsNE c)⟩
    · have heq : ∀ᶠ x in 𝓝[≠] c, K x = lo := by
        filter_upwards [((hcont lo).eventually (lt_mem_nhds hh)).filter_mono
          nhdsWithin_le_nhds, hDp, hclip] with x hx hd hk
        rw [hk]
        exact clip_eq_lo hd hx.le
      exact ⟨lo, lo,
        (tendsto_const_nhds.congr' (Filter.EventuallyEq.symm heq)).mono_left (nhdsLT_le_nhdsNE c),
        (tendsto_const_nhds.congr' (Filter.EventuallyEq.symm heq)).mono_left (nhdsGT_le_nhdsNE c)⟩

/-- The actual clamped second-order feedback has finite one-sided limits at
a quadratic zero, including cancellation of both the numerator and its first
derivative. No continuity or limit of the clamped function is assumed. -/
theorem exists_oneSided_clamp_limits_of_quadratic_feedback
    {H G D K e : ℝ → ℝ} {a b c lo hi α β : ℝ}
    (ha : a < c) (hb : c < b) (hlohi : lo ≤ hi) (hα : 0 < α)
    (hH : AbsolutelyContinuousOnInterval H a b)
    (hG : AbsolutelyContinuousOnInterval G a b)
    (hODE : ∀ᵐ x ∂volume, x ∈ Ioo a b →
      HasDerivAt H (G x) x ∧ HasDerivAt G (α * K x + β + e x) x)
    (hD0 : D c = 0)
    (he : Tendsto e (𝓝[≠] c) (𝓝 0))
    (hD : Tendsto (fun x => D x / (x - c) ^ 2) (𝓝[≠] c) (𝓝 α))
    (hclip : ∀ᶠ x in 𝓝[≠] c, K x = max lo (min hi (-H x / D x))) :
    (∃ kl kr : ℝ, Tendsto K (𝓝[<] c) (𝓝 kl) ∧ Tendsto K (𝓝[>] c) (𝓝 kr)) ∧
    (H c = 0 → G c = 0 →
      Tendsto K (𝓝[≠] c) (𝓝 (max lo (min hi (-β / (3 * α)))))) := by
  have hcritical := tendsto_clamp_of_quadratic_feedback (D := D) ha hb hlohi hα hH hG hODE
  have htrace : H c = 0 → G c = 0 →
      Tendsto K (𝓝[≠] c) (𝓝 (max lo (min hi (-β / (3 * α))))) :=
    fun h0 h1 => hcritical h0 h1 he hD hclip
  refine ⟨?_, htrace⟩
  by_cases h0 : H c = 0 ∧ G c = 0
  · exact ⟨_, _, (htrace h0.1 h0.2).mono_left (nhdsLT_le_nhdsNE c),
      (htrace h0.1 h0.2).mono_left (nhdsGT_le_nhdsNE c)⟩
  have hHD : HasDerivAt H (G c) c := by
    have hlim : Tendsto (deriv H) (𝓝 c ⊓ ae volume) (𝓝 (G c)) := by
      have hcC := hG.continuousOn.continuousAt (by
        simpa only [uIcc_of_le (ha.trans hb).le] using Icc_mem_nhds ha hb)
      apply (hcC.tendsto.mono_left inf_le_left).congr'
      have hI : ∀ᶠ x in 𝓝 c, x ∈ Ioo a b := Ioo_mem_nhds ha hb
      filter_upwards [hODE.filter_mono inf_le_right,
        hI.filter_mono inf_le_left] with x hx hxI
      exact (hx hxI).1.deriv.symm
    have hID := intervalIntegral.integral_hasDerivAt_of_tendsto_ae_right
      (f := deriv H) (a := c) (b := c) (c := G c) IntervalIntegrable.refl
      (stronglyMeasurable_deriv H).aestronglyMeasurable.stronglyMeasurableAtFilter hlim
    have heq : (fun y => ∫ t in c..y, deriv H t) =ᶠ[𝓝 c] (fun y => H y - H c) := by
      filter_upwards [Ioo_mem_nhds ha hb] with y hy
      apply AbsolutelyContinuousOnInterval.integral_deriv_eq_sub
      apply hH.mono
      intro t ht
      rw [uIcc_of_le (ha.trans hb).le]
      rcases mem_uIcc.mp ht with ht | ht
      · exact ⟨ha.le.trans ht.1, ht.2.trans hy.2.le⟩
      · exact ⟨hy.1.le.trans ht.1, ht.2.trans hb.le⟩
    have hsub : HasDerivAt (fun y => H y - H c) (G c) c :=
      hID.congr_of_eventuallyEq heq.symm
    simpa only [sub_add_cancel] using hsub.add_const (H c)
  have hDn : HasDerivAt D 0 c := by
    apply hasDerivAt_iff_tendsto_slope.mpr
    have hz : Tendsto (fun x : ℝ => x - c) (𝓝[≠] c) (𝓝 0) := by
      have hh : ContinuousAt (fun x : ℝ => x - c) c := continuousAt_id.sub continuousAt_const
      simpa only [sub_self] using hh.tendsto.mono_left nhdsWithin_le_nhds
    have hh := hD.mul hz
    have hh0 : Tendsto (fun x => D x / (x - c) ^ 2 * (x - c))
        (𝓝[≠] c) (𝓝 0) := by simpa only [mul_zero] using hh
    apply hh0.congr'
    filter_upwards [self_mem_nhdsWithin] with x hx
    change x ≠ c at hx
    simp only [slope_def_field, hD0, sub_zero]
    field_simp [sub_ne_zero.mpr hx]
  have hDp : ∀ᶠ x in 𝓝[≠] c, 0 < D x := by
    filter_upwards [hD.eventually (lt_mem_nhds hα), self_mem_nhdsWithin] with x hx hn
    change x ≠ c at hn
    simpa only [zero_mul] using
      (lt_div_iff₀ (sq_pos_of_ne_zero (sub_ne_zero.mpr hn))).mp hx
  apply first_order_clip_limits hlohi hHD hDn hD0 hDp hclip
  simpa only [not_and_or] using h0

end RicciFlowSharpEstimate.Analysis
