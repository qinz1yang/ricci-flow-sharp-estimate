/-
Copyright (c) 2026 Ziyang Qin. All rights reserved.
No license is granted by this file.
Authors: Ziyang Qin
-/
import RicciFlowSharpEstimate.Analysis.PolarDerivativeAsymptotics
import RicciFlowSharpEstimate.Analysis.AbsolutelyContinuousReflection
import Mathlib.Analysis.Calculus.LHopital
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Haar.Unique

/-! # Leading probe rates from the genuine degenerate derivative flux -/

noncomputable section
namespace RicciFlowSharpEstimate.Analysis
open Set MeasureTheory Filter Topology

/-- A first-order warp and a bounded measurable lower coefficient turn the
actual derivative-flux equation into pointwise leading rates for p and r.
No limit of the lower coefficient or of p is assumed. -/
theorem leading_rates_of_degenerate_derivative_flux
    {f K r p q F : ℝ → ℝ} {b c L M : ℝ}
    (hb : 0 < b) (hc : c ≠ 0)
    (hF : AbsolutelyContinuousOnInterval F 0 b) (hF0 : F 0 = 0)
    (hFD : ∀ᵐ x ∂volume.restrict (Ioo (0 : ℝ) b),
      HasDerivAt F (f x * (q x + K x * r x)) x)
    (hFP : ∀ x ∈ Ioo (0 : ℝ) b, F x = f x ^ 2 * p x)
    (hf : Tendsto (fun x => f x / x) (𝓝[>] (0 : ℝ)) (𝓝 c))
    (hK : ∀ᵐ x ∂volume.restrict (Ioo (0 : ℝ) b), |K x| ≤ M)
    (hr : Tendsto r (𝓝[>] (0 : ℝ)) (𝓝 0))
    (hq : Tendsto q (𝓝[>] (0 : ℝ)) (𝓝 L))
    (hrD : ∀ x ∈ Ioo (0 : ℝ) b, HasDerivAt r (p x) x) :
    Tendsto p (𝓝[>] (0 : ℝ)) (𝓝 (L / (2 * c))) ∧
      Tendsto (fun x => r x / x) (𝓝[>] (0 : ℝ)) (𝓝 (L / (2 * c))) := by
  let l := (𝓝[>] (0 : ℝ)) ⊓ ae volume
  have hdom : ∀ᶠ x in 𝓝[>] (0 : ℝ), x ∈ Ioo (0 : ℝ) b := Ioo_mem_nhdsGT hb
  have hKB : ∀ᶠ x in l, |K x| ≤ M := by
    filter_upwards [hdom.filter_mono inf_le_left,
      (ae_imp_of_ae_restrict hK).filter_mono inf_le_right] with x hx hKx
    exact hKx hx
  have hKr : Tendsto (fun x => K x * r x) l (𝓝 0) := by
    apply squeeze_zero_norm' (a := fun x => M * ‖r x‖)
    · filter_upwards [hKB] with x hx
      simpa only [norm_mul, Real.norm_eq_abs] using
        mul_le_mul_of_nonneg_right hx (abs_nonneg (r x))
    · simpa only [norm_zero, mul_zero] using (hr.mono_left inf_le_left).norm.const_mul M
  have hDer : Tendsto (fun x => deriv F x / x) l (𝓝 (c * L)) := by
    have hh := (hf.mono_left inf_le_left).mul ((hq.mono_left inf_le_left).add hKr)
    apply (show Tendsto (fun x => (f x / x) * (q x + K x * r x)) l
      (𝓝 (c * L)) from by simpa only [add_zero] using hh).congr'
    filter_upwards [hdom.filter_mono inf_le_left,
      (ae_imp_of_ae_restrict hFD).filter_mono inf_le_right] with x hx hDx
    rw [(hDx hx).deriv]
    ring
  have hFlux := tendsto_div_sq_of_ae_derivative_quotient hb hF hF0 hDer
  have hP : Tendsto p (𝓝[>] (0 : ℝ)) (𝓝 (L / (2 * c))) := by
    have hh := hFlux.div (hf.pow 2) (pow_ne_zero 2 hc)
    have he : (c * L / 2) / c ^ 2 = L / (2 * c) := by field_simp
    rw [he] at hh
    apply hh.congr'
    filter_upwards [hdom, hf.eventually (isOpen_compl_singleton.mem_nhds hc)] with x hx hfx
    have hfn : f x ≠ 0 := by
      intro heq
      exact hfx (by simp only [heq, zero_div, mem_singleton_iff])
    change (F x / x ^ 2) / (f x / x) ^ 2 = p x
    rw [hFP x hx]
    field_simp [hfn, hx.1.ne']
  refine ⟨hP, ?_⟩
  exact HasDerivAt.lhopital_zero_right_on_Ioo hb hrD
    (fun x _ => hasDerivAt_id x) (fun _ _ => one_ne_zero) hr
    (tendsto_id.mono_left nhdsWithin_le_nhds) (by simpa only [div_one] using hP)

private theorem reflect_right_zero (b : ℝ) :
    Tendsto (fun x : ℝ => b - x) (𝓝[>] 0) (𝓝[<] b) := by
  apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
  · simpa only [sub_zero] using
      (tendsto_const_nhds.sub (tendsto_id.mono_left nhdsWithin_le_nhds) :
        Tendsto (fun x : ℝ => b - x) (𝓝[>] 0) (𝓝 (b - 0)))
  · filter_upwards [self_mem_nhdsWithin] with x hx
    change 0 < x at hx
    change b - x < b
    linarith

private theorem reflect_left_endpoint (b : ℝ) :
    Tendsto (fun x : ℝ => b - x) (𝓝[<] b) (𝓝[>] 0) := by
  apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
  · simpa only [sub_self] using
      (tendsto_const_nhds.sub (tendsto_id.mono_left nhdsWithin_le_nhds) :
        Tendsto (fun x : ℝ => b - x) (𝓝[<] b) (𝓝 (b - b)))
  · filter_upwards [self_mem_nhdsWithin] with x hx
    change x < b at hx
    change 0 < b - x
    exact sub_pos.mpr hx

/-- Exact reflection of the genuine flux gives the right-endpoint rates.
The derivative p acquires the sign of the oriented tail primitive. -/
theorem leading_rates_of_degenerate_derivative_flux_right
    {f K r p q F : ℝ → ℝ} {b c L M : ℝ}
    (hb : 0 < b) (hc : c ≠ 0)
    (hF : AbsolutelyContinuousOnInterval F 0 b) (hFb : F b = 0)
    (hFD : ∀ᵐ x ∂volume.restrict (Ioo (0 : ℝ) b),
      HasDerivAt F (f x * (q x + K x * r x)) x)
    (hFP : ∀ x ∈ Ioo (0 : ℝ) b, F x = f x ^ 2 * p x)
    (hf : Tendsto (fun x => f x / (b - x)) (𝓝[<] b) (𝓝 c))
    (hK : ∀ᵐ x ∂volume.restrict (Ioo (0 : ℝ) b), |K x| ≤ M)
    (hr : Tendsto r (𝓝[<] b) (𝓝 0))
    (hq : Tendsto q (𝓝[<] b) (𝓝 L))
    (hrD : ∀ x ∈ Ioo (0 : ℝ) b, HasDerivAt r (p x) x) :
    Tendsto p (𝓝[<] b) (𝓝 (-L / (2 * c))) ∧
      Tendsto (fun x => r x / (b - x)) (𝓝[<] b) (𝓝 (L / (2 * c))) := by
  let fR := fun x => f (b - x)
  let KR := fun x => K (b - x)
  let rR := fun x => r (b - x)
  let pR := fun x => -p (b - x)
  let qR := fun x => q (b - x)
  let FR := fun x => -F (b - x)
  have href (x : ℝ) (hx : x ∈ Ioo (0 : ℝ) b) : b - x ∈ Ioo (0 : ℝ) b :=
    ⟨sub_pos.mpr hx.2, by linarith [hx.1]⟩
  have hFR : AbsolutelyContinuousOnInterval FR 0 b := by
    simpa only [sub_self, sub_zero, FR] using
      (absolutelyContinuousOnInterval_comp_sub_left (c := b) hF).fun_neg
  have hFR0 : FR 0 = 0 := by simp only [FR, sub_zero, hFb, neg_zero]
  have hFRD : ∀ᵐ x ∂volume.restrict (Ioo (0 : ℝ) b),
      HasDerivAt FR (fR x * (qR x + KR x * rR x)) x := by
    have hd := (volume.measurePreserving_sub_left b).quasiMeasurePreserving.ae
      (ae_imp_of_ae_restrict hFD)
    filter_upwards [hd.filter_mono (ae_mono Measure.restrict_le_self),
      ae_restrict_mem measurableSet_Ioo] with x hx hxI
    have hh := ((hx (href x hxI)).comp x
      ((hasDerivAt_const x b).fun_sub (hasDerivAt_id x))).fun_neg
    simpa only [FR, fR, qR, KR, rR, Function.comp_def, zero_sub,
      mul_neg_one, neg_neg, id_eq] using hh
  have hKRD : ∀ᵐ x ∂volume.restrict (Ioo (0 : ℝ) b), |KR x| ≤ M := by
    have hd := (volume.measurePreserving_sub_left b).quasiMeasurePreserving.ae
      (ae_imp_of_ae_restrict hK)
    filter_upwards [hd.filter_mono (ae_mono Measure.restrict_le_self),
      ae_restrict_mem measurableSet_Ioo] with x hx hxI
    exact hx (href x hxI)
  have hrRD (x : ℝ) (hx : x ∈ Ioo (0 : ℝ) b) : HasDerivAt rR (pR x) x := by
    simpa only [rR, pR, Function.comp_def, zero_sub, mul_neg_one, id_eq] using
      (hrD (b - x) (href x hx)).comp x
        ((hasDerivAt_const x b).fun_sub (hasDerivAt_id x))
  have hfR : Tendsto (fun x => fR x / x) (𝓝[>] (0 : ℝ)) (𝓝 c) := by
    simpa only [fR, Function.comp_def, sub_sub_cancel] using hf.comp (reflect_right_zero b)
  obtain ⟨hPR, hrR⟩ := leading_rates_of_degenerate_derivative_flux hb hc hFR hFR0 hFRD
    (fun x hx => by dsimp only [FR, fR, pR]; rw [hFP (b - x) (href x hx)]; ring)
    hfR hKRD (hr.comp (reflect_right_zero b)) (hq.comp (reflect_right_zero b)) hrRD
  constructor
  · simpa only [pR, Function.comp_def, sub_sub_cancel, neg_neg, neg_div] using
      hPR.neg.comp (reflect_left_endpoint b)
  · simpa only [rR, Function.comp_def, sub_sub_cancel] using
      hrR.comp (reflect_left_endpoint b)

end RicciFlowSharpEstimate.Analysis
