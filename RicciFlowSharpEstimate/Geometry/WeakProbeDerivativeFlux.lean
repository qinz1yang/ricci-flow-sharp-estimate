/-
Copyright (c) 2026 Ziyang Qin. All rights reserved.
No license is granted by this file.
Authors: Ziyang Qin
-/
import RicciFlowSharpEstimate.Geometry.RecoverableAreaRegularity
import RicciFlowSharpEstimate.Analysis.IntegrableBoundaryTrace

/-!
# Actual derivative flux and natural weak pole traces

The literal first-order divergence flux is `f²p`. Its derivative is integrable
on the full physical interval. A local primitive therefore extends the flux
absolutely continuously. The weighted graph makes both inverse-distance flux
quotients integrable, forcing the extension's two endpoint traces to vanish.
This is a trace proof, not just substitution of the zero warp at a pole.
-/

noncomputable section
namespace RicciFlowSharpEstimate.Geometry.AreaProfile
open Set MeasureTheory Filter Topology
local notation "areaμ" => volume.restrict (Ioo (0 : ℝ) 1)

/-- The actual first-order derivative flux of a probe with weak derivative p. -/
def weakProbeDerivativeFlux (K p : ℝ → ℝ) (x : ℝ) : ℝ := warp K x ^ 2 * p x

private theorem flux_div_bound (f p w d hi : ℝ)
    (hw0 : 0 ≤ w) (hw1 : w ≤ 1) (hd : 0 < d) (hwd : w ≤ d)
    (hhi : 0 ≤ hi) (hf0 : 0 ≤ f) (hfhi : f ≤ hi * w) :
    |f ^ 2 * p / d| ≤ hi ^ 2 * |Real.sqrt w * p| := by
  have hs0 := Real.sqrt_nonneg w
  have hs2 := Real.sq_sqrt hw0
  have hs1 : Real.sqrt w ≤ 1 := by nlinarith
  have hws : w ≤ Real.sqrt w := by
    nlinarith [mul_nonneg hs0 (sub_nonneg.mpr hs1)]
  have hww := mul_le_mul hws hwd hw0 hs0
  have hsq : f ^ 2 ≤ (hi * w) ^ 2 := by
    nlinarith only [mul_nonneg (sub_nonneg.mpr hfhi)
      (add_nonneg (mul_nonneg hhi hw0) hf0)]
  have hcoef : f ^ 2 / d ≤ hi ^ 2 * Real.sqrt w := by
    apply (div_le_iff₀ hd).2
    calc
      f ^ 2 ≤ (hi * w) ^ 2 := hsq
      _ = hi ^ 2 * (w * w) := by ring
      _ ≤ hi ^ 2 * (Real.sqrt w * d) := mul_le_mul_of_nonneg_left hww (sq_nonneg hi)
      _ = hi ^ 2 * Real.sqrt w * d := by ring
  rw [abs_div, abs_mul, abs_of_nonneg (sq_nonneg f), abs_of_pos hd,
    abs_mul, abs_of_nonneg hs0]
  calc
    f ^ 2 * |p| / d = (f ^ 2 / d) * |p| := by ring
    _ ≤ (hi ^ 2 * Real.sqrt w) * |p| := mul_le_mul_of_nonneg_right hcoef (abs_nonneg p)
    _ = hi ^ 2 * (Real.sqrt w * |p|) := by ring

private theorem derivative_flux_integrability
    {C : ℝ} {K r p z : ℝ → ℝ} (hC : 1 ≤ C)
    (h : IsRecoverableAreaCompetitor C K r p z) :
    Integrable (fun x => warp K x * (weakMeridionalOperator K r p z x + K x * r x)) areaμ ∧
      Integrable (fun x => weakProbeDerivativeFlux K p x / x) areaμ ∧
      Integrable (fun x => weakProbeDerivativeFlux K p x / (1 - x)) areaμ := by
  have hCpos : 0 < C := zero_lt_one.trans_le hC
  have hg := h.geometry_bounds hC
  have hf : AEStronglyMeasurable (warp K) areaμ :=
    ((hg.1.mono Ioo_subset_Icc_self).locallyIntegrableOn measurableSet_Ioo).aestronglyMeasurable
  have hb : AEStronglyMeasurable (warpSlope K) areaμ :=
    ((hg.2.1.mono Ioo_subset_Icc_self).locallyIntegrableOn measurableSet_Ioo).aestronglyMeasurable
  have hpM : AEStronglyMeasurable p areaμ :=
    h.2.1.weakDeriv.locallyIntegrable_deriv.aestronglyMeasurable
  have hKbox : ∀ᵐ x ∂areaμ, 0 ≤ K x ∧ K x ≤ 2 * C := by
    filter_upwards [hg.2.2.2.2] with x hx
    exact ⟨(by positivity : (0 : ℝ) ≤ 2 / C).trans hx.1, hx.2⟩
  have hfbox : ∀ᵐ x ∂areaμ,
      0 ≤ warp K x ∧ warp K x ≤ (2 * C) * (x * (1 - x)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
    have hh := hg.2.2.1 x ⟨hx.1.le, hx.2.le⟩
    exact ⟨(mul_nonneg (mul_nonneg (by positivity : (0 : ℝ) ≤ 2 / C) hx.1.le)
      (sub_nonneg.mpr hx.2.le)).trans hh.1, by simpa only [mul_assoc] using hh.2.1⟩
  have hbbox : ∀ᵐ x ∂areaμ, |warpSlope K x| ≤ 2 := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
    exact (hg.2.2.1 x ⟨hx.1.le, hx.2.le⟩).2.2
  have hw (x : ℝ) (hx : x ∈ Ioo (0 : ℝ) 1) :
      0 ≤ x * (1 - x) ∧ x * (1 - x) ≤ 1 := by
    exact ⟨mul_nonneg hx.1.le (sub_nonneg.mpr hx.2.le), by nlinarith [sq_nonneg x]⟩
  have hsf : MemLp (fun x => Real.sqrt (warp K x)) 2 areaμ := by
    apply MemLp.of_bound (Real.continuous_sqrt.comp_aestronglyMeasurable hf)
      (Real.sqrt (2 * C))
    filter_upwards [hfbox, ae_restrict_mem measurableSet_Ioo] with x hx hxI
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
    apply Real.sqrt_le_sqrt
    exact hx.2.trans (by nlinarith [(hw x hxI).2])
  obtain ⟨hQ, hR⟩ := memLp_weak_operator_and_potential_of_warp_bounds
    K r p z (2 * C) h.2.1 (by positivity) h.1.aestronglyMeasurable hf hb hKbox hfbox hbbox
  have hS : Integrable (fun x => warp K x *
      (weakMeridionalOperator K r p z x + K x * r x)) areaμ := by
    apply (memLp_one_iff_integrable.mp (hsf.mul (hQ.add hR))).congr
    filter_upwards [hfbox] with x hx
    calc
      Real.sqrt (warp K x) *
          (Real.sqrt (warp K x) * weakMeridionalOperator K r p z x +
            Real.sqrt (warp K x) * (K x * r x)) =
          (Real.sqrt (warp K x) * Real.sqrt (warp K x)) *
            (weakMeridionalOperator K r p z x + K x * r x) := by ring
      _ = _ := by rw [Real.mul_self_sqrt hx.1]
  have hP := (h.2.1.memLp_weighted_deriv.integrable (by norm_num : (1 : ENNReal) ≤ 2)).abs
  have hFLM : AEStronglyMeasurable (fun x => weakProbeDerivativeFlux K p x / x) areaμ := by
    simpa only [weakProbeDerivativeFlux, Pi.pow_def, Pi.mul_def, Pi.div_def, id_eq] using
      ((hf.pow 2).mul hpM).div₀ continuous_id.aestronglyMeasurable
  have hFRM : AEStronglyMeasurable
      (fun x => weakProbeDerivativeFlux K p x / (1 - x)) areaμ := by
    simpa only [weakProbeDerivativeFlux, Pi.pow_def, Pi.mul_def, Pi.div_def,
      Pi.sub_def, id_eq] using
      ((hf.pow 2).mul hpM).div₀
        (show Continuous (fun x : ℝ => 1 - x) from
          continuous_const.sub continuous_id).aestronglyMeasurable
  refine ⟨hS, ?_, ?_⟩
  · apply (hP.const_mul ((2 * C) ^ 2)).mono' hFLM
    filter_upwards [hfbox, ae_restrict_mem measurableSet_Ioo] with x hx hxI
    simpa only [Real.norm_eq_abs, weakProbeDerivativeFlux] using
      flux_div_bound (warp K x) (p x) (x * (1 - x)) x (2 * C)
        (hw x hxI).1 (hw x hxI).2 hxI.1 (by nlinarith [hxI.1, hxI.2])
        (by positivity) hx.1 hx.2
  · apply (hP.const_mul ((2 * C) ^ 2)).mono' hFRM
    filter_upwards [hfbox, ae_restrict_mem measurableSet_Ioo] with x hx hxI
    simpa only [Real.norm_eq_abs, weakProbeDerivativeFlux] using
      flux_div_bound (warp K x) (p x) (x * (1 - x)) (1 - x) (2 * C)
        (hw x hxI).1 (hw x hxI).2 (sub_pos.mpr hxI.2)
        (by nlinarith [hxI.1, hxI.2]) (by positivity) hx.1 hx.2

private theorem uIcc_subset_area {a b : ℝ}
    (ha : a ∈ Ioo (0 : ℝ) 1) (hb : b ∈ Ioo (0 : ℝ) 1) :
    uIcc a b ⊆ Ioo (0 : ℝ) 1 := by
  intro x hx
  rcases mem_uIcc.mp hx with hx | hx
  · exact ⟨ha.1.trans_le hx.1, hx.2.trans_lt hb.2⟩
  · exact ⟨hb.1.trans_le hx.1, hx.2.trans_lt ha.2⟩

/-- The literal derivative flux extends absolutely continuously through both
poles and has genuine zero traces. Weighted graph integrability supplies the
traces; no endpoint value of the weak probe or its derivative is prescribed. -/
theorem IsRecoverableAreaCompetitor.derivative_flux_absolutelyContinuous
    {C : ℝ} {K r p z : ℝ → ℝ} (hC : 1 ≤ C)
    (h : IsRecoverableAreaCompetitor C K r p z)
    (hp : ContinuousOn p (Ioo (0 : ℝ) 1)) :
    AbsolutelyContinuousOnInterval (weakProbeDerivativeFlux K p) 0 1 ∧
      weakProbeDerivativeFlux K p 0 = 0 ∧ weakProbeDerivativeFlux K p 1 = 0 ∧
      (∀ᵐ x ∂areaμ, HasDerivAt (weakProbeDerivativeFlux K p)
        (warp K x * (weakMeridionalOperator K r p z x + K x * r x)) x) := by
  let F := weakProbeDerivativeFlux K p
  let S := fun x => warp K x * (weakMeridionalOperator K r p z x + K x * r x)
  have hg := h.geometry_bounds hC
  have hfD := (h.primitive_local_regularity hC).1
  have hfC : ContDiffOn ℝ 1 (warp K) (Ioo (0 : ℝ) 1) :=
    (h.primitive_weak_derivatives hC).1.contDiffOn_one_of_continuousOn
      (hg.1.mono Ioo_subset_Icc_self) (hg.2.1.mono Ioo_subset_Icc_self)
  have hFAC (a b : ℝ) (ha : a ∈ Ioo (0 : ℝ) 1) (hb : b ∈ Ioo (0 : ℝ) 1) :
      AbsolutelyContinuousOnInterval F a b := by
    have hfa := ((hfC.pow 2).mono (uIcc_subset_area ha hb)).absolutelyContinuousOnInterval
    have hpa := h.2.1.weakDeriv_deriv.absolutelyContinuousOnInterval hp ha hb
    change AbsolutelyContinuousOnInterval (fun x => warp K x ^ 2 * p x) a b
    simpa only [Pi.mul_def, Pi.pow_def] using hfa.mul hpa
  have hFD : ∀ᵐ x ∂areaμ, HasDerivAt F (S x) x := by
    filter_upwards [h.2.1.weakDeriv_deriv.ae_hasDerivAt_of_continuousOn hp,
      ae_restrict_mem measurableSet_Ioo] with x hx hxI
    have hd := ((hfD x hxI).pow 2).mul hx
    convert hd using 1
    · rfl
    · simp only [S, weakMeridionalOperator, Nat.cast_ofNat, Nat.reduceSub, pow_one, Pi.pow_apply]
      ring
  obtain ⟨hSI, hFL, hFR⟩ := derivative_flux_integrability hC h
  have hSI' : IntervalIntegrable S volume 0 1 :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le zero_le_one).mpr hSI
  let c : ℝ := 1 / 2
  have hc : c ∈ Ioo (0 : ℝ) 1 := by norm_num [c]
  let G := fun x => F c + ∫ t in c..x, S t
  have hGAC : AbsolutelyContinuousOnInterval G 0 1 := by
    have hConst : AbsolutelyContinuousOnInterval (fun _ : ℝ => F c) 0 1 :=
      ((contDiff_const : ContDiff ℝ 1 (fun _ : ℝ => F c)).contDiffOn).absolutelyContinuousOnInterval
    exact hConst.fun_add (hSI'.absolutelyContinuousOnInterval_intervalIntegral (by norm_num [c]))
  have hEq (x : ℝ) (hx : x ∈ Ioo (0 : ℝ) 1) : G x = F x := by
    have hi := (hFAC c x hc hx).integral_deriv_eq_sub
    have hInt : (∫ t in c..x, deriv F t) = ∫ t in c..x, S t := by
      apply intervalIntegral.integral_congr_ae
      filter_upwards [ae_imp_of_ae_restrict hFD] with t ht htI
      exact (ht (uIcc_subset_area hc hx (uIoc_subset_uIcc htI))).deriv
    rw [hInt] at hi
    dsimp only [G]
    linarith
  have hGL : IntegrableOn (fun x => G x / (x - 0)) (Ioo (0 : ℝ) 1) := by
    apply hFL.congr
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
    simp only [sub_zero, hEq x hx, F]
  have hGR : IntegrableOn (fun x => G x / (1 - x)) (Ioo (0 : ℝ) 1) := by
    apply hFR.congr
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
    rw [hEq x hx]
  have hGC : ContinuousOn G (Icc (0 : ℝ) 1) := by
    simpa only [uIcc_of_le zero_le_one] using hGAC.continuousOn
  have hG0 := Analysis.eq_zero_of_integrableOn_div_left zero_lt_one hGC hGL
  have hG1 := Analysis.eq_zero_of_integrableOn_div_right zero_lt_one hGC hGR
  have hF0 : F 0 = 0 := by simp [F, weakProbeDerivativeFlux, warp_zero]
  have hF1 : F 1 = 0 := by
    simp only [F, weakProbeDerivativeFlux, hg.2.2.2.1.2.1, zero_pow (by norm_num : 2 ≠ 0),
      zero_mul]
  have hClosed : EqOn G F (uIcc (0 : ℝ) 1) := by
    rw [uIcc_of_le zero_le_one]
    intro x hx
    by_cases h0 : x = 0
    · simp only [h0, hG0, hF0]
    by_cases h1 : x = 1
    · simp only [h1, hG1, hF1]
    exact hEq x ⟨lt_of_le_of_ne hx.1 (Ne.symm h0), lt_of_le_of_ne hx.2 h1⟩
  exact ⟨hGAC.congr hClosed, hF0, hF1, hFD⟩

end RicciFlowSharpEstimate.Geometry.AreaProfile
