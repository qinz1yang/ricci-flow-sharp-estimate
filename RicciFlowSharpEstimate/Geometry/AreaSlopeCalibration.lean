/-
Copyright (c) 2026 Ziyang Qin. All rights reserved.
No license is granted by this file.
Authors: Ziyang Qin
-/
import RicciFlowSharpEstimate.Geometry.AreaWarpCalibration
import RicciFlowSharpEstimate.Geometry.AreaSlopeMass

/-! # The slope-weighted comparison on the genuine recoverable class -/

noncomputable section
namespace RicciFlowSharpEstimate.Geometry.AreaProfile
open Set MeasureTheory Filter Topology
open scoped ContDiff ENNReal
local notation "areaμ" => volume.restrict (Ioo (0 : ℝ) 1)

private theorem smooth_action_ge_slope_mass {C : ℝ} {K r : ℝ → ℝ}
    (hC : 1 ≤ C) (hupper : C ≤ 1 + Real.sqrt (3 / 2))
    (h : IsSmoothAreaCompetitor C K r) :
    3 / (16 * C ^ 2) * (∫ x, warp K x * warpSlope K x ^ 2 * r x ^ 2 ∂areaμ) ≤
      meridionalAction K r := by
  obtain ⟨hK, hr, ⟨κ, Λ, hκ, hbox, hratio⟩, hzero, hone, _⟩ := h
  have hC0 : 0 < C := zero_lt_one.trans_le hC
  let T : ℝ := 1 + Real.sqrt (3 / 2)
  have hΛ : Λ ≤ C * κ := (div_le_iff₀ hκ).mp hratio
  have hΛT : Λ ≤ T * κ := hΛ.trans (mul_le_mul_of_nonneg_right hupper hκ.le)
  have hΛ2 : 2 ≤ Λ := by
    have hi := intervalIntegral.integral_mono_on (μ := volume) zero_le_one
      (hK.continuous.intervalIntegrable 0 1)
      (continuous_const.intervalIntegrable 0 1)
      (fun x hx => (hbox x hx).2)
    simpa only [hzero, intervalIntegral.integral_const, sub_zero, one_smul] using hi
  have hκC : 2 ≤ C * κ := hΛ2.trans hΛ
  have hcoeff : 3 / (16 * C ^ 2) ≤ 3 * κ ^ 2 / 64 := by
    apply (div_le_iff₀ (by positivity : 0 < 16 * C ^ 2)).mpr
    have hsq : 4 ≤ (C * κ) ^ 2 := by nlinarith
    nlinarith only [hsq]
  have hs : (Real.sqrt (3 / 2 : ℝ)) ^ 2 = 3 / 2 := Real.sq_sqrt (by norm_num)
  have hT : T ^ 2 = 2 * T + 1 / 2 := by dsimp [T]; nlinarith
  have hpinch : (T * κ) ^ 2 ≤ 2 * κ * (T * κ) + κ ^ 2 / 2 := by
    have hh := congrArg (fun t : ℝ => t * κ ^ 2) hT
    nlinarith only [hh]
  have hA := meridionalAction_ge_slope_mass_of_quadratic_pinching K r hK.continuous
    (hr.of_le (by simp)) hzero hone κ (T * κ) hκ
    (fun x hx => ⟨(hbox x hx).1, (hbox x hx).2.trans hΛT⟩) hpinch
  have hmass : 0 ≤ ∫ x, warp K x * warpSlope K x ^ 2 * r x ^ 2 ∂areaμ := by
    apply integral_nonneg_of_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
    have hf := (warp_nonneg_le_two_mul_min K hK.continuous
      (fun y hy => hκ.le.trans (hbox y hy).1) hzero hone x ⟨hx.1.le, hx.2.le⟩).1
    positivity
  rw [intervalIntegral.integral_of_le zero_le_one, integral_Ioc_eq_integral_Ioo] at hA
  exact (mul_le_mul_of_nonneg_right hcoeff hmass).trans hA

private theorem slope_mass_tendsto {C : ℝ} {K r p z : ℝ → ℝ}
    (hC : 1 ≤ C) (h : IsRecoverableAreaCompetitor C K r p z)
    (Ks rs : ℕ → ℝ → ℝ) (hS : ∀ n, IsSmoothAreaCompetitor C (Ks n) (rs n))
    (hKS : Tendsto (fun n => eLpNorm (Ks n - K) 2 areaμ) atTop (𝓝 0))
    (hRS : Tendsto (fun n => eLpNorm (rs n - r) 2 areaμ) atTop (𝓝 0)) :
    Tendsto (fun n => ∫ x, warp (Ks n) x * warpSlope (Ks n) x ^ 2 * rs n x ^ 2 ∂areaμ)
      atTop (𝓝 (∫ x, warp K x * warpSlope K x ^ 2 * r x ^ 2 ∂areaμ)) := by
  have hC0 : 0 < C := zero_lt_one.trans_le hC
  have hg := h.geometry_bounds hC
  have hKm (n : ℕ) := (hS n).memLp_curvature
  have hrm (n : ℕ) : MemLp (rs n) 2 areaμ :=
    (Analysis.hasParabolicWeakDerivatives_of_contDiff
      ((hS n).2.1.of_le (by simp))).memLp
  have hweak : ∀ v : Lp ℝ 2 areaμ,
      Tendsto (fun n => ∫ x, Ks n x * v x ∂areaμ) atTop
        (𝓝 (∫ x, K x * v x ∂areaμ)) := by
    intro v
    have hv : Tendsto (fun _ : ℕ => eLpNorm ((v : ℝ → ℝ) - (v : ℝ → ℝ)) 2 areaμ)
        atTop (𝓝 0) := by simp only [sub_self, eLpNorm_zero]; exact tendsto_const_nhds
    exact (Analysis.tendsto_integral_mul_of_tendsto_eLpNorm_two hKm h.1
      (fun _ => Lp.memLp v) (Lp.memLp v) hKS hv).2.2
  let a := fun n x => warp (Ks n) x * warpSlope (Ks n) x ^ 2
  let a0 := fun x => warp K x * warpSlope K x ^ 2
  have ha (n : ℕ) : AEStronglyMeasurable (a n) areaμ := by
    exact ((warp_continuous (Ks n) (hS n).1.continuous).mul
      ((warpSlope_continuous (Ks n) (hS n).1.continuous).pow 2)).aestronglyMeasurable
  have ha0 : AEStronglyMeasurable a0 areaμ :=
    ((hg.1.mul (hg.2.1.pow 2)).mono Ioo_subset_Icc_self).aestronglyMeasurable
      measurableSet_Ioo
  have hbound (f b : ℝ) (hf : 0 ≤ f ∧ f ≤ 2 * C) (hb : |b| ≤ 2) :
      |f * b ^ 2| ≤ 8 * C := by
    rw [abs_mul, abs_of_nonneg hf.1, abs_of_nonneg (sq_nonneg b)]
    have hbs : b ^ 2 ≤ 4 := by
      have hh := (sq_le_sq₀ (abs_nonneg b) (by norm_num : (0 : ℝ) ≤ 2)).mpr hb
      simpa only [sq_abs, show (2 : ℝ) ^ 2 = 4 by norm_num] using hh
    calc
      f * b ^ 2 ≤ (2 * C) * 4 := mul_le_mul hf.2 hbs (sq_nonneg b) (by positivity)
      _ = 8 * C := by ring
  have hfbound (f x : ℝ) (hx : x ∈ Ioo (0 : ℝ) 1)
      (hf : (2 / C) * x * (1 - x) ≤ f ∧ f ≤ (2 * C) * x * (1 - x)) :
      0 ≤ f ∧ f ≤ 2 * C := by
    refine ⟨(mul_nonneg (mul_nonneg (by positivity : 0 ≤ 2 / C) hx.1.le)
      (sub_nonneg.mpr hx.2.le)).trans hf.1, ?_⟩
    calc
      f ≤ (2 * C) * x * (1 - x) := hf.2
      _ = (2 * C) * (x * (1 - x)) := by ring
      _ ≤ 2 * C := mul_le_of_le_one_right (by positivity)
        (by nlinarith only [hx.2, sq_nonneg x])
  have hBn (n : ℕ) : ∀ᵐ x ∂areaμ, |a n x| ≤ 8 * C := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
    have hgeo := warp_bounds_of_curvature_bounds (Ks n) (hS n).1.continuous
      (2 / C) (2 * C) (hS n).common_bounds (hS n).2.2.2.1 (hS n).2.2.2.2.1
      x ⟨hx.1.le, hx.2.le⟩
    exact hbound _ _ (hfbound _ x hx hgeo)
      (abs_warpSlope_le_two (Ks n) (hS n).1.continuous
        (fun y hy => (by positivity : 0 ≤ 2 / C).trans ((hS n).common_bounds y hy).1)
        (hS n).2.2.2.1 x ⟨hx.1.le, hx.2.le⟩)
  have hB0 : ∀ᵐ x ∂areaμ, |a0 x| ≤ 8 * C := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
    have hgeo := hg.2.2.1 x ⟨hx.1.le, hx.2.le⟩
    exact hbound _ _ (hfbound _ x hx ⟨hgeo.1, hgeo.2.1⟩) hgeo.2.2
  have haL : ∀ᵐ x ∂areaμ, Tendsto (fun n => a n x) atTop (𝓝 (a0 x)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
    exact (tendsto_warp_of_weak_L2 Ks K hKm h.1 hweak x ⟨hx.1.le, hx.2.le⟩).mul
      ((tendsto_warpSlope_of_weak_L2 Ks K hKm h.1 hweak x ⟨hx.1.le, hx.2.le⟩).pow 2)
  obtain ⟨hmn, hm0, hmL⟩ := Analysis.strong_L2_mul_of_ae_tendsto_of_ae_abs_le
    hrm h.2.1.memLp hRS ha ha0 hBn hB0 haL
  have hpair := (Analysis.tendsto_integral_mul_of_tendsto_eLpNorm_two
    hmn hm0 hrm h.2.1.memLp hmL hRS).2.2
  simpa only [a, a0, pow_two, mul_assoc] using hpair

/-- The complete slope-weighted estimate passes to the actual strong graph
closure of the original class. No minimizing or stationarity hypothesis is used. -/
theorem IsRecoverableAreaCompetitor.action_ge_slope_mass_of_quadratic_pinching
    {C : ℝ} {K r p z : ℝ → ℝ} (hC : 1 ≤ C)
    (hupper : C ≤ 1 + Real.sqrt (3 / 2))
    (h : IsRecoverableAreaCompetitor C K r p z) :
    3 / (16 * C ^ 2) * (∫ x, warp K x * warpSlope K x ^ 2 * r x ^ 2 ∂areaμ) ≤
      weakMeridionalAction K r p z := by
  obtain ⟨_, _, Ks, rs, hS, hKS, hRS, _, _, hA⟩ := h.exists_action_recovery hC
  exact le_of_tendsto_of_tendsto
    ((slope_mass_tendsto hC h Ks rs hS hKS hRS).const_mul _) hA
    (Eventually.of_forall fun n => smooth_action_ge_slope_mass hC hupper (hS n))

/-- Every genuine recoverable unit-mass competitor has strictly positive
complete action throughout the explicit quadratic-pinching range. -/
theorem IsRecoverableAreaCompetitor.action_pos_of_quadratic_pinching
    {C : ℝ} {K r p z : ℝ → ℝ} (hC : 1 ≤ C)
    (hupper : C ≤ 1 + Real.sqrt (3 / 2))
    (h : IsRecoverableAreaCompetitor C K r p z) :
    0 < weakMeridionalAction K r p z := by
  have hC0 : 0 < C := zero_lt_one.trans_le hC
  exact (mul_pos (by positivity : 0 < 3 / (16 * C ^ 2))
    (h.integral_warp_mul_slope_sq_mul_probe_sq_pos hC)).trans_le
      (h.action_ge_slope_mass_of_quadratic_pinching hC hupper)

end RicciFlowSharpEstimate.Geometry.AreaProfile
