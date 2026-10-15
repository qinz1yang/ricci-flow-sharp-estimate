/-
Copyright (c) 2026 Ziyang Qin. All rights reserved.
No license is granted by this file.
Authors: Ziyang Qin
-/
import RicciFlowSharpEstimate.Geometry.RecoverableAreaRegularity
import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun

/-! # Physical slope increments divided by distance to the pole -/

noncomputable section
namespace RicciFlowSharpEstimate.Geometry.AreaProfile
open Set MeasureTheory Filter Topology
local notation "areaμ" => volume.restrict (Ioo (0 : ℝ) 1)

/-- The actual curvature slope is AC through both poles. Its increments from
the two physical slope values have bounded reciprocal-distance quotients,
with no continuity or derivative assumption on the original curvature. -/
theorem IsRecoverableAreaCompetitor.slope_pole_quotient_bounds
    {C : ℝ} {K r p z : ℝ → ℝ} (hC : 1 ≤ C)
    (h : IsRecoverableAreaCompetitor C K r p z) :
    AbsolutelyContinuousOnInterval (warpSlope K) 0 1 ∧
      ∀ x ∈ Ioo (0 : ℝ) 1,
        |(2 - warpSlope K x) / x| ≤ 4 * C ∧
        |(2 + warpSlope K x) / (1 - x)| ≤ 4 * C := by
  have hg := h.geometry_bounds hC
  have hKI : IntervalIntegrable K volume 0 1 :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le zero_le_one).mpr
      (h.1.integrable (by norm_num : (1 : ENNReal) ≤ 2))
  have hbAC : AbsolutelyContinuousOnInterval (warpSlope K) 0 1 := by
    have hp := hKI.absolutelyContinuousOnInterval_intervalIntegral
      (show (0 : ℝ) ∈ uIcc (0 : ℝ) 1 by simp)
    have hcCD : ContDiffOn ℝ 1 (fun _ : ℝ => (2 : ℝ)) (uIcc (0 : ℝ) 1) :=
      contDiff_const.contDiffOn
    have hc : AbsolutelyContinuousOnInterval (fun _ : ℝ => (2 : ℝ)) 0 1 :=
      hcCD.absolutelyContinuousOnInterval
    change AbsolutelyContinuousOnInterval (fun x => 2 - 2 * ∫ t in (0 : ℝ)..x, K t) 0 1
    exact hc.fun_sub (hp.const_mul 2)
  have hDB : ∀ᵐ x ∂areaμ, |deriv (warpSlope K) x| ≤ 4 * C := by
    filter_upwards [(h.primitive_local_regularity hC).2.2, hg.2.2.2.2] with x hx hK
    rw [hx.deriv, abs_mul, abs_neg,
      abs_of_nonneg ((by positivity : (0 : ℝ) ≤ 2 / C).trans hK.1)]
    norm_num
    linarith [hK.2]
  have hInc (a b : ℝ) (ha : a ∈ Icc (0 : ℝ) 1) (hb : b ∈ Icc (0 : ℝ) 1) :
      |warpSlope K b - warpSlope K a| ≤ 4 * C * |b - a| := by
    have hs : uIcc a b ⊆ uIcc (0 : ℝ) 1 := uIcc_subset_uIcc
      (by simpa only [uIcc_of_le zero_le_one] using ha)
      (by simpa only [uIcc_of_le zero_le_one] using hb)
    rw [← (hbAC.mono hs).integral_deriv_eq_sub]
    have hi := intervalIntegral.norm_integral_le_of_norm_le_const_ae
      (f := deriv (warpSlope K)) (C := 4 * C) (a := a) (b := b) (by
        filter_upwards [ae_imp_of_ae_restrict hDB, volume.ae_ne (0 : ℝ),
          volume.ae_ne (1 : ℝ)] with x hx hx0 hx1 hxI
        have hxC : x ∈ Icc (0 : ℝ) 1 := by
          simpa only [uIcc_of_le zero_le_one] using hs (uIoc_subset_uIcc hxI)
        rw [Real.norm_eq_abs]
        exact hx ⟨lt_of_le_of_ne hxC.1 (Ne.symm hx0), lt_of_le_of_ne hxC.2 hx1⟩)
    simpa only [Real.norm_eq_abs] using hi
  refine ⟨hbAC, ?_⟩
  intro x hx
  have hL := hInc 0 x ⟨le_rfl, zero_le_one⟩ ⟨hx.1.le, hx.2.le⟩
  have hR := hInc x 1 ⟨hx.1.le, hx.2.le⟩ ⟨zero_le_one, le_rfl⟩
  rw [hg.2.2.2.1.2.2.1, sub_zero, abs_of_pos hx.1, abs_sub_comm] at hL
  rw [hg.2.2.2.1.2.2.2, show -2 - warpSlope K x = -(2 + warpSlope K x) by ring,
    abs_neg, abs_of_pos (sub_pos.mpr hx.2)] at hR
  constructor
  · rw [abs_div, abs_of_pos hx.1]
    exact (div_le_iff₀ hx.1).mpr hL
  · rw [abs_div, abs_of_pos (sub_pos.mpr hx.2)]
    exact (div_le_iff₀ (sub_pos.mpr hx.2)).mpr hR

/-- On the two canonical physical half intervals, the inverse warp times
pole distance and both corrected slope ratios have box-only bounds. -/
theorem IsRecoverableAreaCompetitor.primitive_polar_ratio_bounds
    {C : ℝ} {K r p z : ℝ → ℝ} (hC : 1 ≤ C)
    (h : IsRecoverableAreaCompetitor C K r p z) :
    (∀ x ∈ Ioo (0 : ℝ) (1 / 2), |x / warp K x| ≤ C ∧
      |(2 - warpSlope K x) / warp K x| ≤ 4 * C ^ 2) ∧
    (∀ x ∈ Ioo (1 / 2 : ℝ) 1, |(1 - x) / warp K x| ≤ C ∧
      |(2 + warpSlope K x) / warp K x| ≤ 4 * C ^ 2) := by
  let f := warp K
  let b := warpSlope K
  let uL := fun x => 2 - b x
  let uR := fun x => 2 + b x
  have hC0 : 0 < C := zero_lt_one.trans_le hC
  have hg := h.geometry_bounds hC
  have hGeom := h.slope_pole_quotient_bounds hC
  have hSubL : Ioo (0 : ℝ) (1 / 2) ⊆ Ioo (0 : ℝ) 1 :=
    fun _ hx => ⟨hx.1, by linarith [hx.2]⟩
  have hSubR : Ioo (1 / 2 : ℝ) 1 ⊆ Ioo (0 : ℝ) 1 :=
    fun _ hx => ⟨by linarith [hx.1], hx.2⟩
  have hfpos (x : ℝ) (hx : x ∈ Ioo (0 : ℝ) 1) : 0 < f x :=
    (mul_pos (mul_pos (by positivity : (0 : ℝ) < 2 / C) hx.1)
      (sub_pos.mpr hx.2)).trans_le (hg.2.2.1 x ⟨hx.1.le, hx.2.le⟩).1
  have hCf (x : ℝ) (hx : x ∈ Ioo (0 : ℝ) 1) : 2 * (x * (1 - x)) ≤ C * f x := by
    have hm := mul_le_mul_of_nonneg_left (hg.2.2.1 x ⟨hx.1.le, hx.2.le⟩).1 hC0.le
    have heq : C * (2 / C * x * (1 - x)) = 2 * (x * (1 - x)) := by
      field_simp [hC0.ne']
    rwa [heq] at hm
  have hRatio (x d u : ℝ) (hx : x ∈ Ioo (0 : ℝ) 1)
      (hd : 0 < d) (hdF : d ≤ C * f x) (huD : |u / d| ≤ 4 * C) :
      |d / f x| ≤ C ∧ |u / f x| ≤ 4 * C ^ 2 := by
    have hdB : |d / f x| ≤ C := by
      rw [abs_of_pos (div_pos hd (hfpos x hx))]
      exact (div_le_iff₀ (hfpos x hx)).mpr hdF
    refine ⟨hdB, ?_⟩
    have heq : u / f x = (u / d) * (d / f x) := by field_simp [hd.ne']
    rw [heq, abs_mul]
    have hh := mul_le_mul huD hdB (abs_nonneg _) (by positivity : 0 ≤ 4 * C)
    nlinarith only [hh]
  have hRatioL (x : ℝ) (hx : x ∈ Ioo (0 : ℝ) (1 / 2)) :
      |x / f x| ≤ C ∧ |uL x / f x| ≤ 4 * C ^ 2 := by
    apply hRatio x x (uL x) (hSubL hx) hx.1
    · have hh := hCf x (hSubL hx)
      nlinarith [mul_nonneg hx.1.le (show 0 ≤ 1 - 2 * x by linarith [hx.2])]
    · exact (hGeom.2 x (hSubL hx)).1
  have hRatioR (x : ℝ) (hx : x ∈ Ioo (1 / 2 : ℝ) 1) :
      |(1 - x) / f x| ≤ C ∧ |uR x / f x| ≤ 4 * C ^ 2 := by
    apply hRatio x (1 - x) (uR x) (hSubR hx) (sub_pos.mpr hx.2)
    · have hh := hCf x (hSubR hx)
      nlinarith [mul_nonneg (sub_nonneg.mpr hx.2.le)
        (show 0 ≤ 2 * x - 1 by linarith [hx.1])]
    · exact (hGeom.2 x (hSubR hx)).2
  exact ⟨hRatioL, hRatioR⟩

end RicciFlowSharpEstimate.Geometry.AreaProfile
