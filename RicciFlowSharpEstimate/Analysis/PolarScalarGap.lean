/-
Copyright (c) 2026 Ziyang Qin. All rights reserved.
No license is granted by this file.
Authors: Ziyang Qin
-/
import RicciFlowSharpEstimate.Analysis.PolarEndpointBounds
import RicciFlowSharpEstimate.Analysis.PolarSquareCompletion
import RicciFlowSharpEstimate.Analysis.CircleWirtinger
import Mathlib.MeasureTheory.Integral.Prod

/-!
# A positive polar scalar gap

Smooth vanishing at both poles controls every singular energy term. The radial
square completion and the angular Wirtinger inequality then give a positive
weighted scalar lower bound without any finite-energy hypothesis.
-/

noncomputable section

namespace RicciFlowSharpEstimate.Analysis

open MeasureTheory Set
open scoped ContDiff

private theorem integrable_rectangle_of_continuous (f : ℝ × ℝ → ℝ)
    (hf : Continuous f) (a b : ℝ) :
    Integrable f ((volume.restrict (Ioc 0 Real.pi)).prod (volume.restrict (Ioc a b))) := by
  rw [Measure.prod_restrict]
  exact (hf.continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)).mono_set
    (Set.prod_mono Ioc_subset_Icc_self Ioc_subset_Icc_self)

private theorem sq_div_polarWeight_le {v t w C m : ℝ}
    (ht : 0 ≤ t) (ht1 : t ≤ 1) (hm : 0 < m) (hmw : m ≤ w)
    (hC : 0 ≤ C) (hv : |v| ≤ C * t) :
    0 ≤ v ^ 2 / (t * w) ∧ v ^ 2 / (t * w) ≤ C ^ 2 / m := by
  have hw : 0 < w := hm.trans_le hmw
  refine ⟨div_nonneg (sq_nonneg _) (mul_nonneg ht hw.le), ?_⟩
  by_cases ht0 : t = 0
  · simp [ht0, div_nonneg (sq_nonneg C) hm.le]
  have htpos : 0 < t := lt_of_le_of_ne ht (Ne.symm ht0)
  have hv2 : v ^ 2 ≤ C ^ 2 * t := by
    have habs := (sq_le_sq₀ (abs_nonneg v) (mul_nonneg hC ht)).mpr hv
    rw [sq_abs, mul_pow] at habs
    have ht2 : t ^ 2 ≤ t := by nlinarith
    exact habs.trans (mul_le_mul_of_nonneg_left ht2 (sq_nonneg C))
  calc
    v ^ 2 / (t * w) ≤ (C ^ 2 * t) / (t * w) :=
      div_le_div_of_nonneg_right hv2 (mul_pos htpos hw).le
    _ = C ^ 2 / w := by field_simp
    _ ≤ C ^ 2 / m := div_le_div_of_nonneg_left (sq_nonneg C) hm hmw

private theorem integrable_polar_quotient_of_bound (f : ℝ × ℝ → ℝ) (w : ℝ → ℝ)
    (hf : Continuous f) (hw : Continuous w) (hwpos : ∀ s ∈ Icc 0 Real.pi, 0 < w s)
    (a b C : ℝ) (hC : 0 ≤ C)
    (hbound : ∀ s ∈ Icc 0 Real.pi, ∀ θ ∈ Icc a b, |f (s, θ)| ≤ C * Real.sin s) :
    Integrable (fun x : ℝ × ℝ => f x ^ 2 / (Real.sin x.1 * w x.1))
      ((volume.restrict (Ioc 0 Real.pi)).prod (volume.restrict (Ioc a b))) := by
  obtain ⟨z, hz, hmin⟩ := isCompact_Icc.exists_isMinOn
    (show (Icc (0 : ℝ) Real.pi).Nonempty from ⟨0, le_rfl, Real.pi_pos.le⟩) hw.continuousOn
  have hm : 0 < w z := hwpos z hz
  have hmeas : Measurable (fun x : ℝ × ℝ => f x ^ 2 / (Real.sin x.1 * w x.1)) :=
    (hf.measurable.pow_const 2).div
      ((Real.continuous_sin.comp continuous_fst).mul (hw.comp continuous_fst)).measurable
  apply (integrable_const (C ^ 2 / w z)).mono' hmeas.aestronglyMeasurable
  rw [Measure.prod_restrict]
  filter_upwards [ae_restrict_mem (measurableSet_Ioc.prod measurableSet_Ioc)] with x hx
  have hs : x.1 ∈ Icc 0 Real.pi := ⟨hx.1.1.le, hx.1.2⟩
  have hθ : x.2 ∈ Icc a b := ⟨hx.2.1.le, hx.2.2⟩
  obtain ⟨hnonneg, hle⟩ := sq_div_polarWeight_le
    (Real.sin_nonneg_of_mem_Icc hs) (Real.sin_le_one x.1) hm (hmin hs) hC
    (hbound x.1 hs x.2 hθ)
  simpa only [Real.norm_eq_abs, abs_of_nonneg hnonneg] using hle

/-- All polar energy terms are integrable on a compact angular strip. In order,
the factors are the radial energy, value quotient, angular energy, completed square,
boundary derivative, positive remainder, potential, and boundary primitive. -/
theorem integrable_polar_energy_terms (q : ℝ × ℝ → ℝ) (w : ℝ → ℝ)
    (hq : ContDiff ℝ 2 q) (hzero : ∀ θ, q (0, θ) = 0)
    (hpi : ∀ θ, q (Real.pi, θ) = 0)
    (hw : Continuous w) (hwpos : ∀ s ∈ Icc 0 Real.pi, 0 < w s) (a b : ℝ) :
    let W := fun s => Real.sin s * w s
    let μ := (volume.restrict (Ioc (0 : ℝ) Real.pi)).prod (volume.restrict (Ioc a b))
    Integrable (fun x : ℝ × ℝ => W x.1 * (deriv (fun t => q (t, x.2)) x.1) ^ 2) μ ∧
    Integrable (fun x : ℝ × ℝ => q x ^ 2 / W x.1) μ ∧
    Integrable (fun x : ℝ × ℝ => (deriv (fun t => q (x.1, t)) x.2) ^ 2 / W x.1) μ ∧
    Integrable (fun x : ℝ × ℝ =>
      (W x.1 * deriv (fun t => q (t, x.2)) x.1 - Real.cos x.1 * q x) ^ 2 / W x.1) μ ∧
    Integrable (fun x : ℝ × ℝ => -Real.sin x.1 * q x ^ 2 +
      2 * Real.cos x.1 * q x * deriv (fun t => q (t, x.2)) x.1) μ ∧
    Integrable (fun x : ℝ × ℝ => Real.sin x.1 ^ 2 * q x ^ 2 / W x.1) μ ∧
    Integrable (fun x : ℝ × ℝ => Real.sin x.1 * q x ^ 2) μ ∧
    Integrable (fun x : ℝ × ℝ => Real.cos x.1 * q x ^ 2) μ := by
  dsimp only
  have hr : Continuous (fun x : ℝ × ℝ => deriv (fun t => q (t, x.2)) x.1) :=
    (contDiff_deriv_fst hq (m := 1) (by norm_num)).continuous
  have ha : Continuous (fun x : ℝ × ℝ => deriv (fun t => q (x.1, t)) x.2) :=
    (contDiff_deriv_snd hq (m := 1) (by norm_num)).continuous
  have hW : Continuous (fun x : ℝ × ℝ => Real.sin x.1 * w x.1) :=
    (Real.continuous_sin.comp continuous_fst).mul (hw.comp continuous_fst)
  have hR := integrable_rectangle_of_continuous _ (hW.mul (hr.pow 2)) a b
  obtain ⟨C, hC, hbound⟩ := exists_pos_polar_endpoint_bounds q hq hzero hpi a b
  have hV := integrable_polar_quotient_of_bound q w hq.continuous hw hwpos a b C hC.le
    (fun s hs θ hθ => (hbound s hs θ hθ).1)
  have hA := integrable_polar_quotient_of_bound _ w ha hw hwpos a b C hC.le
    (fun s hs θ hθ => (hbound s hs θ hθ).2.2)
  have hP := integrable_rectangle_of_continuous _
    ((Real.continuous_sin.comp continuous_fst).mul (hq.continuous.pow 2)) a b
  have hcross := integrable_rectangle_of_continuous _
    ((((continuous_const (y := (2 : ℝ))).mul
      (Real.continuous_cos.comp continuous_fst)).mul hq.continuous).mul hr)
    a b
  have hB := hP.neg.add hcross
  have hprimitive := integrable_rectangle_of_continuous _
    ((Real.continuous_cos.comp continuous_fst).mul (hq.continuous.pow 2)) a b
  have hcosV := hV.bdd_mul
    ((Real.continuous_cos.comp continuous_fst).pow 2).aestronglyMeasurable
    (Filter.Eventually.of_forall (fun x => show ‖Real.cos x.1 ^ 2‖ ≤ (1 : ℝ) by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      nlinarith [Real.sin_sq_add_cos_sq x.1, sq_nonneg (Real.sin x.1)]))
  have hG := hV.bdd_mul
    ((Real.continuous_sin.comp continuous_fst).pow 2).aestronglyMeasurable
    (Filter.Eventually.of_forall (fun x => show ‖Real.sin x.1 ^ 2‖ ≤ (1 : ℝ) by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      nlinarith [Real.sin_sq_add_cos_sq x.1, sq_nonneg (Real.cos x.1)]))
  have hS : Integrable (fun x : ℝ × ℝ =>
      ((Real.sin x.1 * w x.1) * deriv (fun t => q (t, x.2)) x.1 - Real.cos x.1 * q x) ^ 2 /
        (Real.sin x.1 * w x.1))
      ((volume.restrict (Ioc 0 Real.pi)).prod (volume.restrict (Ioc a b))) := by
    apply ((hR.add hcosV).sub hcross).congr
    rw [Measure.prod_restrict]
    filter_upwards [ae_restrict_mem (measurableSet_Ioc.prod measurableSet_Ioc)] with x hx
    by_cases hxp : x.1 = Real.pi
    · simp [hxp, show q x = 0 from by simpa [← hxp] using hpi x.2]
    have hpos : 0 < Real.sin x.1 * w x.1 :=
      mul_pos (Real.sin_pos_of_pos_of_lt_pi hx.1.1 (lt_of_le_of_ne hx.1.2 hxp))
        (hwpos x.1 ⟨hx.1.1.le, hx.1.2⟩)
    change (Real.sin x.1 * w x.1) * (deriv (fun t => q (t, x.2)) x.1) ^ 2 +
      Real.cos x.1 ^ 2 * (q x ^ 2 / (Real.sin x.1 * w x.1)) -
      2 * Real.cos x.1 * q x * deriv (fun t => q (t, x.2)) x.1 = _
    have hne := mul_ne_zero_iff.mp (ne_of_gt hpos)
    field_simp [hne.1, hne.2]
    ring
  refine ⟨hR, hV, hA, hS, ?_, ?_, hP, hprimitive⟩
  · change Integrable (fun x : ℝ × ℝ => -(Real.sin x.1 * q x ^ 2) +
      2 * Real.cos x.1 * q x * deriv (fun t => q (t, x.2)) x.1) _ at hB
    simpa only [neg_mul] using hB
  · simpa only [Pi.pow_apply, Function.comp_apply, mul_div_assoc] using hG

/-- A positive scalar energy lower bound for a polar function with zero angular mean.
All integrability at the poles follows from the stated smoothness and vanishing. -/
theorem integral_polar_energy_ge_of_angular_mean_zero (q : ℝ × ℝ → ℝ) (w : ℝ → ℝ)
    (hq : ContDiff ℝ 2 q) (hzero : ∀ θ, q (0, θ) = 0)
    (hpi : ∀ θ, q (Real.pi, θ) = 0)
    (hperiod : ∀ s, q (s, 2 * Real.pi) = q (s, 0))
    (hmean : ∀ s, (∫ θ in (0 : ℝ)..2 * Real.pi, q (s, θ)) = 0)
    (hw : Continuous w) (hwpos : ∀ s ∈ Icc 0 Real.pi, 0 < w s) :
    (∫ s in (0 : ℝ)..Real.pi, ∫ θ in (0 : ℝ)..2 * Real.pi,
      Real.sin s ^ 2 * q (s, θ) ^ 2 / (Real.sin s * w s)) ≤
    ∫ s in (0 : ℝ)..Real.pi, ∫ θ in (0 : ℝ)..2 * Real.pi,
      (Real.sin s * w s) * (deriv (fun t => q (t, θ)) s) ^ 2 +
      (deriv (fun t => q (s, t)) θ) ^ 2 / (Real.sin s * w s) -
      Real.sin s * q (s, θ) ^ 2 := by
  let μ := volume.restrict (Ioc (0 : ℝ) Real.pi)
  let ν := volume.restrict (Ioc (0 : ℝ) (2 * Real.pi))
  let W := fun s => Real.sin s * w s
  let R := fun x : ℝ × ℝ => W x.1 * (deriv (fun t => q (t, x.2)) x.1) ^ 2
  let V := fun x : ℝ × ℝ => q x ^ 2 / W x.1
  let A := fun x : ℝ × ℝ => (deriv (fun t => q (x.1, t)) x.2) ^ 2 / W x.1
  let P := fun x : ℝ × ℝ => Real.sin x.1 * q x ^ 2
  let G := fun x : ℝ × ℝ => Real.sin x.1 ^ 2 * q x ^ 2 / W x.1
  obtain ⟨hR, hV, hA, _, _, hG, hP, _⟩ :=
    integrable_polar_energy_terms q w hq hzero hpi hw hwpos 0 (2 * Real.pi)
  change Integrable R (μ.prod ν) at hR
  change Integrable V (μ.prod ν) at hV
  change Integrable A (μ.prod ν) at hA
  change Integrable G (μ.prod ν) at hG
  change Integrable P (μ.prod ν) at hP
  have hE : Integrable (fun x => R x + V x - P x) (μ.prod ν) := (hR.add hV).sub hP
  have hF : Integrable (fun x => R x + A x - P x) (μ.prod ν) := (hR.add hA).sub hP
  have hWpos (s : ℝ) (hs : s ∈ Ioo 0 Real.pi) : 0 < W s :=
    mul_pos (Real.sin_pos_of_pos_of_lt_pi hs.1 hs.2) (hwpos s ⟨hs.1.le, hs.2.le⟩)
  have hradial : (∫ x, G x ∂μ.prod ν) ≤ ∫ x, R x + V x - P x ∂μ.prod ν := by
    rw [integral_prod_symm _ hG, integral_prod_symm _ hE]
    apply integral_mono_ae hG.integral_prod_right hE.integral_prod_right
    filter_upwards [hR.prod_left_ae, hV.prod_left_ae] with θ hRθ hVθ
    have hslice : ContDiff ℝ 1 (fun s => q (s, θ)) :=
      (hq.comp (contDiff_id.prodMk contDiff_const)).of_le (by norm_num)
    have h := integral_weighted_sin_sq_le_polar_energy W (fun s => q (s, θ)) hWpos hslice
      (hzero θ) (hpi θ)
      ((intervalIntegrable_iff_integrableOn_Ioc_of_le Real.pi_pos.le).mpr hRθ)
      ((intervalIntegrable_iff_integrableOn_Ioc_of_le Real.pi_pos.le).mpr hVθ)
    simpa only [intervalIntegral.integral_of_le Real.pi_pos.le, μ, R, V, P, G] using h
  have hangular : (∫ x, V x ∂μ.prod ν) ≤ ∫ x, A x ∂μ.prod ν := by
    rw [integral_prod _ hV, integral_prod _ hA]
    apply integral_mono_ae hV.integral_prod_left hA.integral_prod_left
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
    have hslice : ContDiff ℝ 1 (fun θ => q (s, θ)) :=
      (hq.comp (contDiff_const.prodMk contDiff_id)).of_le (by norm_num)
    have hcircle := integral_sq_le_deriv_sq_of_periodic_mean_zero
      (fun θ => q (s, θ)) hslice (hperiod s) (hmean s)
    have hWnonneg : 0 ≤ W s :=
      mul_nonneg (Real.sin_nonneg_of_mem_Icc ⟨hs.1.le, hs.2⟩)
        (hwpos s ⟨hs.1.le, hs.2⟩).le
    have h := div_le_div_of_nonneg_right hcircle hWnonneg
    rw [← intervalIntegral.integral_div, ← intervalIntegral.integral_div] at h
    simpa only [intervalIntegral.integral_of_le (by positivity : (0 : ℝ) ≤ 2 * Real.pi),
      ν, V, A] using h
  have hprod : (∫ x, G x ∂μ.prod ν) ≤ ∫ x, R x + A x - P x ∂μ.prod ν := by
    calc
      _ ≤ ∫ x, R x + V x - P x ∂μ.prod ν := hradial
      _ ≤ _ := by
        have hRV : Integrable (fun x => R x + V x) (μ.prod ν) := hR.add hV
        have hRA : Integrable (fun x => R x + A x) (μ.prod ν) := hR.add hA
        rw [integral_sub hRV hP, integral_add hR hV,
          integral_sub hRA hP, integral_add hR hA]
        linarith
  rw [integral_prod _ hG, integral_prod _ hF] at hprod
  simpa only [intervalIntegral.integral_of_le Real.pi_pos.le,
    intervalIntegral.integral_of_le (by positivity : (0 : ℝ) ≤ 2 * Real.pi),
    μ, ν, R, A, P, G, W] using hprod

/-- The boundary primitive in polar square completion tends to zero at both poles. -/
theorem tendsto_polar_boundary_at_endpoints (q : ℝ × ℝ → ℝ)
    (hq : Continuous q) (hzero : ∀ θ, q (0, θ) = 0)
    (hpi : ∀ θ, q (Real.pi, θ) = 0) (θ : ℝ) :
    Filter.Tendsto (fun s => Real.cos s * q (s, θ) ^ 2) (nhds 0) (nhds 0) ∧
    Filter.Tendsto (fun s => Real.cos s * q (s, θ) ^ 2) (nhds Real.pi) (nhds 0) := by
  have hc : Continuous (fun s => Real.cos s * q (s, θ) ^ 2) :=
    Real.continuous_cos.mul ((hq.comp (continuous_id.prodMk continuous_const)).pow 2)
  constructor
  · simpa only [hzero, zero_pow (by norm_num : 2 ≠ 0), mul_zero] using hc.tendsto 0
  · simpa only [hpi, zero_pow (by norm_num : 2 ≠ 0), mul_zero] using hc.tendsto Real.pi

end RicciFlowSharpEstimate.Analysis
