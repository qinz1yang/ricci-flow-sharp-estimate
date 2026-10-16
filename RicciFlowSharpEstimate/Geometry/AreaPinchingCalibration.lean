/-
Copyright (c) 2026 Ziyang Qin. All rights reserved.
No license is granted by this file.
Authors: Ziyang Qin
-/
import RicciFlowSharpEstimate.Geometry.AreaProbeEnergy

/-! # A complete-action calibration for curvature ratio at most two -/

noncomputable section
namespace RicciFlowSharpEstimate.Geometry.AreaProfile
open Set MeasureTheory
open scoped ContDiff

private def pinchingDensity (K r : ℝ → ℝ) (κ Λ x : ℝ) : ℝ :=
  let f := warp K x
  let b := warpSlope K x
  f * (meridionalOperator K r x + κ * r x) ^ 2 +
    (2 * κ - (Λ - K x) / 2) * f ^ 2 * deriv r x ^ 2 +
    (Λ - K x) / 2 * (f * deriv r x + b * r x) ^ 2 +
    (K x ^ 2 + (2 * κ - Λ) * K x - κ ^ 2) * f * r x ^ 2

private def pinchingFlux (K r : ℝ → ℝ) (κ Λ x : ℝ) : ℝ :=
  (-2 * κ) * ((warp K x ^ 2 * r x) * deriv r x) -
    (Λ / 2) * ((warp K x * warpSlope K x) * r x ^ 2)

private theorem pinching_flux_hasDerivAt (K r : ℝ → ℝ)
    (hK : Continuous K) (hr : ContDiff ℝ 2 r) (κ Λ x : ℝ) :
    HasDerivAt (pinchingFlux K r κ Λ)
      (meridionalActionDensity (warp K x) (warpSlope K x) (K x)
          (r x) (deriv r x) (deriv (deriv r) x) -
        pinchingDensity K r κ Λ x) x := by
  have hf := warp_hasDerivAt K hK x
  have hb := warpSlope_hasDerivAt K hK x
  have hrd := (hr.differentiable (by norm_num) x).hasDerivAt
  have hrD : ContDiff ℝ 1 (deriv r) := hr.deriv'
  have hrdd := (hrD.differentiable (by norm_num) x).hasDerivAt
  have h := ((((hf.pow 2).mul hrd).mul hrdd).const_mul (-2 * κ)).sub
    (((hf.mul hb).mul (hrd.pow 2)).const_mul (Λ / 2))
  convert h using 1
  · rfl
  · simp only [Pi.mul_apply, Pi.pow_apply]
    unfold meridionalActionDensity pinchingDensity meridionalOperator
    ring

private theorem pinching_density_continuous (K r : ℝ → ℝ)
    (hK : Continuous K) (hr : ContDiff ℝ 2 r) (κ Λ : ℝ) :
    Continuous (pinchingDensity K r κ Λ) := by
  have hf := warp_continuous K hK
  have hb := warpSlope_continuous K hK
  have hr0 := hr.continuous
  have hr1 := hr.continuous_deriv (by norm_num)
  have hq := meridionalOperator_continuous_of_contDiff_two K r hK hr
  unfold pinchingDensity
  fun_prop

/-- Two genuine boundary-null fluxes complete the original six-entry action
into four squares/potential terms. Continuous curvature and a C² probe suffice;
neither curvature derivatives nor probe pole conditions are required. -/
theorem meridionalAction_eq_pinching_calibration (K r : ℝ → ℝ)
    (hK : Continuous K) (hr : ContDiff ℝ 2 r)
    (hzero : (∫ x in (0 : ℝ)..1, K x) = 2)
    (hone : (∫ x in (0 : ℝ)..1, x * K x) = 1) (κ Λ : ℝ) :
    meridionalAction K r = ∫ x in (0 : ℝ)..1,
      let f := warp K x
      let b := warpSlope K x
      f * (meridionalOperator K r x + κ * r x) ^ 2 +
        (2 * κ - (Λ - K x) / 2) * f ^ 2 * deriv r x ^ 2 +
        (Λ - K x) / 2 * (f * deriv r x + b * r x) ^ 2 +
        (K x ^ 2 + (2 * κ - Λ) * K x - κ ^ 2) * f * r x ^ 2 := by
  have hf := warp_continuous K hK
  have hb := warpSlope_continuous K hK
  have hr0 := hr.continuous
  have hr1 := hr.continuous_deriv (by norm_num)
  have hr2 := hr.deriv'.continuous_deriv_one
  have hD : Continuous (fun x => meridionalActionDensity (warp K x)
      (warpSlope K x) (K x) (r x) (deriv r x) (deriv (deriv r) x)) := by
    unfold meridionalActionDensity
    fun_prop
  have hCal := pinching_density_continuous K r hK hr κ Λ
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun x _ => pinching_flux_hasDerivAt K r hK hr κ Λ x)
    ((hD.sub hCal).intervalIntegrable 0 1)
  rw [intervalIntegral.integral_sub (hD.intervalIntegrable 0 1)
    (hCal.intervalIntegrable 0 1)] at h
  have hF0 : pinchingFlux K r κ Λ 0 = 0 := by
    simp only [pinchingFlux, warp_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0),
      zero_mul, mul_zero, sub_zero]
  have hF1 : pinchingFlux K r κ Λ 1 = 0 := by
    simp only [pinchingFlux, warp_one K hK hzero hone,
      zero_pow (by norm_num : (2 : ℕ) ≠ 0), zero_mul, mul_zero, sub_zero]
  rw [hF0, hF1, sub_self] at h
  exact sub_eq_zero.mp h

/-- An original positive curvature box with upper bound at most twice its
lower bound gives a homogeneous, independent complete-action mass bound.
The probe has its actual derivatives and arbitrary smooth pole values. -/
theorem meridionalAction_ge_pinching_mass (K r : ℝ → ℝ)
    (hK : Continuous K) (hr : ContDiff ℝ 2 r)
    (hzero : (∫ x in (0 : ℝ)..1, K x) = 2)
    (hone : (∫ x in (0 : ℝ)..1, x * K x) = 1)
    (κ Λ : ℝ) (hκ : 0 < κ)
    (hbox : ∀ x ∈ Icc (0 : ℝ) 1, κ ≤ K x ∧ K x ≤ Λ)
    (hΛ : Λ ≤ 2 * κ) :
    κ * (2 * κ - Λ) * probeMass K r ≤ meridionalAction K r := by
  rw [meridionalAction_eq_pinching_calibration K r hK hr hzero hone κ Λ,
    probeMass, ← intervalIntegral.integral_const_mul]
  change (∫ x in (0 : ℝ)..1, κ * (2 * κ - Λ) * (warp K x * r x ^ 2)) ≤
    ∫ x in (0 : ℝ)..1, pinchingDensity K r κ Λ x
  have hf := warp_continuous K hK
  have hr0 := hr.continuous
  have hM : Continuous (fun x => κ * (2 * κ - Λ) * (warp K x * r x ^ 2)) := by
    fun_prop
  apply intervalIntegral.integral_mono_on zero_le_one (hM.intervalIntegrable 0 1)
    ((pinching_density_continuous K r hK hr κ Λ).intervalIntegrable 0 1)
  intro x hx
  obtain ⟨hlo, hhi⟩ := hbox x hx
  have hKn : 0 ≤ K x := hκ.le.trans hlo
  have hfn : 0 ≤ warp K x :=
    (warp_nonneg_le_two_mul_min K hK
      (fun y hy => hκ.le.trans (hbox y hy).1) hzero hone x hx).1
  have hd : 0 ≤ Λ - K x := sub_nonneg.mpr hhi
  have hdhi : Λ - K x ≤ κ := by linarith
  have hc : 0 ≤ 2 * κ - (Λ - K x) / 2 := by linarith
  have hpot : κ * (2 * κ - Λ) ≤ K x ^ 2 + (2 * κ - Λ) * K x - κ ^ 2 := by
    have hs := mul_nonneg (sub_nonneg.mpr hlo) (add_nonneg hKn hκ.le)
    have hl := mul_nonneg (by linarith : 0 ≤ 2 * κ - Λ) (sub_nonneg.mpr hlo)
    nlinarith only [hs, hl]
  have ht := mul_le_mul_of_nonneg_right hpot (mul_nonneg hfn (sq_nonneg (r x)))
  have hs1 := mul_nonneg hfn (sq_nonneg (meridionalOperator K r x + κ * r x))
  have hs2 := mul_nonneg (mul_nonneg hc (sq_nonneg (warp K x)))
    (sq_nonneg (deriv r x))
  have hs3 := mul_nonneg (div_nonneg hd (by norm_num : (0 : ℝ) ≤ 2))
    (sq_nonneg (warp K x * deriv r x + warpSlope K x * r x))
  dsimp only [pinchingDensity]
  nlinarith only [ht, hs1, hs2, hs3]

end RicciFlowSharpEstimate.Geometry.AreaProfile
