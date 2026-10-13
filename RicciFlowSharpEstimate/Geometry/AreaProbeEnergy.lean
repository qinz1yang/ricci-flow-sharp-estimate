/-
Copyright (c) 2026 Ziyang Qin. All rights reserved.
No license is granted by this file.
Authors: Ziyang Qin
-/
import RicciFlowSharpEstimate.Geometry.AreaProbeRayleigh
import RicciFlowSharpEstimate.Geometry.AreaWarpBounds
import RicciFlowSharpEstimate.Analysis.ParabolicWeightedHardy

/-!
# Weighted energy of the actual meridional probe operator

The complete second-order operator has a divergence pairing whose actual flux
vanishes at the geometric poles, without imposing boundary values on the probe.
-/

noncomputable section

namespace RicciFlowSharpEstimate.Geometry.AreaProfile

open Set MeasureTheory
open scoped ContDiff

/-- Weighted square of the actual second-order meridional operator. -/
def probeOperatorEnergy (K r : ℝ → ℝ) : ℝ :=
  ∫ x in (0 : ℝ)..1, warp K x * meridionalOperator K r x ^ 2

/-- Gradient energy with the actual degenerating warp squared. -/
def probeGradientEnergy (K r : ℝ → ℝ) : ℝ :=
  ∫ x in (0 : ℝ)..1, warp K x ^ 2 * deriv r x ^ 2

/-- Continuous curvature and a C² probe suffice for the actual operator to be continuous. -/
theorem meridionalOperator_continuous_of_contDiff_two (K r : ℝ → ℝ)
    (hK : Continuous K) (hr : ContDiff ℝ 2 r) : Continuous (meridionalOperator K r) := by
  have hf := warp_continuous K hK
  have hb := warpSlope_continuous K hK
  have hr0 := hr.continuous
  have hr1 := hr.continuous_deriv (by norm_num)
  have hr2 := hr.deriv'.continuous_deriv_one
  unfold meridionalOperator
  fun_prop

private theorem probe_flux_hasDerivAt (K r : ℝ → ℝ)
    (hK : Continuous K) (hr : ContDiff ℝ 2 r) (x : ℝ) :
    HasDerivAt (fun y => warp K y ^ 2 * deriv r y * r y)
      (warp K x * r x * meridionalOperator K r x +
        warp K x ^ 2 * deriv r x ^ 2 + warp K x * K x * r x ^ 2) x := by
  have hf := warp_hasDerivAt K hK x
  have hr0 := (hr.differentiable (by norm_num) x).hasDerivAt
  have hrD : ContDiff ℝ 1 (deriv r) := hr.deriv'
  have hr1 := (hrD.differentiable (by norm_num) x).hasDerivAt
  convert (((hf.pow 2).mul hr1).mul hr0) using 1
  simp only [Pi.mul_apply, Pi.pow_apply]
  unfold meridionalOperator
  ring

/-- Integration of the actual divergence flux gives the weighted operator pairing.
Both pole fluxes vanish because the warp vanishes, with arbitrary smooth pole values. -/
theorem integral_warp_mul_probe_operator (K r : ℝ → ℝ)
    (hK : Continuous K) (hr : ContDiff ℝ 2 r)
    (hzero : (∫ x in (0 : ℝ)..1, K x) = 2)
    (hone : (∫ x in (0 : ℝ)..1, x * K x) = 1) :
    (∫ x in (0 : ℝ)..1, warp K x * r x * meridionalOperator K r x) =
      -probeGradientEnergy K r - ∫ x in (0 : ℝ)..1, warp K x * K x * r x ^ 2 := by
  have hf := warp_continuous K hK
  have hr0 := hr.continuous
  have hr1 := hr.continuous_deriv (by norm_num)
  have hL := meridionalOperator_continuous_of_contDiff_two K r hK hr
  have hF : Continuous (fun x => warp K x * r x * meridionalOperator K r x) := by fun_prop
  have hG : Continuous (fun x => warp K x ^ 2 * deriv r x ^ 2) := by fun_prop
  have hT : Continuous (fun x => warp K x * K x * r x ^ 2) := by fun_prop
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun x _ => probe_flux_hasDerivAt K r hK hr x)
    (((hF.add hG).add hT).intervalIntegrable 0 1)
  have hFG : IntervalIntegrable (fun x => warp K x * r x * meridionalOperator K r x +
      warp K x ^ 2 * deriv r x ^ 2) volume 0 1 := (hF.add hG).intervalIntegrable 0 1
  rw [intervalIntegral.integral_add hFG (hT.intervalIntegrable 0 1),
    intervalIntegral.integral_add (hF.intervalIntegrable 0 1) (hG.intervalIntegrable 0 1)] at h
  simp only [warp_zero, warp_one K hK hzero hone, zero_pow (by norm_num : (2 : ℕ) ≠ 0),
    zero_mul, sub_self] at h
  unfold probeGradientEnergy
  linarith

/-- The actual weighted gradient energy is nonnegative. -/
theorem probeGradientEnergy_nonneg (K r : ℝ → ℝ) : 0 ≤ probeGradientEnergy K r := by
  apply intervalIntegral.integral_nonneg zero_le_one
  intro x _
  exact mul_nonneg (sq_nonneg _) (sq_nonneg _)


/-- Nonnegative normalized curvature gives nonnegative operator energy. -/
theorem probeOperatorEnergy_nonneg (K r : ℝ → ℝ) (hK : Continuous K)
    (hnonneg : ∀ x ∈ Icc (0 : ℝ) 1, 0 ≤ K x)
    (hzero : (∫ x in (0 : ℝ)..1, K x) = 2)
    (hone : (∫ x in (0 : ℝ)..1, x * K x) = 1) : 0 ≤ probeOperatorEnergy K r := by
  apply intervalIntegral.integral_nonneg zero_le_one
  intro x hx
  exact mul_nonneg (warp_nonneg_le_two_mul_min K hK hnonneg hzero hone x hx).1 (sq_nonneg _)

/-- Weighted interpolation from the actual operator flux, uniformly in the
curvature derivatives and with no boundary conditions on the probe. -/
theorem probeGradientEnergy_interpolation (K r : ℝ → ℝ)
    (hK : Continuous K) (hr : ContDiff ℝ 2 r)
    (hnonneg : ∀ x ∈ Icc (0 : ℝ) 1, 0 ≤ K x)
    (hzero : (∫ x in (0 : ℝ)..1, K x) = 2)
    (hone : (∫ x in (0 : ℝ)..1, x * K x) = 1)
    (t : ℝ) (ht : 0 ≤ t) :
    4 * t * probeGradientEnergy K r ≤ 4 * t ^ 2 * probeOperatorEnergy K r + probeMass K r := by
  have hf := warp_continuous K hK
  have hr0 := hr.continuous
  have hL := meridionalOperator_continuous_of_contDiff_two K r hK hr
  have hF : Continuous (fun x => warp K x * r x * meridionalOperator K r x) := by fun_prop
  have hE : Continuous (fun x => warp K x * meridionalOperator K r x ^ 2) := by fun_prop
  have hM : Continuous (fun x => warp K x * r x ^ 2) := by fun_prop
  have hFnonneg (x : ℝ) (hx : x ∈ Icc (0 : ℝ) 1) : 0 ≤ warp K x :=
    (warp_nonneg_le_two_mul_min K hK hnonneg hzero hone x hx).1
  have hsq : 0 ≤ ∫ x in (0 : ℝ)..1,
      4 * t * (warp K x * r x * meridionalOperator K r x) +
        4 * t ^ 2 * (warp K x * meridionalOperator K r x ^ 2) + warp K x * r x ^ 2 := by
    apply intervalIntegral.integral_nonneg zero_le_one
    intro x hx
    have h := mul_nonneg (hFnonneg x hx) (sq_nonneg (r x + 2 * t * meridionalOperator K r x))
    nlinarith only [h]
  have hFE : IntervalIntegrable (fun x =>
      4 * t * (warp K x * r x * meridionalOperator K r x) +
        4 * t ^ 2 * (warp K x * meridionalOperator K r x ^ 2)) volume 0 1 :=
    ((hF.const_mul (4 * t)).add (hE.const_mul (4 * t ^ 2))).intervalIntegrable 0 1
  rw [intervalIntegral.integral_add hFE (hM.intervalIntegrable 0 1),
    intervalIntegral.integral_add ((hF.const_mul (4 * t)).intervalIntegrable 0 1)
      ((hE.const_mul (4 * t ^ 2)).intervalIntegrable 0 1),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    integral_warp_mul_probe_operator K r hK hr hzero hone] at hsq
  have hpot : 0 ≤ ∫ x in (0 : ℝ)..1, warp K x * K x * r x ^ 2 := by
    apply intervalIntegral.integral_nonneg zero_le_one
    intro x hx
    exact mul_nonneg (mul_nonneg (hFnonneg x hx) (hnonneg x hx)) (sq_nonneg _)
  change 0 ≤ 4 * t * (-probeGradientEnergy K r -
    (∫ x in (0 : ℝ)..1, warp K x * K x * r x ^ 2)) +
      4 * t ^ 2 * probeOperatorEnergy K r + probeMass K r at hsq
  nlinarith [mul_nonneg ht hpot]

/-- A nonnegative lower curvature bound transfers the parabolic Hardy estimate to
the actual physical mass and gradient, without curvature derivative bounds. -/
theorem integral_sq_le_probeMass_gradient (K r : ℝ → ℝ)
    (hK : Continuous K) (hr : ContDiff ℝ 1 r) (lo : ℝ) (hlo : 0 ≤ lo)
    (hlower : ∀ x ∈ Icc (0 : ℝ) 1, lo ≤ K x)
    (hzero : (∫ x in (0 : ℝ)..1, K x) = 2)
    (hone : (∫ x in (0 : ℝ)..1, x * K x) = 1) :
    lo ^ 2 * (∫ x in (0 : ℝ)..1, r x ^ 2) ≤
      12 * lo * probeMass K r + 4 * probeGradientEnergy K r := by
  have hf := warp_continuous K hK
  have hr0 := hr.continuous
  have hr1 := hr.continuous_deriv_one
  have hw : Continuous (fun x : ℝ => x * (1 - x)) := by fun_prop
  have hM : lo * (∫ x in (0 : ℝ)..1, x * (1 - x) * r x ^ 2) ≤ probeMass K r := by
    rw [← intervalIntegral.integral_const_mul]
    unfold probeMass
    apply intervalIntegral.integral_mono_on zero_le_one
      ((continuous_const.mul (hw.mul (hr0.pow 2))).intervalIntegrable 0 1)
      ((hf.mul (hr0.pow 2)).intervalIntegrable 0 1)
    intro x hx
    change lo * (x * (1 - x) * r x ^ 2) ≤ warp K x * r x ^ 2
    have h := mul_le_mul_of_nonneg_right
      (quadratic_le_warp_of_curvature_lower K hK lo hlower hzero hone x hx) (sq_nonneg (r x))
    nlinarith only [h]
  have hG : lo ^ 2 * (∫ x in (0 : ℝ)..1, (x * (1 - x)) ^ 2 * deriv r x ^ 2) ≤
      probeGradientEnergy K r := by
    rw [← intervalIntegral.integral_const_mul]
    unfold probeGradientEnergy
    apply intervalIntegral.integral_mono_on zero_le_one
      ((continuous_const.mul ((hw.pow 2).mul (hr1.pow 2))).intervalIntegrable 0 1)
      (((hf.pow 2).mul (hr1.pow 2)).intervalIntegrable 0 1)
    intro x hx
    change lo ^ 2 * ((x * (1 - x)) ^ 2 * deriv r x ^ 2) ≤
      warp K x ^ 2 * deriv r x ^ 2
    have hbound := quadratic_le_warp_of_curvature_lower K hK lo hlower hzero hone x hx
    have hw0 : 0 ≤ lo * x * (1 - x) :=
      mul_nonneg (mul_nonneg hlo hx.1) (sub_nonneg.mpr hx.2)
    have hf0 : 0 ≤ warp K x := hw0.trans hbound
    have hsquare : (lo * x * (1 - x)) ^ 2 ≤ warp K x ^ 2 := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hbound) (add_nonneg hf0 hw0)]
    have h := mul_le_mul_of_nonneg_right hsquare (sq_nonneg (deriv r x))
    nlinarith only [h]
  have hHardy := Analysis.integral_sq_le_parabolic_weighted_energy r hr
  have hScaled := mul_le_mul_of_nonneg_left hHardy (sq_nonneg lo)
  have hMScaled := mul_le_mul_of_nonneg_left hM (mul_nonneg (by norm_num : (0 : ℝ) ≤ 12) hlo)
  nlinarith only [hScaled, hMScaled, hG]


end RicciFlowSharpEstimate.Geometry.AreaProfile
