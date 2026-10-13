/-
Copyright (c) 2026 Ziyang Qin. All rights reserved.
No license is granted by this file.
Authors: Ziyang Qin
-/
import RicciFlowSharpEstimate.Geometry.AreaProbeEnergy
import RicciFlowSharpEstimate.Analysis.ParabolicDerivativeEnergy

/-!
# Second derivative control by the actual meridional operator

The derivative of the actual flux `2 f² b (r′)²` gives an exact square identity.
Its pole values vanish by the two normalized curvature moments. A nonnegative
curvature box then controls the weighted second derivative without imposing
probe boundary conditions or differentiating the curvature.
-/

noncomputable section

namespace RicciFlowSharpEstimate.Geometry.AreaProfile

open Set MeasureTheory
open scoped ContDiff

private theorem probe_second_flux_hasDerivAt (K r : ℝ → ℝ)
    (hK : Continuous K) (hr : ContDiff ℝ 2 r) (x : ℝ) :
    HasDerivAt (fun y => 2 * warp K y ^ 2 * warpSlope K y * deriv r y ^ 2)
      (warp K x * (meridionalOperator K r x + K x * r x) ^ 2 -
        warp K x ^ 3 * deriv (deriv r) x ^ 2 -
        4 * (warp K x ^ 2 * K x * deriv r x ^ 2)) x := by
  have hf := warp_hasDerivAt K hK x
  have hb := warpSlope_hasDerivAt K hK x
  have hrD : ContDiff ℝ 1 (deriv r) := hr.deriv'
  have hr1 := (hrD.differentiable (by norm_num) x).hasDerivAt
  convert ((((hf.pow 2).const_mul 2).mul hb).mul (hr1.pow 2)) using 1
  simp only [Pi.mul_apply, Pi.pow_apply]
  unfold meridionalOperator
  ring

/-- The complete operator with its curvature term restored satisfies an exact
weighted square identity for every C² probe, with no probe pole conditions. -/
theorem integral_warp_operator_add_curvature_sq (K r : ℝ → ℝ)
    (hK : Continuous K) (hr : ContDiff ℝ 2 r)
    (hzero : (∫ x in (0 : ℝ)..1, K x) = 2)
    (hone : (∫ x in (0 : ℝ)..1, x * K x) = 1) :
    (∫ x in (0 : ℝ)..1, warp K x * (meridionalOperator K r x + K x * r x) ^ 2) =
      (∫ x in (0 : ℝ)..1, warp K x ^ 3 * deriv (deriv r) x ^ 2) +
        4 * ∫ x in (0 : ℝ)..1, warp K x ^ 2 * K x * deriv r x ^ 2 := by
  have hf := warp_continuous K hK
  have hr0 := hr.continuous
  have hr1 := hr.continuous_deriv (by norm_num)
  have hr2 := hr.deriv'.continuous_deriv_one
  have hL := meridionalOperator_continuous_of_contDiff_two K r hK hr
  have hA : Continuous (fun x =>
      warp K x * (meridionalOperator K r x + K x * r x) ^ 2) := by fun_prop
  have hB : Continuous (fun x => warp K x ^ 3 * deriv (deriv r) x ^ 2) := by fun_prop
  have hC : Continuous (fun x => warp K x ^ 2 * K x * deriv r x ^ 2) := by fun_prop
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun x _ => probe_second_flux_hasDerivAt K r hK hr x)
    (((hA.sub hB).sub (hC.const_mul 4)).intervalIntegrable 0 1)
  have hAB : IntervalIntegrable (fun x =>
      warp K x * (meridionalOperator K r x + K x * r x) ^ 2 -
        warp K x ^ 3 * deriv (deriv r) x ^ 2) volume 0 1 :=
    (hA.sub hB).intervalIntegrable 0 1
  rw [intervalIntegral.integral_sub hAB
      ((hC.const_mul 4).intervalIntegrable 0 1),
    intervalIntegral.integral_sub (hA.intervalIntegrable 0 1) (hB.intervalIntegrable 0 1),
    intervalIntegral.integral_const_mul] at h
  simp only [warp_zero, warp_one K hK hzero hone,
    zero_pow (by norm_num : (2 : ℕ) ≠ 0), mul_zero, zero_mul, sub_self] at h
  linarith

/-- A nonnegative curvature box controls the actual weighted second derivative
by the operator energy and probe mass, uniformly in curvature derivatives. -/
theorem integral_warp_cube_second_deriv_sq_le (K r : ℝ → ℝ)
    (hK : Continuous K) (hr : ContDiff ℝ 2 r) (hi : ℝ)
    (hbox : ∀ x ∈ Icc (0 : ℝ) 1, 0 ≤ K x ∧ K x ≤ hi)
    (hzero : (∫ x in (0 : ℝ)..1, K x) = 2)
    (hone : (∫ x in (0 : ℝ)..1, x * K x) = 1) :
    (∫ x in (0 : ℝ)..1, warp K x ^ 3 * deriv (deriv r) x ^ 2) ≤
      2 * probeOperatorEnergy K r + 2 * hi ^ 2 * probeMass K r := by
  have hhi : 0 ≤ hi :=
    (hbox 0 (by norm_num)).1.trans (hbox 0 (by norm_num)).2
  have hnonneg : ∀ x ∈ Icc (0 : ℝ) 1, 0 ≤ K x := fun x hx => (hbox x hx).1
  have hf := warp_continuous K hK
  have hr0 := hr.continuous
  have hL := meridionalOperator_continuous_of_contDiff_two K r hK hr
  have hA : Continuous (fun x =>
      warp K x * (meridionalOperator K r x + K x * r x) ^ 2) := by fun_prop
  have hE : Continuous (fun x => warp K x * meridionalOperator K r x ^ 2) := by fun_prop
  have hM : Continuous (fun x => warp K x * r x ^ 2) := by fun_prop
  have hbound : (∫ x in (0 : ℝ)..1,
      warp K x * (meridionalOperator K r x + K x * r x) ^ 2) ≤
      ∫ x in (0 : ℝ)..1, 2 * (warp K x * meridionalOperator K r x ^ 2) +
        2 * hi ^ 2 * (warp K x * r x ^ 2) := by
    apply intervalIntegral.integral_mono_on zero_le_one (hA.intervalIntegrable 0 1)
      (((hE.const_mul 2).add (hM.const_mul (2 * hi ^ 2))).intervalIntegrable 0 1)
    intro x hx
    have hf0 := (warp_nonneg_le_two_mul_min K hK hnonneg hzero hone x hx).1
    have hKsq : K x ^ 2 ≤ hi ^ 2 := by
      nlinarith only [mul_nonneg (sub_nonneg.mpr (hbox x hx).2)
        (add_nonneg hhi (hbox x hx).1)]
    have hpot := mul_le_mul_of_nonneg_right hKsq (sq_nonneg (r x))
    have hsq : (meridionalOperator K r x + K x * r x) ^ 2 ≤
        2 * meridionalOperator K r x ^ 2 + 2 * hi ^ 2 * r x ^ 2 := by
      nlinarith only [sq_nonneg (meridionalOperator K r x - K x * r x), hpot]
    calc
      warp K x * (meridionalOperator K r x + K x * r x) ^ 2 ≤
          warp K x * (2 * meridionalOperator K r x ^ 2 + 2 * hi ^ 2 * r x ^ 2) :=
        mul_le_mul_of_nonneg_left hsq hf0
      _ = 2 * (warp K x * meridionalOperator K r x ^ 2) +
          2 * hi ^ 2 * (warp K x * r x ^ 2) := by ring
  rw [intervalIntegral.integral_add ((hE.const_mul 2).intervalIntegrable 0 1)
      ((hM.const_mul (2 * hi ^ 2)).intervalIntegrable 0 1),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul] at hbound
  change (∫ x in (0 : ℝ)..1,
      warp K x * (meridionalOperator K r x + K x * r x) ^ 2) ≤
    2 * probeOperatorEnergy K r + 2 * hi ^ 2 * probeMass K r at hbound
  have hcurv : 0 ≤ ∫ x in (0 : ℝ)..1, warp K x ^ 2 * K x * deriv r x ^ 2 := by
    apply intervalIntegral.integral_nonneg zero_le_one
    intro x hx
    exact mul_nonneg (mul_nonneg (sq_nonneg _) (hbox x hx).1) (sq_nonneg _)
  have hidentity := integral_warp_operator_add_curvature_sq K r hK hr hzero hone
  linarith


/-- The first power of the parabolic weight controls the actual probe derivative
uniformly from its operator energy and mass on a positive curvature box. -/
theorem integral_parabolic_deriv_sq_le (K r : ℝ → ℝ)
    (hK : Continuous K) (hr : ContDiff ℝ 2 r) (lo hi : ℝ) (hlo : 0 < lo)
    (hbox : ∀ x ∈ Icc (0 : ℝ) 1, lo ≤ K x ∧ K x ≤ hi)
    (hzero : (∫ x in (0 : ℝ)..1, K x) = 2)
    (hone : (∫ x in (0 : ℝ)..1, x * K x) = 1) :
    lo ^ 3 * (∫ x in (0 : ℝ)..1, x * (1 - x) * deriv r x ^ 2) ≤
      (10 * lo + 2) * probeOperatorEnergy K r +
        (5 * lo / 2 + 2 * hi ^ 2) * probeMass K r := by
  have hf := warp_continuous K hK
  have hrD : ContDiff ℝ 1 (deriv r) := hr.deriv'
  have hr1 := hrD.continuous
  have hr2 := hrD.continuous_deriv_one
  have hw : Continuous (fun x : ℝ => x * (1 - x)) := by fun_prop
  have hlower (x : ℝ) (hx : x ∈ Icc (0 : ℝ) 1) :
      lo * (x * (1 - x)) ≤ warp K x := by
    simpa only [mul_assoc] using
      quadratic_le_warp_of_curvature_lower K hK lo (fun y hy => (hbox y hy).1) hzero hone x hx
  have hw0 (x : ℝ) (hx : x ∈ Icc (0 : ℝ) 1) : 0 ≤ lo * (x * (1 - x)) :=
    mul_nonneg hlo.le (mul_nonneg hx.1 (sub_nonneg.mpr hx.2))
  have hG : lo ^ 2 * (∫ x in (0 : ℝ)..1, (x * (1 - x)) ^ 2 * deriv r x ^ 2) ≤
      probeGradientEnergy K r := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_mono_on zero_le_one
      ((continuous_const.mul ((hw.pow 2).mul (hr1.pow 2))).intervalIntegrable 0 1)
      (((hf.pow 2).mul (hr1.pow 2)).intervalIntegrable 0 1)
    intro x hx
    have hs := pow_le_pow_left₀ (hw0 x hx) (hlower x hx) 2
    have hm := mul_le_mul_of_nonneg_right hs (sq_nonneg (deriv r x))
    simpa only [Pi.mul_apply, Pi.pow_apply, mul_pow, mul_assoc] using hm
  have hJ : lo ^ 3 * (∫ x in (0 : ℝ)..1, (x * (1 - x)) ^ 3 * deriv (deriv r) x ^ 2) ≤
      ∫ x in (0 : ℝ)..1, warp K x ^ 3 * deriv (deriv r) x ^ 2 := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_mono_on zero_le_one
      ((continuous_const.mul ((hw.pow 3).mul (hr2.pow 2))).intervalIntegrable 0 1)
      (((hf.pow 3).mul (hr2.pow 2)).intervalIntegrable 0 1)
    intro x hx
    have hs := pow_le_pow_left₀ (hw0 x hx) (hlower x hx) 3
    have hm := mul_le_mul_of_nonneg_right hs (sq_nonneg (deriv (deriv r) x))
    simpa only [Pi.mul_apply, Pi.pow_apply, mul_pow, mul_assoc] using hm
  have hH := mul_le_mul_of_nonneg_left
    (Analysis.integral_parabolic_mul_sq_le (deriv r) hrD) (pow_nonneg hlo.le 3)
  have hGscaled := mul_le_mul_of_nonneg_left hG (by positivity : 0 ≤ 10 * lo)
  have hsecond := integral_warp_cube_second_deriv_sq_le K r hK hr hi
    (fun x hx => ⟨hlo.le.trans (hbox x hx).1, (hbox x hx).2⟩) hzero hone
  have hgrad := probeGradientEnergy_interpolation K r hK hr
    (fun x hx => hlo.le.trans (hbox x hx).1) hzero hone 1 zero_le_one
  have hgradscaled := mul_le_mul_of_nonneg_left hgrad (by positivity : 0 ≤ 5 * lo / 2)
  nlinarith only [hH, hGscaled, hJ, hsecond, hgradscaled]

end RicciFlowSharpEstimate.Geometry.AreaProfile
