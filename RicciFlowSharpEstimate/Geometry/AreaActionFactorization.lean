/-
Copyright (c) 2026 Ziyang Qin. All rights reserved.
No license is granted by this file.
Authors: Ziyang Qin
-/
import RicciFlowSharpEstimate.Geometry.AreaAction

/-!
# Square and potential factorization of the complete area action

The complete action is the sum of the weighted square of its second-order
meridional operator and a curvature-derivative potential. The difference of
the two densities is an exact derivative. The normalized curvature moments
make its flux vanish at both poles, without boundary conditions on the probe.
-/

noncomputable section

namespace RicciFlowSharpEstimate.Geometry.AreaProfile

open MeasureTheory
open scoped ContDiff

/-- The meridional operator formed from the actual warp and probe derivatives. -/
def meridionalOperator (K r : ℝ → ℝ) (x : ℝ) : ℝ :=
  warp K x * deriv (deriv r) x + 2 * warpSlope K x * deriv r x - K x * r x

/-- Smooth curvature and a smooth probe give a smooth meridional operator. -/
theorem meridionalOperator_contDiff (K r : ℝ → ℝ)
    (hK : ContDiff ℝ ∞ K) (hr : ContDiff ℝ ∞ r) :
    ContDiff ℝ ∞ (meridionalOperator K r) := by
  have hr1 : ContDiff ℝ ∞ (deriv r) := (contDiff_infty_iff_deriv.mp hr).2
  have hr2 : ContDiff ℝ ∞ (deriv (deriv r)) := (contDiff_infty_iff_deriv.mp hr1).2
  have hf := warp_contDiff K hK
  have hf1 := warpSlope_contDiff K hK
  unfold meridionalOperator
  fun_prop

private theorem factorization_flux_hasDerivAt (K r : ℝ → ℝ)
    (hK : ContDiff ℝ ∞ K) (hr : ContDiff ℝ ∞ r) (x : ℝ) :
    HasDerivAt (fun y => -(K y * warp K y * warpSlope K y * r y ^ 2) / 2)
      (meridionalActionDensity (warp K x) (warpSlope K x) (K x)
        (r x) (deriv r x) (deriv (deriv r) x) -
        (warp K x * meridionalOperator K r x ^ 2 +
          (warp K x * warpSlope K x * deriv K x / 2) * r x ^ 2)) x := by
  have hdK := (hK.differentiable (by simp) x).hasDerivAt
  have hdr := (hr.differentiable (by simp) x).hasDerivAt
  have hf := warp_hasDerivAt K hK.continuous x
  have hf1 := warpSlope_hasDerivAt K hK.continuous x
  have hFlux := ((((hdK.mul hf).mul hf1).mul (hdr.pow 2)).neg).div_const 2
  convert hFlux using 1
  simp only [Pi.mul_apply, Pi.pow_apply]
  unfold meridionalActionDensity meridionalOperator
  ring

/-- Under the normalized curvature moments, the complete area action is the
weighted square of the actual meridional operator plus its curvature potential. -/
theorem meridionalAction_eq_square_potential (K r : ℝ → ℝ)
    (hK : ContDiff ℝ ∞ K) (hr : ContDiff ℝ ∞ r)
    (hzero : (∫ x in (0 : ℝ)..1, K x) = 2)
    (hone : (∫ x in (0 : ℝ)..1, x * K x) = 1) :
    meridionalAction K r =
      ∫ x in (0 : ℝ)..1, warp K x * meridionalOperator K r x ^ 2 +
        (warp K x * warpSlope K x * deriv K x / 2) * r x ^ 2 := by
  have hf := warp_continuous K hK.continuous
  have hf1 := warpSlope_continuous K hK.continuous
  have hK1 := hK.continuous_deriv (by simp)
  have hL := (meridionalOperator_contDiff K r hK hr).continuous
  have hDensity := meridionalAction_integrand_continuous K r hK.continuous hr
  have hFactor : Continuous (fun x => warp K x * meridionalOperator K r x ^ 2 +
      (warp K x * warpSlope K x * deriv K x / 2) * r x ^ 2) := by
    fun_prop
  have hIntegral := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun x _ => factorization_flux_hasDerivAt K r hK hr x)
    ((hDensity.sub hFactor).intervalIntegrable 0 1)
  rw [intervalIntegral.integral_sub (hDensity.intervalIntegrable 0 1)
    (hFactor.intervalIntegrable 0 1)] at hIntegral
  have hFlux0 : -(K 0 * warp K 0 * warpSlope K 0 * r 0 ^ 2) / 2 = 0 := by
    simp only [warp_zero, mul_zero, zero_mul, neg_zero, zero_div]
  have hFlux1 : -(K 1 * warp K 1 * warpSlope K 1 * r 1 ^ 2) / 2 = 0 := by
    simp only [warp_one K hK.continuous hzero hone, mul_zero, zero_mul,
      neg_zero, zero_div]
  rw [hFlux0, hFlux1, sub_self] at hIntegral
  exact sub_eq_zero.mp hIntegral

end RicciFlowSharpEstimate.Geometry.AreaProfile
