/-
Copyright (c) 2026 Ziyang Qin. All rights reserved.
No license is granted by this file.
Authors: Ziyang Qin
-/
import RicciFlowSharpEstimate.Analysis.ParabolicWeightedPointwise
import RicciFlowSharpEstimate.Geometry.AreaProbeEnergy
import RicciFlowSharpEstimate.Geometry.AreaRelativeWarpContinuity

/-!
# Stability of the meridional operator under curvature variation

Equal curvature moments control the warp error relative to both poles. The
weighted pointwise probe estimate then bounds the remaining curvature error
in the same weighted source space, without curvature derivative estimates.
-/

noncomputable section

namespace RicciFlowSharpEstimate.Geometry.AreaProfile

open Set MeasureTheory
open scoped ContDiff

private theorem integral_abs_sq_le_integral_sq (v : ℝ → ℝ) (hv : Continuous v) :
    (∫ x in (0 : ℝ)..1, |v x|) ^ 2 ≤ ∫ x in (0 : ℝ)..1, v x ^ 2 := by
  let A := ∫ x in (0 : ℝ)..1, |v x|
  have hsq : 0 ≤ ∫ x in (0 : ℝ)..1,
      (v x ^ 2 - 2 * A * |v x|) + A ^ 2 := by
    apply intervalIntegral.integral_nonneg zero_le_one
    intro x _
    nlinarith only [sq_nonneg (|v x| - A), sq_abs (v x)]
  have hVi : IntervalIntegrable (fun x => v x ^ 2) volume (0 : ℝ) 1 :=
    (hv.pow 2).intervalIntegrable 0 1
  have hAi : IntervalIntegrable (fun x => 2 * A * |v x|) volume (0 : ℝ) 1 :=
    (hv.abs.const_mul (2 * A)).intervalIntegrable 0 1
  rw [intervalIntegral.integral_add (hVi.sub hAi) intervalIntegrable_const,
    intervalIntegral.integral_sub hVi hAi, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const] at hsq
  simp only [sub_zero, one_smul] at hsq
  change 0 ≤ (∫ x in (0 : ℝ)..1, v x ^ 2) - 2 * A * A + A ^ 2 at hsq
  change A ^ 2 ≤ _
  nlinarith only [hsq]

/-- Varying the curvature while preserving both moments changes the actual
operator by at most the curvature L² error times the probe graph energy.
No curvature sign, prescribed moment value, or probe normalization is needed. -/
theorem meridionalOperator_sub_curvature_energy_le (K L u : ℝ → ℝ)
    (hK : Continuous K) (hL : Continuous L) (hu : ContDiff ℝ 2 u)
    (hzero : (∫ x in (0 : ℝ)..1, K x) = ∫ x in (0 : ℝ)..1, L x)
    (hone : (∫ x in (0 : ℝ)..1, x * K x) = ∫ x in (0 : ℝ)..1, x * L x) :
    (∫ x in (0 : ℝ)..1, x * (1 - x) *
      (meridionalOperator K u x - meridionalOperator L u x) ^ 2) ≤
      60 * ((∫ x in (0 : ℝ)..1, u x ^ 2) +
        (∫ x in (0 : ℝ)..1, x * (1 - x) * deriv u x ^ 2) +
        (∫ x in (0 : ℝ)..1, (x * (1 - x)) ^ 3 * deriv (deriv u) x ^ 2)) *
          (∫ x in (0 : ℝ)..1, (K x - L x) ^ 2) := by
  let w : ℝ → ℝ := fun x => x * (1 - x)
  let A := ∫ x in (0 : ℝ)..1, |K x - L x|
  let D := ∫ x in (0 : ℝ)..1, (K x - L x) ^ 2
  let U := ∫ x in (0 : ℝ)..1, u x ^ 2
  let P := ∫ x in (0 : ℝ)..1, w x * deriv u x ^ 2
  let Z := ∫ x in (0 : ℝ)..1, w x ^ 3 * deriv (deriv u) x ^ 2
  have hw : Continuous w := by dsimp [w]; fun_prop
  have hu1 := hu.continuous_deriv (by norm_num)
  have hu2 := hu.deriv'.continuous_deriv_one
  have hQK := meridionalOperator_continuous_of_contDiff_two K u hK hu
  have hQL := meridionalOperator_continuous_of_contDiff_two L u hL hu
  have hKint : IntegrableOn K (Ioo (0 : ℝ) 1) :=
    (hK.continuousOn.integrableOn_compact isCompact_Icc).mono_set Ioo_subset_Icc_self
  have hLint : IntegrableOn L (Ioo (0 : ℝ) 1) :=
    (hL.continuousOn.integrableOn_compact isCompact_Icc).mono_set Ioo_subset_Icc_self
  have hCS : A ^ 2 ≤ D := integral_abs_sq_le_integral_sq (fun x => K x - L x) (hK.sub hL)
  have hpoint (x : ℝ) (hx : x ∈ Icc (0 : ℝ) 1) :
      w x * (meridionalOperator K u x - meridionalOperator L u x) ^ 2 ≤
        48 * A ^ 2 * (w x ^ 3 * deriv (deriv u) x ^ 2) +
        48 * A ^ 2 * (w x * deriv u x ^ 2) +
        12 * (U + P) * (K x - L x) ^ 2 := by
    have hw0 : 0 ≤ w x := mul_nonneg hx.1 (sub_nonneg.mpr hx.2)
    have hf : |warp K x - warp L x| ≤ 4 * w x * A := by
      simpa only [w, A, mul_assoc] using
        abs_warp_sub_le_relative_integral_abs K L hKint hLint hzero hone x hx
    have hb : |warpSlope K x - warpSlope L x| ≤ 2 * A :=
      abs_warpSlope_sub_le_integral_abs_of_integrableOn K L hKint hLint x hx
    have hfsq := pow_le_pow_left₀ (abs_nonneg (warp K x - warp L x)) hf 2
    have hbsq := pow_le_pow_left₀ (abs_nonneg (warpSlope K x - warpSlope L x)) hb 2
    rw [sq_abs] at hfsq hbsq
    have hF : w x * ((warp K x - warp L x) * deriv (deriv u) x) ^ 2 ≤
        16 * A ^ 2 * (w x ^ 3 * deriv (deriv u) x ^ 2) := by
      have hscaled := mul_le_mul_of_nonneg_left hfsq
        (mul_nonneg hw0 (sq_nonneg (deriv (deriv u) x)))
      nlinarith only [hscaled]
    have hB : w x * (2 * (warpSlope K x - warpSlope L x) * deriv u x) ^ 2 ≤
        16 * A ^ 2 * (w x * deriv u x ^ 2) := by
      have hscaled := mul_le_mul_of_nonneg_left hbsq
        (mul_nonneg hw0 (sq_nonneg (deriv u x)))
      nlinarith only [hscaled]
    have hvalue : w x * u x ^ 2 ≤ 4 * (U + P) :=
      Analysis.parabolic_weight_mul_sq_le_energy u (hu.of_le (by norm_num)) x hx
    have hC : w x * ((K x - L x) * u x) ^ 2 ≤
        4 * (U + P) * (K x - L x) ^ 2 := by
      nlinarith only [mul_le_mul_of_nonneg_right hvalue (sq_nonneg (K x - L x))]
    let a := (warp K x - warp L x) * deriv (deriv u) x
    let b := 2 * (warpSlope K x - warpSlope L x) * deriv u x
    let c := (K x - L x) * u x
    have hthree : (a + b - c) ^ 2 ≤ 3 * (a ^ 2 + b ^ 2 + c ^ 2) := by
      nlinarith only [sq_nonneg (a - b), sq_nonneg (a + c), sq_nonneg (b + c)]
    have hscaled := mul_le_mul_of_nonneg_left hthree hw0
    have heq : meridionalOperator K u x - meridionalOperator L u x = a + b - c := by
      dsimp [a, b, c, meridionalOperator]
      ring
    rw [heq]
    change w x * a ^ 2 ≤ _ at hF
    change w x * b ^ 2 ≤ _ at hB
    change w x * c ^ 2 ≤ _ at hC
    nlinarith only [hscaled, hF, hB, hC]
  have hZc : Continuous (fun x => w x ^ 3 * deriv (deriv u) x ^ 2) := by fun_prop
  have hPc : Continuous (fun x => w x * deriv u x ^ 2) := by fun_prop
  have hDc : Continuous (fun x => (K x - L x) ^ 2) := (hK.sub hL).pow 2
  have hQc : Continuous (fun x =>
      w x * (meridionalOperator K u x - meridionalOperator L u x) ^ 2) := by fun_prop
  have hbound : (∫ x in (0 : ℝ)..1,
      w x * (meridionalOperator K u x - meridionalOperator L u x) ^ 2) ≤
      ∫ x in (0 : ℝ)..1,
        48 * A ^ 2 * (w x ^ 3 * deriv (deriv u) x ^ 2) +
        48 * A ^ 2 * (w x * deriv u x ^ 2) +
        12 * (U + P) * (K x - L x) ^ 2 := by
    apply intervalIntegral.integral_mono_on zero_le_one (hQc.intervalIntegrable 0 1)
      ((((hZc.const_mul (48 * A ^ 2)).add (hPc.const_mul (48 * A ^ 2))).add
        (hDc.const_mul (12 * (U + P)))).intervalIntegrable 0 1)
    exact hpoint
  have hSum : IntervalIntegrable (fun x =>
      48 * A ^ 2 * (w x ^ 3 * deriv (deriv u) x ^ 2) +
        48 * A ^ 2 * (w x * deriv u x ^ 2)) volume (0 : ℝ) 1 :=
    ((hZc.const_mul (48 * A ^ 2)).add (hPc.const_mul (48 * A ^ 2))).intervalIntegrable 0 1
  rw [intervalIntegral.integral_add hSum
      ((hDc.const_mul (12 * (U + P))).intervalIntegrable 0 1),
    intervalIntegral.integral_add ((hZc.const_mul (48 * A ^ 2)).intervalIntegrable 0 1)
      ((hPc.const_mul (48 * A ^ 2)).intervalIntegrable 0 1),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul] at hbound
  change (∫ x in (0 : ℝ)..1,
      w x * (meridionalOperator K u x - meridionalOperator L u x) ^ 2) ≤
        48 * A ^ 2 * Z + 48 * A ^ 2 * P + 12 * (U + P) * D at hbound
  have hU0 : 0 ≤ U := intervalIntegral.integral_nonneg zero_le_one (fun x _ => sq_nonneg (u x))
  have hD0 : 0 ≤ D :=
    intervalIntegral.integral_nonneg zero_le_one (fun x _ => sq_nonneg (K x - L x))
  have hP0 : 0 ≤ P := by
    apply intervalIntegral.integral_nonneg zero_le_one
    intro x hx
    exact mul_nonneg (mul_nonneg hx.1 (sub_nonneg.mpr hx.2)) (sq_nonneg _)
  have hZ0 : 0 ≤ Z := by
    apply intervalIntegral.integral_nonneg zero_le_one
    intro x hx
    exact mul_nonneg (pow_nonneg (mul_nonneg hx.1 (sub_nonneg.mpr hx.2)) 3) (sq_nonneg _)
  have hPscaled := mul_le_mul_of_nonneg_right hCS hP0
  have hZscaled := mul_le_mul_of_nonneg_right hCS hZ0
  change (∫ x in (0 : ℝ)..1,
      w x * (meridionalOperator K u x - meridionalOperator L u x) ^ 2) ≤ 60 * (U + P + Z) * D
  nlinarith only [hbound, hPscaled, hZscaled, mul_nonneg hU0 hD0, mul_nonneg hZ0 hD0]

end RicciFlowSharpEstimate.Geometry.AreaProfile
