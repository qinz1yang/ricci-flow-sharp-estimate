/-
Copyright (c) 2026 Ziyang Qin. All rights reserved.
No license is granted by this file.
Authors: Ziyang Qin
-/
import RicciFlowSharpEstimate.Analysis.IntervalDerivativeEnergy

/-!
# Weighted pointwise control from the parabolic first derivative energy

The square-root parabolic weight turns the ordinary probe and weighted first
derivative energies into a uniform pointwise bound. No boundary value or mass
normalization is needed.
-/

noncomputable section

namespace RicciFlowSharpEstimate.Analysis

open Set MeasureTheory
open scoped ContDiff

/-- The first parabolic graph energies bound the square of the weighted probe
at every point of the physical interval, including both endpoints. -/
theorem parabolic_weight_mul_sq_le_energy
    (u : ℝ → ℝ) (hu : ContDiff ℝ 1 u) (x : ℝ) (hx : x ∈ Icc (0 : ℝ) 1) :
    x * (1 - x) * u x ^ 2 ≤
      4 * ((∫ y in (0 : ℝ)..1, u y ^ 2) +
        ∫ y in (0 : ℝ)..1, y * (1 - y) * deriv u y ^ 2) := by
  let a := x / 2
  let b := (x + 1) / 2
  let w := x * (1 - x)
  have ha : 0 ≤ a := by
    dsimp [a]
    exact div_nonneg hx.1 (by norm_num)
  have hb : b ≤ 1 := by dsimp [b]; linarith only [hx.2]
  have hab : a < b := by dsimp [a, b]; linarith
  have hxab : x ∈ Icc a b := by
    constructor <;> dsimp [a, b] <;> linarith only [hx.1, hx.2]
  have hw0 : 0 ≤ w := mul_nonneg hx.1 (sub_nonneg.mpr hx.2)
  have hw1 : w ≤ 1 := by
    dsimp [w]
    nlinarith only [sq_nonneg (x - 1 / 2)]
  have hu1 := hu.continuous_deriv_one
  have hUcont : Continuous (fun y => u y ^ 2) := hu.continuous.pow 2
  have hPcont : Continuous (fun y => y * (1 - y) * deriv u y ^ 2) := by fun_prop
  have hDcont : Continuous (fun y => deriv u y ^ 2) := hu1.pow 2
  have hpoint := length_mul_sq_le_integral_sq_add_integral_deriv_sq u hu a b x hab hxab
  have hpoint' : u x ^ 2 ≤
      4 * (∫ y in a..b, u y ^ 2) + ∫ y in a..b, deriv u y ^ 2 := by
    have hlength : b - a = (1 / 2 : ℝ) := by dsimp [a, b]; ring
    rw [hlength] at hpoint
    nlinarith only [hpoint]
  have hU : (∫ y in a..b, u y ^ 2) ≤ ∫ y in (0 : ℝ)..1, u y ^ 2 :=
    intervalIntegral.integral_mono_interval ha hab.le hb
      (Filter.Eventually.of_forall fun y => sq_nonneg (u y))
      (hUcont.intervalIntegrable 0 1)
  have hP : w / 4 * (∫ y in a..b, deriv u y ^ 2) ≤
      ∫ y in (0 : ℝ)..1, y * (1 - y) * deriv u y ^ 2 := by
    have hlocal : w / 4 * (∫ y in a..b, deriv u y ^ 2) ≤
        ∫ y in a..b, y * (1 - y) * deriv u y ^ 2 := by
      rw [← intervalIntegral.integral_const_mul]
      apply intervalIntegral.integral_mono_on hab.le
        ((hDcont.const_mul (w / 4)).intervalIntegrable a b)
        (hPcont.intervalIntegrable a b)
      intro y hy
      have hprod := mul_le_mul hy.1 (sub_le_sub_left hy.2 1)
        (sub_nonneg.mpr hb) (ha.trans hy.1)
      have hweight : w / 4 ≤ y * (1 - y) := by
        dsimp [a, b] at hprod
        dsimp [w]
        nlinarith only [hprod]
      exact mul_le_mul_of_nonneg_right hweight (sq_nonneg (deriv u y))
    have hmono : (∫ y in a..b, y * (1 - y) * deriv u y ^ 2) ≤
        ∫ y in (0 : ℝ)..1, y * (1 - y) * deriv u y ^ 2 := by
      apply intervalIntegral.integral_mono_interval ha hab.le hb _
        (hPcont.intervalIntegrable 0 1)
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with y hy
      exact mul_nonneg (mul_nonneg hy.1.le (sub_nonneg.mpr hy.2)) (sq_nonneg _)
    exact hlocal.trans hmono
  have hU0 : 0 ≤ ∫ y in (0 : ℝ)..1, u y ^ 2 :=
    intervalIntegral.integral_nonneg zero_le_one (fun y _ => sq_nonneg (u y))
  have hpointScaled := mul_le_mul_of_nonneg_left hpoint' hw0
  have hUScaled := mul_le_mul_of_nonneg_left hU hw0
  have hUW := mul_le_mul_of_nonneg_right hw1 hU0
  change w * u x ^ 2 ≤ _
  nlinarith only [hpointScaled, hUScaled, hUW, hP]

end RicciFlowSharpEstimate.Analysis
