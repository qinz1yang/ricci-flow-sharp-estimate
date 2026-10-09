/-
Copyright (c) 2026 Ziyang Qin. All rights reserved.
No license is granted by this file.
Authors: Ziyang Qin
-/
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Mul

/-!
# Calculus of the triangular second primitive

The literal triangular integral is a second antiderivative of its continuous
coefficient. Adapted from Ziyang Qin's historical smooth meridian primitives.
-/

noncomputable section

namespace RicciFlowSharpEstimate.Analysis.SecondPrimitive

open MeasureTheory
open scoped ContDiff

/-- Splitting the triangular kernel reduces its integral to two ordinary moments. -/
theorem integral_kernel_eq (u : ℝ → ℝ) (hu : Continuous u) (a x : ℝ) :
    (∫ t in a..x, (x - t) * u t) =
      x * (∫ t in a..x, u t) - ∫ t in a..x, t * u t := by
  have huInt : IntervalIntegrable u volume a x := hu.intervalIntegrable a x
  have htuInt : IntervalIntegrable (fun t : ℝ => t * u t) volume a x :=
    (continuous_id.mul hu).intervalIntegrable a x
  calc
    (∫ t in a..x, (x - t) * u t) = ∫ t in a..x, x * u t - t * u t := by
      apply intervalIntegral.integral_congr
      intro t _
      ring
    _ = (∫ t in a..x, x * u t) - ∫ t in a..x, t * u t :=
      intervalIntegral.integral_sub (huInt.const_mul x) htuInt
    _ = x * (∫ t in a..x, u t) - ∫ t in a..x, t * u t := by
      rw [intervalIntegral.integral_const_mul]

/-- The derivative of the actual triangular integral is its first primitive. -/
theorem integral_kernel_hasDerivAt (u : ℝ → ℝ) (hu : Continuous u) (a x : ℝ) :
    HasDerivAt (fun y => ∫ t in a..y, (y - t) * u t)
      (∫ t in a..x, u t) x := by
  have hFunction : (fun y => ∫ t in a..y, (y - t) * u t) =
      fun y => y * (∫ t in a..y, u t) - ∫ t in a..y, t * u t := by
    funext y
    exact integral_kernel_eq u hu a y
  rw [hFunction]
  have hFirst := (hu.integral_hasStrictDerivAt a x).hasDerivAt
  have hWeighted := ((continuous_id.mul hu).integral_hasStrictDerivAt a x).hasDerivAt
  convert ((hasDerivAt_id x).mul hFirst).sub hWeighted using 1
  · rfl
  · simp only [id_eq, Pi.mul_apply]
    ring

/-- A smooth coefficient has a smooth integral with a fixed lower endpoint. -/
theorem integral_contDiff (u : ℝ → ℝ) (hu : ContDiff ℝ ∞ u) (a : ℝ) :
    ContDiff ℝ ∞ (fun x => ∫ t in a..x, u t) := by
  rw [contDiff_infty_iff_deriv]
  refine ⟨fun x => (hu.continuous.integral_hasStrictDerivAt a x).hasDerivAt.differentiableAt, ?_⟩
  have hDeriv : deriv (fun x => ∫ t in a..x, u t) = u := by
    funext x
    exact (hu.continuous.integral_hasStrictDerivAt a x).hasDerivAt.deriv
  rw [hDeriv]
  exact hu

/-- A smooth coefficient has a smooth triangular second primitive. -/
theorem integral_kernel_contDiff (u : ℝ → ℝ) (hu : ContDiff ℝ ∞ u) (a : ℝ) :
    ContDiff ℝ ∞ (fun x => ∫ t in a..x, (x - t) * u t) := by
  rw [contDiff_infty_iff_deriv]
  refine ⟨fun x => (integral_kernel_hasDerivAt u hu.continuous a x).differentiableAt, ?_⟩
  have hDeriv : deriv (fun x => ∫ t in a..x, (x - t) * u t) =
      fun x => ∫ t in a..x, u t := by
    funext x
    exact (integral_kernel_hasDerivAt u hu.continuous a x).deriv
  rw [hDeriv]
  exact integral_contDiff u hu a

end RicciFlowSharpEstimate.Analysis.SecondPrimitive
