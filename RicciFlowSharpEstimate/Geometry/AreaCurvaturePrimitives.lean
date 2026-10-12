/-
Copyright (c) 2026 Ziyang Qin. All rights reserved.
No license is granted by this file.
Authors: Ziyang Qin
-/
import RicciFlowSharpEstimate.Geometry.AreaAction

/-!
# Affine curvature variations of the actual normalized primitives

The affine geometric term is fixed. The variation is the literal integral of
the curvature direction, and zero moments preserve both physical pole conditions.
-/

noncomputable section

namespace RicciFlowSharpEstimate.Geometry.AreaProfile

open MeasureTheory
open scoped ContDiff

/-- The variation of the corrected warp in a curvature direction. -/
def warpVariation (ξ : ℝ → ℝ) (x : ℝ) : ℝ :=
  -2 * ∫ s in (0 : ℝ)..x, (x - s) * ξ s

/-- The variation of the actual warp slope in the same curvature direction. -/
def warpSlopeVariation (ξ : ℝ → ℝ) (x : ℝ) : ℝ :=
  -2 * ∫ s in (0 : ℝ)..x, ξ s

/-- The actual warp is affine in the curvature coefficient. -/
theorem warp_add_mul (K ξ : ℝ → ℝ) (hK : Continuous K) (hξ : Continuous ξ)
    (t x : ℝ) : warp (fun s => K s + t * ξ s) x =
      warp K x + t * warpVariation ξ x := by
  have h0 : IntervalIntegrable (fun s : ℝ => (x - s) * K s) volume 0 x :=
    ((continuous_const.sub continuous_id).mul hK).intervalIntegrable 0 x
  have h1 : IntervalIntegrable (fun s : ℝ => (x - s) * ξ s) volume 0 x :=
    ((continuous_const.sub continuous_id).mul hξ).intervalIntegrable 0 x
  have hi : (∫ s in (0 : ℝ)..x, (x - s) * (K s + t * ξ s)) =
      (∫ s in (0 : ℝ)..x, (x - s) * K s) +
        t * ∫ s in (0 : ℝ)..x, (x - s) * ξ s := by
    calc
      _ = ∫ s in (0 : ℝ)..x, (x - s) * K s + t * ((x - s) * ξ s) := by
        apply intervalIntegral.integral_congr
        intro s _
        ring
      _ = _ := by
        rw [intervalIntegral.integral_add h0 (h1.const_mul t),
          intervalIntegral.integral_const_mul]
  simp only [warp, warpVariation, hi]
  ring

/-- The actual warp slope is affine in the same curvature direction. -/
theorem warpSlope_add_mul (K ξ : ℝ → ℝ) (hK : Continuous K) (hξ : Continuous ξ)
    (t x : ℝ) : warpSlope (fun s => K s + t * ξ s) x =
      warpSlope K x + t * warpSlopeVariation ξ x := by
  simp only [warpSlope, warpSlopeVariation,
    intervalIntegral.integral_add (hK.intervalIntegrable 0 x)
      ((hξ.intervalIntegrable 0 x).const_mul t), intervalIntegral.integral_const_mul]
  ring

/-- The warp direction is the actual antiderivative of the slope direction. -/
theorem warpVariation_hasDerivAt (ξ : ℝ → ℝ) (hξ : Continuous ξ) (x : ℝ) :
    HasDerivAt (warpVariation ξ) (warpSlopeVariation ξ x) x :=
  (Analysis.SecondPrimitive.integral_kernel_hasDerivAt ξ hξ 0 x).const_mul (-2)

/-- The slope direction has the prescribed actual curvature derivative. -/
theorem warpSlopeVariation_hasDerivAt (ξ : ℝ → ℝ) (hξ : Continuous ξ) (x : ℝ) :
    HasDerivAt (warpSlopeVariation ξ) (-2 * ξ x) x :=
  (hξ.integral_hasStrictDerivAt 0 x).hasDerivAt.const_mul (-2)

theorem warpVariation_continuous (ξ : ℝ → ℝ) (hξ : Continuous ξ) :
    Continuous (warpVariation ξ) :=
  continuous_iff_continuousAt.mpr fun x => (warpVariation_hasDerivAt ξ hξ x).continuousAt

theorem warpSlopeVariation_continuous (ξ : ℝ → ℝ) (hξ : Continuous ξ) :
    Continuous (warpSlopeVariation ξ) :=
  continuous_iff_continuousAt.mpr fun x => (warpSlopeVariation_hasDerivAt ξ hξ x).continuousAt

/-- Zero moments of the direction preserve the two moments of the original curvature. -/
theorem curvature_moments_add_mul (K ξ : ℝ → ℝ) (hK : Continuous K)
    (hξ : Continuous ξ) (hzero : (∫ x in (0 : ℝ)..1, ξ x) = 0)
    (hone : (∫ x in (0 : ℝ)..1, x * ξ x) = 0) (t : ℝ) :
    (∫ x in (0 : ℝ)..1, K x + t * ξ x) = (∫ x in (0 : ℝ)..1, K x) ∧
      (∫ x in (0 : ℝ)..1, x * (K x + t * ξ x)) =
        ∫ x in (0 : ℝ)..1, x * K x := by
  constructor
  · rw [intervalIntegral.integral_add (hK.intervalIntegrable 0 1)
      ((hξ.intervalIntegrable 0 1).const_mul t),
      intervalIntegral.integral_const_mul, hzero, mul_zero, add_zero]
  · calc
      _ = ∫ x in (0 : ℝ)..1, x * K x + t * (x * ξ x) := by
        apply intervalIntegral.integral_congr
        intro x _
        ring
      _ = _ := by
        have hKx : IntervalIntegrable (fun x : ℝ => x * K x) volume 0 1 :=
          (continuous_id.mul hK).intervalIntegrable 0 1
        have hξx : IntervalIntegrable (fun x : ℝ => x * ξ x) volume 0 1 :=
          (continuous_id.mul hξ).intervalIntegrable 0 1
        rw [intervalIntegral.integral_add hKx (hξx.const_mul t),
          intervalIntegral.integral_const_mul, hone, mul_zero, add_zero]

/-- The moment-preserving warp and slope directions vanish at both physical endpoints. -/
theorem curvature_variation_endpoints (ξ : ℝ → ℝ) (hξ : Continuous ξ)
    (hzero : (∫ x in (0 : ℝ)..1, ξ x) = 0)
    (hone : (∫ x in (0 : ℝ)..1, x * ξ x) = 0) :
    warpVariation ξ 0 = 0 ∧ warpVariation ξ 1 = 0 ∧
      warpSlopeVariation ξ 0 = 0 ∧ warpSlopeVariation ξ 1 = 0 := by
  simp [warpVariation, warpSlopeVariation,
    Analysis.SecondPrimitive.integral_kernel_eq ξ hξ 0 1, hzero, hone]

end RicciFlowSharpEstimate.Geometry.AreaProfile
