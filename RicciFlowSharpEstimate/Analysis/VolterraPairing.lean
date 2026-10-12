/-
Copyright (c) 2026 Ziyang Qin. All rights reserved.
No license is granted by this file.
Authors: Ziyang Qin
-/
import RicciFlowSharpEstimate.Analysis.SecondPrimitive
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

/-!
# Pairing identities for Volterra primitives

The first and triangular second primitives pair with their corresponding tail
integrals. The identities hold for either orientation of the endpoints.
-/

noncomputable section

namespace RicciFlowSharpEstimate.Analysis.VolterraPairing

open MeasureTheory

private theorem tail_hasDerivAt (f : ℝ → ℝ) (hf : Continuous f) (b x : ℝ) :
    HasDerivAt (fun y => ∫ t in y..b, f t) (-f x) x :=
  intervalIntegral.integral_hasDerivAt_left (hf.intervalIntegrable x b)
    (hf.stronglyMeasurableAtFilter _ _) hf.continuousAt

private theorem prefix_continuous (f : ℝ → ℝ) (hf : Continuous f) (a : ℝ) :
    Continuous (fun x => ∫ t in a..x, f t) :=
  continuous_iff_continuousAt.mpr fun x =>
    (hf.integral_hasStrictDerivAt a x).hasDerivAt.continuousAt

private theorem tail_continuous (f : ℝ → ℝ) (hf : Continuous f) (b : ℝ) :
    Continuous (fun x => ∫ t in x..b, f t) :=
  continuous_iff_continuousAt.mpr fun x => (tail_hasDerivAt f hf b x).continuousAt

/-- Pairing a continuous coefficient with a first primitive transfers the
primitive to a tail integral of the coefficient. -/
theorem integral_mul_primitive_eq (β ξ : ℝ → ℝ) (hβ : Continuous β)
    (hξ : Continuous ξ) (a b : ℝ) :
    (∫ x in a..b, β x * (∫ t in a..x, ξ t)) =
      ∫ t in a..b, ξ t * (∫ x in t..b, β x) := by
  have hParts := intervalIntegral.integral_mul_deriv_eq_deriv_mul
    (a := a) (b := b)
    (u := fun x => ∫ t in x..b, β t) (u' := fun x => -β x)
    (v := fun x => ∫ t in a..x, ξ t) (v' := ξ)
    (fun x _ => tail_hasDerivAt β hβ b x)
    (fun x _ => (hξ.integral_hasStrictDerivAt a x).hasDerivAt)
    (hβ.neg.intervalIntegrable a b) (hξ.intervalIntegrable a b)
  simpa only [intervalIntegral.integral_same, zero_mul, mul_zero, sub_zero,
    zero_sub, neg_mul, intervalIntegral.integral_neg, neg_neg, mul_comm] using hParts.symm

/-- Pairing a continuous coefficient with a triangular second primitive
transfers the triangular kernel to a tail integral of the coefficient. -/
theorem integral_mul_kernel_eq (α ξ : ℝ → ℝ) (hα : Continuous α)
    (hξ : Continuous ξ) (a b : ℝ) :
    (∫ x in a..b, α x * (∫ t in a..x, (x - t) * ξ t)) =
      ∫ t in a..b, ξ t * (∫ x in t..b, (x - t) * α x) := by
  have hPrefix := prefix_continuous ξ hξ a
  have hWeightedPrefix := prefix_continuous (fun t : ℝ => t * ξ t)
    (continuous_id.mul hξ) a
  have hTail := tail_continuous α hα b
  have hWeightedTail := tail_continuous (fun x : ℝ => x * α x)
    (continuous_id.mul hα) b
  have hFirst := integral_mul_primitive_eq (fun x : ℝ => x * α x) ξ
    (continuous_id.mul hα) hξ a b
  have hSecond := integral_mul_primitive_eq α (fun t : ℝ => t * ξ t)
    hα (continuous_id.mul hξ) a b
  calc
    (∫ x in a..b, α x * (∫ t in a..x, (x - t) * ξ t)) =
        (∫ x in a..b, (x * α x) * (∫ t in a..x, ξ t)) -
          ∫ x in a..b, α x * (∫ t in a..x, t * ξ t) := by
      have hA : IntervalIntegrable
          (fun x => (x * α x) * (∫ t in a..x, ξ t)) volume a b :=
        ((continuous_id.mul hα).mul hPrefix).intervalIntegrable a b
      have hB : IntervalIntegrable
          (fun x => α x * (∫ t in a..x, t * ξ t)) volume a b :=
        (hα.mul hWeightedPrefix).intervalIntegrable a b
      rw [← intervalIntegral.integral_sub hA hB]
      apply intervalIntegral.integral_congr
      intro x _
      dsimp only
      rw [SecondPrimitive.integral_kernel_eq ξ hξ a x]
      ring
    _ = (∫ t in a..b, ξ t * (∫ x in t..b, x * α x)) -
          ∫ t in a..b, (t * ξ t) * (∫ x in t..b, α x) := by
      rw [hFirst, hSecond]
    _ = ∫ t in a..b, ξ t * (∫ x in t..b, (x - t) * α x) := by
      have hA : IntervalIntegrable
          (fun t => ξ t * (∫ x in t..b, x * α x)) volume a b :=
        (hξ.mul hWeightedTail).intervalIntegrable a b
      have hB : IntervalIntegrable
          (fun t => (t * ξ t) * (∫ x in t..b, α x)) volume a b :=
        ((continuous_id.mul hξ).mul hTail).intervalIntegrable a b
      rw [← intervalIntegral.integral_sub hA hB]
      apply intervalIntegral.integral_congr
      intro t _
      have hKernel : (∫ x in t..b, (x - t) * α x) =
          (∫ x in t..b, x * α x) - t * (∫ x in t..b, α x) := by
        calc
          (∫ x in t..b, (x - t) * α x) =
              ∫ x in t..b, x * α x - t * α x := by
            apply intervalIntegral.integral_congr
            intro x _
            ring
          _ = (∫ x in t..b, x * α x) - t * (∫ x in t..b, α x) := by
            have h1 : IntervalIntegrable (fun x : ℝ => x * α x) volume t b :=
              (continuous_id.mul hα).intervalIntegrable t b
            have h2 : IntervalIntegrable (fun x => t * α x) volume t b :=
              (continuous_const.mul hα).intervalIntegrable t b
            rw [intervalIntegral.integral_sub h1 h2, intervalIntegral.integral_const_mul]
      dsimp only
      rw [hKernel]
      ring

end RicciFlowSharpEstimate.Analysis.VolterraPairing
