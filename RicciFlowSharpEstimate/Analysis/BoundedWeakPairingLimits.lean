/-
Copyright (c) 2026 Ziyang Qin. All rights reserved.
No license is granted by this file.
Authors: Ziyang Qin
-/
import RicciFlowSharpEstimate.Analysis.BoundedWeakPairing

/-!
# Bounded weak pairings with strongly convergent integrable tests

A common essential bound lets an L1-convergent sequence of test functions
replace a fixed test in a weak pairing. The limiting product is integrable.
-/

noncomputable section

namespace RicciFlowSharpEstimate.Analysis

open Filter MeasureTheory
open scoped Topology

/-- Bounded weak pairings remain convergent when the integrable test varies
strongly in L¹. The literal limiting product is genuinely integrable. -/
theorem integrable_and_tendsto_mul_of_bounded_weak_pairing
    {μ : Measure ℝ} {K : ℕ → ℝ → ℝ} {K0 : ℝ → ℝ} {g : ℕ → ℝ → ℝ} {g0 : ℝ → ℝ}
    {B : ℝ} (hK : ∀ n, AEStronglyMeasurable (K n) μ)
    (hK0 : AEStronglyMeasurable K0 μ)
    (hKB : ∀ n, ∀ᵐ x ∂μ, |K n x| ≤ B) (hK0B : ∀ᵐ x ∂μ, |K0 x| ≤ B)
    (hweak : ∀ v : ℝ → ℝ, Integrable v μ →
      Tendsto (fun n => ∫ x, K n x * v x ∂μ) atTop (𝓝 (∫ x, K0 x * v x ∂μ)))
    (hg : ∀ n, Integrable (g n) μ) (hg0 : Integrable g0 μ)
    (hstrong : Tendsto (fun n => ∫ x, |g n x - g0 x| ∂μ) atTop (𝓝 0)) :
    Integrable (fun x => K0 x * g0 x) μ ∧
      Tendsto (fun n => ∫ x, K n x * g n x ∂μ) atTop (𝓝 (∫ x, K0 x * g0 x ∂μ)) := by
  refine ⟨integrable_mul_of_ae_abs_le hK0 hK0B hg0, ?_⟩
  have herror : Tendsto
      (fun n => (∫ x, K n x * g n x ∂μ) - ∫ x, K n x * g0 x ∂μ) atTop (𝓝 0) := by
    apply squeeze_zero_norm (fun n => ?_) (by simpa only [mul_zero] using hstrong.const_mul B)
    simpa only [Real.norm_eq_abs] using
      abs_integral_mul_sub_le_of_ae_abs_le (hK n) (hKB n) (hg n) hg0
  have hsum := herror.add (hweak g0 hg0)
  simpa only [sub_add_cancel, zero_add] using hsum

end RicciFlowSharpEstimate.Analysis
