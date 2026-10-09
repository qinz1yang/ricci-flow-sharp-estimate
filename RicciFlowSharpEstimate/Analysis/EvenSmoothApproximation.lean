/-
Copyright (c) 2026 Ziyang Qin. All rights reserved.
No license is granted by this file.
Authors: Ziyang Qin
-/
import DifferentialGeometry.Analysis.Integration.Convolution.Approximation
import DifferentialGeometry.Analysis.Integration.Convolution.ConvexRange
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Even smooth approximation within a closed interval

Normalized smooth convolution preserves a closed interval, and averaging with reflection
preserves that interval while imposing evenness. The resulting smooth sequence converges
uniformly to the original uniformly continuous even function.
-/

noncomputable section

open Filter MeasureTheory Set
open scoped ContDiff Convolution Topology

namespace RicciFlowSharpEstimate.Analysis

private theorem normed_convolution_mem_Icc (φ : ContDiffBump (0 : ℝ))
    {a : ℝ → ℝ} (ha : Continuous a) {lo hi : ℝ}
    (hbox : ∀ x, lo ≤ a x ∧ a x ≤ hi) (x : ℝ) :
    (φ.normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] a) x ∈ Icc lo hi := by
  rw [convolution_def]
  apply (convex_Icc lo hi).integral_smul_mem_of_nonneg_of_integral_eq_one isClosed_Icc
    φ.continuous_normed.measurable.aemeasurable
    (Eventually.of_forall φ.nonneg_normed) φ.integral_normed
  · exact Eventually.of_forall fun y => hbox (x - y)
  · exact φ.hasCompactSupport_normed.convolutionExists_left (ContinuousLinearMap.lsmul ℝ ℝ)
      φ.continuous_normed ha.locallyIntegrable x

/-- A uniformly continuous even function with values in a closed interval admits a
uniformly convergent sequence of globally smooth even functions in the same interval.
The endpoints may coincide, and no sign condition is required. -/
theorem exists_contDiff_even_sequence_Icc {a : ℝ → ℝ} (ha : UniformContinuous a)
    (heven : Function.Even a) {lo hi : ℝ} (hbox : ∀ x, lo ≤ a x ∧ a x ≤ hi) :
    ∃ f : ℕ → ℝ → ℝ,
      (∀ n, ContDiff ℝ ∞ (f n) ∧ Function.Even (f n) ∧
        ∀ x, lo ≤ f n x ∧ f n x ≤ hi) ∧
      TendstoUniformly f a atTop := by
  let φ : ℕ → ContDiffBump (0 : ℝ) := fun n =>
    { rIn := (1 / ((n : ℝ) + 1)) / 2
      rOut := 1 / ((n : ℝ) + 1)
      rIn_pos := by positivity
      rIn_lt_rOut := half_lt_self (by positivity) }
  let g : ℕ → ℝ → ℝ := fun n =>
    (φ n).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] a
  have hg_smooth (n : ℕ) : ContDiff ℝ ∞ (g n) :=
    (φ n).hasCompactSupport_normed.contDiff_convolution_left
      (ContinuousLinearMap.lsmul ℝ ℝ) (φ n).contDiff_normed ha.continuous.locallyIntegrable
  have hg_box (n : ℕ) (x : ℝ) : lo ≤ g n x ∧ g n x ≤ hi :=
    normed_convolution_mem_Icc (φ n) ha.continuous hbox x
  have hg_lim : TendstoUniformly g a atTop :=
    ContDiffBump.tendstoUniformly_normed_convolution
      (show Tendsto (fun n => (φ n).rOut) atTop (𝓝 0) from
        tendsto_one_div_add_atTop_nhds_zero_nat) ha
  refine ⟨fun n x => (g n x + g n (-x)) / 2, ?_, ?_⟩
  · intro n
    refine ⟨((hg_smooth n).add ((hg_smooth n).comp contDiff_id.neg)).div_const 2, ?_, ?_⟩
    · intro x
      simp only [neg_neg, add_comm]
    · intro x
      obtain ⟨hl, hu⟩ := hg_box n x
      obtain ⟨hl', hu'⟩ := hg_box n (-x)
      constructor <;> linarith
  · apply Metric.tendstoUniformly_iff.mpr
    intro ε hε
    filter_upwards [Metric.tendstoUniformly_iff.mp hg_lim ε hε] with n hn
    intro x
    have hpos := hn x
    have hneg := hn (-x)
    rw [heven x] at hneg
    simp only [Real.dist_eq, abs_lt] at hpos hneg ⊢
    constructor <;> linarith

end RicciFlowSharpEstimate.Analysis
