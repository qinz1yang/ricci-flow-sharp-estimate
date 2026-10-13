/-
Copyright (c) 2026 Ziyang Qin. All rights reserved.
No license is granted by this file.
Authors: Ziyang Qin
-/
import Mathlib.MeasureTheory.Function.ContinuousMapDense

/-!
# Extending bounded weak pairings to integrable tests

A common almost-everywhere bound on real functions extends convergence of
their integral pairings from `L²` tests to every integrable real test. The
proof uses bounded continuous approximation in `L¹` on a finite weakly
regular measure space, together with a uniform estimate for the pairing
error.
-/

noncomputable section

namespace RicciFlowSharpEstimate.Analysis

open Filter MeasureTheory
open scoped Topology

/-- An almost-everywhere bounded measurable multiplier preserves
integrability of a real test function. -/
theorem integrable_mul_of_ae_abs_le
    {μ : Measure ℝ} {K g : ℝ → ℝ} {B : ℝ}
    (hK : AEStronglyMeasurable K μ) (hB : ∀ᵐ x ∂μ, |K x| ≤ B)
    (hg : Integrable g μ) : Integrable (fun x ↦ K x * g x) μ :=
  hg.bdd_mul hK (by simpa only [Real.norm_eq_abs] using hB)

/-- A common essential bound controls the change in a pairing by the `L¹`
distance between its two test functions. -/
theorem abs_integral_mul_sub_le_of_ae_abs_le
    {μ : Measure ℝ} {K g h : ℝ → ℝ} {B : ℝ}
    (hK : AEStronglyMeasurable K μ) (hB : ∀ᵐ x ∂μ, |K x| ≤ B)
    (hg : Integrable g μ) (hh : Integrable h μ) :
    |(∫ x, K x * g x ∂μ) - ∫ x, K x * h x ∂μ| ≤
      B * ∫ x, ‖g x - h x‖ ∂μ := by
  have hKg : Integrable (fun x ↦ K x * g x) μ :=
    integrable_mul_of_ae_abs_le hK hB hg
  have hKh : Integrable (fun x ↦ K x * h x) μ :=
    integrable_mul_of_ae_abs_le hK hB hh
  have hi : Integrable (fun x ↦ B * ‖g x - h x‖) μ :=
    (hg.sub hh).norm.const_mul B
  have hb : ∀ᵐ x ∂μ, ‖K x * g x - K x * h x‖ ≤ B * ‖g x - h x‖ := by
    filter_upwards [hB] with x hx
    rw [← mul_sub, norm_mul]
    exact mul_le_mul_of_nonneg_right
      (by simpa only [Real.norm_eq_abs] using hx) (norm_nonneg _)
  rw [← integral_sub hKg hKh]
  simpa only [Real.norm_eq_abs, integral_const_mul] using
    norm_integral_le_of_norm_le hi hb

/-- For a finite weakly regular measure, uniformly essentially bounded real
functions whose pairings converge against every `L²` test also have convergent
pairings against every integrable real test. -/
theorem tendsto_integral_mul_of_bounded_L2_pairings
    {μ : Measure ℝ} [IsFiniteMeasure μ] [μ.WeaklyRegular]
    {K : ℕ → ℝ → ℝ} {K0 : ℝ → ℝ} {B : ℝ}
    (hK : ∀ n, AEStronglyMeasurable (K n) μ)
    (hK0 : AEStronglyMeasurable K0 μ)
    (hKB : ∀ n, ∀ᵐ x ∂μ, |K n x| ≤ B) (hK0B : ∀ᵐ x ∂μ, |K0 x| ≤ B)
    (hpair : ∀ v : Lp ℝ 2 μ,
      Tendsto (fun n ↦ ∫ x, K n x * v x ∂μ) atTop
        (𝓝 (∫ x, K0 x * v x ∂μ))) :
    ∀ g : ℝ → ℝ, Integrable g μ →
      Tendsto (fun n ↦ ∫ x, K n x * g x ∂μ) atTop
        (𝓝 (∫ x, K0 x * g x ∂μ)) := by
  intro g hg
  let C : ℝ := max B 0 + 1
  have hC : 0 < C := by
    dsimp [C]
    have := le_max_right B (0 : ℝ)
    linarith
  have hBC : B ≤ C := by
    dsimp [C]
    have := le_max_left B (0 : ℝ)
    linarith
  have hKC : ∀ n, ∀ᵐ x ∂μ, |K n x| ≤ C := fun n ↦
    (hKB n).mono fun _ hx ↦ hx.trans hBC
  have hK0C : ∀ᵐ x ∂μ, |K0 x| ≤ C :=
    hK0B.mono fun _ hx ↦ hx.trans hBC
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨u, huerr, hui⟩ :=
    hg.exists_boundedContinuous_integral_sub_le
      (ε := ε / (4 * C)) (div_pos hε (mul_pos (by norm_num) hC))
  have huLp : MemLp (u : ℝ → ℝ) 2 μ := u.memLp_top.mono_exponent le_top
  let v : Lp ℝ 2 μ := huLp.toLp (u : ℝ → ℝ)
  have hv : (fun x ↦ v x) =ᵐ[μ] (fun x ↦ u x) := huLp.coeFn_toLp
  have hseq_eq : ∀ n, (∫ x, K n x * v x ∂μ) = ∫ x, K n x * u x ∂μ := by
    intro n
    apply integral_congr_ae
    filter_upwards [hv] with x hx
    rw [hx]
  have hlim_eq : (∫ x, K0 x * v x ∂μ) = ∫ x, K0 x * u x ∂μ := by
    apply integral_congr_ae
    filter_upwards [hv] with x hx
    rw [hx]
  have hutendsto : Tendsto (fun n ↦ ∫ x, K n x * u x ∂μ) atTop
      (𝓝 (∫ x, K0 x * u x ∂μ)) := by
    simpa only [hseq_eq, hlim_eq] using hpair v
  have hbudget : C * (∫ x, ‖g x - u x‖ ∂μ) ≤ ε / 4 := by
    calc
      C * (∫ x, ‖g x - u x‖ ∂μ) ≤ C * (ε / (4 * C)) :=
        mul_le_mul_of_nonneg_left huerr hC.le
      _ = (ε * C) / (4 * C) := by ring
      _ = ε / 4 := mul_div_mul_right ε 4 hC.ne'
  filter_upwards [(Metric.tendsto_nhds.mp hutendsto) (ε / 2) (half_pos hε)]
    with n hn
  have hleft : dist (∫ x, K n x * g x ∂μ) (∫ x, K n x * u x ∂μ) ≤ ε / 4 := by
    simpa only [Real.dist_eq] using
      (abs_integral_mul_sub_le_of_ae_abs_le (hK n) (hKC n) hg hui).trans hbudget
  have hright : dist (∫ x, K0 x * u x ∂μ) (∫ x, K0 x * g x ∂μ) ≤ ε / 4 := by
    rw [dist_comm]
    simpa only [Real.dist_eq] using
      (abs_integral_mul_sub_le_of_ae_abs_le hK0 hK0C hg hui).trans hbudget
  have htri : dist (∫ x, K n x * g x ∂μ) (∫ x, K0 x * g x ∂μ) ≤
      dist (∫ x, K n x * g x ∂μ) (∫ x, K n x * u x ∂μ) +
        (dist (∫ x, K n x * u x ∂μ) (∫ x, K0 x * u x ∂μ) +
          dist (∫ x, K0 x * u x ∂μ) (∫ x, K0 x * g x ∂μ)) := by
    exact (dist_triangle _ _ _).trans (add_le_add le_rfl (dist_triangle _ _ _))
  linarith

end RicciFlowSharpEstimate.Analysis
