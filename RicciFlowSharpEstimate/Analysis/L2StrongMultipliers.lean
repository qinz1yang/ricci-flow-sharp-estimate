/-
Copyright (c) 2026 Ziyang Qin. All rights reserved.
No license is granted by this file.
Authors: Ziyang Qin
-/
import RicciFlowSharpEstimate.Analysis.L2WeakMultipliers
import Mathlib.MeasureTheory.Function.LpSpace.Complete

/-!
# Bounded almost-everywhere convergent multipliers of strong L2 sequences

Uniformly essentially bounded measurable real coefficients that converge
almost everywhere preserve strong L2 convergence of raw functions. The
varying product is split into a uniformly bounded coefficient times the
strong L2 error and a coefficient error times the fixed L2 limit.
Strong L2 convergence of two raw sequences also gives convergence of their
literal integral pairings. No finiteness assumption on the measure is used.
-/

noncomputable section

namespace RicciFlowSharpEstimate.Analysis

open Filter MeasureTheory
open scoped ENNReal Topology

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

/-- Uniformly essentially bounded, almost-everywhere convergent real
multipliers preserve strong L2 convergence. The conclusion records actual
L2 membership of every product and the limiting product. -/
theorem strong_L2_mul_of_ae_tendsto_of_ae_abs_le
    {u : ℕ → α → ℝ} {u0 : α → ℝ} {a : ℕ → α → ℝ} {a0 : α → ℝ}
    {D : ℝ}
    (hu : ∀ n, MemLp (u n) 2 μ) (hu0 : MemLp u0 2 μ)
    (hstrong : Tendsto (fun n ↦ eLpNorm (u n - u0) 2 μ) atTop (𝓝 0))
    (ha : ∀ n, AEStronglyMeasurable (a n) μ)
    (ha0 : AEStronglyMeasurable a0 μ)
    (hD : ∀ n, ∀ᵐ x ∂μ, |a n x| ≤ D)
    (hD0 : ∀ᵐ x ∂μ, |a0 x| ≤ D)
    (hconv : ∀ᵐ x ∂μ, Tendsto (fun n ↦ a n x) atTop (𝓝 (a0 x))) :
    (∀ n, MemLp (fun x ↦ a n x * u n x) 2 μ) ∧
      MemLp (fun x ↦ a0 x * u0 x) 2 μ ∧
      Tendsto (fun n ↦ eLpNorm (fun x ↦ a n x * u n x - a0 x * u0 x) 2 μ)
        atTop (𝓝 0) := by
  refine ⟨fun n ↦ memLp_mul_of_ae_abs_le (ha n) (hD n) (hu n),
    memLp_mul_of_ae_abs_le ha0 hD0 hu0, ?_⟩
  let U0 : Lp ℝ 2 μ := hu0.toLp u0
  have hfixedLp := tendsto_L2_mul_of_ae_tendsto ha ha0 hD hD0 hconv U0
  have hfixedNorm := (Lp.tendsto_Lp_iff_tendsto_eLpNorm''
    (fun n x ↦ a n x * U0 x)
    (fun n ↦ memLp_mul_of_ae_abs_le (ha n) (hD n) (Lp.memLp U0))
    (fun x ↦ a0 x * U0 x)
    (memLp_mul_of_ae_abs_le ha0 hD0 (Lp.memLp U0))).mp hfixedLp
  have hfixed : Tendsto
      (fun n ↦ eLpNorm (fun x ↦ a n x * u0 x - a0 x * u0 x) 2 μ)
      atTop (𝓝 0) := by
    refine hfixedNorm.congr' (Eventually.of_forall ?_)
    intro n
    apply eLpNorm_congr_ae
    filter_upwards [hu0.coeFn_toLp] with x hx
    change a n x * (hu0.toLp u0) x - a0 x * (hu0.toLp u0) x =
      a n x * u0 x - a0 x * u0 x
    rw [hx]
  have hmajorRaw := ENNReal.Tendsto.const_mul
    (a := ENNReal.ofReal D) hstrong (Or.inr ENNReal.ofReal_ne_top)
  have hmajor : Tendsto
      (fun n ↦ ENNReal.ofReal D * eLpNorm (u n - u0) 2 μ) atTop (𝓝 0) := by
    simpa only [mul_zero] using hmajorRaw
  have herror : Tendsto
      (fun n ↦ eLpNorm (fun x ↦ a n x * (u n x - u0 x)) 2 μ)
      atTop (𝓝 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hmajor
      (fun _ ↦ zero_le) ?_
    intro n
    refine eLpNorm_le_mul_eLpNorm_of_ae_le_mul
      ((ha n).mul ((hu n).sub hu0).aestronglyMeasurable) ?_ 2
    filter_upwards [hD n] with x hx
    change ‖a n x * (u n x - u0 x)‖ ≤ D * ‖u n x - u0 x‖
    rw [norm_mul, Real.norm_eq_abs (a n x)]
    exact mul_le_mul_of_nonneg_right hx (norm_nonneg _)
  have hsumRaw := herror.add hfixed
  have hsum : Tendsto
      (fun n ↦ eLpNorm (fun x ↦ a n x * (u n x - u0 x)) 2 μ +
        eLpNorm (fun x ↦ a n x * u0 x - a0 x * u0 x) 2 μ)
      atTop (𝓝 0) := by
    simpa only [zero_add] using hsumRaw
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsum
    (fun _ ↦ zero_le) ?_
  intro n
  have heq : (fun x ↦ a n x * u n x - a0 x * u0 x) =
      (fun x ↦ a n x * (u n x - u0 x)) +
        (fun x ↦ a n x * u0 x - a0 x * u0 x) := by
    funext x
    simp only [Pi.add_apply]
    ring
  change eLpNorm (fun x => a n x * u n x - a0 x * u0 x) 2 μ ≤
    eLpNorm (fun x => a n x * (u n x - u0 x)) 2 μ +
      eLpNorm (fun x => a n x * u0 x - a0 x * u0 x) 2 μ
  rw [heq]
  exact eLpNorm_add_le (by norm_num)

/-- Two strongly L2-convergent raw sequences have convergent literal
integral pairings. All products in the conclusion are genuinely integrable,
even when the ambient measure is infinite. -/
theorem tendsto_integral_mul_of_tendsto_eLpNorm_two
    {u v : ℕ → α → ℝ} {u0 v0 : α → ℝ}
    (hu : ∀ n, MemLp (u n) 2 μ) (hu0 : MemLp u0 2 μ)
    (hv : ∀ n, MemLp (v n) 2 μ) (hv0 : MemLp v0 2 μ)
    (hustrong : Tendsto (fun n ↦ eLpNorm (u n - u0) 2 μ) atTop (𝓝 0))
    (hvstrong : Tendsto (fun n ↦ eLpNorm (v n - v0) 2 μ) atTop (𝓝 0)) :
    (∀ n, Integrable (fun x ↦ u n x * v n x) μ) ∧
      Integrable (fun x ↦ u0 x * v0 x) μ ∧
      Tendsto (fun n ↦ ∫ x, u n x * v n x ∂μ) atTop
        (𝓝 (∫ x, u0 x * v0 x ∂μ)) := by
  refine ⟨fun n ↦ memLp_one_iff_integrable.mp ((hu n).mul (hv n)),
    memLp_one_iff_integrable.mp (hu0.mul hv0), ?_⟩
  have hU := (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' u hu u0 hu0).mpr hustrong
  have hV := (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' v hv v0 hv0).mpr hvstrong
  have hpair : ∀ {f g : α → ℝ} (hf : MemLp f 2 μ) (hg : MemLp g 2 μ),
      inner ℝ (hf.toLp f) (hg.toLp g) = ∫ x, f x * g x ∂μ := by
    intro f g hf hg
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hf.coeFn_toLp, hg.coeFn_toLp] with x hfx hgx
    simp only [Real.inner_apply, hfx, hgx]
  have hinner : Tendsto
      (fun n ↦ inner ℝ ((hu n).toLp (u n)) ((hv n).toLp (v n))) atTop
      (𝓝 (inner ℝ (hu0.toLp u0) (hv0.toLp v0))) := hU.inner hV
  simpa only [hpair] using hinner

end RicciFlowSharpEstimate.Analysis
