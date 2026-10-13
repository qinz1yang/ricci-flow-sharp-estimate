/-
Copyright (c) 2026 Ziyang Qin. All rights reserved.
No license is granted by this file.
Authors: Ziyang Qin
-/
import RicciFlowSharpEstimate.Analysis.HilbertConvexApproximation
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSpace.Complete

/-!
# Simultaneous convex approximation of weak L2 limits

One family of finite convex tail mixtures approximates a finite collection
of raw weak L2 limits strongly. The coefficients act on the original raw
functions and their actual L2 classes, with the representative equations
proved almost everywhere.
-/

noncomputable section

namespace RicciFlowSharpEstimate.Analysis

open Filter MeasureTheory
open scoped Topology BigOperators

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

private theorem inner_toLp_left {f : α → ℝ} (hf : MemLp f 2 μ) (v : Lp ℝ 2 μ) :
    inner ℝ (hf.toLp f) v = ∫ x, f x * v x ∂μ := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hf.coeFn_toLp] with x hx
  simp only [Real.inner_apply, hx]

private theorem sum_toLp_ae (s : Finset ℕ) (w : ℕ → ℝ) (f : ℕ → α → ℝ)
    (hf : ∀ n, MemLp (f n) 2 μ) :
    (fun x => (∑ i ∈ s, w i • (hf i).toLp (f i)) x) =ᵐ[μ]
      (fun x => ∑ i ∈ s, w i * f i x) := by
  apply (Lp.coeFn_fun_finsetSum s (fun i => w i • (hf i).toLp (f i))).trans
  have hi (i : ℕ) :
      (fun x => (w i • (hf i).toLp (f i)) x) =ᵐ[μ] (fun x => w i * f i x) := by
    filter_upwards [Lp.coeFn_smul (w i) ((hf i).toLp (f i)), (hf i).coeFn_toLp]
      with x hx hy
    simpa only [Pi.smul_apply, smul_eq_mul, hy] using hx
  filter_upwards [eventuallyEq_sum (s := s) (fun i _ => hi i)] with x hx
  simpa only [Finset.sum_apply] using hx

/-- A finite collection of raw weak L² limits has simultaneous strong L²
approximants given by the same finite convex combinations of original tails. -/
theorem exists_tail_convexCombination_tendsto_eLpNorm_two
    {ι : Type*} [Finite ι] (f : ℕ → ι → α → ℝ) (g : ι → α → ℝ)
    (hf : ∀ n i, MemLp (f n i) 2 μ) (hg : ∀ i, MemLp (g i) 2 μ)
    (hweak : ∀ i, ∀ v : Lp ℝ 2 μ,
      Tendsto (fun n => ∫ x, f n i x * v x ∂μ) atTop (𝓝 (∫ x, g i x * v x ∂μ))) :
    ∃ (s : ℕ → Finset ℕ) (w : ℕ → ℕ → ℝ),
      (∀ n i, 0 ≤ w n i) ∧
      (∀ n i, i ∉ s n → w n i = 0) ∧
      (∀ n, ∀ i ∈ s n, n ≤ i) ∧
      (∀ n, (∑ i ∈ s n, w n i) = 1) ∧
      (∀ n j, MemLp (fun x => ∑ i ∈ s n, w n i * f i j x) 2 μ) ∧
      ∀ j, Tendsto (fun n => eLpNorm
        (fun x => (∑ i ∈ s n, w n i * f i j x) - g j x) 2 μ) atTop (𝓝 0) := by
  let U : ℕ → ι → Lp ℝ 2 μ := fun n i => (hf n i).toLp (f n i)
  let X : ι → Lp ℝ 2 μ := fun i => (hg i).toLp (g i)
  have hUweak : ∀ i, ∀ v : Lp ℝ 2 μ,
      Tendsto (fun n => inner ℝ (U n i) v) atTop (𝓝 (inner ℝ (X i) v)) := by
    intro i v
    simpa only [U, X, inner_toLp_left] using hweak i v
  obtain ⟨s, w, hw, hwzero, htail, hsum, hconv⟩ :=
    exists_tail_convexCombination_tendsto_family U X hUweak
  have hAE (n : ℕ) (j : ι) :
      (fun x => (∑ i ∈ s n, w n i • U i j) x) =ᵐ[μ]
        (fun x => ∑ i ∈ s n, w n i * f i j x) :=
    sum_toLp_ae (s n) (w n) (fun i => f i j) (fun i => hf i j)
  refine ⟨s, w, hw, hwzero, htail, hsum, ?_, ?_⟩
  · intro n j
    exact (Lp.memLp (∑ i ∈ s n, w n i • U i j)).ae_eq (hAE n j)
  · intro j
    have ht := (Lp.tendsto_Lp_iff_tendsto_eLpNorm'
      (fun n => ∑ i ∈ s n, w n i • U i j) (X j)).mp (hconv j)
    refine ht.congr' (Eventually.of_forall ?_)
    intro n
    apply eLpNorm_congr_ae
    filter_upwards [hAE n j, (hg j).coeFn_toLp] with x hx hx0
    change (∑ i ∈ s n, w n i • U i j) x - (hg j).toLp (g j) x =
      (∑ i ∈ s n, w n i * f i j x) - g j x
    rw [hx, hx0]

end RicciFlowSharpEstimate.Analysis
