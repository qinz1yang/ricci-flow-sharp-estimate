/-
Copyright (c) 2026 Ziyang Qin. All rights reserved.
No license is granted by this file.
Authors: Ziyang Qin
-/
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Topology.Order.LiminfLimsup
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Lower semicontinuity of real square integrals under weak L2 convergence

The affine supporting minorant of the squared norm gives the eventual lower
bound without assuming convergence or tightness of the square integrals.
-/

noncomputable section

namespace RicciFlowSharpEstimate.Analysis

open Filter MeasureTheory
open scoped Topology

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

private theorem affine_square_minorant {f g : α → ℝ}
    (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    2 * (∫ x, f x * g x ∂μ) - (∫ x, g x ^ 2 ∂μ) ≤ ∫ x, f x ^ 2 ∂μ := by
  have hi : 0 ≤ ∫ x, (f x - g x) ^ 2 ∂μ :=
    integral_nonneg (fun x => sq_nonneg (f x - g x))
  have heq : (fun x => (f x - g x) ^ 2) =
      fun x => (f x ^ 2 - 2 * (f x * g x)) + g x ^ 2 := by
    funext x
    ring
  have hfg : Integrable (fun x => f x * g x) μ := hf.integrable_mul hg
  have htw : Integrable (fun x => 2 * (f x * g x)) μ := hfg.const_mul 2
  have hsub : Integrable (fun x => f x ^ 2 - 2 * (f x * g x)) μ :=
    hf.integrable_sq.sub htw
  rw [heq, integral_add hsub hg.integrable_sq,
    integral_sub hf.integrable_sq htw, integral_const_mul] at hi
  linarith

/-- Every strict lower bound on the limiting square integral eventually
bounds the square integrals of a weakly convergent L² sequence. No energy-tail
vanishing or convergence of the square integrals is required. -/
theorem eventually_lt_integral_sq_of_weak_L2
    {f : ℕ → α → ℝ} {g : α → ℝ} (hf : ∀ n, MemLp (f n) 2 μ) (hg : MemLp g 2 μ)
    (hweak : ∀ v : Lp ℝ 2 μ,
      Tendsto (fun n => ∫ x, f n x * v x ∂μ) atTop (𝓝 (∫ x, g x * v x ∂μ)))
    {a : ℝ} (ha : a < ∫ x, g x ^ 2 ∂μ) :
    ∀ᶠ n in atTop, a < ∫ x, f n x ^ 2 ∂μ := by
  let v : Lp ℝ 2 μ := hg.toLp g
  have heq (u : α → ℝ) : (∫ x, u x * v x ∂μ) = ∫ x, u x * g x ∂μ := by
    apply integral_congr_ae
    filter_upwards [hg.coeFn_toLp] with x hx
    change v x = g x at hx
    rw [hx]
  have hpair : Tendsto (fun n => ∫ x, f n x * g x ∂μ) atTop
      (𝓝 (∫ x, g x ^ 2 ∂μ)) := by
    simpa only [heq, pow_two] using hweak v
  have hminor : Tendsto (fun n => 2 * (∫ x, f n x * g x ∂μ) - ∫ x, g x ^ 2 ∂μ)
      atTop (𝓝 (∫ x, g x ^ 2 ∂μ)) := by
    convert (hpair.const_mul 2).sub_const (∫ x, g x ^ 2 ∂μ) using 1
    congr 1
    ring
  filter_upwards [hminor.eventually_const_lt ha] with n hn
  exact hn.trans_le (affine_square_minorant (hf n) hg)

/-- For a square-integral sequence bounded above, weak L² convergence gives
the ordinary real-valued liminf inequality. -/
theorem integral_sq_le_liminf_of_weak_L2
    {f : ℕ → α → ℝ} {g : α → ℝ} (hf : ∀ n, MemLp (f n) 2 μ) (hg : MemLp g 2 μ)
    (hweak : ∀ v : Lp ℝ 2 μ,
      Tendsto (fun n => ∫ x, f n x * v x ∂μ) atTop (𝓝 (∫ x, g x * v x ∂μ)))
    (hupper : IsBoundedUnder (· ≤ ·) atTop (fun n => ∫ x, f n x ^ 2 ∂μ)) :
    (∫ x, g x ^ 2 ∂μ) ≤ liminf (fun n => ∫ x, f n x ^ 2 ∂μ) atTop := by
  apply (le_liminf_iff hupper.isCoboundedUnder_ge
    ⟨0, eventually_map.mpr (Eventually.of_forall
      (fun n => integral_nonneg (fun x => sq_nonneg (f n x))))⟩).mpr
  intro a ha
  exact eventually_lt_integral_sq_of_weak_L2 hf hg hweak ha

/-- The sum of two weakly lower-semicontinuous square integrals remains
lower semicontinuous after subtracting a convergent real scalar term. -/
theorem eventually_lt_sum_integral_sq_sub_of_weak_L2
    {f h : ℕ → α → ℝ} {g k : α → ℝ} {s : ℕ → ℝ} {s0 : ℝ}
    (hf : ∀ n, MemLp (f n) 2 μ) (hg : MemLp g 2 μ)
    (hh : ∀ n, MemLp (h n) 2 μ) (hk : MemLp k 2 μ)
    (hfweak : ∀ v : Lp ℝ 2 μ,
      Tendsto (fun n => ∫ x, f n x * v x ∂μ) atTop (𝓝 (∫ x, g x * v x ∂μ)))
    (hhweak : ∀ v : Lp ℝ 2 μ,
      Tendsto (fun n => ∫ x, h n x * v x ∂μ) atTop (𝓝 (∫ x, k x * v x ∂μ)))
    (hs : Tendsto s atTop (𝓝 s0)) {a : ℝ}
    (ha : a < (∫ x, g x ^ 2 ∂μ) + (∫ x, k x ^ 2 ∂μ) - s0) :
    ∀ᶠ n in atTop, a < (∫ x, f n x ^ 2 ∂μ) + (∫ x, h n x ^ 2 ∂μ) - s n := by
  let ε := ((∫ x, g x ^ 2 ∂μ) + (∫ x, k x ^ 2 ∂μ) - s0 - a) / 4
  have hε : 0 < ε := by dsimp [ε]; linarith
  have hF := eventually_lt_integral_sq_of_weak_L2 hf hg hfweak
    (show (∫ x, g x ^ 2 ∂μ) - ε < (∫ x, g x ^ 2 ∂μ) by linarith)
  have hH := eventually_lt_integral_sq_of_weak_L2 hh hk hhweak
    (show (∫ x, k x ^ 2 ∂μ) - ε < (∫ x, k x ^ 2 ∂μ) by linarith)
  have hS := hs.eventually_lt_const (show s0 < s0 + ε by linarith)
  filter_upwards [hF, hH, hS] with n hnF hnH hnS
  dsimp [ε] at hnF hnH hnS
  linarith

end RicciFlowSharpEstimate.Analysis
