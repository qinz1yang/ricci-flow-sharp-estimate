/-
Copyright (c) 2026 Ziyang Qin. All rights reserved.
No license is granted by this file.
Authors: Ziyang Qin
-/
import Mathlib.MeasureTheory.Function.Holder
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Analysis.Normed.Operator.Mul
import Mathlib.Analysis.InnerProductSpace.Continuous

/-!
# Continuity of weighted L2 mass

Strong L-infinity convergence of real weights and strong L2 convergence of
real probes imply convergence of the literal weighted square integrals. The
proof uses the continuous Holder multiplier and its a.e. pointwise product
law, followed by continuity of the L2 inner product. No finiteness assumption
on the measure is needed.
-/

noncomputable section

namespace RicciFlowSharpEstimate.Analysis.L2WeightedMassContinuity

open Filter MeasureTheory
open scoped ENNReal

variable {α ι : Type*} [MeasurableSpace α] {μ : Measure α} {l : Filter ι}

/-- Weighted square integrals are continuous when the actual weights converge
in L-infinity and the actual probes converge in L2. -/
theorem tendsto_integral_mul_sq
    {a : ι → Lp ℝ ∞ μ} {a0 : Lp ℝ ∞ μ}
    {r : ι → Lp ℝ 2 μ} {r0 : Lp ℝ 2 μ}
    (ha : Tendsto a l (nhds a0)) (hr : Tendsto r l (nhds r0)) :
    Tendsto (fun n ↦ ∫ x, a n x * (r n x) ^ 2 ∂μ) l
      (nhds (∫ x, a0 x * (r0 x) ^ 2 ∂μ)) := by
  let M : Lp ℝ ∞ μ →L[ℝ] Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ :=
    (ContinuousLinearMap.mul ℝ ℝ).holderL μ ∞ 2 2
  have hproduct : ∀ (b : Lp ℝ ∞ μ) (s : Lp ℝ 2 μ),
      ⇑(M b s) =ᵐ[μ] fun x ↦ b x * s x := by
    intro b s
    simpa only [M, ContinuousLinearMap.holderL_apply_apply,
      ContinuousLinearMap.mul_apply'] using
      (ContinuousLinearMap.mul ℝ ℝ).coeFn_holder (r := 2) b s
  have hpair : ∀ (b : Lp ℝ ∞ μ) (s : Lp ℝ 2 μ),
      inner ℝ (M b s) s = ∫ x, b x * (s x) ^ 2 ∂μ := by
    intro b s
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hproduct b s] with x hx
    simp only [Real.inner_apply, hx, pow_two, mul_assoc]
  have hMraw := (M.continuous₂.tendsto (a0, r0)).comp (ha.prodMk_nhds hr)
  have hM : Tendsto (fun n ↦ M (a n) (r n)) l (nhds (M a0 r0)) := by
    simpa only [Function.comp_def, Function.uncurry] using hMraw
  have hinner : Tendsto (fun n ↦ inner ℝ (M (a n) (r n)) (r n)) l
      (nhds (inner ℝ (M a0 r0) r0)) := hM.inner hr
  simpa only [hpair] using hinner

/-- Eventual a.e. uniform bounds on the literal differences of L-infinity
representatives imply convergence in the L-infinity norm. -/
theorem tendsto_top_of_eventually_ae_abs_sub_le
    {a : ι → Lp ℝ ∞ μ} {a0 : Lp ℝ ∞ μ}
    (h : ∀ ε : ℝ, 0 < ε → ∀ᶠ n in l, ∀ᵐ x ∂μ, |a n x - a0 x| ≤ ε) :
    Tendsto a l (nhds a0) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  filter_upwards [h (ε / 2) (half_pos hε)] with n hn
  have hae : ∀ᵐ x ∂μ, ‖(a n - a0) x‖ ≤ ε / 2 := by
    filter_upwards [Lp.coeFn_sub (a n) a0, hn] with x hx hnx
    simpa only [hx, Pi.sub_apply, Real.norm_eq_abs] using hnx
  have he : eLpNorm (a n - a0) ∞ μ ≤ ENNReal.ofReal (ε / 2) := by
    rw [eLpNorm_exponent_top (Lp.aestronglyMeasurable (a n - a0))]
    exact eLpNormEssSup_le_of_ae_bound hae
  have hnorm : ‖a n - a0‖ ≤ ε / 2 := by
    rw [Lp.norm_def]
    exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top he).trans_eq
      (ENNReal.toReal_ofReal (half_pos hε).le)
  rw [dist_eq_norm]
  exact hnorm.trans_lt (half_lt_self hε)

end RicciFlowSharpEstimate.Analysis.L2WeightedMassContinuity
