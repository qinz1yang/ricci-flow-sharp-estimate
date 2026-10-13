/-
Copyright (c) 2026 Ziyang Qin. All rights reserved.
No license is granted by this file.
Authors: Ziyang Qin
-/
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.InnerProductSpace.Continuous
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Bounded almost-everywhere convergent multipliers of weak L2 sequences

A bounded weakly convergent real L2 sequence can be paired with a strongly
convergent L2 sequence of tests. Uniformly essentially bounded multipliers
that converge almost everywhere multiply each fixed L2 test strongly in L2,
so they preserve weak convergence of the original sequence. The measure
need not be finite.
-/

noncomputable section

namespace RicciFlowSharpEstimate.Analysis

open Filter MeasureTheory
open scoped ENNReal Topology

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

/-- An essentially bounded measurable real multiplier preserves membership
in every Lp space. This statement does not require a finite measure. -/
theorem memLp_mul_of_ae_abs_le {p : ℝ≥0∞} {a v : α → ℝ} {D : ℝ}
    (ha : AEStronglyMeasurable a μ) (hD : ∀ᵐ x ∂μ, |a x| ≤ D)
    (hv : MemLp v p μ) : MemLp (fun x ↦ a x * v x) p μ := by
  apply hv.of_le_mul (c := D) (ha.mul hv.aestronglyMeasurable)
  filter_upwards [hD] with x hx
  change ‖a x * v x‖ ≤ D * ‖v x‖
  rw [norm_mul, Real.norm_eq_abs (a x)]
  exact mul_le_mul_of_nonneg_right hx (norm_nonneg _)

private theorem norm_L2_sq_eq_integral_sq (v : Lp ℝ 2 μ) :
    ‖v‖ ^ 2 = ∫ x, (v x) ^ 2 ∂μ := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  simp only [Real.inner_apply, pow_two]

private theorem inner_toLp_left {f : α → ℝ} (hf : MemLp f 2 μ)
    (v : Lp ℝ 2 μ) :
    inner ℝ (hf.toLp f) v = ∫ x, f x * v x ∂μ := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hf.coeFn_toLp] with x hx
  simp only [Real.inner_apply, hx]

/-- A weakly convergent raw L2 sequence with a common square-integral bound
can be tested against a strongly convergent sequence of L2 tests. -/
theorem tendsto_integral_mul_of_weak_L2_strong_L2
    {u : ℕ → α → ℝ} {u0 : α → ℝ} {B : ℝ}
    (hu : ∀ n, MemLp (u n) 2 μ) (hu0 : MemLp u0 2 μ)
    (hB : ∀ n, (∫ x, (u n x) ^ 2 ∂μ) ≤ B)
    (hweak : ∀ w : Lp ℝ 2 μ,
      Tendsto (fun n ↦ ∫ x, u n x * w x ∂μ) atTop
        (𝓝 (∫ x, u0 x * w x ∂μ)))
    {v : ℕ → Lp ℝ 2 μ} {v0 : Lp ℝ 2 μ}
    (hv : Tendsto v atTop (𝓝 v0)) :
    Tendsto (fun n ↦ ∫ x, u n x * v n x ∂μ) atTop
      (𝓝 (∫ x, u0 x * v0 x ∂μ)) := by
  let U : ℕ → Lp ℝ 2 μ := fun n ↦ (hu n).toLp (u n)
  let U0 : Lp ℝ 2 μ := hu0.toLp u0
  have hsq : ∀ n, ‖U n‖ ^ 2 = ∫ x, (u n x) ^ 2 ∂μ := by
    intro n
    rw [norm_L2_sq_eq_integral_sq]
    apply integral_congr_ae
    filter_upwards [(hu n).coeFn_toLp] with x hx
    exact congrArg (fun t : ℝ ↦ t ^ 2) hx
  have hnorm : ∀ n, ‖U n‖ ≤ B + 1 := by
    intro n
    have hn : ‖U n‖ ^ 2 ≤ B := (hsq n).trans_le (hB n)
    nlinarith [sq_nonneg (‖U n‖ - 1), sq_nonneg ‖U n‖]
  have hw : ∀ w : Lp ℝ 2 μ,
      Tendsto (fun n ↦ inner ℝ (U n) w) atTop
        (𝓝 (inner ℝ U0 w)) := by
    intro w
    simpa only [U, U0, inner_toLp_left] using hweak w
  have hdist : Tendsto (fun n ↦ ‖v n - v0‖) atTop (𝓝 0) := by
    have hsub : Tendsto (fun n ↦ v n - v0) atTop (𝓝 (v0 - v0)) :=
      hv.sub tendsto_const_nhds
    simpa only [sub_self, norm_zero] using hsub.norm
  have herr : Tendsto (fun n ↦ inner ℝ (U n) (v n - v0)) atTop (𝓝 0) := by
    apply squeeze_zero_norm (a := fun n ↦ (B + 1) * ‖v n - v0‖)
    · intro n
      exact (norm_inner_le_norm _ _).trans
        (mul_le_mul_of_nonneg_right (hnorm n) (norm_nonneg _))
    · simpa only [mul_zero] using hdist.const_mul (B + 1)
  have hresult := herr.add (hw v0)
  simpa only [inner_sub_right, sub_add_cancel, zero_add, U, U0,
    inner_toLp_left] using hresult

/-- Uniformly essentially bounded multipliers that converge almost
everywhere multiply each fixed L2 test strongly in L2. -/
theorem tendsto_L2_mul_of_ae_tendsto
    {a : ℕ → α → ℝ} {a0 : α → ℝ} {D : ℝ}
    (ha : ∀ n, AEStronglyMeasurable (a n) μ)
    (ha0 : AEStronglyMeasurable a0 μ)
    (hD : ∀ n, ∀ᵐ x ∂μ, |a n x| ≤ D)
    (hD0 : ∀ᵐ x ∂μ, |a0 x| ≤ D)
    (hconv : ∀ᵐ x ∂μ, Tendsto (fun n ↦ a n x) atTop (𝓝 (a0 x)))
    (v : Lp ℝ 2 μ) :
    Tendsto
      (fun n ↦ (memLp_mul_of_ae_abs_le (ha n) (hD n) (Lp.memLp v)).toLp
        (fun x ↦ a n x * v x)) atTop
      (𝓝 ((memLp_mul_of_ae_abs_le ha0 hD0 (Lp.memLp v)).toLp
        (fun x ↦ a0 x * v x))) := by
  let V : ℕ → Lp ℝ 2 μ := fun n ↦
    (memLp_mul_of_ae_abs_le (ha n) (hD n) (Lp.memLp v)).toLp
      (fun x ↦ a n x * v x)
  let V0 : Lp ℝ 2 μ :=
    (memLp_mul_of_ae_abs_le ha0 hD0 (Lp.memLp v)).toLp
      (fun x ↦ a0 x * v x)
  have hV : ∀ n, ⇑(V n) =ᵐ[μ] fun x ↦ a n x * v x := fun n ↦
    (memLp_mul_of_ae_abs_le (ha n) (hD n) (Lp.memLp v)).coeFn_toLp
  have hV0 : ⇑V0 =ᵐ[μ] fun x ↦ a0 x * v x :=
    (memLp_mul_of_ae_abs_le ha0 hD0 (Lp.memLp v)).coeFn_toLp
  let C : ℝ := max D 0
  have hDC : D ≤ C := le_max_left D 0
  have hbound : ∀ n, ∀ᵐ x ∂μ,
      ‖(a n x * v x - a0 x * v x) ^ 2‖ ≤ (2 * C) ^ 2 * (v x) ^ 2 := by
    intro n
    filter_upwards [hD n, hD0] with x hx hx0
    have hdiff : |a n x * v x - a0 x * v x| ≤ 2 * C * |v x| := by
      calc
        |a n x * v x - a0 x * v x| ≤
            |a n x * v x| + |a0 x * v x| := abs_sub _ _
        _ = |a n x| * |v x| + |a0 x| * |v x| := by rw [abs_mul, abs_mul]
        _ ≤ C * |v x| + C * |v x| :=
          add_le_add (mul_le_mul_of_nonneg_right (hx.trans hDC) (abs_nonneg _))
            (mul_le_mul_of_nonneg_right (hx0.trans hDC) (abs_nonneg _))
        _ = 2 * C * |v x| := by ring
    have hsq := mul_self_le_mul_self (abs_nonneg _) hdiff
    calc
      ‖(a n x * v x - a0 x * v x) ^ 2‖ =
          |a n x * v x - a0 x * v x| ^ 2 := by rw [Real.norm_eq_abs, abs_pow]
      _ ≤ (2 * C * |v x|) ^ 2 := by simpa only [pow_two] using hsq
      _ = (2 * C) ^ 2 * (v x) ^ 2 := by rw [mul_pow, sq_abs]
  have hlimit : ∀ᵐ x ∂μ,
      Tendsto (fun n ↦ (a n x * v x - a0 x * v x) ^ 2) atTop (𝓝 (0 : ℝ)) := by
    filter_upwards [hconv] with x hx
    have hsub : Tendsto (fun n ↦ a n x * v x - a0 x * v x) atTop
        (𝓝 (a0 x * v x - a0 x * v x)) :=
      (hx.mul_const (v x)).sub tendsto_const_nhds
    simpa only [sub_self, zero_pow (by decide : (2 : ℕ) ≠ 0)] using
      hsub.pow 2
  have hint : Tendsto
      (fun n ↦ ∫ x, (a n x * v x - a0 x * v x) ^ 2 ∂μ) atTop (𝓝 0) := by
    have ht := tendsto_integral_of_dominated_convergence
      (fun x ↦ (2 * C) ^ 2 * (v x) ^ 2)
      (fun n ↦ (((ha n).mul (Lp.aestronglyMeasurable v)).sub
        (ha0.mul (Lp.aestronglyMeasurable v))).pow 2)
      ((Lp.memLp v).integrable_sq.const_mul ((2 * C) ^ 2)) hbound hlimit
    simpa only [Pi.mul_apply, Pi.sub_apply, Pi.pow_apply, integral_zero] using ht
  have hnormsq : ∀ n, dist (V n) V0 ^ 2 =
      ∫ x, (a n x * v x - a0 x * v x) ^ 2 ∂μ := by
    intro n
    rw [dist_eq_norm, norm_L2_sq_eq_integral_sq]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_sub (V n) V0, hV n, hV0] with x hx hn h0
    simp only [hx, Pi.sub_apply, hn, h0]
  change Tendsto V atTop (𝓝 V0)
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  filter_upwards [(Metric.tendsto_nhds.mp hint) (ε ^ 2) (sq_pos_of_pos hε)] with n hn
  have hsq : dist (V n) V0 ^ 2 < ε ^ 2 := by
    rw [hnormsq]
    exact (le_abs_self _).trans_lt (by simpa only [Real.dist_eq, sub_zero] using hn)
  have hn : 0 ≤ dist (V n) V0 := dist_nonneg
  nlinarith

/-- Bounded almost-everywhere convergent real multipliers preserve genuine
weak L2 convergence. The conclusion also records membership of every
product and of the limiting product in L2. -/
theorem weak_L2_mul_of_ae_tendsto_of_ae_abs_le
    {u : ℕ → α → ℝ} {u0 : α → ℝ} {a : ℕ → α → ℝ} {a0 : α → ℝ}
    {B D : ℝ}
    (hu : ∀ n, MemLp (u n) 2 μ) (hu0 : MemLp u0 2 μ)
    (hB : ∀ n, (∫ x, (u n x) ^ 2 ∂μ) ≤ B)
    (hweak : ∀ v : Lp ℝ 2 μ,
      Tendsto (fun n ↦ ∫ x, u n x * v x ∂μ) atTop
        (𝓝 (∫ x, u0 x * v x ∂μ)))
    (ha : ∀ n, AEStronglyMeasurable (a n) μ)
    (ha0 : AEStronglyMeasurable a0 μ)
    (hD : ∀ n, ∀ᵐ x ∂μ, |a n x| ≤ D)
    (hD0 : ∀ᵐ x ∂μ, |a0 x| ≤ D)
    (hconv : ∀ᵐ x ∂μ, Tendsto (fun n ↦ a n x) atTop (𝓝 (a0 x))) :
    (∀ n, MemLp (fun x ↦ a n x * u n x) 2 μ) ∧
      MemLp (fun x ↦ a0 x * u0 x) 2 μ ∧
      ∀ v : Lp ℝ 2 μ,
        Tendsto (fun n ↦ ∫ x, (a n x * u n x) * v x ∂μ) atTop
          (𝓝 (∫ x, (a0 x * u0 x) * v x ∂μ)) := by
  refine ⟨fun n ↦ memLp_mul_of_ae_abs_le (ha n) (hD n) (hu n),
    memLp_mul_of_ae_abs_le ha0 hD0 hu0, ?_⟩
  intro v
  let V : ℕ → Lp ℝ 2 μ := fun n ↦
    (memLp_mul_of_ae_abs_le (ha n) (hD n) (Lp.memLp v)).toLp
      (fun x ↦ a n x * v x)
  let V0 : Lp ℝ 2 μ :=
    (memLp_mul_of_ae_abs_le ha0 hD0 (Lp.memLp v)).toLp
      (fun x ↦ a0 x * v x)
  have hstrong : Tendsto V atTop (𝓝 V0) :=
    tendsto_L2_mul_of_ae_tendsto ha ha0 hD hD0 hconv v
  have hp := tendsto_integral_mul_of_weak_L2_strong_L2 hu hu0 hB hweak hstrong
  have hpair : ∀ n, (∫ x, u n x * V n x ∂μ) =
      ∫ x, (a n x * u n x) * v x ∂μ := by
    intro n
    apply integral_congr_ae
    filter_upwards
      [(memLp_mul_of_ae_abs_le (ha n) (hD n) (Lp.memLp v)).coeFn_toLp]
      with x hx
    have hx' : V n x = a n x * v x := hx
    rw [hx']
    ring
  have hpair0 : (∫ x, u0 x * V0 x ∂μ) =
      ∫ x, (a0 x * u0 x) * v x ∂μ := by
    apply integral_congr_ae
    filter_upwards
      [(memLp_mul_of_ae_abs_le ha0 hD0 (Lp.memLp v)).coeFn_toLp]
      with x hx
    have hx' : V0 x = a0 x * v x := hx
    rw [hx']
    ring
  simpa only [hpair, hpair0] using hp

end RicciFlowSharpEstimate.Analysis
