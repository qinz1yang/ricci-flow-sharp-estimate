/-
Copyright (c) 2026 Ziyang Qin. All rights reserved.
No license is granted by this file.
Authors: Ziyang Qin
-/
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Almost-everywhere order bounds under weak L2 convergence

Testing a weak limit against its own negative part proves that nonnegativity
is retained almost everywhere. On a finite measure space, subtraction of
scalar multiples of the constant-one L2 function then proves retention of
lower and upper bounds whose scalar values converge.
-/

noncomputable section

namespace RicciFlowSharpEstimate.Analysis.L2WeakOrder

open Filter MeasureTheory

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

/-- A weak limit of almost-everywhere nonnegative real L2 functions is
almost everywhere nonnegative. No finiteness assumption on the measure is
needed for this cone-closure statement. -/
theorem ae_nonneg_of_tendsto_inner (u : ℕ → Lp ℝ 2 μ) (f : Lp ℝ 2 μ)
    (hpos : ∀ n, ∀ᵐ x ∂μ, 0 ≤ u n x)
    (hweak : ∀ g : Lp ℝ 2 μ,
      Tendsto (fun n ↦ inner ℝ (u n) g) atTop (nhds (inner ℝ f g))) :
    ∀ᵐ x ∂μ, 0 ≤ f x := by
  have hpair : ∀ n, 0 ≤ inner ℝ (u n) (Lp.negPart f) := by
    intro n
    rw [L2.inner_def]
    apply integral_nonneg_of_ae
    filter_upwards [hpos n, Lp.coeFn_negPart_eq_max f] with x hx hneg
    rw [Real.inner_apply, hneg]
    exact mul_nonneg hx (le_max_right _ _)
  have hlimit : 0 ≤ inner ℝ f (Lp.negPart f) :=
    ge_of_tendsto' (hweak (Lp.negPart f)) hpair
  have hidentity : inner ℝ f (Lp.negPart f) =
      -(inner ℝ (Lp.negPart f) (Lp.negPart f)) := by
    rw [L2.inner_def, L2.inner_def, ← integral_neg]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_negPart_eq_max f] with x hneg
    rw [Real.inner_apply, Real.inner_apply, hneg]
    by_cases hx : 0 ≤ f x
    · simp only [max_eq_right (neg_nonpos.mpr hx), mul_zero, neg_zero]
    · rw [max_eq_left (neg_nonneg.mpr (lt_of_not_ge hx).le)]
      ring
  have hself : 0 ≤ inner ℝ (Lp.negPart f) (Lp.negPart f) :=
    real_inner_self_nonneg
  have hzero : Lp.negPart f = 0 := by
    apply (inner_self_eq_zero (𝕜 := ℝ)).mp
    linarith only [hlimit, hidentity, hself]
  have hzero_ae : ∀ᵐ x ∂μ, Lp.negPart f x = 0 := by
    rw [hzero]
    exact Lp.coeFn_zero ℝ 2 μ
  filter_upwards [Lp.coeFn_negPart_eq_max f, hzero_ae] with x hneg hz
  have hle : -f x ≤ 0 := by
    calc
      -f x ≤ max (-f x) 0 := le_max_left _ _
      _ = Lp.negPart f x := hneg.symm
      _ = 0 := hz
  exact neg_nonpos.mp hle

/-- Weak L2 convergence on a finite measure space preserves a.e. lower and
upper real bounds when the bounding scalar sequences converge. -/
theorem ae_bounds_of_tendsto_inner [IsFiniteMeasure μ]
    (u : ℕ → Lp ℝ 2 μ) (f : Lp ℝ 2 μ)
    (aSeq bSeq : ℕ → ℝ) (a b : ℝ)
    (ha : Tendsto aSeq atTop (nhds a)) (hb : Tendsto bSeq atTop (nhds b))
    (hbox : ∀ n, ∀ᵐ x ∂μ, aSeq n ≤ u n x ∧ u n x ≤ bSeq n)
    (hweak : ∀ g : Lp ℝ 2 μ,
      Tendsto (fun n ↦ inner ℝ (u n) g) atTop (nhds (inner ℝ f g))) :
    ∀ᵐ x ∂μ, a ≤ f x ∧ f x ≤ b := by
  let c : Lp ℝ 2 μ :=
    (memLp_const (μ := μ) (p := 2) (1 : ℝ)).toLp (fun _ : α ↦ 1)
  have hc : ⇑c =ᵐ[μ] fun _ : α ↦ (1 : ℝ) :=
    (memLp_const (μ := μ) (p := 2) (1 : ℝ)).coeFn_toLp
  have hlowSeq : ∀ n, ∀ᵐ x ∂μ, 0 ≤ (u n - aSeq n • c) x := by
    intro n
    filter_upwards [hbox n, Lp.coeFn_sub (u n) (aSeq n • c),
      Lp.coeFn_smul (aSeq n) c, hc] with x hx hsub hsmul hc1
    simpa only [hsub, Pi.sub_apply, hsmul, Pi.smul_apply, smul_eq_mul, hc1, mul_one]
      using (sub_nonneg.mpr hx.1)
  have huppSeq : ∀ n, ∀ᵐ x ∂μ, 0 ≤ (bSeq n • c - u n) x := by
    intro n
    filter_upwards [hbox n, Lp.coeFn_sub (bSeq n • c) (u n),
      Lp.coeFn_smul (bSeq n) c, hc] with x hx hsub hsmul hc1
    simpa only [hsub, Pi.sub_apply, hsmul, Pi.smul_apply, smul_eq_mul, hc1, mul_one]
      using (sub_nonneg.mpr hx.2)
  have hlowWeak : ∀ g : Lp ℝ 2 μ,
      Tendsto (fun n ↦ inner ℝ (u n - aSeq n • c) g) atTop
        (nhds (inner ℝ (f - a • c) g)) := by
    intro g
    simpa only [inner_sub_left, real_inner_smul_left] using
      (hweak g).sub (ha.mul_const (inner ℝ c g))
  have huppWeak : ∀ g : Lp ℝ 2 μ,
      Tendsto (fun n ↦ inner ℝ (bSeq n • c - u n) g) atTop
        (nhds (inner ℝ (b • c - f) g)) := by
    intro g
    simpa only [inner_sub_left, real_inner_smul_left] using
      (hb.mul_const (inner ℝ c g)).sub (hweak g)
  have hlow := ae_nonneg_of_tendsto_inner
    (fun n ↦ u n - aSeq n • c) (f - a • c) hlowSeq hlowWeak
  have hupp := ae_nonneg_of_tendsto_inner
    (fun n ↦ bSeq n • c - u n) (b • c - f) huppSeq huppWeak
  filter_upwards [hlow, hupp, Lp.coeFn_sub f (a • c), Lp.coeFn_sub (b • c) f,
    Lp.coeFn_smul a c, Lp.coeFn_smul b c, hc]
    with x hl hu hsuba hsubb hsmula hsmulb hc1
  have hl' : 0 ≤ f x - a := by
    simpa only [hsuba, Pi.sub_apply, hsmula, Pi.smul_apply, smul_eq_mul, hc1, mul_one]
      using hl
  have hu' : 0 ≤ b - f x := by
    simpa only [hsubb, Pi.sub_apply, hsmulb, Pi.smul_apply, smul_eq_mul, hc1, mul_one]
      using hu
  exact ⟨sub_nonneg.mp hl', sub_nonneg.mp hu'⟩

end RicciFlowSharpEstimate.Analysis.L2WeakOrder
