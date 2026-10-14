/-
Copyright (c) 2026 Ziyang Qin. All rights reserved.
No license is granted by this file.
Authors: Ziyang Qin
-/
import RicciFlowSharpEstimate.Analysis.FiniteHadamardFactor
import Mathlib.Analysis.Calculus.ContDiff.Operations

/-!
# Finite regularity of a quotient at two distinct simple poles

Each endpoint is treated with its own Hadamard factor. Consequently, division
at two distinct endpoints loses only one derivative, not two.
-/

noncomputable section

namespace RicciFlowSharpEstimate.Analysis

open Set Filter
open DifferentialGeometry.Analysis.Calculus
open scoped ContDiff Topology

private theorem div_eq_hadamardFactor_div (p f : ℝ → ℝ)
    (hp : ContDiff ℝ 1 p) (hf : ContDiff ℝ 1 f) (a x : ℝ)
    (hpa : p a = 0) (hfa : f a = 0) (hxa : x ≠ a) :
    p x / f x = hadamardFactor p a x / hadamardFactor f a x := by
  have hpEq : p x = (x - a) * hadamardFactor p a x := by
    rw [sub_mul_hadamardFactor_of_contDiff_one p hp a x, hpa, sub_zero]
  have hfEq : f x = (x - a) * hadamardFactor f a x := by
    rw [sub_mul_hadamardFactor_of_contDiff_one f hf a x, hfa, sub_zero]
  rw [hpEq, hfEq, mul_div_mul_left _ _ (sub_ne_zero.mpr hxa)]

/-- A quotient with the derivative-ratio values at two simple endpoint zeros
is C^n on the closed interval when numerator and denominator are C^(n+1).
There is no assumed continuity or regularity of the quotient. -/
theorem contDiffOn_quotient_of_simple_endpoint_zeros (n : ℕ) (a b : ℝ)
    (hab : a < b) (p f q : ℝ → ℝ)
    (hp : ContDiff ℝ (n + 1 : ℕ) p) (hf : ContDiff ℝ (n + 1 : ℕ) f)
    (hpa : p a = 0) (hpb : p b = 0) (hfa : f a = 0) (hfb : f b = 0)
    (hdfa : deriv f a ≠ 0) (hdfb : deriv f b ≠ 0)
    (hfne : ∀ x ∈ Ioo a b, f x ≠ 0)
    (hqa : q a = deriv p a / deriv f a)
    (hqb : q b = deriv p b / deriv f b)
    (hqi : ∀ x ∈ Ioo a b, q x = p x / f x) :
    ContDiffOn ℝ n q (Icc a b) := by
  have hp1 : ContDiff ℝ 1 p := hp.of_le (by simp)
  have hf1 : ContDiff ℝ 1 f := hf.of_le (by simp)
  have hpn : ContDiff ℝ n p := hp.of_le (by simp)
  have hfn : ContDiff ℝ n f := hf.of_le (by simp)
  intro x hx
  by_cases hxa : x = a
  · subst x
    have hne : hadamardFactor f a a ≠ 0 := by
      simpa only [hadamardFactor_apply_center] using hdfa
    have hreg : ContDiffAt ℝ n
        (fun y => hadamardFactor p a y / hadamardFactor f a y) a :=
      (hadamardFactor_contDiff_nat n p hp a).contDiffAt.div
        (hadamardFactor_contDiff_nat n f hf a).contDiffAt hne
    apply hreg.contDiffWithinAt.congr_of_eventuallyEq
    · have hnb : ∀ᶠ y in 𝓝[Icc a b] a, y < b :=
        mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds hab)
      filter_upwards [self_mem_nhdsWithin, hnb] with y hy hyb
      by_cases hya : y = a
      · subst y
        simpa only [hadamardFactor_apply_center] using hqa
      · rw [hqi y ⟨lt_of_le_of_ne hy.1 (Ne.symm hya), hyb⟩]
        exact div_eq_hadamardFactor_div p f hp1 hf1 a y hpa hfa hya
    · simpa only [hadamardFactor_apply_center] using hqa
  by_cases hxb : x = b
  · subst x
    have hne : hadamardFactor f b b ≠ 0 := by
      simpa only [hadamardFactor_apply_center] using hdfb
    have hreg : ContDiffAt ℝ n
        (fun y => hadamardFactor p b y / hadamardFactor f b y) b :=
      (hadamardFactor_contDiff_nat n p hp b).contDiffAt.div
        (hadamardFactor_contDiff_nat n f hf b).contDiffAt hne
    apply hreg.contDiffWithinAt.congr_of_eventuallyEq
    · have hna : ∀ᶠ y in 𝓝[Icc a b] b, a < y :=
        mem_nhdsWithin_of_mem_nhds (Ioi_mem_nhds hab)
      filter_upwards [self_mem_nhdsWithin, hna] with y hy hay
      by_cases hyb : y = b
      · subst y
        simpa only [hadamardFactor_apply_center] using hqb
      · rw [hqi y ⟨hay, lt_of_le_of_ne hy.2 hyb⟩]
        exact div_eq_hadamardFactor_div p f hp1 hf1 b y hpb hfb hyb
    · simpa only [hadamardFactor_apply_center] using hqb
  have hxi : x ∈ Ioo a b :=
    ⟨lt_of_le_of_ne hx.1 (Ne.symm hxa), lt_of_le_of_ne hx.2 hxb⟩
  have hreg : ContDiffAt ℝ n (fun y => p y / f y) x :=
    hpn.contDiffAt.div hfn.contDiffAt (hfne x hxi)
  apply hreg.contDiffWithinAt.congr_of_eventuallyEq
  · have hni : ∀ᶠ y in 𝓝[Icc a b] x, y ∈ Ioo a b :=
      mem_nhdsWithin_of_mem_nhds (Ioo_mem_nhds hxi.1 hxi.2)
    filter_upwards [hni] with y hy using hqi y hy
  · exact hqi x hxi

end RicciFlowSharpEstimate.Analysis
