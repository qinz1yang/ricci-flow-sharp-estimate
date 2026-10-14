/-
Copyright (c) 2026 Ziyang Qin. All rights reserved.
No license is granted by this file.
Authors: Ziyang Qin
-/
import RicciFlowSharpEstimate.Analysis.FiniteIntervalExtension
import DifferentialGeometry.Analysis.Calculus.Taylor
import DifferentialGeometry.Analysis.Calculus.Derivative.ParametricIntervalIntegral
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# Finite-order Hadamard factors on the real line and a closed interval

Differentiation of a weighted dilation average shifts its integer weight and
differentiates its coefficient. This gives finite-order Hadamard division,
including the value at the root. Closed-interval data first receive a finite
extension of the same order.
-/

noncomputable section

namespace RicciFlowSharpEstimate.Analysis

open Set MeasureTheory
open DifferentialGeometry.Analysis.Calculus
open scoped ContDiff

/-- A weighted average along the segment from a fixed center to the argument. -/
private def weightedDilationAverage (m : ℕ) (f : ℝ → ℝ) (a x : ℝ) : ℝ :=
  ∫ t in (0 : ℝ)..1, t ^ m * f (a + t * (x - a))

private theorem weightedDilationAverage_continuous (m : ℕ) (f : ℝ → ℝ)
    (hf : Continuous f) (a : ℝ) : Continuous (weightedDilationAverage m f a) := by
  unfold weightedDilationAverage
  simp_rw [intervalIntegral.integral_of_le zero_le_one,
    ← MeasureTheory.integral_Icc_eq_integral_Ioc]
  apply continuous_parametric_integral_of_continuous _ isCompact_Icc
  change Continuous (fun z : ℝ × ℝ => z.2 ^ m * f (a + z.2 * (z.1 - a)))
  fun_prop

private theorem weightedDilationAverage_hasDerivAt (m : ℕ) (f : ℝ → ℝ)
    (hf : ContDiff ℝ 1 f) (a x : ℝ) :
    HasDerivAt (weightedDilationAverage m f a)
      (weightedDilationAverage (m + 1) (deriv f) a x) x := by
  have hdc : Continuous (deriv f) := hf.continuous_deriv_one
  have hF : ContinuousOn
      (fun z : ℝ × ℝ => z.1 ^ m * f (a + z.1 * (z.2 - a)))
      (Icc (0 : ℝ) 1 ×ˢ Icc (x - 1) (x + 1)) := by
    apply Continuous.continuousOn
    fun_prop
  have hG : ContinuousOn
      (fun z : ℝ × ℝ => z.1 ^ (m + 1) * deriv f (a + z.1 * (z.2 - a)))
      (Icc (0 : ℝ) 1 ×ˢ Icc (x - 1) (x + 1)) := by
    apply Continuous.continuousOn
    fun_prop
  have hD : ∀ t ∈ Icc (0 : ℝ) 1, ∀ y ∈ Icc (x - 1) (x + 1),
      HasDerivWithinAt (fun z => t ^ m * f (a + t * (z - a)))
        (t ^ (m + 1) * deriv f (a + t * (y - a))) (Icc (x - 1) (x + 1)) y := by
    intro t _ y _
    have hi := (((hasDerivAt_id y).sub_const a).const_mul t).const_add a
    have hcomp := (hf.differentiable (by norm_num) (a + t * (y - a))).hasDerivAt.comp y hi
    have ho := hcomp.const_mul (t ^ m)
    convert ho.hasDerivWithinAt using 1 <;>
      simp only [Function.comp_def, id_eq, mul_one, pow_succ]
    ring
  have hx : x ∈ Icc (x - 1) (x + 1) := ⟨by linarith, by linarith⟩
  have h := hasDerivWithinAt_paramIntervalIntegral_on_interval
    (F := fun t y => t ^ m * f (a + t * (y - a)))
    (G := fun t y => t ^ (m + 1) * deriv f (a + t * (y - a)))
    (p := 0) (q := 1) (s := x - 1) (u := x + 1)
    zero_le_one hF hG hD x hx
  exact h.hasDerivAt (Icc_mem_nhds (by linarith) (by linarith))

/-- Dilation averaging preserves every finite differentiability order. -/
private theorem weightedDilationAverage_contDiff (n m : ℕ) (f : ℝ → ℝ)
    (hf : ContDiff ℝ n f) (a : ℝ) :
    ContDiff ℝ n (weightedDilationAverage m f a) := by
  induction n generalizing m f with
  | zero =>
      exact contDiff_zero.mpr (weightedDilationAverage_continuous m f hf.continuous a)
  | succ n ih =>
      have hfn : ContDiff ℝ ((n : ℕ∞ω) + 1) f := by
        simpa only [Nat.cast_add, Nat.cast_one] using hf
      have hf1 : ContDiff ℝ 1 f := hfn.of_le (by simp)
      have hfd : ContDiff ℝ n (deriv f) := (contDiff_succ_iff_deriv.mp hfn).2.2
      have hd : deriv (weightedDilationAverage m f a) =
          weightedDilationAverage (m + 1) (deriv f) a := by
        funext x
        exact (weightedDilationAverage_hasDerivAt m f hf1 a x).deriv
      change ContDiff ℝ ((n : ℕ∞ω) + 1) (weightedDilationAverage m f a)
      rw [contDiff_succ_iff_deriv]
      refine ⟨fun x => (weightedDilationAverage_hasDerivAt m f hf1 a x).differentiableAt,
        ?_, ?_⟩
      · simp
      · rw [hd]
        exact ih (m + 1) (deriv f) hfd

/-- Division by the centered linear factor loses only one finite derivative. -/
theorem hadamardFactor_contDiff_nat (n : ℕ) (f : ℝ → ℝ)
    (hf : ContDiff ℝ (n + 1 : ℕ) f) (a : ℝ) :
    ContDiff ℝ n (hadamardFactor f a) := by
  have hfn : ContDiff ℝ ((n : ℕ∞ω) + 1) f := by
    simpa only [Nat.cast_add, Nat.cast_one] using hf
  have heq : weightedDilationAverage 0 (deriv f) a = hadamardFactor f a := by
    funext x
    simp only [weightedDilationAverage, hadamardFactor, pow_zero, one_mul]
  rw [← heq]
  exact weightedDilationAverage_contDiff n 0 (deriv f)
    (contDiff_succ_iff_deriv.mp hfn).2.2 a

@[simp]
theorem hadamardFactor_apply_center (f : ℝ → ℝ) (a : ℝ) :
    hadamardFactor f a a = deriv f a := by
  simp [hadamardFactor]

/-- The finite Hadamard factor has the exact producer equation on the whole line. -/
theorem sub_mul_hadamardFactor_of_contDiff_one (f : ℝ → ℝ) (hf : ContDiff ℝ 1 f)
    (a x : ℝ) : (x - a) * hadamardFactor f a x = f x - f a := by
  have hdc : Continuous (deriv f) := hf.continuous_deriv_one
  have hD (t : ℝ) : HasDerivAt (fun s => f (a + s * (x - a)))
      ((x - a) * deriv f (a + t * (x - a))) t := by
    have hi := ((hasDerivAt_id t).mul_const (x - a)).const_add a
    convert (hf.differentiable (by norm_num) _).hasDerivAt.comp t hi using 1 <;>
      simp only [Function.comp_def, id_eq, one_mul]
    ring
  have hint : IntervalIntegrable
      (fun t => (x - a) * deriv f (a + t * (x - a))) volume 0 1 := by
    apply Continuous.intervalIntegrable
    fun_prop
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hD t) hint
  rw [intervalIntegral.integral_const_mul] at h
  simpa [hadamardFactor] using h

/-- Finite-order data vanishing at the left endpoint have a globally C^n
factor whose exact multiplication law holds on the original interval. -/
theorem exists_contDiff_nat_sub_factor_Icc (n : ℕ) (f : ℝ → ℝ)
    (a b : ℝ) (hab : a < b) (hf : ContDiffOn ℝ (n + 1 : ℕ) f (Icc a b))
    (hroot : f a = 0) :
    ∃ q : ℝ → ℝ, ContDiff ℝ n q ∧ ∀ x ∈ Icc a b, f x = (x - a) * q x := by
  obtain ⟨F, hF, hEq⟩ := exists_contDiff_nat_extension_Icc (n + 1) f a b hab hf
  have hF1 : ContDiff ℝ 1 F := hF.of_le (by simp)
  have hFa : F a = 0 := (hEq (left_mem_Icc.mpr hab.le)).trans hroot
  refine ⟨hadamardFactor F a, hadamardFactor_contDiff_nat n F hF a, ?_⟩
  intro x hx
  rw [sub_mul_hadamardFactor_of_contDiff_one F hF1 a x, hFa, sub_zero]
  exact (hEq hx).symm

end RicciFlowSharpEstimate.Analysis
