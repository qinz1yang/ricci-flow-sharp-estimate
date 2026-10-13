/-
Copyright (c) 2026 Ziyang Qin. All rights reserved.
No license is granted by this file.
Authors: Ziyang Qin
-/
import RicciFlowSharpEstimate.Geometry.AreaProfile
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.ContDiff.Deriv

/-!
# Convex mixtures of smooth area curvature and probe data

Finite convex mixtures preserve both curvature moments and the original
ratio through mixtures of the actual box witnesses. Probe derivatives are
the actual derivatives of the same smooth finite mixture. Unit physical
mass is a separate nonlinear constraint and is not asserted here.
-/

noncomputable section

namespace RicciFlowSharpEstimate.Geometry.AreaProfile

open Set MeasureTheory
open scoped ContDiff BigOperators

/-- A finite convex mixture of smooth pairs retains the curvature box,
its actual ratio witnesses, both exact moments, and both actual probe jets. -/
theorem smooth_area_pair_convexCombination
    {ι : Type*} (s : Finset ι) (w : ι → ℝ) (K r : ι → ℝ → ℝ)
    (κ Λ : ι → ℝ) (C : ℝ)
    (hw : ∀ i ∈ s, 0 ≤ w i) (hsum : (∑ i ∈ s, w i) = 1)
    (hK : ∀ i ∈ s, ContDiff ℝ ∞ (K i)) (hr : ∀ i ∈ s, ContDiff ℝ ∞ (r i))
    (hκ : ∀ i ∈ s, 0 < κ i)
    (hbox : ∀ i ∈ s, ∀ x ∈ Icc (0 : ℝ) 1, κ i ≤ K i x ∧ K i x ≤ Λ i)
    (hratio : ∀ i ∈ s, Λ i / κ i ≤ C)
    (hzero : ∀ i ∈ s, (∫ x in (0 : ℝ)..1, K i x) = 2)
    (hone : ∀ i ∈ s, (∫ x in (0 : ℝ)..1, x * K i x) = 1) :
    ContDiff ℝ ∞ (fun x => ∑ i ∈ s, w i * K i x) ∧
    ContDiff ℝ ∞ (fun x => ∑ i ∈ s, w i * r i x) ∧
    (deriv (fun x => ∑ i ∈ s, w i * r i x) = fun x => ∑ i ∈ s, w i * deriv (r i) x) ∧
    (deriv (deriv (fun x => ∑ i ∈ s, w i * r i x)) =
      fun x => ∑ i ∈ s, w i * deriv (deriv (r i)) x) ∧
    0 < (∑ i ∈ s, w i * κ i) ∧
    (∀ x ∈ Icc (0 : ℝ) 1,
      (∑ i ∈ s, w i * κ i) ≤ (∑ i ∈ s, w i * K i x) ∧
      (∑ i ∈ s, w i * K i x) ≤ (∑ i ∈ s, w i * Λ i)) ∧
    (∑ i ∈ s, w i * Λ i) / (∑ i ∈ s, w i * κ i) ≤ C ∧
    (∫ x in (0 : ℝ)..1, ∑ i ∈ s, w i * K i x) = 2 ∧
    (∫ x in (0 : ℝ)..1, x * (∑ i ∈ s, w i * K i x)) = 1 := by
  classical
  have hposw : ∃ i ∈ s, 0 < w i := by
    by_contra h
    push Not at h
    have hz := Finset.sum_nonpos (fun i hi => h i hi)
    rw [hsum] at hz
    norm_num at hz
  have hkpos : 0 < ∑ i ∈ s, w i * κ i := by
    obtain ⟨i, hi, hwi⟩ := hposw
    exact Finset.sum_pos' (fun j hj => mul_nonneg (hw j hj) (hκ j hj).le)
      ⟨i, hi, mul_pos hwi (hκ i hi)⟩
  have hR1 : deriv (fun x => ∑ i ∈ s, w i * r i x) =
      fun x => ∑ i ∈ s, w i * deriv (r i) x := by
    funext x
    exact (HasDerivAt.fun_sum (fun i hi =>
      ((hr i hi).differentiable (by simp)).differentiableAt.hasDerivAt.const_mul (w i))).deriv
  have hR2 : deriv (deriv (fun x => ∑ i ∈ s, w i * r i x)) =
      fun x => ∑ i ∈ s, w i * deriv (deriv (r i)) x := by
    rw [hR1]
    funext x
    have hd (i : ι) (hi : i ∈ s) : HasDerivAt
        (fun y => w i * deriv (r i) y) (w i * deriv (deriv (r i)) x) x := by
      have hc : ContDiff ℝ ∞ (deriv (r i)) := (contDiff_infty_iff_deriv.mp (hr i hi)).2
      exact (hc.differentiable (by simp)).differentiableAt.hasDerivAt.const_mul (w i)
    exact (HasDerivAt.fun_sum hd).deriv
  refine ⟨ContDiff.sum (fun i hi => contDiff_const.mul (hK i hi)),
    ContDiff.sum (fun i hi => contDiff_const.mul (hr i hi)), hR1, hR2, hkpos, ?_, ?_, ?_, ?_⟩
  · intro x hx
    exact ⟨Finset.sum_le_sum (fun i hi => mul_le_mul_of_nonneg_left (hbox i hi x hx).1 (hw i hi)),
      Finset.sum_le_sum (fun i hi => mul_le_mul_of_nonneg_left (hbox i hi x hx).2 (hw i hi))⟩
  · apply (div_le_iff₀ hkpos).mpr
    calc
      (∑ i ∈ s, w i * Λ i) ≤ ∑ i ∈ s, w i * (C * κ i) :=
        Finset.sum_le_sum (fun i hi => mul_le_mul_of_nonneg_left
          ((div_le_iff₀ (hκ i hi)).mp (hratio i hi)) (hw i hi))
      _ = C * (∑ i ∈ s, w i * κ i) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        ring
  · rw [intervalIntegral.integral_finsetSum
      (fun i hi => ((hK i hi).continuous.const_mul (w i)).intervalIntegrable 0 1)]
    calc
      (∑ i ∈ s, ∫ x in (0 : ℝ)..1, w i * K i x) = ∑ i ∈ s, w i * 2 := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [intervalIntegral.integral_const_mul, hzero i hi]
      _ = 2 := by rw [← Finset.sum_mul, hsum, one_mul]
  · have heq : (fun x => x * (∑ i ∈ s, w i * K i x)) =
        fun x => ∑ i ∈ s, w i * (x * K i x) := by
      funext x
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring
    have hiInt (i : ι) (hi : i ∈ s) :
        IntervalIntegrable (fun x : ℝ => w i * (x * K i x)) volume 0 1 :=
      ((continuous_id.mul (hK i hi).continuous).const_mul (w i)).intervalIntegrable 0 1
    rw [heq, intervalIntegral.integral_finsetSum hiInt]
    calc
      (∑ i ∈ s, ∫ x in (0 : ℝ)..1, w i * (x * K i x)) = ∑ i ∈ s, w i := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [intervalIntegral.integral_const_mul, hone i hi, mul_one]
      _ = 1 := hsum

end RicciFlowSharpEstimate.Geometry.AreaProfile
