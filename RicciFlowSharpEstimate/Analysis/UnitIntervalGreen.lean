/-
Copyright (c) 2026 Ziyang Qin. All rights reserved.
No license is granted by this file.
Authors: Ziyang Qin
-/
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Tactic.Ring

/-!
# Dirichlet Green kernels on the unit interval

The continuous Green kernel and its slope kernel recover the two curvature
primitives from their affine moment terms. The slope kernel has value `-s`
on the diagonal. The integral formulas include both endpoints and require only
Lebesgue integrability on the open unit interval.
-/

noncomputable section

namespace RicciFlowSharpEstimate.Analysis

open MeasureTheory Set

/-- The Green kernel for the negative second derivative with zero Dirichlet data
on the unit interval. -/
def unitDirichletKernel (x s : ℝ) : ℝ := min x s - x * s

/-- The slope kernel, with value `-s` chosen on the diagonal. -/
def unitDirichletSlopeKernel (x s : ℝ) : ℝ := if s ≤ x then -s else 1 - s

/-- The Dirichlet Green kernel is jointly continuous. -/
theorem continuous_unitDirichletKernel :
    Continuous (fun v : ℝ × ℝ => unitDirichletKernel v.1 v.2) := by
  change Continuous (fun v : ℝ × ℝ => min v.1 v.2 - v.1 * v.2)
  exact continuous_min.sub (continuous_fst.mul continuous_snd)

/-- The Dirichlet Green kernel is jointly measurable. -/
theorem measurable_unitDirichletKernel :
    Measurable (fun v : ℝ × ℝ => unitDirichletKernel v.1 v.2) :=
  continuous_unitDirichletKernel.measurable

/-- The slope kernel is jointly measurable, including its prescribed diagonal
values. -/
theorem measurable_unitDirichletSlopeKernel :
    Measurable (fun v : ℝ × ℝ => unitDirichletSlopeKernel v.1 v.2) := by
  change Measurable (fun v : ℝ × ℝ => if v.2 ≤ v.1 then -v.2 else 1 - v.2)
  exact Measurable.ite (measurableSet_le measurable_snd measurable_fst)
    measurable_snd.neg (measurable_const.sub measurable_snd)

/-- The Green kernel is bounded by the product of the distances of its first
argument from the two endpoints. -/
theorem abs_unitDirichletKernel_le (x s : ℝ)
    (hx : x ∈ Icc (0 : ℝ) 1) (hs : s ∈ Icc (0 : ℝ) 1) :
    |unitDirichletKernel x s| ≤ x * (1 - x) := by
  by_cases hsx : s ≤ x
  · calc
      |unitDirichletKernel x s| = |s * (1 - x)| := by
        congr 1
        rw [unitDirichletKernel, min_eq_right hsx]
        ring
      _ = s * (1 - x) :=
        abs_of_nonneg (mul_nonneg hs.1 (sub_nonneg.mpr hx.2))
      _ ≤ x * (1 - x) :=
        mul_le_mul_of_nonneg_right hsx (sub_nonneg.mpr hx.2)
  · have hxs : x ≤ s := le_of_not_ge hsx
    calc
      |unitDirichletKernel x s| = |x * (1 - s)| := by
        congr 1
        rw [unitDirichletKernel, min_eq_left hxs]
        ring
      _ = x * (1 - s) :=
        abs_of_nonneg (mul_nonneg hx.1 (sub_nonneg.mpr hs.2))
      _ ≤ x * (1 - x) :=
        mul_le_mul_of_nonneg_left (sub_le_sub_left hxs 1) hx.1

/-- The slope kernel has absolute value at most one when its second argument
lies in the unit interval. -/
theorem abs_unitDirichletSlopeKernel_le_one (x s : ℝ)
    (hs : s ∈ Icc (0 : ℝ) 1) :
    |unitDirichletSlopeKernel x s| ≤ 1 := by
  by_cases hsx : s ≤ x
  · rw [unitDirichletSlopeKernel, ite_eq_left hsx, abs_neg, abs_of_nonneg hs.1]
    exact hs.2
  · rw [unitDirichletSlopeKernel, ite_eq_right hsx,
      abs_of_nonneg (sub_nonneg.mpr hs.2)]
    exact sub_le_self 1 hs.1

private theorem unit_intervalIntegrable_of_integrableOn
    (u : ℝ → ℝ) (hu : IntegrableOn u (Ioo (0 : ℝ) 1)) :
    IntervalIntegrable u volume 0 1 :=
  (intervalIntegrable_iff_integrableOn_Ioo_of_le (by norm_num : (0 : ℝ) ≤ 1)).2 hu

private theorem unit_intervalIntegrable_indicator_Iic
    (u : ℝ → ℝ) (hu : IntervalIntegrable u volume 0 1) (x : ℝ) :
    IntervalIntegrable ((Iic x).indicator u) volume 0 1 :=
  ⟨hu.1.indicator measurableSet_Iic, hu.2.indicator measurableSet_Iic⟩

/-- Integrating the Dirichlet Green kernel recovers the affine moment minus
the triangular curvature primitive, including both endpoints. -/
theorem integral_unitDirichletKernel (u : ℝ → ℝ)
    (hu : IntegrableOn u (Ioo (0 : ℝ) 1))
    (x : ℝ) (hx : x ∈ Icc (0 : ℝ) 1) :
    (∫ s in (0 : ℝ)..1, unitDirichletKernel x s * u s) =
      x * (∫ s in (0 : ℝ)..1, (1 - s) * u s) -
        ∫ s in (0 : ℝ)..x, (x - s) * u s := by
  have hi := unit_intervalIntegrable_of_integrableOn u hu
  have hw : IntervalIntegrable (fun s : ℝ => (1 - s) * u s) volume 0 1 :=
    hi.continuousOn_mul (continuous_const.sub continuous_id).continuousOn
  have ht : IntervalIntegrable (fun s : ℝ => (x - s) * u s) volume 0 1 :=
    hi.continuousOn_mul (continuous_const.sub continuous_id).continuousOn
  have hind := unit_intervalIntegrable_indicator_Iic _ ht x
  calc
    (∫ s in (0 : ℝ)..1, unitDirichletKernel x s * u s) =
        ∫ s in (0 : ℝ)..1,
          x * ((1 - s) * u s) - (Iic x).indicator (fun t => (x - t) * u t) s := by
      apply intervalIntegral.integral_congr
      intro s _
      dsimp only
      by_cases hsx : s ≤ x
      · rw [unitDirichletKernel, min_eq_right hsx, Set.indicator_of_mem (show s ∈ Iic x from hsx)]
        ring
      · rw [unitDirichletKernel, min_eq_left (le_of_not_ge hsx),
          Set.indicator_of_notMem (show s ∉ Iic x from hsx)]
        ring
    _ = _ := by
      rw [intervalIntegral.integral_sub (hw.const_mul x) hind,
        intervalIntegral.integral_const_mul]
      congr 1
      exact intervalIntegral.integral_indicator hx

/-- Integrating the slope kernel recovers the affine moment minus the first
curvature primitive, with the diagonal branch handled by the exact indicator
integral formula. -/
theorem integral_unitDirichletSlopeKernel (u : ℝ → ℝ)
    (hu : IntegrableOn u (Ioo (0 : ℝ) 1))
    (x : ℝ) (hx : x ∈ Icc (0 : ℝ) 1) :
    (∫ s in (0 : ℝ)..1, unitDirichletSlopeKernel x s * u s) =
      (∫ s in (0 : ℝ)..1, (1 - s) * u s) - ∫ s in (0 : ℝ)..x, u s := by
  have hi := unit_intervalIntegrable_of_integrableOn u hu
  have hw : IntervalIntegrable (fun s : ℝ => (1 - s) * u s) volume 0 1 :=
    hi.continuousOn_mul (continuous_const.sub continuous_id).continuousOn
  have hind := unit_intervalIntegrable_indicator_Iic u hi x
  calc
    (∫ s in (0 : ℝ)..1, unitDirichletSlopeKernel x s * u s) =
        ∫ s in (0 : ℝ)..1, (1 - s) * u s - (Iic x).indicator u s := by
      apply intervalIntegral.integral_congr
      intro s _
      dsimp only
      by_cases hsx : s ≤ x
      · rw [unitDirichletSlopeKernel, ite_eq_left hsx,
          Set.indicator_of_mem (show s ∈ Iic x from hsx)]
        ring
      · rw [unitDirichletSlopeKernel, ite_eq_right hsx,
          Set.indicator_of_notMem (show s ∉ Iic x from hsx)]
        ring
    _ = _ := by
      rw [intervalIntegral.integral_sub hw hind]
      congr 1
      exact intervalIntegral.integral_indicator hx

end RicciFlowSharpEstimate.Analysis
