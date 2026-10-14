/-
Copyright (c) 2026 Ziyang Qin. All rights reserved.
No license is granted by this file.
Authors: Ziyang Qin
-/
import RicciFlowSharpEstimate.Analysis.FiniteIntervalExtension
import RicciFlowSharpEstimate.Analysis.SecondPrimitive
import RicciFlowSharpEstimate.Analysis.UnitIntervalGreen

/-!
# Finite regularity of the unit-interval Dirichlet primitive

The affine-minus-triangular formula defines the Green primitive globally and
gains two derivatives. It vanishes at both physical endpoints.
-/

noncomputable section

namespace RicciFlowSharpEstimate.Analysis

open Set MeasureTheory
open scoped ContDiff

/-- The affine-minus-triangular formula for the Dirichlet Green primitive. -/
def unitDirichletPrimitive (h : ℝ → ℝ) (x : ℝ) : ℝ :=
  x * (∫ t in (0 : ℝ)..1, (1 - t) * h t) -
    ∫ t in (0 : ℝ)..x, (x - t) * h t

theorem unitDirichletPrimitive_hasDerivAt (h : ℝ → ℝ) (hh : Continuous h) (x : ℝ) :
    HasDerivAt (unitDirichletPrimitive h)
      ((∫ t in (0 : ℝ)..1, (1 - t) * h t) - ∫ t in (0 : ℝ)..x, h t) x := by
  change HasDerivAt
    (fun y => y * (∫ t in (0 : ℝ)..1, (1 - t) * h t) -
      ∫ t in (0 : ℝ)..y, (y - t) * h t)
    ((∫ t in (0 : ℝ)..1, (1 - t) * h t) - ∫ t in (0 : ℝ)..x, h t) x
  simpa only [Pi.sub_def, id_eq, one_mul] using
    ((hasDerivAt_id x).mul_const (∫ t in (0 : ℝ)..1, (1 - t) * h t)).sub
      (SecondPrimitive.integral_kernel_hasDerivAt h hh 0 x)

theorem unitDirichletPrimitive_contDiff (n : ℕ) (h : ℝ → ℝ)
    (hh : ContDiff ℝ n h) : ContDiff ℝ (n + 2 : ℕ) (unitDirichletPrimitive h) := by
  have hd : deriv (unitDirichletPrimitive h) =
      fun x => (∫ t in (0 : ℝ)..1, (1 - t) * h t) - ∫ t in (0 : ℝ)..x, h t := by
    funext x
    exact (unitDirichletPrimitive_hasDerivAt h hh.continuous x).deriv
  change ContDiff ℝ (((n + 1 : ℕ) : ℕ∞ω) + 1) (unitDirichletPrimitive h)
  rw [contDiff_succ_iff_deriv]
  refine ⟨fun x => (unitDirichletPrimitive_hasDerivAt h hh.continuous x).differentiableAt,
    ?_, ?_⟩
  · simp
  · rw [hd]
    exact contDiff_const.sub (integral_contDiff_succ n h hh 0)

@[simp]
theorem unitDirichletPrimitive_zero (h : ℝ → ℝ) : unitDirichletPrimitive h 0 = 0 := by
  simp [unitDirichletPrimitive]

@[simp]
theorem unitDirichletPrimitive_one (h : ℝ → ℝ) : unitDirichletPrimitive h 1 = 0 := by
  simp [unitDirichletPrimitive]

theorem deriv_unitDirichletPrimitive_zero (h : ℝ → ℝ) (hh : Continuous h) :
    deriv (unitDirichletPrimitive h) 0 = ∫ t in (0 : ℝ)..1, (1 - t) * h t := by
  simpa using (unitDirichletPrimitive_hasDerivAt h hh 0).deriv

theorem deriv_unitDirichletPrimitive_one (h : ℝ → ℝ) (hh : Continuous h) :
    deriv (unitDirichletPrimitive h) 1 = -(∫ t in (0 : ℝ)..1, t * h t) := by
  rw [(unitDirichletPrimitive_hasDerivAt h hh 1).deriv]
  have hm : (∫ t in (0 : ℝ)..1, (1 - t) * h t) =
      (∫ t in (0 : ℝ)..1, h t) - ∫ t in (0 : ℝ)..1, t * h t := by
    calc
      _ = ∫ t in (0 : ℝ)..1, h t - t * h t := by
        apply intervalIntegral.integral_congr
        intro t _
        ring
      _ = _ := intervalIntegral.integral_sub (hh.intervalIntegrable 0 1)
        ((continuous_id.mul hh).intervalIntegrable 0 1)
  rw [hm]
  ring

/-- On the closed physical interval this global primitive is exactly the
accepted Dirichlet Green integral. -/
theorem unitDirichletPrimitive_eq_integral (h : ℝ → ℝ)
    (hh : IntegrableOn h (Ioo (0 : ℝ) 1)) (x : ℝ) (hx : x ∈ Icc (0 : ℝ) 1) :
    unitDirichletPrimitive h x =
      ∫ t in (0 : ℝ)..1, unitDirichletKernel x t * h t := by
  exact (integral_unitDirichletKernel h hh x hx).symm

end RicciFlowSharpEstimate.Analysis
