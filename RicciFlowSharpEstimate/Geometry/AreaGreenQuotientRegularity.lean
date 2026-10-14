/-
Copyright (c) 2026 Ziyang Qin. All rights reserved.
No license is granted by this file.
Authors: Ziyang Qin
-/
import RicciFlowSharpEstimate.Analysis.FiniteSimplePoleQuotient
import RicciFlowSharpEstimate.Analysis.UnitIntervalGreenRegularity
import RicciFlowSharpEstimate.Geometry.AreaProfileCalculus

/-!
# Finite-order regularity of division by the physical area warp

The quotient of the Dirichlet Green primitive by the actual warp has canonical
pole values. For a C^n source on the closed interval, the quotient is C^(n+1)
there. This is the regularity gain needed to bootstrap a continuous fixed point.
-/

noncomputable section

namespace RicciFlowSharpEstimate.Geometry.AreaProfile

open Set MeasureTheory
open scoped ContDiff

/-- The Dirichlet Green quotient with its continuous values at the two poles. -/
def areaGreenQuotient (K h : ℝ → ℝ) (x : ℝ) : ℝ :=
  if x = 0 then (∫ t in (0 : ℝ)..1, (1 - t) * h t) / 2
  else if x = 1 then (∫ t in (0 : ℝ)..1, t * h t) / 2
  else (∫ t in (0 : ℝ)..1, Analysis.unitDirichletKernel x t * h t) / warp K x

/-- The physical Green quotient gains one finite derivative through both
endpoints, starting from merely continuous closed-interval source data. -/
theorem areaGreenQuotient_contDiffOn_succ (n : ℕ) (K h : ℝ → ℝ)
    (hK : ContDiff ℝ ∞ K) (hpos : ∀ x ∈ Icc (0 : ℝ) 1, 0 < K x)
    (hzero : (∫ x in (0 : ℝ)..1, K x) = 2)
    (hone : (∫ x in (0 : ℝ)..1, x * K x) = 1)
    (hh : ContDiffOn ℝ n h (Icc (0 : ℝ) 1)) :
    ContDiffOn ℝ (n + 1 : ℕ) (areaGreenQuotient K h) (Icc (0 : ℝ) 1) := by
  obtain ⟨H, hH, hEq⟩ := Analysis.exists_contDiff_nat_extension_Icc n h 0 1 zero_lt_one hh
  have hA : (∫ t in (0 : ℝ)..1, (1 - t) * H t) =
      ∫ t in (0 : ℝ)..1, (1 - t) * h t := by
    apply intervalIntegral.integral_congr
    intro t ht
    have ht' : t ∈ Icc (0 : ℝ) 1 := by
      simpa only [uIcc_of_le zero_le_one] using ht
    dsimp only
    rw [hEq ht']
  have hB : (∫ t in (0 : ℝ)..1, t * H t) =
      ∫ t in (0 : ℝ)..1, t * h t := by
    apply intervalIntegral.integral_congr
    intro t ht
    have ht' : t ∈ Icc (0 : ℝ) 1 := by
      simpa only [uIcc_of_le zero_le_one] using ht
    dsimp only
    rw [hEq ht']
  have hHInt : IntegrableOn H (Ioo (0 : ℝ) 1) :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le zero_le_one).mp
      (hH.continuous.intervalIntegrable 0 1)
  have hpGreen (x : ℝ) (hx : x ∈ Icc (0 : ℝ) 1) :
      Analysis.unitDirichletPrimitive H x =
        ∫ t in (0 : ℝ)..1, Analysis.unitDirichletKernel x t * h t := by
    rw [Analysis.unitDirichletPrimitive_eq_integral H hHInt x hx]
    apply intervalIntegral.integral_congr
    intro t ht
    have ht' : t ∈ Icc (0 : ℝ) 1 := by
      simpa only [uIcc_of_le zero_le_one] using ht
    dsimp only
    rw [hEq ht']
  apply Analysis.contDiffOn_quotient_of_simple_endpoint_zeros (n + 1) 0 1 zero_lt_one
    (Analysis.unitDirichletPrimitive H) (warp K) (areaGreenQuotient K h)
  · simpa only [Nat.add_assoc] using Analysis.unitDirichletPrimitive_contDiff n H hH
  · exact (warp_contDiff K hK).of_le (by simp)
  · exact Analysis.unitDirichletPrimitive_zero H
  · exact Analysis.unitDirichletPrimitive_one H
  · exact warp_zero K
  · exact warp_one K hK.continuous hzero hone
  · rw [deriv_warp K hK.continuous, warpSlope_zero]
    norm_num
  · rw [deriv_warp K hK.continuous, warpSlope_one K hzero]
    norm_num
  · intro x hx
    exact (warp_pos_of_moments K hK.continuous hpos hzero hone x hx).ne'
  · simp [areaGreenQuotient, deriv_warp K hK.continuous,
      warpSlope_zero, Analysis.deriv_unitDirichletPrimitive_zero H hH.continuous, hA]
  · norm_num [areaGreenQuotient,
      deriv_warp K hK.continuous, warpSlope_one K hzero,
      Analysis.deriv_unitDirichletPrimitive_one H hH.continuous, hB, neg_div_neg_eq]
  · intro x hx
    have hx0 : x ≠ 0 := ne_of_gt hx.1
    have hx1 : x ≠ 1 := ne_of_lt hx.2
    simp only [areaGreenQuotient, ite_eq_right hx0, ite_eq_right hx1]
    rw [hpGreen x ⟨hx.1.le, hx.2.le⟩]

end RicciFlowSharpEstimate.Geometry.AreaProfile
