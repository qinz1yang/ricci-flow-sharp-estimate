/-
Copyright (c) 2026 Ziyang Qin. All rights reserved.
No license is granted by this file.
Authors: Ziyang Qin
-/
import RicciFlowSharpEstimate.Geometry.AreaActionVariation
import RicciFlowSharpEstimate.Geometry.AreaActionBridge

/-!
# Original-metric realization of the area Euler pairing

The fixed-geometry first variation retains the same actual sphere metric, smooth
one-forms, area/height coordinate equations and canonical angular factor.
-/

noncomputable section

namespace RicciFlowSharpEstimate.Geometry.AreaProfile

open MeasureTheory
open scoped ContDiff

/-- The original sphere action is paired with the Euler operator for the same
physical curvature, metric and probe, with all coordinate equations retained. -/
theorem oneFormDissipation_eq_integral_jacobi_of_profile_probe (K r : ℝ → ℝ)
    (hK : ContDiff ℝ ∞ K) (hr : ContDiff ℝ ∞ r)
    (hpos : ∀ x ∈ Set.Icc (0 : ℝ) 1, 0 < K x)
    (hzero : (∫ x in (0 : ℝ)..1, K x) = 2)
    (hone : (∫ x in (0 : ℝ)..1, x * K x) = 1) (D : RotationalProfile.PoleData)
    (R : ℝ → ℝ) (hR : ContDiff ℝ ∞ R)
    (ha : ∀ x ∈ Set.Icc (0 : ℝ) 1, D.a (heightCoordinate K x) = 1 / K x)
    (hprobe : ∀ x ∈ Set.Icc (0 : ℝ) 1, R (heightCoordinate K x) = r x) :
    oneFormDissipation D.metric (D.meridionalOneForm R hR) =
      2 * Real.pi * ∫ x in (0 : ℝ)..1, warp K x * r x * meridionalJacobiOperator K r x := by
  rw [oneFormDissipation_eq_areaAction_of_profile_probe K r hK hr hpos hzero D R hR ha hprobe,
    meridionalAction_eq_integral_jacobi K r hK hr hzero hone]

/-- The full original geometric dissipation has the same first variation under
a variation of the smooth form on the fixed original metric. -/
theorem oneFormDissipation_meridional_hasDerivAt (K r s : ℝ → ℝ)
    (hK : ContDiff ℝ ∞ K) (hr : ContDiff ℝ ∞ r) (hs : ContDiff ℝ ∞ s)
    (hpos : ∀ x ∈ Set.Icc (0 : ℝ) 1, 0 < K x)
    (hzero : (∫ x in (0 : ℝ)..1, K x) = 2)
    (hone : (∫ x in (0 : ℝ)..1, x * K x) = 1) (D : RotationalProfile.PoleData)
    (R S : ℝ → ℝ) (hR : ContDiff ℝ ∞ R) (hS : ContDiff ℝ ∞ S)
    (ha : ∀ x ∈ Set.Icc (0 : ℝ) 1, D.a (heightCoordinate K x) = 1 / K x)
    (hprobeR : ∀ x ∈ Set.Icc (0 : ℝ) 1, R (heightCoordinate K x) = r x)
    (hprobeS : ∀ x ∈ Set.Icc (0 : ℝ) 1, S (heightCoordinate K x) = s x) :
    HasDerivAt (fun t => oneFormDissipation D.metric
      (D.meridionalOneForm (fun v => R v + t * S v) (hR.add (contDiff_const.mul hS))))
      (4 * Real.pi * ∫ x in (0 : ℝ)..1, warp K x * s x * meridionalJacobiOperator K r x) 0 := by
  have heq : (fun t => oneFormDissipation D.metric
      (D.meridionalOneForm (fun v => R v + t * S v) (hR.add (contDiff_const.mul hS)))) =
      fun t => 2 * Real.pi * meridionalAction K (fun x => r x + t * s x) := by
    funext t
    apply oneFormDissipation_eq_areaAction_of_profile_probe K _ hK
      (hr.add (contDiff_const.mul hs)) hpos hzero D _ (hR.add (contDiff_const.mul hS)) ha
    intro x hx
    rw [hprobeR x hx, hprobeS x hx]
  rw [heq]
  convert (meridionalAction_hasDerivAt K r s hK hr hs hzero hone).const_mul
    (2 * Real.pi) using 1
  ring

end RicciFlowSharpEstimate.Geometry.AreaProfile
