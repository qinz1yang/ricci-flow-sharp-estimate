/-
Copyright (c) 2026 Ziyang Qin. All rights reserved.
No license is granted by this file.
Authors: Ziyang Qin
-/
import RicciFlowSharpEstimate.Geometry.RotationalZonalReduction
import RicciFlowSharpEstimate.Geometry.HemispherePairFunctional

/-!
# The original constant-probe zonal action

Both constants multiply the same actual meridional action coefficient. The
calculation retains the original warping integral and the geometric `2*pi` factor.
-/

noncomputable section

namespace RicciFlowSharpEstimate.Geometry.RotationalProfile.PoleData

open Set MeasureTheory intervalIntegral
open scoped ContDiff

/-- The complete scalar density for a constant probe, with its actual derivative terms. -/
theorem meridionalDensity_const (D : PoleData) (c v : ℝ) :
    D.meridionalDensity (fun _ => c) v =
      (2 * D.meridionalWeight v - 2 * v ^ 2) * c ^ 2 := by
  simp only [meridionalDensity, meridionalOperator, deriv_const', deriv_const,
    mul_zero, add_zero, zero_sub, neg_sq]
  ring

/-- Exact constant-probe action before angular integration. -/
theorem meridionalAction_const (D : PoleData) (c : ℝ) :
    D.meridionalAction (fun _ => c) =
      (2 * (∫ v in (-1 : ℝ)..1, D.meridionalWeight v) - 4 / 3) * c ^ 2 := by
  have hH : IntervalIntegrable D.meridionalWeight volume (-1) 1 :=
    D.meridionalWeight_continuousOn.intervalIntegrable_of_Icc (by norm_num)
  have hv : IntervalIntegrable (fun v : ℝ => v ^ 2) volume (-1) 1 :=
    (continuous_id.pow 2).intervalIntegrable _ _
  unfold meridionalAction
  simp_rw [D.meridionalDensity_const]
  rw [intervalIntegral.integral_mul_const,
    intervalIntegral.integral_sub (hH.const_mul 2) (hv.const_mul 2),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
  norm_num [integral_pow]

/-- The same two constant probes in the genuine complete zonal dissipation. -/
theorem oneFormDissipation_constant_zonal (D : PoleData) (c d : ℝ) :
    oneFormDissipation D.metric
      (D.meridionalOneForm (fun _ => c) contDiff_const +
        D.azimuthalOneForm (fun _ => d) contDiff_const) =
      2 * Real.pi * (2 * (∫ v in (-1 : ℝ)..1, D.meridionalWeight v) - 4 / 3) *
        (c ^ 2 + d ^ 2) := by
  rw [D.oneFormDissipation_zonal, D.meridionalAction_const, D.meridionalAction_const]
  ring

/-- Literal northern and southern pair functionals give the exact geometric
constant-zonal coefficient, with the original sections and angular factor. -/
theorem oneFormDissipation_constant_zonal_eq_pair_sum (D : PoleData)
    (M : ℝ) (hM : 0 < M) (c d : ℝ) :
    oneFormDissipation D.metric
      (D.meridionalOneForm (fun _ => c) contDiff_const +
        D.azimuthalOneForm (fun _ => d) contDiff_const) =
      2 * Real.pi *
        (2 * (Variational.pairFunctional (fun v => Real.log (M / D.a v)) +
          Variational.pairFunctional (fun v => Real.log (M / D.a (-v)))) - 4 / 3) *
        (c ^ 2 + d ^ 2) := by
  rw [D.oneFormDissipation_constant_zonal, D.integral_meridionalWeight_eq_pairFunctional_sum M hM]

end RicciFlowSharpEstimate.Geometry.RotationalProfile.PoleData
