/-
Copyright (c) 2026 Ziyang Qin. All rights reserved.
No license is granted by this file.
Authors: Ziyang Qin
-/
import RicciFlowSharpEstimate.Geometry.RotationalPoleData

/-!
# Height-coordinate curvature coefficients

The actual warping integral and radial coefficient have the derivative identities
needed in the intrinsic radial diagonal curvature formula.
-/

noncomputable section

namespace RicciFlowSharpEstimate.Geometry.RotationalProfile.PoleData

open Set
open scoped ContDiff

/-- The radial metric coefficient in height coordinates. -/
def radialCoefficient (D : PoleData) (v : ℝ) : ℝ := D.a v ^ 2 / warp D.a v

/-- The radial coefficient is smooth between the poles. -/
theorem radialCoefficient_contDiffOn (D : PoleData) :
    ContDiffOn ℝ ∞ D.radialCoefficient (Ioo (-1 : ℝ) 1) :=
  D.a_contDiff.contDiffOn.pow 2 |>.div (warp_contDiff D.a D.a_contDiff).contDiffOn
    (fun v hv => (warp_pos_of_balance D.a D.a_contDiff.continuous
      D.a_pos D.balance_eq v hv).ne')

/-- The actual second warping derivative. -/
theorem deriv_warp_hasDerivAt (D : PoleData) (v : ℝ) :
    HasDerivAt (deriv (warp D.a)) (-2 * D.a v - 2 * v * deriv D.a v) v := by
  have hf : deriv (warp D.a) = fun z => -2 * z * D.a z :=
    funext (deriv_warp_eq D.a D.a_contDiff.continuous)
  rw [hf]
  convert ((hasDerivAt_id v).const_mul (-2)).mul
    (D.a_contDiff.differentiable (by simp)).differentiableAt.hasDerivAt using 1
  · rfl
  · simp only [id_eq]
    ring

/-- Differentiating the actual radial coefficient between the poles. -/
theorem radialCoefficient_hasDerivAt (D : PoleData) (v : ℝ)
    (hv : v ∈ Ioo (-1 : ℝ) 1) :
    HasDerivAt D.radialCoefficient
      ((2 * D.a v * deriv D.a v * warp D.a v + 2 * v * D.a v ^ 3) /
        warp D.a v ^ 2) v := by
  have hf := (warp_pos_of_balance D.a D.a_contDiff.continuous
    D.a_pos D.balance_eq v hv).ne'
  convert (((D.a_contDiff.differentiable (by simp)).differentiableAt.hasDerivAt).pow 2).div
    (warp_hasDerivAt D.a D.a_contDiff.continuous v) hf using 1
  · rfl
  · simp only [Pi.pow_apply]
    ring

/-- Substitution of the actual profile coefficients into the scalar-curvature
expression gives twice the reciprocal profile. -/
theorem radial_curvature_identity (D : PoleData) (v : ℝ)
    (hv : v ∈ Ioo (-1 : ℝ) 1) :
    2 * ((-deriv (deriv (warp D.a)) v / (2 * warp D.a v) +
        deriv (warp D.a) v ^ 2 / (4 * warp D.a v ^ 2) +
        deriv D.radialCoefficient v * deriv (warp D.a) v /
          (4 * D.radialCoefficient v * warp D.a v)) / D.radialCoefficient v) =
      2 / D.a v := by
  have ha := (D.a_pos v ⟨hv.1.le, hv.2.le⟩).ne'
  have hf := (warp_pos_of_balance D.a D.a_contDiff.continuous
    D.a_pos D.balance_eq v hv).ne'
  rw [(D.deriv_warp_hasDerivAt v).deriv,
    deriv_warp_eq D.a D.a_contDiff.continuous,
    (D.radialCoefficient_hasDerivAt v hv).deriv, radialCoefficient]
  field_simp [ha, hf]
  ring

end RicciFlowSharpEstimate.Geometry.RotationalProfile.PoleData
