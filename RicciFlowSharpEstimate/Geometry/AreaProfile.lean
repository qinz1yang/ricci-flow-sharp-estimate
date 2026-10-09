/-
Copyright (c) 2026 Ziyang Qin. All rights reserved.
No license is granted by this file.
Authors: Ziyang Qin
-/
import RicciFlowSharpEstimate.Geometry.RotationalProfile

/-!
# Normalized area-coordinate profiles and their complete action

The height and metric coefficients are the actual curvature primitives on
the normalized interval. The complete action retains all six coefficient
and probe entries. Their derivative and geometric realization laws are proved
in the dependent calculus and realization modules.

Adapted from Ziyang Qin's historical connection meridian primitive and
complete-action formulas, with the corrected affine term and sign.
-/

noncomputable section

namespace RicciFlowSharpEstimate.Geometry.AreaProfile

open MeasureTheory
open scoped ContDiff

/-- Height is the normalized curvature primitive starting at the south pole. -/
def heightCoordinate (K : ℝ → ℝ) (x : ℝ) : ℝ :=
  -1 + ∫ t in (0 : ℝ)..x, K t

/-- The corrected area-coordinate warping coefficient. -/
def warp (K : ℝ → ℝ) (x : ℝ) : ℝ :=
  2 * x - 2 * ∫ t in (0 : ℝ)..x, (x - t) * K t

/-- The explicit first primitive giving the actual warping slope. -/
def warpSlope (K : ℝ → ℝ) (x : ℝ) : ℝ :=
  2 - 2 * ∫ t in (0 : ℝ)..x, K t

/-- The complete area density as a polynomial in its six coefficient/jet entries. -/
def meridionalActionDensity (f f1 K r r1 r2 : ℝ) : ℝ :=
  f * (f * r2 + 2 * f1 * r1 - K * r) ^ 2 -
    K * f1 * r * (f * r1 + f1 * r / 2) + K ^ 2 * f * r ^ 2

/-- The normalized complete area action of the actual curvature primitives
and the actual first and second derivatives of the supplied scalar probe. -/
def meridionalAction (K r : ℝ → ℝ) : ℝ :=
  ∫ x in (0 : ℝ)..1, meridionalActionDensity
    (warp K x) (warpSlope K x) (K x) (r x) (deriv r x) (deriv (deriv r) x)

/-- The actual height derivative is the original curvature coefficient. -/
theorem heightCoordinate_hasDerivAt (K : ℝ → ℝ) (hK : Continuous K) (x : ℝ) :
    HasDerivAt (heightCoordinate K) (K x) x := by
  have hInt : HasDerivAt (fun y : ℝ => ∫ t in (0 : ℝ)..y, K t) (K x) x :=
    (hK.integral_hasStrictDerivAt 0 x).hasDerivAt
  exact hInt.const_add (-1)

theorem deriv_heightCoordinate (K : ℝ → ℝ) (hK : Continuous K) :
    deriv (heightCoordinate K) = K := by
  funext x
  exact (heightCoordinate_hasDerivAt K hK x).deriv

/-- A smooth curvature coefficient has a genuinely smooth height primitive. -/
theorem heightCoordinate_contDiff (K : ℝ → ℝ) (hK : ContDiff ℝ ∞ K) :
    ContDiff ℝ ∞ (heightCoordinate K) := by
  rw [contDiff_infty_iff_deriv]
  refine ⟨fun x => (heightCoordinate_hasDerivAt K hK.continuous x).differentiableAt, ?_⟩
  rw [deriv_heightCoordinate K hK.continuous]
  exact hK

@[simp]
theorem heightCoordinate_zero (K : ℝ → ℝ) : heightCoordinate K 0 = -1 := by
  simp [heightCoordinate]

/-- The zeroth normalized moment gives the north-pole height. -/
theorem heightCoordinate_one (K : ℝ → ℝ) (hzero : (∫ x in (0 : ℝ)..1, K x) = 2) :
    heightCoordinate K 1 = 1 := by
  simp only [heightCoordinate, hzero]
  norm_num

@[simp]
theorem warp_zero (K : ℝ → ℝ) : warp K 0 = 0 := by
  simp [warp]

@[simp]
theorem warpSlope_zero (K : ℝ → ℝ) : warpSlope K 0 = 2 := by
  simp [warpSlope]

/-- The same height coordinate determines the warping slope exactly. -/
theorem warpSlope_eq_neg_two_height (K : ℝ → ℝ) (x : ℝ) :
    warpSlope K x = -2 * heightCoordinate K x := by
  simp only [warpSlope, heightCoordinate]
  ring

end RicciFlowSharpEstimate.Geometry.AreaProfile
