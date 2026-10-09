/-
Copyright (c) 2026 Ziyang Qin. All rights reserved.
No license is granted by this file.
Authors: Ziyang Qin
-/
import RicciFlowSharpEstimate.Analysis.SecondPrimitive
import RicciFlowSharpEstimate.Geometry.AreaProfile
import Mathlib.Analysis.Convex.Deriv

/-!
# Calculus and positivity of normalized area profiles

The exact curvature primitives satisfy their differential equations and pole
conditions. Positive curvature makes the height strictly increasing and the
warping coefficient strictly concave, with strict positivity between its poles.
-/

noncomputable section

namespace RicciFlowSharpEstimate.Geometry.AreaProfile

open MeasureTheory
open scoped ContDiff

/-- The actual first derivative of the triangular warping primitive. -/
theorem warp_hasDerivAt (K : ℝ → ℝ) (hK : Continuous K) (x : ℝ) :
    HasDerivAt (warp K) (warpSlope K x) x := by
  have hSecond := Analysis.SecondPrimitive.integral_kernel_hasDerivAt K hK 0 x
  unfold warp warpSlope
  convert ((hasDerivAt_id x).const_mul 2).sub (hSecond.const_mul 2) using 1
  · rfl
  · ring

/-- The warping slope has the prescribed curvature derivative. -/
theorem warpSlope_hasDerivAt (K : ℝ → ℝ) (hK : Continuous K) (x : ℝ) :
    HasDerivAt (warpSlope K) (-2 * K x) x := by
  have hFirst := (hK.integral_hasStrictDerivAt 0 x).hasDerivAt
  unfold warpSlope
  convert (hasDerivAt_const x 2).sub (hFirst.const_mul 2) using 1
  ring

theorem deriv_warp (K : ℝ → ℝ) (hK : Continuous K) :
    deriv (warp K) = warpSlope K := by
  funext x
  exact (warp_hasDerivAt K hK x).deriv

theorem deriv_warpSlope (K : ℝ → ℝ) (hK : Continuous K) :
    deriv (warpSlope K) = fun x => -2 * K x := by
  funext x
  exact (warpSlope_hasDerivAt K hK x).deriv

/-- The second derivative of the original warp equals minus twice its curvature. -/
theorem deriv_deriv_warp (K : ℝ → ℝ) (hK : Continuous K) :
    deriv (deriv (warp K)) = fun x => -2 * K x := by
  rw [deriv_warp K hK, deriv_warpSlope K hK]

/-- Smooth curvature gives a globally smooth warp. -/
theorem warp_contDiff (K : ℝ → ℝ) (hK : ContDiff ℝ ∞ K) :
    ContDiff ℝ ∞ (warp K) := by
  exact (contDiff_const.mul contDiff_id).sub
    (contDiff_const.mul (Analysis.SecondPrimitive.integral_kernel_contDiff K hK 0))

/-- Smooth curvature gives a globally smooth warping slope. -/
theorem warpSlope_contDiff (K : ℝ → ℝ) (hK : ContDiff ℝ ∞ K) :
    ContDiff ℝ ∞ (warpSlope K) := by
  exact contDiff_const.sub
    (contDiff_const.mul (Analysis.SecondPrimitive.integral_contDiff K hK 0))

/-- The two exact moments close the warping primitive at the north pole. -/
theorem warp_one (K : ℝ → ℝ) (hK : Continuous K)
    (hzero : (∫ x in (0 : ℝ)..1, K x) = 2)
    (hone : (∫ x in (0 : ℝ)..1, x * K x) = 1) :
    warp K 1 = 0 := by
  rw [warp, Analysis.SecondPrimitive.integral_kernel_eq K hK 0 1, hzero, hone]
  norm_num

/-- The zeroth moment gives the north-pole slope. -/
theorem warpSlope_one (K : ℝ → ℝ)
    (hzero : (∫ x in (0 : ℝ)..1, K x) = 2) :
    warpSlope K 1 = -2 := by
  rw [warpSlope, hzero]
  norm_num

/-- The height primitive is continuous for every continuous curvature coefficient. -/
theorem heightCoordinate_continuous (K : ℝ → ℝ) (hK : Continuous K) :
    Continuous (heightCoordinate K) := by
  exact continuous_iff_continuousAt.mpr fun x =>
    (heightCoordinate_hasDerivAt K hK x).continuousAt

/-- The warp is continuous without any differentiability hypothesis on the curvature. -/
theorem warp_continuous (K : ℝ → ℝ) (hK : Continuous K) :
    Continuous (warp K) := by
  exact continuous_iff_continuousAt.mpr fun x => (warp_hasDerivAt K hK x).continuousAt

/-- The stored slope is continuous for every continuous curvature coefficient. -/
theorem warpSlope_continuous (K : ℝ → ℝ) (hK : Continuous K) :
    Continuous (warpSlope K) := by
  exact continuous_iff_continuousAt.mpr fun x => (warpSlope_hasDerivAt K hK x).continuousAt

/-- Positive curvature makes the normalized height strictly increasing on the physical interval. -/
theorem heightCoordinate_strictMonoOn (K : ℝ → ℝ) (hK : Continuous K)
    (hpos : ∀ x ∈ Set.Icc (0 : ℝ) 1, 0 < K x) :
    StrictMonoOn (heightCoordinate K) (Set.Icc (0 : ℝ) 1) := by
  apply strictMonoOn_of_deriv_pos (convex_Icc 0 1)
    (heightCoordinate_continuous K hK).continuousOn
  intro x hx
  rw [deriv_heightCoordinate K hK]
  exact hpos x (interior_subset hx)

/-- The normalized height sends the full area interval into the full height interval. -/
theorem heightCoordinate_mapsTo (K : ℝ → ℝ) (hK : Continuous K)
    (hpos : ∀ x ∈ Set.Icc (0 : ℝ) 1, 0 < K x)
    (hzero : (∫ x in (0 : ℝ)..1, K x) = 2) :
    Set.MapsTo (heightCoordinate K) (Set.Icc (0 : ℝ) 1) (Set.Icc (-1 : ℝ) 1) := by
  have hmono := (heightCoordinate_strictMonoOn K hK hpos).monotoneOn
  intro x hx
  constructor
  · calc
      -1 = heightCoordinate K 0 := (heightCoordinate_zero K).symm
      _ ≤ heightCoordinate K x := hmono (by norm_num) hx hx.1
  · calc
      heightCoordinate K x ≤ heightCoordinate K 1 := hmono hx (by norm_num) hx.2
      _ = 1 := heightCoordinate_one K hzero

/-- The actual normalized height is a bijection of the physical closed intervals. -/
theorem heightCoordinate_bijOn (K : ℝ → ℝ) (hK : Continuous K)
    (hpos : ∀ x ∈ Set.Icc (0 : ℝ) 1, 0 < K x)
    (hzero : (∫ x in (0 : ℝ)..1, K x) = 2) :
    Set.BijOn (heightCoordinate K) (Set.Icc (0 : ℝ) 1) (Set.Icc (-1 : ℝ) 1) := by
  refine ⟨heightCoordinate_mapsTo K hK hpos hzero,
    (heightCoordinate_strictMonoOn K hK hpos).injOn, ?_⟩
  have hIV := intermediate_value_Icc (by norm_num : (0 : ℝ) ≤ 1)
    (heightCoordinate_continuous K hK).continuousOn
  intro y hy
  apply hIV
  simpa only [heightCoordinate_zero, heightCoordinate_one K hzero] using hy

/-- Actual positive curvature makes the original warping primitive strictly concave. -/
theorem warp_strictConcaveOn (K : ℝ → ℝ) (hK : Continuous K)
    (hpos : ∀ x ∈ Set.Icc (0 : ℝ) 1, 0 < K x) :
    StrictConcaveOn ℝ (Set.Icc (0 : ℝ) 1) (warp K) := by
  apply strictConcaveOn_of_deriv2_neg' (convex_Icc 0 1) (warp_continuous K hK).continuousOn
  intro x hx
  change deriv (deriv (warp K)) x < 0
  rw [deriv_deriv_warp K hK]
  nlinarith [hpos x hx]

/-- Both exact moments and positive curvature force strict interior warping positivity. -/
theorem warp_pos_of_moments (K : ℝ → ℝ) (hK : Continuous K)
    (hpos : ∀ x ∈ Set.Icc (0 : ℝ) 1, 0 < K x)
    (hzero : (∫ x in (0 : ℝ)..1, K x) = 2)
    (hone : (∫ x in (0 : ℝ)..1, x * K x) = 1)
    (x : ℝ) (hx : x ∈ Set.Ioo (0 : ℝ) 1) : 0 < warp K x := by
  have hconc := warp_strictConcaveOn K hK hpos
  have hChord := hconc.2 (by norm_num : (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1)
    (by norm_num : (1 : ℝ) ∈ Set.Icc (0 : ℝ) 1) (by norm_num : (0 : ℝ) ≠ 1)
    (sub_pos.mpr hx.2) hx.1 (by ring : 1 - x + x = 1)
  simpa only [smul_eq_mul, warp_zero, warp_one K hK hzero hone,
    mul_zero, mul_one, zero_add, add_zero] using hChord

/-- The two moment conditions center the actual normalized height primitive. -/
theorem integral_heightCoordinate (K : ℝ → ℝ) (hK : Continuous K)
    (hzero : (∫ x in (0 : ℝ)..1, K x) = 2)
    (hone : (∫ x in (0 : ℝ)..1, x * K x) = 1) :
    (∫ x in (0 : ℝ)..1, heightCoordinate K x) = 0 := by
  have hPrimitive : ∀ x : ℝ,
      HasDerivAt (fun y => -(warp K y) / 2) (heightCoordinate K x) x := by
    intro x
    convert ((warp_hasDerivAt K hK x).neg.div_const 2) using 1
    rw [warpSlope_eq_neg_two_height]
    ring
  have hIntegral := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun x _ => hPrimitive x) ((heightCoordinate_continuous K hK).intervalIntegrable 0 1)
  rw [hIntegral, warp_one K hK hzero hone, warp_zero]
  norm_num

end RicciFlowSharpEstimate.Geometry.AreaProfile
