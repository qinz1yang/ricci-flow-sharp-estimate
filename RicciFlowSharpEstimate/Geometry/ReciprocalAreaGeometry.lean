/-
Copyright (c) 2026 Ziyang Qin. All rights reserved.
No license is granted by this file.
Authors: Ziyang Qin
-/
import RicciFlowSharpEstimate.Analysis.ContinuousIntervalInverse
import RicciFlowSharpEstimate.Geometry.AreaAction
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

/-!
# Continuous reciprocal profiles in normalized area coordinates

The normalized primitive and its genuine clamped physical inverse transport a
positive continuous reciprocal profile to the actual area curvature. Balance
closes the warp and its first moment. Forward change of variables identifies
the complete unit-probe action without differentiating the inverse or curvature.

Adapted from Ziyang Qin's historical critical meridian construction, generalized
to every continuous positive balanced reciprocal profile.
-/

noncomputable section

namespace RicciFlowSharpEstimate.Geometry.ReciprocalArea

open MeasureTheory Set

/-- The total reciprocal-profile area scale. -/
def length (a : ℝ → ℝ) : ℝ := ∫ v in (-1 : ℝ)..1, a v

/-- The actual normalized area primitive. -/
def coordinate (a : ℝ → ℝ) (v : ℝ) : ℝ :=
  (∫ s in (-1 : ℝ)..v, a s) / length a

/-- The genuine physical inverse, continuously clamped at the two poles. -/
def inverse (a : ℝ → ℝ) : ℝ → ℝ :=
  Analysis.clampedIntervalInverse (coordinate a) (-1) 1

/-- Curvature transported by the physical inverse with the actual area normalization. -/
def curvature (a : ℝ → ℝ) (x : ℝ) : ℝ := length a / a (inverse a x)

/-- A positive continuous reciprocal profile has positive total scale. -/
theorem length_pos (a : ℝ → ℝ) (ha : Continuous a)
    (hpos : ∀ v ∈ Icc (-1 : ℝ) 1, 0 < a v) : 0 < length a := by
  apply intervalIntegral.intervalIntegral_pos_of_pos_on (ha.intervalIntegrable (-1) 1)
  · intro v hv
    exact hpos v ⟨hv.1.le, hv.2.le⟩
  · norm_num

/-- The derivative of the original coordinate is its normalized reciprocal profile. -/
theorem coordinate_hasDerivAt (a : ℝ → ℝ) (ha : Continuous a) (v : ℝ) :
    HasDerivAt (coordinate a) (a v / length a) v :=
  ((ha.integral_hasStrictDerivAt (-1) v).hasDerivAt).div_const (length a)

/-- The original normalized primitive is continuous globally. -/
theorem coordinate_continuous (a : ℝ → ℝ) (ha : Continuous a) :
    Continuous (coordinate a) :=
  continuous_iff_continuousAt.mpr fun v => (coordinate_hasDerivAt a ha v).continuousAt

@[simp]
theorem coordinate_neg_one (a : ℝ → ℝ) : coordinate a (-1) = 0 := by
  simp [coordinate]

/-- The normalized primitive sends the north pole to unit area. -/
theorem coordinate_one (a : ℝ → ℝ) (ha : Continuous a)
    (hpos : ∀ v ∈ Icc (-1 : ℝ) 1, 0 < a v) : coordinate a 1 = 1 := by
  exact div_self (length_pos a ha hpos).ne'

/-- Positivity makes the normalized primitive strictly increasing on the physical interval. -/
theorem coordinate_strictMonoOn (a : ℝ → ℝ) (ha : Continuous a)
    (hpos : ∀ v ∈ Icc (-1 : ℝ) 1, 0 < a v) :
    StrictMonoOn (coordinate a) (Icc (-1 : ℝ) 1) := by
  apply strictMonoOn_of_deriv_pos (convex_Icc (-1) 1) (coordinate_continuous a ha).continuousOn
  intro v hv
  rw [(coordinate_hasDerivAt a ha v).deriv]
  exact div_pos (hpos v (interior_subset hv)) (length_pos a ha hpos)

/-- The full physical height interval maps into the full normalized area interval. -/
theorem coordinate_mapsTo (a : ℝ → ℝ) (ha : Continuous a)
    (hpos : ∀ v ∈ Icc (-1 : ℝ) 1, 0 < a v) :
    MapsTo (coordinate a) (Icc (-1 : ℝ) 1) (Icc (0 : ℝ) 1) := by
  intro v hv
  have hm := (coordinate_strictMonoOn a ha hpos).monotoneOn
  constructor
  · simpa only [coordinate_neg_one] using hm (by norm_num) hv hv.1
  · simpa only [coordinate_one a ha hpos] using hm hv (by norm_num) hv.2

/-- The full physical intervals are bijective under the actual normalized primitive. -/
theorem coordinate_bijOn (a : ℝ → ℝ) (ha : Continuous a)
    (hpos : ∀ v ∈ Icc (-1 : ℝ) 1, 0 < a v) :
    BijOn (coordinate a) (Icc (-1 : ℝ) 1) (Icc (0 : ℝ) 1) := by
  refine ⟨coordinate_mapsTo a ha hpos, (coordinate_strictMonoOn a ha hpos).injOn, ?_⟩
  have h := intermediate_value_Icc (by norm_num : (-1 : ℝ) ≤ 1)
    (coordinate_continuous a ha).continuousOn
  intro x hx
  apply h
  simpa only [coordinate_neg_one, coordinate_one a ha hpos] using hx

/-- Every clamped inverse value lies in the physical height interval. -/
theorem inverse_mem (a : ℝ → ℝ) (ha : Continuous a)
    (hpos : ∀ v ∈ Icc (-1 : ℝ) 1, 0 < a v) (x : ℝ) :
    inverse a x ∈ Icc (-1 : ℝ) 1 :=
  Analysis.clampedIntervalInverse_mem (coordinate a) (-1) 1 (by norm_num)
    (coordinate_continuous a ha).continuousOn (coordinate_strictMonoOn a ha hpos) x

/-- The actual clamped inverse is globally continuous. -/
theorem inverse_continuous (a : ℝ → ℝ) (ha : Continuous a)
    (hpos : ∀ v ∈ Icc (-1 : ℝ) 1, 0 < a v) : Continuous (inverse a) :=
  Analysis.clampedIntervalInverse_continuous (coordinate a) (-1) 1 (by norm_num)
    (coordinate_continuous a ha).continuousOn (coordinate_strictMonoOn a ha hpos)

/-- The physical left-inverse law includes both poles. -/
theorem inverse_coordinate (a : ℝ → ℝ) (ha : Continuous a)
    (hpos : ∀ v ∈ Icc (-1 : ℝ) 1, 0 < a v) (v : ℝ) (hv : v ∈ Icc (-1 : ℝ) 1) :
    inverse a (coordinate a v) = v :=
  Analysis.clampedIntervalInverse_apply (coordinate a) (-1) 1 (by norm_num)
    (coordinate_strictMonoOn a ha hpos) v hv

/-- The physical right-inverse law includes both area endpoints. -/
theorem coordinate_inverse (a : ℝ → ℝ) (ha : Continuous a)
    (hpos : ∀ v ∈ Icc (-1 : ℝ) 1, 0 < a v) (x : ℝ) (hx : x ∈ Icc (0 : ℝ) 1) :
    coordinate a (inverse a x) = x := by
  apply Analysis.apply_clampedIntervalInverse (coordinate a) (-1) 1 (by norm_num)
    (coordinate_continuous a ha).continuousOn
  simpa only [coordinate_neg_one, coordinate_one a ha hpos] using hx

/-- The south area endpoint gives the south height pole. -/
theorem inverse_zero (a : ℝ → ℝ) (ha : Continuous a)
    (hpos : ∀ v ∈ Icc (-1 : ℝ) 1, 0 < a v) : inverse a 0 = -1 := by
  rw [← coordinate_neg_one a]
  exact inverse_coordinate a ha hpos (-1) (by norm_num)

/-- The north area endpoint gives the north height pole. -/
theorem inverse_one (a : ℝ → ℝ) (ha : Continuous a)
    (hpos : ∀ v ∈ Icc (-1 : ℝ) 1, 0 < a v) : inverse a 1 = 1 := by
  simpa only [coordinate_one a ha hpos] using
    inverse_coordinate a ha hpos 1 (by norm_num)

/-- The inverse is strictly increasing on the physical area interval. -/
theorem inverse_strictMonoOn (a : ℝ → ℝ) (ha : Continuous a)
    (hpos : ∀ v ∈ Icc (-1 : ℝ) 1, 0 < a v) :
    StrictMonoOn (inverse a) (Icc (0 : ℝ) 1) := by
  intro x hx y hy hxy
  by_contra hn
  have h := (coordinate_strictMonoOn a ha hpos).monotoneOn
    (inverse_mem a ha hpos y) (inverse_mem a ha hpos x) (le_of_not_gt hn)
  rw [coordinate_inverse a ha hpos x hx, coordinate_inverse a ha hpos y hy] at h
  exact hxy.not_ge h

/-- The transported curvature is continuous globally, including the clamped endpoints. -/
theorem curvature_continuous (a : ℝ → ℝ) (ha : Continuous a)
    (hpos : ∀ v ∈ Icc (-1 : ℝ) 1, 0 < a v) : Continuous (curvature a) :=
  continuous_const.div (ha.comp (inverse_continuous a ha hpos))
    (fun x => (hpos _ (inverse_mem a ha hpos x)).ne')

/-- The transported curvature is positive globally. -/
theorem curvature_pos (a : ℝ → ℝ) (ha : Continuous a)
    (hpos : ∀ v ∈ Icc (-1 : ℝ) 1, 0 < a v) (x : ℝ) : 0 < curvature a x :=
  div_pos (length_pos a ha hpos) (hpos _ (inverse_mem a ha hpos x))

/-- The physical curvature equation preserves the original reciprocal profile exactly. -/
theorem curvature_coordinate (a : ℝ → ℝ) (ha : Continuous a)
    (hpos : ∀ v ∈ Icc (-1 : ℝ) 1, 0 < a v) (v : ℝ) (hv : v ∈ Icc (-1 : ℝ) 1) :
    curvature a (coordinate a v) = length a / a v := by
  rw [curvature, inverse_coordinate a ha hpos v hv]

/-- Forward substitution uses the actual reciprocal-profile Jacobian. -/
theorem integral_comp_coordinate (a : ℝ → ℝ) (ha : Continuous a)
    (hpos : ∀ v ∈ Icc (-1 : ℝ) 1, 0 < a v) (g : ℝ → ℝ) (hg : Continuous g) :
    (∫ v in (-1 : ℝ)..1, g (coordinate a v) * (a v / length a)) =
      ∫ x in (0 : ℝ)..1, g x := by
  have h := intervalIntegral.integral_comp_mul_deriv
    (f := coordinate a) (f' := fun v => a v / length a) (g := g)
    (a := (-1 : ℝ)) (b := 1) (fun v _ => coordinate_hasDerivAt a ha v)
    (ha.div_const (length a)).continuousOn hg
  simpa only [coordinate_neg_one, coordinate_one a ha hpos, Function.comp_apply] using h

/-- The actual area slope pulled back by the original coordinate is minus twice height. -/
theorem warpSlope_coordinate (a : ℝ → ℝ) (ha : Continuous a)
    (hpos : ∀ v ∈ Icc (-1 : ℝ) 1, 0 < a v) (v : ℝ) (hv : v ∈ Icc (-1 : ℝ) 1) :
    AreaProfile.warpSlope (curvature a) (coordinate a v) = -2 * v := by
  apply eq_of_has_deriv_right_eq
    (f := fun s => AreaProfile.warpSlope (curvature a) (coordinate a s))
    (g := fun s => -2 * s) (f' := fun _ => -2) (a := (-1 : ℝ)) (b := 1)
  · intro s hs
    have hs' : s ∈ Icc (-1 : ℝ) 1 := ⟨hs.1, hs.2.le⟩
    have h := (AreaProfile.warpSlope_hasDerivAt (curvature a)
      (curvature_continuous a ha hpos) (coordinate a s)).comp s (coordinate_hasDerivAt a ha s)
    rw [curvature_coordinate a ha hpos s hs'] at h
    have heq : (-2 * (length a / a s)) * (a s / length a) = -2 := by
      field_simp [(length_pos a ha hpos).ne', (hpos s hs').ne']
    exact (heq ▸ h).hasDerivWithinAt
  · intro s _
    simpa only [mul_one, id_eq] using ((hasDerivAt_id s).const_mul (-2)).hasDerivWithinAt
  · exact ((AreaProfile.warpSlope_continuous (curvature a)
      (curvature_continuous a ha hpos)).comp (coordinate_continuous a ha)).continuousOn
  · exact (continuous_const.mul continuous_id).continuousOn
  · rw [coordinate_neg_one, AreaProfile.warpSlope_zero]
    norm_num
  · exact hv

/-- The curvature primitive recovers the genuine physical height. -/
theorem heightCoordinate_coordinate (a : ℝ → ℝ) (ha : Continuous a)
    (hpos : ∀ v ∈ Icc (-1 : ℝ) 1, 0 < a v) (v : ℝ) (hv : v ∈ Icc (-1 : ℝ) 1) :
    AreaProfile.heightCoordinate (curvature a) (coordinate a v) = v := by
  have h := warpSlope_coordinate a ha hpos v hv
  rw [AreaProfile.warpSlope_eq_neg_two_height] at h
  linarith

/-- The normalized curvature has exact zeroth moment two. -/
theorem integral_curvature (a : ℝ → ℝ) (ha : Continuous a)
    (hpos : ∀ v ∈ Icc (-1 : ℝ) 1, 0 < a v) :
    (∫ x in (0 : ℝ)..1, curvature a x) = 2 := by
  have h := warpSlope_coordinate a ha hpos 1 (by norm_num)
  rw [coordinate_one a ha hpos, AreaProfile.warpSlope] at h
  linarith

/-- Balance identifies the actual two warping primitives with their exact area scale. -/
theorem warp_coordinate (a : ℝ → ℝ) (ha : Continuous a)
    (hpos : ∀ v ∈ Icc (-1 : ℝ) 1, 0 < a v)
    (hbalance : RotationalProfile.balance a = 0) (v : ℝ) (hv : v ∈ Icc (-1 : ℝ) 1) :
    AreaProfile.warp (curvature a) (coordinate a v) = RotationalProfile.warp a v / length a := by
  apply eq_of_has_deriv_right_eq
    (f := fun s => AreaProfile.warp (curvature a) (coordinate a s))
    (g := fun s => RotationalProfile.warp a s / length a)
    (f' := fun s => -2 * s * a s / length a) (a := (-1 : ℝ)) (b := 1)
  · intro s hs
    have hs' : s ∈ Icc (-1 : ℝ) 1 := ⟨hs.1, hs.2.le⟩
    have h := (AreaProfile.warp_hasDerivAt (curvature a)
      (curvature_continuous a ha hpos) (coordinate a s)).comp s (coordinate_hasDerivAt a ha s)
    rw [warpSlope_coordinate a ha hpos s hs'] at h
    have heq : (-2 * s) * (a s / length a) = -2 * s * a s / length a := by ring
    exact (heq ▸ h).hasDerivWithinAt
  · intro s _
    exact ((RotationalProfile.warp_hasDerivAt a ha s).div_const (length a)).hasDerivWithinAt
  · exact ((AreaProfile.warp_continuous (curvature a)
      (curvature_continuous a ha hpos)).comp (coordinate_continuous a ha)).continuousOn
  · exact ((continuous_iff_continuousAt.mpr fun s =>
      (RotationalProfile.warp_hasDerivAt a ha s).continuousAt).div_const (length a)).continuousOn
  · rw [coordinate_neg_one, AreaProfile.warp_zero,
      RotationalProfile.warp_neg_one_eq_zero_of_balance a hbalance, zero_div]
  · exact hv

/-- Balance gives the exact first normalized curvature moment. -/
theorem integral_mul_curvature (a : ℝ → ℝ) (ha : Continuous a)
    (hpos : ∀ v ∈ Icc (-1 : ℝ) 1, 0 < a v)
    (hbalance : RotationalProfile.balance a = 0) :
    (∫ x in (0 : ℝ)..1, x * curvature a x) = 1 := by
  have h := warp_coordinate a ha hpos hbalance 1 (by norm_num)
  rw [coordinate_one a ha hpos, RotationalProfile.warp_one, zero_div,
    AreaProfile.warp, Analysis.SecondPrimitive.integral_kernel_eq
      (curvature a) (curvature_continuous a ha hpos) 0 1,
    integral_curvature a ha hpos] at h
  linarith

/-- Reciprocal bounds transport to the exact scaled curvature bounds. -/
theorem curvature_mem_Icc (a : ℝ → ℝ) (ha : Continuous a) (m M : ℝ) (hm : 0 < m)
    (hbox : ∀ v ∈ Icc (-1 : ℝ) 1, a v ∈ Icc m M) (x : ℝ) :
    curvature a x ∈ Icc (length a / M) (length a / m) := by
  have hpos : ∀ v ∈ Icc (-1 : ℝ) 1, 0 < a v := fun v hv => hm.trans_le (hbox v hv).1
  have hv := hbox _ (inverse_mem a ha hpos x)
  exact ⟨div_le_div_of_nonneg_left (length_pos a ha hpos).le (hpos _
    (inverse_mem a ha hpos x)) hv.2,
    div_le_div_of_nonneg_left (length_pos a ha hpos).le hm hv.1⟩

/-- Exact forward substitution of every term of the complete unit-probe density. -/
theorem meridionalAction_one_eq_integral (a : ℝ → ℝ) (ha : Continuous a)
    (hpos : ∀ v ∈ Icc (-1 : ℝ) 1, 0 < a v)
    (hbalance : RotationalProfile.balance a = 0) :
    AreaProfile.meridionalAction (curvature a) (fun _ => 1) =
      ∫ v in (-1 : ℝ)..1, 2 * (RotationalProfile.warp a v / a v) - 2 * v ^ 2 := by
  let G : ℝ → ℝ := fun x => AreaProfile.meridionalActionDensity
    (AreaProfile.warp (curvature a) x) (AreaProfile.warpSlope (curvature a) x)
    (curvature a x) 1 0 0
  have hG : Continuous G := by
    have h := AreaProfile.meridionalAction_integrand_continuous (curvature a)
      (fun _ => 1) (curvature_continuous a ha hpos) contDiff_const
    simpa only [deriv_const', deriv_const] using h
  have hsub := integral_comp_coordinate a ha hpos G hG
  change (∫ x in (0 : ℝ)..1, AreaProfile.meridionalActionDensity
    (AreaProfile.warp (curvature a) x) (AreaProfile.warpSlope (curvature a) x)
    (curvature a x) 1 (deriv (fun _ : ℝ => (1 : ℝ)) x)
      (deriv (deriv (fun _ : ℝ => (1 : ℝ))) x)) = _
  simp only [deriv_const', deriv_const]
  change (∫ x in (0 : ℝ)..1, G x) = _
  rw [← hsub]
  apply intervalIntegral.integral_congr
  intro v hv
  have hv' : v ∈ Icc (-1 : ℝ) 1 := by simpa using hv
  dsimp only [G]
  rw [warp_coordinate a ha hpos hbalance v hv', warpSlope_coordinate a ha hpos v hv',
    curvature_coordinate a ha hpos v hv']
  unfold AreaProfile.meridionalActionDensity
  field_simp [(length_pos a ha hpos).ne', (hpos v hv').ne']
  ring

/-- The actual complete area action equals the reciprocal-profile unit action.
Only continuity, physical positivity and balance are needed. -/
theorem meridionalAction_one (a : ℝ → ℝ) (ha : Continuous a)
    (hpos : ∀ v ∈ Icc (-1 : ℝ) 1, 0 < a v)
    (hbalance : RotationalProfile.balance a = 0) :
    AreaProfile.meridionalAction (curvature a) (fun _ => 1) =
      2 * (∫ v in (-1 : ℝ)..1, RotationalProfile.warp a v / a v) - 4 / 3 := by
  have hw : Continuous (RotationalProfile.warp a) :=
    continuous_iff_continuousAt.mpr fun v => (RotationalProfile.warp_hasDerivAt a ha v).continuousAt
  have hratio : ContinuousOn (fun v => RotationalProfile.warp a v / a v) (Icc (-1 : ℝ) 1) :=
    hw.continuousOn.div ha.continuousOn (fun v hv => (hpos v hv).ne')
  have hi : IntervalIntegrable (fun v => RotationalProfile.warp a v / a v) volume (-1) 1 :=
    ContinuousOn.intervalIntegrable (by
      simpa only [uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 1)] using hratio)
  have hi2 : IntervalIntegrable (fun v : ℝ => 2 * v ^ 2) volume (-1) 1 :=
    (continuous_const.mul (continuous_id.pow 2)).intervalIntegrable (-1) 1
  rw [meridionalAction_one_eq_integral a ha hpos hbalance,
    intervalIntegral.integral_sub (hi.const_mul 2) hi2,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
  norm_num [integral_pow]

end RicciFlowSharpEstimate.Geometry.ReciprocalArea
