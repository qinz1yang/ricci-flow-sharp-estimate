/-
Copyright (c) 2026 Ziyang Qin. All rights reserved.
No license is granted by this file.
Authors: Ziyang Qin
-/
import RicciFlowSharpEstimate.Geometry.ReciprocalAreaSymmetry
import RicciFlowSharpEstimate.Geometry.ReciprocalProfileAction
import RicciFlowSharpEstimate.Variational.ReciprocalProfileShape
import RicciFlowSharpEstimate.Variational.CriticalCap

/-!
# The actual critical curvature in normalized area coordinates

The accepted continuous reciprocal optimizer produces the physical area
coordinate and curvature. Its exact moments, hemisphere shape, positive
plateau and zero unit-probe action are derived without a smooth metric.

Adapted from Ziyang Qin's historical critical meridian construction, retaining
the actual normalized coordinate and both inverse laws publicly.
-/

noncomputable section

namespace RicciFlowSharpEstimate.Geometry.CriticalAreaProfile

open MeasureTheory Set Variational

/-- The actual reciprocal optimizer at the structurally derived critical cap. -/
def reciprocal : ℝ → ℝ := evenReciprocalProfile criticalCap

/-- Its total reciprocal area scale. -/
def length : ℝ := ReciprocalArea.length reciprocal

/-- Its actual normalized area primitive. -/
def coordinate : ℝ → ℝ := ReciprocalArea.coordinate reciprocal

/-- The actual physical inverse, continuously clamped outside the area interval. -/
def inverse : ℝ → ℝ := ReciprocalArea.inverse reciprocal

/-- The continuous critical curvature, with the actual area normalization. -/
def curvature : ℝ → ℝ := ReciprocalArea.curvature reciprocal

private theorem reciprocal_continuous : Continuous reciprocal :=
  (uniformContinuous_evenReciprocalProfile criticalCap).continuous

private theorem reciprocal_pos (v : ℝ) (_hv : v ∈ Icc (-1 : ℝ) 1) :
    0 < reciprocal v :=
  (one_div_pos.mpr (zero_lt_one.trans one_lt_criticalCap)).trans_le
    (evenReciprocalProfile_bounds criticalCap one_lt_criticalCap.le v).1

private theorem reciprocal_even : Function.Even reciprocal :=
  even_evenReciprocalProfile criticalCap

private theorem reciprocal_balance : RotationalProfile.balance reciprocal = 0 :=
  RotationalProfile.balance_eq_zero_of_even reciprocal reciprocal_even

/-- The actual critical normalization is strictly positive. -/
theorem length_pos : 0 < length :=
  ReciprocalArea.length_pos reciprocal reciprocal_continuous reciprocal_pos

/-- The constant two lies strictly inside the actual critical curvature box. -/
theorem strict_average_bounds : length < 2 ∧ 2 < length * criticalCap :=
  evenReciprocalProfile_strict_average_bounds criticalCap one_lt_criticalCap

/-- The actual forward coordinate has derivative equal to its normalized reciprocal. -/
theorem coordinate_hasDerivAt (v : ℝ) :
    HasDerivAt coordinate (reciprocal v / length) v :=
  ReciprocalArea.coordinate_hasDerivAt reciprocal reciprocal_continuous v

@[simp] theorem coordinate_neg_one : coordinate (-1) = 0 :=
  ReciprocalArea.coordinate_neg_one reciprocal

@[simp] theorem coordinate_one : coordinate 1 = 1 :=
  ReciprocalArea.coordinate_one reciprocal reciprocal_continuous reciprocal_pos

@[simp] theorem inverse_zero : inverse 0 = -1 :=
  ReciprocalArea.inverse_zero reciprocal reciprocal_continuous reciprocal_pos

@[simp] theorem inverse_one : inverse 1 = 1 :=
  ReciprocalArea.inverse_one reciprocal reciprocal_continuous reciprocal_pos

/-- The actual critical coordinate bijects the two physical intervals. -/
theorem coordinate_bijOn : BijOn coordinate (Icc (-1 : ℝ) 1) (Icc (0 : ℝ) 1) :=
  ReciprocalArea.coordinate_bijOn reciprocal reciprocal_continuous reciprocal_pos

/-- Every value of the clamped inverse lies in the physical height interval. -/
theorem inverse_mem (x : ℝ) : inverse x ∈ Icc (-1 : ℝ) 1 :=
  ReciprocalArea.inverse_mem reciprocal reciprocal_continuous reciprocal_pos x

/-- The physical left-inverse law includes both poles. -/
theorem inverse_coordinate (v : ℝ) (hv : v ∈ Icc (-1 : ℝ) 1) :
    inverse (coordinate v) = v :=
  ReciprocalArea.inverse_coordinate reciprocal reciprocal_continuous reciprocal_pos v hv

/-- The physical right-inverse law includes both area endpoints. -/
theorem coordinate_inverse (x : ℝ) (hx : x ∈ Icc (0 : ℝ) 1) :
    coordinate (inverse x) = x :=
  ReciprocalArea.coordinate_inverse reciprocal reciprocal_continuous reciprocal_pos x hx

/-- The same physical inverse is globally continuous. -/
theorem inverse_continuous : Continuous inverse :=
  ReciprocalArea.inverse_continuous reciprocal reciprocal_continuous reciprocal_pos

/-- Critical curvature is continuous on the whole real line. -/
theorem curvature_continuous : Continuous curvature :=
  ReciprocalArea.curvature_continuous reciprocal reciprocal_continuous reciprocal_pos

/-- Critical curvature is positive, including at both area endpoints. -/
theorem curvature_pos (x : ℝ) : 0 < curvature x :=
  ReciprocalArea.curvature_pos reciprocal reciprocal_continuous reciprocal_pos x

/-- The actual critical coordinate retains the exact curvature tying equation. -/
theorem curvature_coordinate (v : ℝ) (hv : v ∈ Icc (-1 : ℝ) 1) :
    curvature (coordinate v) = length / reciprocal v :=
  ReciprocalArea.curvature_coordinate reciprocal reciprocal_continuous reciprocal_pos v hv

/-- The actual continuous critical curvature remains inside its exact scaled box. -/
theorem curvature_bounds (x : ℝ) : curvature x ∈ Icc length (length * criticalCap) := by
  have h := ReciprocalArea.curvature_mem_Icc reciprocal reciprocal_continuous
    (1 / criticalCap) 1 (one_div_pos.mpr (zero_lt_one.trans one_lt_criticalCap))
    (fun v _ => evenReciprocalProfile_bounds criticalCap one_lt_criticalCap.le v) x
  simpa only [curvature, length, div_one, div_div_eq_mul_div] using h

/-- Both normalized moments hold for this actual critical curvature. -/
theorem curvature_moments :
    (∫ x in (0 : ℝ)..1, curvature x) = 2 ∧
      (∫ x in (0 : ℝ)..1, x * curvature x) = 1 :=
  ⟨ReciprocalArea.integral_curvature reciprocal reciprocal_continuous reciprocal_pos,
    ReciprocalArea.integral_mul_curvature reciprocal reciprocal_continuous
      reciprocal_pos reciprocal_balance⟩

/-- The actual critical warp retains its exact normalization in the height coordinate. -/
theorem warp_coordinate (v : ℝ) (hv : v ∈ Icc (-1 : ℝ) 1) :
    AreaProfile.warp curvature (coordinate v) = RotationalProfile.warp reciprocal v / length :=
  ReciprocalArea.warp_coordinate reciprocal reciprocal_continuous reciprocal_pos
    reciprocal_balance v hv

/-- Its actual slope is minus twice the physical height. -/
theorem warpSlope_coordinate (v : ℝ) (hv : v ∈ Icc (-1 : ℝ) 1) :
    AreaProfile.warpSlope curvature (coordinate v) = -2 * v :=
  ReciprocalArea.warpSlope_coordinate reciprocal reciprocal_continuous reciprocal_pos v hv

/-- The original curvature primitive and the constructed inverse agree physically. -/
theorem heightCoordinate_eq_inverse (x : ℝ) (hx : x ∈ Icc (0 : ℝ) 1) :
    AreaProfile.heightCoordinate curvature x = inverse x := by
  have h : AreaProfile.heightCoordinate curvature (coordinate (inverse x)) = inverse x :=
    ReciprocalArea.heightCoordinate_coordinate reciprocal reciprocal_continuous
    reciprocal_pos (inverse x) (inverse_mem x)
  simpa only [coordinate_inverse x hx] using h

/-- Reflection in height is reflection about half area for the actual critical coordinate. -/
theorem coordinate_reflection (v : ℝ) : coordinate (-v) = 1 - coordinate v :=
  ReciprocalArea.coordinate_reflection reciprocal reciprocal_continuous reciprocal_pos
    reciprocal_even v

@[simp] theorem coordinate_zero : coordinate 0 = 1 / 2 :=
  ReciprocalArea.coordinate_zero reciprocal reciprocal_continuous reciprocal_pos reciprocal_even

@[simp] theorem inverse_half : inverse (2⁻¹) = 0 := by
  simpa only [inverse, one_div] using
    ReciprocalArea.inverse_half reciprocal reciprocal_continuous reciprocal_pos reciprocal_even

/-- The actual continuous critical curvature is symmetric on the physical interval. -/
theorem curvature_reflection (x : ℝ) (hx : x ∈ Icc (0 : ℝ) 1) :
    curvature (1 - x) = curvature x :=
  ReciprocalArea.curvature_reflection reciprocal reciprocal_continuous reciprocal_pos
    reciprocal_even x hx

/-- Critical curvature decreases on the southern area hemisphere. -/
theorem curvature_antitoneOn_left : AntitoneOn curvature (Icc (0 : ℝ) (1 / 2)) :=
  ReciprocalArea.curvature_antitoneOn_left reciprocal reciprocal_continuous reciprocal_pos
    reciprocal_even (monotoneOn_evenReciprocalProfile criticalCap)

/-- Critical curvature increases on the northern area hemisphere. -/
theorem curvature_monotoneOn_right : MonotoneOn curvature (Icc (1 / 2 : ℝ) 1) :=
  ReciprocalArea.curvature_monotoneOn_right reciprocal reciprocal_continuous reciprocal_pos
    reciprocal_even (antitoneOn_evenReciprocalProfile criticalCap)

/-- Positive curvature and the actual moments give positive interior warping. -/
theorem warp_pos (x : ℝ) (hx : x ∈ Ioo (0 : ℝ) 1) : 0 < AreaProfile.warp curvature x :=
  AreaProfile.warp_pos_of_moments curvature curvature_continuous
    (fun x _ => curvature_pos x) curvature_moments.1 curvature_moments.2 x hx

/-- An actual nonempty closed interior plateau has positive minimum curvature and warp. -/
theorem exists_positive_constant_plateau :
    ∃ l u : ℝ, 0 < l ∧ l < u ∧ u < 1 ∧
      (∀ x ∈ Icc l u, curvature x = length) ∧
      ∀ x ∈ Icc l u, 0 < AreaProfile.warp curvature x := by
  let α := lowerContact (capParameter criticalCap)
  have hα : 0 < α ∧ α < 1 :=
    ⟨(evenReciprocalProfile_central_plateau criticalCap).1,
      (evenReciprocalProfile_central_plateau criticalCap).2.1⟩
  have hhalf : α / 2 ∈ Icc (-1 : ℝ) 1 := by constructor <;> linarith [hα.1, hα.2]
  have hzero : (0 : ℝ) ∈ Icc (-1 : ℝ) 1 := by norm_num
  have hm := ReciprocalArea.coordinate_strictMonoOn reciprocal reciprocal_continuous reciprocal_pos
  have hInv := (ReciprocalArea.inverse_strictMonoOn reciprocal
    reciprocal_continuous reciprocal_pos).monotoneOn
  have hl : 0 < coordinate 0 := by rw [coordinate_zero]; norm_num
  have hlu : coordinate 0 < coordinate (α / 2) := hm hzero hhalf (by linarith [hα.1])
  have hu : coordinate (α / 2) < 1 := by
    have h : coordinate (α / 2) < coordinate 1 :=
      hm hhalf (by norm_num : (1 : ℝ) ∈ Icc (-1 : ℝ) 1) (by linarith [hα.2])
    simpa only [coordinate_one] using h
  have hx01 (x : ℝ) (hx : x ∈ Icc (coordinate 0) (coordinate (α / 2))) :
      x ∈ Icc (0 : ℝ) 1 := ⟨hl.le.trans hx.1, hx.2.trans hu.le⟩
  refine ⟨coordinate 0, coordinate (α / 2), hl, hlu, hu, ?_, ?_⟩
  · intro x hx
    have hvlow : 0 ≤ inverse x := by
      have h := hInv (coordinate_bijOn.mapsTo hzero) (hx01 x hx) hx.1
      change inverse (coordinate 0) ≤ inverse x at h
      simpa only [inverse_coordinate 0 hzero] using h
    have hvhigh : inverse x ≤ α / 2 := by
      have h := hInv (hx01 x hx) (coordinate_bijOn.mapsTo hhalf) hx.2
      change inverse x ≤ inverse (coordinate (α / 2)) at h
      simpa only [inverse_coordinate (α / 2) hhalf] using h
    change length / reciprocal (inverse x) = length
    have hval : reciprocal (inverse x) = 1 :=
      evenReciprocalProfile_eq_low criticalCap (inverse x)
        (by rw [abs_of_nonneg hvlow]; change inverse x ≤ α; linarith [hα.1])
    rw [hval, div_one]
  · intro x hx
    exact warp_pos x ⟨hl.trans_le hx.1, hx.2.trans_lt hu⟩

/-- The genuine complete unit-probe area action vanishes at the critical optimizer. -/
theorem meridionalAction_one_eq_zero : AreaProfile.meridionalAction curvature (fun _ => 1) = 0 := by
  rw [curvature, ReciprocalArea.meridionalAction_one reciprocal reciprocal_continuous
    reciprocal_pos reciprocal_balance]
  rw [reciprocal, RotationalProfile.integral_warp_div_evenReciprocalProfile
    criticalCap one_lt_criticalCap.le, pairFunctional_obstacleLogProfile_criticalCap]
  norm_num

end RicciFlowSharpEstimate.Geometry.CriticalAreaProfile
