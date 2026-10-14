/-
Copyright (c) 2026 Ziyang Qin. All rights reserved.
No license is granted by this file.
Authors: Ziyang Qin
-/
import RicciFlowSharpEstimate.Geometry.AreaThresholdMinimum
import RicciFlowSharpEstimate.Geometry.AreaActionFactorization

/-!
# The round value and the strict cap-one gap

The exact weighted operator pairing proves the round action is at least four
times physical mass. Cap-one competitors have this same round curvature on
the physical interval. The endpoint zero value therefore excludes cap one.
No operator orientation is inferred.
-/

noncomputable section
namespace RicciFlowSharpEstimate.Geometry.AreaProfile
open Set MeasureTheory
open scoped ContDiff

private theorem round_action_lower_bound (r : ℝ → ℝ) (hr : ContDiff ℝ ∞ r) :
    4 * probeMass (fun _ => 2) r ≤ meridionalAction (fun _ => 2) r := by
  let K : ℝ → ℝ := fun _ => 2
  have hzero : (∫ x in (0 : ℝ)..1, K x) = 2 := by simp [K]
  have hone : (∫ x in (0 : ℝ)..1, x * K x) = 1 := by
    norm_num [K, intervalIntegral.integral_mul_const, integral_id]
  have hf := warp_continuous K continuous_const
  have hq := (meridionalOperator_contDiff K r contDiff_const hr).continuous
  have hQ : Continuous (fun x => warp K x * meridionalOperator K r x ^ 2) := by fun_prop
  have hF : Continuous (fun x => warp K x * r x * meridionalOperator K r x) := by fun_prop
  have hM : Continuous (fun x => warp K x * r x ^ 2) := by fun_prop
  have hA : meridionalAction K r = ∫ x in (0 : ℝ)..1,
      warp K x * meridionalOperator K r x ^ 2 := by
    simpa only [K, deriv_const, mul_zero, zero_div, zero_mul, add_zero] using
      meridionalAction_eq_square_potential K r contDiff_const hr hzero hone
  have hpair := integral_warp_mul_probe_operator K r continuous_const
    (hr.of_le (by simp)) hzero hone
  have hmass : (∫ x in (0 : ℝ)..1, warp K x * K x * r x ^ 2) =
      2 * probeMass K r := by
    rw [probeMass, ← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro x _
    dsimp only [K]
    ring
  rw [hmass] at hpair
  have hnonneg : 0 ≤ ∫ x in (0 : ℝ)..1,
      warp K x * meridionalOperator K r x ^ 2 +
        4 * (warp K x * r x * meridionalOperator K r x) + 4 * (warp K x * r x ^ 2) := by
    apply intervalIntegral.integral_nonneg zero_le_one
    intro x hx
    have hf0 : 0 ≤ warp K x := by
      rw [show K = (fun _ => 2) from rfl, warp_two]
      nlinarith [mul_nonneg hx.1 (sub_nonneg.mpr hx.2)]
    nlinarith only [mul_nonneg hf0 (sq_nonneg (meridionalOperator K r x + 2 * r x))]
  have hQF : IntervalIntegrable (fun x => warp K x * meridionalOperator K r x ^ 2 +
      4 * (warp K x * r x * meridionalOperator K r x)) volume 0 1 :=
    (hQ.add (hF.const_mul 4)).intervalIntegrable 0 1
  rw [intervalIntegral.integral_add hQF
      ((hM.const_mul 4).intervalIntegrable 0 1),
    intervalIntegral.integral_add (hQ.intervalIntegrable 0 1)
      ((hF.const_mul 4).intervalIntegrable 0 1),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    ← hA, hpair] at hnonneg
  change 0 ≤ meridionalAction K r + 4 * (-probeGradientEnergy K r -
    2 * probeMass K r) + 4 * probeMass K r at hnonneg
  have hg := probeGradientEnergy_nonneg K r
  change 4 * probeMass K r ≤ meridionalAction K r
  linarith

private theorem cap_one_action_lower_bound {K r : ℝ → ℝ}
    (h : IsSmoothAreaCompetitor 1 K r) : 4 ≤ meridionalAction K r := by
  have hK (x : ℝ) (hx : x ∈ Icc (0 : ℝ) 1) : K x = 2 := by
    have hb := h.common_bounds x hx
    norm_num at hb
    exact le_antisymm hb.2 hb.1
  have hw (x : ℝ) (hx : x ∈ Icc (0 : ℝ) 1) :
      warp K x = warp (fun _ => 2) x := by
    unfold warp
    congr 2
    apply intervalIntegral.integral_congr
    intro y hy
    rw [uIcc_of_le hx.1] at hy
    dsimp only
    rw [hK y ⟨hy.1, hy.2.trans hx.2⟩]
  have hb (x : ℝ) (hx : x ∈ Icc (0 : ℝ) 1) :
      warpSlope K x = warpSlope (fun _ => 2) x := by
    unfold warpSlope
    congr 2
    apply intervalIntegral.integral_congr
    intro y hy
    rw [uIcc_of_le hx.1] at hy
    exact hK y ⟨hy.1, hy.2.trans hx.2⟩
  have hm : probeMass (fun _ => 2) r = 1 := by
    rw [← h.2.2.2.2.2]
    unfold probeMass
    apply intervalIntegral.integral_congr
    intro x hx
    rw [uIcc_of_le zero_le_one] at hx
    dsimp only
    rw [hw x hx]
  have hA : meridionalAction K r = meridionalAction (fun _ => 2) r := by
    unfold meridionalAction
    apply intervalIntegral.integral_congr
    intro x hx
    rw [uIcc_of_le zero_le_one] at hx
    dsimp only
    rw [hw x hx, hb x hx, hK x hx]
  have hh := round_action_lower_bound r h.2.1
  rw [hm, mul_one] at hh
  exact hA.symm ▸ hh

/-- The cap-one smooth normalized problem has exact value four. -/
theorem smoothAreaInfimum_one : smoothAreaInfimum 1 = 4 := by
  apply le_antisymm (smoothAreaInfimum_le_four 1 le_rfl)
  apply le_csInf (smoothAreaActionValues_nonempty 1 le_rfl)
  rintro a ⟨K, r, h, rfl⟩
  exact cap_one_action_lower_bound h

end RicciFlowSharpEstimate.Geometry.AreaProfile

namespace RicciFlowSharpEstimate.Geometry
open AreaProfile

/-- The zero-action endpoint lies strictly above the round cap, so the actual
endpoint minimum meets the strict-cap hypothesis of moment qualification. -/
theorem one_lt_rotationalThreshold : 1 < rotationalThreshold := by
  apply lt_of_le_of_ne one_le_rotationalThreshold
  intro heq
  have hz := smoothAreaInfimum_rotationalThreshold
  rw [← heq, smoothAreaInfimum_one] at hz
  norm_num at hz

end RicciFlowSharpEstimate.Geometry
