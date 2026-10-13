/-
Copyright (c) 2026 Ziyang Qin. All rights reserved.
No license is granted by this file.
Authors: Ziyang Qin
-/
import RicciFlowSharpEstimate.Geometry.AreaActionPolarControl
import RicciFlowSharpEstimate.Analysis.ParabolicSobolev

/-!
# Uniform parabolic graph bounds on complete-action sublevels

The original complete action bounds the three actual graph coordinates on
the physical interval. No curvature derivative or probe boundary condition
is required.
-/

noncomputable section

namespace RicciFlowSharpEstimate.Geometry.AreaProfile

open Set MeasureTheory

local notation "areaμ" => volume.restrict (Ioo (0 : ℝ) 1)

private theorem parabolic_second_derivative_le (K r : ℝ → ℝ)
    (hK : Continuous K) (hr : ContDiff ℝ 2 r) (lo hi : ℝ) (hlo : 0 < lo)
    (hbox : ∀ x ∈ Icc (0 : ℝ) 1, lo ≤ K x ∧ K x ≤ hi)
    (hzero : (∫ x in (0 : ℝ)..1, K x) = 2)
    (hone : (∫ x in (0 : ℝ)..1, x * K x) = 1) :
    lo ^ 3 * (∫ x in (0 : ℝ)..1, (x * (1 - x)) ^ 3 * deriv (deriv r) x ^ 2) ≤
      2 * probeOperatorEnergy K r + 2 * hi ^ 2 * probeMass K r := by
  have hf := warp_continuous K hK
  have hr2 := hr.deriv'.continuous_deriv_one
  have hw : Continuous (fun x : ℝ => x * (1 - x)) := by fun_prop
  have hJ : lo ^ 3 * (∫ x in (0 : ℝ)..1, (x * (1 - x)) ^ 3 * deriv (deriv r) x ^ 2) ≤
      ∫ x in (0 : ℝ)..1, warp K x ^ 3 * deriv (deriv r) x ^ 2 := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_mono_on zero_le_one
      ((continuous_const.mul ((hw.pow 3).mul (hr2.pow 2))).intervalIntegrable 0 1)
      (((hf.pow 3).mul (hr2.pow 2)).intervalIntegrable 0 1)
    intro x hx
    have hbound := quadratic_le_warp_of_curvature_lower K hK lo
      (fun y hy => (hbox y hy).1) hzero hone x hx
    have hpos : 0 ≤ lo * x * (1 - x) :=
      mul_nonneg (mul_nonneg hlo.le hx.1) (sub_nonneg.mpr hx.2)
    have hs := pow_le_pow_left₀ hpos hbound 3
    have hm := mul_le_mul_of_nonneg_right hs (sq_nonneg (deriv (deriv r) x))
    simpa only [Pi.mul_apply, Pi.pow_apply, mul_pow, mul_assoc] using hm
  exact hJ.trans (integral_warp_cube_second_deriv_sq_le K r hK hr hi
    (fun x hx => ⟨hlo.le.trans (hbox x hx).1, (hbox x hx).2⟩) hzero hone)

/-- A single constant controls the ordinary L² probe, its first weighted
actual derivative, and its second weighted actual derivative throughout a
normalized complete-action sublevel. -/
theorem exists_uniform_parabolic_graph_bound (lo hi : ℝ) (hlo : 0 < lo) (hhi : 0 ≤ hi)
    (B : ℝ) : ∃ M > (0 : ℝ), ∀ K r : ℝ → ℝ,
      Continuous K → ContDiff ℝ 2 r →
      (∀ x ∈ Icc (0 : ℝ) 1, lo ≤ K x ∧ K x ≤ hi) →
      (∫ x in (0 : ℝ)..1, K x) = 2 → (∫ x in (0 : ℝ)..1, x * K x) = 1 →
      probeMass K r = 1 → meridionalAction K r ≤ B →
      (∫ x, r x ^ 2 ∂areaμ) ≤ M ∧
      (∫ x, (Real.sqrt (x * (1 - x)) * deriv r x) ^ 2 ∂areaμ) ≤ M ∧
      (∫ x, (x * (1 - x) * Real.sqrt (x * (1 - x)) * deriv (deriv r) x) ^ 2 ∂areaμ) ≤ M := by
  obtain ⟨D, hD, hbound⟩ := exists_uniform_probe_regularity_bound lo hi hlo hhi B
  let J := (2 * D + 2 * hi ^ 2) / lo ^ 3
  have hJ : 0 ≤ J := by dsimp [J]; positivity
  refine ⟨D + J, by positivity, ?_⟩
  intro K r hK hr hbox hzero hone hmass hA
  obtain ⟨hE, hU, _, hP⟩ := hbound K r hK hr hbox hzero hone hmass hA
  have hsecond := parabolic_second_derivative_le K r hK hr lo hi hlo hbox hzero hone
  rw [hmass, mul_one] at hsecond
  have hZ : (∫ x in (0 : ℝ)..1, (x * (1 - x)) ^ 3 * deriv (deriv r) x ^ 2) ≤ J := by
    apply (le_div_iff₀ (pow_pos hlo 3)).mpr
    nlinarith only [hsecond, hE]
  rw [intervalIntegral.integral_of_le zero_le_one, integral_Ioc_eq_integral_Ioo] at hU hP hZ
  have hpEq : (∫ x, (Real.sqrt (x * (1 - x)) * deriv r x) ^ 2 ∂areaμ) =
      ∫ x, x * (1 - x) * deriv r x ^ 2 ∂areaμ := by
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
    rw [mul_pow, Real.sq_sqrt (mul_nonneg hx.1.le (sub_nonneg.mpr hx.2.le))]
  have hzEq : (∫ x, (x * (1 - x) * Real.sqrt (x * (1 - x)) *
      deriv (deriv r) x) ^ 2 ∂areaμ) =
      ∫ x, (x * (1 - x)) ^ 3 * deriv (deriv r) x ^ 2 ∂areaμ := by
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
    have hs := Real.sq_sqrt (mul_nonneg hx.1.le (sub_nonneg.mpr hx.2.le))
    calc
      _ = (x * (1 - x)) ^ 2 * Real.sqrt (x * (1 - x)) ^ 2 *
          deriv (deriv r) x ^ 2 := by ring
      _ = _ := by rw [hs]; ring
  rw [hpEq, hzEq]
  exact ⟨hU.trans (le_add_of_nonneg_right hJ), hP.trans (le_add_of_nonneg_right hJ),
    hZ.trans (le_add_of_nonneg_left hD.le)⟩

end RicciFlowSharpEstimate.Geometry.AreaProfile
