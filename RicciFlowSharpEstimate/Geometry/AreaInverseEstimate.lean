/-
Copyright (c) 2026 Ziyang Qin. All rights reserved.
No license is granted by this file.
Authors: Ziyang Qin
-/
import RicciFlowSharpEstimate.Geometry.AreaProbeRegularity

/-!
# Uniform graph estimate for the actual meridional operator

A positive lower curvature bound makes the operator square control the physical
probe mass and gradient. The actual weighted pairing and the existing Hardy
estimates then control all three parabolic graph coordinates, without a mass
normalization or a boundary condition on the probe.
-/

noncomputable section

namespace RicciFlowSharpEstimate.Geometry.AreaProfile

open Set MeasureTheory
open scoped ContDiff

/-- The actual operator energy controls the physical mass and gradient on a
nonnegative curvature lower bound. The pole fluxes vanish through the warp,
without imposing boundary values on the probe. -/
theorem probeMass_gradient_le_probeOperatorEnergy (K r : ℝ → ℝ)
    (hK : Continuous K) (hr : ContDiff ℝ 2 r) (lo : ℝ) (hlo : 0 ≤ lo)
    (hlower : ∀ x ∈ Icc (0 : ℝ) 1, lo ≤ K x)
    (hzero : (∫ x in (0 : ℝ)..1, K x) = 2)
    (hone : (∫ x in (0 : ℝ)..1, x * K x) = 1) :
    lo ^ 2 * probeMass K r + 2 * lo * probeGradientEnergy K r ≤
      probeOperatorEnergy K r := by
  have hf := warp_continuous K hK
  have hr0 := hr.continuous
  have hL := meridionalOperator_continuous_of_contDiff_two K r hK hr
  have hF : Continuous (fun x => warp K x * r x * meridionalOperator K r x) := by fun_prop
  have hE : Continuous (fun x => warp K x * meridionalOperator K r x ^ 2) := by fun_prop
  have hM : Continuous (fun x => warp K x * r x ^ 2) := by fun_prop
  have hT : Continuous (fun x => warp K x * K x * r x ^ 2) := by fun_prop
  have hf0 (x : ℝ) (hx : x ∈ Icc (0 : ℝ) 1) : 0 ≤ warp K x :=
    (warp_nonneg_le_two_mul_min K hK (fun y hy => hlo.trans (hlower y hy))
      hzero hone x hx).1
  have hsq : 0 ≤ ∫ x in (0 : ℝ)..1,
      2 * lo * (warp K x * r x * meridionalOperator K r x) +
        warp K x * meridionalOperator K r x ^ 2 + lo ^ 2 * (warp K x * r x ^ 2) := by
    apply intervalIntegral.integral_nonneg zero_le_one
    intro x hx
    have h := mul_nonneg (hf0 x hx) (sq_nonneg (meridionalOperator K r x + lo * r x))
    nlinarith only [h]
  have hFE : IntervalIntegrable (fun x =>
      2 * lo * (warp K x * r x * meridionalOperator K r x) +
        warp K x * meridionalOperator K r x ^ 2) volume 0 1 :=
    ((hF.const_mul (2 * lo)).add hE).intervalIntegrable 0 1
  rw [intervalIntegral.integral_add hFE ((hM.const_mul (lo ^ 2)).intervalIntegrable 0 1),
    intervalIntegral.integral_add ((hF.const_mul (2 * lo)).intervalIntegrable 0 1)
      (hE.intervalIntegrable 0 1),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    integral_warp_mul_probe_operator K r hK hr hzero hone] at hsq
  change 0 ≤ 2 * lo * (-probeGradientEnergy K r -
    (∫ x in (0 : ℝ)..1, warp K x * K x * r x ^ 2)) +
      probeOperatorEnergy K r + lo ^ 2 * probeMass K r at hsq
  have hpot : lo * probeMass K r ≤
      ∫ x in (0 : ℝ)..1, warp K x * K x * r x ^ 2 := by
    unfold probeMass
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_mono_on zero_le_one
      ((hM.const_mul lo).intervalIntegrable 0 1) (hT.intervalIntegrable 0 1)
    intro x hx
    have h := mul_le_mul_of_nonneg_right (hlower x hx)
      (mul_nonneg (hf0 x hx) (sq_nonneg (r x)))
    nlinarith only [h]
  have hpotScaled := mul_le_mul_of_nonneg_left hpot
    (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hlo)
  nlinarith only [hsq, hpotScaled]

private theorem inverse_parabolic_second_derivative_le (K r : ℝ → ℝ)
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

/-- A constant depending only on a positive curvature box controls the full
parabolic graph norm of each actual C² probe by its actual operator energy.
Neither a mass normalization nor a probe pole condition is required. -/
theorem exists_uniform_meridional_inverse_graph_bound
    (lo hi : ℝ) (hlo : 0 < lo) :
    ∃ M > (0 : ℝ), ∀ K r : ℝ → ℝ,
      Continuous K → ContDiff ℝ 2 r →
      (∀ x ∈ Icc (0 : ℝ) 1, lo ≤ K x ∧ K x ≤ hi) →
      (∫ x in (0 : ℝ)..1, K x) = 2 → (∫ x in (0 : ℝ)..1, x * K x) = 1 →
      (∫ x in (0 : ℝ)..1, r x ^ 2) +
        (∫ x in (0 : ℝ)..1, x * (1 - x) * deriv r x ^ 2) +
        (∫ x in (0 : ℝ)..1, (x * (1 - x)) ^ 3 * deriv (deriv r) x ^ 2) ≤
          M * probeOperatorEnergy K r := by
  let C := 12 * lo ^ 2 +
    (lo ^ 2 * (10 * lo + 2) + (5 * lo / 2 + 2 * hi ^ 2)) + 2 * (lo ^ 2 + hi ^ 2)
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C / lo ^ 5, div_pos hC (pow_pos hlo 5), ?_⟩
  intro K r hK hr hbox hzero hone
  have hcoercive := probeMass_gradient_le_probeOperatorEnergy K r hK hr lo hlo.le
    (fun x hx => (hbox x hx).1) hzero hone
  have hgrad0 : 0 ≤ lo * probeGradientEnergy K r :=
    mul_nonneg hlo.le (probeGradientEnergy_nonneg K r)
  have hmass : lo ^ 2 * probeMass K r ≤ probeOperatorEnergy K r := by
    nlinarith only [hcoercive, hgrad0]
  have hHardy := integral_sq_le_probeMass_gradient K r hK (hr.of_le (by norm_num))
    lo hlo.le (fun x hx => (hbox x hx).1) hzero hone
  have hHardyScaled := mul_le_mul_of_nonneg_left hHardy hlo.le
  have hcoerciveScaled := mul_le_mul_of_nonneg_left hcoercive (by norm_num : (0 : ℝ) ≤ 12)
  have hU : lo ^ 3 * (∫ x in (0 : ℝ)..1, r x ^ 2) ≤
      12 * probeOperatorEnergy K r := by
    nlinarith only [hHardyScaled, hcoerciveScaled, hgrad0]
  have hUScaled : lo ^ 5 * (∫ x in (0 : ℝ)..1, r x ^ 2) ≤
      12 * lo ^ 2 * probeOperatorEnergy K r := by
    nlinarith only [mul_le_mul_of_nonneg_left hU (sq_nonneg lo)]
  have hhi2 : 0 ≤ hi ^ 2 := sq_nonneg hi
  have hPcoeff : 0 ≤ 5 * lo / 2 + 2 * hi ^ 2 :=
    add_nonneg (div_nonneg (mul_nonneg (by norm_num) hlo.le) (by norm_num))
      (mul_nonneg (by norm_num) hhi2)
  have hP := integral_parabolic_deriv_sq_le K r hK hr lo hi hlo hbox hzero hone
  have hPScaled := mul_le_mul_of_nonneg_left hP (sq_nonneg lo)
  have hPMass := mul_le_mul_of_nonneg_left hmass hPcoeff
  have hPBound : lo ^ 5 * (∫ x in (0 : ℝ)..1, x * (1 - x) * deriv r x ^ 2) ≤
      (lo ^ 2 * (10 * lo + 2) + (5 * lo / 2 + 2 * hi ^ 2)) *
        probeOperatorEnergy K r := by
    nlinarith only [hPScaled, hPMass]
  have hZ := inverse_parabolic_second_derivative_le K r hK hr lo hi hlo hbox hzero hone
  have hZScaled := mul_le_mul_of_nonneg_left hZ (sq_nonneg lo)
  have hZMass := mul_le_mul_of_nonneg_left hmass
    (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hhi2)
  have hZBound : lo ^ 5 *
      (∫ x in (0 : ℝ)..1, (x * (1 - x)) ^ 3 * deriv (deriv r) x ^ 2) ≤
        2 * (lo ^ 2 + hi ^ 2) * probeOperatorEnergy K r := by
    nlinarith only [hZScaled, hZMass]
  have hsum : lo ^ 5 * ((∫ x in (0 : ℝ)..1, r x ^ 2) +
      (∫ x in (0 : ℝ)..1, x * (1 - x) * deriv r x ^ 2) +
      (∫ x in (0 : ℝ)..1, (x * (1 - x)) ^ 3 * deriv (deriv r) x ^ 2)) ≤
        C * probeOperatorEnergy K r := by
    dsimp [C]
    nlinarith only [hUScaled, hPBound, hZBound]
  have hquot : (∫ x in (0 : ℝ)..1, r x ^ 2) +
      (∫ x in (0 : ℝ)..1, x * (1 - x) * deriv r x ^ 2) +
      (∫ x in (0 : ℝ)..1, (x * (1 - x)) ^ 3 * deriv (deriv r) x ^ 2) ≤
        C * probeOperatorEnergy K r / lo ^ 5 := by
    apply (le_div_iff₀ (pow_pos hlo 5)).mpr
    nlinarith only [hsum]
  simpa only [div_mul_eq_mul_div] using hquot

end RicciFlowSharpEstimate.Geometry.AreaProfile
