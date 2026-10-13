/-
Copyright (c) 2026 Ziyang Qin. All rights reserved.
No license is granted by this file.
Authors: Ziyang Qin
-/
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Polar tails controlled by parabolic derivative energy

The unweighted square integral on each short polar interval is controlled by
the full square integral and the derivative energy with weight `x * (1 - x)`.
Two affine fluxes meet at the cutoff and vanish at the outer endpoints, so no
endpoint condition on the function or its derivative is required.
-/

noncomputable section

namespace RicciFlowSharpEstimate.Analysis

open MeasureTheory Set

private theorem polar_tent_sq_le (δ x h : ℝ)
    (hx : 0 ≤ x) (hh : 0 ≤ h) (hl : h ≤ x) (hr : h ≤ δ * (1 - x)) :
    h ^ 2 ≤ δ * (x * (1 - x)) := by
  have hprod := mul_le_mul hl hr hh hx
  nlinarith only [hprod]

private theorem polar_mixed_term_le (t w h u v : ℝ)
    (ht : 0 < t) (hh : h ^ 2 ≤ t ^ 2 * w) :
    -2 * (h * u * v) ≤ t * (u ^ 2 + w * v ^ 2) := by
  have hprod := mul_le_mul_of_nonneg_right hh (sq_nonneg v)
  apply (mul_le_mul_iff_right₀ ht).mp
  nlinarith only [hprod, sq_nonneg (t * u + h * v)]

private theorem integral_polar_affine_sq_flux
    (r : ℝ → ℝ) (hr : ContDiff ℝ 1 r) (a b c d : ℝ) :
    c * (∫ x in a..b, r x ^ 2) +
        2 * (∫ x in a..b, (c * x + d) * r x * deriv r x) =
      (c * b + d) * r b ^ 2 - (c * a + d) * r a ^ 2 := by
  have hU : IntervalIntegrable (fun x => r x ^ 2) volume a b :=
    (hr.continuous.pow 2).intervalIntegrable a b
  have hC : IntervalIntegrable
      (fun x => (c * x + d) * r x * deriv r x) volume a b :=
    ((((continuous_const.mul continuous_id).add continuous_const).mul
      hr.continuous).mul hr.continuous_deriv_one).intervalIntegrable a b
  have hderiv (x : ℝ) :
      HasDerivAt (fun y : ℝ => (c * y + d) * r y ^ 2)
        (c * r x ^ 2 + 2 * ((c * x + d) * r x * deriv r x)) x := by
    have hlinear : HasDerivAt (fun y : ℝ => c * y + d) c x := by
      simpa only [id_eq, mul_one] using
        ((hasDerivAt_id x).const_mul c).add_const d
    convert hlinear.mul
      (((hr.differentiable (by norm_num)) x).hasDerivAt.pow 2) using 1
    simp only [Pi.pow_apply]
    ring
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun x _ => hderiv x) ((hU.const_mul c).add (hC.const_mul 2))
  rw [intervalIntegral.integral_add (hU.const_mul c) (hC.const_mul 2),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul] at h
  exact h

/-- The unweighted square integral near the left pole is small when the cutoff
is at most the square of the energy parameter. No endpoint conditions are imposed. -/
theorem integral_left_sq_le_parabolic_energy
    (r : ℝ → ℝ) (hr : ContDiff ℝ 1 r) {δ t : ℝ}
    (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1) (ht : 0 < t) (hδt : δ ≤ t ^ 2) :
    (∫ x in (0 : ℝ)..δ, r x ^ 2) ≤
      δ * (∫ x in (0 : ℝ)..1, r x ^ 2) +
        t * ((∫ x in (0 : ℝ)..1, r x ^ 2) +
          (∫ x in (0 : ℝ)..1, x * (1 - x) * (deriv r x) ^ 2)) := by
  have hU (a b : ℝ) : IntervalIntegrable (fun x => r x ^ 2) volume a b :=
    (hr.continuous.pow 2).intervalIntegrable a b
  have hH (a b : ℝ) :
      IntervalIntegrable (fun x => x * (1 - x) * (deriv r x) ^ 2) volume a b :=
    ((continuous_id.mul (continuous_const.sub continuous_id)).mul
      (hr.continuous_deriv_one.pow 2)).intervalIntegrable a b
  have hCL : IntervalIntegrable
      (fun x => (1 - δ) * x * r x * deriv r x) volume 0 δ :=
    (((continuous_const.mul continuous_id).mul hr.continuous).mul
      hr.continuous_deriv_one).intervalIntegrable 0 δ
  have hCR : IntervalIntegrable
      (fun x => (-δ * x + δ) * r x * deriv r x) volume δ 1 :=
    ((((continuous_const.mul continuous_id).add continuous_const).mul
      hr.continuous).mul hr.continuous_deriv_one).intervalIntegrable δ 1
  have hfluxL :
      (1 - δ) * (∫ x in (0 : ℝ)..δ, r x ^ 2) +
          2 * (∫ x in (0 : ℝ)..δ, (1 - δ) * x * r x * deriv r x) =
        (1 - δ) * δ * r δ ^ 2 := by
    simpa only [add_zero, mul_zero, zero_mul, sub_zero] using
      integral_polar_affine_sq_flux r hr 0 δ (1 - δ) 0
  have hfluxR :
      -δ * (∫ x in δ..1, r x ^ 2) +
          2 * (∫ x in δ..1, (-δ * x + δ) * r x * deriv r x) =
        -δ * (1 - δ) * r δ ^ 2 := by
    have h := integral_polar_affine_sq_flux r hr δ 1 (-δ) δ
    nlinarith only [h]
  have hpointL (x : ℝ) (hx : x ∈ Icc (0 : ℝ) δ) :
      -2 * ((1 - δ) * x * r x * deriv r x) ≤
        t * (r x ^ 2 + x * (1 - x) * (deriv r x) ^ 2) := by
    have hx1 : x ≤ 1 := hx.2.trans hδ1
    have hw : 0 ≤ x * (1 - x) := mul_nonneg hx.1 (sub_nonneg.mpr hx1)
    have hh : 0 ≤ (1 - δ) * x := mul_nonneg (sub_nonneg.mpr hδ1) hx.1
    have hl : (1 - δ) * x ≤ x := by
      nlinarith only [mul_nonneg hδ0 hx.1]
    have hr' : (1 - δ) * x ≤ δ * (1 - x) := by
      nlinarith only [hx.2]
    have hsq := polar_tent_sq_le δ x ((1 - δ) * x) hx.1 hh hl hr'
    exact polar_mixed_term_le t (x * (1 - x)) ((1 - δ) * x)
      (r x) (deriv r x) ht
      (hsq.trans (mul_le_mul_of_nonneg_right hδt hw))
  have hpointR (x : ℝ) (hx : x ∈ Icc δ (1 : ℝ)) :
      -2 * ((-δ * x + δ) * r x * deriv r x) ≤
        t * (r x ^ 2 + x * (1 - x) * (deriv r x) ^ 2) := by
    have hx0 : 0 ≤ x := hδ0.trans hx.1
    have hw : 0 ≤ x * (1 - x) := mul_nonneg hx0 (sub_nonneg.mpr hx.2)
    have hh : 0 ≤ -δ * x + δ := by
      nlinarith only [mul_nonneg hδ0 (sub_nonneg.mpr hx.2)]
    have hl : -δ * x + δ ≤ x := by
      nlinarith only [hx.1, mul_nonneg hδ0 hx0]
    have hr' : -δ * x + δ ≤ δ * (1 - x) := le_of_eq (by ring)
    have hsq := polar_tent_sq_le δ x (-δ * x + δ) hx0 hh hl hr'
    exact polar_mixed_term_le t (x * (1 - x)) (-δ * x + δ)
      (r x) (deriv r x) ht
      (hsq.trans (mul_le_mul_of_nonneg_right hδt hw))
  have hboundL := intervalIntegral.integral_mono_on hδ0 (hCL.const_mul (-2))
    (((hU 0 δ).add (hH 0 δ)).const_mul t) hpointL
  have hboundR := intervalIntegral.integral_mono_on hδ1 (hCR.const_mul (-2))
    (((hU δ 1).add (hH δ 1)).const_mul t) hpointR
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_add (hU 0 δ) (hH 0 δ)] at hboundL
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_add (hU δ 1) (hH δ 1)] at hboundR
  rw [← intervalIntegral.integral_add_adjacent_intervals (hU 0 δ) (hU δ 1),
    ← intervalIntegral.integral_add_adjacent_intervals (hH 0 δ) (hH δ 1)]
  nlinarith only [hfluxL, hfluxR, hboundL, hboundR]

/-- Both unweighted polar square integrals are controlled by the full square
integral and the parabolic derivative energy, without endpoint conditions. -/
theorem integral_polar_sq_le_parabolic_energy
    (r : ℝ → ℝ) (hr : ContDiff ℝ 1 r) {δ t : ℝ}
    (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1) (ht : 0 < t) (hδt : δ ≤ t ^ 2) :
    (∫ x in (0 : ℝ)..δ, r x ^ 2) + (∫ x in (1 - δ)..1, r x ^ 2) ≤
      2 * δ * (∫ x in (0 : ℝ)..1, r x ^ 2) +
        2 * t * ((∫ x in (0 : ℝ)..1, r x ^ 2) +
          (∫ x in (0 : ℝ)..1, x * (1 - x) * (deriv r x) ^ 2)) := by
  let s : ℝ → ℝ := fun x => r (1 - x)
  have hs : ContDiff ℝ 1 s := hr.comp (contDiff_const.sub contDiff_id)
  have hsderiv (x : ℝ) : deriv s x = -deriv r (1 - x) := by
    have h := (((hr.differentiable (by norm_num)) (1 - x)).hasDerivAt).comp x
      ((hasDerivAt_id x).const_sub 1)
    simpa only [s, Function.comp_def, id_eq, mul_neg_one] using h.deriv
  have hsL : (∫ x in (0 : ℝ)..δ, s x ^ 2) =
      ∫ x in (1 - δ)..1, r x ^ 2 := by
    simpa only [s, sub_zero] using
      (intervalIntegral.integral_comp_sub_left (a := (0 : ℝ)) (b := δ)
        (fun x => r x ^ 2) 1)
  have hsU : (∫ x in (0 : ℝ)..1, s x ^ 2) =
      ∫ x in (0 : ℝ)..1, r x ^ 2 := by
    simpa only [s, sub_self, sub_zero] using
      (intervalIntegral.integral_comp_sub_left (a := (0 : ℝ)) (b := 1)
        (fun x => r x ^ 2) 1)
  have hsH : (∫ x in (0 : ℝ)..1, x * (1 - x) * (deriv s x) ^ 2) =
      ∫ x in (0 : ℝ)..1, x * (1 - x) * (deriv r x) ^ 2 := by
    calc
      _ = ∫ x in (0 : ℝ)..1,
          (1 - x) * (1 - (1 - x)) * (deriv r (1 - x)) ^ 2 := by
        apply intervalIntegral.integral_congr
        intro x _
        change x * (1 - x) * deriv s x ^ 2 =
          (1 - x) * (1 - (1 - x)) * deriv r (1 - x) ^ 2
        rw [hsderiv]
        ring
      _ = _ := by
        simpa only [sub_self, sub_zero] using
          (intervalIntegral.integral_comp_sub_left (a := (0 : ℝ)) (b := 1)
            (fun x => x * (1 - x) * (deriv r x) ^ 2) 1)
  have hleft := integral_left_sq_le_parabolic_energy r hr hδ0 hδ1 ht hδt
  have hright := integral_left_sq_le_parabolic_energy s hs hδ0 hδ1 ht hδt
  rw [hsL, hsU, hsH] at hright
  linarith only [hleft, hright]

end RicciFlowSharpEstimate.Analysis
