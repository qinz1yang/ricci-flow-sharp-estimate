/-
Copyright (c) 2026 Ziyang Qin. All rights reserved.
No license is granted by this file.
Authors: Ziyang Qin
-/
import RicciFlowSharpEstimate.Geometry.SmoothAreaNormalization
import RicciFlowSharpEstimate.Analysis.ClosedIntervalDerivatives
import RicciFlowSharpEstimate.Geometry.RotationalMeridionalReduction
import RicciFlowSharpEstimate.Geometry.AreaActionFactorization

/-!
# Complete general-probe action transport from original geometry

All first and second derivatives come from the actual transported probe. The
original coordinate Jacobian cancels the geometry scale in every density term.
Physical values, jets and action are independent of the smooth extension choice.
-/

noncomputable section

namespace RicciFlowSharpEstimate.Geometry.AreaProfile

open Set MeasureTheory
open scoped ContDiff

/-- The complete normalized area action is independent of the smooth probe's
extension outside the physical interval. -/
theorem meridionalAction_congr (K r s : ℝ → ℝ) (hr : ContDiff ℝ ∞ r)
    (hs : ContDiff ℝ ∞ s) (heq : EqOn r s (Icc (0 : ℝ) 1)) :
    meridionalAction K r = meridionalAction K s := by
  obtain ⟨hd, hdd⟩ := Analysis.eqOn_derivatives_Icc 0 1 zero_lt_one r s
    (hr.of_le (by simp)) (hs.of_le (by simp)) heq
  unfold meridionalAction
  apply intervalIntegral.integral_congr
  intro x hx
  have hx' : x ∈ Icc (0 : ℝ) 1 := by simpa using hx
  dsimp only
  rw [heq hx', hd hx', hdd hx']

end RicciFlowSharpEstimate.Geometry.AreaProfile

namespace RicciFlowSharpEstimate.Geometry.RotationalProfile.PoleData.AreaNormalization

open Set MeasureTheory
open scoped ContDiff

variable {D : RotationalProfile.PoleData}

/-- Every smooth original probe is transported by the same smooth inverse. -/
theorem probe_contDiff (N : AreaNormalization D) (R : ℝ → ℝ) (hR : ContDiff ℝ ∞ R) :
    ContDiff ℝ ∞ (N.probe R) := hR.comp N.inverse_contDiff

/-- The transported probe retains every physical value, including both endpoints. -/
theorem probe_coordinate (N : AreaNormalization D) (R : ℝ → ℝ) (v : ℝ)
    (hv : v ∈ Icc (-1 : ℝ) 1) : N.probe R (ReciprocalArea.coordinate D.a v) = R v := by
  simp only [probe, Function.comp_apply, N.inverse_coordinate v hv]

/-- The actual first derivative of the transported probe. -/
theorem deriv_probe (N : AreaNormalization D) (R : ℝ → ℝ) (hR : ContDiff ℝ ∞ R)
    (x : ℝ) : deriv (N.probe R) x = N.curvature x * deriv R (N.inverse x) := by
  have h := ((hR.differentiable (by simp) (N.inverse x)).hasDerivAt).comp x
    (N.inverse_hasDerivAt x)
  simpa only [probe, mul_comm] using h.deriv

/-- The actual second derivative is derived from the same curvature and probe. -/
theorem deriv_deriv_probe (N : AreaNormalization D) (R : ℝ → ℝ)
    (hR : ContDiff ℝ ∞ R) (x : ℝ) :
    deriv (deriv (N.probe R)) x =
      N.curvature x ^ 2 * deriv (deriv R) (N.inverse x) +
        deriv N.curvature x * deriv R (N.inverse x) := by
  have hR1 := (contDiff_infty_iff_deriv.mp hR).2
  have hfun : deriv (N.probe R) = fun y => N.curvature y * deriv R (N.inverse y) :=
    funext (N.deriv_probe R hR)
  rw [hfun]
  have h := ((N.curvature_contDiff.differentiable (by simp) x).hasDerivAt).mul
    (((hR1.differentiable (by simp) (N.inverse x)).hasDerivAt).comp x (N.inverse_hasDerivAt x))
  convert h.deriv using 1
  · rfl
  · simp only [Function.comp_apply]
    ring

/-- Differentiation of the original scaled curvature equation is valid at both poles. -/
theorem curvature_deriv_coordinate (N : AreaNormalization D) (v : ℝ)
    (hv : v ∈ Icc (-1 : ℝ) 1) :
    deriv N.curvature (ReciprocalArea.coordinate D.a v) =
      -(ReciprocalArea.length D.a) ^ 2 * deriv D.a v / D.a v ^ 3 := by
  have ha := (D.a_pos v hv).ne'
  have hL := (ReciprocalArea.length_pos D.a D.a_contDiff.continuous D.a_pos).ne'
  have hleft := ((N.curvature_contDiff.differentiable (by simp)
    (ReciprocalArea.coordinate D.a v)).hasDerivAt).comp v
      (ReciprocalArea.coordinate_hasDerivAt D.a D.a_contDiff.continuous v)
  have hright : HasDerivAt (fun y => ReciprocalArea.length D.a / D.a y)
      (-(ReciprocalArea.length D.a) * deriv D.a v / D.a v ^ 2) v := by
    convert (hasDerivAt_const v (ReciprocalArea.length D.a)).div
      ((D.a_contDiff.differentiable (by simp) v).hasDerivAt) ha using 1
    ring
  have heq := (uniqueDiffOn_Icc (by norm_num : (-1 : ℝ) < 1) v hv).eq_deriv _
    (hleft.hasDerivWithinAt.congr_of_mem (fun y hy => (N.curvature_coordinate y hy).symm) hv)
    hright.hasDerivWithinAt
  field_simp [ha, hL] at heq ⊢
  nlinarith [heq]

/-- Every actual second-order probe term has its exact original scale. -/
theorem meridionalOperator_coordinate (N : AreaNormalization D)
    (R : ℝ → ℝ) (hR : ContDiff ℝ ∞ R) (v : ℝ) (hv : v ∈ Icc (-1 : ℝ) 1) :
    AreaProfile.meridionalOperator N.curvature (N.probe R) (ReciprocalArea.coordinate D.a v) =
      (ReciprocalArea.length D.a / D.a v) * D.meridionalOperator R v := by
  unfold AreaProfile.meridionalOperator
  rw [N.deriv_deriv_probe R hR, N.deriv_probe R hR, N.probe_coordinate R v hv,
    N.warp_coordinate v hv, N.warpSlope_coordinate v hv, N.inverse_coordinate v hv,
    N.curvature_coordinate v hv, N.curvature_deriv_coordinate v hv]
  rw [meridionalOperator, (D.meridionalWeight_hasDerivAt v hv).deriv]
  unfold meridionalWeight
  field_simp [(D.a_pos v hv).ne',
    (ReciprocalArea.length_pos D.a D.a_contDiff.continuous D.a_pos).ne']
  ring

/-- The actual normalized-coordinate Jacobian cancels every scale factor in
all terms of the complete general-probe density. -/
theorem meridionalDensity_coordinate (N : AreaNormalization D)
    (R : ℝ → ℝ) (hR : ContDiff ℝ ∞ R) (v : ℝ) (hv : v ∈ Icc (-1 : ℝ) 1) :
    AreaProfile.meridionalActionDensity
      (AreaProfile.warp N.curvature (ReciprocalArea.coordinate D.a v))
      (AreaProfile.warpSlope N.curvature (ReciprocalArea.coordinate D.a v))
      (N.curvature (ReciprocalArea.coordinate D.a v))
      (N.probe R (ReciprocalArea.coordinate D.a v))
      (deriv (N.probe R) (ReciprocalArea.coordinate D.a v))
      (deriv (deriv (N.probe R)) (ReciprocalArea.coordinate D.a v)) *
        (D.a v / ReciprocalArea.length D.a) = D.meridionalDensity R v := by
  let x := ReciprocalArea.coordinate D.a v
  change (AreaProfile.warp N.curvature x *
      (AreaProfile.meridionalOperator N.curvature (N.probe R) x) ^ 2 -
    N.curvature x * AreaProfile.warpSlope N.curvature x * N.probe R x *
      (AreaProfile.warp N.curvature x * deriv (N.probe R) x +
        AreaProfile.warpSlope N.curvature x * N.probe R x / 2) +
    N.curvature x ^ 2 * AreaProfile.warp N.curvature x * (N.probe R x) ^ 2) *
      (D.a v / ReciprocalArea.length D.a) = _
  dsimp only [x]
  rw [N.meridionalOperator_coordinate R hR v hv, N.deriv_probe R hR,
    N.probe_coordinate R v hv, N.warp_coordinate v hv, N.warpSlope_coordinate v hv,
    N.curvature_coordinate v hv, N.inverse_coordinate v hv]
  unfold meridionalDensity meridionalWeight
  field_simp [(D.a_pos v hv).ne',
    (ReciprocalArea.length_pos D.a D.a_contDiff.continuous D.a_pos).ne']
  ring

/-- Complete action transport from every original smooth probe, at every original scale. -/
theorem meridionalAction_eq (N : AreaNormalization D) (R : ℝ → ℝ)
    (hR : ContDiff ℝ ∞ R) :
    AreaProfile.meridionalAction N.curvature (N.probe R) = D.meridionalAction R := by
  have hG := AreaProfile.meridionalAction_integrand_continuous N.curvature
    (N.probe R) N.curvature_contDiff.continuous (N.probe_contDiff R hR)
  have hsub := ReciprocalArea.integral_comp_coordinate D.a D.a_contDiff.continuous D.a_pos
    (fun x => AreaProfile.meridionalActionDensity (AreaProfile.warp N.curvature x)
      (AreaProfile.warpSlope N.curvature x) (N.curvature x) (N.probe R x)
      (deriv (N.probe R) x) (deriv (deriv (N.probe R)) x)) hG
  rw [AreaProfile.meridionalAction, ← hsub, meridionalAction]
  apply intervalIntegral.integral_congr
  intro v hv
  exact N.meridionalDensity_coordinate R hR v (by simpa using hv)

/-- The original metric and the original one-form retain the full normalized action. -/
theorem oneFormDissipation_meridional_eq (N : AreaNormalization D) (R : ℝ → ℝ)
    (hR : ContDiff ℝ ∞ R) :
    oneFormDissipation D.metric (D.meridionalOneForm R hR) =
      2 * Real.pi * AreaProfile.meridionalAction N.curvature (N.probe R) := by
  rw [D.oneFormDissipation_meridional R hR, N.meridionalAction_eq R hR]

/-- Two choices of smooth curvature extension agree at every physical point. -/
theorem curvature_eq_on (N M : AreaNormalization D) :
    EqOn N.curvature M.curvature (Icc (0 : ℝ) 1) := fun _ hx =>
  (N.curvature_eq hx).trans (M.curvature_eq hx).symm

/-- The actual derivatives of the curvature extensions also agree through both poles. -/
theorem curvature_deriv_eq_on (N M : AreaNormalization D) :
    EqOn (deriv N.curvature) (deriv M.curvature) (Icc (0 : ℝ) 1) :=
  (Analysis.eqOn_derivatives_Icc 0 1 zero_lt_one N.curvature M.curvature
    (N.curvature_contDiff.of_le (by simp)) (M.curvature_contDiff.of_le (by simp))
    (N.curvature_eq_on M)).1

/-- Physical inverse values are independent of the smooth extension choice. -/
theorem inverse_eq_on (N M : AreaNormalization D) :
    EqOn N.inverse M.inverse (Icc (0 : ℝ) 1) := fun x hx =>
  (N.inverse_eq x hx).trans (M.inverse_eq x hx).symm

/-- All transported physical probe values are independent of the geometry extension choice. -/
theorem probe_eq_on (N M : AreaNormalization D) (R : ℝ → ℝ) :
    EqOn (N.probe R) (M.probe R) (Icc (0 : ℝ) 1) := by
  intro x hx
  simp only [probe, Function.comp_apply, N.inverse_eq_on M hx]

/-- Both actual transported probe jets are independent of the geometry extension choice. -/
theorem probe_derivatives_eq_on (N M : AreaNormalization D) (R : ℝ → ℝ)
    (hR : ContDiff ℝ ∞ R) :
    EqOn (deriv (N.probe R)) (deriv (M.probe R)) (Icc (0 : ℝ) 1) ∧
      EqOn (deriv (deriv (N.probe R))) (deriv (deriv (M.probe R))) (Icc (0 : ℝ) 1) :=
  Analysis.eqOn_derivatives_Icc 0 1 zero_lt_one _ _ ((N.probe_contDiff R hR).of_le (by simp))
    ((M.probe_contDiff R hR).of_le (by simp)) (N.probe_eq_on M R)

/-- The complete general-probe action is independent of both smooth geometry extensions. -/
theorem meridionalAction_extension_independent (N M : AreaNormalization D)
    (R : ℝ → ℝ) (hR : ContDiff ℝ ∞ R) :
    AreaProfile.meridionalAction N.curvature (N.probe R) =
      AreaProfile.meridionalAction M.curvature (M.probe R) :=
  (N.meridionalAction_eq R hR).trans (M.meridionalAction_eq R hR).symm

/-- Pulling any area probe back by the fixed coordinate and transporting it again
recovers the original area probe throughout the physical interval. -/
theorem probe_comp_coordinate (N : AreaNormalization D) (r : ℝ → ℝ)
    (x : ℝ) (hx : x ∈ Icc (0 : ℝ) 1) :
    N.probe (r ∘ ReciprocalArea.coordinate D.a) x = r x := by
  simp only [probe, Function.comp_apply, N.coordinate_inverse x hx]

/-- Every smooth area probe is represented by a smooth height probe of this same
original metric, with its complete action preserved. -/
theorem meridionalAction_comp_coordinate (N : AreaNormalization D)
    (r : ℝ → ℝ) (hr : ContDiff ℝ ∞ r) :
    AreaProfile.meridionalAction N.curvature r =
      D.meridionalAction (r ∘ ReciprocalArea.coordinate D.a) := by
  have hR := hr.comp (ReciprocalArea.coordinate_contDiff D.a D.a_contDiff)
  rw [← N.meridionalAction_eq _ hR]
  exact AreaProfile.meridionalAction_congr _ _ _ hr (N.probe_contDiff _ hR)
    (fun x hx => (N.probe_comp_coordinate r x hx).symm)

end RicciFlowSharpEstimate.Geometry.RotationalProfile.PoleData.AreaNormalization
