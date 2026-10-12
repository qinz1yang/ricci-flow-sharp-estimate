/-
Copyright (c) 2026 Ziyang Qin. All rights reserved.
No license is granted by this file.
Authors: Ziyang Qin
-/
import RicciFlowSharpEstimate.Geometry.NormalizedAreaHaar

/-!
# Original-form variations under the fixed smooth area normalization

The geometry normalization is fixed before the original smooth probe directions.
Actual geometric action derivatives retain the complete Euler pairing at every
original scale, and cover the full smooth probe class through both poles.
-/

noncomputable section

namespace RicciFlowSharpEstimate.Geometry.RotationalProfile.PoleData.AreaNormalization

open Set MeasureTheory
open scoped ContDiff

variable {D : RotationalProfile.PoleData}

/-- Every original smooth probe variation has its complete geometric derivative
under the same fixed normalization, with no supplied compatibility equations. -/
theorem oneFormDissipation_meridional_hasDerivAt (N : AreaNormalization D)
    (R S : ℝ → ℝ) (hR : ContDiff ℝ ∞ R) (hS : ContDiff ℝ ∞ S) :
    HasDerivAt (fun t => oneFormDissipation D.metric
      (D.meridionalOneForm (fun v => R v + t * S v) (hR.add (contDiff_const.mul hS))))
      (4 * Real.pi * ∫ x in (0 : ℝ)..1, AreaProfile.warp N.curvature x * N.probe S x *
        AreaProfile.meridionalJacobiOperator N.curvature (N.probe R) x) 0 := by
  have heq : (fun t => oneFormDissipation D.metric
      (D.meridionalOneForm (fun v => R v + t * S v) (hR.add (contDiff_const.mul hS)))) =
      fun t => 2 * Real.pi * AreaProfile.meridionalAction N.curvature
        (fun x => N.probe R x + t * N.probe S x) := by
    funext t
    exact N.oneFormDissipation_meridional_eq _ (hR.add (contDiff_const.mul hS))
  rw [heq]
  convert (AreaProfile.meridionalAction_hasDerivAt N.curvature (N.probe R) (N.probe S)
    N.curvature_contDiff (N.probe_contDiff R hR) (N.probe_contDiff S hS)
    N.integral_curvature N.integral_mul_curvature).const_mul (2 * Real.pi) using 1
  ring

/-- Stationarity along every original smooth meridional direction is equivalent
to the complete smooth zero-mode equation, including both physical endpoints. -/
theorem oneFormDissipation_meridional_stationary_iff (N : AreaNormalization D)
    (R : ℝ → ℝ) (hR : ContDiff ℝ ∞ R) :
    (∀ S : ℝ → ℝ, ∀ hS : ContDiff ℝ ∞ S,
      deriv (fun t => oneFormDissipation D.metric
        (D.meridionalOneForm (fun v => R v + t * S v) (hR.add (contDiff_const.mul hS)))) 0 = 0) ↔
      ∀ x ∈ Icc (0 : ℝ) 1,
        AreaProfile.meridionalJacobiOperator N.curvature (N.probe R) x = 0 := by
  constructor
  · intro hstat
    apply (AreaProfile.meridionalAction_stationary_iff N.curvature (N.probe R)
      N.curvature_contDiff (N.probe_contDiff R hR) N.curvature_pos N.integral_curvature
      N.integral_mul_curvature).mp
    intro s hs
    let S := s ∘ ReciprocalArea.coordinate D.a
    have hS : ContDiff ℝ ∞ S := hs.comp
      (ReciprocalArea.coordinate_contDiff D.a D.a_contDiff)
    have h := hstat S hS
    rw [(N.oneFormDissipation_meridional_hasDerivAt R S hR hS).deriv] at h
    have hpair : (∫ x in (0 : ℝ)..1, AreaProfile.warp N.curvature x * N.probe S x *
        AreaProfile.meridionalJacobiOperator N.curvature (N.probe R) x) =
        ∫ x in (0 : ℝ)..1, AreaProfile.warp N.curvature x * s x *
          AreaProfile.meridionalJacobiOperator N.curvature (N.probe R) x := by
      apply intervalIntegral.integral_congr
      intro x hx
      have hx' : x ∈ Icc (0 : ℝ) 1 := by simpa using hx
      dsimp only [S]
      rw [N.probe_comp_coordinate s x hx']
    rw [hpair] at h
    have hpi : 4 * Real.pi ≠ 0 := mul_ne_zero (by norm_num) Real.pi_ne_zero
    have hi := (mul_eq_zero.mp h).resolve_left hpi
    rw [(AreaProfile.meridionalAction_hasDerivAt N.curvature (N.probe R) s
      N.curvature_contDiff (N.probe_contDiff R hR) hs N.integral_curvature
      N.integral_mul_curvature).deriv, hi, mul_zero]
  · intro heq S hS
    rw [(N.oneFormDissipation_meridional_hasDerivAt R S hR hS).deriv]
    have hi : (∫ x in (0 : ℝ)..1, AreaProfile.warp N.curvature x * N.probe S x *
        AreaProfile.meridionalJacobiOperator N.curvature (N.probe R) x) = 0 := by
      calc
        _ = ∫ _x in (0 : ℝ)..1, (0 : ℝ) := by
          apply intervalIntegral.integral_congr
          intro x hx
          have hx' : x ∈ Icc (0 : ℝ) 1 := by simpa using hx
          dsimp only
          rw [heq x hx', mul_zero]
        _ = 0 := by simp
    rw [hi, mul_zero]

open DifferentialGeometry
open scoped Manifold

local instance : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 2 + 1) :=
  ⟨finrank_euclideanSpace_fin⟩

/-- The same complete first variation holds on the represented original metric,
using the actual derivative pullback of the original varying form. -/
theorem oneFormDissipation_pullback_meridional_hasDerivAt (N : AreaNormalization D)
    (F : RotationalSphere ≃ₘ⟮𝓡 2, 𝓡 2⟯ RotationalSphere)
    (R S : ℝ → ℝ) (hR : ContDiff ℝ ∞ R) (hS : ContDiff ℝ ∞ S) :
    HasDerivAt (fun t => oneFormDissipation (Diffeomorph.pullbackMetric D.metric F)
      (diffeomorphTensorPullback F
        (D.meridionalOneForm (fun v => R v + t * S v) (hR.add (contDiff_const.mul hS)))))
      (4 * Real.pi * ∫ x in (0 : ℝ)..1, AreaProfile.warp N.curvature x * N.probe S x *
        AreaProfile.meridionalJacobiOperator N.curvature (N.probe R) x) 0 := by
  simpa only [oneFormDissipation_diffeomorphTensorPullback] using
    N.oneFormDissipation_meridional_hasDerivAt R S hR hS

end RicciFlowSharpEstimate.Geometry.RotationalProfile.PoleData.AreaNormalization
