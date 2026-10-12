/-
Copyright (c) 2026 Ziyang Qin. All rights reserved.
No license is granted by this file.
Authors: Ziyang Qin
-/
import RicciFlowSharpEstimate.Geometry.NormalizedAreaHaar

/-!
# The original geometric Rayleigh quotient in normalized area coordinates

The numerator is the complete dissipation of the original meridional one-form,
and its denominator is that same form's squared norm integrated against the
original metric volume. Their quotient has exactly the inverse squared original
area scale. Affine variations and local minimality use original smooth forms.
-/

noncomputable section

namespace RicciFlowSharpEstimate.Geometry.RotationalProfile.PoleData.AreaNormalization

open Set MeasureTheory
open DifferentialGeometry.Tensor0SBundle DifferentialGeometry.Integral.Measure
open scoped ContDiff Manifold

variable {D : RotationalProfile.PoleData}

private local instance : MeasurableSpace RotationalSphere := borel RotationalSphere
private local instance : BorelSpace RotationalSphere := ⟨rfl⟩

/-- The complete original geometric quotient has the actual inverse squared
area scale. Totalized real division makes the identity valid for zero forms too. -/
theorem oneFormDissipation_div_normSq_eq (N : AreaNormalization D)
    (R : ℝ → ℝ) (hR : ContDiff ℝ ∞ R) :
    oneFormDissipation D.metric (D.meridionalOneForm R hR) /
      (∫ p : RotationalSphere, normSq0S D.metric p 1 (D.meridionalOneForm R hR p)
        ∂(riemannianVolumeMeasure (I := 𝓡 2) (M := RotationalSphere) D.metric)) =
      AreaProfile.rayleighQuotient N.curvature (N.probe R) /
        (ReciprocalArea.length D.a) ^ 2 := by
  rw [N.oneFormDissipation_meridional_eq R hR, N.integral_normSq_eq_probeMass R hR]
  unfold AreaProfile.rayleighQuotient
  by_cases hm : AreaProfile.probeMass N.curvature (N.probe R) = 0
  · simp only [hm, mul_zero, div_zero, zero_div]
  · field_simp [hm, Real.pi_ne_zero,
      (ReciprocalArea.length_pos D.a D.a_contDiff.continuous D.a_pos).ne']

/-- The derivative of the literal original geometric quotient along the original
forms associated to `R + t S`. Nonvanishing is required of the actual base form. -/
theorem oneFormDissipation_div_normSq_hasDerivAt (N : AreaNormalization D)
    (R S : ℝ → ℝ) (hR : ContDiff ℝ ∞ R) (hS : ContDiff ℝ ∞ S)
    (hne : D.meridionalOneForm R hR ≠ 0) :
    HasDerivAt
      (fun t =>
        oneFormDissipation D.metric
            (D.meridionalOneForm (fun v => R v + t * S v)
              (hR.add (contDiff_const.mul hS))) /
          (∫ p : RotationalSphere, normSq0S D.metric p 1
            (D.meridionalOneForm (fun v => R v + t * S v)
              (hR.add (contDiff_const.mul hS)) p)
            ∂(riemannianVolumeMeasure (I := 𝓡 2) (M := RotationalSphere) D.metric)))
      (2 / ((ReciprocalArea.length D.a) ^ 2 *
          AreaProfile.probeMass N.curvature (N.probe R)) *
        (∫ x in (0 : ℝ)..1, AreaProfile.warp N.curvature x * N.probe S x *
          (AreaProfile.meridionalJacobiOperator N.curvature (N.probe R) x -
            AreaProfile.rayleighQuotient N.curvature (N.probe R) * N.probe R x))) 0 := by
  have hm := (N.probeMass_pos_iff_meridional_ne_zero R hR).mpr hne
  have hL := ReciprocalArea.length_pos D.a D.a_contDiff.continuous D.a_pos
  have hQ := (AreaProfile.rayleighQuotient_hasDerivAt N.curvature (N.probe R)
    (N.probe S) N.curvature_contDiff (N.probe_contDiff R hR) (N.probe_contDiff S hS)
    N.integral_curvature N.integral_mul_curvature hm.ne').div_const
      ((ReciprocalArea.length D.a) ^ 2)
  have hScaled : HasDerivAt
      (fun t => AreaProfile.rayleighQuotient N.curvature
        (fun x => N.probe R x + t * N.probe S x) / (ReciprocalArea.length D.a) ^ 2)
      (2 / ((ReciprocalArea.length D.a) ^ 2 *
          AreaProfile.probeMass N.curvature (N.probe R)) *
        (∫ x in (0 : ℝ)..1, AreaProfile.warp N.curvature x * N.probe S x *
          (AreaProfile.meridionalJacobiOperator N.curvature (N.probe R) x -
            AreaProfile.rayleighQuotient N.curvature (N.probe R) * N.probe R x))) 0 := by
    convert hQ using 1
    field_simp [hm.ne', hL.ne']
  apply hScaled.congr_of_eventuallyEq
  filter_upwards [] with t
  exact N.oneFormDissipation_div_normSq_eq (fun v => R v + t * S v)
    (hR.add (contDiff_const.mul hS))

/-- Local minimality of the actual original quotient along every smooth original
meridional direction forces its Rayleigh eigen-equation, including both poles.
This necessary condition does not assert that a minimizing form exists. -/
theorem oneFormDissipation_div_normSq_euler_eq_of_isLocalMin (N : AreaNormalization D)
    (R : ℝ → ℝ) (hR : ContDiff ℝ ∞ R) (hne : D.meridionalOneForm R hR ≠ 0)
    (hmin : ∀ (S : ℝ → ℝ) (hS : ContDiff ℝ ∞ S),
      IsLocalMin
        (fun t =>
          oneFormDissipation D.metric
              (D.meridionalOneForm (fun v => R v + t * S v)
                (hR.add (contDiff_const.mul hS))) /
            (∫ p : RotationalSphere, normSq0S D.metric p 1
              (D.meridionalOneForm (fun v => R v + t * S v)
                (hR.add (contDiff_const.mul hS)) p)
              ∂(riemannianVolumeMeasure (I := 𝓡 2) (M := RotationalSphere) D.metric))) 0) :
    ∀ x ∈ Icc (0 : ℝ) 1,
      AreaProfile.meridionalJacobiOperator N.curvature (N.probe R) x =
        AreaProfile.rayleighQuotient N.curvature (N.probe R) * N.probe R x := by
  have hm := (N.probeMass_pos_iff_meridional_ne_zero R hR).mpr hne
  apply (AreaProfile.rayleighQuotient_stationary_iff N.curvature (N.probe R)
    N.curvature_contDiff (N.probe_contDiff R hR) N.curvature_pos N.integral_curvature
    N.integral_mul_curvature hm).mp
  intro s hs
  let S : ℝ → ℝ := s ∘ ReciprocalArea.coordinate D.a
  have hS : ContDiff ℝ ∞ S := hs.comp
    (ReciprocalArea.coordinate_contDiff D.a D.a_contDiff)
  have h := (hmin S hS).hasDerivAt_eq_zero
    (N.oneFormDissipation_div_normSq_hasDerivAt R S hR hS hne)
  have hL := ReciprocalArea.length_pos D.a D.a_contDiff.continuous D.a_pos
  have hcoeff : 2 / ((ReciprocalArea.length D.a) ^ 2 *
      AreaProfile.probeMass N.curvature (N.probe R)) ≠ 0 :=
    div_ne_zero (by norm_num) (mul_ne_zero (pow_ne_zero 2 hL.ne') hm.ne')
  have hpair := (mul_eq_zero.mp h).resolve_left hcoeff
  have heq : (∫ x in (0 : ℝ)..1, AreaProfile.warp N.curvature x * N.probe S x *
      (AreaProfile.meridionalJacobiOperator N.curvature (N.probe R) x -
        AreaProfile.rayleighQuotient N.curvature (N.probe R) * N.probe R x)) =
      ∫ x in (0 : ℝ)..1, AreaProfile.warp N.curvature x * s x *
        (AreaProfile.meridionalJacobiOperator N.curvature (N.probe R) x -
          AreaProfile.rayleighQuotient N.curvature (N.probe R) * N.probe R x) := by
    apply intervalIntegral.integral_congr
    intro x hx
    have hx' : x ∈ Icc (0 : ℝ) 1 := by simpa using hx
    dsimp only [S]
    rw [N.probe_comp_coordinate s x hx']
  rw [heq] at hpair
  rw [(AreaProfile.rayleighQuotient_hasDerivAt N.curvature (N.probe R) s
    N.curvature_contDiff (N.probe_contDiff R hR) hs N.integral_curvature
    N.integral_mul_curvature hm.ne').deriv, hpair, mul_zero]

end RicciFlowSharpEstimate.Geometry.RotationalProfile.PoleData.AreaNormalization
