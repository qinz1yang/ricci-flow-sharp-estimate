/-
Copyright (c) 2026 Ziyang Qin. All rights reserved.
No license is granted by this file.
Authors: Ziyang Qin
-/
import RicciFlowSharpEstimate.Geometry.AreaProbeRayleigh

/-!
# Affine curvature primitives and mass under integrability

The actual warp and slope are affine in integrable curvature coefficients on
the physical interval. Both normalized moments are preserved, and the actual
weighted probe mass is affine with the literal difference-density derivative.
-/

noncomputable section

namespace RicciFlowSharpEstimate.Geometry.AreaProfile

open MeasureTheory Set

private theorem affine_intervalIntegrable_of_integrableOn
    (K : ℝ → ℝ) (hK : IntegrableOn K (Ioo (0 : ℝ) 1)) :
    IntervalIntegrable K volume 0 1 :=
  (intervalIntegrable_iff_integrableOn_Ioo_of_le (by norm_num : (0 : ℝ) ≤ 1)).2 hK

private theorem affine_intervalIntegrable_initial
    (K : ℝ → ℝ) (hK : IntegrableOn K (Ioo (0 : ℝ) 1))
    (x : ℝ) (hx : x ∈ Icc (0 : ℝ) 1) :
    IntervalIntegrable K volume 0 x := by
  apply (affine_intervalIntegrable_of_integrableOn K hK).mono_set
  rw [uIcc_of_le hx.1, uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
  exact Icc_subset_Icc le_rfl hx.2

/-- The original warp is affine in integrable curvature on the physical interval. -/
theorem warp_affine_of_integrableOn (K J : ℝ → ℝ)
    (hK : IntegrableOn K (Ioo (0 : ℝ) 1))
    (hJ : IntegrableOn J (Ioo (0 : ℝ) 1))
    (t x : ℝ) (hx : x ∈ Icc (0 : ℝ) 1) :
    warp (fun y => (1 - t) * K y + t * J y) x =
      (1 - t) * warp K x + t * warp J x := by
  have hiK : IntervalIntegrable (fun y : ℝ => (x - y) * K y) volume 0 x :=
    (affine_intervalIntegrable_initial K hK x hx).continuousOn_mul
      (continuous_const.sub continuous_id).continuousOn
  have hiJ : IntervalIntegrable (fun y : ℝ => (x - y) * J y) volume 0 x :=
    (affine_intervalIntegrable_initial J hJ x hx).continuousOn_mul
      (continuous_const.sub continuous_id).continuousOn
  have hi : (∫ y in (0 : ℝ)..x, (x - y) * ((1 - t) * K y + t * J y)) =
      (1 - t) * (∫ y in (0 : ℝ)..x, (x - y) * K y) +
        t * ∫ y in (0 : ℝ)..x, (x - y) * J y := by
    calc
      _ = ∫ y in (0 : ℝ)..x,
          (1 - t) * ((x - y) * K y) + t * ((x - y) * J y) := by
        apply intervalIntegral.integral_congr
        intro y _
        ring
      _ = _ := by
        rw [intervalIntegral.integral_add (hiK.const_mul (1 - t)) (hiJ.const_mul t)]
        simp only [intervalIntegral.integral_const_mul]
  simp only [warp, hi]
  ring

/-- The original warp slope is affine in integrable curvature on the physical interval. -/
theorem warpSlope_affine_of_integrableOn (K J : ℝ → ℝ)
    (hK : IntegrableOn K (Ioo (0 : ℝ) 1))
    (hJ : IntegrableOn J (Ioo (0 : ℝ) 1))
    (t x : ℝ) (hx : x ∈ Icc (0 : ℝ) 1) :
    warpSlope (fun y => (1 - t) * K y + t * J y) x =
      (1 - t) * warpSlope K x + t * warpSlope J x := by
  have hiK := affine_intervalIntegrable_initial K hK x hx
  have hiJ := affine_intervalIntegrable_initial J hJ x hx
  simp only [warpSlope,
    intervalIntegral.integral_add (hiK.const_mul (1 - t)) (hiJ.const_mul t),
    intervalIntegral.integral_const_mul]
  ring

/-- Affine mixtures of integrable curvature preserve both normalized moments. -/
theorem curvature_moments_affine_of_integrableOn (K J : ℝ → ℝ)
    (hK : IntegrableOn K (Ioo (0 : ℝ) 1))
    (hJ : IntegrableOn J (Ioo (0 : ℝ) 1))
    (hK0 : (∫ x in (0 : ℝ)..1, K x) = 2)
    (hK1 : (∫ x in (0 : ℝ)..1, x * K x) = 1)
    (hJ0 : (∫ x in (0 : ℝ)..1, J x) = 2)
    (hJ1 : (∫ x in (0 : ℝ)..1, x * J x) = 1) (t : ℝ) :
    (∫ x in (0 : ℝ)..1, (1 - t) * K x + t * J x) = 2 ∧
      (∫ x in (0 : ℝ)..1, x * ((1 - t) * K x + t * J x)) = 1 := by
  have hiK := affine_intervalIntegrable_of_integrableOn K hK
  have hiJ := affine_intervalIntegrable_of_integrableOn J hJ
  constructor
  · rw [intervalIntegral.integral_add (hiK.const_mul (1 - t)) (hiJ.const_mul t)]
    simp only [intervalIntegral.integral_const_mul, hK0, hJ0]
    ring
  · have hiKx : IntervalIntegrable (fun x : ℝ => x * K x) volume 0 1 :=
      hiK.continuousOn_mul continuous_id.continuousOn
    have hiJx : IntervalIntegrable (fun x : ℝ => x * J x) volume 0 1 :=
      hiJ.continuousOn_mul continuous_id.continuousOn
    calc
      _ = ∫ x in (0 : ℝ)..1, (1 - t) * (x * K x) + t * (x * J x) := by
        apply intervalIntegral.integral_congr
        intro x _
        ring
      _ = (1 - t) * (∫ x in (0 : ℝ)..1, x * K x) +
          t * ∫ x in (0 : ℝ)..1, x * J x := by
        rw [intervalIntegral.integral_add (hiKx.const_mul (1 - t)) (hiJx.const_mul t)]
        simp only [intervalIntegral.integral_const_mul]
      _ = 1 := by rw [hK1, hJ1]; ring

/-- The actual weighted mass is affine in integrable curvature when the endpoint
mass densities are integrable. -/
theorem probeMass_affine_curvature_of_integrableOn (K J r : ℝ → ℝ)
    (hK : IntegrableOn K (Ioo (0 : ℝ) 1))
    (hJ : IntegrableOn J (Ioo (0 : ℝ) 1))
    (hMK : IntervalIntegrable (fun x => warp K x * r x ^ 2) volume 0 1)
    (hMJ : IntervalIntegrable (fun x => warp J x * r x ^ 2) volume 0 1)
    (t : ℝ) :
    probeMass (fun y => (1 - t) * K y + t * J y) r =
      (1 - t) * probeMass K r + t * probeMass J r := by
  unfold probeMass
  calc
    _ = ∫ x in (0 : ℝ)..1,
        (1 - t) * (warp K x * r x ^ 2) + t * (warp J x * r x ^ 2) := by
      apply intervalIntegral.integral_congr
      intro x hx
      have hx01 : x ∈ Icc (0 : ℝ) 1 := by
        simpa only [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using hx
      dsimp only
      rw [warp_affine_of_integrableOn K J hK hJ t x hx01]
      ring
    _ = _ := by
      rw [intervalIntegral.integral_add (hMK.const_mul (1 - t)) (hMJ.const_mul t)]
      simp only [intervalIntegral.integral_const_mul]

/-- The literal curvature derivative of the mass density is integrable whenever
both endpoint mass densities are integrable. -/
theorem probeMass_curvature_difference_intervalIntegrable (K J r : ℝ → ℝ)
    (hMK : IntervalIntegrable (fun x => warp K x * r x ^ 2) volume 0 1)
    (hMJ : IntervalIntegrable (fun x => warp J x * r x ^ 2) volume 0 1) :
    IntervalIntegrable (fun x => (warp J x - warp K x) * r x ^ 2) volume 0 1 := by
  simpa only [sub_mul] using hMJ.sub hMK

/-- Differentiating the actual curvature-segment mass gives the integral of the
literal warp difference against the square of the same probe. -/
theorem probeMass_curvature_segment_hasDerivAt (K J r : ℝ → ℝ)
    (hK : IntegrableOn K (Ioo (0 : ℝ) 1))
    (hJ : IntegrableOn J (Ioo (0 : ℝ) 1))
    (hMK : IntervalIntegrable (fun x => warp K x * r x ^ 2) volume 0 1)
    (hMJ : IntervalIntegrable (fun x => warp J x * r x ^ 2) volume 0 1)
    (t : ℝ) :
    HasDerivAt (fun s => probeMass (fun y => (1 - s) * K y + s * J y) r)
      (∫ x in (0 : ℝ)..1, (warp J x - warp K x) * r x ^ 2) t := by
  have hfun : (fun s => probeMass (fun y => (1 - s) * K y + s * J y) r) =
      fun s => (1 - s) * probeMass K r + s * probeMass J r := by
    funext s
    exact probeMass_affine_curvature_of_integrableOn K J r hK hJ hMK hMJ s
  have hdiff : (∫ x in (0 : ℝ)..1, (warp J x - warp K x) * r x ^ 2) =
      probeMass J r - probeMass K r := by
    simp only [sub_mul, intervalIntegral.integral_sub hMJ hMK, probeMass]
  rw [hfun, hdiff]
  convert (((hasDerivAt_id t).const_sub 1).mul_const (probeMass K r)).add
    ((hasDerivAt_id t).mul_const (probeMass J r)) using 1
  · funext s
    simp only [Pi.add_apply, id_eq]
  · ring

end RicciFlowSharpEstimate.Geometry.AreaProfile
