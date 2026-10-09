/-
Copyright (c) 2026 Ziyang Qin. All rights reserved.
No license is granted by this file.
Authors: Ziyang Qin
-/
import RicciFlowSharpEstimate.Geometry.AreaActionContinuity
import RicciFlowSharpEstimate.Geometry.CriticalPlateauInstability

/-!
# Strict contraction of the actual critical curvature

Mixing the actual critical area curvature toward its mean preserves both exact
moments and the physical hemisphere shape. The resulting positive box has
strictly smaller ratio. A single fixed smooth negative plateau probe remains
negative for a sufficiently small positive contraction parameter.
-/

noncomputable section

namespace RicciFlowSharpEstimate.Geometry.CriticalAreaProfile

open Filter MeasureTheory Set Variational Topology
open scoped ContDiff

/-- The literal contraction of the actual critical curvature toward its mean. -/
def contractedCurvature (t x : ℝ) : ℝ := (1 - t) * curvature x + 2 * t

/-- The lower endpoint of the same contracted critical curvature box. -/
def contractedLower (t : ℝ) : ℝ := (1 - t) * length + 2 * t

/-- The upper endpoint of the same contracted critical curvature box. -/
def contractedUpper (t : ℝ) : ℝ := (1 - t) * length * criticalCap + 2 * t

/-- Every member of the literal affine family is globally continuous. -/
theorem contractedCurvature_continuous (t : ℝ) : Continuous (contractedCurvature t) :=
  (continuous_const.mul curvature_continuous).add continuous_const

/-- Both exact normalized curvature moments survive every affine parameter. -/
theorem contractedCurvature_moments (t : ℝ) :
    (∫ x in (0 : ℝ)..1, contractedCurvature t x) = 2 ∧
      (∫ x in (0 : ℝ)..1, x * contractedCurvature t x) = 1 := by
  have hK : IntervalIntegrable curvature volume 0 1 :=
    curvature_continuous.intervalIntegrable 0 1
  have hxK : IntervalIntegrable (fun x : ℝ => x * curvature x) volume 0 1 :=
    (continuous_id.mul curvature_continuous).intervalIntegrable 0 1
  constructor
  · change (∫ x in (0 : ℝ)..1, (1 - t) * curvature x + 2 * t) = 2
    rw [intervalIntegral.integral_add
      (hK.const_mul (1 - t)) intervalIntegrable_const,
      intervalIntegral.integral_const_mul, curvature_moments.1]
    simp only [intervalIntegral.integral_const, sub_zero, smul_eq_mul, one_mul]
    ring
  · have heq : (fun x : ℝ => x * contractedCurvature t x) =
        fun x => (1 - t) * (x * curvature x) + (2 * t) * x := by
      funext x
      unfold contractedCurvature
      ring
    have hlin : IntervalIntegrable (fun x : ℝ => (2 * t) * x) volume 0 1 :=
      (continuous_const.mul continuous_id).intervalIntegrable 0 1
    rw [heq, intervalIntegral.integral_add (hxK.const_mul (1 - t)) hlin,
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
      curvature_moments.2, integral_id]
    norm_num
    ring

/-- The same physical reflection law holds throughout the affine family. -/
theorem contractedCurvature_reflection (t x : ℝ) (hx : x ∈ Icc (0 : ℝ) 1) :
    contractedCurvature t (1 - x) = contractedCurvature t x := by
  simp only [contractedCurvature, curvature_reflection x hx]

/-- Contraction with nonnegative original coefficient preserves southern order. -/
theorem contractedCurvature_antitoneOn_left (t : ℝ) (ht : t ≤ 1) :
    AntitoneOn (contractedCurvature t) (Icc (0 : ℝ) (1 / 2)) := by
  intro x hx y hy hxy
  exact add_le_add (mul_le_mul_of_nonneg_left
    (curvature_antitoneOn_left hx hy hxy) (sub_nonneg.mpr ht)) le_rfl

/-- Contraction with nonnegative original coefficient preserves northern order. -/
theorem contractedCurvature_monotoneOn_right (t : ℝ) (ht : t ≤ 1) :
    MonotoneOn (contractedCurvature t) (Icc (1 / 2 : ℝ) 1) := by
  intro x hx y hy hxy
  exact add_le_add (mul_le_mul_of_nonneg_left
    (curvature_monotoneOn_right hx hy hxy) (sub_nonneg.mpr ht)) le_rfl

/-- The actual contracted curvature lies in its literal box on the whole line. -/
theorem contractedCurvature_bounds (t : ℝ) (ht : t ≤ 1) (x : ℝ) :
    contractedCurvature t x ∈ Icc (contractedLower t) (contractedUpper t) := by
  obtain ⟨hlo, hhi⟩ := curvature_bounds x
  constructor
  · exact add_le_add (mul_le_mul_of_nonneg_left hlo (sub_nonneg.mpr ht)) le_rfl
  · change (1 - t) * curvature x + 2 * t ≤ (1 - t) * length * criticalCap + 2 * t
    simpa only [mul_assoc] using
      add_le_add (mul_le_mul_of_nonneg_left hhi (sub_nonneg.mpr ht))
        (le_rfl : 2 * t ≤ 2 * t)

/-- An interior contraction puts the mean strictly inside a positive box. -/
theorem contracted_strict_bounds (t : ℝ) (ht0 : 0 < t) (ht1 : t < 1) :
    0 < contractedLower t ∧ contractedLower t < 2 ∧ 2 < contractedUpper t := by
  have hL := length_pos
  have hcoef : 0 < 1 - t := sub_pos.mpr ht1
  have hlo := strict_average_bounds.1
  have hhi := strict_average_bounds.2
  unfold contractedLower contractedUpper
  refine ⟨by positivity, ?_, ?_⟩
  · nlinarith [mul_pos hcoef (sub_pos.mpr hlo)]
  · nlinarith [mul_pos hcoef (sub_pos.mpr hhi)]

/-- The exact deficit of the contracted box ratio comes from its constant summand. -/
theorem contracted_ratio_deficit (t : ℝ) (hlo : contractedLower t ≠ 0) :
    criticalCap - contractedUpper t / contractedLower t =
      2 * t * (criticalCap - 1) / contractedLower t := by
  apply (eq_div_iff hlo).2
  field_simp
  unfold contractedLower contractedUpper
  ring

/-- The exact ratio deficit is positive for every interior contraction. -/
theorem contracted_ratio_deficit_pos (t : ℝ) (ht0 : 0 < t) (ht1 : t < 1) :
    0 < 2 * t * (criticalCap - 1) / contractedLower t := by
  exact div_pos (mul_pos (mul_pos (by norm_num) ht0) (sub_pos.mpr one_lt_criticalCap))
    (contracted_strict_bounds t ht0 ht1).1

/-- Every interior contracted box has ratio strictly below the actual critical cap. -/
theorem contracted_ratio_lt_criticalCap (t : ℝ) (ht0 : 0 < t) (ht1 : t < 1) :
    contractedUpper t / contractedLower t < criticalCap := by
  have hdef := contracted_ratio_deficit t (ne_of_gt (contracted_strict_bounds t ht0 ht1).1)
  have hpos := contracted_ratio_deficit_pos t ht0 ht1
  linarith

/-- A supplied fixed smooth negative probe stays negative under some positive
strict contraction of the original critical curvature. -/
theorem exists_negative_contraction_parameter_of_negative_action (r : ℝ → ℝ)
    (hr : ContDiff ℝ ∞ r) (hneg : AreaProfile.meridionalAction curvature r < 0) :
    ∃ t ∈ Ioo (0 : ℝ) 1, AreaProfile.meridionalAction (contractedCurvature t) r < 0 := by
  have hlim : Tendsto (fun t => AreaProfile.meridionalAction (contractedCurvature t) r)
      (𝓝 0) (𝓝 (AreaProfile.meridionalAction curvature r)) := by
    change Tendsto (fun t => AreaProfile.meridionalAction
      (fun x => (1 - t) * curvature x + 2 * t) r) (𝓝 0)
      (𝓝 (AreaProfile.meridionalAction curvature r))
    simpa only [sub_zero, mul_zero, zero_mul, one_mul, add_zero] using
      (AreaProfile.continuous_meridionalAction_affine curvature r curvature_continuous hr).tendsto 0
  have hevent := hlim.eventually (gt_mem_nhds hneg)
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.mp hevent
  let t := min δ 1 / 2
  have ht0 : 0 < t := by dsimp [t]; positivity
  have htδ : t < δ := by
    dsimp [t]
    linarith [min_le_left δ 1, lt_min hδ (by norm_num : (0 : ℝ) < 1)]
  have ht1 : t < 1 := by
    dsimp [t]
    linarith [min_le_right δ 1]
  refine ⟨t, ⟨ht0, ht1⟩, hball ?_⟩
  simpa only [Real.dist_eq, sub_zero, abs_of_pos ht0] using htδ

/-- One accepted critical plateau probe and one positive contraction give a negative
complete action strictly below the critical curvature ratio, with the same endpoint data. -/
theorem exists_smooth_negative_contraction :
    ∃ (r : ℝ → ℝ) (t : ℝ), ContDiff ℝ ∞ r ∧ r 0 = 1 ∧ deriv r 0 = 0 ∧
      r =ᶠ[𝓝 0] (fun _ => 1) ∧ r =ᶠ[𝓝 1] (fun _ => 1) ∧
      (∃ x ∈ Ioo (0 : ℝ) 1, r x ≠ 1) ∧ 0 < t ∧ t < 1 ∧
      0 < contractedLower t ∧ contractedLower t < 2 ∧ 2 < contractedUpper t ∧
      contractedUpper t / contractedLower t < criticalCap ∧
      AreaProfile.meridionalAction (contractedCurvature t) r < 0 := by
  obtain ⟨r, hr, hr0, hrd0, hn0, hn1, hnonconstant, hneg⟩ := exists_smooth_negative_probe
  obtain ⟨t, ht, htneg⟩ := exists_negative_contraction_parameter_of_negative_action r hr hneg
  obtain ⟨hlo, hlo2, hhi2⟩ := contracted_strict_bounds t ht.1 ht.2
  exact ⟨r, t, hr, hr0, hrd0, hn0, hn1, hnonconstant, ht.1, ht.2, hlo, hlo2, hhi2,
    contracted_ratio_lt_criticalCap t ht.1 ht.2, htneg⟩

end RicciFlowSharpEstimate.Geometry.CriticalAreaProfile
