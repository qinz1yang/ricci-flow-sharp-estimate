/-
Copyright (c) 2026 Ziyang Qin. All rights reserved.
No license is granted by this file.
Authors: Ziyang Qin
-/
import RicciFlowSharpEstimate.Geometry.AreaActionContinuity
import RicciFlowSharpEstimate.Geometry.AreaIntegrableAffine
import RicciFlowSharpEstimate.Geometry.NormalizedAreaHaar

/-!
# Safety at the unrestricted rotational threshold

Every cap strictly below the supremum is safe. Contraction toward round
curvature preserves both exact area moments and strictly improves the pinching
ratio. Continuity of the complete action then gives safety at the supremum,
with the original all-form quantifiers supplied by the normalized Haar transfer.
-/

noncomputable section

namespace RicciFlowSharpEstimate.Geometry

open Filter MeasureTheory Set Topology
open scoped ContDiff

/-- Every cap at least one and strictly below the unrestricted threshold is safe. -/
theorem mem_rotationalSafeCaps_of_lt_rotationalThreshold {C : ℝ} (hC : 1 ≤ C)
    (hthreshold : C < rotationalThreshold) : C ∈ rotationalSafeCaps := by
  obtain ⟨D, hD, hCD⟩ :=
    exists_lt_of_lt_csSup rotationalSafeCaps_nonempty hthreshold
  exact rotationalSafeCaps_downward hD hC hCD.le

private theorem areaAction_contraction_nonneg
    (hthreshold : 1 < rotationalThreshold) (K r : ℝ → ℝ)
    (hK : ContDiff ℝ ∞ K) (hr : ContDiff ℝ ∞ r)
    (hzero : (∫ x in (0 : ℝ)..1, K x) = 2)
    (hone : (∫ x in (0 : ℝ)..1, x * K x) = 1)
    (κ Λ : ℝ) (hκ : 0 < κ)
    (hbox : ∀ x ∈ Icc (0 : ℝ) 1, K x ∈ Icc κ Λ)
    (hratio : Λ / κ ≤ rotationalThreshold)
    (t : ℝ) (ht0 : 0 < t) (ht1 : t < 1) :
    0 ≤ AreaProfile.meridionalAction (fun x => (1 - t) * K x + 2 * t) r := by
  have hweight : 0 < 1 - t := sub_pos.mpr ht1
  have hlo : 0 < (1 - t) * κ + 2 * t := by positivity
  have hboxt : ∀ x ∈ Icc (0 : ℝ) 1,
      (1 - t) * K x + 2 * t ∈
        Icc ((1 - t) * κ + 2 * t) ((1 - t) * Λ + 2 * t) := by
    intro x hx
    constructor <;> nlinarith [hbox x hx,
      mul_le_mul_of_nonneg_left (hbox x hx).1 hweight.le,
      mul_le_mul_of_nonneg_left (hbox x hx).2 hweight.le]
  have hratio_one : 1 ≤ ((1 - t) * Λ + 2 * t) / ((1 - t) * κ + 2 * t) := by
    apply (le_div_iff₀ hlo).mpr
    have hb := hboxt 0 (by norm_num)
    simpa only [one_mul] using hb.1.trans hb.2
  have hratio_strict :
      ((1 - t) * Λ + 2 * t) / ((1 - t) * κ + 2 * t) < rotationalThreshold := by
    apply (div_lt_iff₀ hlo).mpr
    have hupper := mul_le_mul_of_nonneg_left ((div_le_iff₀ hκ).mp hratio) hweight.le
    have hgap : 0 < (2 * t) * (rotationalThreshold - 1) :=
      mul_pos (mul_pos (by norm_num) ht0) (sub_pos.mpr hthreshold)
    nlinarith
  have hsafe := mem_rotationalSafeCaps_of_lt_rotationalThreshold hratio_one hratio_strict
  have hKi : IntegrableOn K (Ioo (0 : ℝ) 1) volume :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le zero_le_one).mp
      (hK.continuous.intervalIntegrable 0 1)
  have htwoi : IntegrableOn (fun _ : ℝ => (2 : ℝ)) (Ioo (0 : ℝ) 1) volume :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le zero_le_one).mp
      intervalIntegrable_const
  have htwozero : (∫ _x in (0 : ℝ)..1, (2 : ℝ)) = 2 := by norm_num
  have htwoone : (∫ x in (0 : ℝ)..1, x * (2 : ℝ)) = 1 := by
    norm_num [intervalIntegral.integral_mul_const, integral_id]
  have hmoments := AreaProfile.curvature_moments_affine_of_integrableOn
    K (fun _ => 2) hKi htwoi hzero hone htwozero htwoone t
  have hmoments' :
      (∫ x in (0 : ℝ)..1, (1 - t) * K x + 2 * t) = 2 ∧
        (∫ x in (0 : ℝ)..1, x * ((1 - t) * K x + 2 * t)) = 1 := by
    simpa only [mul_comm t (2 : ℝ)] using hmoments
  exact areaAction_nonneg_of_rotationalSafeCap _ hsafe
    (fun x => (1 - t) * K x + 2 * t) r
    ((contDiff_const.mul hK).add contDiff_const) hr
    (fun x hx => hlo.trans_le (hboxt x hx).1) hmoments'.1 hmoments'.2
    ((1 - t) * κ + 2 * t) ((1 - t) * Λ + 2 * t) hlo hboxt le_rfl

/-- The unrestricted rotational threshold is safe for every original smooth
one-form on every represented rotational metric, including its endpoint. -/
theorem rotationalThreshold_mem_rotationalSafeCaps :
    rotationalThreshold ∈ rotationalSafeCaps := by
  rcases eq_or_lt_of_le one_le_rotationalThreshold with hthreshold | hthreshold
  · simpa only [← hthreshold] using one_mem_rotationalSafeCaps
  · apply rotationalSafeCaps_of_normalized_area_safety rotationalThreshold
      one_le_rotationalThreshold
    intro K hK _hpos hzero hone κ Λ hκ hbox hratio r hr _hmass
    by_contra hnonneg
    have hneg : AreaProfile.meridionalAction K r < 0 := lt_of_not_ge hnonneg
    have hlim : Tendsto
        (fun t : ℝ => AreaProfile.meridionalAction (fun x => (1 - t) * K x + 2 * t) r)
        (𝓝 0) (𝓝 (AreaProfile.meridionalAction K r)) := by
      simpa only [sub_zero, mul_zero, zero_mul, one_mul, add_zero] using
        (AreaProfile.continuous_meridionalAction_affine K r hK.continuous hr).tendsto 0
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
    have htneg :
        AreaProfile.meridionalAction (fun x => (1 - t) * K x + 2 * t) r < 0 := by
      apply hball
      simpa only [Real.dist_eq, sub_zero, abs_of_pos ht0] using htδ
    exact (not_lt_of_ge (areaAction_contraction_nonneg hthreshold K r hK hr
      hzero hone κ Λ hκ hbox hratio t ht0 ht1)) htneg

end RicciFlowSharpEstimate.Geometry
