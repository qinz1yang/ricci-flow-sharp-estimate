/-
Copyright (c) 2026 Ziyang Qin. All rights reserved.
No license is granted by this file.
Authors: Ziyang Qin
-/
import RicciFlowSharpEstimate.Geometry.RecoverableAreaGeometry
import RicciFlowSharpEstimate.Geometry.AreaIntegrableAffine
import RicciFlowSharpEstimate.Geometry.SmoothAreaCurvature

/-!
# Curvature segments of the complete weak area action

The complete density is cubic in curvature and its two actual affine
primitives. Its first coefficient is integrable on the parabolic weak
graph: four convex samples of the complete density recover that coefficient
by finite differences. The resulting two-sided derivative requires no
curvature derivative and no smoothness of the weak probe.
-/

noncomputable section

namespace RicciFlowSharpEstimate.Geometry.AreaProfile

open Set MeasureTheory Filter

local notation "areaμ" => volume.restrict (Ioo (0 : ℝ) 1)

/-- The full physical derivative of the complete density along the segment
from `K` to `J`, with all three weak probe entries fixed. -/
def weakCurvatureSegmentDensity (K J r p z : ℝ → ℝ) (x : ℝ) : ℝ :=
  let f := warp K x
  let b := warpSlope K x
  let q := weakMeridionalOperator K r p z x
  let df := warp J x - f
  let db := warpSlope J x - b
  let dk := J x - K x
  let dq := df * z x + 2 * db * p x - dk * r x
  df * q ^ 2 + 2 * f * q * dq -
    (dk * b * f + K x * db * f + K x * b * df) * r x * p x -
    (dk * b ^ 2 / 2 + K x * b * db) * r x ^ 2 +
    (2 * K x * dk * f + K x ^ 2 * df) * r x ^ 2

/-- The actual interval integral of the complete curvature-segment density. -/
def weakCurvatureSegmentVariation (K J r p z : ℝ → ℝ) : ℝ :=
  ∫ x in (0 : ℝ)..1, weakCurvatureSegmentDensity K J r p z x

private def segmentDensity (K J r p z : ℝ → ℝ) (t x : ℝ) : ℝ :=
  meridionalActionDensity
    ((1 - t) * warp K x + t * warp J x)
    ((1 - t) * warpSlope K x + t * warpSlope J x)
    ((1 - t) * K x + t * J x) (r x) (p x) (z x)

private def segmentQuadraticCoefficient (K J r p z : ℝ → ℝ) (x : ℝ) : ℝ :=
  (18 * segmentDensity K J r p z 0 x -
    45 * segmentDensity K J r p z (1 / 3) x +
    36 * segmentDensity K J r p z (2 / 3) x -
    9 * segmentDensity K J r p z 1 x) / 2

private def segmentCubicCoefficient (K J r p z : ℝ → ℝ) (x : ℝ) : ℝ :=
  (-9 * segmentDensity K J r p z 0 x +
    27 * segmentDensity K J r p z (1 / 3) x -
    27 * segmentDensity K J r p z (2 / 3) x +
    9 * segmentDensity K J r p z 1 x) / 2

private theorem segmentDensity_linear_coefficient (K J r p z : ℝ → ℝ) (x : ℝ) :
    weakCurvatureSegmentDensity K J r p z x =
      (-11 * segmentDensity K J r p z 0 x +
        18 * segmentDensity K J r p z (1 / 3) x -
        9 * segmentDensity K J r p z (2 / 3) x +
        2 * segmentDensity K J r p z 1 x) / 2 := by
  unfold weakCurvatureSegmentDensity weakMeridionalOperator segmentDensity
    meridionalActionDensity
  ring

private theorem segmentDensity_expansion (K J r p z : ℝ → ℝ) (t x : ℝ) :
    segmentDensity K J r p z t x =
      segmentDensity K J r p z 0 x +
        t * weakCurvatureSegmentDensity K J r p z x +
        t ^ 2 * segmentQuadraticCoefficient K J r p z x +
        t ^ 3 * segmentCubicCoefficient K J r p z x := by
  unfold segmentQuadraticCoefficient segmentCubicCoefficient
    weakCurvatureSegmentDensity weakMeridionalOperator segmentDensity
    meridionalActionDensity
  ring

private theorem affine_mem_Icc {a b lo hi t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1)
    (ha : a ∈ Icc lo hi) (hb : b ∈ Icc lo hi) :
    (1 - t) * a + t * b ∈ Icc lo hi := by
  have hnt : 0 ≤ 1 - t := sub_nonneg.mpr ht.2
  constructor
  · calc
      lo = (1 - t) * lo + t * lo := by ring
      _ ≤ (1 - t) * a + t * b := add_le_add
        (mul_le_mul_of_nonneg_left ha.1 hnt) (mul_le_mul_of_nonneg_left hb.1 ht.1)
  · calc
      (1 - t) * a + t * b ≤ (1 - t) * hi + t * hi := add_le_add
        (mul_le_mul_of_nonneg_left ha.2 hnt) (mul_le_mul_of_nonneg_left hb.2 ht.1)
      _ = hi := by ring

private theorem actual_segmentDensity_eq (K J r p z : ℝ → ℝ)
    (hKi : IntegrableOn K (Ioo (0 : ℝ) 1))
    (hJi : IntegrableOn J (Ioo (0 : ℝ) 1)) (t x : ℝ) (hx : x ∈ Icc (0 : ℝ) 1) :
    meridionalActionDensity
      (warp (fun y => (1 - t) * K y + t * J y) x)
      (warpSlope (fun y => (1 - t) * K y + t * J y) x)
      ((1 - t) * K x + t * J x) (r x) (p x) (z x) =
        segmentDensity K J r p z t x := by
  rw [warp_affine_of_integrableOn K J hKi hJi t x hx,
    warpSlope_affine_of_integrableOn K J hKi hJi t x hx]
  rfl

private theorem segmentDensity_integrable {C : ℝ} {K J r p z : ℝ → ℝ}
    (hC : 1 ≤ C) (h : IsRecoverableAreaCompetitor C K r p z)
    (hJ : IsSmoothAreaCurvature C J) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
    Integrable (segmentDensity K J r p z t) areaμ := by
  have hCpos : 0 < C := zero_lt_one.trans_le hC
  have hlo : 0 ≤ 2 / C := by positivity
  have hhi : 0 ≤ 2 * C := by positivity
  have hKi : IntegrableOn K (Ioo (0 : ℝ) 1) := h.1.integrable (by norm_num)
  have hJi : IntegrableOn J (Ioo (0 : ℝ) 1) :=
    hJ.memLp_curvature.integrable (by norm_num)
  obtain ⟨hfK, hbK, hgeomK, _, hboxK⟩ := h.geometry_bounds hC
  have hfKm : AEStronglyMeasurable (warp K) areaμ :=
    ((hfK.integrableOn_compact isCompact_Icc).mono_set Ioo_subset_Icc_self).aestronglyMeasurable
  have hbKm : AEStronglyMeasurable (warpSlope K) areaμ :=
    ((hbK.integrableOn_compact isCompact_Icc).mono_set Ioo_subset_Icc_self).aestronglyMeasurable
  have hfJm : AEStronglyMeasurable (warp J) areaμ :=
    (warp_continuous J hJ.1.continuous).aestronglyMeasurable
  have hbJm : AEStronglyMeasurable (warpSlope J) areaμ :=
    (warpSlope_continuous J hJ.1.continuous).aestronglyMeasurable
  let L : ℝ → ℝ := fun x => (1 - t) * K x + t * J x
  have hLm : AEStronglyMeasurable L areaμ :=
    (h.1.aestronglyMeasurable.const_mul (1 - t)).add
      (hJ.memLp_curvature.aestronglyMeasurable.const_mul t)
  have hfLm : AEStronglyMeasurable (warp L) areaμ := by
    apply ((hfKm.const_mul (1 - t)).add (hfJm.const_mul t)).congr
    filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Ioo] with x hx
    exact (warp_affine_of_integrableOn K J hKi hJi t x ⟨hx.1.le, hx.2.le⟩).symm
  have hbLm : AEStronglyMeasurable (warpSlope L) areaμ := by
    apply ((hbKm.const_mul (1 - t)).add (hbJm.const_mul t)).congr
    filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Ioo] with x hx
    exact (warpSlope_affine_of_integrableOn K J hKi hJi t x ⟨hx.1.le, hx.2.le⟩).symm
  have hLbox : ∀ᵐ x ∂areaμ, 0 ≤ L x ∧ L x ≤ 2 * C := by
    filter_upwards [hboxK, ae_restrict_mem (μ := volume) measurableSet_Ioo] with x hx hxI
    have hJx := hJ.common_bounds x ⟨hxI.1.le, hxI.2.le⟩
    exact affine_mem_Icc ht ⟨hlo.trans hx.1, hx.2⟩ ⟨hlo.trans hJx.1, hJx.2⟩
  have hfLbox : ∀ᵐ x ∂areaμ,
      0 ≤ warp L x ∧ warp L x ≤ (2 * C) * (x * (1 - x)) := by
    filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Ioo] with x hx
    have hxI : x ∈ Icc (0 : ℝ) 1 := ⟨hx.1.le, hx.2.le⟩
    have hfKx := hgeomK x hxI
    have hfJx := hJ.geometry_bounds x hxI
    have hbase : 0 ≤ (2 / C) * x * (1 - x) :=
      mul_nonneg (mul_nonneg hlo hxI.1) (sub_nonneg.mpr hxI.2)
    change 0 ≤ warp (fun y => (1 - t) * K y + t * J y) x ∧ _
    rw [warp_affine_of_integrableOn K J hKi hJi t x hxI]
    exact affine_mem_Icc ht
      ⟨hbase.trans hfKx.1, by simpa only [mul_assoc] using hfKx.2.1⟩
      ⟨hbase.trans hfJx.1, by simpa only [mul_assoc] using hfJx.2.1⟩
  have hbLbox : ∀ᵐ x ∂areaμ, |warpSlope L x| ≤ 2 := by
    filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Ioo] with x hx
    have hxI : x ∈ Icc (0 : ℝ) 1 := ⟨hx.1.le, hx.2.le⟩
    have hbKx := (hgeomK x hxI).2.2
    have hbJx := (hJ.geometry_bounds x hxI).2.2
    change |warpSlope (fun y => (1 - t) * K y + t * J y) x| ≤ 2
    rw [warpSlope_affine_of_integrableOn K J hKi hJi t x hxI]
    exact abs_le.mpr (affine_mem_Icc ht (abs_le.mp hbKx) (abs_le.mp hbJx))
  have hD := integrable_weakMeridionalActionDensity_of_warp_bounds
    L r p z (2 * C) h.2.1 hhi hLm hfLm hbLm hLbox hfLbox hbLbox
  apply hD.congr
  filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Ioo] with x hx
  exact actual_segmentDensity_eq K J r p z hKi hJi t x ⟨hx.1.le, hx.2.le⟩

private theorem segment_coefficients_integrable {C : ℝ} {K J r p z : ℝ → ℝ}
    (hC : 1 ≤ C) (h : IsRecoverableAreaCompetitor C K r p z)
    (hJ : IsSmoothAreaCurvature C J) :
    Integrable (segmentDensity K J r p z 0) areaμ ∧
    Integrable (weakCurvatureSegmentDensity K J r p z) areaμ ∧
    Integrable (segmentQuadraticCoefficient K J r p z) areaμ ∧
    Integrable (segmentCubicCoefficient K J r p z) areaμ := by
  have h0 := segmentDensity_integrable hC h hJ 0 (by constructor <;> norm_num)
  have hthird := segmentDensity_integrable hC h hJ (1 / 3) (by constructor <;> norm_num)
  have htwoThirds := segmentDensity_integrable hC h hJ (2 / 3)
    (by constructor <;> norm_num)
  have h1 := segmentDensity_integrable hC h hJ 1 (by constructor <;> norm_num)
  refine ⟨h0, ?_, ?_, ?_⟩
  · apply (((((h0.const_mul (-11)).add (hthird.const_mul 18)).sub
      (htwoThirds.const_mul 9)).add (h1.const_mul 2)).div_const 2).congr
    exact Eventually.of_forall fun x => (segmentDensity_linear_coefficient K J r p z x).symm
  · exact ((((h0.const_mul 18).sub (hthird.const_mul 45)).add
      (htwoThirds.const_mul 36)).sub (h1.const_mul 9)).div_const 2
  · exact ((((h0.const_mul (-9)).add (hthird.const_mul 27)).sub
      (htwoThirds.const_mul 27)).add (h1.const_mul 9)).div_const 2

/-- The full curvature derivative is genuinely integrable for every
recoverable weak competitor and normalized smooth comparison curvature. -/
theorem weakCurvatureSegmentDensity_integrable {C : ℝ} {K J r p z : ℝ → ℝ}
    (hC : 1 ≤ C) (h : IsRecoverableAreaCompetitor C K r p z)
    (hJ : IsSmoothAreaCurvature C J) :
    IntegrableOn (weakCurvatureSegmentDensity K J r p z) (Ioo (0 : ℝ) 1) :=
  (segment_coefficients_integrable hC h hJ).2.1

/-- The complete physical curvature-segment pairing has an integrable
interval integrand, including the mixed and negative terms. -/
theorem weakCurvatureSegmentDensity_intervalIntegrable
    {C : ℝ} {K J r p z : ℝ → ℝ}
    (hC : 1 ≤ C) (h : IsRecoverableAreaCompetitor C K r p z)
    (hJ : IsSmoothAreaCurvature C J) :
    IntervalIntegrable (weakCurvatureSegmentDensity K J r p z) volume 0 1 :=
  (intervalIntegrable_iff_integrableOn_Ioo_of_le zero_le_one).mpr
    (weakCurvatureSegmentDensity_integrable hC h hJ)

/-- The actual complete weak action has the full curvature derivative
along the segment to any normalized smooth comparison curvature. The
two-sided derivative follows from its exact cubic polynomial identity. -/
theorem weakMeridionalAction_curvature_segment_hasDerivAt
    {C : ℝ} {K r p z : ℝ → ℝ}
    (hC : 1 ≤ C) (h : IsRecoverableAreaCompetitor C K r p z)
    (J : ℝ → ℝ) (hJ : IsSmoothAreaCurvature C J) :
    HasDerivAt (fun t => weakMeridionalAction (fun x => (1 - t) * K x + t * J x)
      r p z) (weakCurvatureSegmentVariation K J r p z) 0 := by
  have hKi : IntegrableOn K (Ioo (0 : ℝ) 1) := h.1.integrable (by norm_num)
  have hJi : IntegrableOn J (Ioo (0 : ℝ) 1) :=
    hJ.memLp_curvature.integrable (by norm_num)
  obtain ⟨hD, hV, hB, hT⟩ := segment_coefficients_integrable hC h hJ
  have hDI : IntervalIntegrable (segmentDensity K J r p z 0) volume 0 1 :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le zero_le_one).mpr hD
  have hVI : IntervalIntegrable (weakCurvatureSegmentDensity K J r p z) volume 0 1 :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le zero_le_one).mpr hV
  have hBI : IntervalIntegrable (segmentQuadraticCoefficient K J r p z) volume 0 1 :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le zero_le_one).mpr hB
  have hTI : IntervalIntegrable (segmentCubicCoefficient K J r p z) volume 0 1 :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le zero_le_one).mpr hT
  have heq (t : ℝ) :
      weakMeridionalAction (fun x => (1 - t) * K x + t * J x) r p z =
        weakMeridionalAction K r p z + t * weakCurvatureSegmentVariation K J r p z +
          t ^ 2 * (∫ x in (0 : ℝ)..1, segmentQuadraticCoefficient K J r p z x) +
          t ^ 3 * (∫ x in (0 : ℝ)..1, segmentCubicCoefficient K J r p z x) := by
    calc
      _ = ∫ x in (0 : ℝ)..1, segmentDensity K J r p z 0 x +
          t * weakCurvatureSegmentDensity K J r p z x +
          t ^ 2 * segmentQuadraticCoefficient K J r p z x +
          t ^ 3 * segmentCubicCoefficient K J r p z x := by
        unfold weakMeridionalAction
        apply intervalIntegral.integral_congr
        intro x hx
        have hxI : x ∈ Icc (0 : ℝ) 1 := by
          simpa only [uIcc_of_le zero_le_one] using hx
        exact (actual_segmentDensity_eq K J r p z hKi hJi t x hxI).trans
          (segmentDensity_expansion K J r p z t x)
      _ = _ := by
        rw [intervalIntegral.integral_add
            ((hDI.add (hVI.const_mul t)).add (hBI.const_mul (t ^ 2)))
            (hTI.const_mul (t ^ 3)),
          intervalIntegral.integral_add (hDI.add (hVI.const_mul t))
            (hBI.const_mul (t ^ 2)),
          intervalIntegral.integral_add hDI (hVI.const_mul t)]
        simp only [intervalIntegral.integral_const_mul, segmentDensity,
          sub_zero, one_mul, zero_mul, add_zero, weakMeridionalAction,
          weakCurvatureSegmentVariation]
  rw [funext heq]
  have hlin := ((hasDerivAt_id (0 : ℝ)).mul_const
    (weakCurvatureSegmentVariation K J r p z)).const_add (weakMeridionalAction K r p z)
  have hquad := ((hasDerivAt_id (0 : ℝ)).pow 2).mul_const
    (∫ x in (0 : ℝ)..1, segmentQuadraticCoefficient K J r p z x)
  have hcubic := ((hasDerivAt_id (0 : ℝ)).pow 3).mul_const
    (∫ x in (0 : ℝ)..1, segmentCubicCoefficient K J r p z x)
  convert (hlin.add hquad).add hcubic using 1
  · funext t
    rfl
  · norm_num

end RicciFlowSharpEstimate.Geometry.AreaProfile
