/-
Copyright (c) 2026 Ziyang Qin. All rights reserved.
No license is granted by this file.
Authors: Ziyang Qin
-/
import RicciFlowSharpEstimate.Geometry.RecoverableCurvatureSegment
import RicciFlowSharpEstimate.Geometry.WeakCurvatureSegment
import RicciFlowSharpEstimate.Geometry.RecoverableProbeStationarity
import Mathlib.Analysis.Calculus.LocalExtr.Basic

/-!
# Actual curvature inequalities for the recoverable joint minimum

The normalized segment toward every admissible smooth curvature is proved
feasible throughout the convex segment. The full cubic action derivative and
actual varying-mass derivative therefore give a one-sided inequality.
The produced joint minimum satisfies this and the full weak probe equation.
No moment multipliers or structural optimizer restrictions are assumed.
-/

noncomputable section
namespace RicciFlowSharpEstimate.Geometry.AreaProfile
open Set MeasureTheory Filter Topology
open scoped ContDiff ENNReal
local notation "areaμ" => volume.restrict (Ioo (0 : ℝ) 1)

/-- Every actual recoverable minimum has a nonnegative complete curvature
variation, corrected by the varying physical mass, toward each admissible
original smooth curvature. This is a one-sided condition; no multiplier,
zero action or smooth limiting curvature is assumed. -/
theorem IsRecoverableAreaCompetitor.curvature_segment_inequality_of_minimum
    {C : ℝ} {K r p z : ℝ → ℝ} (hC : 1 ≤ C)
    (h : IsRecoverableAreaCompetitor C K r p z)
    (hmin : ∀ K' r' p' z' : ℝ → ℝ, IsRecoverableAreaCompetitor C K' r' p' z' →
      weakMeridionalAction K r p z ≤ weakMeridionalAction K' r' p' z')
    (J : ℝ → ℝ) (hJ : IsSmoothAreaCurvature C J) :
    0 ≤ weakCurvatureSegmentVariation K J r p z -
      weakMeridionalAction K r p z *
        (∫ x in (0 : ℝ)..1, (warp J x - warp K x) * r x ^ 2) := by
  have hCpos : 0 < C := zero_lt_one.trans_le hC
  have hKi : IntegrableOn K (Ioo (0 : ℝ) 1) := h.1.integrable (by norm_num)
  have hJi : IntegrableOn J (Ioo (0 : ℝ) 1) :=
    hJ.memLp_curvature.integrable (by norm_num)
  have hMK : IntervalIntegrable (fun x => warp K x * r x ^ 2) volume 0 1 :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le zero_le_one).mpr
      (h.exists_action_recovery hC).2.1
  have hfJ : AEStronglyMeasurable (warp J) areaμ :=
    (warp_continuous J hJ.1.continuous).aestronglyMeasurable
  have hfJbox : ∀ᵐ x ∂areaμ,
      0 ≤ warp J x ∧ warp J x ≤ (2 * C) * (x * (1 - x)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
    have hg := hJ.geometry_bounds x ⟨hx.1.le, hx.2.le⟩
    refine ⟨?_, by simpa only [mul_assoc] using hg.2.1⟩
    exact (mul_nonneg (mul_nonneg (by positivity : (0 : ℝ) ≤ 2 / C) hx.1.le)
      (sub_nonneg.mpr hx.2.le)).trans hg.1
  have hMJ := probeMass_intervalIntegrable_of_warp_bounds J r (2 * C)
    h.2.1.memLp (by positivity) hfJ hfJbox
  have hDA := weakMeridionalAction_curvature_segment_hasDerivAt hC h J hJ
  have hDM := probeMass_curvature_segment_hasDerivAt K J r hKi hJi hMK hMJ 0
  have hunit : probeMass K r = 1 := h.2.2.2.2.2.1
  let F : ℝ → ℝ := fun t =>
    weakMeridionalAction (fun x => (1 - t) * K x + t * J x) r p z -
      weakMeridionalAction K r p z * probeMass (fun x => (1 - t) * K x + t * J x) r
  have hDF := hDA.sub (hDM.const_mul (weakMeridionalAction K r p z))
  have hLocal : IsLocalMinOn F (Icc (0 : ℝ) 1) 0 := by
    filter_upwards [self_mem_nhdsWithin] with t htI
    have ht := h.probeMass_curvature_segment_pos hC J hJ t htI
    have hfeas := h.normalized_curvature_segment hC J hJ t htI
    have hc := hmin _ _ _ _ hfeas
    let Kt : ℝ → ℝ := fun x => (1 - t) * K x + t * J x
    let m : ℝ := probeMass Kt r
    let c : ℝ := 1 / Real.sqrt m
    change weakMeridionalAction K r p z ≤
      weakMeridionalAction Kt (fun x => c * r x) (fun x => c * p x) (fun x => c * z x) at hc
    rw [weakMeridionalAction_const_mul] at hc
    have hcm : c ^ 2 * m = 1 := by
      dsimp only [c]
      rw [one_div_pow, Real.sq_sqrt ht.le]
      exact one_div_mul_cancel ht.ne'
    have hmul := mul_le_mul_of_nonneg_right hc ht.le
    have hcancel : (c ^ 2 * weakMeridionalAction Kt r p z) * m =
        weakMeridionalAction Kt r p z := by
      calc
        _ = (c ^ 2 * m) * weakMeridionalAction Kt r p z := by ring
        _ = _ := by rw [hcm, one_mul]
    change weakMeridionalAction K r p z * m ≤ _ at hmul
    rw [hcancel] at hmul
    simpa only [F, sub_zero, one_mul, zero_mul, add_zero, hunit, mul_one, sub_self] using
      (sub_nonneg.mpr hmul)
  have hseg : segment ℝ (0 : ℝ) 1 ⊆ Icc (0 : ℝ) 1 := by
    rw [segment_eq_Icc zero_le_one]
  have hdir : (1 : ℝ) ∈ posTangentConeAt (Icc (0 : ℝ) 1) 0 := by
    simpa only [sub_zero] using sub_mem_posTangentConeAt_of_segment_subset hseg
  have hp := hLocal.hasFDerivWithinAt_nonneg hDF.hasFDerivAt.hasFDerivWithinAt hdir
  simpa only [ContinuousLinearMap.toSpanSingleton_apply, smul_eq_mul, one_mul] using hp

/-- A cap alone produces the actual joint minimum satisfying both the full
weak probe equation and the mass-corrected curvature inequality toward
every admissible original smooth curvature. These are necessary conditions,
not a determining threshold or a global positivity certificate. -/
theorem exists_recoverable_area_minimizer_weak_conditions (C : ℝ) (hC : 1 ≤ C) :
    ∃ K r p z : ℝ → ℝ,
      IsRecoverableAreaCompetitor C K r p z ∧
      ContinuousOn r (Ioo (0 : ℝ) 1) ∧ ContinuousOn p (Ioo (0 : ℝ) 1) ∧
      (∃ x ∈ Ioo (0 : ℝ) 1, r x ≠ 0) ∧
      weakMeridionalAction K r p z = smoothAreaInfimum C ∧
      (∀ K' r' p' z' : ℝ → ℝ, IsRecoverableAreaCompetitor C K' r' p' z' →
        weakMeridionalAction K r p z ≤ weakMeridionalAction K' r' p' z') ∧
      (∀ s : ℝ → ℝ, ContDiff ℝ ∞ s →
        weakMeridionalPairing K r p z s (deriv s) (deriv (deriv s)) =
          smoothAreaInfimum C * (∫ x in (0 : ℝ)..1, warp K x * s x * r x)) ∧
      (∀ J : ℝ → ℝ, IsSmoothAreaCurvature C J →
        0 ≤ weakCurvatureSegmentVariation K J r p z - smoothAreaInfimum C *
          (∫ x in (0 : ℝ)..1, (warp J x - warp K x) * r x ^ 2)) := by
  obtain ⟨K, r, p, z, h, hrc, hpc, hnz, hEq, hmin, hProbe⟩ :=
    exists_recoverable_area_minimizer_weak_probe_equation C hC
  refine ⟨K, r, p, z, h, hrc, hpc, hnz, hEq, hmin, hProbe, ?_⟩
  intro J hJ
  simpa only [hEq] using h.curvature_segment_inequality_of_minimum hC hmin J hJ

end RicciFlowSharpEstimate.Geometry.AreaProfile
