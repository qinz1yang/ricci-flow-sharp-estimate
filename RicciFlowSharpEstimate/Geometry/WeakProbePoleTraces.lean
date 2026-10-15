/-
Copyright (c) 2026 Ziyang Qin. All rights reserved.
No license is granted by this file.
Authors: Ziyang Qin
-/
import RicciFlowSharpEstimate.Geometry.WeakProbeOperatorIntegrability
import RicciFlowSharpEstimate.Geometry.WeakProbeDerivativeFlux
import RicciFlowSharpEstimate.Analysis.ParabolicDivergenceIntegrability

/-! # Finite physical pole traces of the actual signed minimizing probe -/

noncomputable section
namespace RicciFlowSharpEstimate.Geometry.AreaProfile
open Set MeasureTheory Filter Topology
local notation "areaμ" => volume.restrict (Ioo (0 : ℝ) 1)

/-- The actual signed minimizing probe and its literal weak operator have
unweighted L1 control through both physical poles. The displayed primitive
extends that same probe absolutely continuously, with its genuine derivative
and finite pole traces. No endpoint value, sign or nonzero trace is imposed. -/
theorem IsRecoverableAreaCompetitor.probe_pole_integrability_of_minimum
    {C : ℝ} {K r p z : ℝ → ℝ} (hC : 1 ≤ C)
    (h : IsRecoverableAreaCompetitor C K r p z)
    (hr : ContinuousOn r (Ioo (0 : ℝ) 1))
    (hp : ContinuousOn p (Ioo (0 : ℝ) 1))
    (hmin : ∀ K' r' p' z' : ℝ → ℝ, IsRecoverableAreaCompetitor C K' r' p' z' →
      weakMeridionalAction K r p z ≤ weakMeridionalAction K' r' p' z') :
    Integrable (weakMeridionalOperator K r p z) areaμ ∧ Integrable p areaμ ∧
      let R := fun x => r (1 / 2) + ∫ t in (1 / 2 : ℝ)..x, p t
      AbsolutelyContinuousOnInterval R 0 1 ∧ EqOn R r (Ioo (0 : ℝ) 1) ∧
      (∀ x ∈ Ioo (0 : ℝ) 1, HasDerivAt R (p x) x) ∧
      Tendsto r (𝓝[>] 0) (𝓝 (R 0)) ∧ Tendsto r (𝓝[<] 1) (𝓝 (R 1)) ∧
      ∃ B : ℝ, ∀ x ∈ Ioo (0 : ℝ) 1, |r x| ≤ B := by
  have hC0 : 0 < C := zero_lt_one.trans_le hC
  have hg := h.geometry_bounds hC
  have hfM : AEStronglyMeasurable (warp K) areaμ :=
    ((hg.1.integrableOn_compact isCompact_Icc).mono_set Ioo_subset_Icc_self).aestronglyMeasurable
  have hKB : ∀ᵐ x ∂areaμ, ‖K x‖ ≤ 2 * C := by
    filter_upwards [hg.2.2.2.2] with x hx
    rw [Real.norm_eq_abs, abs_of_nonneg ((by positivity : (0 : ℝ) ≤ 2 / C).trans hx.1)]
    exact hx.2
  have hfbounds : ∀ᵐ x ∂areaμ,
      (2 / C) * (x * (1 - x)) ≤ warp K x ∧
        warp K x ≤ (2 * C) * (x * (1 - x)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
    have hh := hg.2.2.1 x ⟨hx.1.le, hx.2.le⟩
    exact ⟨by simpa only [mul_assoc] using hh.1,
      by simpa only [mul_assoc] using hh.2.1⟩
  have hQI := h.weak_operator_integrable_of_minimum hC hr hp hmin
  have hrI := h.2.1.memLp.integrable (by norm_num : (1 : ENNReal) ≤ 2)
  have hSI : Integrable
      (fun x => weakMeridionalOperator K r p z x + K x * r x) areaμ :=
    hQI.add (hrI.bdd_mul h.1.aestronglyMeasurable hKB)
  obtain ⟨hFAC, hF0, hF1, hFD⟩ := h.derivative_flux_absolutelyContinuous hC hp
  have hpI : Integrable p areaμ :=
    Analysis.integrable_of_parabolic_divergence_flux hfM (by positivity : 0 < 2 / C)
      hfbounds hFAC hF0 hF1 (Eventually.of_forall fun _ => rfl) hFD hSI
  let c : ℝ := 1 / 2
  let R := fun x => r c + ∫ t in c..x, p t
  have hc : c ∈ Ioo (0 : ℝ) 1 := by norm_num [c]
  have hpII : IntervalIntegrable p volume 0 1 :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le zero_le_one).mpr hpI
  have hRAC : AbsolutelyContinuousOnInterval R 0 1 :=
    (contDiff_const : ContDiff ℝ 1 (fun _ : ℝ => r c)).contDiffOn.absolutelyContinuousOnInterval
      |>.fun_add (hpII.absolutelyContinuousOnInterval_intervalIntegral (by norm_num [c]))
  have hReq : EqOn R r (Ioo (0 : ℝ) 1) := by
    intro x hx
    have hh := h.2.1.weakDeriv.integral_eq_sub_of_continuousOn hr hc hx
    change r c + (∫ t in c..x, p t) = r x
    rw [hh]
    ring
  have hRC : ContinuousOn R (Icc (0 : ℝ) 1) := by
    simpa only [uIcc_of_le zero_le_one] using hRAC.continuousOn
  have hLdom : ∀ᶠ x in 𝓝[>] (0 : ℝ), x ∈ Ioo (0 : ℝ) 1 :=
    Ioo_mem_nhdsGT zero_lt_one
  have hRdom : ∀ᶠ x in 𝓝[<] (1 : ℝ), x ∈ Ioo (0 : ℝ) 1 :=
    Ioo_mem_nhdsLT zero_lt_one
  have hLi : Tendsto (fun x : ℝ => x) (𝓝[>] 0) (𝓝[Icc (0 : ℝ) 1] 0) :=
    tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
      (tendsto_id.mono_left nhdsWithin_le_nhds)
      (hLdom.mono fun _ hx => ⟨hx.1.le, hx.2.le⟩)
  have hRi : Tendsto (fun x : ℝ => x) (𝓝[<] 1) (𝓝[Icc (0 : ℝ) 1] 1) :=
    tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
      (tendsto_id.mono_left nhdsWithin_le_nhds)
      (hRdom.mono fun _ hx => ⟨hx.1.le, hx.2.le⟩)
  have hLtrace : Tendsto r (𝓝[>] 0) (𝓝 (R 0)) :=
    ((hRC.continuousWithinAt ⟨le_rfl, zero_le_one⟩).tendsto.comp hLi).congr'
      (hLdom.mono fun x hx => hReq hx)
  have hRtrace : Tendsto r (𝓝[<] 1) (𝓝 (R 1)) :=
    ((hRC.continuousWithinAt ⟨zero_le_one, le_rfl⟩).tendsto.comp hRi).congr'
      (hRdom.mono fun x hx => hReq hx)
  refine ⟨hQI, hpI, hRAC, hReq, ?_, hLtrace, hRtrace, ?_⟩
  · intro x hx
    have heq : R =ᶠ[𝓝 x] r :=
      (show ∀ᶠ y in 𝓝 x, y ∈ Ioo (0 : ℝ) 1 from isOpen_Ioo.mem_nhds hx).mono
        fun y hy => hReq hy
    exact (h.2.1.weakDeriv.hasDerivAt_of_continuousOn hr hp hx).congr_of_eventuallyEq heq
  · obtain ⟨B, hB⟩ := isCompact_Icc.exists_bound_of_continuousOn hRC
    refine ⟨B, ?_⟩
    intro x hx
    rw [← hReq hx]
    simpa only [Real.norm_eq_abs] using hB x ⟨hx.1.le, hx.2.le⟩

end RicciFlowSharpEstimate.Geometry.AreaProfile
