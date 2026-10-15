/-
Copyright (c) 2026 Ziyang Qin. All rights reserved.
No license is granted by this file.
Authors: Ziyang Qin
-/
import RicciFlowSharpEstimate.Analysis.IntegrableBoundaryTrace
import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun

/-! # Zero boundary extensions from genuine integrable derivatives -/

noncomputable section
namespace RicciFlowSharpEstimate.Analysis
open Set MeasureTheory Filter Topology

/-- A locally absolutely continuous function with integrable derivative and
integrable reciprocal-distance quotients extends absolutely continuously with
zero values at both endpoints. The extension agrees throughout the interior. -/
theorem exists_zero_boundary_extension_of_integrable_deriv
    {a b : ℝ} {u v : ℝ → ℝ} (hab : a < b)
    (hu : ∀ c ∈ Ioo a b, ∀ d ∈ Ioo a b, AbsolutelyContinuousOnInterval u c d)
    (hd : ∀ᵐ x ∂volume.restrict (Ioo a b), HasDerivAt u (v x) x)
    (hv : IntegrableOn v (Ioo a b))
    (hL : IntegrableOn (fun x => u x / (x - a)) (Ioo a b))
    (hR : IntegrableOn (fun x => u x / (b - x)) (Ioo a b)) :
    ∃ U : ℝ → ℝ, AbsolutelyContinuousOnInterval U a b ∧ EqOn U u (Ioo a b) ∧
      U a = 0 ∧ U b = 0 ∧
      Tendsto u (𝓝[>] a) (𝓝 0) ∧ Tendsto u (𝓝[<] b) (𝓝 0) := by
  let c := (a + b) / 2
  have hc : c ∈ Ioo a b := by dsimp only [c]; constructor <;> linarith
  let U := fun x => u c + ∫ t in c..x, v t
  have hvI : IntervalIntegrable v volume a b :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le hab.le).mpr hv
  have hUAC : AbsolutelyContinuousOnInterval U a b :=
    (contDiff_const : ContDiff ℝ 1 (fun _ : ℝ => u c)).contDiffOn.absolutelyContinuousOnInterval
      |>.fun_add (hvI.absolutelyContinuousOnInterval_intervalIntegral (by
        rw [uIcc_of_le hab.le]; exact ⟨hc.1.le, hc.2.le⟩))
  have hEq : EqOn U u (Ioo a b) := by
    intro x hx
    have hi := (hu c hc x hx).integral_deriv_eq_sub
    have heq : (∫ t in c..x, deriv u t) = ∫ t in c..x, v t := by
      apply intervalIntegral.integral_congr_ae
      filter_upwards [ae_imp_of_ae_restrict hd] with t ht htI
      exact (ht (ordConnected_Ioo.uIcc_subset hc hx (uIoc_subset_uIcc htI))).deriv
    rw [heq] at hi
    change u c + (∫ t in c..x, v t) = u x
    linarith only [hi]
  have hUC : ContinuousOn U (Icc a b) := by
    simpa only [uIcc_of_le hab.le] using hUAC.continuousOn
  have hUL : IntegrableOn (fun x => U x / (x - a)) (Ioo a b) := by
    apply hL.congr
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
    rw [hEq hx]
  have hUR : IntegrableOn (fun x => U x / (b - x)) (Ioo a b) := by
    apply hR.congr
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
    rw [hEq hx]
  have hU0 := eq_zero_of_integrableOn_div_left hab hUC hUL
  have hU1 := eq_zero_of_integrableOn_div_right hab hUC hUR
  have hLD : ∀ᶠ x in 𝓝[>] a, x ∈ Ioo a b := Ioo_mem_nhdsGT hab
  have hRD : ∀ᶠ x in 𝓝[<] b, x ∈ Ioo a b := Ioo_mem_nhdsLT hab
  have hLT : Tendsto (fun x : ℝ => x) (𝓝[>] a) (𝓝[Icc a b] a) :=
    tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
      (tendsto_id.mono_left nhdsWithin_le_nhds)
      (hLD.mono fun _ hx => ⟨hx.1.le, hx.2.le⟩)
  have hRT : Tendsto (fun x : ℝ => x) (𝓝[<] b) (𝓝[Icc a b] b) :=
    tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
      (tendsto_id.mono_left nhdsWithin_le_nhds)
      (hRD.mono fun _ hx => ⟨hx.1.le, hx.2.le⟩)
  refine ⟨U, hUAC, hEq, hU0, hU1, ?_, ?_⟩
  · simpa only [hU0] using
      (((hUC.continuousWithinAt ⟨le_rfl, hab.le⟩).tendsto.comp hLT).congr'
        (hLD.mono fun _ hx => hEq hx))
  · simpa only [hU1] using
      (((hUC.continuousWithinAt ⟨hab.le, le_rfl⟩).tendsto.comp hRT).congr'
        (hRD.mono fun _ hx => hEq hx))

end RicciFlowSharpEstimate.Analysis
