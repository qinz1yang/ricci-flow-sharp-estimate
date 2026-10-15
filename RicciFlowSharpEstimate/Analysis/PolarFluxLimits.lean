/-
Copyright (c) 2026 Ziyang Qin. All rights reserved.
No license is granted by this file.
Authors: Ziyang Qin
-/
import RicciFlowSharpEstimate.Analysis.PolarFluxIntegrability
import RicciFlowSharpEstimate.Analysis.IntegrableDerivativeExtension
import RicciFlowSharpEstimate.Analysis.IntegrableBoundaryTrace
import Mathlib.Analysis.Calculus.ContDiff.Operations

/-! # Vanishing first-order rates of genuine coordinate-weighted fluxes -/

noncomputable section
namespace RicciFlowSharpEstimate.Analysis
open Set MeasureTheory Filter Topology

/-- A true AC zero flux whose derivative is x times an L1 source is o(x) at
zero. Integrability of its squared-distance quotient forces the trace. -/
theorem tendsto_div_zero_of_coordinate_derivative {b : ℝ} {F g : ℝ → ℝ}
    (hb : 0 < b) (hF : AbsolutelyContinuousOnInterval F 0 b) (h0 : F 0 = 0)
    (hD : ∀ᵐ x ∂volume.restrict (Ioo 0 b), HasDerivAt F (x * g x) x)
    (hg : IntegrableOn g (Ioo 0 b) volume) :
    Tendsto (fun x => F x / x) (𝓝[>] 0) (𝓝 0) := by
  let u := fun x => F x / x
  have hQ := integrableOn_div_sq_of_coordinate_derivative hF h0 hD hg
  have hu (c : ℝ) (hc : c ∈ Ioo 0 b) (d : ℝ) (hd : d ∈ Ioo 0 b) :
      AbsolutelyContinuousOnInterval u c d := by
    have hs := ordConnected_Ioo.uIcc_subset hc hd
    have hFc := hF.mono (show uIcc c d ⊆ uIcc (0 : ℝ) b by
      simpa only [uIcc_of_le hb.le] using hs.trans Ioo_subset_Icc_self)
    have hInv : ContDiffOn ℝ 1 (fun x : ℝ => x⁻¹) (uIcc c d) := by
      apply contDiffOn_id.inv
      intro x hx
      exact (hs hx).1.ne'
    change AbsolutelyContinuousOnInterval (fun x => F x * x⁻¹) c d
    exact hFc.fun_mul hInv.absolutelyContinuousOnInterval
  have hUD : ∀ᵐ x ∂volume.restrict (Ioo 0 b),
      HasDerivAt u (g x - F x / x ^ 2) x := by
    filter_upwards [hD, ae_restrict_mem measurableSet_Ioo] with x hx hxI
    have hh := hx.div (hasDerivAt_id x) hxI.1.ne'
    change HasDerivAt u _ x at hh
    apply hh.congr_deriv
    simp only [id_eq]
    field_simp [hxI.1.ne']
  obtain ⟨U, hUAC, hEq, hLT, _, _⟩ :=
    exists_boundary_extension_of_integrable_deriv hb hu hUD (hg.sub hQ)
  have hUC : ContinuousOn U (Icc (0 : ℝ) b) := by
    simpa only [uIcc_of_le hb.le] using hUAC.continuousOn
  have hUQ : IntegrableOn (fun x => U x / (x - 0)) (Ioo 0 b) volume := by
    apply hQ.congr
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
    rw [hEq hx]
    dsimp only [u]
    simp only [sub_zero]
    field_simp [hx.1.ne']
  have hU0 := eq_zero_of_integrableOn_div_left hb hUC hUQ
  simpa only [hU0] using hLT

/-- The matching right-pole rate uses the actual zero trace at b and the
actual derivative (b-x)*g. It does not require a pointwise source limit. -/
theorem tendsto_div_sub_zero_of_distance_derivative {b : ℝ} {F g : ℝ → ℝ}
    (hb : 0 < b) (hF : AbsolutelyContinuousOnInterval F 0 b) (h1 : F b = 0)
    (hD : ∀ᵐ x ∂volume.restrict (Ioo 0 b), HasDerivAt F ((b - x) * g x) x)
    (hg : IntegrableOn g (Ioo 0 b) volume) :
    Tendsto (fun x => F x / (b - x)) (𝓝[<] b) (𝓝 0) := by
  let u := fun x => F x / (b - x)
  have hQ := integrableOn_div_sub_sq_of_distance_derivative hF h1 hD hg
  have hu (c : ℝ) (hc : c ∈ Ioo 0 b) (d : ℝ) (hd : d ∈ Ioo 0 b) :
      AbsolutelyContinuousOnInterval u c d := by
    have hs := ordConnected_Ioo.uIcc_subset hc hd
    have hFc := hF.mono (show uIcc c d ⊆ uIcc (0 : ℝ) b by
      simpa only [uIcc_of_le hb.le] using hs.trans Ioo_subset_Icc_self)
    have hInv : ContDiffOn ℝ 1 (fun x : ℝ => (b - x)⁻¹) (uIcc c d) := by
      apply (contDiffOn_const.sub contDiffOn_id).inv
      intro x hx
      exact (sub_pos.mpr (hs hx).2).ne'
    change AbsolutelyContinuousOnInterval (fun x => F x * (b - x)⁻¹) c d
    exact hFc.fun_mul hInv.absolutelyContinuousOnInterval
  have hUD : ∀ᵐ x ∂volume.restrict (Ioo 0 b),
      HasDerivAt u (g x + F x / (b - x) ^ 2) x := by
    filter_upwards [hD, ae_restrict_mem measurableSet_Ioo] with x hx hxI
    have hh := hx.div ((hasDerivAt_const x b).sub (hasDerivAt_id x))
      (sub_pos.mpr hxI.2).ne'
    change HasDerivAt u _ x at hh
    apply hh.congr_deriv
    simp only [Pi.sub_apply, id_eq]
    field_simp [(sub_pos.mpr hxI.2).ne']
    ring
  obtain ⟨U, hUAC, hEq, _, hRT, _⟩ :=
    exists_boundary_extension_of_integrable_deriv hb hu hUD (hg.add hQ)
  have hUC : ContinuousOn U (Icc (0 : ℝ) b) := by
    simpa only [uIcc_of_le hb.le] using hUAC.continuousOn
  have hUQ : IntegrableOn (fun x => U x / (b - x)) (Ioo 0 b) volume := by
    apply hQ.congr
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
    rw [hEq hx]
    dsimp only [u]
    field_simp [(sub_pos.mpr hx.2).ne']
  have hU1 := eq_zero_of_integrableOn_div_right hb hUC hUQ
  simpa only [hU1] using hRT

end RicciFlowSharpEstimate.Analysis
