/-
Copyright (c) 2026 Ziyang Qin. All rights reserved.
No license is granted by this file.
Authors: Ziyang Qin
-/
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# A one-dimensional divergence maximum principle

A locally absolutely continuous flux with zero endpoint traces controls the negative
part of an interior `C¹` function. The diffusion coefficient may vanish, and the
function itself need not have endpoint values or limits. Only the flux is required
to extend continuously to the endpoints.
-/

noncomputable section

namespace RicciFlowSharpEstimate.Analysis

open Filter MeasureTheory Set
open scoped Topology

private theorem antitoneOn_of_local_ac_of_ae_deriv_nonpos
    {a b : ℝ} {H : ℝ → ℝ}
    (hHac : ∀ u ∈ Ioo a b, ∀ v ∈ Ioo a b, u ≤ v →
      AbsolutelyContinuousOnInterval H u v)
    (hd : ∀ᵐ x ∂volume.restrict (Ioo a b), deriv H x ≤ 0) :
    AntitoneOn H (Ioo a b) := by
  intro u hu v hv huv
  have hsub : Icc u v ⊆ Ioo a b := by
    intro x hx
    exact ⟨hu.1.trans_le hx.1, hx.2.trans_lt hv.2⟩
  have hloc := hHac u hu v hv huv
  have hle := intervalIntegral.integral_mono_ae_restrict huv
    hloc.intervalIntegrable_deriv
    (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ ↦ (0 : ℝ)) volume u v)
    (ae_restrict_of_ae_restrict_of_subset hsub hd)
  rw [hloc.integral_deriv_eq_sub] at hle
  simp only [intervalIntegral.integral_zero] at hle
  linarith

private theorem eq_zero_of_antitoneOn_of_zero_flux_bound
    {a b : ℝ} (hab : a < b) {H G : ℝ → ℝ}
    (hG : ContinuousOn G (Icc a b)) (hGa : G a = 0) (hGb : G b = 0)
    (hbound : ∀ x, ‖H x‖ ≤ ‖G x‖)
    (hmono : AntitoneOn H (Ioo a b)) :
    ∀ x ∈ Ioo a b, H x = 0 := by
  have hGa' : Tendsto G (𝓝[Ioo a b] a) (𝓝 0) := by
    simpa only [ContinuousWithinAt, hGa] using
      (hG a ⟨le_rfl, hab.le⟩).mono Ioo_subset_Icc_self
  have hGb' : Tendsto G (𝓝[Ioo a b] b) (𝓝 0) := by
    simpa only [ContinuousWithinAt, hGb] using
      (hG b ⟨hab.le, le_rfl⟩).mono Ioo_subset_Icc_self
  have hHa : Tendsto H (𝓝[Ioo a b] a) (𝓝 0) :=
    squeeze_zero_norm hbound (by simpa only [norm_zero] using hGa'.norm)
  have hHb : Tendsto H (𝓝[Ioo a b] b) (𝓝 0) :=
    squeeze_zero_norm hbound (by simpa only [norm_zero] using hGb'.norm)
  let : NeBot (𝓝[Ioo a b] a) := left_nhdsWithin_Ioo_neBot hab
  let : NeBot (𝓝[Ioo a b] b) := right_nhdsWithin_Ioo_neBot hab
  intro x hx
  have hleft : H x ≤ 0 := by
    apply ge_of_tendsto hHa
    filter_upwards [self_mem_nhdsWithin,
      nhdsWithin_le_nhds (gt_mem_nhds hx.1)] with y hy hyx
    exact hmono hy hx hyx.le
  have hright : 0 ≤ H x := by
    apply le_of_tendsto hHb
    filter_upwards [self_mem_nhdsWithin,
      nhdsWithin_le_nhds (lt_mem_nhds hx.2)] with y hy hxy
    exact hmono hx hy hxy.le
  exact le_antisymm hleft hright

/-- A divergence inequality with a nonnegative diffusion coefficient, strictly
positive zeroth-order coefficient, and zero endpoint flux forces an interior
`C¹` function to be nonnegative. The function has no boundary regularity or
boundary-value assumptions. -/
theorem nonneg_of_divergence_inequality
    {a b : ℝ} (hab : a < b) (r A G S c : ℝ → ℝ)
    (hr : ContDiffOn ℝ 1 r (Ioo a b))
    (hG : ContinuousOn G (Icc a b)) (hGa : G a = 0) (hGb : G b = 0)
    (hGac : ∀ u ∈ Ioo a b, ∀ v ∈ Ioo a b, u ≤ v →
      AbsolutelyContinuousOnInterval G u v)
    (hflux : ∀ x ∈ Ioo a b, G x = A x * deriv r x)
    (hA : ∀ x ∈ Ioo a b, 0 ≤ A x)
    (hderiv : ∀ᵐ x ∂volume.restrict (Ioo a b), HasDerivAt G (S x) x)
    (hineq : ∀ᵐ x ∂volume.restrict (Ioo a b), S x ≤ c x * r x)
    (hc : ∀ᵐ x ∂volume.restrict (Ioo a b), 0 < c x) :
    ∀ x ∈ Ioo a b, 0 ≤ r x := by
  let ψ : ℝ → ℝ := fun x ↦ Real.smoothTransition (-r x)
  let H : ℝ → ℝ := fun x ↦ G x * ψ x
  let D : ℝ → ℝ := fun x ↦ S x * ψ x +
    G x * (deriv Real.smoothTransition (-r x) * (-deriv r x))
  have hψC : ContDiffOn ℝ 1 ψ (Ioo a b) :=
    Real.smoothTransition.contDiff.comp_contDiffOn hr.neg
  have hψderiv : ∀ x ∈ Ioo a b,
      HasDerivAt ψ (deriv Real.smoothTransition (-r x) * (-deriv r x)) x := by
    intro x hx
    have hrx := (hr.contDiffAt (isOpen_Ioo.mem_nhds hx)).differentiableAt_one
    have htx := (Real.smoothTransition.contDiff :
      ContDiff ℝ 1 Real.smoothTransition).differentiable_one (-r x)
    exact htx.hasDerivAt.comp x hrx.hasDerivAt.neg
  have hHac : ∀ u ∈ Ioo a b, ∀ v ∈ Ioo a b, u ≤ v →
      AbsolutelyContinuousOnInterval H u v := by
    intro u hu v hv huv
    have hsub : uIcc u v ⊆ Ioo a b := by
      rw [uIcc_of_le huv]
      intro x hx
      exact ⟨hu.1.trans_le hx.1, hx.2.trans_lt hv.2⟩
    exact (hGac u hu v hv huv).fun_mul
      (hψC.mono hsub).absolutelyContinuousOnInterval
  have hHderiv : ∀ᵐ x ∂volume.restrict (Ioo a b), HasDerivAt H (D x) x := by
    filter_upwards [hderiv, ae_restrict_mem measurableSet_Ioo] with x hdx hx
    exact hdx.mul (hψderiv x hx)
  have hsecond : ∀ x ∈ Ioo a b,
      G x * (deriv Real.smoothTransition (-r x) * (-deriv r x)) ≤ 0 := by
    intro x hx
    rw [hflux x hx]
    calc
      _ = -(A x * deriv Real.smoothTransition (-r x) * (deriv r x) ^ 2) := by
        ring
      _ ≤ 0 := neg_nonpos.mpr
        (mul_nonneg (mul_nonneg (hA x hx) Real.smoothTransition.monotone.deriv_nonneg)
          (sq_nonneg (deriv r x)))
  have hDnonpos : ∀ᵐ x ∂volume.restrict (Ioo a b), D x ≤ 0 := by
    filter_upwards [hineq, hc, ae_restrict_mem measurableSet_Ioo] with x hix hcx hx
    have hfirst : S x * ψ x ≤ 0 := by
      by_cases hneg : r x < 0
      · exact mul_nonpos_of_nonpos_of_nonneg
          (hix.trans_lt (mul_neg_of_pos_of_neg hcx hneg)).le
          (Real.smoothTransition.nonneg _)
      · have hψzero : ψ x = 0 :=
          Real.smoothTransition.zero_of_nonpos (neg_nonpos.mpr (le_of_not_gt hneg))
        rw [hψzero, mul_zero]
    exact add_nonpos hfirst (hsecond x hx)
  have hmono : AntitoneOn H (Ioo a b) := by
    apply antitoneOn_of_local_ac_of_ae_deriv_nonpos hHac
    filter_upwards [hHderiv, hDnonpos] with x hdx hDx
    rwa [hdx.deriv]
  have hbound : ∀ x, ‖H x‖ ≤ ‖G x‖ := by
    intro x
    calc
      ‖H x‖ = ‖G x‖ * Real.smoothTransition (-r x) := by
        simp only [H, ψ, norm_mul, Real.norm_eq_abs,
          abs_of_nonneg (Real.smoothTransition.nonneg _)]
      _ ≤ ‖G x‖ * 1 := mul_le_mul_of_nonneg_left
        (Real.smoothTransition.le_one _) (norm_nonneg _)
      _ = ‖G x‖ := mul_one _
  have hHzero : ∀ x ∈ Ioo a b, H x = 0 :=
    eq_zero_of_antitoneOn_of_zero_flux_bound hab hG hGa hGb hbound hmono
  have hψzero_ae : ψ =ᵐ[volume.restrict (Ioo a b)] (fun _ ↦ 0) := by
    filter_upwards [hHderiv, hineq, hc, ae_restrict_mem measurableSet_Ioo]
      with x hdx hix hcx hx
    have h0 : HasDerivAt H 0 x := by
      apply (hasDerivAt_const x (0 : ℝ)).congr_of_eventuallyEq
      filter_upwards [isOpen_Ioo.mem_nhds hx] with y hy
      exact hHzero y hy
    have hDx : D x = 0 := hdx.unique h0
    have hrx : 0 ≤ r x := by
      by_contra hneg
      have hrneg : r x < 0 := lt_of_not_ge hneg
      have hSneg : S x < 0 := hix.trans_lt (mul_neg_of_pos_of_neg hcx hrneg)
      have hψpos : 0 < ψ x := Real.smoothTransition.pos_of_pos (neg_pos.mpr hrneg)
      have hDneg : D x < 0 := add_neg_of_neg_of_nonpos
        (mul_neg_of_neg_of_pos hSneg hψpos) (hsecond x hx)
      exact (ne_of_lt hDneg) hDx
    exact Real.smoothTransition.zero_of_nonpos (neg_nonpos.mpr hrx)
  have hψzero : EqOn ψ (fun _ ↦ 0) (Ioo a b) :=
    MeasureTheory.Measure.eqOn_open_of_ae_eq hψzero_ae isOpen_Ioo
      hψC.continuousOn continuousOn_const
  intro x hx
  have hneg : -r x ≤ 0 := Real.smoothTransition.zero_iff_nonpos.mp (hψzero hx)
  exact neg_nonpos.mp hneg

end RicciFlowSharpEstimate.Analysis
