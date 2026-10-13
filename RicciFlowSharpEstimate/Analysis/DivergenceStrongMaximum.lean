/-
Copyright (c) 2026 Ziyang Qin. All rights reserved.
No license is granted by this file.
Authors: Ziyang Qin
-/
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# A one-dimensional strong divergence maximum principle

A nonnegative interior `C¹` function satisfying a weak divergence inequality is
strictly positive unless it vanishes identically. The diffusion coefficient is
continuous and strictly positive in the interior. The zeroth-order coefficient
is continuous and may have either sign. No endpoint data are needed.
-/

noncomputable section

namespace RicciFlowSharpEstimate.Analysis

open Filter MeasureTheory Set
open scoped Topology

private theorem eq_zero_at_right_of_deriv_le_primitive
    {u v K : ℝ} (huv : u ≤ v) {r R d : ℝ → ℝ}
    (hr : ∀ x ∈ Icc u v, HasDerivAt r (d x) x)
    (hR : ∀ x ∈ Icc u v, HasDerivAt R (r x) x)
    (hrnonneg : ∀ x ∈ Icc u v, 0 ≤ r x)
    (hRnonneg : ∀ x ∈ Icc u v, 0 ≤ R x)
    (hru : r u = 0) (hRu : R u = 0)
    (hbound : ∀ x ∈ Icc u v, d x ≤ K * R x) : r v = 0 := by
  let L : ℝ := max K 1
  let H : ℝ → ℝ := fun x ↦ (r x + R x) * Real.exp (-L * x)
  let D : ℝ → ℝ := fun x ↦
    (d x + r x - L * (r x + R x)) * Real.exp (-L * x)
  have hD : ∀ x ∈ Icc u v, HasDerivAt H (D x) x := by
    intro x hx
    convert ((hr x hx).add (hR x hx)).mul
      (((hasDerivAt_id x).const_mul (-L)).exp) using 1
    all_goals simp only [H, D, Pi.mul_def, Pi.add_def, id_eq]
    all_goals ring
  have hDnonpos : ∀ x ∈ Icc u v, D x ≤ 0 := by
    intro x hx
    have h₁ : K * R x ≤ L * R x :=
      mul_le_mul_of_nonneg_right (le_max_left K 1) (hRnonneg x hx)
    have h₂ : r x ≤ L * r x := by
      simpa only [one_mul] using
        mul_le_mul_of_nonneg_right (le_max_right K 1) (hrnonneg x hx)
    exact mul_nonpos_of_nonpos_of_nonneg
      (by nlinarith [hbound x hx]) (Real.exp_pos _).le
  have hHcont : ContinuousOn H (Icc u v) := fun x hx ↦
    (hD x hx).continuousAt.continuousWithinAt
  have hmono : AntitoneOn H (Icc u v) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc u v) hHcont
    · intro x hx
      exact (hD x (interior_subset hx)).differentiableAt.differentiableWithinAt
    · intro x hx
      rw [(hD x (interior_subset hx)).deriv]
      exact hDnonpos x (interior_subset hx)
  have hHle := hmono (left_mem_Icc.mpr huv) (right_mem_Icc.mpr huv) huv
  have hsum : r v + R v ≤ 0 := by
    have hprod : (r v + R v) * Real.exp (-L * v) ≤ 0 := by
      simpa only [H, hru, hRu, add_zero, zero_mul] using hHle
    by_contra hnot
    have hpos := mul_pos (lt_of_not_ge hnot) (Real.exp_pos (-L * v))
    exact (not_lt_of_ge hprod) hpos
  exact le_antisymm (by linarith [hRnonneg v (right_mem_Icc.mpr huv)])
    (hrnonneg v (right_mem_Icc.mpr huv))

/-- A nonnegative interior `C¹` function satisfying a divergence inequality
with continuous strictly positive diffusion is strictly positive everywhere
in the interior as soon as it is positive at one point. The continuous
zeroth-order coefficient may be signed, and no boundary traces are assumed. -/
theorem pos_of_divergence_inequality_of_nonneg
    {a b : ℝ} (r A G S c : ℝ → ℝ)
    (hr : ContDiffOn ℝ 1 r (Ioo a b))
    (hGac : ∀ u ∈ Ioo a b, ∀ v ∈ Ioo a b, u ≤ v →
      AbsolutelyContinuousOnInterval G u v)
    (hflux : ∀ x ∈ Ioo a b, G x = A x * deriv r x)
    (hAcont : ContinuousOn A (Ioo a b))
    (hApos : ∀ x ∈ Ioo a b, 0 < A x)
    (hc : ContinuousOn c (Ioo a b))
    (hderiv : ∀ᵐ x ∂volume.restrict (Ioo a b), HasDerivAt G (S x) x)
    (hineq : ∀ᵐ x ∂volume.restrict (Ioo a b), S x ≤ c x * r x)
    (hnonneg : ∀ x ∈ Ioo a b, 0 ≤ r x)
    (hpos : ∃ x ∈ Ioo a b, 0 < r x) :
    ∀ x ∈ Ioo a b, 0 < r x := by
  have hrd : ∀ x ∈ Ioo a b, HasDerivAt r (deriv r x) x := by
    intro x hx
    exact (hr.contDiffAt (isOpen_Ioo.mem_nhds hx)).differentiableAt_one.hasDerivAt
  have hrmeas : ∀ x ∈ Ioo a b, StronglyMeasurableAtFilter r (𝓝 x) volume := by
    intro x hx
    exact ⟨Ioo a b, isOpen_Ioo.mem_nhds hx,
      (hr.continuousOn.locallyIntegrableOn measurableSet_Ioo).aestronglyMeasurable⟩
  have hGzero : ∀ x ∈ Ioo a b, r x = 0 → G x = 0 := by
    intro x hx hzero
    have hmin : IsLocalMin r x := by
      filter_upwards [isOpen_Ioo.mem_nhds hx] with y hy
      simpa only [hzero] using hnonneg y hy
    rw [hflux x hx, hmin.deriv_eq_zero, mul_zero]
  have hlocal : ∀ u ∈ Ioo a b, ∀ v ∈ Ioo a b, u ≤ v →
      (r u = 0 → r v = 0) ∧ (r v = 0 → r u = 0) := by
    intro u hu v hv huv
    have hsub : Icc u v ⊆ Ioo a b := by
      intro x hx
      exact ⟨hu.1.trans_le hx.1, hx.2.trans_lt hv.2⟩
    obtain ⟨m, hm, hmA⟩ := isCompact_Icc.exists_forall_le'
      (hAcont.mono hsub) (fun x hx ↦ hApos x (hsub hx))
    obtain ⟨t, _, htmax⟩ := isCompact_Icc.exists_isMaxOn
      (nonempty_Icc.mpr huv) (hc.mono hsub)
    let C : ℝ := max (c t) 0
    have hC : 0 ≤ C := le_max_right _ _
    have hcC : ∀ x ∈ Icc u v, c x ≤ C := by
      intro x hx
      exact (htmax hx).trans (le_max_left _ _)
    have hrint : ∀ s ∈ Icc u v, ∀ t ∈ Icc u v, s ≤ t →
        IntervalIntegrable r volume s t := by
      intro s hs t ht hst
      apply ContinuousOn.intervalIntegrable_of_Icc hst
      apply hr.continuousOn.mono
      intro x hx
      exact hsub ⟨hs.1.trans hx.1, hx.2.trans ht.2⟩
    have hinc : ∀ s ∈ Icc u v, ∀ t ∈ Icc u v, s ≤ t →
        G t - G s ≤ C * ∫ x in s..t, r x := by
      intro s hs t ht hst
      have hstsub : Icc s t ⊆ Ioo a b := by
        intro x hx
        exact hsub ⟨hs.1.trans hx.1, hx.2.trans ht.2⟩
      have hAC := hGac s (hsub hs) t (hsub ht) hst
      have hle : ∀ᵐ x ∂volume.restrict (Icc s t), deriv G x ≤ C * r x := by
        filter_upwards [ae_restrict_of_ae_restrict_of_subset hstsub hderiv,
          ae_restrict_of_ae_restrict_of_subset hstsub hineq,
          ae_restrict_mem measurableSet_Icc] with x hdx hix hx
        rw [hdx.deriv]
        exact hix.trans (mul_le_mul_of_nonneg_right
          (hcC x ⟨hs.1.trans hx.1, hx.2.trans ht.2⟩) (hnonneg x (hstsub hx)))
      have hleint := intervalIntegral.integral_mono_ae_restrict hst
        hAC.intervalIntegrable_deriv ((hrint s hs t ht hst).const_mul C) hle
      rwa [hAC.integral_deriv_eq_sub, intervalIntegral.integral_const_mul] at hleint
    have hdivide : ∀ x ∈ Icc u v, ∀ d Q : ℝ,
        0 ≤ Q → A x * d ≤ C * Q → d ≤ C / m * Q := by
      intro x hx d Q hQ hd
      by_cases hd0 : d ≤ 0
      · exact hd0.trans (mul_nonneg (div_nonneg hC hm.le) hQ)
      · have hmd : m * d ≤ C * Q :=
          (mul_le_mul_of_nonneg_right (hmA x hx) (le_of_not_ge hd0)).trans hd
        rw [div_mul_eq_mul_div]
        exact (le_div_iff₀ hm).mpr (by nlinarith)
    constructor
    · intro hu0
      let R : ℝ → ℝ := fun x ↦ ∫ t in u..x, r t
      have hR : ∀ x ∈ Icc u v, HasDerivAt R (r x) x := by
        intro x hx
        exact intervalIntegral.integral_hasDerivAt_right
          (hrint u (left_mem_Icc.mpr huv) x hx hx.1) (hrmeas x (hsub hx))
          (hrd x (hsub hx)).continuousAt
      have hRnonneg : ∀ x ∈ Icc u v, 0 ≤ R x := by
        intro x hx
        exact intervalIntegral.integral_nonneg hx.1 fun t ht ↦
          hnonneg t (hsub ⟨ht.1, ht.2.trans hx.2⟩)
      apply eq_zero_at_right_of_deriv_le_primitive (K := C / m) huv
        (fun x hx ↦ hrd x (hsub hx)) hR
        (fun x hx ↦ hnonneg x (hsub hx)) hRnonneg hu0
        (by simp [R])
      intro x hx
      apply hdivide x hx (deriv r x) (R x) (hRnonneg x hx)
      have hbound := hinc u (left_mem_Icc.mpr huv) x hx hx.1
      simpa only [hGzero u hu hu0, sub_zero, hflux x (hsub hx)] using hbound
    · intro hv0
      let R : ℝ → ℝ := fun x ↦ ∫ t in x..v, r t
      have hR : ∀ x ∈ Icc u v, HasDerivAt R (-r x) x := by
        intro x hx
        exact intervalIntegral.integral_hasDerivAt_left
          (hrint x hx v (right_mem_Icc.mpr huv) hx.2) (hrmeas x (hsub hx))
          (hrd x (hsub hx)).continuousAt
      have hRnonneg : ∀ x ∈ Icc u v, 0 ≤ R x := by
        intro x hx
        exact intervalIntegral.integral_nonneg hx.2 fun t ht ↦
          hnonneg t (hsub ⟨hx.1.trans ht.1, ht.2⟩)
      have hreflect : ∀ x ∈ Icc (-v) (-u), -x ∈ Icc u v := by
        intro x hx
        constructor <;> linarith [hx.1, hx.2]
      have hreflected : r (- -u) = 0 := by
        apply eq_zero_at_right_of_deriv_le_primitive (neg_le_neg huv)
          (r := fun x ↦ r (-x)) (R := fun x ↦ R (-x))
          (d := fun x ↦ -deriv r (-x)) (K := C / m)
        · intro x hx
          simpa only [Function.comp_def, mul_neg, mul_one] using
            (hrd (-x) (hsub (hreflect x hx))).comp x (hasDerivAt_id x).neg
        · intro x hx
          simpa only [Function.comp_def, mul_neg, mul_one, neg_neg] using
            (hR (-x) (hreflect x hx)).comp x (hasDerivAt_id x).neg
        · intro x hx
          exact hnonneg (-x) (hsub (hreflect x hx))
        · intro x hx
          exact hRnonneg (-x) (hreflect x hx)
        · simpa only [neg_neg] using hv0
        · simp [R]
        · intro x hx
          have hx' := hreflect x hx
          apply hdivide (-x) hx' (-deriv r (-x)) (R (-x)) (hRnonneg (-x) hx')
          have hbound := hinc (-x) hx' v (right_mem_Icc.mpr huv) hx'.2
          simpa only [hGzero v hv hv0, zero_sub, hflux (-x) (hsub hx'), mul_neg]
            using hbound
      simpa only [neg_neg] using hreflected
  obtain ⟨y, hy, hry⟩ := hpos
  intro x hx
  by_contra hnotpos
  have hxzero : r x = 0 := le_antisymm (le_of_not_gt hnotpos) (hnonneg x hx)
  have hyzero : r y = 0 := by
    rcases le_total x y with hxy | hyx
    · exact (hlocal x hx y hy hxy).1 hxzero
    · exact (hlocal y hy x hx hyx).2 hxzero
  exact (ne_of_gt hry) hyzero

end RicciFlowSharpEstimate.Analysis
