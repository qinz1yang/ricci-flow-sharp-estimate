/-
Copyright (c) 2026 Ziyang Qin. All rights reserved.
No license is granted by this file.
Authors: Ziyang Qin
-/
import RicciFlowSharpEstimate.Geometry.AreaGroundStateComparison
import Mathlib.Analysis.Calculus.DerivativeTest

/-!
# Maximum principle for the actual area-coordinate meridional operator

Positive continuous curvature and its two exact moments give the physical
warping coefficient and the two pole slopes. A nonpositive meridional operator
then forces every C² probe to be nonnegative, with no conditions on the probe
or its derivatives at the poles. A strictly negative source forces positivity
on the entire closed interval.
-/

noncomputable section

namespace RicciFlowSharpEstimate.Geometry.AreaProfile

open Set Filter MeasureTheory
open scoped ContDiff Topology

private theorem neg_curvature_mul_le_operator_of_isMinOn (K r : ℝ → ℝ)
    (hK : Continuous K) (hpos : ∀ x ∈ Icc (0 : ℝ) 1, 0 < K x)
    (hr : ContDiff ℝ 2 r)
    (hzero : (∫ x in (0 : ℝ)..1, K x) = 2)
    (hone : (∫ x in (0 : ℝ)..1, x * K x) = 1)
    (x : ℝ) (hx : x ∈ Icc (0 : ℝ) 1)
    (hmin : IsMinOn r (Icc (0 : ℝ) 1) x) :
    -(K x * r x) ≤ meridionalOperator K r x := by
  by_cases hx0 : x = 0
  · subst x
    have ht : (1 : ℝ) ∈ posTangentConeAt (Icc (0 : ℝ) 1) 0 := by
      have hseg : segment ℝ (0 : ℝ) 1 ⊆ Icc (0 : ℝ) 1 :=
        (convex_Icc 0 1).segment_subset (by norm_num) (by norm_num)
      simpa only [sub_zero] using
        sub_mem_posTangentConeAt_of_segment_subset hseg
    have hD := (hr.differentiable (by norm_num) 0).hasDerivAt
    have hsign : 0 ≤ deriv r 0 := by
      simpa using hmin.isLocalMinOn.hasFDerivWithinAt_nonneg
        hD.hasFDerivAt.hasFDerivWithinAt ht
    simp only [meridionalOperator, warp_zero, warpSlope_zero, zero_mul, zero_add]
    linarith
  by_cases hx1 : x = 1
  · subst x
    have ht : (-1 : ℝ) ∈ posTangentConeAt (Icc (0 : ℝ) 1) 1 := by
      have hseg : segment ℝ (1 : ℝ) 0 ⊆ Icc (0 : ℝ) 1 :=
        (convex_Icc 0 1).segment_subset (by norm_num) (by norm_num)
      simpa only [zero_sub] using
        sub_mem_posTangentConeAt_of_segment_subset hseg
    have hD := (hr.differentiable (by norm_num) 1).hasDerivAt
    have hsign : deriv r 1 ≤ 0 := by
      have h := hmin.isLocalMinOn.hasFDerivWithinAt_nonneg
        hD.hasFDerivAt.hasFDerivWithinAt ht
      simpa using h
    simp only [meridionalOperator, warp_one K hK hzero hone,
      warpSlope_one K hzero, zero_mul, zero_add]
    linarith
  have hxi : x ∈ Ioo (0 : ℝ) 1 :=
    ⟨lt_of_le_of_ne hx.1 (Ne.symm hx0), lt_of_le_of_ne hx.2 hx1⟩
  have hlocal : IsLocalMin r x := hmin.isLocalMin (Icc_mem_nhds hxi.1 hxi.2)
  have hD : deriv r x = 0 := hlocal.deriv_eq_zero
  have hD2 : 0 ≤ deriv (deriv r) x := by
    by_contra hn
    have hneg : deriv (deriv r) x < 0 := lt_of_not_ge hn
    have hmax : IsLocalMax r x :=
      isLocalMax_of_deriv_deriv_neg hneg hD hr.continuous.continuousAt
    have hconst : r =ᶠ[𝓝 x] (fun _ : ℝ => r x) := by
      filter_upwards [hlocal, hmax] with y hymin hymax
      exact le_antisymm hymax hymin
    have hDconst : deriv r =ᶠ[𝓝 x] (fun _ : ℝ => 0) := by
      filter_upwards [hconst.deriv] with y hy
      simpa only [deriv_const] using hy
    have hD2zero : deriv (deriv r) x = 0 := by
      simpa only [deriv_const] using hDconst.deriv_eq
    exact (ne_of_lt hneg) hD2zero
  have hwarp : 0 ≤ warp K x :=
    (warp_pos_of_moments K hK hpos hzero hone x hxi).le
  have hprod := mul_nonneg hwarp hD2
  simp only [meridionalOperator, hD, mul_zero, add_zero]
  linarith

/-- The actual physical meridional operator has a maximum principle on the
closed normalized interval, without probe or derivative pole conditions. -/
theorem nonneg_of_meridionalOperator_nonpos (K r : ℝ → ℝ)
    (hK : Continuous K) (hpos : ∀ x ∈ Icc (0 : ℝ) 1, 0 < K x)
    (hr : ContDiff ℝ 2 r)
    (hzero : (∫ x in (0 : ℝ)..1, K x) = 2)
    (hone : (∫ x in (0 : ℝ)..1, x * K x) = 1)
    (hL : ∀ x ∈ Icc (0 : ℝ) 1, meridionalOperator K r x ≤ 0) :
    ∀ x ∈ Icc (0 : ℝ) 1, 0 ≤ r x := by
  obtain ⟨z, hz, hmin⟩ := isCompact_Icc.exists_isMinOn
    (show (Icc (0 : ℝ) 1).Nonempty from ⟨0, by norm_num⟩)
    hr.continuous.continuousOn
  have hbound := neg_curvature_mul_le_operator_of_isMinOn
    K r hK hpos hr hzero hone z hz hmin
  have hznonneg : 0 ≤ r z := by
    by_contra hn
    have hprod : K z * r z < 0 :=
      mul_neg_of_pos_of_neg (hpos z hz) (lt_of_not_ge hn)
    have hLz := hL z hz
    linarith
  intro x hx
  exact hznonneg.trans (hmin hx)

/-- A strictly negative actual meridional source forces strict positivity of
the same probe at every point, including both physical poles. -/
theorem pos_of_meridionalOperator_neg (K r : ℝ → ℝ)
    (hK : Continuous K) (hpos : ∀ x ∈ Icc (0 : ℝ) 1, 0 < K x)
    (hr : ContDiff ℝ 2 r)
    (hzero : (∫ x in (0 : ℝ)..1, K x) = 2)
    (hone : (∫ x in (0 : ℝ)..1, x * K x) = 1)
    (hL : ∀ x ∈ Icc (0 : ℝ) 1, meridionalOperator K r x < 0) :
    ∀ x ∈ Icc (0 : ℝ) 1, 0 < r x := by
  have hnonneg := nonneg_of_meridionalOperator_nonpos K r hK hpos hr hzero hone
    (fun x hx => (hL x hx).le)
  intro x hx
  by_contra hn
  have hrzero : r x = 0 := le_antisymm (le_of_not_gt hn) (hnonneg x hx)
  have hmin : IsMinOn r (Icc (0 : ℝ) 1) x := by
    intro y hy
    rw [hrzero]
    exact hnonneg y hy
  have hbound := neg_curvature_mul_le_operator_of_isMinOn
    K r hK hpos hr hzero hone x hx hmin
  rw [hrzero, mul_zero, neg_zero] at hbound
  exact (not_le_of_gt (hL x hx)) hbound

/-- Strict negativity of the actual meridional source supplies the positive
reference required by complete Picone comparison. No reference-sign hypothesis
is imposed in this version of the same-geometry all-probe certificate. -/
theorem meridionalAction_ge_mass_of_negative_source
    (C lam : ℝ) (K r : ℝ → ℝ) (hK : IsSmoothAreaCurvature C K)
    (hr : ContDiff ℝ ∞ r)
    (heigen : ∀ x ∈ Icc (0 : ℝ) 1, meridionalJacobiOperator K r x = lam * r x)
    (hoperator : ∀ x ∈ Icc (0 : ℝ) 1, meridionalOperator K r x < 0) :
    ∀ s : ℝ → ℝ, ContDiff ℝ ∞ s → lam * probeMass K s ≤ meridionalAction K s := by
  obtain ⟨κ, Λ, hκ, hbox, _⟩ := hK.2.1
  have hpos : ∀ x ∈ Icc (0 : ℝ) 1, 0 < K x :=
    fun x hx => hκ.trans_le (hbox x hx).1
  have hrpos := pos_of_meridionalOperator_neg K r hK.1.continuous hpos
    (hr.of_le (by simp)) hK.2.2.1 hK.2.2.2 hoperator
  exact meridionalAction_ge_mass_of_ground_state C lam K r hK hr hrpos heigen
    (fun x hx => (hoperator x hx).le)

end RicciFlowSharpEstimate.Geometry.AreaProfile
