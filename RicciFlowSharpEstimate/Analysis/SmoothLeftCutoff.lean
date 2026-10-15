/-
Copyright (c) 2026 Ziyang Qin. All rights reserved.
No license is granted by this file.
Authors: Ziyang Qin
-/
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Smooth cutoffs of a left half-line

The transition has width `ε` and lies to the left of `c`. Both derivative
bounds come from one fixed smooth transition; no derivative of any coefficient
or input probe is used.
-/

noncomputable section

namespace RicciFlowSharpEstimate.Analysis

open Set Filter
open scoped ContDiff Topology

/-- A smooth cutoff equal to one to the left of `c - ε` and zero to the right
of `c`, when `ε` is positive. -/
def smoothLeftCutoff (c ε x : ℝ) : ℝ := Real.smoothTransition ((c - x) / ε)

/-- Every fixed smooth left cutoff is globally smooth. -/
theorem contDiff_smoothLeftCutoff (c ε : ℝ) : ContDiff ℝ ∞ (smoothLeftCutoff c ε) := by
  exact Real.smoothTransition.contDiff.comp ((contDiff_const.sub contDiff_id).div_const ε)

/-- The cutoff takes values in the unit interval. -/
theorem smoothLeftCutoff_mem_Icc (c ε x : ℝ) : smoothLeftCutoff c ε x ∈ Icc (0 : ℝ) 1 :=
  ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩

/-- The cutoff is one before its transition interval. -/
theorem smoothLeftCutoff_eq_one {c ε x : ℝ} (hε : 0 < ε) (hx : x ≤ c - ε) :
    smoothLeftCutoff c ε x = 1 := by
  apply Real.smoothTransition.one_of_one_le
  apply (le_div_iff₀ hε).mpr
  linarith

/-- The cutoff is zero at and after the cutting point. -/
theorem smoothLeftCutoff_eq_zero {c ε x : ℝ} (hε : 0 < ε) (hx : c ≤ x) :
    smoothLeftCutoff c ε x = 0 := by
  exact Real.smoothTransition.zero_of_nonpos
    (div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hx) hε.le)

private theorem smoothLeftCutoff_deriv (c ε : ℝ) :
    deriv (smoothLeftCutoff c ε) =
      fun x ↦ deriv Real.smoothTransition ((c - x) / ε) * (-1 / ε) := by
  funext x
  have hlin : HasDerivAt (fun y : ℝ ↦ (c - y) / ε) (-1 / ε) x :=
    ((hasDerivAt_id x).const_sub c).div_const ε
  have hs : ContDiff ℝ ∞ Real.smoothTransition := Real.smoothTransition.contDiff
  exact ((hs.differentiable (by simp) ((c - x) / ε)).hasDerivAt.comp x hlin).deriv

private theorem smoothLeftCutoff_secondDeriv (c ε : ℝ) :
    deriv (deriv (smoothLeftCutoff c ε)) =
      fun x ↦ deriv (deriv Real.smoothTransition) ((c - x) / ε) / ε ^ 2 := by
  rw [smoothLeftCutoff_deriv]
  funext x
  have hsD : ContDiff ℝ ∞ (deriv Real.smoothTransition) :=
    (contDiff_infty_iff_deriv.mp Real.smoothTransition.contDiff).2
  have hlin : HasDerivAt (fun y : ℝ ↦ (c - y) / ε) (-1 / ε) x :=
    ((hasDerivAt_id x).const_sub c).div_const ε
  have hcomp := (hsD.differentiable (by simp) ((c - x) / ε)).hasDerivAt.comp x hlin
  convert (hcomp.mul_const (-1 / ε)).deriv using 1 <;>
    (first | rfl | (simp only [div_eq_mul_inv, ← inv_pow]; ring))

/-- Both derivatives vanish off the closed transition interval. -/
theorem smoothLeftCutoff_derivatives_eq_zero {c ε x : ℝ} (hε : 0 < ε)
    (hx : x ∉ Icc (c - ε) c) :
    deriv (smoothLeftCutoff c ε) x = 0 ∧
      deriv (deriv (smoothLeftCutoff c ε)) x = 0 := by
  rcases lt_or_gt_of_ne (show x ≠ c - ε by intro heq; subst x; exact hx ⟨le_rfl, by linarith⟩)
    with hleft | hright
  · have heq : smoothLeftCutoff c ε =ᶠ[𝓝 x] (fun _ ↦ (1 : ℝ)) := by
      filter_upwards [Iio_mem_nhds hleft] with y hy
      exact smoothLeftCutoff_eq_one hε hy.le
    exact ⟨by simpa using heq.deriv_eq, by simpa using heq.deriv.deriv_eq⟩
  · have hxc : c < x := by
      by_contra hnot
      exact hx ⟨hright.le, le_of_not_gt hnot⟩
    have heq : smoothLeftCutoff c ε =ᶠ[𝓝 x] (fun _ ↦ (0 : ℝ)) := by
      filter_upwards [Ioi_mem_nhds hxc] with y hy
      exact smoothLeftCutoff_eq_zero hε hy.le
    exact ⟨by simpa using heq.deriv_eq, by simpa using heq.deriv.deriv_eq⟩

/-- One pair of constants bounds the first two derivatives at every positive
width, with the usual inverse-width scaling. -/
theorem exists_smoothLeftCutoff_derivative_bounds :
    ∃ A B : ℝ, 0 < A ∧ 0 < B ∧
      ∀ c ε : ℝ, 0 < ε → ∀ x ∈ Icc (c - ε) c,
        |deriv (smoothLeftCutoff c ε) x| ≤ A / ε ∧
        |deriv (deriv (smoothLeftCutoff c ε)) x| ≤ B / ε ^ 2 := by
  have hs : ContDiff ℝ ∞ Real.smoothTransition := Real.smoothTransition.contDiff
  have hsD : ContDiff ℝ ∞ (deriv Real.smoothTransition) :=
    (contDiff_infty_iff_deriv.mp hs).2
  obtain ⟨A, hA⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (s := Icc (0 : ℝ) 1) (hs.continuous_deriv (by simp)).continuousOn
  obtain ⟨B, hB⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (s := Icc (0 : ℝ) 1) (hsD.continuous_deriv (by simp)).continuousOn
  refine ⟨|A| + 1, |B| + 1, by positivity, by positivity, ?_⟩
  intro c ε hε x hx
  have hxI : (c - x) / ε ∈ Icc (0 : ℝ) 1 := by
    constructor
    · exact div_nonneg (sub_nonneg.mpr hx.2) hε.le
    · apply (div_le_iff₀ hε).mpr
      linarith [hx.1]
  have hAD : |deriv Real.smoothTransition ((c - x) / ε)| ≤ |A| + 1 := by
    have hh : |deriv Real.smoothTransition ((c - x) / ε)| ≤ A := by
      simpa only [Real.norm_eq_abs] using hA _ hxI
    exact hh.trans (by linarith [le_abs_self A])
  have hBDD : |deriv (deriv Real.smoothTransition) ((c - x) / ε)| ≤ |B| + 1 := by
    have hh : |deriv (deriv Real.smoothTransition) ((c - x) / ε)| ≤ B := by
      simpa only [Real.norm_eq_abs] using hB _ hxI
    exact hh.trans (by linarith [le_abs_self B])
  constructor
  · rw [smoothLeftCutoff_deriv]
    simp only [abs_mul, abs_div, abs_neg, abs_one, abs_of_pos hε]
    simpa only [div_eq_mul_inv, one_mul] using
      mul_le_mul_of_nonneg_right hAD (inv_nonneg.mpr hε.le)
  · rw [smoothLeftCutoff_secondDeriv]
    rw [abs_div, abs_of_nonneg (sq_nonneg ε)]
    exact div_le_div_of_nonneg_right hBDD (sq_nonneg ε)

/-- Shrinking positive widths converge pointwise to the literal left indicator,
including its value zero at the cutting point. -/
theorem smoothLeftCutoff_tendsto {ε : ℕ → ℝ} {c : ℝ}
    (hε : ∀ n, 0 < ε n) (hlim : Tendsto ε atTop (𝓝 0)) (x : ℝ) :
    Tendsto (fun n ↦ smoothLeftCutoff c (ε n) x) atTop
      (𝓝 (if x < c then (1 : ℝ) else 0)) := by
  by_cases hx : x < c
  · simp only [ite_eq_left hx]
    apply tendsto_const_nhds.congr'
    filter_upwards [hlim.eventually (gt_mem_nhds (sub_pos.mpr hx))] with n hn
    exact (smoothLeftCutoff_eq_one (hε n) (by linarith)).symm
  · simp only [ite_eq_right hx]
    apply tendsto_const_nhds.congr'
    exact Filter.Eventually.of_forall fun n ↦
      (smoothLeftCutoff_eq_zero (hε n) (le_of_not_gt hx)).symm

end RicciFlowSharpEstimate.Analysis
