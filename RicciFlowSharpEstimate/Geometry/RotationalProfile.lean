/-
Copyright (c) 2026 Ziyang Qin. All rights reserved.
No license is granted by this file.
Authors: Ziyang Qin
-/
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Balanced rotational profiles

The actual balance, moment coordinate and warping integral attached to a profile.
These analytic identities precede construction of the sphere metric.

Adapted from Ziyang Qin's historical `BalancedRotationalProfile.lean`.
-/

noncomputable section

namespace RicciFlowSharpEstimate.Geometry.RotationalProfile

open MeasureTheory
open intervalIntegral
open Set
open scoped ContDiff

/-- The linear two-pole balance functional. -/
def balance (a : ℝ → ℝ) : ℝ :=
  ∫ v : ℝ in (-1)..1, v * a v

/-- The moment coordinate reconstructed from reciprocal curvature. -/
def momentCoordinate (a : ℝ → ℝ) (v : ℝ) : ℝ :=
  ∫ ξ : ℝ in 0..v, a ξ

/-- The rotational warping coefficient reconstructed from reciprocal
curvature. -/
def warp (a : ℝ → ℝ) (v : ℝ) : ℝ :=
  2 * ∫ ξ : ℝ in v..1, ξ * a ξ

/-- The reconstructed moment coordinate has derivative `a`. -/
theorem momentCoordinate_hasDerivAt
    (a : ℝ → ℝ) (ha : Continuous a) (v : ℝ) :
    HasDerivAt (momentCoordinate a) (a v) v := by
  exact (ha.integral_hasStrictDerivAt 0 v).hasDerivAt

/-- The reconstructed warping coefficient has parametric derivative
`f_v = -2 v a(v)`. -/
theorem warp_hasDerivAt
    (a : ℝ → ℝ) (ha : Continuous a) (v : ℝ) :
    HasDerivAt (warp a) (-2 * v * a v) v := by
  have hg : Continuous (fun ξ : ℝ => ξ * a ξ) :=
    continuous_id.mul ha
  have hbase :
      HasDerivAt
        (fun y : ℝ => ∫ ξ : ℝ in 1..y, ξ * a ξ)
        (v * a v) v :=
    (hg.integral_hasStrictDerivAt 1 v).hasDerivAt
  have hfun :
      warp a =
        fun y : ℝ => -2 * ∫ ξ : ℝ in 1..y, ξ * a ξ := by
    funext y
    rw [warp, integral_symm]
    ring
  rw [hfun]
  convert hbase.const_mul (-2) using 1
  ring

/-- Derivative form of the reconstructed moment-coordinate identity. -/
theorem deriv_momentCoordinate_eq
    (a : ℝ → ℝ) (ha : Continuous a) (v : ℝ) :
    deriv (momentCoordinate a) v = a v :=
  (momentCoordinate_hasDerivAt a ha v).deriv

/-- Derivative form of the reconstructed warping identity. -/
theorem deriv_warp_eq
    (a : ℝ → ℝ) (ha : Continuous a) (v : ℝ) :
    deriv (warp a) v = -2 * v * a v :=
  (warp_hasDerivAt a ha v).deriv

/-- Positivity of the reciprocal-curvature profile makes the reconstructed
moment coordinate strictly increasing between the poles. -/
theorem momentCoordinate_strictMonoOn
    (a : ℝ → ℝ) (ha : Continuous a)
    (haPos : ∀ v ∈ Icc (-1 : ℝ) 1, 0 < a v) :
    StrictMonoOn (momentCoordinate a) (Icc (-1 : ℝ) 1) := by
  intro x hx y hy hxy
  have hInt :
      IntervalIntegrable a volume x y :=
    ha.intervalIntegrable x y
  have hPos :
      0 < ∫ ξ : ℝ in x..y, a ξ := by
    apply intervalIntegral_pos_of_pos_on hInt
    · intro ξ hξ
      apply haPos ξ
      exact
        ⟨hx.1.trans hξ.1.le,
          hξ.2.le.trans hy.2⟩
    · exact hxy
  have hLeft :
      IntervalIntegrable a volume 0 x :=
    ha.intervalIntegrable 0 x
  have hAdd :=
    integral_add_adjacent_intervals hLeft hInt
  change
    (∫ ξ : ℝ in 0..x, a ξ) <
      ∫ ξ : ℝ in 0..y, a ξ
  linarith

/-- In particular, the moment coordinate is injective on the closed
two-pole interval. -/
theorem momentCoordinate_injOn
    (a : ℝ → ℝ) (ha : Continuous a)
    (haPos : ∀ v ∈ Icc (-1 : ℝ) 1, 0 < a v) :
    Set.InjOn (momentCoordinate a) (Icc (-1 : ℝ) 1) :=
  (momentCoordinate_strictMonoOn a ha haPos).injOn

/-- Dividing the parametric derivatives gives the first metric-coordinate
identity `f_x = -2v`. -/
theorem warp_deriv_div_momentCoordinate_deriv
    (a : ℝ → ℝ) (ha : Continuous a) (v : ℝ)
    (haNe : a v ≠ 0) :
    deriv (warp a) v / deriv (momentCoordinate a) v = -2 * v := by
  rw [deriv_warp_eq a ha v, deriv_momentCoordinate_eq a ha v]
  field_simp

/-- North-pole ratio of the warping and moment-coordinate derivatives. -/
theorem warp_northPole_slope
    (a : ℝ → ℝ) (ha : Continuous a)
    (haPos : ∀ v ∈ Icc (-1 : ℝ) 1, 0 < a v) :
    deriv (warp a) 1 / deriv (momentCoordinate a) 1 = -2 := by
  simpa using
    (warp_deriv_div_momentCoordinate_deriv
      a ha 1 (haPos 1 ⟨by norm_num, by norm_num⟩).ne')

/-- South-pole ratio of the warping and moment-coordinate derivatives. -/
theorem warp_southPole_slope
    (a : ℝ → ℝ) (ha : Continuous a)
    (haPos : ∀ v ∈ Icc (-1 : ℝ) 1, 0 < a v) :
    deriv (warp a) (-1) / deriv (momentCoordinate a) (-1) = 2 := by
  have h :=
    warp_deriv_div_momentCoordinate_deriv
      a ha (-1) (haPos (-1) ⟨by norm_num, by norm_num⟩).ne'
  norm_num at h ⊢
  exact h

/-- The north-pole warping value is zero. -/
@[simp]
theorem warp_one (a : ℝ → ℝ) :
    warp a 1 = 0 := by
  simp [warp]

/-- Balance is exactly the south-pole endpoint condition. -/
theorem warp_neg_one_eq_zero_of_balance
    (a : ℝ → ℝ) (hBalance : balance a = 0) :
    warp a (-1) = 0 := by
  rw [warp]
  change 2 * balance a = 0
  rw [hBalance]
  ring

/-- Under balance, the northern integral can be rewritten as the negative
southern integral. -/
theorem integral_from_eq_neg_integral_to_of_balance
    (a : ℝ → ℝ) (ha : Continuous a)
    (hBalance : balance a = 0) (v : ℝ) :
    (∫ ξ : ℝ in v..1, ξ * a ξ) =
      -(∫ ξ : ℝ in (-1)..v, ξ * a ξ) := by
  have hg : Continuous (fun ξ : ℝ => ξ * a ξ) :=
    continuous_id.mul ha
  have hleft :=
    hg.intervalIntegrable (-1) v
      (μ := (volume : Measure ℝ))
  have hright :=
    hg.intervalIntegrable v 1
      (μ := (volume : Measure ℝ))
  have hadd :=
    integral_add_adjacent_intervals hleft hright
  change (∫ ξ : ℝ in (-1)..1, ξ * a ξ) = 0 at hBalance
  linarith

/-- A positive balanced reciprocal-curvature profile reconstructs a
strictly positive warping coefficient between the two poles. -/
theorem warp_pos_of_balance
    (a : ℝ → ℝ) (ha : Continuous a)
    (haPos : ∀ v ∈ Icc (-1 : ℝ) 1, 0 < a v)
    (hBalance : balance a = 0)
    (v : ℝ) (hv : v ∈ Ioo (-1 : ℝ) 1) :
    0 < warp a v := by
  have hg : Continuous (fun ξ : ℝ => ξ * a ξ) :=
    continuous_id.mul ha
  by_cases hvNonneg : 0 ≤ v
  · have hInt :
        IntervalIntegrable (fun ξ : ℝ => ξ * a ξ)
          volume v 1 :=
      hg.intervalIntegrable v 1
    have hPos :
        0 < ∫ ξ : ℝ in v..1, ξ * a ξ := by
      apply intervalIntegral_pos_of_pos_on hInt
      · intro ξ hξ
        have hξPos : 0 < ξ := lt_of_le_of_lt hvNonneg hξ.1
        have hξMem : ξ ∈ Icc (-1 : ℝ) 1 :=
          ⟨hv.1.le.trans hξ.1.le, hξ.2.le⟩
        exact mul_pos hξPos (haPos ξ hξMem)
      · exact hv.2
    rw [warp]
    linarith
  · have hvNeg : v < 0 := lt_of_not_ge hvNonneg
    have hnegCont : Continuous (fun ξ : ℝ => -(ξ * a ξ)) :=
      hg.neg
    have hInt :
        IntervalIntegrable (fun ξ : ℝ => -(ξ * a ξ))
          volume (-1) v :=
      hnegCont.intervalIntegrable (-1) v
    have hPos :
        0 < ∫ ξ : ℝ in (-1)..v, -(ξ * a ξ) := by
      apply intervalIntegral_pos_of_pos_on hInt
      · intro ξ hξ
        have hξNeg : ξ < 0 := hξ.2.trans hvNeg
        have hξMem : ξ ∈ Icc (-1 : ℝ) 1 :=
          ⟨hξ.1.le, hξ.2.le.trans hv.2.le⟩
        have haξ := haPos ξ hξMem
        nlinarith
      · exact hv.1
    have hrewrite :=
      integral_from_eq_neg_integral_to_of_balance
        a ha hBalance v
    have hneg :
        (∫ ξ : ℝ in (-1)..v, -(ξ * a ξ)) =
          -(∫ ξ : ℝ in (-1)..v, ξ * a ξ) := by
      rw [intervalIntegral.integral_neg]
    rw [hneg] at hPos
    rw [warp, hrewrite]
    linarith

/-- The moment coordinate of a globally smooth profile is globally smooth. -/
theorem momentCoordinate_contDiff (a : ℝ → ℝ) (ha : ContDiff ℝ ∞ a) :
    ContDiff ℝ ∞ (momentCoordinate a) := by
  rw [contDiff_infty_iff_deriv]
  refine ⟨fun v => (momentCoordinate_hasDerivAt a ha.continuous v).differentiableAt, ?_⟩
  convert ha using 1
  funext v
  exact deriv_momentCoordinate_eq a ha.continuous v

/-- The warping integral of a globally smooth profile is globally smooth. -/
theorem warp_contDiff (a : ℝ → ℝ) (ha : ContDiff ℝ ∞ a) :
    ContDiff ℝ ∞ (warp a) := by
  rw [contDiff_infty_iff_deriv]
  refine ⟨fun v => (warp_hasDerivAt a ha.continuous v).differentiableAt, ?_⟩
  have h : deriv (warp a) = fun v => -2 * v * a v := by
    funext v
    exact deriv_warp_eq a ha.continuous v
  rw [h]
  exact (contDiff_const.mul contDiff_id).mul ha

/-- Constant reciprocal curvature has the standard quadratic warping profile. -/
theorem warp_const (c v : ℝ) : warp (fun _ => c) v = c * (1 - v ^ 2) := by
  have hInt : (∫ x in v..1, x * c) = c * 1 ^ 2 / 2 - c * v ^ 2 / 2 := by
    apply integral_eq_sub_of_hasDerivAt (f := fun x : ℝ => c * x ^ 2 / 2)
    · intro x hx
      convert (((hasDerivAt_id x).pow 2).const_mul c).div_const 2 using 1
      · rfl
      · simp only [id_eq]
        ring
    · exact (continuous_id.mul continuous_const).intervalIntegrable _ _
  rw [warp, hInt]
  ring

/-- Every constant profile is balanced. -/
theorem balance_const (c : ℝ) : balance (fun _ => c) = 0 := by
  have h := warp_const c (-1)
  change 2 * balance (fun _ => c) = _ at h
  linarith

/-- The moment coordinate of a constant profile is linear. -/
theorem momentCoordinate_const (c v : ℝ) : momentCoordinate (fun _ => c) v = v * c := by
  simp [momentCoordinate]

end RicciFlowSharpEstimate.Geometry.RotationalProfile
