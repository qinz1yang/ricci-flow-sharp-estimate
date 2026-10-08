/-
Copyright (c) 2026 Ziyang Qin. All rights reserved.
No license is granted by this file.
Authors: Ziyang Qin
-/
import RicciFlowSharpEstimate.Analysis.SmoothFactor
import RicciFlowSharpEstimate.Geometry.RotationalProfile

/-!
# Removable pole factors of a balanced profile

Global smoothness and balance produce the factors needed to extend the rotational
metric across both poles. The input profile is retained by an explicit equation.

Adapted from Ziyang Qin's historical `SmoothBalancedRotationalSphereMetric.lean`.
-/

noncomputable section

namespace RicciFlowSharpEstimate.Geometry.RotationalProfile

open Set
open scoped ContDiff

private theorem deriv_one_sub_sq_mul (b : ℝ → ℝ) (hb : ContDiff ℝ ∞ b) (z : ℝ) :
    deriv (fun y : ℝ => (1 - y ^ 2) * b y) z =
      (-2 * z) * b z + (1 - z ^ 2) * deriv b z := by
  have hbase : HasDerivAt (fun y : ℝ => 1 - y ^ 2) (-2 * z) z := by
    convert (hasDerivAt_const z (1 : ℝ)).sub ((hasDerivAt_id z).pow 2) using 1
    · rfl
    · simp only [id_eq]
      ring
  exact (hbase.mul ((hb.differentiable (by simp)).differentiableAt.hasDerivAt)).deriv

/-- The tangential pole factor exists, is positive on the closed height interval,
and agrees with the original profile at both poles. -/
theorem exists_smooth_positive_warp_factor (a : ℝ → ℝ) (ha : ContDiff ℝ ∞ a)
    (haPos : ∀ z ∈ Icc (-1 : ℝ) 1, 0 < a z) (hBalance : balance a = 0) :
    ∃ b : ℝ → ℝ, ContDiff ℝ ∞ b ∧
      (∀ z : ℝ, warp a z = (1 - z ^ 2) * b z) ∧
      b (-1) = a (-1) ∧ b 1 = a 1 ∧ ∀ z ∈ Icc (-1 : ℝ) 1, 0 < b z := by
  obtain ⟨b, hb, hfactor⟩ := Analysis.exists_contDiff_one_sub_sq_factor_of_roots
    (warp a) (warp_contDiff a ha) (warp_neg_one_eq_zero_of_balance a hBalance) (warp_one a)
  have hfactorFun : warp a = fun z : ℝ => (1 - z ^ 2) * b z := funext hfactor
  have hderivFun := congrArg deriv hfactorFun
  have hbSouth : b (-1) = a (-1) := by
    have h := congrFun hderivFun (-1)
    rw [deriv_warp_eq a ha.continuous, deriv_one_sub_sq_mul b hb] at h
    norm_num at h
    linarith
  have hbNorth : b 1 = a 1 := by
    have h := congrFun hderivFun 1
    rw [deriv_warp_eq a ha.continuous, deriv_one_sub_sq_mul b hb] at h
    norm_num at h
    linarith
  refine ⟨b, hb, hfactor, hbSouth, hbNorth, ?_⟩
  intro z hz
  rcases eq_or_lt_of_le hz.1 with rfl | hSouth
  · rw [hbSouth]
    exact haPos (-1) ⟨le_rfl, by norm_num⟩
  rcases eq_or_lt_of_le hz.2 with rfl | hNorth
  · rw [hbNorth]
    exact haPos 1 ⟨by norm_num, le_rfl⟩
  · have hDenom : 0 < 1 - z ^ 2 := by nlinarith
    have hWarp := warp_pos_of_balance a ha.continuous haPos hBalance z ⟨hSouth, hNorth⟩
    rw [hfactor z] at hWarp
    exact (mul_pos_iff_of_pos_left hDenom).mp hWarp

/-- Smooth balanced profile and its two globally removable pole factors.
Every admissible smooth profile produces this data in `exists_poleData`. -/
structure PoleData where
  a : ℝ → ℝ
  b : ℝ → ℝ
  c : ℝ → ℝ
  a_contDiff : ContDiff ℝ ∞ a
  b_contDiff : ContDiff ℝ ∞ b
  c_contDiff : ContDiff ℝ ∞ c
  a_pos : ∀ z ∈ Icc (-1 : ℝ) 1, 0 < a z
  b_pos : ∀ z ∈ Icc (-1 : ℝ) 1, 0 < b z
  balance_eq : balance a = 0
  warp_factor : ∀ z : ℝ, warp a z = (1 - z ^ 2) * b z
  radial_factor : ∀ z : ℝ, a z ^ 2 - b z ^ 2 = (1 - z ^ 2) * c z

/-- Both smooth factors are produced from the actual profile, rather than
assumed as additional input. The original profile and pole values are retained. -/
theorem exists_poleData (a : ℝ → ℝ) (ha : ContDiff ℝ ∞ a)
    (haPos : ∀ z ∈ Icc (-1 : ℝ) 1, 0 < a z) (hBalance : balance a = 0) :
    ∃ D : PoleData, D.a = a ∧ D.b (-1) = a (-1) ∧ D.b 1 = a 1 := by
  obtain ⟨b, hb, hWarp, hbSouth, hbNorth, hbPos⟩ :=
    exists_smooth_positive_warp_factor a ha haPos hBalance
  have hSouth : a (-1) ^ 2 - b (-1) ^ 2 = 0 := by rw [hbSouth, sub_self]
  have hNorth : a 1 ^ 2 - b 1 ^ 2 = 0 := by rw [hbNorth, sub_self]
  obtain ⟨c, hc, hRadial⟩ := Analysis.exists_contDiff_one_sub_sq_factor_of_roots
    (fun z => a z ^ 2 - b z ^ 2) ((ha.pow 2).sub (hb.pow 2)) hSouth hNorth
  exact ⟨{
    a := a, b := b, c := c
    a_contDiff := ha, b_contDiff := hb, c_contDiff := hc
    a_pos := haPos, b_pos := hbPos, balance_eq := hBalance
    warp_factor := hWarp, radial_factor := hRadial }, rfl, hbSouth, hbNorth⟩

/-- Constant positive profiles supply a nonvacuous family of pole data. -/
def PoleData.constant (r : ℝ) (hr : 0 < r) : PoleData where
  a := fun _ => r
  b := fun _ => r
  c := fun _ => 0
  a_contDiff := contDiff_const
  b_contDiff := contDiff_const
  c_contDiff := contDiff_const
  a_pos := fun _ _ => hr
  b_pos := fun _ _ => hr
  balance_eq := balance_const r
  warp_factor := fun z => by rw [warp_const]; ring
  radial_factor := fun _ => by ring

end RicciFlowSharpEstimate.Geometry.RotationalProfile
