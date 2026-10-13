/-
Copyright (c) 2026 Ziyang Qin. All rights reserved.
No license is granted by this file.
Authors: Ziyang Qin
-/
import RicciFlowSharpEstimate.Geometry.AreaProfileCalculus
import Mathlib.Analysis.Calculus.MeanValue

/-!
# Bounds for the actual normalized area warp

Curvature bounds give quadratic bounds for the original triangular primitive.
Its actual derivative and the two moment identities also give slope and pole
bounds without differentiating the curvature. The final normalization lemma
retains the original positive curvature box and its ratio hypothesis.
-/

noncomputable section

namespace RicciFlowSharpEstimate.Geometry.AreaProfile

open MeasureTheory Set

private theorem warp_sub_quadratic_hasDerivAt (K : ℝ → ℝ) (hK : Continuous K)
    (c x : ℝ) :
    HasDerivAt (fun y => warp K y - c * y * (1 - y))
      (warpSlope K x - c * (1 - 2 * x)) x := by
  have hquad : HasDerivAt (fun y : ℝ => c * y * (1 - y))
      (c * (1 - 2 * x)) x := by
    convert ((hasDerivAt_id x).const_mul c).mul
      ((hasDerivAt_const x 1).sub (hasDerivAt_id x)) using 1
    · rfl
    · simp only [Pi.sub_apply, id_eq]
      ring
  exact (warp_hasDerivAt K hK x).sub hquad

private theorem deriv_warp_sub_quadratic (K : ℝ → ℝ) (hK : Continuous K) (c : ℝ) :
    deriv (fun y => warp K y - c * y * (1 - y)) =
      fun y => warpSlope K y - c * (1 - 2 * y) := by
  funext x
  exact (warp_sub_quadratic_hasDerivAt K hK c x).deriv

private theorem warpSlope_sub_linear_hasDerivAt (K : ℝ → ℝ) (hK : Continuous K)
    (c x : ℝ) :
    HasDerivAt (fun y => warpSlope K y - c * (1 - 2 * y))
      (-2 * K x + 2 * c) x := by
  convert (warpSlope_hasDerivAt K hK x).sub
    (((hasDerivAt_const x 1).sub ((hasDerivAt_id x).const_mul 2)).const_mul c)
    using 1
  · rfl
  · ring

/-- A lower curvature bound gives the corresponding quadratic lower warp bound. -/
theorem quadratic_le_warp_of_curvature_lower (K : ℝ → ℝ) (hK : Continuous K)
    (lo : ℝ) (hlower : ∀ x ∈ Icc (0 : ℝ) 1, lo ≤ K x)
    (hzero : (∫ x in (0 : ℝ)..1, K x) = 2)
    (hone : (∫ x in (0 : ℝ)..1, x * K x) = 1)
    (x : ℝ) (hx : x ∈ Icc (0 : ℝ) 1) :
    lo * x * (1 - x) ≤ warp K x := by
  have hconc : ConcaveOn ℝ (Icc (0 : ℝ) 1)
      (fun y => warp K y - lo * y * (1 - y)) := by
    apply concaveOn_of_deriv2_nonpos' (convex_Icc 0 1)
    · intro y _
      exact (warp_sub_quadratic_hasDerivAt K hK lo y).differentiableAt.differentiableWithinAt
    · rw [deriv_warp_sub_quadratic K hK lo]
      intro y _
      exact (warpSlope_sub_linear_hasDerivAt K hK lo y).differentiableAt.differentiableWithinAt
    · intro y hy
      change deriv (deriv (fun t => warp K t - lo * t * (1 - t))) y ≤ 0
      rw [deriv_warp_sub_quadratic K hK lo,
        (warpSlope_sub_linear_hasDerivAt K hK lo y).deriv]
      linarith [hlower y hy]
  have hchord := hconc.2 (by norm_num : (0 : ℝ) ∈ Icc (0 : ℝ) 1)
    (by norm_num : (1 : ℝ) ∈ Icc (0 : ℝ) 1)
    (sub_nonneg.mpr hx.2) hx.1 (by ring : 1 - x + x = 1)
  have hnonneg : 0 ≤ warp K x - lo * x * (1 - x) := by
    simpa only [smul_eq_mul, warp_zero, warp_one K hK hzero hone,
      sub_self, sub_zero, zero_mul, mul_zero, mul_one, zero_add, add_zero] using hchord
  linarith

/-- An upper curvature bound gives the corresponding quadratic upper warp bound. -/
theorem warp_le_quadratic_of_curvature_upper (K : ℝ → ℝ) (hK : Continuous K)
    (hi : ℝ) (hupper : ∀ x ∈ Icc (0 : ℝ) 1, K x ≤ hi)
    (hzero : (∫ x in (0 : ℝ)..1, K x) = 2)
    (hone : (∫ x in (0 : ℝ)..1, x * K x) = 1)
    (x : ℝ) (hx : x ∈ Icc (0 : ℝ) 1) :
    warp K x ≤ hi * x * (1 - x) := by
  have hconv : ConvexOn ℝ (Icc (0 : ℝ) 1)
      (fun y => warp K y - hi * y * (1 - y)) := by
    apply convexOn_of_deriv2_nonneg' (convex_Icc 0 1)
    · intro y _
      exact (warp_sub_quadratic_hasDerivAt K hK hi y).differentiableAt.differentiableWithinAt
    · rw [deriv_warp_sub_quadratic K hK hi]
      intro y _
      exact (warpSlope_sub_linear_hasDerivAt K hK hi y).differentiableAt.differentiableWithinAt
    · intro y hy
      change 0 ≤ deriv (deriv (fun t => warp K t - hi * t * (1 - t))) y
      rw [deriv_warp_sub_quadratic K hK hi,
        (warpSlope_sub_linear_hasDerivAt K hK hi y).deriv]
      linarith [hupper y hy]
  have hchord := hconv.2 (by norm_num : (0 : ℝ) ∈ Icc (0 : ℝ) 1)
    (by norm_num : (1 : ℝ) ∈ Icc (0 : ℝ) 1)
    (sub_nonneg.mpr hx.2) hx.1 (by ring : 1 - x + x = 1)
  have hnonpos : warp K x - hi * x * (1 - x) ≤ 0 := by
    simpa only [smul_eq_mul, warp_zero, warp_one K hK hzero hone,
      sub_self, sub_zero, zero_mul, mul_zero, mul_one, zero_add, add_zero] using hchord
  linarith

/-- A curvature box controls the original warp by the matching two quadratics. -/
theorem warp_bounds_of_curvature_bounds (K : ℝ → ℝ) (hK : Continuous K)
    (lo hi : ℝ) (hbox : ∀ x ∈ Icc (0 : ℝ) 1, lo ≤ K x ∧ K x ≤ hi)
    (hzero : (∫ x in (0 : ℝ)..1, K x) = 2)
    (hone : (∫ x in (0 : ℝ)..1, x * K x) = 1)
    (x : ℝ) (hx : x ∈ Icc (0 : ℝ) 1) :
    lo * x * (1 - x) ≤ warp K x ∧ warp K x ≤ hi * x * (1 - x) := by
  exact ⟨quadratic_le_warp_of_curvature_lower K hK lo (fun y hy => (hbox y hy).1)
    hzero hone x hx,
    warp_le_quadratic_of_curvature_upper K hK hi (fun y hy => (hbox y hy).2)
      hzero hone x hx⟩

/-- Nonnegative curvature and its zeroth moment bound the actual warp slope. -/
theorem abs_warpSlope_le_two (K : ℝ → ℝ) (hK : Continuous K)
    (hnonneg : ∀ x ∈ Icc (0 : ℝ) 1, 0 ≤ K x)
    (hzero : (∫ x in (0 : ℝ)..1, K x) = 2)
    (x : ℝ) (hx : x ∈ Icc (0 : ℝ) 1) : |warpSlope K x| ≤ 2 := by
  have hanti : AntitoneOn (warpSlope K) (Icc (0 : ℝ) 1) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc 0 1)
      (warpSlope_continuous K hK).continuousOn
    · intro y _
      exact (warpSlope_hasDerivAt K hK y).differentiableAt.differentiableWithinAt
    · intro y hy
      rw [deriv_warpSlope K hK]
      linarith [hnonneg y (interior_subset hy)]
  have hupper := hanti (by norm_num : (0 : ℝ) ∈ Icc (0 : ℝ) 1) hx hx.1
  have hlower := hanti hx (by norm_num : (1 : ℝ) ∈ Icc (0 : ℝ) 1) hx.2
  rw [warpSlope_zero] at hupper
  rw [warpSlope_one K hzero] at hlower
  exact abs_le.mpr ⟨hlower, hupper⟩

/-- The native moments and nonnegative curvature give uniform bounds at both poles. -/
theorem warp_nonneg_le_two_mul_min (K : ℝ → ℝ) (hK : Continuous K)
    (hnonneg : ∀ x ∈ Icc (0 : ℝ) 1, 0 ≤ K x)
    (hzero : (∫ x in (0 : ℝ)..1, K x) = 2)
    (hone : (∫ x in (0 : ℝ)..1, x * K x) = 1)
    (x : ℝ) (hx : x ∈ Icc (0 : ℝ) 1) :
    0 ≤ warp K x ∧ warp K x ≤ 2 * min x (1 - x) := by
  have hdist (y : ℝ) (hy : y ∈ Icc (0 : ℝ) 1) :
      |warp K x - warp K y| ≤ 2 * |x - y| := by
    simpa only [Real.norm_eq_abs] using
      Convex.norm_image_sub_le_of_norm_deriv_le
        (fun t _ => (warp_hasDerivAt K hK t).differentiableAt)
        (fun t ht => by
          rw [deriv_warp K hK]
          simpa only [Real.norm_eq_abs] using abs_warpSlope_le_two K hK hnonneg hzero t ht)
        (convex_Icc 0 1) hy hx
  have hleft : |warp K x| ≤ 2 * x := by
    simpa only [warp_zero, sub_zero, abs_of_nonneg hx.1] using
      hdist 0 (by norm_num)
  have hright : |warp K x| ≤ 2 * (1 - x) := by
    simpa only [warp_one K hK hzero hone, sub_zero,
      abs_of_nonpos (sub_nonpos.mpr hx.2), neg_sub] using hdist 1 (by norm_num)
  constructor
  · simpa only [zero_mul] using
      quadratic_le_warp_of_curvature_lower K hK 0 hnonneg hzero hone x hx
  · by_cases hside : x ≤ 1 - x
    · rw [min_eq_left hside]
      exact (le_abs_self _).trans hleft
    · rw [min_eq_right (le_of_lt (lt_of_not_ge hside))]
      exact (le_abs_self _).trans hright

/-- The normalized zeroth moment turns the original positive box ratio into a common box. -/
theorem curvature_bounds_of_ratio (K : ℝ → ℝ) (hK : Continuous K)
    (kappa Lambda C : ℝ) (hkappa : 0 < kappa)
    (hbox : ∀ x ∈ Icc (0 : ℝ) 1, kappa ≤ K x ∧ K x ≤ Lambda)
    (hratio : Lambda / kappa ≤ C)
    (hzero : (∫ x in (0 : ℝ)..1, K x) = 2)
    (x : ℝ) (hx : x ∈ Icc (0 : ℝ) 1) :
    2 / C ≤ K x ∧ K x ≤ 2 * C := by
  have hkappa_le : kappa ≤ 2 := by
    have hi := intervalIntegral.integral_mono_on (by norm_num : (0 : ℝ) ≤ 1)
      (show IntervalIntegrable (fun _ : ℝ => kappa) volume 0 1 from
        continuous_const.intervalIntegrable 0 1)
      (hK.intervalIntegrable 0 1) (fun y hy => (hbox y hy).1)
    simpa only [intervalIntegral.integral_const, sub_zero, one_smul, hzero] using hi
  have hLambda_ge : 2 ≤ Lambda := by
    have hi := intervalIntegral.integral_mono_on (by norm_num : (0 : ℝ) ≤ 1)
      (hK.intervalIntegrable 0 1)
      (show IntervalIntegrable (fun _ : ℝ => Lambda) volume 0 1 from
        continuous_const.intervalIntegrable 0 1) (fun y hy => (hbox y hy).2)
    simpa only [intervalIntegral.integral_const, sub_zero, one_smul, hzero] using hi
  have hLambda_pos : 0 < Lambda := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 2) hLambda_ge
  have hCpos : 0 < C := (div_pos hLambda_pos hkappa).trans_le hratio
  have hratio_mul : Lambda ≤ C * kappa := (div_le_iff₀ hkappa).mp hratio
  have hlower : 2 / C ≤ kappa := by
    apply (div_le_iff₀ hCpos).mpr
    nlinarith [hLambda_ge, hratio_mul]
  have hupper : Lambda ≤ 2 * C := by
    have hmul := mul_le_mul_of_nonneg_left hkappa_le hCpos.le
    nlinarith [hratio_mul, hmul]
  exact ⟨hlower.trans (hbox x hx).1, (hbox x hx).2.trans hupper⟩

end RicciFlowSharpEstimate.Geometry.AreaProfile
