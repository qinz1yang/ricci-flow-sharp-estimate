/-
Copyright (c) 2026 Ziyang Qin. All rights reserved.
No license is granted by this file.
Authors: Ziyang Qin
-/
import RicciFlowSharpEstimate.Geometry.AreaWarpBounds

/-!
# Joint bounds for the actual area warp and its slope

The original curvature box and both exact moments bound the combination
of the squared warp slope and the warp itself. The sign of the monotone
slope selects the pole used in each comparison; no symmetry is assumed.
-/

noncomputable section

namespace RicciFlowSharpEstimate.Geometry.AreaProfile

open MeasureTheory Set

private theorem warpSlope_sq_add_four_mul_warp_hasDerivAt
    (K : ℝ → ℝ) (hK : Continuous K) (c x : ℝ) :
    HasDerivAt (fun y => (warpSlope K y) ^ 2 + 4 * c * warp K y)
      (-4 * warpSlope K x * (K x - c)) x := by
  have hD := ((warpSlope_hasDerivAt K hK x).pow 2).add
    ((warp_hasDerivAt K hK x).const_mul (4 * c))
  change HasDerivAt (fun y => (warpSlope K y) ^ 2 + 4 * c * warp K y) _ x at hD
  convert hD using 1
  ring

/-- The squared slope and warp of the original normalized curvature primitive
lie between the two constant-curvature relations determined by its curvature
box. Both exact moments are retained, and either pole may control the point. -/
theorem warpSlope_sq_add_four_mul_warp_bounds
    (K : ℝ → ℝ) (hK : Continuous K) (kappa Lambda : ℝ) (hkappa : 0 ≤ kappa)
    (hbox : ∀ x ∈ Icc (0 : ℝ) 1, kappa ≤ K x ∧ K x ≤ Lambda)
    (hzero : (∫ x in (0 : ℝ)..1, K x) = 2)
    (hone : (∫ x in (0 : ℝ)..1, x * K x) = 1)
    (x : ℝ) (hx : x ∈ Icc (0 : ℝ) 1) :
    (warpSlope K x) ^ 2 + 4 * kappa * warp K x ≤ 4 ∧
      4 ≤ (warpSlope K x) ^ 2 + 4 * Lambda * warp K x := by
  have hanti : AntitoneOn (warpSlope K) (Icc (0 : ℝ) 1) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc 0 1)
      (warpSlope_continuous K hK).continuousOn
    · intro y _
      exact (warpSlope_hasDerivAt K hK y).differentiableAt.differentiableWithinAt
    · intro y hy
      rw [deriv_warpSlope K hK]
      have hKy : 0 ≤ K y := hkappa.trans (hbox y (interior_subset hy)).1
      linarith
  let E : ℝ → ℝ → ℝ := fun c y => (warpSlope K y) ^ 2 + 4 * c * warp K y
  have hED (c y : ℝ) : HasDerivAt (E c) (-4 * warpSlope K y * (K y - c)) y :=
    warpSlope_sq_add_four_mul_warp_hasDerivAt K hK c y
  have hEC (c : ℝ) : Continuous (E c) :=
    continuous_iff_continuousAt.mpr fun y => (hED c y).continuousAt
  have hE0 (c : ℝ) : E c 0 = 4 := by
    dsimp only [E]
    rw [warpSlope_zero, warp_zero]
    norm_num
  have hE1 (c : ℝ) : E c 1 = 4 := by
    dsimp only [E]
    rw [warpSlope_one K hzero, warp_one K hK hzero hone]
    norm_num
  have hmonoE (c u v : ℝ)
      (hsign : ∀ y ∈ Icc u v, 0 ≤ -4 * warpSlope K y * (K y - c)) :
      MonotoneOn (E c) (Icc u v) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc u v) (hEC c).continuousOn
    · intro y _
      exact (hED c y).differentiableAt.differentiableWithinAt
    · intro y hy
      rw [(hED c y).deriv]
      exact hsign y (interior_subset hy)
  have hantiE (c u v : ℝ)
      (hsign : ∀ y ∈ Icc u v, -4 * warpSlope K y * (K y - c) ≤ 0) :
      AntitoneOn (E c) (Icc u v) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc u v) (hEC c).continuousOn
    · intro y _
      exact (hED c y).differentiableAt.differentiableWithinAt
    · intro y hy
      rw [(hED c y).deriv]
      exact hsign y (interior_subset hy)
  change E kappa x ≤ 4 ∧ 4 ≤ E Lambda x
  rcases le_total 0 (warpSlope K x) with hpos | hneg
  · have hleft (y : ℝ) (hy : y ∈ Icc (0 : ℝ) x) :
        y ∈ Icc (0 : ℝ) 1 ∧ 0 ≤ warpSlope K y := by
      have hy01 : y ∈ Icc (0 : ℝ) 1 := ⟨hy.1, hy.2.trans hx.2⟩
      exact ⟨hy01, hpos.trans (hanti hy01 hx hy.2)⟩
    have hlow : AntitoneOn (E kappa) (Icc (0 : ℝ) x) := by
      apply hantiE
      intro y hy
      have hs := hleft y hy
      nlinarith only [mul_nonneg hs.2 (sub_nonneg.mpr (hbox y hs.1).1)]
    have hupp : MonotoneOn (E Lambda) (Icc (0 : ℝ) x) := by
      apply hmonoE
      intro y hy
      have hs := hleft y hy
      nlinarith only [mul_nonneg hs.2 (sub_nonneg.mpr (hbox y hs.1).2)]
    have hL := hlow ⟨le_rfl, hx.1⟩ ⟨hx.1, le_rfl⟩ hx.1
    have hU := hupp ⟨le_rfl, hx.1⟩ ⟨hx.1, le_rfl⟩ hx.1
    rw [hE0 kappa] at hL
    rw [hE0 Lambda] at hU
    exact ⟨hL, hU⟩
  · have hright (y : ℝ) (hy : y ∈ Icc x (1 : ℝ)) :
        y ∈ Icc (0 : ℝ) 1 ∧ warpSlope K y ≤ 0 := by
      have hy01 : y ∈ Icc (0 : ℝ) 1 := ⟨hx.1.trans hy.1, hy.2⟩
      exact ⟨hy01, (hanti hx hy01 hy.1).trans hneg⟩
    have hlow : MonotoneOn (E kappa) (Icc x (1 : ℝ)) := by
      apply hmonoE
      intro y hy
      have hs := hright y hy
      nlinarith only [mul_nonneg (neg_nonneg.mpr hs.2)
        (sub_nonneg.mpr (hbox y hs.1).1)]
    have hupp : AntitoneOn (E Lambda) (Icc x (1 : ℝ)) := by
      apply hantiE
      intro y hy
      have hs := hright y hy
      nlinarith only [mul_nonneg (neg_nonneg.mpr hs.2)
        (sub_nonneg.mpr (hbox y hs.1).2)]
    have hL := hlow ⟨le_rfl, hx.2⟩ ⟨hx.2, le_rfl⟩ hx.2
    have hU := hupp ⟨le_rfl, hx.2⟩ ⟨hx.2, le_rfl⟩ hx.2
    rw [hE1 kappa] at hL
    rw [hE1 Lambda] at hU
    exact ⟨hL, hU⟩

end RicciFlowSharpEstimate.Geometry.AreaProfile
