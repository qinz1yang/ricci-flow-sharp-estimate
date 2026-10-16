/-
Copyright (c) 2026 Ziyang Qin. All rights reserved.
No license is granted by this file.
Authors: Ziyang Qin
-/
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# First-order vanishing of a nonnegative affine pencil at an interior zero

This private calculus probe uses two genuine parameter slices through an
interior zero. No field, curvature or profile application is asserted.
-/

noncomputable section

namespace RicciFlowSharpEstimate.Analysis

open Filter Set Topology

private theorem affine_pencil_zero_first_order
    {P Q : ℝ → ℝ} {a b c d x s : ℝ}
    (hx : x ∈ Ioo a b) (hs : s ∈ Ioo c d)
    (hP : DifferentiableAt ℝ P x) (hQ : DifferentiableAt ℝ Q x)
    (hnonneg : ∀ k ∈ Ioo a b, ∀ t ∈ Ioo c d, 0 ≤ P k + t * Q k)
    (hzero : P x + s * Q x = 0) :
    P x = 0 ∧ Q x = 0 ∧ deriv P x = 0 ∧ deriv Q x = 0 := by
  let ε := min (s - c) (d - s) / 2
  have hε : 0 < ε :=
    div_pos (lt_min (sub_pos.mpr hs.1) (sub_pos.mpr hs.2)) (by norm_num)
  have hεleft : ε < s - c := by
    dsimp only [ε]
    linarith [min_le_left (s - c) (d - s),
      lt_min (sub_pos.mpr hs.1) (sub_pos.mpr hs.2)]
  have hεright : ε < d - s := by
    dsimp only [ε]
    linarith [min_le_right (s - c) (d - s),
      lt_min (sub_pos.mpr hs.1) (sub_pos.mpr hs.2)]
  have hminus : s - ε ∈ Ioo c d := by
    constructor <;> linarith [hs.1, hs.2]
  have hplus : s + ε ∈ Ioo c d := by
    constructor <;> linarith [hs.1, hs.2]
  have hvalueMinus := hnonneg x hx (s - ε) hminus
  have hvaluePlus := hnonneg x hx (s + ε) hplus
  have hproduct : ε * Q x = 0 := by
    nlinarith only [hzero, hvalueMinus, hvaluePlus]
  have hQ0 : Q x = 0 := (mul_eq_zero.mp hproduct).resolve_left hε.ne'
  have hP0 : P x = 0 := by
    simpa only [hQ0, mul_zero, add_zero] using hzero
  have hslice (t : ℝ) (ht : t ∈ Ioo c d) : deriv P x + t * deriv Q x = 0 := by
    have hmin : IsLocalMin (fun k => P k + t * Q k) x := by
      change ∀ᶠ k in 𝓝 x, P x + t * Q x ≤ P k + t * Q k
      filter_upwards [isOpen_Ioo.mem_nhds hx] with k hk
      simpa only [hP0, hQ0, mul_zero, add_zero] using hnonneg k hk t ht
    have hD := hP.hasDerivAt.add (hQ.hasDerivAt.const_mul t)
    change HasDerivAt (fun k => P k + t * Q k)
      (deriv P x + t * deriv Q x) x at hD
    exact hmin.hasDerivAt_eq_zero hD
  have hderivMinus := hslice (s - ε) hminus
  have hderivPlus := hslice (s + ε) hplus
  have hderivProduct : ε * deriv Q x = 0 := by
    nlinarith only [hderivMinus, hderivPlus]
  have hQderiv : deriv Q x = 0 :=
    (mul_eq_zero.mp hderivProduct).resolve_left hε.ne'
  have hPderiv : deriv P x = 0 := by
    simpa only [hQderiv, mul_zero, add_zero] using hderivMinus
  exact ⟨hP0, hQ0, hPderiv, hQderiv⟩



private def calibrationDet (f a af beta bf t k : ℝ) : ℝ :=
  8 * a * f * (k ^ 2 + (2 * a - beta) * k - a ^ 2) +
    t * (4 * a * (beta - k + f * bf) - (beta - k + 2 * f * af) ^ 2)

-- A strict algebraic obstruction on an OPEN RECTANGLE, not a physical
-- reachability theorem or a rejection of general x,f,b-dependent fields.
private theorem calibration_det_pos_on_rectangle
    (f a af beta bf kl ku tl tu k t : ℝ) (hf : 0 < f) (ha : 0 < a)
    (hkI : k ∈ Ioo kl ku) (htI : t ∈ Ioo tl tu)
    (hN : ∀ j ∈ Ioo kl ku, ∀ s ∈ Ioo tl tu,
      0 ≤ calibrationDet f a af beta bf s j) :
    0 < calibrationDet f a af beta bf t k := by
  by_contra hn
  have hz : calibrationDet f a af beta bf t k = 0 :=
    le_antisymm (le_of_not_gt hn) (hN k hkI t htI)
  let P := fun j : ℝ => 8 * a * f * (j ^ 2 + (2 * a - beta) * j - a ^ 2)
  let Q := fun j : ℝ => 4 * a * (beta - j + f * bf) - (beta - j + 2 * f * af) ^ 2
  have hDP : HasDerivAt P (8 * a * f * (2 * k + 2 * a - beta)) k := by
    have h := ((((hasDerivAt_id k).pow 2).add
      ((hasDerivAt_id k).const_mul (2 * a - beta))).sub_const (a ^ 2)).const_mul
        (8 * a * f)
    convert h using 1
    · rfl
    · simp only [id_eq]
      ring
  have hDQ : DifferentiableAt ℝ Q k := by dsimp [Q]; fun_prop
  have h := affine_pencil_zero_first_order hkI htI hDP.differentiableAt hDQ hN hz
  have hF : 8 * a * f ≠ 0 := ne_of_gt (by positivity)
  have hP0 : k ^ 2 + (2 * a - beta) * k - a ^ 2 = 0 :=
    (mul_eq_zero.mp h.1).resolve_left hF
  have hPD := h.2.2.1
  rw [hDP.deriv] at hPD
  have hL : 2 * k + 2 * a - beta = 0 := (mul_eq_zero.mp hPD).resolve_left hF
  have hLK := congrArg (fun y : ℝ => y * k) hL
  nlinarith only [hP0, hLK, sq_pos_of_pos ha, sq_nonneg k]

private theorem matrix_completion (f a af beta bf b k w r : ℝ) :
    8 * a * (2 * a * w ^ 2 + (beta - k + 2 * f * af) * b * w * r +
      (f * (k ^ 2 + (2 * a - beta) * k - a ^ 2) +
        (beta - k + f * bf) * b ^ 2 / 2) * r ^ 2) =
      (4 * a * w + (beta - k + 2 * f * af) * b * r) ^ 2 +
        calibrationDet f a af beta bf (b ^ 2) k * r ^ 2 := by
  unfold calibrationDet
  ring

end RicciFlowSharpEstimate.Analysis
