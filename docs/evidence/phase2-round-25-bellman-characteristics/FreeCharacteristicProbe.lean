import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Tactic
import RicciFlowSharpEstimate.Geometry.AreaScaleBalancedFreeInterval

noncomputable section

namespace RicciFlowSharpEstimate.Analysis

open Set Filter Topology MeasureTheory


private theorem cross_eq_zero_of_zero_bottom {D B : ℝ}
    (h : ∀ r v : ℝ, 0 ≤ D * r ^ 2 + B * r * v) : B = 0 := by
  by_contra hB
  have hh := h B (-(D + 1))
  nlinarith only [hh, sq_pos_of_ne_zero hB]

private theorem zero_control_of_positive_bottom_slope
    {l h u d1 d0 b1 b0 v1 v0 : ℝ} (hv1 : 0 < v1)
    (hPSD : ∀ k ∈ Icc l h, ∀ r v : ℝ,
      0 ≤ (u * k ^ 2 + d1 * k + d0) * r ^ 2 +
        (b1 * k + b0) * r * v + (v1 * k + v0) * v ^ 2)
    (hzero : ∀ r v : ℝ, ∃ k ∈ Icc l h,
      (u * k ^ 2 + d1 * k + d0) * r ^ 2 +
        (b1 * k + b0) * r * v + (v1 * k + v0) * v ^ 2 = 0) :
    ∃ k ∈ Icc l h, u * k ^ 2 + d1 * k + d0 = 0 ∧
      b1 * k + b0 = 0 ∧ v1 * k + v0 = 0 := by
  obtain ⟨k0, hk0, hk0zero⟩ := hzero 0 1
  have hlh : l ≤ h := hk0.1.trans hk0.2
  have hl : l ∈ Icc l h := ⟨le_rfl, hlh⟩
  have hVroot : v1 * k0 + v0 = 0 := by simpa using hk0zero
  have hVl_nonneg : 0 ≤ v1 * l + v0 := by simpa using hPSD l hl 0 1
  have hVl : v1 * l + v0 = 0 := by
    have hh := mul_le_mul_of_nonneg_left hk0.1 hv1.le
    nlinarith only [hVroot, hVl_nonneg, hh]
  have hBl : b1 * l + b0 = 0 := by
    apply cross_eq_zero_of_zero_bottom (D := u * l ^ 2 + d1 * l + d0)
    intro r v
    simpa only [hVl, zero_mul, add_zero] using hPSD l hl r v
  have hDl_nonneg : 0 ≤ u * l ^ 2 + d1 * l + d0 := by
    simpa using hPSD l hl 1 0
  let C := |u| * (2 * |l| + |h|) + |d1|
  have hC : 0 ≤ C := by dsimp only [C]; positivity
  have hcoeff (k : ℝ) (hk : k ∈ Icc l h) : |u * (k + l) + d1| ≤ C := by
    have hkabs : |k| ≤ |l| + |h| := by
      apply abs_le.mpr
      constructor <;> linarith [hk.1, hk.2, neg_abs_le l, le_abs_self h,
        abs_nonneg l, abs_nonneg h]
    have hsum : |k + l| ≤ 2 * |l| + |h| := by
      have hh := abs_add_le k l
      linarith
    calc
      |u * (k + l) + d1| ≤ |u * (k + l)| + |d1| := abs_add_le _ _
      _ = |u| * |k + l| + |d1| := by rw [abs_mul]
      _ ≤ |u| * (2 * |l| + |h|) + |d1| :=
        by linarith only [mul_le_mul_of_nonneg_left hsum (abs_nonneg u)]
      _ = C := rfl
  let r := min 1 (v1 / (C + |b1| + 1))
  have hden : 0 < C + |b1| + 1 := by linarith [abs_nonneg b1]
  have hr : 0 < r := lt_min zero_lt_one (div_pos hv1 hden)
  have hr1 : r ≤ 1 := min_le_left _ _
  have hrden : r * (C + |b1| + 1) ≤ v1 :=
    (le_div_iff₀ hden).mp (show r ≤ v1 / (C + |b1| + 1) from min_le_right _ _)
  have hrsq : r ^ 2 ≤ r := by
    nlinarith only [mul_nonneg hr.le (sub_nonneg.mpr hr1)]
  have hsmall : C * r ^ 2 + |b1| * r < v1 := by
    have hh := mul_le_mul_of_nonneg_left hrsq hC
    nlinarith only [hh, hrden, hr]
  have hbracket (k : ℝ) (hk : k ∈ Icc l h) :
      0 < r ^ 2 * (u * (k + l) + d1) + b1 * r + v1 := by
    have ha := mul_le_mul_of_nonneg_left (abs_le.mp (hcoeff k hk)).1 (sq_nonneg r)
    have hb := mul_le_mul_of_nonneg_right (neg_abs_le b1) hr.le
    nlinarith only [ha, hb, hsmall]
  have hBaff : b0 = -b1 * l := by linarith only [hBl]
  have hVaff : v0 = -v1 * l := by linarith only [hVl]
  have hfactor (k : ℝ) :
      (u * k ^ 2 + d1 * k + d0) * r ^ 2 + (b1 * k + b0) * r + (v1 * k + v0) =
        (u * l ^ 2 + d1 * l + d0) * r ^ 2 +
          (k - l) * (r ^ 2 * (u * (k + l) + d1) + b1 * r + v1) := by
    rw [hBaff, hVaff]
    ring
  obtain ⟨k, hk, hkzero⟩ := hzero r 1
  have hkzero' : (u * k ^ 2 + d1 * k + d0) * r ^ 2 +
      (b1 * k + b0) * r + (v1 * k + v0) = 0 := by simpa using hkzero
  rw [hfactor k] at hkzero'
  have hrest : 0 ≤ (k - l) * (r ^ 2 * (u * (k + l) + d1) + b1 * r + v1) :=
    mul_nonneg (sub_nonneg.mpr hk.1) (hbracket k hk).le
  have hproduct : (u * l ^ 2 + d1 * l + d0) * r ^ 2 = 0 := by
    apply le_antisymm
    · linarith only [hkzero', hrest]
    · exact mul_nonneg hDl_nonneg (sq_nonneg r)
  have hDl : u * l ^ 2 + d1 * l + d0 = 0 :=
    (mul_eq_zero.mp hproduct).resolve_right (sq_pos_of_pos hr).ne'
  exact ⟨l, hl, hDl, hBl, hVl⟩

/-- A nonnegative compact-control pencil that vanishes in every direction
has one control at which its entire quadratic matrix is zero. Interval
nonemptiness is already implied by the directional-zero hypothesis. -/
private theorem exists_zero_control_matrix
    {l h u d1 d0 b1 b0 v1 v0 : ℝ}
    (hPSD : ∀ k ∈ Icc l h, ∀ r v : ℝ,
      0 ≤ (u * k ^ 2 + d1 * k + d0) * r ^ 2 +
        (b1 * k + b0) * r * v + (v1 * k + v0) * v ^ 2)
    (hzero : ∀ r v : ℝ, ∃ k ∈ Icc l h,
      (u * k ^ 2 + d1 * k + d0) * r ^ 2 +
        (b1 * k + b0) * r * v + (v1 * k + v0) * v ^ 2 = 0) :
    ∃ k ∈ Icc l h, u * k ^ 2 + d1 * k + d0 = 0 ∧
      b1 * k + b0 = 0 ∧ v1 * k + v0 = 0 := by
  rcases lt_trichotomy v1 0 with hv1 | hv1 | hv1
  · have hPSDref : ∀ k ∈ Icc (-h) (-l), ∀ r v : ℝ,
        0 ≤ (u * k ^ 2 + (-d1) * k + d0) * r ^ 2 +
          ((-b1) * k + b0) * r * v + ((-v1) * k + v0) * v ^ 2 := by
      intro k hk r v
      have hk' : -k ∈ Icc l h := by constructor <;> linarith [hk.1, hk.2]
      have hh := hPSD (-k) hk' r v
      convert hh using 1
      ring
    have hzeroref : ∀ r v : ℝ, ∃ k ∈ Icc (-h) (-l),
        (u * k ^ 2 + (-d1) * k + d0) * r ^ 2 +
          ((-b1) * k + b0) * r * v + ((-v1) * k + v0) * v ^ 2 = 0 := by
      intro r v
      obtain ⟨k, hk, hkzero⟩ := hzero r v
      refine ⟨-k, ⟨by linarith [hk.2], by linarith [hk.1]⟩, ?_⟩
      convert hkzero using 1
      ring
    obtain ⟨k, hk, hD, hB, hV⟩ := zero_control_of_positive_bottom_slope
      (neg_pos.mpr hv1) hPSDref hzeroref
    refine ⟨-k, ⟨by linarith [hk.2], by linarith [hk.1]⟩, ?_, ?_, ?_⟩
    · convert hD using 1
      ring
    · convert hB using 1
      ring
    · convert hV using 1
      ring
  · obtain ⟨k0, _, hk0zero⟩ := hzero 0 1
    have hv0 : v0 = 0 := by simpa [hv1] using hk0zero
    obtain ⟨k, hk, hkzero⟩ := hzero 1 0
    have hD : u * k ^ 2 + d1 * k + d0 = 0 := by simpa using hkzero
    have hB : b1 * k + b0 = 0 := by
      apply cross_eq_zero_of_zero_bottom (D := u * k ^ 2 + d1 * k + d0)
      intro r v
      simpa only [hv1, hv0, zero_mul, zero_add, add_zero] using hPSD k hk r v
    exact ⟨k, hk, hD, hB, by simp only [hv1, hv0, zero_mul, zero_add]⟩
  · exact zero_control_of_positive_bottom_slope hv1 hPSD hzero



-- Actual partial derivatives in the full (x,f,b) geometry state are retained.
-- These are the V=0 and curvature-linear B=0 equations of a free Bellman branch.
private theorem no_free_quadratic_branch_on_box
    (a c : ℝ → ℝ → ℝ → ℝ)
    (xl xu fl fu bl bu x0 f0 b0 b1 : ℝ)
    (hx0 : x0 ∈ Ioo xl xu) (hf0 : f0 ∈ Ioo fl fu)
    (hb0 : b0 ∈ Ioo bl bu) (hb1 : b1 ∈ Ioo bl bu) (hne : b0 ≠ b1)
    (hcb : ∀ x ∈ Ioo xl xu, ∀ f ∈ Ioo fl fu, ∀ b ∈ Ioo bl bu,
      HasDerivAt (c x f) 0 b)
    (hV : ∀ x ∈ Ioo xl xu, ∀ f ∈ Ioo fl fu, ∀ b ∈ Ioo bl bu,
      2 * a x f b - b * c x f b +
        f * (deriv (fun y => c y f b) x + b * deriv (fun y => c x y b) f) -
        f * (c x f b) ^ 2 = 0)
    (hB : ∀ x ∈ Ioo xl xu, ∀ f ∈ Ioo fl fu, ∀ b ∈ Ioo bl bu,
      -b - 4 * f * deriv (a x f) b + 2 * f * c x f b = 0) : False := by
  have hC (x : ℝ) (hx : x ∈ Ioo xl xu) (f : ℝ) (hf : f ∈ Ioo fl fu)
      (b : ℝ) (hb : b ∈ Ioo bl bu) : c x f b = c x f b0 := by
    apply isOpen_Ioo.is_const_of_deriv_eq_zero (convex_Ioo bl bu).isPreconnected
      (fun y hy => (hcb x hx f hf y hy).differentiableAt.differentiableWithinAt)
      (fun y hy => (hcb x hx f hf y hy).deriv) hb hb0
  have hCx (b : ℝ) (hb : b ∈ Ioo bl bu) :
      deriv (fun x => c x f0 b) x0 = deriv (fun x => c x f0 b0) x0 := by
    apply Filter.EventuallyEq.deriv_eq
    filter_upwards [isOpen_Ioo.mem_nhds hx0] with x hx
    exact hC x hx f0 hf0 b hb
  have hCf (b : ℝ) (hb : b ∈ Ioo bl bu) :
      deriv (fun f => c x0 f b) f0 = deriv (fun f => c x0 f b0) f0 := by
    apply Filter.EventuallyEq.deriv_eq
    filter_upwards [isOpen_Ioo.mem_nhds hf0] with f hf
    exact hC x0 hx0 f hf b hb
  let L := (c x0 f0 b0 - f0 * deriv (fun f => c x0 f b0) f0) / 2
  let M := (f0 * (c x0 f0 b0) ^ 2 - f0 * deriv (fun x => c x f0 b0) x0) / 2
  have hA (b : ℝ) (hb : b ∈ Ioo bl bu) : a x0 f0 b = b * L + M := by
    have h := hV x0 hx0 f0 hf0 b hb
    rw [hC x0 hx0 f0 hf0 b hb, hCx b hb, hCf b hb] at h
    dsimp only [L, M]
    nlinarith only [h]
  have hAD (b : ℝ) (hb : b ∈ Ioo bl bu) : deriv (a x0 f0) b = L := by
    have hlin : HasDerivAt (fun y : ℝ => y * L + M) L b := by
      simpa only [one_mul, id_eq] using ((hasDerivAt_id b).mul_const L).add_const M
    apply (hlin.congr_of_eventuallyEq ?_).deriv
    filter_upwards [isOpen_Ioo.mem_nhds hb] with y hy
    exact hA y hy
  have h0 := hB x0 hx0 f0 hf0 b0 hb0
  have h1 := hB x0 hx0 f0 hf0 b1 hb1
  rw [hAD b0 hb0] at h0
  rw [hAD b1 hb1, hC x0 hx0 f0 hf0 b1 hb1] at h1
  apply hne
  linarith only [h0, h1]

private theorem free_control_coefficients
    (f b s a c ax af ab cx cf cb l h : ℝ)
    (hf : f ≠ 0) (hlh : l ≠ h)
    (hVl : 2 * a - b * c + f * (cx + b * cf - 2 * l * cb) - f * c ^ 2 = 0)
    (hVh : 2 * a - b * c + f * (cx + b * cf - 2 * h * cb) - f * c ^ 2 = 0)
    (hBl : -l * b + 2 * s + 2 * f * (ax + b * af - 2 * l * ab) +
      2 * f * c * (l - a) = 0)
    (hBh : -h * b + 2 * s + 2 * f * (ax + b * af - 2 * h * ab) +
      2 * f * c * (h - a) = 0) :
    cb = 0 ∧ 2 * a - b * c + f * (cx + b * cf) - f * c ^ 2 = 0 ∧
      -b - 4 * f * ab + 2 * f * c = 0 := by
  have hdiff : ((-2 * f) * cb) * (h - l) = 0 := by
    linear_combination hVh - hVl
  have hhl : h - l ≠ 0 := sub_ne_zero.mpr (Ne.symm hlh)
  have hfc : -2 * f ≠ 0 := mul_ne_zero (by norm_num) hf
  have hcb : cb = 0 :=
    (mul_eq_zero.mp ((mul_eq_zero.mp hdiff).resolve_right hhl)).resolve_left hfc
  refine ⟨hcb, ?_, ?_⟩
  · simpa only [hcb, mul_zero, sub_zero] using hVl
  · have hdiffB : (-b - 4 * f * ab + 2 * f * c) * (h - l) = 0 := by
      linear_combination hBh - hBl
    exact (mul_eq_zero.mp hdiffB).resolve_right hhl

private def controlCost (u d1 d0 b1 b0 v1 v0 k r v : ℝ) : ℝ :=
  (u * k ^ 2 + d1 * k + d0) * r ^ 2 +
    (b1 * k + b0) * r * v + (v1 * k + v0) * v ^ 2

private theorem control_zero_pins_control
    (u d1 d0 b1 b0 v1 v0 l h e k r v : ℝ)
    (hu : 0 < u) (he : e ∈ Icc l h) (hk : k ∈ Icc l h) (hr : r ≠ 0)
    (hPSD : ∀ j ∈ Icc l h, ∀ R V : ℝ, 0 ≤ controlCost u d1 d0 b1 b0 v1 v0 j R V)
    (heD : u * e ^ 2 + d1 * e + d0 = 0)
    (heB : b1 * e + b0 = 0) (heV : v1 * e + v0 = 0)
    (hkzero : controlCost u d1 d0 b1 b0 v1 v0 k r v = 0) : e = k := by
  by_contra hne
  have hm : (e + k) / 2 ∈ Icc l h := by constructor <;> linarith [he.1, he.2, hk.1, hk.2]
  have hmid := hPSD ((e + k) / 2) hm r v
  have hezero : controlCost u d1 d0 b1 b0 v1 v0 e r v = 0 := by
    unfold controlCost
    rw [heD, heB, heV]
    ring
  have hid : 4 * controlCost u d1 d0 b1 b0 v1 v0 ((e + k) / 2) r v =
      2 * controlCost u d1 d0 b1 b0 v1 v0 e r v +
        2 * controlCost u d1 d0 b1 b0 v1 v0 k r v - u * r ^ 2 * (e - k) ^ 2 := by
    unfold controlCost
    ring
  rw [hezero, hkzero] at hid
  have hgap : 0 < u * r ^ 2 * (e - k) ^ 2 :=
    mul_pos (mul_pos hu (sq_pos_of_ne_zero hr)) (sq_pos_of_ne_zero (sub_ne_zero.mpr hne))
  nlinarith only [hmid, hid, hgap]

private theorem interior_control_forces_vanishing_rows
    (u d1 d0 b1 b0 v1 v0 l h e : ℝ) (he : e ∈ Ioo l h)
    (hPSD : ∀ k ∈ Icc l h, ∀ r v : ℝ, 0 ≤ controlCost u d1 d0 b1 b0 v1 v0 k r v)
    (heV : v1 * e + v0 = 0) :
    v1 = 0 ∧ v0 = 0 ∧ b1 * l + b0 = 0 ∧ b1 * h + b0 = 0 := by
  have hlh := he.1.trans he.2
  have hVl : 0 ≤ v1 * l + v0 := by
    simpa [controlCost] using hPSD l ⟨le_rfl, hlh.le⟩ 0 1
  have hVh : 0 ≤ v1 * h + v0 := by
    simpa [controlCost] using hPSD h ⟨hlh.le, le_rfl⟩ 0 1
  have hv1 : v1 = 0 := by
    rcases lt_trichotomy v1 0 with hn | hz | hp
    · have hm := mul_neg_of_neg_of_pos hn (sub_pos.mpr he.2)
      nlinarith only [hm, hVh, heV]
    · exact hz
    · have hm := mul_pos hp (sub_pos.mpr he.1)
      nlinarith only [hm, hVl, heV]
  have hv0 : v0 = 0 := by simpa [hv1] using heV
  have hB (k : ℝ) (hk : k ∈ Icc l h) : b1 * k + b0 = 0 := by
    apply cross_eq_zero_of_zero_bottom (D := u * k ^ 2 + d1 * k + d0)
    intro r v
    simpa only [controlCost, hv1, hv0, zero_mul, zero_add, add_zero] using hPSD k hk r v
  exact ⟨hv1, hv0, hB l ⟨le_rfl, hlh.le⟩, hB h ⟨hlh.le, le_rfl⟩⟩

private def fieldD1 (s a : ℝ → ℝ → ℝ → ℝ) (x f b : ℝ) : ℝ :=
  2 * f * a x f b - 2 * f * deriv (s x f) b - b ^ 2 / 2
private def fieldD0 (s a : ℝ → ℝ → ℝ → ℝ) (x f b : ℝ) : ℝ :=
  -f * (a x f b) ^ 2 + b * s x f b +
    f * (deriv (fun y => s y f b) x + b * deriv (fun y => s x y b) f)
private def fieldB1 (a c : ℝ → ℝ → ℝ → ℝ) (x f b : ℝ) : ℝ :=
  -b - 4 * f * deriv (a x f) b + 2 * f * c x f b
private def fieldB0 (s a c : ℝ → ℝ → ℝ → ℝ) (x f b : ℝ) : ℝ :=
  2 * s x f b + 2 * f * (deriv (fun y => a y f b) x +
    b * deriv (fun y => a x y b) f) - 2 * f * c x f b * a x f b
private def fieldV1 (c : ℝ → ℝ → ℝ → ℝ) (x f b : ℝ) : ℝ :=
  -2 * f * deriv (c x f) b
private def fieldV0 (a c : ℝ → ℝ → ℝ → ℝ) (x f b : ℝ) : ℝ :=
  2 * a x f b - b * c x f b +
    f * (deriv (fun y => c y f b) x + b * deriv (fun y => c x y b) f) -
    f * (c x f b) ^ 2

private def fieldCost (s a c : ℝ → ℝ → ℝ → ℝ) (x f b k r v : ℝ) : ℝ :=
  controlCost f (fieldD1 s a x f b) (fieldD0 s a x f b)
    (fieldB1 a c x f b) (fieldB0 s a c x f b)
    (fieldV1 c x f b) (fieldV0 a c x f b) k r v

private theorem fieldCost_eq_full_remainder
    (s a c : ℝ → ℝ → ℝ → ℝ) (x f b k r v : ℝ) :
    fieldCost s a c x f b k r v =
      (2 * a x f b - b * c x f b + f *
        (deriv (fun y => c y f b) x + b * deriv (fun y => c x y b) f -
          2 * k * deriv (c x f) b) - f * (c x f b) ^ 2) * v ^ 2 +
      (-k * b + 2 * s x f b + 2 * f *
        (deriv (fun y => a y f b) x + b * deriv (fun y => a x y b) f -
          2 * k * deriv (a x f) b) + 2 * f * c x f b * (k - a x f b)) * r * v +
      (f * (k ^ 2 + 2 * k * a x f b - (a x f b) ^ 2) + b * s x f b + f *
        (deriv (fun y => s y f b) x + b * deriv (fun y => s x y b) f -
          2 * k * deriv (s x f) b) - k * b ^ 2 / 2) * r ^ 2 := by
  unfold fieldCost controlCost fieldD1 fieldD0 fieldB1 fieldB0 fieldV1 fieldV0
  ring

-- A whole-state tight Bellman branch cannot have a positive r² cost at
-- both curvature endpoints on an open geometry-state box. This does not
-- assume or conclude that all useful calibrations are Bellman-tight.
private theorem no_tight_free_field_box
    (s a c : ℝ → ℝ → ℝ → ℝ) (l h xl xu fl fu bl bu x0 f0 b0 b1 : ℝ)
    (hlh : l < h) (hx0 : x0 ∈ Ioo xl xu) (hf0 : f0 ∈ Ioo fl fu)
    (hb0 : b0 ∈ Ioo bl bu) (hb1 : b1 ∈ Ioo bl bu) (hne : b0 ≠ b1)
    (hf : ∀ f ∈ Ioo fl fu, f ≠ 0)
    (hc : ∀ x ∈ Ioo xl xu, ∀ f ∈ Ioo fl fu, ∀ b ∈ Ioo bl bu,
      DifferentiableAt ℝ (c x f) b)
    (hD : ∀ x ∈ Ioo xl xu, ∀ f ∈ Ioo fl fu, ∀ b ∈ Ioo bl bu,
      0 < f * l ^ 2 + fieldD1 s a x f b * l + fieldD0 s a x f b ∧
      0 < f * h ^ 2 + fieldD1 s a x f b * h + fieldD0 s a x f b)
    (hPSD : ∀ x ∈ Ioo xl xu, ∀ f ∈ Ioo fl fu, ∀ b ∈ Ioo bl bu,
      ∀ k ∈ Icc l h, ∀ r v : ℝ, 0 ≤ fieldCost s a c x f b k r v)
    (hzero : ∀ x ∈ Ioo xl xu, ∀ f ∈ Ioo fl fu, ∀ b ∈ Ioo bl bu,
      ∀ r v : ℝ, ∃ k ∈ Icc l h, fieldCost s a c x f b k r v = 0) : False := by
  have hdata (x : ℝ) (hx : x ∈ Ioo xl xu) (f : ℝ) (hfi : f ∈ Ioo fl fu)
      (b : ℝ) (hb : b ∈ Ioo bl bu) :
      deriv (c x f) b = 0 ∧ fieldV0 a c x f b = 0 ∧ fieldB1 a c x f b = 0 := by
    obtain ⟨e, he, heD, _, heV⟩ := exists_zero_control_matrix
      (hPSD x hx f hfi b hb) (hzero x hx f hfi b hb)
    have hei : e ∈ Ioo l h := by
      constructor
      · by_contra hn
        have hel : e = l := le_antisymm (le_of_not_gt hn) he.1
        subst e
        linarith only [heD, (hD x hx f hfi b hb).1]
      · by_contra hn
        have heh : e = h := le_antisymm he.2 (le_of_not_gt hn)
        subst e
        linarith only [heD, (hD x hx f hfi b hb).2]
    have hv := interior_control_forces_vanishing_rows f
      (fieldD1 s a x f b) (fieldD0 s a x f b)
      (fieldB1 a c x f b) (fieldB0 s a c x f b)
      (fieldV1 c x f b) (fieldV0 a c x f b) l h e hei
      (hPSD x hx f hfi b hb) heV
    have hcb : deriv (c x f) b = 0 :=
      (mul_eq_zero.mp hv.1).resolve_left (mul_ne_zero (by norm_num) (hf f hfi))
    have hB : fieldB1 a c x f b = 0 := by
      have hh : fieldB1 a c x f b * (h - l) = 0 := by
        linear_combination hv.2.2.2 - hv.2.2.1
      exact (mul_eq_zero.mp hh).resolve_right (sub_ne_zero.mpr hlh.ne')
    exact ⟨hcb, hv.2.1, hB⟩
  apply no_free_quadratic_branch_on_box a c xl xu fl fu bl bu x0 f0 b0 b1
    hx0 hf0 hb0 hb1 hne
  · intro x hx f hfi b hb
    have h := (hc x hx f hfi b hb).hasDerivAt
    rw [(hdata x hx f hfi b hb).1] at h
    exact h
  · intro x hx f hfi b hb
    exact (hdata x hx f hfi b hb).2.1
  · intro x hx f hfi b hb
    exact (hdata x hx f hfi b hb).2.2

private theorem no_tight_interior_control_kernel
    (s a c : ℝ → ℝ → ℝ → ℝ) (l h : ℝ)
    (U : Set (ℝ × ℝ × ℝ)) (hU : IsOpen U)
    (hf : ∀ x f b : ℝ, (x, f, b) ∈ U → 0 < f)
    (hc : ∀ x f b : ℝ, (x, f, b) ∈ U → DifferentiableAt ℝ (c x f) b)
    (hDl : ContinuousOn (fun z : ℝ × ℝ × ℝ =>
      z.2.1 * l ^ 2 + fieldD1 s a z.1 z.2.1 z.2.2 * l +
        fieldD0 s a z.1 z.2.1 z.2.2) U)
    (hDh : ContinuousOn (fun z : ℝ × ℝ × ℝ =>
      z.2.1 * h ^ 2 + fieldD1 s a z.1 z.2.1 z.2.2 * h +
        fieldD0 s a z.1 z.2.1 z.2.2) U)
    (hPSD : ∀ x f b : ℝ, (x, f, b) ∈ U →
      ∀ k ∈ Icc l h, ∀ r v : ℝ, 0 ≤ fieldCost s a c x f b k r v)
    (hzero : ∀ x f b : ℝ, (x, f, b) ∈ U →
      ∀ r v : ℝ, ∃ k ∈ Icc l h, fieldCost s a c x f b k r v = 0)
    (x0 f0 b0 k0 r0 v0 : ℝ) (hz0 : (x0, f0, b0) ∈ U)
    (hk0 : k0 ∈ Ioo l h) (hr0 : r0 ≠ 0)
    (hcost : fieldCost s a c x0 f0 b0 k0 r0 v0 = 0) : False := by
  have hlh := hk0.1.trans hk0.2
  have hf0 := hf x0 f0 b0 hz0
  obtain ⟨e, he, heD, heB, heV⟩ := exists_zero_control_matrix
    (hPSD x0 f0 b0 hz0) (hzero x0 f0 b0 hz0)
  have heq := control_zero_pins_control f0 (fieldD1 s a x0 f0 b0)
    (fieldD0 s a x0 f0 b0) (fieldB1 a c x0 f0 b0) (fieldB0 s a c x0 f0 b0)
    (fieldV1 c x0 f0 b0) (fieldV0 a c x0 f0 b0) l h e k0 r0 v0 hf0 he
    ⟨hk0.1.le, hk0.2.le⟩ hr0 (hPSD x0 f0 b0 hz0) heD heB heV hcost
  subst e
  have hends (j : ℝ) (hj : j ∈ Icc l h) (hjk : j ≠ k0) :
      0 < f0 * j ^ 2 + fieldD1 s a x0 f0 b0 * j + fieldD0 s a x0 f0 b0 := by
    have hnonneg : 0 ≤ f0 * j ^ 2 + fieldD1 s a x0 f0 b0 * j +
        fieldD0 s a x0 f0 b0 := by
      simpa [fieldCost, controlCost] using hPSD x0 f0 b0 hz0 j hj 1 0
    by_contra hn
    have hjzero : fieldCost s a c x0 f0 b0 j 1 0 = 0 := by
      have hd := le_antisymm (le_of_not_gt hn) hnonneg
      simpa [fieldCost, controlCost] using hd
    have hpin := control_zero_pins_control f0 (fieldD1 s a x0 f0 b0)
      (fieldD0 s a x0 f0 b0) (fieldB1 a c x0 f0 b0) (fieldB0 s a c x0 f0 b0)
      (fieldV1 c x0 f0 b0) (fieldV0 a c x0 f0 b0) l h k0 j 1 0 hf0
      ⟨hk0.1.le, hk0.2.le⟩ hj (by norm_num) (hPSD x0 f0 b0 hz0) heD heB heV hjzero
    exact hjk hpin.symm
  let L := fun z : ℝ × ℝ × ℝ => z.2.1 * l ^ 2 +
    fieldD1 s a z.1 z.2.1 z.2.2 * l + fieldD0 s a z.1 z.2.1 z.2.2
  let H := fun z : ℝ × ℝ × ℝ => z.2.1 * h ^ 2 +
    fieldD1 s a z.1 z.2.1 z.2.2 * h + fieldD0 s a z.1 z.2.1 z.2.2
  have hLp : 0 < L (x0, f0, b0) := hends l ⟨le_rfl, hlh.le⟩ hk0.1.ne
  have hHp : 0 < H (x0, f0, b0) := hends h ⟨hlh.le, le_rfl⟩ hk0.2.ne'
  have hLa : ContinuousAt L (x0, f0, b0) :=
    (hDl (x0, f0, b0) hz0).continuousAt (hU.mem_nhds hz0)
  have hHa : ContinuousAt H (x0, f0, b0) :=
    (hDh (x0, f0, b0) hz0).continuousAt (hU.mem_nhds hz0)
  have hLN : ∀ᶠ z in 𝓝 (x0, f0, b0), 0 < L z :=
    hLa.eventually (isOpen_Ioi.mem_nhds hLp)
  have hHN : ∀ᶠ z in 𝓝 (x0, f0, b0), 0 < H z :=
    hHa.eventually (isOpen_Ioi.mem_nhds hHp)
  have hN : ∀ᶠ z in 𝓝 (x0, f0, b0), z ∈ U ∧ 0 < L z ∧ 0 < H z := by
    filter_upwards [hU.mem_nhds hz0, hLN, hHN] with z hz hl hh
    exact ⟨hz, hl, hh⟩
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp hN
  have hbox (x f b : ℝ) (hx : x ∈ Ioo (x0 - δ) (x0 + δ))
      (hfi : f ∈ Ioo (f0 - δ) (f0 + δ)) (hb : b ∈ Ioo (b0 - δ) (b0 + δ)) :
      (x, f, b) ∈ U ∧ 0 < L (x, f, b) ∧ 0 < H (x, f, b) := by
    apply hball
    simp only [Metric.mem_ball, Prod.dist_eq, Real.dist_eq, max_lt_iff]
    exact ⟨abs_lt.mpr ⟨by linarith [hx.1], by linarith [hx.2]⟩,
      abs_lt.mpr ⟨by linarith [hfi.1], by linarith [hfi.2]⟩,
      abs_lt.mpr ⟨by linarith [hb.1], by linarith [hb.2]⟩⟩
  have hxc : x0 ∈ Ioo (x0 - δ) (x0 + δ) := ⟨by linarith, by linarith⟩
  have hfc : f0 ∈ Ioo (f0 - δ) (f0 + δ) := ⟨by linarith, by linarith⟩
  have hbc : b0 ∈ Ioo (b0 - δ) (b0 + δ) := ⟨by linarith, by linarith⟩
  have hbL : b0 - δ / 2 ∈ Ioo (b0 - δ) (b0 + δ) := ⟨by linarith, by linarith⟩
  have hbR : b0 + δ / 2 ∈ Ioo (b0 - δ) (b0 + δ) := ⟨by linarith, by linarith⟩
  apply no_tight_free_field_box s a c l h (x0 - δ) (x0 + δ)
    (f0 - δ) (f0 + δ) (b0 - δ) (b0 + δ) x0 f0 (b0 - δ / 2) (b0 + δ / 2)
    hlh hxc hfc hbL hbR (by linarith)
  · intro f hfi
    exact (hf x0 f b0 (hbox x0 f b0 hxc hfi hbc).1).ne'
  · intro x hx f hfi b hb
    exact hc x f b (hbox x f b hx hfi hb).1
  · intro x hx f hfi b hb
    exact (hbox x f b hx hfi hb).2
  · intro x hx f hfi b hb
    exact hPSD x f b (hbox x f b hx hfi hb).1
  · intro x hx f hfi b hb
    exact hzero x f b (hbox x f b hx hfi hb).1

open RicciFlowSharpEstimate.Geometry.AreaProfile in
private theorem actual_free_interval_excludes_tight_field
    (K r p : ℝ → ℝ) (l h A B η : ℝ)
    (hA : 0 < A) (hAB : A < B) (hB : B < 1) (hη : 0 < η)
    (hr : ∀ x ∈ Icc A B, η ≤ |r x|)
    (hK : ∀ᵐ x ∂volume.restrict (Ioo (0 : ℝ) 1),
      x ∈ Icc A B → l + η ≤ K x ∧ K x ≤ h - η)
    (s a c : ℝ → ℝ → ℝ → ℝ) (U : Set (ℝ × ℝ × ℝ)) (hU : IsOpen U)
    (hf : ∀ x f b : ℝ, (x, f, b) ∈ U → 0 < f)
    (hc : ∀ x f b : ℝ, (x, f, b) ∈ U → DifferentiableAt ℝ (c x f) b)
    (hDl : ContinuousOn (fun z : ℝ × ℝ × ℝ =>
      z.2.1 * l ^ 2 + fieldD1 s a z.1 z.2.1 z.2.2 * l +
        fieldD0 s a z.1 z.2.1 z.2.2) U)
    (hDh : ContinuousOn (fun z : ℝ × ℝ × ℝ =>
      z.2.1 * h ^ 2 + fieldD1 s a z.1 z.2.1 z.2.2 * h +
        fieldD0 s a z.1 z.2.1 z.2.2) U)
    (hPSD : ∀ x f b : ℝ, (x, f, b) ∈ U →
      ∀ k ∈ Icc l h, ∀ R V : ℝ, 0 ≤ fieldCost s a c x f b k R V)
    (hzero : ∀ x f b : ℝ, (x, f, b) ∈ U →
      ∀ R V : ℝ, ∃ k ∈ Icc l h, fieldCost s a c x f b k R V = 0)
    (hdom : ∀ x ∈ Ioo (0 : ℝ) 1, (x, warp K x, warpSlope K x) ∈ U)
    (hsat : ∀ᵐ x ∂volume.restrict (Ioo (0 : ℝ) 1),
      fieldCost s a c x (warp K x) (warpSlope K x) (K x) (r x) (warp K x * p x) = 0) :
    False := by
  let μ : Measure ℝ := volume.restrict (Ioo A B)
  have hsub : Ioo A B ⊆ Ioo (0 : ℝ) 1 := by
    intro x hx
    exact ⟨hA.trans hx.1, hx.2.trans hB⟩
  have hgood : ∀ᵐ x ∂μ, (x ∈ Icc A B → l + η ≤ K x ∧ K x ≤ h - η) ∧
      fieldCost s a c x (warp K x) (warpSlope K x) (K x) (r x) (warp K x * p x) = 0 := by
    exact ae_restrict_of_ae_restrict_of_subset hsub (hK.and hsat)
  have hμpos : 0 < μ univ := by
    simpa [μ, Real.volume_Ioo] using (sub_pos.mpr hAB)
  have hμne : μ ≠ 0 := by
    intro hh
    rw [hh] at hμpos
    simp at hμpos
  let : (ae μ).NeBot := ae_neBot.mpr hμne
  have hself : ∀ᵐ x ∂μ, x ∈ Ioo A B := ae_restrict_mem measurableSet_Ioo
  obtain ⟨x, hx, hcurv, hcost⟩ := (hself.and hgood).exists
  have hxcc : x ∈ Icc A B := ⟨hx.1.le, hx.2.le⟩
  have hKx := hcurv hxcc
  have hrx : r x ≠ 0 := abs_pos.mp (hη.trans_le (hr x hxcc))
  exact no_tight_interior_control_kernel s a c l h U hU hf hc hDl hDh hPSD hzero
    x (warp K x) (warpSlope K x) (K x) (r x) (warp K x * p x)
    (hdom x (hsub hx)) ⟨by linarith [hKx.1], by linarith [hKx.2]⟩ hrx hcost

open RicciFlowSharpEstimate.Geometry.AreaProfile in
private def TightBellmanFieldFor (l h : ℝ) (K r p : ℝ → ℝ) : Prop :=
  ∃ (s a c : ℝ → ℝ → ℝ → ℝ) (U : Set (ℝ × ℝ × ℝ)), IsOpen U ∧
    (∀ x f b : ℝ, (x, f, b) ∈ U → 0 < f) ∧
    (∀ x f b : ℝ, (x, f, b) ∈ U → DifferentiableAt ℝ (c x f) b) ∧
    ContinuousOn (fun z : ℝ × ℝ × ℝ =>
      z.2.1 * l ^ 2 + fieldD1 s a z.1 z.2.1 z.2.2 * l +
        fieldD0 s a z.1 z.2.1 z.2.2) U ∧
    ContinuousOn (fun z : ℝ × ℝ × ℝ =>
      z.2.1 * h ^ 2 + fieldD1 s a z.1 z.2.1 z.2.2 * h +
        fieldD0 s a z.1 z.2.1 z.2.2) U ∧
    (∀ x f b : ℝ, (x, f, b) ∈ U →
      ∀ k ∈ Icc l h, ∀ R V : ℝ, 0 ≤ fieldCost s a c x f b k R V) ∧
    (∀ x f b : ℝ, (x, f, b) ∈ U →
      ∀ R V : ℝ, ∃ k ∈ Icc l h, fieldCost s a c x f b k R V = 0) ∧
    (∀ x ∈ Ioo (0 : ℝ) 1, (x, warp K x, warpSlope K x) ∈ U) ∧
    (∀ᵐ x ∂volume.restrict (Ioo (0 : ℝ) 1),
      fieldCost s a c x (warp K x) (warpSlope K x) (K x) (r x) (warp K x * p x) = 0)

-- This is a negative result about the stated tight Bellman producer and
-- remainder-saturation specification, not about all quadratic certificates.
-- The actual minimum is an input here, never determining data for C_rot.
open RicciFlowSharpEstimate.Geometry.AreaProfile in
private theorem minimum_excludes_selected_box_tight_bellman
    {C : ℝ} {K r p z : ℝ → ℝ} (hC : 1 < C)
    (h : IsRecoverableAreaCompetitor C K r p z)
    (hr : ContinuousOn r (Ioo (0 : ℝ) 1))
    (hp : ContinuousOn p (Ioo (0 : ℝ) 1))
    (hzero : weakMeridionalAction K r p z = 0)
    (hmin : ∀ K' r' p' z' : ℝ → ℝ, IsRecoverableAreaCompetitor C K' r' p' z' →
      weakMeridionalAction K r p z ≤ weakMeridionalAction K' r' p' z') :
    ∃ κ : ℝ, 0 < κ ∧
      (∀ᵐ x ∂volume.restrict (Ioo (0 : ℝ) 1), κ ≤ K x ∧ K x ≤ C * κ) ∧
      ¬ TightBellmanFieldFor κ (C * κ) K r p := by
  obtain ⟨κ, _, A, B, η, hκ, _, _, hbox, _, _, _, _, _, _, _, _, _,
    hA, hAB, hB, hη, hfr, hfree⟩ :=
      h.exists_scale_balanced_free_curvature_interval hC hr hp hzero hmin
  refine ⟨κ, hκ, hbox, ?_⟩
  rintro ⟨s, a, c, U, hU, hf, hc, hDl, hDh, hPSD, hTight, hDom, hSat⟩
  have hfree' : ∀ᵐ x ∂volume.restrict (Ioo (0 : ℝ) 1),
      x ∈ Icc A B → κ + η ≤ K x ∧ K x ≤ C * κ - η := by
    filter_upwards [hfree] with x hx hxab
    exact ⟨(hx hxab).1, (hx hxab).2.1⟩
  exact actual_free_interval_excludes_tight_field K r p κ (C * κ) A B η hA hAB hB hη
    (fun x hx => (hfr x hx).2) hfree' s a c U hU hf hc hDl hDh hPSD hTight hDom hSat

end RicciFlowSharpEstimate.Analysis
