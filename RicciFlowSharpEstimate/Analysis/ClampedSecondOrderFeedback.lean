/-
Copyright (c) 2026 Ziyang Qin. All rights reserved.
No license is granted by this file.
Authors: Ziyang Qin
-/
import RicciFlowSharpEstimate.Analysis.AbsolutelyContinuousTaylor
import Mathlib.Algebra.Order.Group.MinMax

/-! # A clamped second-order feedback at a quadratic zero -/

noncomputable section
namespace RicciFlowSharpEstimate.Analysis
open Set MeasureTheory Filter Topology

private theorem clamp_distance (lo hi u v : ℝ) :
    |max lo (min hi u) - max lo (min hi v)| ≤ |u - v| := by
  have hmax := abs_max_sub_max_le_max lo (min hi u) lo (min hi v)
  have hmin := abs_min_sub_min_le_max hi u hi v
  simp only [sub_self, abs_zero,
    max_eq_right (abs_nonneg (min hi u - min hi v))] at hmax
  simp only [sub_self, abs_zero, max_eq_right (abs_nonneg (u - v))] at hmin
  exact hmax.trans hmin

private theorem clamp_feedback_fixed (lo hi α β : ℝ) (hlohi : lo ≤ hi) (hα : 0 < α) :
    let k := max lo (min hi (-β / (3 * α)))
    max lo (min hi (-(α * k + β) / (2 * α))) = k := by
  let t := -β / (3 * α)
  have hβ : β = -3 * α * t := by dsimp [t]; field_simp
  by_cases htl : t ≤ lo
  · have hk : max lo (min hi t) = lo := max_eq_left ((min_le_right _ _).trans htl)
    change max lo (min hi (-(α * max lo (min hi t) + β) / (2 * α))) = _
    rw [hk]
    apply max_eq_left
    apply (min_le_right _ _).trans
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < 2 * α)).mpr
    rw [hβ]
    nlinarith [mul_nonneg hα.le (sub_nonneg.mpr htl)]
  by_cases hht : hi ≤ t
  · have hk : max lo (min hi t) = hi := by rw [min_eq_left hht, max_eq_right hlohi]
    change max lo (min hi (-(α * max lo (min hi t) + β) / (2 * α))) = _
    rw [hk]
    have hh : hi ≤ -(α * hi + β) / (2 * α) := by
      apply (le_div_iff₀ (by positivity : (0 : ℝ) < 2 * α)).mpr
      rw [hβ]
      nlinarith [mul_nonneg hα.le (sub_nonneg.mpr hht)]
    rw [min_eq_left hh, max_eq_right hlohi]
  have hk : max lo (min hi t) = t := by
    rw [min_eq_right (le_of_not_ge hht), max_eq_right (le_of_not_ge htl)]
  change max lo (min hi (-(α * max lo (min hi t) + β) / (2 * α))) = _
  rw [hk]
  have heq : -(α * t + β) / (2 * α) = t := by rw [hβ]; field_simp; ring
  rw [heq]
  exact hk

private theorem join_distance {c x t : ℝ} (ht : t ∈ uIcc c x) : |t - c| ≤ |x - c| := by
  rcases mem_uIcc.mp ht with ht | ht
  · rw [abs_of_nonneg (sub_nonneg.mpr ht.1),
      abs_of_nonneg (sub_nonneg.mpr (ht.1.trans ht.2))]
    linarith [ht.2]
  · rw [abs_of_nonpos (sub_nonpos.mpr ht.2),
      abs_of_nonpos (sub_nonpos.mpr (ht.1.trans ht.2))]
    linarith [ht.1]

/-- A quadratic vanishing denominator and its actual second-order clamped
feedback force a finite trace. Only AC/FTC and an error tending to zero are
required; the clamped function itself need not be continuous at the node. -/
theorem tendsto_clamp_of_quadratic_feedback
    {H G D K e : ℝ → ℝ} {a b c lo hi α β : ℝ}
    (ha : a < c) (hb : c < b) (hlohi : lo ≤ hi) (hα : 0 < α)
    (hH : AbsolutelyContinuousOnInterval H a b)
    (hG : AbsolutelyContinuousOnInterval G a b)
    (hODE : ∀ᵐ x ∂volume, x ∈ Ioo a b →
      HasDerivAt H (G x) x ∧ HasDerivAt G (α * K x + β + e x) x)
    (hH0 : H c = 0) (hG0 : G c = 0)
    (he : Tendsto e (𝓝[≠] c) (𝓝 0))
    (hD : Tendsto (fun x => D x / (x - c) ^ 2) (𝓝[≠] c) (𝓝 α))
    (hclip : ∀ᶠ x in 𝓝[≠] c, K x = max lo (min hi (-H x / D x))) :
    Tendsto K (𝓝[≠] c) (𝓝 (max lo (min hi (-β / (3 * α))))) := by
  let k := max lo (min hi (-β / (3 * α)))
  let ell := (α * k + β) / (2 * α)
  let m := α * ell
  have hm : 2 * m = α * k + β := by dsimp [m, ell]; field_simp
  have hkfixed : max lo (min hi (-ell)) = k := by
    simpa only [ell, k, neg_div] using clamp_feedback_fixed lo hi α β hlohi hα
  change Tendsto K (𝓝[≠] c) (𝓝 k)
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have hepos : 0 < α * ε / 8 := by positivity
  have hrpos : 0 < min (α / 4) (α * ε / (16 * (|ell| + 1))) := by positivity
  have heabs : Tendsto (fun x => |e x|) (𝓝[≠] c) (𝓝 0) := by
    simpa only [abs_zero] using he.abs
  have hdabs : Tendsto (fun x => |D x / (x - c) ^ 2 - α|) (𝓝[≠] c) (𝓝 0) := by
    simpa only [sub_self, abs_zero] using (hD.sub_const α).abs
  have hnear : ∀ᶠ x in 𝓝[≠] c,
      |e x| ≤ α * ε / 8 ∧
      |D x / (x - c) ^ 2 - α| ≤ α / 4 ∧
      |D x / (x - c) ^ 2 - α| ≤ α * ε / (16 * (|ell| + 1)) ∧
      K x = max lo (min hi (-H x / D x)) := by
    filter_upwards [heabs.eventually (gt_mem_nhds hepos),
      hdabs.eventually (gt_mem_nhds hrpos), hclip] with x hx hd hk
    exact ⟨hx.le, hd.le.trans (min_le_left _ _), hd.le.trans (min_le_right _ _), hk⟩
  have hnear' : ∀ᶠ x in 𝓝 c, x ≠ c →
      |e x| ≤ α * ε / 8 ∧
      |D x / (x - c) ^ 2 - α| ≤ α / 4 ∧
      |D x / (x - c) ^ 2 - α| ≤ α * ε / (16 * (|ell| + 1)) ∧
      K x = max lo (min hi (-H x / D x)) := by
    simpa only [eventually_nhdsWithin_iff, mem_compl_iff, mem_singleton_iff] using hnear
  have hI : ∀ᶠ x in 𝓝 c, x ∈ Ioo a b := Ioo_mem_nhds ha hb
  obtain ⟨δ, hδ, hlocal⟩ := Metric.eventually_nhds_iff.mp (hI.and hnear')
  have hlocal' (x : ℝ) (hx : |x - c| < δ) :=
    hlocal (y := x) (by simpa only [Real.dist_eq] using hx)
  let S : Set ℝ := {y | ∃ x, 0 < |x - c| ∧ |x - c| < δ ∧ y = |K x - k|}
  have hSbdd : BddAbove S := by
    refine ⟨|lo| + |hi| + |k|, ?_⟩
    rintro y ⟨x, hx0, hx, rfl⟩
    have hnx : x ≠ c := sub_ne_zero.mp (abs_pos.mp hx0)
    have hcx := (hlocal' x hx).2 hnx
    have hbox : lo ≤ K x ∧ K x ≤ hi := by
      rw [hcx.2.2.2]
      exact ⟨le_max_left _ _, max_le hlohi (min_le_left _ _)⟩
    have hbK : |K x| ≤ |lo| + |hi| := by
      apply abs_le.mpr
      constructor <;> linarith [neg_abs_le lo, le_abs_self hi, abs_nonneg lo, abs_nonneg hi]
    exact (abs_sub _ _).trans (by linarith)
  have hSnonempty : S.Nonempty := by
    refine ⟨|K (c + δ / 2) - k|, c + δ / 2, ?_, ?_, rfl⟩ <;>
      rw [add_sub_cancel_left, abs_of_pos (by positivity : (0 : ℝ) < δ / 2)] <;> linarith
  let M := sSup S
  have hM (x : ℝ) (hx0 : 0 < |x - c|) (hx : |x - c| < δ) : |K x - k| ≤ M :=
    le_csSup hSbdd ⟨x, hx0, hx, rfl⟩
  have hM0 : 0 ≤ M := by
    obtain ⟨y, hy⟩ := hSnonempty
    obtain ⟨x, hx0, hx, rfl⟩ := hy
    exact (abs_nonneg _).trans (hM x hx0 hx)
  have himproved (x : ℝ) (hx0 : 0 < |x - c|) (hx : |x - c| < δ) :
      |K x - k| ≤ (2 / 3 : ℝ) * M + ε / 6 := by
    have hnx : x ≠ c := sub_ne_zero.mp (abs_pos.mp hx0)
    have hxl := hlocal' x hx
    have hxc := hxl.2 hnx
    have hsub : uIcc c x ⊆ uIcc a b := uIcc_subset_uIcc
      (by simpa only [uIcc_of_le (ha.trans hb).le] using Ioo_subset_Icc_self ⟨ha, hb⟩)
      (by simpa only [uIcc_of_le (ha.trans hb).le] using Ioo_subset_Icc_self hxl.1)
    let u := fun t => H t - m * (t - c) ^ 2
    let v := fun t => G t - 2 * m * (t - c)
    have hu : AbsolutelyContinuousOnInterval u c x :=
      (hH.mono hsub).fun_sub
        (show ContDiff ℝ 1 (fun t : ℝ => m * (t - c) ^ 2) by
          fun_prop).contDiffOn.absolutelyContinuousOnInterval
    have hv : AbsolutelyContinuousOnInterval v c x :=
      (hG.mono hsub).fun_sub
        (show ContDiff ℝ 1 (fun t : ℝ => 2 * m * (t - c)) by
          fun_prop).contDiffOn.absolutelyContinuousOnInterval
    have huv : ∀ᵐ t ∂volume, t ∈ uIcc c x → HasDerivAt u (v t) t := by
      filter_upwards [hODE] with t ht htI
      have hti := (hlocal' t ((join_distance htI).trans_lt hx)).1
      have hpol := (((hasDerivAt_id t).sub_const c).pow 2).const_mul m
      change HasDerivAt (fun y => m * (y - c) ^ 2) _ t at hpol
      have hUV := (ht hti).1.fun_sub hpol
      change HasDerivAt u _ t at hUV
      apply hUV.congr_deriv
      dsimp only [v]
      norm_num
      ring
    have hvb : ∀ᵐ t ∂volume, t ∈ uIcc c x → |deriv v t| ≤ α * M + α * ε / 8 := by
      filter_upwards [hODE, volume.ae_ne c] with t ht htc htI
      have htd := (join_distance htI).trans_lt hx
      have htl := hlocal' t htd
      have htr := htl.2 htc
      have hpoly := ((hasDerivAt_id t).sub_const c).const_mul (2 * m)
      have hVD := (ht htl.1).2.fun_sub hpoly
      change HasDerivAt v _ t at hVD
      have hval : deriv v t = α * (K t - k) + e t := by
        rw [hVD.deriv]
        nlinarith only [hm]
      rw [hval]
      calc
        _ ≤ |α * (K t - k)| + |e t| := abs_add_le _ _
        _ = α * |K t - k| + |e t| := by rw [abs_mul, abs_of_pos hα]
        _ ≤ α * M + α * ε / 8 := by
          gcongr
          · exact hM t (abs_pos.mpr (sub_ne_zero.mpr htc)) htd
          · exact htr.1
    have htay := AbsolutelyContinuousOnInterval.abs_sub_linear_le_of_deriv_bound
      hu hv huv hvb (c := c) (x := x) left_mem_uIcc right_mem_uIcc
    have htay' : |H x - m * (x - c) ^ 2| ≤ (α * M + α * ε / 8) / 2 * (x - c) ^ 2 := by
      simpa only [u, v, hH0, hG0, sub_self, zero_pow (by decide : 2 ≠ 0),
        mul_zero, sub_zero, zero_mul] using htay
    have hsquare : 0 < (x - c) ^ 2 := sq_pos_of_ne_zero (sub_ne_zero.mpr hnx)
    have hlow : 3 * α / 4 * (x - c) ^ 2 ≤ D x := by
      apply (le_div_iff₀ hsquare).mp
      have hh := (abs_le.mp hxc.2.1).1
      linarith
    have hDx : 0 < D x := (mul_pos (by positivity : (0 : ℝ) < 3 * α / 4) hsquare).trans_le hlow
    have hterm1 : |H x - m * (x - c) ^ 2| / D x ≤ (2 / 3 : ℝ) * M + ε / 12 := by
      apply (div_le_iff₀ hDx).mpr
      have hn : 0 ≤ (2 / 3 : ℝ) * M + ε / 12 := by positivity
      calc
        _ ≤ (α * M + α * ε / 8) / 2 * (x - c) ^ 2 := htay'
        _ = ((2 / 3 : ℝ) * M + ε / 12) * (3 * α / 4 * (x - c) ^ 2) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left hlow hn
    have hdiff : |α * (x - c) ^ 2 - D x| ≤
        (α * ε / (16 * (|ell| + 1))) * (x - c) ^ 2 := by
      have hid : α * (x - c) ^ 2 - D x =
          -(D x / (x - c) ^ 2 - α) * (x - c) ^ 2 := by
        field_simp [hsquare.ne']; ring
      rw [hid, abs_mul, abs_neg, abs_of_pos hsquare]
      exact mul_le_mul_of_nonneg_right hxc.2.2.1 hsquare.le
    have hell : |ell| * (α * ε / (16 * (|ell| + 1))) ≤ α * ε / 16 := by
      rw [← mul_div_assoc]
      apply (div_le_iff₀ (by positivity : (0 : ℝ) < 16 * (|ell| + 1))).mpr
      nlinarith [mul_nonneg hα.le hε.le]
    have hterm2 : |ell| * |α * (x - c) ^ 2 - D x| / D x ≤ ε / 12 := by
      apply (div_le_iff₀ hDx).mpr
      calc
        _ ≤ |ell| * ((α * ε / (16 * (|ell| + 1))) * (x - c) ^ 2) :=
          mul_le_mul_of_nonneg_left hdiff (abs_nonneg ell)
        _ = (|ell| * (α * ε / (16 * (|ell| + 1)))) * (x - c) ^ 2 := by ring
        _ ≤ (α * ε / 16) * (x - c) ^ 2 := mul_le_mul_of_nonneg_right hell hsquare.le
        _ = ε / 12 * (3 * α / 4 * (x - c) ^ 2) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left hlow (by positivity)
    have hClip := clamp_distance lo hi (-H x / D x) (-ell)
    rw [← hxc.2.2.2, hkfixed] at hClip
    have hid : -H x / D x - -ell =
        -((H x - m * (x - c) ^ 2) / D x +
          ell * (α * (x - c) ^ 2 - D x) / D x) := by
      dsimp only [m]
      field_simp [hDx.ne']; ring
    rw [hid, abs_neg] at hClip
    have hadd := abs_add_le ((H x - m * (x - c) ^ 2) / D x)
      (ell * (α * (x - c) ^ 2 - D x) / D x)
    simp only [abs_div, abs_mul, abs_of_pos hDx] at hadd
    linarith
  have hMsup : M ≤ (2 / 3 : ℝ) * M + ε / 6 := by
    apply csSup_le hSnonempty
    rintro y ⟨x, hx0, hx, rfl⟩
    exact himproved x hx0 hx
  have hMsmall : M < ε := by linarith
  have hball : ∀ᶠ x in 𝓝 c, |x - c| < δ := by
    filter_upwards [Metric.ball_mem_nhds c hδ] with x hx
    simpa only [Metric.mem_ball, Real.dist_eq] using hx
  filter_upwards [hball.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin]
    with x hx hnx
  change x ≠ c at hnx
  simpa only [Real.dist_eq] using
    (hM x (abs_pos.mpr (sub_ne_zero.mpr hnx)) hx).trans_lt hMsmall

end RicciFlowSharpEstimate.Analysis
