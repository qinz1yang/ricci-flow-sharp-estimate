/-
Copyright (c) 2026 Ziyang Qin. All rights reserved.
No license is granted by this file.
Authors: Ziyang Qin
-/
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.LocalExtr.Rolle
import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Isolated zeros of a weak triangular differential system

The leading coefficients are continuous and nonzero at the zero under study.
The lower coefficients need only be essentially bounded near that zero. The
proof uses absolute continuity and never differentiates a lower coefficient.
-/

noncomputable section

namespace RicciFlowSharpEstimate.Analysis

open Set Filter MeasureTheory
open scoped Topology

private theorem ae_nhds_le_nhdsNE (x : ℝ) :
    (𝓝 x ⊓ ae volume) ≤ 𝓝[≠] x := by
  apply le_inf inf_le_left
  apply le_principal_iff.mpr
  exact (volume.ae_ne x).filter_mono inf_le_right

private theorem tendsto_bounded_mul_zero {α : Type*} {l : Filter α}
    {u v : α → ℝ} {M : ℝ} (hu : ∀ᶠ x in l, |u x| ≤ M)
    (hv : Tendsto v l (𝓝 0)) : Tendsto (fun x => u x * v x) l (𝓝 0) := by
  apply squeeze_zero_norm' (a := fun x => M * ‖v x‖)
  · filter_upwards [hu] with x hx
    simpa only [norm_mul, Real.norm_eq_abs] using
      mul_le_mul_of_nonneg_right hx (abs_nonneg (v x))
  · simpa only [norm_zero, mul_zero] using hv.norm.const_mul M

private theorem ac_hasDerivAt_of_tendsto_deriv
    {f : ℝ → ℝ} {a x b c : ℝ}
    (hf : AbsolutelyContinuousOnInterval f a b) (hax : a < x) (hxb : x < b)
    (hlim : Tendsto (deriv f) (𝓝 x ⊓ ae volume) (𝓝 c)) :
    HasDerivAt f c x := by
  have hD := intervalIntegral.integral_hasDerivAt_of_tendsto_ae_right
    (f := deriv f) (a := x) (b := x) (c := c) IntervalIntegrable.refl
    (stronglyMeasurable_deriv f).aestronglyMeasurable.stronglyMeasurableAtFilter hlim
  have heq : (fun y => ∫ t in x..y, deriv f t) =ᶠ[𝓝 x] (fun y => f y - f x) := by
    filter_upwards [Ioo_mem_nhds hax hxb] with y hy
    apply AbsolutelyContinuousOnInterval.integral_deriv_eq_sub
    apply hf.mono
    intro t ht
    rw [uIcc_of_le (hax.trans hxb).le]
    rcases mem_uIcc.mp ht with ht | ht
    · exact ⟨hax.le.trans ht.1, ht.2.trans hy.2.le⟩
    · exact ⟨hy.1.le.trans ht.1, ht.2.trans hxb.le⟩
  have hsub : HasDerivAt (fun y => f y - f x) c x :=
    hD.congr_of_eventuallyEq heq.symm
  simpa only [sub_add_cancel] using hsub.add_const (f x)

private theorem eventually_ne_zero_of_hasDerivAt
    {f : ℝ → ℝ} {x c : ℝ} (hf : HasDerivAt f c x)
    (hf0 : f x = 0) (hc : c ≠ 0) : ∀ᶠ y in 𝓝[≠] x, f y ≠ 0 := by
  have he : ∀ᶠ y in 𝓝[≠] x, slope f x y ≠ 0 :=
    hf.tendsto_slope.eventually (eventually_ne_nhds hc)
  filter_upwards [he] with y hy hfy
  apply hy
  simp [slope, hf0, hfy]

private theorem eventually_ne_zero_of_derivative_eventually_ne_zero
    {f g : ℝ → ℝ} {a x b : ℝ} (hax : a < x) (hxb : x < b)
    (hD : ∀ y ∈ Ioo a b, HasDerivAt f (g y) y) (hf0 : f x = 0)
    (hg : ∀ᶠ y in 𝓝[≠] x, g y ≠ 0) : ∀ᶠ y in 𝓝[≠] x, f y ≠ 0 := by
  have hg' : ∀ᶠ y in 𝓝 x, y ≠ x → g y ≠ 0 := by
    simpa only [eventually_nhdsWithin_iff, mem_compl_iff, mem_singleton_iff] using hg
  have hI : ∀ᶠ y in 𝓝 x, y ∈ Ioo a b := Ioo_mem_nhds hax hxb
  have he : {y | y ∈ Ioo a b ∧ (y ≠ x → g y ≠ 0)} ∈ 𝓝 x :=
    hI.and hg'
  obtain ⟨u, v, hxuv, huv⟩ := mem_nhds_iff_exists_Ioo_subset.mp he
  have huvN : ∀ᶠ y in 𝓝 x, y ∈ Ioo u v := Ioo_mem_nhds hxuv.1 hxuv.2
  filter_upwards [huvN.filter_mono nhdsWithin_le_nhds,
    self_mem_nhdsWithin] with y hy hyx
  change y ≠ x at hyx
  intro hfy
  rcases lt_or_gt_of_ne hyx with hyx | hxy
  · have hcont : ContinuousOn f (Icc y x) := by
      intro t ht
      have htD := hD t (huv ⟨hy.1.trans_le ht.1, ht.2.trans_lt hxuv.2⟩).1
      exact htD.continuousAt.continuousWithinAt
    obtain ⟨t, ht, hgt⟩ := exists_hasDerivAt_eq_zero hyx hcont
      (hfy.trans hf0.symm) (fun t ht => hD t (huv
        ⟨hy.1.trans ht.1, ht.2.trans hxuv.2⟩).1)
    exact (huv ⟨hy.1.trans ht.1, ht.2.trans hxuv.2⟩).2 ht.2.ne hgt
  · have hcont : ContinuousOn f (Icc x y) := by
      intro t ht
      have htD := hD t (huv ⟨hxuv.1.trans_le ht.1, ht.2.trans_lt hy.2⟩).1
      exact htD.continuousAt.continuousWithinAt
    obtain ⟨t, ht, hgt⟩ := exists_hasDerivAt_eq_zero hxy hcont
      (hf0.trans hfy.symm) (fun t ht => hD t (huv
        ⟨hxuv.1.trans ht.1, ht.2.trans hy.2⟩).1)
    exact (huv ⟨hxuv.1.trans ht.1, ht.2.trans hy.2⟩).2 ht.1.ne' hgt

private theorem integral_pos_of_ae_pos {f : ℝ → ℝ} {a b : ℝ}
    (hab : a < b) (hf : IntervalIntegrable f volume a b)
    (hpos : ∀ᵐ x, x ∈ Ioo a b → 0 < f x) : 0 < ∫ x in a..b, f x := by
  let g : ℝ → ℝ := fun x => if 0 < f x then f x else 1
  have heq : f =ᵐ[volume.restrict (uIoc a b)] g := by
    rw [uIoc_of_le hab.le]
    apply ae_restrict_of_ae_eq_of_ae_restrict Ioo_ae_eq_Ioc
    rw [ae_restrict_iff' measurableSet_Ioo]
    filter_upwards [hpos] with x hx hxI
    simp only [g, ite_eq_left (hx hxI)]
  have hg : IntervalIntegrable g volume a b := hf.congr_ae heq
  have hgpos : ∀ x, 0 < g x := by
    intro x
    dsimp only [g]
    split_ifs with hx
    · exact hx
    · exact zero_lt_one
  rw [intervalIntegral.integral_congr_ae_restrict heq]
  exact intervalIntegral.intervalIntegral_pos_of_pos hg hgpos hab

private theorem ac_ne_of_ae_mul_deriv_pos {f : ℝ → ℝ} {a b c : ℝ}
    (hab : a < b) (hf : AbsolutelyContinuousOnInterval f a b)
    (hpos : ∀ᵐ x, x ∈ Ioo a b → 0 < c * deriv f x) : f a ≠ f b := by
  intro heq
  have hint := integral_pos_of_ae_pos hab (hf.intervalIntegrable_deriv.const_mul c) hpos
  rw [intervalIntegral.integral_const_mul, hf.integral_deriv_eq_sub, heq, sub_self,
    mul_zero] at hint
  exact (lt_irrefl 0) hint

private theorem ac_eventually_ne_zero_of_tendsto_deriv_div
    {f : ℝ → ℝ} {a x b c : ℝ}
    (hf : AbsolutelyContinuousOnInterval f a b) (hax : a < x) (hxb : x < b)
    (hf0 : f x = 0) (hc : c ≠ 0)
    (hlim : Tendsto (fun y => deriv f y / (y - x)) (𝓝 x ⊓ ae volume) (𝓝 c)) :
    ∀ᶠ y in 𝓝[≠] x, f y ≠ 0 := by
  have hcc : 0 < c * c := mul_self_pos.mpr hc
  have hsign : ∀ᶠ y in 𝓝 x ⊓ ae volume, 0 < c * deriv f y / (y - x) := by
    simpa only [mul_div_assoc] using
      (hlim.const_mul c).eventually (eventually_gt_nhds hcc)
  obtain ⟨s, hs, t, ht, hst⟩ := mem_inf_iff.mp hsign
  have hlocal : s ∩ Ioo a b ∈ 𝓝 x := inter_mem hs (Ioo_mem_nhds hax hxb)
  obtain ⟨u, v, hxuv, huv⟩ := mem_nhds_iff_exists_Ioo_subset.mp hlocal
  have hsign' : ∀ᵐ y, y ∈ Ioo u v → 0 < c * deriv f y / (y - x) := by
    filter_upwards [ht] with y hyt hy
    change y ∈ {y | 0 < c * deriv f y / (y - x)}
    rw [hst]
    exact ⟨(huv hy).1, hyt⟩
  have huvN : ∀ᶠ y in 𝓝 x, y ∈ Ioo u v := Ioo_mem_nhds hxuv.1 hxuv.2
  filter_upwards [huvN.filter_mono nhdsWithin_le_nhds,
    self_mem_nhdsWithin] with y hy hyx
  change y ≠ x at hyx
  intro hfy
  rcases lt_or_gt_of_ne hyx with hyx | hxy
  · have hfyx : AbsolutelyContinuousOnInterval f y x := by
      apply hf.mono
      rw [uIcc_of_le hyx.le, uIcc_of_le (hax.trans hxb).le]
      intro z hz
      exact ⟨(huv hy).2.1.le.trans hz.1, hz.2.trans hxb.le⟩
    apply ac_ne_of_ae_mul_deriv_pos hyx hfyx (c := -c) _ (hfy.trans hf0.symm)
    filter_upwards [hsign'] with z hz hzI
    have hratio := hz ⟨hy.1.trans hzI.1, hzI.2.trans hxuv.2⟩
    rcases div_pos_iff.mp hratio with h | h
    · exact False.elim ((sub_neg.mpr hzI.2).not_gt h.2)
    · simpa only [neg_mul] using neg_pos.mpr h.1
  · have hfxy : AbsolutelyContinuousOnInterval f x y := by
      apply hf.mono
      rw [uIcc_of_le hxy.le, uIcc_of_le (hax.trans hxb).le]
      intro z hz
      exact ⟨hax.le.trans hz.1, hz.2.trans (huv hy).2.2.le⟩
    apply ac_ne_of_ae_mul_deriv_pos hxy hfxy (c := c) _ (hf0.trans hfy.symm)
    filter_upwards [hsign'] with z hz hzI
    have hratio := hz ⟨hxuv.1.trans hzI.1, hzI.2.trans hy.2⟩
    rcases div_pos_iff.mp hratio with h | h
    · exact h.1
    · exact False.elim ((sub_pos.mpr hzI.1).not_gt h.2)

/-- A zero of the first coordinate of a weak triangular differential system is
isolated unless all four state coordinates vanish there. Only the two leading
coefficients and the last state must be continuous at the zero; the lower
coefficients are merely locally essentially bounded. No derivative of any
coefficient is assumed. -/
theorem isolated_zero_of_weak_triangular_system
    {r p q P a₁ a₂ b₁ c₁ b₂ c₂ d₂ : ℝ → ℝ} {a x₀ b : ℝ}
    (ha : a < x₀) (hb : x₀ < b)
    (hr : ∀ x ∈ Ioo a b, HasDerivAt r (p x) x)
    (hp : AbsolutelyContinuousOnInterval p a b)
    (hq : AbsolutelyContinuousOnInterval q a b)
    (hP : ContinuousAt P x₀) (ha₁ : ContinuousAt a₁ x₀) (ha₂ : ContinuousAt a₂ x₀)
    (ha₁0 : a₁ x₀ ≠ 0) (ha₂0 : a₂ x₀ ≠ 0)
    (hbound : ∃ M : ℝ, ∀ᵐ x, x ∈ Ioo a b →
      |b₁ x| ≤ M ∧ |c₁ x| ≤ M ∧ |b₂ x| ≤ M ∧ |c₂ x| ≤ M ∧ |d₂ x| ≤ M)
    (hODE : ∀ᵐ x, x ∈ Ioo a b →
      HasDerivAt p (a₁ x * q x + b₁ x * p x + c₁ x * r x) x ∧
      HasDerivAt q (a₂ x * P x + b₂ x * q x + c₂ x * p x + d₂ x * r x) x)
    (hr0 : r x₀ = 0) (hnonzero : p x₀ ≠ 0 ∨ q x₀ ≠ 0 ∨ P x₀ ≠ 0) :
    ∀ᶠ x in 𝓝[≠] x₀, r x ≠ 0 := by
  have hx₀ : x₀ ∈ Ioo a b := ⟨ha, hb⟩
  by_cases hp0 : p x₀ = 0
  · have hrc := (hr x₀ hx₀).continuousAt
    have hpc : ContinuousAt p x₀ := hp.continuousOn.continuousAt (by
      simpa only [uIcc_of_le (ha.trans hb).le] using Icc_mem_nhds ha hb)
    have hqc : ContinuousAt q x₀ := hq.continuousOn.continuousAt (by
      simpa only [uIcc_of_le (ha.trans hb).le] using Icc_mem_nhds ha hb)
    obtain ⟨M, hM⟩ := hbound
    let l : Filter ℝ := 𝓝 x₀ ⊓ ae volume
    have hIN : ∀ᶠ x in 𝓝 x₀, x ∈ Ioo a b := Ioo_mem_nhds ha hb
    have hI : ∀ᶠ x in l, x ∈ Ioo a b :=
      hIN.filter_mono inf_le_left
    have hM' : ∀ᶠ x in l,
        |b₁ x| ≤ M ∧ |c₁ x| ≤ M ∧ |b₂ x| ≤ M ∧ |c₂ x| ≤ M ∧ |d₂ x| ≤ M := by
      filter_upwards [hM.filter_mono inf_le_right, hI] with x hx hxI using hx hxI
    have hb₁ := hM'.mono fun _ hx => hx.1
    have hc₁ := hM'.mono fun _ hx => hx.2.1
    have hb₂ := hM'.mono fun _ hx => hx.2.2.1
    have hc₂ := hM'.mono fun _ hx => hx.2.2.2.1
    have hd₂ := hM'.mono fun _ hx => hx.2.2.2.2
    have hODE' : ∀ᶠ x in l,
        deriv p x = a₁ x * q x + b₁ x * p x + c₁ x * r x ∧
        deriv q x = a₂ x * P x + b₂ x * q x + c₂ x * p x + d₂ x * r x := by
      filter_upwards [hODE.filter_mono inf_le_right, hI] with x hx hxI
      exact ⟨(hx hxI).1.deriv, (hx hxI).2.deriv⟩
    have hrL : Tendsto r l (𝓝 0) := by
      simpa only [hr0] using hrc.tendsto.mono_left (show l ≤ 𝓝 x₀ from inf_le_left)
    have hpL : Tendsto p l (𝓝 0) := by
      simpa only [hp0] using hpc.tendsto.mono_left (show l ≤ 𝓝 x₀ from inf_le_left)
    have hqL : Tendsto q l (𝓝 (q x₀)) :=
      hqc.tendsto.mono_left inf_le_left
    have ha₁L : Tendsto a₁ l (𝓝 (a₁ x₀)) := ha₁.tendsto.mono_left inf_le_left
    have hpDL : Tendsto (deriv p) l (𝓝 (a₁ x₀ * q x₀)) := by
      have h := ((ha₁L.mul hqL).add (tendsto_bounded_mul_zero hb₁ hpL)).add
        (tendsto_bounded_mul_zero hc₁ hrL)
      have h' : Tendsto
          (fun x => a₁ x * q x + b₁ x * p x + c₁ x * r x) l
          (𝓝 (a₁ x₀ * q x₀)) := by simpa only [add_zero] using h
      exact h'.congr' (hODE'.mono fun _ hx => hx.1.symm)
    have hpD : HasDerivAt p (a₁ x₀ * q x₀) x₀ :=
      ac_hasDerivAt_of_tendsto_deriv hp ha hb hpDL
    apply eventually_ne_zero_of_derivative_eventually_ne_zero ha hb hr hr0
    by_cases hq0 : q x₀ = 0
    · have hP0 : P x₀ ≠ 0 := by
        rcases hnonzero with h | h | h
        · exact False.elim (h hp0)
        · exact False.elim (h hq0)
        · exact h
      have hqL0 : Tendsto q l (𝓝 0) := by simpa only [hq0] using hqL
      have hqDL : Tendsto (deriv q) l (𝓝 (a₂ x₀ * P x₀)) := by
        have h := ((((ha₂.tendsto.mono_left (show l ≤ 𝓝 x₀ from inf_le_left)).mul
          (hP.tendsto.mono_left inf_le_left)).add (tendsto_bounded_mul_zero hb₂ hqL0)).add
          (tendsto_bounded_mul_zero hc₂ hpL)).add (tendsto_bounded_mul_zero hd₂ hrL)
        have h' : Tendsto
            (fun x => a₂ x * P x + b₂ x * q x + c₂ x * p x + d₂ x * r x) l
            (𝓝 (a₂ x₀ * P x₀)) := by simpa only [add_zero] using h
        exact h'.congr' (hODE'.mono fun _ hx => hx.2.symm)
      have hqD : HasDerivAt q (a₂ x₀ * P x₀) x₀ :=
        ac_hasDerivAt_of_tendsto_deriv hq ha hb hqDL
      have hqSlope : Tendsto (fun x => q x / (x - x₀)) l (𝓝 (a₂ x₀ * P x₀)) := by
        have hs := hqD.tendsto_slope.mono_left (ae_nhds_le_nhdsNE x₀)
        change Tendsto (fun x => slope q x₀ x) _ _ at hs
        simpa only [slope_def_field, hq0, sub_zero] using hs
      have hpSlope : Tendsto (fun x => p x / (x - x₀)) l (𝓝 0) := by
        have hs := hpD.tendsto_slope.mono_left (ae_nhds_le_nhdsNE x₀)
        change Tendsto (fun x => slope p x₀ x) _ _ at hs
        simpa only [slope_def_field, hp0, hq0, mul_zero, sub_zero] using hs
      have hrSlope : Tendsto (fun x => r x / (x - x₀)) l (𝓝 0) := by
        have hs := (hr x₀ hx₀).tendsto_slope.mono_left (ae_nhds_le_nhdsNE x₀)
        change Tendsto (fun x => slope r x₀ x) _ _ at hs
        simpa only [slope_def_field, hr0, hp0, sub_zero] using hs
      have hpDSlope : Tendsto (fun x => deriv p x / (x - x₀)) l
          (𝓝 (a₁ x₀ * (a₂ x₀ * P x₀))) := by
        have h := ((ha₁L.mul hqSlope).add
          (tendsto_bounded_mul_zero hb₁ hpSlope)).add (tendsto_bounded_mul_zero hc₁ hrSlope)
        have h' : Tendsto
            (fun x => a₁ x * (q x / (x - x₀)) + b₁ x * (p x / (x - x₀)) +
              c₁ x * (r x / (x - x₀))) l
            (𝓝 (a₁ x₀ * (a₂ x₀ * P x₀))) := by simpa only [add_zero] using h
        apply h'.congr'
        filter_upwards [hODE'] with x hx
        rw [hx.1, add_div, add_div]
        simp only [mul_div_assoc]
      exact ac_eventually_ne_zero_of_tendsto_deriv_div hp ha hb hp0
        (mul_ne_zero ha₁0 (mul_ne_zero ha₂0 hP0)) hpDSlope
    · exact eventually_ne_zero_of_hasDerivAt hpD hp0 (mul_ne_zero ha₁0 hq0)
  · exact eventually_ne_zero_of_hasDerivAt (hr x₀ hx₀) hr0 hp0

end RicciFlowSharpEstimate.Analysis
