/-
Copyright (c) 2026 Ziyang Qin. All rights reserved.
No license is granted by this file.
Authors: Ziyang Qin
-/
import RicciFlowSharpEstimate.Analysis.InteriorMomentBasis
import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable

/-!
# A strict descent direction after enlarging a moment-constrained box

A source with positive negative-part mass admits a strictly negative pairing
after enlarging the upper box bound, while preserving both interval moments.
A free interior interval supplies two smooth moment corrections, and all
coefficient bounds and source identities are interpreted almost everywhere.
-/

noncomputable section

namespace RicciFlowSharpEstimate.Analysis

open Filter Function MeasureTheory Set
open scoped ContDiff Topology

local notation "areaμ" => volume.restrict (Ioo (0 : ℝ) 1)

private theorem window_moment_basis {a b : ℝ}
    (ha : 0 < a) (hab : a < b) (hb : b < 1) :
    ∃ (ψ0 ψ1 : ℝ → ℝ) (B : ℝ),
      0 < B ∧ ContDiff ℝ ∞ ψ0 ∧ ContDiff ℝ ∞ ψ1 ∧
      tsupport ψ0 ⊆ Ioo a b ∧ tsupport ψ1 ⊆ Ioo a b ∧
      (∀ x, |ψ0 x| ≤ B ∧ |ψ1 x| ≤ B) ∧
      (∫ x in (0 : ℝ)..1, ψ0 x) = 1 ∧
      (∫ x in (0 : ℝ)..1, x * ψ0 x) = 0 ∧
      (∫ x in (0 : ℝ)..1, ψ1 x) = 0 ∧
      (∫ x in (0 : ℝ)..1, x * ψ1 x) = 1 := by
  let c0 : ℝ := (2 * a + b) / 3
  let c1 : ℝ := (a + 2 * b) / 3
  have hac0 : a < c0 := by dsimp only [c0]; linarith
  have hc01 : c0 < c1 := by dsimp only [c0, c1]; linarith
  have hc1b : c1 < b := by dsimp only [c1]; linarith
  obtain ⟨χ0, hχ0smooth, hχ0compact, hχ0support, hχ0box, hχ0mass⟩ :=
    exists_contDiff_nonneg_tsupport_subset_integral_mul_pos
      (fun _ : ℝ => 1) 0 1 a c0 continuous_const.continuousOn ha.le hac0
      (hc01.le.trans (hc1b.le.trans hb.le)) (by intro x hx; norm_num)
  obtain ⟨χ1, hχ1smooth, hχ1compact, hχ1support, hχ1box, hχ1mass⟩ :=
    exists_contDiff_nonneg_tsupport_subset_integral_mul_pos
      (fun _ : ℝ => 1) 0 1 c1 b continuous_const.continuousOn
      (ha.le.trans (hac0.le.trans hc01.le)) hc1b hb.le (by intro x hx; norm_num)
  let m0 : ℝ := ∫ x in (0 : ℝ)..1, χ0 x
  let m1 : ℝ := ∫ x in (0 : ℝ)..1, χ1 x
  let n0 : ℝ := ∫ x in (0 : ℝ)..1, x * χ0 x
  let n1 : ℝ := ∫ x in (0 : ℝ)..1, x * χ1 x
  have hm0 : 0 < m0 := by simpa only [m0, one_mul] using hχ0mass
  have hm1 : 0 < m1 := by simpa only [m1, one_mul] using hχ1mass
  have hi0 : IntervalIntegrable χ0 volume 0 1 := hχ0smooth.continuous.intervalIntegrable 0 1
  have hi1 : IntervalIntegrable χ1 volume 0 1 := hχ1smooth.continuous.intervalIntegrable 0 1
  have hiw0 : IntervalIntegrable (fun x : ℝ => x * χ0 x) volume 0 1 :=
    (continuous_id.mul hχ0smooth.continuous).intervalIntegrable 0 1
  have hiw1 : IntervalIntegrable (fun x : ℝ => x * χ1 x) volume 0 1 :=
    (continuous_id.mul hχ1smooth.continuous).intervalIntegrable 0 1
  have hn0 : n0 ≤ c0 * m0 := by
    have hpoint : ∀ x ∈ Icc (0 : ℝ) 1, x * χ0 x ≤ c0 * χ0 x := by
      intro x _
      by_cases hx : χ0 x = 0
      · simp only [hx, mul_zero, le_refl]
      · have hxs := hχ0support (subset_tsupport χ0 (mem_support.mpr hx))
        exact mul_le_mul_of_nonneg_right hxs.2.le (hχ0box x).1
    have h := intervalIntegral.integral_mono_on zero_le_one hiw0 (hi0.const_mul c0) hpoint
    simpa only [intervalIntegral.integral_const_mul, m0, n0] using h
  have hn1 : c1 * m1 ≤ n1 := by
    have hpoint : ∀ x ∈ Icc (0 : ℝ) 1, c1 * χ1 x ≤ x * χ1 x := by
      intro x _
      by_cases hx : χ1 x = 0
      · simp only [hx, mul_zero, le_refl]
      · have hxs := hχ1support (subset_tsupport χ1 (mem_support.mpr hx))
        exact mul_le_mul_of_nonneg_right hxs.1.le (hχ1box x).1
    have h := intervalIntegral.integral_mono_on zero_le_one (hi1.const_mul c1) hiw1 hpoint
    simpa only [intervalIntegral.integral_const_mul, m1, n1] using h
  let d : ℝ := m0 * n1 - m1 * n0
  have hd : 0 < d := by
    have hupper := mul_le_mul_of_nonneg_left hn0 hm1.le
    have hlower := mul_le_mul_of_nonneg_left hn1 hm0.le
    have hgap := mul_pos (mul_pos (sub_pos.mpr hc01) hm0) hm1
    dsimp only [d]
    nlinarith
  let ψ0 : ℝ → ℝ := fun x => (n1 * χ0 x - n0 * χ1 x) / d
  let ψ1 : ℝ → ℝ := fun x => (m0 * χ1 x - m1 * χ0 x) / d
  have hψ0smooth : ContDiff ℝ ∞ ψ0 :=
    (((contDiff_const (c := n1)).mul hχ0smooth).sub
      ((contDiff_const (c := n0)).mul hχ1smooth)).div_const d
  have hψ1smooth : ContDiff ℝ ∞ ψ1 :=
    (((contDiff_const (c := m0)).mul hχ1smooth).sub
      ((contDiff_const (c := m1)).mul hχ0smooth)).div_const d
  have hψ0union : tsupport ψ0 ⊆ tsupport χ0 ∪ tsupport χ1 :=
    tsupport_binop_subset (fun u v : ℝ => (n1 * u - n0 * v) / d) (by simp) χ0 χ1
  have hψ1union : tsupport ψ1 ⊆ tsupport χ0 ∪ tsupport χ1 :=
    tsupport_binop_subset (fun u v : ℝ => (m0 * v - m1 * u) / d) (by simp) χ0 χ1
  have hcompactUnion : IsCompact (tsupport χ0 ∪ tsupport χ1) :=
    hχ0compact.isCompact.union hχ1compact.isCompact
  have hψ0compact : HasCompactSupport ψ0 :=
    hcompactUnion.of_isClosed_subset (isClosed_tsupport ψ0) hψ0union
  have hψ1compact : HasCompactSupport ψ1 :=
    hcompactUnion.of_isClosed_subset (isClosed_tsupport ψ1) hψ1union
  have hsupportUnion : tsupport χ0 ∪ tsupport χ1 ⊆ Ioo a b := by
    intro x hx
    rcases hx with hx | hx
    · have hx' := hχ0support hx
      exact ⟨hx'.1, hx'.2.trans (hc01.trans hc1b)⟩
    · have hx' := hχ1support hx
      exact ⟨(hac0.trans hc01).trans hx'.1, hx'.2⟩
  obtain ⟨B, hBpos, hB⟩ :=
    ((hψ0compact.isCompact_range hψ0smooth.continuous).union
      (hψ1compact.isCompact_range hψ1smooth.continuous)).isBounded.exists_pos_norm_le
  have hbound : ∀ x, |ψ0 x| ≤ B ∧ |ψ1 x| ≤ B := by
    intro x
    constructor
    · simpa only [Real.norm_eq_abs] using hB (ψ0 x) (Or.inl (mem_range_self x))
    · simpa only [Real.norm_eq_abs] using hB (ψ1 x) (Or.inr (mem_range_self x))
  have hlin (f g : ℝ → ℝ)
      (hf : IntervalIntegrable f volume 0 1) (hg : IntervalIntegrable g volume 0 1)
      (u v : ℝ) :
      (∫ x in (0 : ℝ)..1, (u * f x - v * g x) / d) =
        (u * (∫ x in (0 : ℝ)..1, f x) - v * (∫ x in (0 : ℝ)..1, g x)) / d := by
    rw [intervalIntegral.integral_div,
      intervalIntegral.integral_sub (hf.const_mul u) (hg.const_mul v),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
  refine ⟨ψ0, ψ1, B, hBpos, hψ0smooth, hψ1smooth,
    hψ0union.trans hsupportUnion, hψ1union.trans hsupportUnion, hbound, ?_, ?_, ?_, ?_⟩
  · calc
      (∫ x in (0 : ℝ)..1, ψ0 x) = (n1 * m0 - n0 * m1) / d :=
        hlin χ0 χ1 hi0 hi1 n1 n0
      _ = d / d := by congr 1; dsimp only [d]; ring
      _ = 1 := div_self hd.ne'
  · calc
      (∫ x in (0 : ℝ)..1, x * ψ0 x) =
          ∫ x in (0 : ℝ)..1, (n1 * (x * χ0 x) - n0 * (x * χ1 x)) / d := by
        apply intervalIntegral.integral_congr
        intro x _
        dsimp only [ψ0]
        ring
      _ = (n1 * n0 - n0 * n1) / d :=
        hlin (fun x => x * χ0 x) (fun x => x * χ1 x) hiw0 hiw1 n1 n0
      _ = 0 := by ring
  · calc
      (∫ x in (0 : ℝ)..1, ψ1 x) = (m0 * m1 - m1 * m0) / d :=
        hlin χ1 χ0 hi1 hi0 m0 m1
      _ = 0 := by ring
  · calc
      (∫ x in (0 : ℝ)..1, x * ψ1 x) =
          ∫ x in (0 : ℝ)..1, (m0 * (x * χ1 x) - m1 * (x * χ0 x)) / d := by
        apply intervalIntegral.integral_congr
        intro x _
        dsimp only [ψ1]
        ring
      _ = d / d :=
        hlin (fun x => x * χ1 x) (fun x => x * χ0 x) hiw1 hiw0 m0 m1
      _ = 1 := div_self hd.ne'

/-- Enlarging the upper box bound permits a strict negative pairing while
preserving both interval moments, provided a free interval has zero source
and the source has positive negative-part mass. -/
theorem exists_moment_preserving_box_expansion
    {K Z : ℝ → ℝ} {lo hi hi2 a b η : ℝ}
    (hKm : AEStronglyMeasurable K areaμ)
    (hbox : ∀ᵐ x ∂areaμ, lo ≤ K x ∧ K x ≤ hi)
    (hneg : 0 < ∫ x, max (-Z x) 0 ∂areaμ)
    (ha : 0 < a) (hab : a < b) (hb : b < 1) (hη : 0 < η)
    (hfree : ∀ᵐ x ∂areaμ, x ∈ Icc a b →
      lo + η ≤ K x ∧ K x ≤ hi - η ∧ Z x = 0)
    (hhi : hi < hi2) :
    ∃ J : ℝ → ℝ, AEStronglyMeasurable J areaμ ∧
      (∀ᵐ x ∂areaμ, lo ≤ J x ∧ J x ≤ hi2) ∧
      (∫ x in (0 : ℝ)..1, J x) = (∫ x in (0 : ℝ)..1, K x) ∧
      (∫ x in (0 : ℝ)..1, x * J x) = (∫ x in (0 : ℝ)..1, x * K x) ∧
      Integrable (fun x => Z x * (J x - K x)) areaμ ∧
      (∫ x, Z x * (J x - K x) ∂areaμ) < 0 := by
  obtain ⟨ψ0, ψ1, B, hB, hψ0, hψ1, hsψ0, hsψ1, hψbound,
    hm00, hm10, hm01, hm11⟩ := window_moment_basis ha hab hb
  let N := fun x => max (-Z x) 0
  have hNI : Integrable N areaμ := by
    by_contra hn
    exact (ne_of_gt hneg) (integral_undef hn)
  let N0 := hNI.aestronglyMeasurable.mk N
  have hN0m : Measurable N0 := hNI.aestronglyMeasurable.stronglyMeasurable_mk.measurable
  have hNeq : N =ᵐ[areaμ] N0 := hNI.aestronglyMeasurable.ae_eq_mk
  let V : ℝ → ℝ := {x | 0 < N0 x}.indicator (fun _ => 1)
  have hVm : Measurable V :=
    measurable_const.indicator (measurableSet_lt measurable_const hN0m)
  have hVbox (x : ℝ) : 0 ≤ V x ∧ V x ≤ 1 := by
    by_cases hx : 0 < N0 x <;> simp [V, hx]
  have hVI : Integrable V areaμ := by
    apply (integrable_const (1 : ℝ)).mono' hVm.aestronglyMeasurable
    exact Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hVbox x).1]
      exact (hVbox x).2
  have hxM : AEStronglyMeasurable (fun x : ℝ => x) areaμ :=
    continuous_id.aestronglyMeasurable
  have hxBound : ∀ᵐ x ∂areaμ, ‖x‖ ≤ 1 := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
    rw [Real.norm_eq_abs, abs_of_pos hx.1]
    exact hx.2.le
  have hKI : Integrable K areaμ := by
    apply (integrable_const (|lo| + |hi|)).mono' hKm
    filter_upwards [hbox] with x hx
    rw [Real.norm_eq_abs]
    apply abs_le.mpr
    constructor <;> linarith [neg_abs_le lo, le_abs_self hi, abs_nonneg lo, abs_nonneg hi]
  have hKII : IntervalIntegrable K volume 0 1 :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le zero_le_one).mpr hKI
  have hKWII : IntervalIntegrable (fun x : ℝ => x * K x) volume 0 1 :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le zero_le_one).mpr
      (hKI.bdd_mul hxM hxBound)
  have hVII : IntervalIntegrable V volume 0 1 :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le zero_le_one).mpr hVI
  have hVWII : IntervalIntegrable (fun x : ℝ => x * V x) volume 0 1 :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le zero_le_one).mpr
      (hVI.bdd_mul hxM hxBound)
  let m0 : ℝ := ∫ x in (0 : ℝ)..1, V x
  let m1 : ℝ := ∫ x in (0 : ℝ)..1, x * V x
  let c : ℝ → ℝ := fun x => m0 * ψ0 x + m1 * ψ1 x
  have hc : Continuous c :=
    (continuous_const.mul hψ0.continuous).add (continuous_const.mul hψ1.continuous)
  let C : ℝ := (|m0| + |m1|) * B
  have hC : 0 ≤ C := mul_nonneg (add_nonneg (abs_nonneg _) (abs_nonneg _)) hB.le
  have hcabs (x : ℝ) : |c x| ≤ C := by
    calc
      |c x| ≤ |m0 * ψ0 x| + |m1 * ψ1 x| := abs_add_le _ _
      _ = |m0| * |ψ0 x| + |m1| * |ψ1 x| := by rw [abs_mul, abs_mul]
      _ ≤ |m0| * B + |m1| * B := add_le_add
        (mul_le_mul_of_nonneg_left (hψbound x).1 (abs_nonneg _))
        (mul_le_mul_of_nonneg_left (hψbound x).2 (abs_nonneg _))
      _ = C := by dsimp only [C]; ring
  have hc_zero (x : ℝ) (hx : x ∉ Icc a b) : c x = 0 := by
    have hψ0x : ψ0 x = 0 := by
      by_contra hn
      exact hx (Ioo_subset_Icc_self (hsψ0 (subset_tsupport ψ0 (mem_support.mpr hn))))
    have hψ1x : ψ1 x = 0 := by
      by_contra hn
      exact hx (Ioo_subset_Icc_self (hsψ1 (subset_tsupport ψ1 (mem_support.mpr hn))))
    simp only [c, hψ0x, hψ1x, mul_zero, add_zero]
  have hψ0I : IntervalIntegrable ψ0 volume 0 1 := hψ0.continuous.intervalIntegrable 0 1
  have hψ1I : IntervalIntegrable ψ1 volume 0 1 := hψ1.continuous.intervalIntegrable 0 1
  have hψ0W : IntervalIntegrable (fun x : ℝ => x * ψ0 x) volume 0 1 :=
    (continuous_id.mul hψ0.continuous).intervalIntegrable 0 1
  have hψ1W : IntervalIntegrable (fun x : ℝ => x * ψ1 x) volume 0 1 :=
    (continuous_id.mul hψ1.continuous).intervalIntegrable 0 1
  have hcII : IntervalIntegrable c volume 0 1 := hc.intervalIntegrable 0 1
  have hcWII : IntervalIntegrable (fun x : ℝ => x * c x) volume 0 1 :=
    (continuous_id.mul hc).intervalIntegrable 0 1
  have hc0 : (∫ x in (0 : ℝ)..1, c x) = m0 := by
    change (∫ x in (0 : ℝ)..1, m0 * ψ0 x + m1 * ψ1 x) = m0
    rw [intervalIntegral.integral_add (hψ0I.const_mul m0) (hψ1I.const_mul m1),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul, hm00, hm01]
    ring
  have hc1 : (∫ x in (0 : ℝ)..1, x * c x) = m1 := by
    calc
      _ = ∫ x in (0 : ℝ)..1, m0 * (x * ψ0 x) + m1 * (x * ψ1 x) := by
        apply intervalIntegral.integral_congr
        intro x _
        dsimp only [c]
        ring
      _ = m1 := by
        rw [intervalIntegral.integral_add (hψ0W.const_mul m0) (hψ1W.const_mul m1),
          intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul, hm10, hm11]
        ring
  let d : ℝ → ℝ := fun x => V x - c x
  have hdM : AEStronglyMeasurable d areaμ := hVm.aestronglyMeasurable.sub hc.aestronglyMeasurable
  have hdI : Integrable d areaμ :=
    hVI.sub ((intervalIntegrable_iff_integrableOn_Ioo_of_le zero_le_one).mp hcII)
  have hdII : IntervalIntegrable d volume 0 1 :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le zero_le_one).mpr hdI
  have hdWII : IntervalIntegrable (fun x : ℝ => x * d x) volume 0 1 :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le zero_le_one).mpr
      (hdI.bdd_mul hxM hxBound)
  have hd0 : (∫ x in (0 : ℝ)..1, d x) = 0 := by
    change (∫ x in (0 : ℝ)..1, V x - c x) = 0
    rw [intervalIntegral.integral_sub hVII hcII, hc0]
    exact sub_self m0
  have hd1 : (∫ x in (0 : ℝ)..1, x * d x) = 0 := by
    calc
      _ = ∫ x in (0 : ℝ)..1, x * V x - x * c x := by
        apply intervalIntegral.integral_congr
        intro x _
        dsimp only [d]
        ring
      _ = 0 := by
        rw [intervalIntegral.integral_sub hVWII hcWII, hc1]
        exact sub_self m1
  let ε : ℝ := min (hi2 - hi) (η / (C + 1))
  have hden : 0 < C + 1 := by linarith
  have hε : 0 < ε := lt_min (sub_pos.mpr hhi) (div_pos hη hden)
  have hεgap : ε ≤ hi2 - hi := min_le_left _ _
  have hεC : ε * C ≤ η := by
    have he := (le_div_iff₀ hden).mp (show ε ≤ η / (C + 1) from min_le_right _ _)
    nlinarith
  let J : ℝ → ℝ := fun x => K x + ε * d x
  have hJm : AEStronglyMeasurable J areaμ := hKm.add (hdM.const_mul ε)
  have hJbox : ∀ᵐ x ∂areaμ, lo ≤ J x ∧ J x ≤ hi2 := by
    filter_upwards [hbox, hfree, hNeq] with x hxK hxFree hxN
    by_cases hx : x ∈ Icc a b
    · have hFx := hxFree hx
      have hN0x : N0 x = 0 := hxN.symm.trans (by simp only [N, hFx.2.2, neg_zero, max_self])
      have hVx : V x = 0 := by simp [V, hN0x]
      have hcε : |ε * c x| ≤ η := by
        rw [abs_mul, abs_of_pos hε]
        exact (mul_le_mul_of_nonneg_left (hcabs x) hε.le).trans hεC
      obtain ⟨hclo, hchi⟩ := abs_le.mp hcε
      change lo ≤ K x + ε * (V x - c x) ∧ K x + ε * (V x - c x) ≤ hi2
      rw [hVx]
      constructor <;> nlinarith [hFx.1, hFx.2.1]
    · have hcx := hc_zero x hx
      have hVx := hVbox x
      have hεV0 := mul_nonneg hε.le hVx.1
      have hεV1 := mul_le_mul_of_nonneg_left hVx.2 hε.le
      change lo ≤ K x + ε * (V x - c x) ∧ K x + ε * (V x - c x) ≤ hi2
      rw [hcx, sub_zero]
      constructor <;> nlinarith [hxK.1, hxK.2]
  have hZc : ∀ᵐ x ∂areaμ, Z x * c x = 0 := by
    filter_upwards [hfree] with x hx
    by_cases hxI : x ∈ Icc a b
    · rw [(hx hxI).2.2, zero_mul]
    · rw [hc_zero x hxI, mul_zero]
  have hZV : (fun x => Z x * V x) =ᵐ[areaμ] (fun x => -max (-Z x) 0) := by
    filter_upwards [hNeq] with x hx
    by_cases hn : 0 < N0 x
    · have hpos : 0 < max (-Z x) 0 := by simpa only [N, hx] using hn
      have hz : Z x < 0 := neg_pos.mp ((lt_max_iff.mp hpos).resolve_right (lt_irrefl 0))
      simp [V, hn, max_eq_left (neg_nonneg.mpr hz.le)]
    · have hnp : max (-Z x) 0 ≤ 0 := by
        simpa only [N, hx] using (le_of_not_gt hn : N0 x ≤ 0)
      have hz : 0 ≤ Z x := by have hh := (le_max_left (-Z x) 0).trans hnp; linarith
      simp [V, hn, max_eq_right (neg_nonpos.mpr hz)]
  have hZVI : Integrable (fun x => Z x * V x) areaμ := hNI.neg.congr hZV.symm
  have hZVint : (∫ x, Z x * V x ∂areaμ) = -(∫ x, max (-Z x) 0 ∂areaμ) := by
    rw [integral_congr_ae hZV, integral_neg]
  have hpair : (fun x => Z x * (J x - K x)) =ᵐ[areaμ]
      (fun x => ε * (Z x * V x)) := by
    filter_upwards [hZc] with x hx
    change Z x * ((K x + ε * (V x - c x)) - K x) = ε * (Z x * V x)
    calc
      _ = ε * (Z x * V x) - ε * (Z x * c x) := by ring
      _ = _ := by rw [hx, mul_zero, sub_zero]
  have hpairI : Integrable (fun x => Z x * (J x - K x)) areaμ :=
    (hZVI.const_mul ε).congr hpair.symm
  refine ⟨J, hJm, hJbox, ?_, ?_, hpairI, ?_⟩
  · change (∫ x in (0 : ℝ)..1, K x + ε * d x) = ∫ x in (0 : ℝ)..1, K x
    rw [intervalIntegral.integral_add hKII (hdII.const_mul ε),
      intervalIntegral.integral_const_mul, hd0, mul_zero, add_zero]
  · calc
      (∫ x in (0 : ℝ)..1, x * J x) =
          ∫ x in (0 : ℝ)..1, x * K x + ε * (x * d x) := by
        apply intervalIntegral.integral_congr
        intro x _
        dsimp only [J]
        ring
      _ = ∫ x in (0 : ℝ)..1, x * K x := by
        rw [intervalIntegral.integral_add hKWII (hdWII.const_mul ε),
          intervalIntegral.integral_const_mul, hd1, mul_zero, add_zero]
  · rw [integral_congr_ae hpair, integral_const_mul, hZVint]
    exact mul_neg_of_pos_of_neg hε (neg_neg_of_pos hneg)

end RicciFlowSharpEstimate.Analysis
