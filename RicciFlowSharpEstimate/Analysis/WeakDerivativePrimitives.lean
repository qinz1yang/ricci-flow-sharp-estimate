/-
Copyright (c) 2026 Ziyang Qin. All rights reserved.
No license is granted by this file.
Authors: Ziyang Qin
-/
import RicciFlowSharpEstimate.Analysis.WeakDerivative
import RicciFlowSharpEstimate.Analysis.SecondPrimitive
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
import Mathlib.MeasureTheory.Measure.OpenPos

/-!
# Integral representatives of real weak derivatives

A locally integrable function with locally integrable weak derivative on an
open interval has an explicit integral representative. All integrability used
in forming and differentiating the primitive is proved on compact intervals
strictly inside the domain; no endpoint integrability is assumed.
-/

noncomputable section

namespace RicciFlowSharpEstimate.Analysis

open Filter Function MeasureTheory Set
open scoped ContDiff Topology

private theorem weakPrimitive_uIcc_subset_Ioo {a b u v : ℝ}
    (hu : u ∈ Ioo a b) (hv : v ∈ Ioo a b) : uIcc u v ⊆ Ioo a b := by
  intro x hx
  rcases mem_uIcc.mp hx with hx | hx
  · exact ⟨hu.1.trans_le hx.1, hx.2.trans_lt hv.2⟩
  · exact ⟨hv.1.trans_le hx.1, hx.2.trans_lt hu.2⟩

private theorem weakPrimitive_intervalIntegrable {a b u v : ℝ} {f : ℝ → ℝ}
    (hf : LocallyIntegrableOn f (Ioo a b) volume)
    (hu : u ∈ Ioo a b) (hv : v ∈ Ioo a b) :
    IntervalIntegrable f volume u v :=
  intervalIntegrable_iff.mpr
    ((hf.integrableOn_compact_subset (weakPrimitive_uIcc_subset_Ioo hu hv)
      isCompact_uIcc).mono_set uIoc_subset_uIcc)

private theorem weakPrimitive_compact_enclosure {a b c : ℝ} {K : Set ℝ}
    (hc : c ∈ Ioo a b) (hK : IsCompact K) (hKU : K ⊆ Ioo a b) :
    ∃ u v : ℝ, a < u ∧ u < v ∧ v < b ∧ K ⊆ Ioo u v ∧ c ∈ Ioo u v := by
  have hK' : IsCompact (insert c K) := hK.insert c
  have hKU' : insert c K ⊆ Ioo a b := by
    intro x hx
    rcases hx with rfl | hx
    · exact hc
    · exact hKU hx
  obtain ⟨l, hl⟩ := hK'.exists_isLeast (insert_nonempty c K)
  obtain ⟨w, hw⟩ := hK'.exists_isGreatest (insert_nonempty c K)
  obtain ⟨u, hau, hul⟩ := exists_between (hKU' hl.1).1
  obtain ⟨v, hwv, hvb⟩ := exists_between (hKU' hw.1).2
  have huv : u < v := (hul.trans_le (hl.2 hw.1)).trans hwv
  refine ⟨u, v, hau, huv, hvb, ?_, ?_⟩
  · intro x hx
    exact ⟨hul.trans_le (hl.2 (mem_insert_of_mem c hx)),
      (hw.2 (mem_insert_of_mem c hx)).trans_lt hwv⟩
  · exact ⟨hul.trans_le (hl.2 (mem_insert c K)),
      (hw.2 (mem_insert c K)).trans_lt hwv⟩

private theorem weakPrimitive_absolutelyContinuous {a b c u v : ℝ} {p : ℝ → ℝ}
    (hp : LocallyIntegrableOn p (Ioo a b) volume) (hc : c ∈ Ioo a b)
    (hu : u ∈ Ioo a b) (hv : v ∈ Ioo a b) :
    AbsolutelyContinuousOnInterval (fun x ↦ ∫ t in c..x, p t) u v := by
  let l := min c (min u v)
  let w := max c (max u v)
  have hl : l ∈ Ioo a b :=
    ⟨lt_min hc.1 (lt_min hu.1 hv.1), (min_le_left _ _).trans_lt hc.2⟩
  have hw : w ∈ Ioo a b :=
    ⟨hc.1.trans_le (le_max_left _ _), max_lt hc.2 (max_lt hu.2 hv.2)⟩
  have hlw : l ≤ w := (min_le_left _ _).trans (le_max_left _ _)
  have hcw : c ∈ uIcc l w := by
    rw [uIcc_of_le hlw]
    exact ⟨min_le_left _ _, le_max_left _ _⟩
  have huw : u ∈ uIcc l w := by
    rw [uIcc_of_le hlw]
    exact ⟨(min_le_right _ _).trans (min_le_left _ _),
      (le_max_left _ _).trans (le_max_right _ _)⟩
  have hvw : v ∈ uIcc l w := by
    rw [uIcc_of_le hlw]
    exact ⟨(min_le_right _ _).trans (min_le_right _ _),
      (le_max_right _ _).trans (le_max_right _ _)⟩
  have hi := weakPrimitive_intervalIntegrable hp hl hw
  have hAC := hi.absolutelyContinuousOnInterval_intervalIntegral hcw
  exact hAC.mono (uIcc_subset_uIcc huw hvw)

private theorem weakPrimitive_continuousOn {a b c : ℝ} {p : ℝ → ℝ}
    (hp : LocallyIntegrableOn p (Ioo a b) volume) (hc : c ∈ Ioo a b) :
    ContinuousOn (fun x ↦ ∫ t in c..x, p t) (Ioo a b) := by
  intro x hx
  obtain ⟨u, hau, hux⟩ := exists_between hx.1
  obtain ⟨v, hxv, hvb⟩ := exists_between hx.2
  have huv : u < v := hux.trans hxv
  have hAC := weakPrimitive_absolutelyContinuous hp hc
    (show u ∈ Ioo a b from ⟨hau, hux.trans hx.2⟩)
    (show v ∈ Ioo a b from ⟨hx.1.trans hxv, hvb⟩)
  have hN : uIcc u v ∈ 𝓝 x := by
    rw [uIcc_of_le huv.le]
    exact Icc_mem_nhds hux hxv
  exact (hAC.continuousOn.continuousAt hN).continuousWithinAt

private theorem weakPrimitive_integral_mul_bridge {u v : ℝ} {φ f : ℝ → ℝ}
    (hφ : tsupport φ ⊆ Ioo u v) :
    (∫ x, φ x * f x) = ∫ x in u..v, φ x * f x := by
  symm
  apply intervalIntegral.integral_eq_integral_of_support_subset
  intro x hx
  have hxφ : x ∈ tsupport φ := subset_tsupport φ (mul_ne_zero_iff.mp hx).1
  exact ⟨(hφ hxφ).1, (hφ hxφ).2.le⟩

private theorem weakPrimitive_hasWeakDerivOn {a b c : ℝ} {p : ℝ → ℝ}
    (hp : LocallyIntegrableOn p (Ioo a b) volume) (hc : c ∈ Ioo a b) :
    HasWeakDerivOn (Ioo a b) (fun x ↦ ∫ t in c..x, p t) p := by
  let Q : ℝ → ℝ := fun x ↦ ∫ t in c..x, p t
  refine ⟨(weakPrimitive_continuousOn hp hc).locallyIntegrableOn measurableSet_Ioo,
    hp, ?_⟩
  intro φ hφ hφc hφU
  obtain ⟨u, v, hau, huv, hvb, hφuv, hcuv⟩ :=
    weakPrimitive_compact_enclosure hc hφc hφU
  have hu : u ∈ Ioo a b := ⟨hau, huv.trans hvb⟩
  have hv : v ∈ Ioo a b := ⟨hau.trans huv, hvb⟩
  have hpI := weakPrimitive_intervalIntegrable hp hu hv
  have hcI : c ∈ uIcc u v := by
    rw [uIcc_of_le huv.le]
    exact ⟨hcuv.1.le, hcuv.2.le⟩
  have hQAC : AbsolutelyContinuousOnInterval Q u v :=
    hpI.absolutelyContinuousOnInterval_intervalIntegral hcI
  have hφAC : AbsolutelyContinuousOnInterval φ u v :=
    ((hφ.of_le (by simp) : ContDiff ℝ 1 φ).contDiffOn).absolutelyContinuousOnInterval
  have hφu : φ u = 0 := image_eq_zero_of_notMem_tsupport fun hx ↦
    (hφuv hx).1.false
  have hφv : φ v = 0 := image_eq_zero_of_notMem_tsupport fun hx ↦
    (hφuv hx).2.false
  have hD : (∫ x in u..v, deriv Q x * φ x) = ∫ x in u..v, p x * φ x := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards [hpI.ae_hasDerivAt_integral] with x hx hxI
    rw [(hx (uIoc_subset_uIcc hxI) c hcI).deriv]
  have hParts := hQAC.integral_mul_deriv_eq_deriv_mul hφAC
  rw [hφu, hφv, hD] at hParts
  rw [weakPrimitive_integral_mul_bridge (tsupport_deriv_subset.trans hφuv),
    weakPrimitive_integral_mul_bridge hφuv]
  simpa only [Q, mul_comm, mul_zero, zero_mul, zero_sub, sub_zero] using hParts

private theorem weakPrimitive_unit_test {a b c : ℝ} (hc : c ∈ Ioo a b) :
    ∃ ρ : ℝ → ℝ, ContDiff ℝ ∞ ρ ∧ HasCompactSupport ρ ∧
      tsupport ρ ⊆ Ioo a b ∧ (∫ x, ρ x) = 1 := by
  obtain ⟨f, hfU, hfc, hf, hf01, hfc'⟩ :=
    exists_contDiff_tsupport_subset (n := (⊤ : ℕ∞)) (isOpen_Ioo.mem_nhds hc)
  have hfpos : 0 < ∫ x, f x :=
    hf.continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero hfc
      (fun x ↦ (hf01 (mem_range_self x)).1) (by rw [hfc']; norm_num)
  refine ⟨fun x ↦ (∫ t, f t)⁻¹ * f x, contDiff_const.mul hf, hfc.mul_left,
    tsupport_mul_subset_right.trans hfU, ?_⟩
  rw [integral_const_mul, inv_mul_cancel₀ hfpos.ne']

private theorem weakPrimitive_compact_antiderivative {a b c : ℝ} {ψ : ℝ → ℝ}
    (hc : c ∈ Ioo a b) (hψ : ContDiff ℝ ∞ ψ) (hψc : HasCompactSupport ψ)
    (hψU : tsupport ψ ⊆ Ioo a b) (hψzero : (∫ x, ψ x) = 0) :
    ∃ Φ : ℝ → ℝ, ContDiff ℝ ∞ Φ ∧ HasCompactSupport Φ ∧
      tsupport Φ ⊆ Ioo a b ∧ deriv Φ = ψ := by
  obtain ⟨u, v, hau, huv, hvb, hψuv, _hcuv⟩ :=
    weakPrimitive_compact_enclosure hc hψc hψU
  let Φ : ℝ → ℝ := fun x ↦ ∫ t in u..x, ψ t
  have hΦ : ContDiff ℝ ∞ Φ := SecondPrimitive.integral_contDiff ψ hψ u
  have hΦD : deriv Φ = ψ := by
    funext x
    exact (hψ.continuous.integral_hasStrictDerivAt u x).hasDerivAt.deriv
  have hΦsupp : support Φ ⊆ Icc u v := by
    intro x hx
    by_contra hxI
    have hzero : Φ x = 0 := by
      by_cases hux : u ≤ x
      · have hvx : v < x := lt_of_not_ge fun hxv ↦ hxI ⟨hux, hxv⟩
        calc
          Φ x = ∫ t, ψ t := by
            apply intervalIntegral.integral_eq_integral_of_support_subset
            intro t ht
            have htI := hψuv (subset_tsupport ψ ht)
            exact ⟨htI.1, htI.2.le.trans hvx.le⟩
          _ = 0 := hψzero
      · have hxu : x ≤ u := (lt_of_not_ge hux).le
        calc
          Φ x = ∫ t in u..x, (0 : ℝ) := by
            apply intervalIntegral.integral_congr
            intro t ht
            rw [uIcc_of_ge hxu] at ht
            exact image_eq_zero_of_notMem_tsupport fun htψ ↦
              (hψuv htψ).1.not_ge ht.2
          _ = 0 := by simp
    exact hx hzero
  have hΦtsupp : tsupport Φ ⊆ Icc u v := closure_minimal hΦsupp isClosed_Icc
  refine ⟨Φ, hΦ, HasCompactSupport.of_support_subset_isCompact isCompact_Icc hΦsupp,
    ?_, hΦD⟩
  intro x hx
  exact ⟨hau.trans_le (hΦtsupp hx).1, (hΦtsupp hx).2.trans_lt hvb⟩

private theorem weakPrimitive_ae_constant {a b c : ℝ} {f : ℝ → ℝ}
    (hc : c ∈ Ioo a b) (hf : LocallyIntegrableOn f (Ioo a b) volume)
    (hzero : ∀ φ : ℝ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      tsupport φ ⊆ Ioo a b → (∫ x, deriv φ x * f x) = 0) :
    ∃ d : ℝ, f =ᵐ[volume.restrict (Ioo a b)] (fun _ ↦ d) := by
  obtain ⟨ρ, hρ, hρc, hρU, hρone⟩ := weakPrimitive_unit_test hc
  let d : ℝ := ∫ x, ρ x * f x
  have hρI : Integrable ρ volume := hρ.continuous.integrable_of_hasCompactSupport hρc
  have hρfI : Integrable (fun x ↦ ρ x * f x) volume :=
    integrable_mul_of_locallyIntegrableOn hf hρ.continuous hρc hρU
  have hz : ∀ᵐ x ∂volume, x ∈ Ioo a b → (f x - d) = 0 := by
    apply isOpen_Ioo.ae_eq_zero_of_integral_contDiff_smul_eq_zero
      (hf.sub (locallyIntegrableOn_const d))
    intro η hη hηc hηU
    let A : ℝ := ∫ x, η x
    let ψ : ℝ → ℝ := fun x ↦ η x - A * ρ x
    have hηI : Integrable η volume := hη.continuous.integrable_of_hasCompactSupport hηc
    have hηfI : Integrable (fun x ↦ η x * f x) volume :=
      integrable_mul_of_locallyIntegrableOn hf hη.continuous hηc hηU
    have hψ : ContDiff ℝ ∞ ψ := hη.sub (contDiff_const.mul hρ)
    have hψc : HasCompactSupport ψ := hηc.sub hρc.mul_left
    have hψU : tsupport ψ ⊆ Ioo a b :=
      (tsupport_sub η (fun x ↦ A * ρ x)).trans
        (union_subset hηU (tsupport_mul_subset_right.trans hρU))
    have hψzero : (∫ x, ψ x) = 0 := by
      dsimp only [ψ]
      rw [integral_sub hηI (hρI.const_mul A), integral_const_mul, hρone]
      simp [A]
    obtain ⟨Φ, hΦ, hΦc, hΦU, hΦD⟩ :=
      weakPrimitive_compact_antiderivative hc hψ hψc hψU hψzero
    have hψf := hzero Φ hΦ hΦc hΦU
    rw [hΦD] at hψf
    change (∫ x, (η x - A * ρ x) * f x) = 0 at hψf
    simp_rw [sub_mul, mul_assoc] at hψf
    rw [integral_sub hηfI (hρfI.const_mul A), integral_const_mul] at hψf
    simp only [Pi.sub_apply, smul_eq_mul, mul_sub]
    rw [integral_sub hηfI (hηI.mul_const d), integral_mul_const]
    exact hψf
  refine ⟨d, (ae_restrict_iff' measurableSet_Ioo).2 ?_⟩
  filter_upwards [hz] with x hx
  intro hxU
  exact sub_eq_zero.mp (hx hxU)

/-- A real weak derivative determines an explicit integral representative on
the open interval, up to one additive constant. -/
theorem HasWeakDerivOn.exists_integral_representative_Ioo
    {a b c : ℝ} {r p : ℝ → ℝ} (h : HasWeakDerivOn (Ioo a b) r p)
    (hc : c ∈ Ioo a b) :
    ∃ d : ℝ, r =ᵐ[volume.restrict (Ioo a b)] (fun x ↦ d + ∫ t in c..x, p t) := by
  let Q : ℝ → ℝ := fun x ↦ ∫ t in c..x, p t
  have hQ : HasWeakDerivOn (Ioo a b) Q p :=
    weakPrimitive_hasWeakDerivOn h.locallyIntegrable_deriv hc
  have hf : LocallyIntegrableOn (r - Q) (Ioo a b) volume :=
    h.locallyIntegrable.sub hQ.locallyIntegrable
  have hzero : ∀ φ : ℝ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      tsupport φ ⊆ Ioo a b → (∫ x, deriv φ x * (r - Q) x) = 0 := by
    intro φ hφ hφc hφU
    simp only [Pi.sub_apply, mul_sub]
    rw [integral_sub (h.integrable_deriv_test_mul hφ hφc hφU)
      (hQ.integrable_deriv_test_mul hφ hφc hφU),
      h.integral_deriv_mul φ hφ hφc hφU, hQ.integral_deriv_mul φ hφ hφc hφU,
      sub_self]
  obtain ⟨d, hd⟩ := weakPrimitive_ae_constant hc hf hzero
  refine ⟨d, ?_⟩
  filter_upwards [hd] with x hx
  change r x - Q x = d at hx
  change r x = d + Q x
  linarith

/-- A function with a locally integrable weak derivative has a continuous
representative satisfying the same compact-test identity. -/
theorem HasWeakDerivOn.exists_continuous_representative_Ioo
    {a b c : ℝ} {r p : ℝ → ℝ} (h : HasWeakDerivOn (Ioo a b) r p)
    (hc : c ∈ Ioo a b) :
    ∃ R : ℝ → ℝ, ContinuousOn R (Ioo a b) ∧
      r =ᵐ[volume.restrict (Ioo a b)] R ∧ HasWeakDerivOn (Ioo a b) R p := by
  obtain ⟨d, hd⟩ := h.exists_integral_representative_Ioo hc
  exact ⟨fun x ↦ d + ∫ t in c..x, p t,
    continuousOn_const.add (weakPrimitive_continuousOn h.locallyIntegrable_deriv hc),
    hd, h.congr_ae hd Filter.EventuallyEq.rfl⟩

/-- A continuous function with a locally integrable weak derivative is
absolutely continuous on every compact subinterval of its open domain. -/
theorem HasWeakDerivOn.absolutelyContinuousOnInterval
    {a b u v : ℝ} {r p : ℝ → ℝ} (h : HasWeakDerivOn (Ioo a b) r p)
    (hr : ContinuousOn r (Ioo a b)) (hu : u ∈ Ioo a b) (hv : v ∈ Ioo a b) :
    AbsolutelyContinuousOnInterval r u v := by
  obtain ⟨d, hd⟩ := h.exists_integral_representative_Ioo hu
  have hR : ContinuousOn (fun x ↦ d + ∫ t in u..x, p t) (Ioo a b) :=
    continuousOn_const.add (weakPrimitive_continuousOn h.locallyIntegrable_deriv hu)
  have hEq := MeasureTheory.Measure.eqOn_Ioo_of_ae_eq volume hd hr hR
  have hConst : AbsolutelyContinuousOnInterval (fun _ : ℝ ↦ d) u v :=
    ((contDiff_const : ContDiff ℝ 1 (fun _ : ℝ ↦ d)).contDiffOn).absolutelyContinuousOnInterval
  have hAC : AbsolutelyContinuousOnInterval (fun x ↦ d + ∫ t in u..x, p t) u v :=
    hConst.fun_add (weakPrimitive_absolutelyContinuous h.locallyIntegrable_deriv hu hu hv)
  exact hAC.congr fun x hx ↦ (hEq (weakPrimitive_uIcc_subset_Ioo hu hv hx)).symm

/-- The pointwise fundamental theorem of calculus for a continuous weakly
differentiable representative on an open interval. -/
theorem HasWeakDerivOn.integral_eq_sub_of_continuousOn
    {a b x y : ℝ} {r p : ℝ → ℝ} (h : HasWeakDerivOn (Ioo a b) r p)
    (hr : ContinuousOn r (Ioo a b)) (hx : x ∈ Ioo a b) (hy : y ∈ Ioo a b) :
    (∫ t in x..y, p t) = r y - r x := by
  obtain ⟨d, hd⟩ := h.exists_integral_representative_Ioo hx
  have hR : ContinuousOn (fun z ↦ d + ∫ t in x..z, p t) (Ioo a b) :=
    continuousOn_const.add (weakPrimitive_continuousOn h.locallyIntegrable_deriv hx)
  have hEq := MeasureTheory.Measure.eqOn_Ioo_of_ae_eq volume hd hr hR
  rw [hEq hx, hEq hy]
  simp

/-- At every point where the weak derivative is continuous on the domain,
it is the actual derivative of the continuous representative. -/
theorem HasWeakDerivOn.hasDerivAt_of_continuousOn
    {a b x : ℝ} {r p : ℝ → ℝ} (h : HasWeakDerivOn (Ioo a b) r p)
    (hr : ContinuousOn r (Ioo a b)) (hp : ContinuousOn p (Ioo a b))
    (hx : x ∈ Ioo a b) : HasDerivAt r (p x) x := by
  have hpM : StronglyMeasurableAtFilter p (𝓝 x) volume :=
    ⟨Ioo a b, isOpen_Ioo.mem_nhds hx, h.locallyIntegrable_deriv.aestronglyMeasurable⟩
  have hD := (intervalIntegral.integral_hasDerivAt_right
    (weakPrimitive_intervalIntegrable h.locallyIntegrable_deriv hx hx) hpM
      (hp.continuousAt (isOpen_Ioo.mem_nhds hx))).const_add (r x)
  apply hD.congr_of_eventuallyEq
  filter_upwards [isOpen_Ioo.mem_nhds hx] with y hy
  have hxy := h.integral_eq_sub_of_continuousOn hr hx hy
  linarith

/-- A continuous weakly differentiable representative with continuous weak
derivative is C¹ on its open interval. -/
theorem HasWeakDerivOn.contDiffOn_one_of_continuousOn
    {a b : ℝ} {r p : ℝ → ℝ} (h : HasWeakDerivOn (Ioo a b) r p)
    (hr : ContinuousOn r (Ioo a b)) (hp : ContinuousOn p (Ioo a b)) :
    ContDiffOn ℝ 1 r (Ioo a b) := by
  have hd (x : ℝ) (hx : x ∈ Ioo a b) := h.hasDerivAt_of_continuousOn hr hp hx
  apply (contDiffOn_one_iff_derivWithin isOpen_Ioo.uniqueDiffOn).mpr
  refine ⟨fun x hx => (hd x hx).differentiableAt.differentiableWithinAt, ?_⟩
  apply hp.congr
  intro x hx
  exact (hd x hx).hasDerivWithinAt.derivWithin (isOpen_Ioo.uniqueDiffWithinAt hx)

/-- A continuous weakly differentiable representative has its stipulated weak
derivative as an actual derivative almost everywhere on the open interval. -/
theorem HasWeakDerivOn.ae_hasDerivAt_of_continuousOn
    {a b : ℝ} {r p : ℝ → ℝ} (h : HasWeakDerivOn (Ioo a b) r p)
    (hr : ContinuousOn r (Ioo a b)) :
    ∀ᵐ x ∂volume.restrict (Ioo a b), HasDerivAt r (p x) x := by
  have hRat : ∀ q : ℚ × ℚ, ∀ᵐ x ∂volume,
      a < (q.1 : ℝ) → (q.2 : ℝ) < b → x ∈ Ioo (q.1 : ℝ) (q.2 : ℝ) →
        HasDerivAt r (p x) x := by
    intro q
    by_cases ha : a < (q.1 : ℝ)
    · by_cases hb : (q.2 : ℝ) < b
      · by_cases hq : (q.1 : ℝ) < (q.2 : ℝ)
        · have hu : (q.1 : ℝ) ∈ Ioo a b := ⟨ha, hq.trans hb⟩
          have hv : (q.2 : ℝ) ∈ Ioo a b := ⟨ha.trans hq, hb⟩
          have hpI := weakPrimitive_intervalIntegrable h.locallyIntegrable_deriv hu hv
          filter_upwards [hpI.ae_hasDerivAt_integral] with x hx _ _ hxI
          have hxU : x ∈ Ioo a b := ⟨ha.trans hxI.1, hxI.2.trans hb⟩
          have hxC : x ∈ uIcc (q.1 : ℝ) (q.2 : ℝ) := by
            rw [uIcc_of_le hq.le]
            exact ⟨hxI.1.le, hxI.2.le⟩
          have hD := (hx hxC (q.1 : ℝ) (by simp)).const_add (r (q.1 : ℝ))
          apply hD.congr_of_eventuallyEq
          filter_upwards [isOpen_Ioo.mem_nhds hxU] with y hy
          have hxy := h.integral_eq_sub_of_continuousOn hr hu hy
          linarith
        · exact Filter.Eventually.of_forall fun x _ _ hx ↦
            (hq (hx.1.trans hx.2)).elim
      · exact Filter.Eventually.of_forall fun _ _ h ↦ (hb h).elim
    · exact Filter.Eventually.of_forall fun _ h ↦ (ha h).elim
  apply (ae_restrict_iff' measurableSet_Ioo).2
  filter_upwards [ae_all_iff.2 hRat] with x hx
  intro hxI
  obtain ⟨u, hau, hux⟩ := exists_rat_btwn hxI.1
  obtain ⟨v, hxv, hvb⟩ := exists_rat_btwn hxI.2
  exact hx (u, v) hau hvb ⟨hux, hxv⟩

end RicciFlowSharpEstimate.Analysis
