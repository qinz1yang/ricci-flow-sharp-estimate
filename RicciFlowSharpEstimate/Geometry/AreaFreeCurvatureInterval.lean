/-
Copyright (c) 2026 Ziyang Qin. All rights reserved.
No license is granted by this file.
Authors: Ziyang Qin
-/
import RicciFlowSharpEstimate.Geometry.RecoverableAreaRegularity
import RicciFlowSharpEstimate.Geometry.RecoverableProbeSign
import RicciFlowSharpEstimate.Geometry.WeakProbeStrongMaximum
import RicciFlowSharpEstimate.Analysis.ParabolicEnergyBoundary
import RicciFlowSharpEstimate.Geometry.AreaCurvatureControl

/-!
# A genuine free curvature interval at a zero-action joint minimum

Actual curvature clamp regularity and true squared-probe flux traces rule out
curvature confined to its box endpoints. The conclusion concerns the original
curvature almost everywhere and the same physical probe. It supplies feasible
local variation space, but does not claim a negative direction or source sign.
-/

noncomputable section
namespace RicciFlowSharpEstimate.Geometry.AreaProfile
open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff
local notation "areaμ" => volume.restrict (Ioo (0 : ℝ) 1)

private theorem actual_warp_pos
    {C : ℝ} {K r p z : ℝ → ℝ} (hC : 1 ≤ C)
    (h : IsRecoverableAreaCompetitor C K r p z)
    (x : ℝ) (hx : x ∈ Ioo (0 : ℝ) 1) : 0 < warp K x := by
  have hCpos : 0 < C := zero_lt_one.trans_le hC
  exact (mul_pos (mul_pos (by positivity : (0 : ℝ) < 2 / C) hx.1)
    (sub_pos.mpr hx.2)).trans_le
    ((h.geometry_bounds hC).2.2.1 x ⟨hx.1.le, hx.2.le⟩).1

private theorem operator_energy_integrable
    {C : ℝ} {K r p z : ℝ → ℝ} (hC : 1 ≤ C)
    (h : IsRecoverableAreaCompetitor C K r p z) :
    Integrable (fun x => warp K x * weakMeridionalOperator K r p z x ^ 2) areaμ := by
  have hCpos : 0 < C := zero_lt_one.trans_le hC
  have hg := h.geometry_bounds hC
  have hw := h.primitive_weak_derivatives hC
  have hKbox : ∀ᵐ x ∂areaμ, 0 ≤ K x ∧ K x ≤ 2 * C := by
    filter_upwards [hg.2.2.2.2] with x hx
    exact ⟨(by positivity : (0 : ℝ) ≤ 2 / C).trans hx.1, hx.2⟩
  have hfbox : ∀ᵐ x ∂areaμ,
      0 ≤ warp K x ∧ warp K x ≤ (2 * C) * (x * (1 - x)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
    refine ⟨(actual_warp_pos hC h x hx).le, ?_⟩
    simpa only [mul_assoc] using (hg.2.2.1 x ⟨hx.1.le, hx.2.le⟩).2.1
  have hbbox : ∀ᵐ x ∂areaμ, |warpSlope K x| ≤ 2 := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
    exact (hg.2.2.1 x ⟨hx.1.le, hx.2.le⟩).2.2
  have hQ := (memLp_weak_operator_and_potential_of_warp_bounds K r p z (2 * C)
    h.2.1 (by positivity) h.1.aestronglyMeasurable
    hw.1.locallyIntegrable.aestronglyMeasurable
    hw.2.locallyIntegrable.aestronglyMeasurable hKbox hfbox hbbox).1
  apply hQ.integrable_sq.congr
  filter_upwards [hfbox] with x hx
  rw [mul_pow, Real.sq_sqrt hx.1]

private theorem operator_energy_pos
    {C : ℝ} {K r p z : ℝ → ℝ} (hC : 1 ≤ C)
    (h : IsRecoverableAreaCompetitor C K r p z)
    (hr : ContinuousOn r (Ioo (0 : ℝ) 1))
    (hp : ContinuousOn p (Ioo (0 : ℝ) 1)) :
    0 < ∫ x, warp K x * weakMeridionalOperator K r p z x ^ 2 ∂areaμ := by
  have hnonneg : ∀ᵐ x ∂areaμ,
      0 ≤ warp K x * weakMeridionalOperator K r p z x ^ 2 := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
    exact mul_nonneg (actual_warp_pos hC h x hx).le (sq_nonneg _)
  by_contra hn
  have hzero : (∫ x, warp K x * weakMeridionalOperator K r p z x ^ 2 ∂areaμ) = 0 :=
    le_antisymm (le_of_not_gt hn) (integral_nonneg_of_ae hnonneg)
  have hzeroae := (integral_eq_zero_iff_of_nonneg_ae hnonneg
    (operator_energy_integrable hC h)).mp hzero
  have hqzero : ∀ᵐ x ∂areaμ, weakMeridionalOperator K r p z x = 0 := by
    filter_upwards [hzeroae, ae_restrict_mem measurableSet_Ioo] with x hx hxI
    have hsq : weakMeridionalOperator K r p z x ^ 2 = 0 :=
      (mul_eq_zero.mp hx).resolve_left (actual_warp_pos hC h x hxI).ne'
    exact (sq_eq_zero_iff).mp hsq
  have hpos := h.pos_of_weakMeridionalOperator_nonpos hC hr hp
    (hqzero.mono fun _ hx => hx.le)
  have hqneg : ∀ᵐ x ∂areaμ, weakMeridionalOperator K (-r) (-p) (-z) x ≤ 0 := by
    rw [weakMeridionalOperator_neg]
    filter_upwards [hqzero] with x hx
    simp only [Pi.neg_apply, hx, neg_zero, le_refl]
  have hneg := h.neg_probe.pos_of_weakMeridionalOperator_nonpos hC hr.neg hp.neg hqneg
  have hm : (1 / 2 : ℝ) ∈ Ioo (0 : ℝ) 1 := by norm_num
  have hp0 := hpos (1 / 2) hm
  have hn0 := hneg (1 / 2) hm
  change 0 < -r (1 / 2) at hn0
  linarith

private theorem squared_probe_boundary
    {C : ℝ} {K r p z : ℝ → ℝ} (hC : 1 ≤ C)
    (h : IsRecoverableAreaCompetitor C K r p z)
    (hr : ContinuousOn r (Ioo (0 : ℝ) 1)) :
    AbsolutelyContinuousOnInterval (fun x => warp K x * r x ^ 2) 0 1 ∧
      warp K 0 * r 0 ^ 2 = 0 ∧ warp K 1 * r 1 ^ 2 = 0 := by
  have hCpos : 0 < C := zero_lt_one.trans_le hC
  have hg := h.geometry_bounds hC
  have hfbox : ∀ x ∈ Icc (0 : ℝ) 1, |warp K x| ≤ (2 * C) * (x * (1 - x)) := by
    intro x hx
    have hb := hg.2.2.1 x hx
    have hf0 : 0 ≤ warp K x :=
      (mul_nonneg (mul_nonneg (by positivity : (0 : ℝ) ≤ 2 / C) hx.1)
        (sub_nonneg.mpr hx.2)).trans hb.1
    simpa only [abs_of_nonneg hf0, mul_assoc] using hb.2.1
  have hbb : ∀ᵐ x ∂areaμ, |warpSlope K x| ≤ 2 * C := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
    exact ((hg.2.2.1 x ⟨hx.1.le, hx.2.le⟩).2.2).trans (by linarith)
  have hd := h.2.1.weakDeriv.absolutelyContinuous_mul_sq_of_parabolic_bounds
    (h.primitive_weak_derivatives hC).1 hr (hg.1.mono Ioo_subset_Icc_self)
    h.2.1.memLp h.2.1.memLp_weighted_deriv hfbox hbb
  exact ⟨hd.1, hd.2.1, hd.2.2.1⟩

private theorem two_value_derivative {F : ℝ → ℝ} {s : Set ℝ} {x lo hi : ℝ}
    (hlohi : lo < hi) (hs : s ∈ 𝓝 x) (hF : ContinuousOn F s)
    (hvals : ∀ y ∈ s, F y = lo ∨ F y = hi) : HasDerivAt F 0 x := by
  have hFc := hF.continuousAt hs
  have hx : x ∈ s := mem_of_mem_nhds hs
  apply (hasDerivAt_const x (F x)).congr_of_eventuallyEq
  rcases hvals x hx with hxlo | hxhi
  · have hn : ∀ᶠ y in 𝓝 x, F y < hi := hFc (Iio_mem_nhds (hxlo ▸ hlohi))
    filter_upwards [hs, hn] with y hy hyhi
    rcases hvals y hy with hylo | hyhi'
    · exact hylo.trans hxlo.symm
    · exact False.elim ((ne_of_lt hyhi) hyhi')
  · have hn : ∀ᶠ y in 𝓝 x, lo < F y := hFc (Ioi_mem_nhds (hxhi ▸ hlohi))
    filter_upwards [hs, hn] with y hy hylo
    rcases hvals y hy with hylo' | hyhi
    · exact False.elim ((ne_of_gt hylo) hylo')
    · exact hyhi.trans hxhi.symm

private theorem nonzero_probe_nhds {r : ℝ → ℝ}
    (hr : ContinuousOn r (Ioo (0 : ℝ) 1)) {x : ℝ}
    (hx : x ∈ Ioo (0 : ℝ) 1) (hrx : r x ≠ 0) :
    {y | y ∈ Ioo (0 : ℝ) 1 ∧ r y ≠ 0} ∈ 𝓝 x := by
  have hI := isOpen_Ioo.mem_nhds hx
  have hne : ∀ᶠ y in 𝓝 x, r y ≠ 0 :=
    (hr.continuousAt hI).eventually (compl_singleton_mem_nhds hrx)
  filter_upwards [hI, hne] with y hy hny
  exact ⟨hy, hny⟩

private theorem free_interval_subset {a b : ℝ}
    (ha : a ∈ Ioo (0 : ℝ) 1) (hb : b ∈ Ioo (0 : ℝ) 1) :
    uIcc a b ⊆ Ioo (0 : ℝ) 1 := by
  intro x hx
  rcases mem_uIcc.mp hx with hx | hx
  · exact ⟨ha.1.trans_le hx.1, hx.2.trans_lt hb.2⟩
  · exact ⟨hb.1.trans_le hx.1, hx.2.trans_lt ha.2⟩

private theorem obstacle_flux_derivative
    {C κ Λ : ℝ} {K Kc r p z : ℝ → ℝ} (hC : 1 ≤ C)
    (h : IsRecoverableAreaCompetitor C K r p z)
    (hr : ContinuousOn r (Ioo (0 : ℝ) 1))
    (hp : ContinuousOn p (Ioo (0 : ℝ) 1))
    (hκ : 0 < κ) (hκΛ : κ < Λ) (hKeq : Kc =ᵐ[areaμ] K)
    (hbox : ∀ x ∈ Ioo (0 : ℝ) 1, κ ≤ Kc x ∧ Kc x ≤ Λ)
    (hKc : ContinuousOn Kc {x | x ∈ Ioo (0 : ℝ) 1 ∧ r x ≠ 0})
    (hvals : ∀ x ∈ Ioo (0 : ℝ) 1, r x ≠ 0 → Kc x = κ ∨ Kc x = Λ)
    (hTac : ∀ a ∈ Ioo (0 : ℝ) 1, ∀ b ∈ Ioo (0 : ℝ) 1,
      AbsolutelyContinuousOnInterval (fun x => Kc x * warp K x * r x ^ 2) a b)
    (a : ℝ) (ha : a ∈ Ioo (0 : ℝ) 1) (b : ℝ) (hb : b ∈ Ioo (0 : ℝ) 1) :
    ∀ᵐ x : ℝ, x ∈ uIcc a b →
      HasDerivAt (fun x => Kc x * warp K x * r x ^ 2 * warpSlope K x / 2)
        (warp K x * weakMeridionalOperator K r p z x ^ 2 -
          meridionalActionDensity (warp K x) (warpSlope K x) (K x) (r x) (p x) (z x)) x := by
  have hreg := h.primitive_local_regularity hC
  filter_upwards [(hTac a ha b hb).ae_differentiableAt,
    ae_imp_of_ae_restrict hKeq, ae_imp_of_ae_restrict hreg.2.2] with x hTx hKx hbx hx
  have hxI := free_interval_subset ha hb hx
  have heq := hKx hxI
  have hdB := hbx hxI
  have hdF := hreg.1 x hxI
  have hdR := h.2.1.weakDeriv.hasDerivAt_of_continuousOn hr hp hxI
  by_cases hrx : r x = 0
  · have hminT : IsLocalMin (fun x => Kc x * warp K x * r x ^ 2) x := by
      filter_upwards [isOpen_Ioo.mem_nhds hxI] with y hy
      simp only [hrx, zero_pow (by norm_num : 2 ≠ 0), mul_zero]
      exact mul_nonneg (mul_nonneg (hκ.le.trans (hbox y hy).1)
        (actual_warp_pos hC h y hy).le) (sq_nonneg _)
    have hdT : HasDerivAt (fun x => Kc x * warp K x * r x ^ 2) 0 x := by
      simpa only [hminT.deriv_eq_zero] using (hTx hx).hasDerivAt
    convert (hdT.mul hdB).div_const 2 using 1
    simp [hrx, meridionalActionDensity, weakMeridionalOperator]
  · have hdK := two_value_derivative hκΛ (nonzero_probe_nhds hr hxI hrx) hKc
      (fun y hy => hvals y hy.1 hy.2)
    convert (((hdK.mul hdF).mul (hdR.pow 2)).mul hdB).div_const 2 using 1
    simp only [Pi.mul_apply, Pi.pow_apply, heq, meridionalActionDensity, weakMeridionalOperator]
    ring

private theorem flux_continuous_on {F E : ℝ → ℝ} {M : ℝ}
    (hFC : ContinuousOn F (Ioo (0 : ℝ) 1))
    (hEC : ContinuousOn E (Icc (0 : ℝ) 1))
    (hF0 : F 0 = 0) (hF1 : F 1 = 0) (hE0 : E 0 = 0) (hE1 : E 1 = 0)
    (hbound : ∀ x ∈ Icc (0 : ℝ) 1, ‖F x‖ ≤ M * E x) :
    ContinuousOn F (Icc (0 : ℝ) 1) := by
  have hEnd (a : ℝ) (ha : a ∈ Icc (0 : ℝ) 1) (hFa : F a = 0) (hEa : E a = 0) :
      ContinuousWithinAt F (Icc (0 : ℝ) 1) a := by
    change Tendsto F (𝓝[Icc (0 : ℝ) 1] a) (𝓝 (F a))
    rw [hFa]
    apply squeeze_zero_norm'
    · filter_upwards [self_mem_nhdsWithin] with x hx
      exact hbound x hx
    · simpa only [hEa, mul_zero] using ((hEC a ha).const_mul M).tendsto
  intro x hx
  by_cases hx0 : x = 0
  · subst x
    exact hEnd 0 (by norm_num) hF0 hE0
  by_cases hx1 : x = 1
  · subst x
    exact hEnd 1 (by norm_num) hF1 hE1
  have hxI : x ∈ Ioo (0 : ℝ) 1 :=
    ⟨lt_of_le_of_ne hx.1 (Ne.symm hx0), lt_of_le_of_ne hx.2 hx1⟩
  exact (hFC.continuousAt (isOpen_Ioo.mem_nhds hxI)).continuousWithinAt

private theorem obstacle_flux_continuous
    {C κ Λ : ℝ} {K Kc r p z : ℝ → ℝ} (hC : 1 ≤ C)
    (h : IsRecoverableAreaCompetitor C K r p z)
    (hr : ContinuousOn r (Ioo (0 : ℝ) 1)) (hκ : 0 < κ)
    (hbox : ∀ x ∈ Ioo (0 : ℝ) 1, κ ≤ Kc x ∧ Kc x ≤ Λ)
    (hTac : ∀ a ∈ Ioo (0 : ℝ) 1, ∀ b ∈ Ioo (0 : ℝ) 1,
      AbsolutelyContinuousOnInterval (fun x => Kc x * warp K x * r x ^ 2) a b) :
    ContinuousOn (fun x => Kc x * warp K x * r x ^ 2 * warpSlope K x / 2)
      (Icc (0 : ℝ) 1) := by
  have hg := h.geometry_bounds hC
  have he := squared_probe_boundary hC h hr
  have hF0 : Kc 0 * warp K 0 * r 0 ^ 2 * warpSlope K 0 / 2 = 0 := by
    have he0 := he.2.1
    calc
      _ = Kc 0 * (warp K 0 * r 0 ^ 2) * warpSlope K 0 / 2 := by ring
      _ = 0 := by rw [he0]; ring
  have hF1 : Kc 1 * warp K 1 * r 1 ^ 2 * warpSlope K 1 / 2 = 0 := by
    have he1 := he.2.2
    calc
      _ = Kc 1 * (warp K 1 * r 1 ^ 2) * warpSlope K 1 / 2 := by ring
      _ = 0 := by rw [he1]; ring
  refine flux_continuous_on (M := Λ) (E := fun x => warp K x * r x ^ 2)
    ?_ (by simpa only [uIcc_of_le zero_le_one] using he.1.continuousOn) hF0 hF1 he.2.1 he.2.2 ?_
  · intro x hx
    let a := x / 2
    let b := (x + 1) / 2
    have ha : a ∈ Ioo (0 : ℝ) 1 := by dsimp [a]; constructor <;> linarith [hx.1, hx.2]
    have hb : b ∈ Ioo (0 : ℝ) 1 := by dsimp [b]; constructor <;> linarith [hx.1, hx.2]
    have hax : a < x := by dsimp [a]; linarith [hx.1]
    have hxb : x < b := by dsimp [b]; linarith [hx.2]
    have hnb : uIcc a b ∈ 𝓝 x := by
      rw [uIcc_of_le (hax.trans hxb).le]
      exact Icc_mem_nhds hax hxb
    have hbac := (h.primitive_local_regularity hC).2.1 a ha b hb
    have hAC := ((hTac a ha b hb).fun_mul hbac).const_mul (1 / 2 : ℝ)
    have hCT := hAC.continuousOn.continuousAt hnb
    convert hCT.continuousWithinAt using 1
    ext y
    simp only [div_eq_mul_inv]
    ring
  · intro x hx
    by_cases hx0 : x = 0
    · subst x
      simp only [hF0, norm_zero, he.2.1, mul_zero, le_refl]
    by_cases hx1 : x = 1
    · subst x
      simp only [hF1, norm_zero, he.2.2, mul_zero, le_refl]
    have hxI : x ∈ Ioo (0 : ℝ) 1 :=
      ⟨lt_of_le_of_ne hx.1 (Ne.symm hx0), lt_of_le_of_ne hx.2 hx1⟩
    have hf0 := (actual_warp_pos hC h x hxI).le
    have hK0 := hκ.le.trans (hbox x hxI).1
    have hEn : 0 ≤ warp K x * r x ^ 2 := mul_nonneg hf0 (sq_nonneg _)
    have hbabs := (hg.2.2.1 x hx).2.2
    rw [Real.norm_eq_abs, abs_div, abs_mul, abs_mul, abs_mul,
      abs_of_nonneg hK0, abs_of_nonneg hf0, abs_of_nonneg (sq_nonneg _)]
    rw [abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 2)).mpr
    calc
      Kc x * warp K x * r x ^ 2 * |warpSlope K x| ≤
          Kc x * warp K x * r x ^ 2 * 2 :=
        mul_le_mul_of_nonneg_left hbabs (by positivity)
      _ ≤ Λ * (warp K x * r x ^ 2) * 2 := by
        nlinarith only [mul_le_mul_of_nonneg_right (hbox x hxI).2 hEn]

private theorem integral_eq_zero_of_local_ac_and_deriv_Ioo
    {F g : ℝ → ℝ}
    (hFC : ContinuousOn F (Icc (0 : ℝ) 1)) (hF0 : F 0 = 0) (hF1 : F 1 = 0)
    (hg : Integrable g (volume.restrict (Ioo (0 : ℝ) 1)))
    (hFac : ∀ a ∈ Ioo (0 : ℝ) 1, ∀ b ∈ Ioo (0 : ℝ) 1,
      AbsolutelyContinuousOnInterval F a b)
    (hD : ∀ a ∈ Ioo (0 : ℝ) 1, ∀ b ∈ Ioo (0 : ℝ) 1,
      ∀ᵐ x ∂volume, x ∈ uIcc a b → HasDerivAt F (g x) x) :
    (∫ x in Ioo (0 : ℝ) 1, g x) = 0 := by
  let c : ℝ := 1 / 2
  have hc : c ∈ Ioo (0 : ℝ) 1 := by norm_num [c]
  have hgI : IntervalIntegrable g volume 0 1 :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le zero_le_one).mpr hg
  let G : ℝ → ℝ := fun x => F c + ∫ t in c..x, g t
  have hGAC : AbsolutelyContinuousOnInterval G 0 1 := by
    have hConst : AbsolutelyContinuousOnInterval (fun _ : ℝ => F c) 0 1 :=
      ((contDiff_const : ContDiff ℝ 1 (fun _ : ℝ => F c)).contDiffOn).absolutelyContinuousOnInterval
    exact hConst.fun_add (hgI.absolutelyContinuousOnInterval_intervalIntegral (by norm_num [c]))
  have hEq (x : ℝ) (hx : x ∈ Ioo (0 : ℝ) 1) : G x = F x := by
    have hFTC := (hFac c hc x hx).integral_deriv_eq_sub
    have hInt : (∫ t in c..x, deriv F t) = ∫ t in c..x, g t := by
      apply intervalIntegral.integral_congr_ae
      filter_upwards [hD c hc x hx] with t ht htI
      exact (ht (uIoc_subset_uIcc htI)).deriv
    rw [hInt] at hFTC
    dsimp only [G]
    linarith
  have hGC : ContinuousOn G (Icc (0 : ℝ) 1) := by
    simpa only [uIcc_of_le zero_le_one] using hGAC.continuousOn
  have hEqClosed : EqOn G F (Icc (0 : ℝ) 1) := by
    have hsub : Ioo (0 : ℝ) 1 ⊆ {x ∈ Icc (0 : ℝ) 1 | G x = F x} := by
      intro x hx
      exact ⟨⟨hx.1.le, hx.2.le⟩, hEq x hx⟩
    have hcl := closure_minimal hsub (isClosed_Icc.isClosed_eq hGC hFC)
    rw [closure_Ioo zero_lt_one.ne] at hcl
    intro x hx
    exact (hcl hx).2
  have hG0 : G 0 = 0 := (hEqClosed (by norm_num)).trans hF0
  have hG1 : G 1 = 0 := (hEqClosed (by norm_num)).trans hF1
  have hc1 : IntervalIntegrable g volume c 1 := by
    apply hgI.mono_set
    rw [uIcc_of_le hc.2.le, uIcc_of_le zero_le_one]
    exact Icc_subset_Icc hc.1.le le_rfl
  have hc0 : IntervalIntegrable g volume c 0 := by
    apply hgI.mono_set
    rw [uIcc_of_ge hc.1.le, uIcc_of_le zero_le_one]
    exact Icc_subset_Icc le_rfl hc.2.le
  have hsub := intervalIntegral.integral_interval_sub_left hc1 hc0
  have hzero : (∫ x in (0 : ℝ)..1, g x) = 0 := by
    rw [← hsub]
    dsimp only [G] at hG0 hG1
    linarith
  simpa only [intervalIntegral.integral_of_le zero_le_one,
    integral_Ioc_eq_integral_Ioo] using hzero


private theorem exists_strict_curvature_point
    {C κ Λ : ℝ} {K Kc r p z : ℝ → ℝ} (hC : 1 ≤ C)
    (h : IsRecoverableAreaCompetitor C K r p z)
    (hr : ContinuousOn r (Ioo (0 : ℝ) 1))
    (hp : ContinuousOn p (Ioo (0 : ℝ) 1))
    (hzero : weakMeridionalAction K r p z = 0)
    (hκ : 0 < κ) (hκΛ : κ < Λ) (hKeq : Kc =ᵐ[areaμ] K)
    (hbox : ∀ x ∈ Ioo (0 : ℝ) 1, κ ≤ Kc x ∧ Kc x ≤ Λ)
    (hKc : ContinuousOn Kc {x | x ∈ Ioo (0 : ℝ) 1 ∧ r x ≠ 0})
    (hTac : ∀ a ∈ Ioo (0 : ℝ) 1, ∀ b ∈ Ioo (0 : ℝ) 1,
      AbsolutelyContinuousOnInterval (fun x => Kc x * warp K x * r x ^ 2) a b) :
    ∃ x ∈ Ioo (0 : ℝ) 1, r x ≠ 0 ∧ κ < Kc x ∧ Kc x < Λ := by
  by_contra hn
  have hvals (x : ℝ) (hx : x ∈ Ioo (0 : ℝ) 1) (hrx : r x ≠ 0) :
      Kc x = κ ∨ Kc x = Λ := by
    by_cases hk : Kc x = κ
    · exact Or.inl hk
    apply Or.inr
    apply le_antisymm (hbox x hx).2
    by_contra hhi
    exact hn ⟨x, hx, hrx, lt_of_le_of_ne (hbox x hx).1 (Ne.symm hk), lt_of_not_ge hhi⟩
  let F := fun x => Kc x * warp K x * r x ^ 2 * warpSlope K x / 2
  let g := fun x => warp K x * weakMeridionalOperator K r p z x ^ 2 -
    meridionalActionDensity (warp K x) (warpSlope K x) (K x) (r x) (p x) (z x)
  have hFC : ContinuousOn F (Icc (0 : ℝ) 1) :=
    obstacle_flux_continuous hC h hr hκ hbox hTac
  have hEnd := (h.geometry_bounds hC).2.2.2.1
  have hF0 : F 0 = 0 := by simp only [F, hEnd.1, mul_zero, zero_mul, zero_div]
  have hF1 : F 1 = 0 := by simp only [F, hEnd.2.1, mul_zero, zero_mul, zero_div]
  have hQi := operator_energy_integrable hC h
  have hDi := (h.exists_action_recovery hC).1
  have hgi : Integrable g areaμ := hQi.sub hDi
  have hFac (a : ℝ) (ha : a ∈ Ioo (0 : ℝ) 1) (b : ℝ) (hb : b ∈ Ioo (0 : ℝ) 1) :
      AbsolutelyContinuousOnInterval F a b := by
    have hAC := ((hTac a ha b hb).fun_mul
      ((h.primitive_local_regularity hC).2.1 a ha b hb)).const_mul (1 / 2 : ℝ)
    convert hAC using 1
    ext x
    dsimp only [F]
    ring
  have hD (a : ℝ) (ha : a ∈ Ioo (0 : ℝ) 1) (b : ℝ) (hb : b ∈ Ioo (0 : ℝ) 1) :
      ∀ᵐ x : ℝ, x ∈ uIcc a b → HasDerivAt F (g x) x :=
    obstacle_flux_derivative hC h hr hp hκ hκΛ hKeq hbox hKc hvals hTac a ha b hb
  have hInt := integral_eq_zero_of_local_ac_and_deriv_Ioo hFC hF0 hF1 hgi hFac hD
  change (∫ x, (warp K x * weakMeridionalOperator K r p z x ^ 2 -
    meridionalActionDensity (warp K x) (warpSlope K x) (K x) (r x) (p x) (z x)) ∂areaμ) = 0 at hInt
  rw [integral_sub hQi hDi] at hInt
  have hA : (∫ x, meridionalActionDensity (warp K x) (warpSlope K x)
      (K x) (r x) (p x) (z x) ∂areaμ) = 0 := by
    simpa only [weakMeridionalAction, intervalIntegral.integral_of_le zero_le_one,
      integral_Ioc_eq_integral_Ioo] using hzero
  rw [hA, sub_zero] at hInt
  exact (operator_energy_pos hC h hr hp).ne' hInt

private theorem exists_closed_interval_uniform_margins
    (f r k : ℝ → ℝ) (lo hi x0 : ℝ)
    (hf : ContinuousOn f (Ioo (0 : ℝ) 1))
    (hr : ContinuousOn r (Ioo (0 : ℝ) 1))
    (hk : ContinuousOn k {x : ℝ | x ∈ Ioo (0 : ℝ) 1 ∧ r x ≠ 0})
    (hx0 : x0 ∈ Ioo (0 : ℝ) 1) (hf0 : 0 < f x0) (hr0 : r x0 ≠ 0)
    (hlo : lo < k x0) (hhi : k x0 < hi) :
    ∃ a b η : ℝ, 0 < a ∧ a < b ∧ b < 1 ∧ 0 < η ∧
      ∀ x ∈ Icc a b, η ≤ f x ∧ η ≤ |r x| ∧ lo + η ≤ k x ∧ k x ≤ hi - η := by
  let m := min (min (f x0) |r x0|) (min (k x0 - lo) (hi - k x0))
  let η := m / 2
  have hm : 0 < m :=
    lt_min (lt_min hf0 (abs_pos.mpr hr0)) (lt_min (sub_pos.mpr hlo) (sub_pos.mpr hhi))
  have hη : 0 < η := div_pos hm zero_lt_two
  have hηm : η < m := by dsimp [η]; linarith only [hm]
  have hmf : m ≤ f x0 := (min_le_left _ _).trans (min_le_left _ _)
  have hmr : m ≤ |r x0| := (min_le_left _ _).trans (min_le_right _ _)
  have hml : m ≤ k x0 - lo := (min_le_right _ _).trans (min_le_left _ _)
  have hmh : m ≤ hi - k x0 := (min_le_right _ _).trans (min_le_right _ _)
  have hfAt : ContinuousAt f x0 := hf.continuousAt (isOpen_Ioo.mem_nhds hx0)
  have hrAt : ContinuousAt r x0 := hr.continuousAt (isOpen_Ioo.mem_nhds hx0)
  have hFevent : ∀ᶠ x in 𝓝 x0, η < f x :=
    hfAt.eventually (eventually_gt_nhds (hηm.trans_le hmf))
  have hRevent : ∀ᶠ x in 𝓝 x0, η < |r x| :=
    hrAt.abs.eventually (eventually_gt_nhds (hηm.trans_le hmr))
  have hDomain : {x : ℝ | x ∈ Ioo (0 : ℝ) 1 ∧ r x ≠ 0} ∈ 𝓝 x0 := by
    filter_upwards [isOpen_Ioo.mem_nhds hx0, hRevent] with x hx hxr
    exact ⟨hx, abs_pos.mp (hη.trans hxr)⟩
  have hkAt : ContinuousAt k x0 := hk.continuousAt hDomain
  have hLower : lo + η < k x0 := by linarith only [hηm.trans_le hml]
  have hUpper : k x0 < hi - η := by linarith only [hηm.trans_le hmh]
  have hLevent : ∀ᶠ x in 𝓝 x0, lo + η < k x := hkAt.eventually (eventually_gt_nhds hLower)
  have hHevent : ∀ᶠ x in 𝓝 x0, k x < hi - η := hkAt.eventually (eventually_lt_nhds hUpper)
  have hN : ∀ᶠ x in 𝓝 x0,
      x ∈ Ioo (0 : ℝ) 1 ∧ η < f x ∧ η < |r x| ∧ lo + η < k x ∧ k x < hi - η := by
    filter_upwards [isOpen_Ioo.mem_nhds hx0, hFevent, hRevent, hLevent, hHevent]
      with x hx hfx hrx hlx hhx
    exact ⟨hx, hfx, hrx, hlx, hhx⟩
  obtain ⟨δ, hδ, hBall⟩ := Metric.mem_nhds_iff.mp hN
  let a := x0 - δ / 2
  let b := x0 + δ / 2
  have hab : a < b := by dsimp [a, b]; linarith only [hδ]
  have hWithin (x : ℝ) (hx : x ∈ Icc a b) : x ∈ Metric.ball x0 δ := by
    rw [Metric.mem_ball, Real.dist_eq]
    apply abs_lt.mpr
    constructor <;> dsimp [a, b] at hx <;> linarith only [hx.1, hx.2, hδ]
  have hA := hBall (hWithin a ⟨le_rfl, hab.le⟩)
  have hB := hBall (hWithin b ⟨hab.le, le_rfl⟩)
  refine ⟨a, b, η, hA.1.1, hab, hB.1.2, hη, ?_⟩
  intro x hx
  have h := hBall (hWithin x hx)
  exact ⟨h.2.1.le, h.2.2.1.le, h.2.2.2.1.le, h.2.2.2.2.le⟩


/-- Every actual zero-action joint minimum admits a nondegenerate compact
interior interval on which its original curvature stays uniformly inside one
of its original admissible ratio boxes and its actual probe stays away from
zero. No free region, curvature derivative, or operator sign is assumed. -/
theorem IsRecoverableAreaCompetitor.exists_free_curvature_interval
    {C : ℝ} {K r p z : ℝ → ℝ} (hC : 1 < C)
    (h : IsRecoverableAreaCompetitor C K r p z)
    (hr : ContinuousOn r (Ioo (0 : ℝ) 1))
    (hp : ContinuousOn p (Ioo (0 : ℝ) 1))
    (hzero : weakMeridionalAction K r p z = 0)
    (hmin : ∀ K' r' p' z' : ℝ → ℝ, IsRecoverableAreaCompetitor C K' r' p' z' →
      weakMeridionalAction K r p z ≤ weakMeridionalAction K' r' p' z') :
    ∃ κ Λ a b η : ℝ, 0 < κ ∧ κ < 2 ∧ 2 < Λ ∧ Λ / κ ≤ C ∧
      (∀ᵐ x ∂areaμ, κ ≤ K x ∧ K x ≤ Λ) ∧
      0 < a ∧ a < b ∧ b < 1 ∧ 0 < η ∧
      (∀ x ∈ Icc a b, η ≤ warp K x ∧ η ≤ |r x|) ∧
      (∀ᵐ x ∂volume.restrict (Icc a b), κ + η ≤ K x ∧ K x ≤ Λ - η) := by
  obtain ⟨κ, Λ, Kc, hκ, hκ2, h2Λ, hratio, hKeq, hbox, hKc, _hKac, hTac⟩ :=
    h.exists_regular_curvature_representative hC hr hp hmin
  obtain ⟨x0, hx0, hr0, hlo, hhi⟩ :=
    exists_strict_curvature_point hC.le h hr hp hzero hκ (hκ2.trans h2Λ) hKeq hbox hKc hTac
  obtain ⟨a, b, η, ha, hab, hb, hη, hmargin⟩ :=
    exists_closed_interval_uniform_margins (warp K) r Kc κ Λ x0
      ((h.geometry_bounds hC.le).1.mono Ioo_subset_Icc_self) hr hKc hx0
      (actual_warp_pos hC.le h x0 hx0) hr0 hlo hhi
  refine ⟨κ, Λ, a, b, η, hκ, hκ2, h2Λ, hratio, ?_, ha, hab, hb, hη, ?_, ?_⟩
  · filter_upwards [hKeq, ae_restrict_mem measurableSet_Ioo] with x hx hxI
    simpa only [hx] using hbox x hxI
  · intro x hx
    exact ⟨(hmargin x hx).1, (hmargin x hx).2.1⟩
  · have hsub : Icc a b ⊆ Ioo (0 : ℝ) 1 := by
      intro x hx
      exact ⟨ha.trans_le hx.1, hx.2.trans_lt hb⟩
    have heq : Kc =ᵐ[volume.restrict (Icc a b)] K :=
      hKeq.filter_mono (ae_mono (Measure.restrict_mono hsub le_rfl))
    filter_upwards [heq, ae_restrict_mem measurableSet_Icc] with x hx hxI
    simpa only [hx] using (hmargin x hxI).2.2

end RicciFlowSharpEstimate.Geometry.AreaProfile
