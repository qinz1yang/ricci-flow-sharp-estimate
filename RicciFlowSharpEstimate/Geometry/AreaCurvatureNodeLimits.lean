/-
Copyright (c) 2026 Ziyang Qin. All rights reserved.
No license is granted by this file.
Authors: Ziyang Qin
-/
import RicciFlowSharpEstimate.Analysis.ClampedNodeLimits
import RicciFlowSharpEstimate.Geometry.WeakCurvatureAdjointRegularity
import RicciFlowSharpEstimate.Geometry.WeakProbeSimpleZeros
import RicciFlowSharpEstimate.Geometry.AreaScaleBalancedMultiplier
import Mathlib.Analysis.Asymptotics.Lemmas

/-! # The actual scale-balanced curvature clamp at every interior node -/

noncomputable section
namespace RicciFlowSharpEstimate.Geometry.AreaProfile
open Set MeasureTheory Filter Topology
local notation "areaμ" => volume.restrict (Ioo (0 : ℝ) 1)

private theorem clamp_of_complementarity (lo hi k c H : ℝ)
    (hlohi : lo < hi) (hc : 0 < c) (hbox : lo ≤ k ∧ k ≤ hi)
    (hs : (lo < k → c * k + H ≤ 0) ∧ (k < hi → 0 ≤ c * k + H)) :
    max lo (min hi (-H / c)) = k := by
  by_cases hklo : k = lo
  · subst k
    have hz := hs.2 hlohi
    have hu : -H / c ≤ lo := (div_le_iff₀ hc).mpr (by nlinarith only [hz])
    exact max_eq_left ((min_le_right _ _).trans hu)
  by_cases hkhi : k = hi
  · subst k
    have hz := hs.1 hlohi
    have hu : hi ≤ -H / c := (le_div_iff₀ hc).mpr (by nlinarith only [hz])
    rw [min_eq_left hu, max_eq_right hlohi.le]
  have hlo : lo < k := lt_of_le_of_ne hbox.1 (Ne.symm hklo)
  have hhi : k < hi := lt_of_le_of_ne hbox.2 hkhi
  have hz : c * k + H = 0 := le_antisymm (hs.1 hlo) (hs.2 hhi)
  have hu : -H / c = k := (div_eq_iff hc.ne').mpr (by nlinarith only [hz])
  rw [hu, min_eq_right hbox.2, max_eq_right hbox.1]

/-- One common scale-balanced box and centered multiplier produce an a.e.
equal curvature representative with finite left and right limits at every
interior probe zero. All zeros are simple as a consequence of actual joint
minimality. When H and H' both vanish, the common trace is explicitly forced
by the complete adjoint feedback. No operator sign or node premise is supplied. -/
theorem IsRecoverableAreaCompetitor.exists_curvature_node_limits_of_zero_action_minimum
    {C : ℝ} {K r p z : ℝ → ℝ} (hC : 1 < C)
    (h : IsRecoverableAreaCompetitor C K r p z)
    (hr : ContinuousOn r (Ioo (0 : ℝ) 1))
    (hp : ContinuousOn p (Ioo (0 : ℝ) 1))
    (hzero : weakMeridionalAction K r p z = 0)
    (hmin : ∀ K' r' p' z' : ℝ → ℝ, IsRecoverableAreaCompetitor C K' r' p' z' →
      weakMeridionalAction K r p z ≤ weakMeridionalAction K' r' p' z') :
    ∃ κ t : ℝ, 0 < κ ∧ κ < 2 ∧ 2 < C * κ ∧
      (∀ᵐ x ∂areaμ, κ ≤ K x ∧ K x ≤ C * κ) ∧
      (let Z := fun x => weakCurvatureAdjoint K r p z 0 x - t * (x - (1 / 2 : ℝ))
       Integrable Z areaμ ∧ Integrable (fun x => Z x * K x) areaμ ∧
       (∀ᵐ x ∂areaμ, (κ < K x → Z x ≤ 0) ∧ (K x < C * κ → 0 ≤ Z x)) ∧
       (∫ x, Z x * K x ∂areaμ) = 0 ∧
       (∫ x, max (Z x) 0 ∂areaμ) = C * (∫ x, max (-Z x) 0 ∂areaμ) ∧
       (∫ x, weakCurvatureAdjoint K r p z 0 x ∂areaμ) =
         (C - 1) * (∫ x, max (-Z x) 0 ∂areaμ)) ∧
      let H := fun x => weakCurvatureAdjointRegularPart K r p z 0 x - t * (x - 1 / 2)
      let D := fun x => 2 * warp K x * r x ^ 2
      let Kc := fun x => if r x = 0 then max κ (min (C * κ) (K x))
        else max κ (min (C * κ) (-H x / D x))
      Kc =ᵐ[areaμ] K ∧ (∀ x : ℝ, κ ≤ Kc x ∧ Kc x ≤ C * κ) ∧
      ∀ c ∈ Ioo (0 : ℝ) 1, r c = 0 →
        p c ≠ 0 ∧
        (∃ kl kr : ℝ, Tendsto Kc (𝓝[<] c) (𝓝 kl) ∧ Tendsto Kc (𝓝[>] c) (𝓝 kr)) ∧
        (H c = 0 → deriv H c = 0 →
          let f := warp K c
          let b := warpSlope K c
          let q := weakProbeEulerMomentum K r p z 0 c / f ^ 2
          let P := weakProbeEulerFlux K r p z 0 c
          let α := 2 * f * p c ^ 2
          let β := 3 * b ^ 2 * p c ^ 2 - 3 * b * q * p c + 4 * P * p c / f
          Tendsto Kc (𝓝[≠] c) (𝓝 (max κ (min (C * κ) (-β / (3 * α)))))) := by
  obtain ⟨κ, t, hκ, hκ2, h2hi, hbox, hscale⟩ :=
    h.exists_scale_balanced_curvature_multiplier hC hzero hmin
  have hκhi : κ < C * κ := hκ2.trans h2hi
  let f := warp K
  let b := warpSlope K
  let P := weakProbeEulerFlux K r p z 0
  let q := fun x => weakProbeEulerMomentum K r p z 0 x / f x ^ 2
  let A := weakCurvatureWarpCoefficient K r p z
  let B := weakCurvatureSlopeCoefficient K r p z
  let J := fun x => (∫ s in x..1, (1 - s) * A s) - ∫ s in (0 : ℝ)..x, s * A s
  let R := weakCurvatureAdjointRegularPart K r p z 0
  let F := fun x => 6 * f x * q x * p x - b x * f x * p x ^ 2 -
    3 * b x * q x * r x - 2 * P x * r x / f x + 2 * J x -
      2 * ∫ s in (0 : ℝ)..1, B s
  let H := fun x => R x - t * (x - 1 / 2)
  let G := fun x => F x - t
  let D := fun x => 2 * f x * r x ^ 2
  let Kc := fun x => if r x = 0 then max κ (min (C * κ) (K x))
    else max κ (min (C * κ) (-H x / D x))
  have hreg := h.curvature_adjoint_regularPart_of_minimum hC.le hr hp hmin
  simp only [hzero, zero_mul, sub_zero] at hreg
  obtain ⟨hres, hRCD, hRD, hFAC, hFDorig⟩ := hreg
  change weakCurvatureAdjoint K r p z 0 =ᵐ[areaμ]
    (fun x => D x * K x + R x) at hres
  change ContDiffOn ℝ 1 R (Ioo (0 : ℝ) 1) at hRCD
  change (∀ x ∈ Ioo (0 : ℝ) 1, HasDerivAt R (F x) x) at hRD
  change (∀ a ∈ Ioo (0 : ℝ) 1, ∀ d ∈ Ioo (0 : ℝ) 1,
    AbsolutelyContinuousOnInterval F a d) at hFAC
  let aK := fun x => 2 * f x * p x ^ 2 + 6 * q x * r x - 4 * b x * r x * p x +
    b x ^ 2 * r x ^ 2 / (2 * f x)
  let dK := fun x => 3 * b x ^ 2 * p x ^ 2 - 3 * b x * q x * p x +
    4 * P x * p x / f x - b x * P x * r x / f x ^ 2
  have hFD : ∀ᵐ x ∂areaμ, HasDerivAt F (aK x * K x + dK x) x := by
    filter_upwards [hFDorig] with x hx
    change HasDerivAt F _ x at hx
    apply hx.congr_deriv
    dsimp only [aK, dK]
    ring
  have hgeom := h.geometry_bounds hC.le
  have hfC : ContinuousOn f (Ioo (0 : ℝ) 1) := hgeom.1.mono Ioo_subset_Icc_self
  have hbC : ContinuousOn b (Ioo (0 : ℝ) 1) := hgeom.2.1.mono Ioo_subset_Icc_self
  have hfpos (x : ℝ) (hx : x ∈ Ioo (0 : ℝ) 1) : 0 < f x := by
    exact (mul_pos (mul_pos (by positivity : (0 : ℝ) < 2 / C) hx.1)
      (sub_pos.mpr hx.2)).trans_le (hgeom.2.2.1 x ⟨hx.1.le, hx.2.le⟩).1
  have hqC : ContinuousOn q (Ioo (0 : ℝ) 1) := by
    simpa only [hzero] using (h.probe_first_order_system_of_minimum hC.le hr hp hmin).2.2.1
  have hPC : ContinuousOn P (Ioo (0 : ℝ) 1) := by
    have hh := (h.probe_euler_flux_of_minimum hC.le hmin).2.1.continuousOn
    have hh' : ContinuousOn P (Icc (0 : ℝ) 1) := by
      simpa only [hzero, uIcc_of_le zero_le_one] using hh
    exact hh'.mono Ioo_subset_Icc_self
  have haKC : ContinuousOn aK (Ioo (0 : ℝ) 1) := by
    exact ((((continuousOn_const.mul hfC).mul (hp.pow 2)).add
      ((continuousOn_const.mul hqC).mul hr)).sub
        (((continuousOn_const.mul hbC).mul hr).mul hp)).add
          (((hbC.pow 2).mul (hr.pow 2)).div (continuousOn_const.mul hfC)
            (fun x hx => mul_ne_zero (by norm_num) (hfpos x hx).ne'))
  have hdKC : ContinuousOn dK (Ioo (0 : ℝ) 1) := by
    exact (((((continuousOn_const.mul (hbC.pow 2)).mul (hp.pow 2)).sub
      (((continuousOn_const.mul hbC).mul hqC).mul hp)).add
        (((continuousOn_const.mul hPC).mul hp).div hfC
          (fun x hx => (hfpos x hx).ne'))).sub
            (((hbC.mul hPC).mul hr).div (hfC.pow 2)
              (fun x hx => pow_ne_zero 2 (hfpos x hx).ne')))
  have hKcbox (x : ℝ) : κ ≤ Kc x ∧ Kc x ≤ C * κ := by
    dsimp only [Kc]
    split_ifs <;> exact ⟨le_max_left _ _, max_le hκhi.le (min_le_left _ _)⟩
  have hKceq : Kc =ᵐ[areaμ] K := by
    filter_upwards [hbox, hscale.2.2.1, hres, ae_restrict_mem measurableSet_Ioo]
      with x hx hs heq hxI
    by_cases hrx : r x = 0
    · simp only [Kc, ite_eq_left hrx]
      rw [min_eq_right hx.2, max_eq_right hx.1]
    · have hDx : 0 < D x := mul_pos (mul_pos (by norm_num) (hfpos x hxI))
        (sq_pos_of_ne_zero hrx)
      dsimp only [Kc]
      rw [ite_eq_right hrx]
      apply clamp_of_complementarity κ (C * κ) (K x) (D x) (H x) hκhi hDx hx
      simpa only [heq, H, sub_eq_add_neg, add_assoc] using hs
  refine ⟨κ, t, hκ, hκ2, h2hi, hbox, hscale, hKceq, hKcbox, ?_⟩
  intro c hc hrc
  have hsimple := h.simple_zero_of_zero_action_minimum hC.le hr hp hzero hmin hc hrc
  refine ⟨hsimple.2, ?_⟩
  let α := 2 * f c * p c ^ 2
  let β := 3 * b c ^ 2 * p c ^ 2 - 3 * b c * q c * p c + 4 * P c * p c / f c
  have hα : 0 < α := mul_pos (mul_pos (by norm_num) (hfpos c hc))
    (sq_pos_of_ne_zero hsimple.2)
  have ha0 : aK c = α := by dsimp only [aK, α]; rw [hrc]; ring
  have hd0 : dK c = β := by dsimp only [dK, β]; rw [hrc]; ring
  let e := fun x => (aK x - α) * Kc x + (dK x - β)
  have hKb : IsBoundedUnder (· ≤ ·) (𝓝[≠] c) (norm ∘ Kc) := by
    refine ⟨C * κ, ?_⟩
    rw [eventually_map]
    apply Eventually.of_forall
    intro x
    change ‖Kc x‖ ≤ C * κ
    rw [Real.norm_eq_abs]
    rw [abs_of_pos (hκ.trans_le (hKcbox x).1)]
    exact (hKcbox x).2
  have he : Tendsto e (𝓝[≠] c) (𝓝 0) := by
    have haT : Tendsto (fun x => aK x - α) (𝓝[≠] c) (𝓝 0) := by
      simpa only [ha0, sub_self] using
        ((haKC.continuousAt (isOpen_Ioo.mem_nhds hc)).tendsto.sub_const α).mono_left
          nhdsWithin_le_nhds
    have hdT : Tendsto (fun x => dK x - β) (𝓝[≠] c) (𝓝 0) := by
      simpa only [hd0, sub_self] using
        ((hdKC.continuousAt (isOpen_Ioo.mem_nhds hc)).tendsto.sub_const β).mono_left
          nhdsWithin_le_nhds
    have hm := NormedField.tendsto_zero_smul_of_tendsto_zero_of_bounded haT hKb
    simpa only [e, Pi.smul_apply, smul_eq_mul, Pi.mul_apply, zero_add] using hm.add hdT
  have hDlim : Tendsto (fun x => D x / (x - c) ^ 2) (𝓝[≠] c) (𝓝 α) := by
    have hrT := hsimple.1.tendsto_slope
    change Tendsto (fun x => slope r c x) (𝓝[≠] c) (𝓝 (p c)) at hrT
    simp only [slope_def_field, hrc, sub_zero] at hrT
    have hfT0 : Tendsto f (𝓝[≠] c) (𝓝 (f c)) :=
      (hfC.continuousAt (isOpen_Ioo.mem_nhds hc)).tendsto.mono_left nhdsWithin_le_nhds
    have hfT := hfT0.const_mul 2
    have hh := hfT.mul (hrT.pow 2)
    simpa only [D, α, div_pow, mul_div_assoc] using hh
  let a := c / 2
  let d := (c + 1) / 2
  have ha : a ∈ Ioo (0 : ℝ) 1 := by dsimp [a]; constructor <;> linarith [hc.1, hc.2]
  have hd : d ∈ Ioo (0 : ℝ) 1 := by dsimp [d]; constructor <;> linarith [hc.1, hc.2]
  have hac : a < c := by dsimp [a]; linarith [hc.1]
  have hcd : c < d := by dsimp [d]; linarith [hc.2]
  have hsub : uIcc a d ⊆ Ioo (0 : ℝ) 1 := by
    rw [uIcc_of_le (hac.trans hcd).le]
    exact fun x hx => ⟨ha.1.trans_le hx.1, hx.2.trans_lt hd.2⟩
  have hHA : AbsolutelyContinuousOnInterval H a d :=
    ((hRCD.mono hsub).absolutelyContinuousOnInterval).fun_sub
      (show ContDiff ℝ 1 (fun x : ℝ => t * (x - 1 / 2)) by
        fun_prop).contDiffOn.absolutelyContinuousOnInterval
  have hGA : AbsolutelyContinuousOnInterval G a d :=
    (hFAC a ha d hd).fun_sub
      (contDiff_const : ContDiff ℝ 1 (fun _ : ℝ => t)).contDiffOn.absolutelyContinuousOnInterval
  have hHD (x : ℝ) (hx : x ∈ Ioo (0 : ℝ) 1) : HasDerivAt H (G x) x := by
    have hh := (hRD x hx).fun_sub (((hasDerivAt_id x).sub_const (1 / 2)).const_mul t)
    change HasDerivAt H _ x at hh
    exact hh.congr_deriv (by dsimp only [G]; ring)
  have hODE : ∀ᵐ x ∂volume, x ∈ Ioo a d →
      HasDerivAt H (G x) x ∧ HasDerivAt G (α * Kc x + β + e x) x := by
    have hae := (ae_restrict_iff' measurableSet_Ioo).mp (hFD.and hKceq)
    filter_upwards [hae] with x hx hxI
    have hxi : x ∈ Ioo (0 : ℝ) 1 := hsub (by
      simpa only [uIcc_of_le (hac.trans hcd).le] using Ioo_subset_Icc_self hxI)
    have hfx := (hx hxi).1.sub_const t
    change HasDerivAt G _ x at hfx
    refine ⟨hHD x hxi, hfx.congr_deriv ?_⟩
    dsimp only [e]
    rw [(hx hxi).2]
    ring
  have hclip : ∀ᶠ x in 𝓝[≠] c, Kc x = max κ (min (C * κ) (-H x / D x)) := by
    filter_upwards [h.isolated_zero_of_minimum hC.le hr hp hmin hc hrc] with x hx
    exact ite_eq_right hx
  have hD0 : D c = 0 := by dsimp only [D]; rw [hrc]; ring
  have hout := Analysis.exists_oneSided_clamp_limits_of_quadratic_feedback
    hac hcd hκhi.le hα hHA hGA hODE hD0 he hDlim hclip
  refine ⟨hout.1, ?_⟩
  intro hH0 hHd0
  have hG0 : G c = 0 := by rw [← (hHD c hc).deriv, hHd0]
  exact hout.2 hH0 hG0

end RicciFlowSharpEstimate.Geometry.AreaProfile
