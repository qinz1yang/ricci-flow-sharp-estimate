/-
Copyright (c) 2026 Ziyang Qin. All rights reserved.
No license is granted by this file.
Authors: Ziyang Qin
-/
import RicciFlowSharpEstimate.Geometry.AreaCurvatureNodeLimits
import RicciFlowSharpEstimate.Geometry.WeakCurvaturePolarRate
import RicciFlowSharpEstimate.Geometry.WeakCurvatureAdjointPoleTraces
import RicciFlowSharpEstimate.Geometry.AreaPrimitivePoleRates
import RicciFlowSharpEstimate.Analysis.ClampedIntegralFeedback

/-! # Actual curvature pole limits at nonzero minimizing probe traces -/

noncomputable section
namespace RicciFlowSharpEstimate.Geometry.AreaProfile
open Set MeasureTheory Filter Topology
local notation "areaμ" => volume.restrict (Ioo (0 : ℝ) 1)

private theorem reflect_right_zero :
    Tendsto (fun x : ℝ => 1 - x) (𝓝[>] 0) (𝓝[<] 1) := by
  apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
  · simpa only [sub_zero] using
      (tendsto_const_nhds.sub (tendsto_id.mono_left nhdsWithin_le_nhds) :
        Tendsto (fun x : ℝ => 1 - x) (𝓝[>] 0) (𝓝 (1 - 0)))
  · filter_upwards [self_mem_nhdsWithin] with x hx
    change 0 < x at hx
    change 1 - x < 1
    linarith

private theorem reflect_left_one :
    Tendsto (fun x : ℝ => 1 - x) (𝓝[<] 1) (𝓝[>] 0) := by
  apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
  · simpa only [sub_self] using
      (tendsto_const_nhds.sub (tendsto_id.mono_left nhdsWithin_le_nhds) :
        Tendsto (fun x : ℝ => 1 - x) (𝓝[<] 1) (𝓝 (1 - 1)))
  · filter_upwards [self_mem_nhdsWithin] with x hx
    change x < 1 at hx
    change 0 < 1 - x
    exact sub_pos.mpr hx

private theorem average_eq_of_ae_eq {f g : ℝ → ℝ} {a b : ℝ}
    (ha : 0 ≤ a) (hab : a < b) (hb : b ≤ 1) (heq : f =ᵐ[areaμ] g) :
    (⨍ t in a..b, f t) = (⨍ t in a..b, g t) := by
  rw [interval_average_eq_div, interval_average_eq_div]
  congr 1
  apply intervalIntegral.integral_congr_ae
  filter_upwards [ae_imp_of_ae_restrict heq, volume.ae_ne (1 : ℝ)] with t ht ht1 htI
  have htC : t ∈ Ioc a b := by simpa only [uIoc_of_le hab.le] using htI
  exact ht ⟨ha.trans_lt htC.1, lt_of_le_of_ne (htC.2.trans hb) ht1⟩

private theorem reflected_average (K : ℝ → ℝ) (x : ℝ) :
    (⨍ t in (0 : ℝ)..x, K (1 - t)) = (⨍ t in (1 - x)..(1 : ℝ), K t) := by
  rw [interval_average_eq_div, interval_average_eq_div,
    intervalIntegral.integral_comp_sub_left]
  simp only [sub_zero, sub_sub_cancel]

private theorem pole_limit_from_rate
    {K H f r : ℝ → ℝ} {lo hi a h0 L : ℝ}
    (hlohi : lo ≤ hi) (hK : IntegrableOn K (Ioo (0 : ℝ) 1))
    (hbox : ∀ x ∈ Ioo (0 : ℝ) 1, lo ≤ K x ∧ K x ≤ hi)
    (hH : DifferentiableOn ℝ H (Ioo (0 : ℝ) 1))
    (hf : Tendsto (fun x => f x / x) (𝓝[>] 0) (𝓝 2))
    (hr : Tendsto r (𝓝[>] 0) (𝓝 a)) (ha : a ≠ 0)
    (hH0 : Tendsto H (𝓝[>] 0) (𝓝 h0))
    (hderiv : Tendsto (fun x => deriv H x - a ^ 2 * (⨍ t in (0 : ℝ)..x, K t))
      (𝓝[>] 0) (𝓝 L))
    (hclip : ∀ᶠ x in 𝓝[>] (0 : ℝ),
      K x = max lo (min hi (-H x / (2 * f x * r x ^ 2)))) :
    (∃ k : ℝ, Tendsto K (𝓝[>] 0) (𝓝 k)) ∧
      (h0 = 0 → Tendsto K (𝓝[>] 0)
        (𝓝 (max lo (min hi (-L / (5 * a ^ 2)))))) := by
  let D := fun x => 2 * f x * r x ^ 2
  have ha2 : 0 < a ^ 2 := sq_pos_of_ne_zero ha
  have hD : Tendsto (fun x => D x / x) (𝓝[>] 0) (𝓝 (4 * a ^ 2)) := by
    convert (hf.const_mul 2).mul (hr.pow 2) using 1
    · ext x
      dsimp only [D]
      simp only [div_eq_mul_inv]
      ring
    · congr 1
      ring
  have hD0 : Tendsto D (𝓝[>] 0) (𝓝 0) := by
    have hh : Tendsto (fun x => D x / x * x) (𝓝[>] 0) (𝓝 0) := by
      simpa only [mul_zero, id_eq] using hD.mul (tendsto_id.mono_left nhdsWithin_le_nhds)
    apply hh.congr'
    filter_upwards [self_mem_nhdsWithin] with x hx
    change 0 < x at hx
    exact div_mul_cancel₀ (D x) hx.ne'
  have hDpos : ∀ᶠ x in 𝓝[>] (0 : ℝ), 0 < D x := by
    filter_upwards [hD.eventually (lt_mem_nhds (by positivity : 0 < 4 * a ^ 2)),
      self_mem_nhdsWithin] with x hx hxp
    change 0 < x at hxp
    have hh := mul_pos hx hxp
    simpa only [div_mul_cancel₀ (D x) hxp.ne'] using hh
  have hcancel (hz : h0 = 0) : Tendsto K (𝓝[>] 0)
      (𝓝 (max lo (min hi (-L / (5 * a ^ 2))))) := by
    have hh := Analysis.tendsto_clamp_of_derivative_average zero_lt_one hlohi
      (sq_nonneg a) (by nlinarith only [ha2] : a ^ 2 < 4 * a ^ 2)
      hK hbox hH (by simpa only [hz] using hH0) hderiv hD hclip
    convert hh using 1
    congr 3
    ring
  refine ⟨?_, hcancel⟩
  by_cases hz : h0 = 0
  · exact ⟨_, hcancel hz⟩
  rcases lt_or_gt_of_ne hz with hn | hp
  · have hS : Tendsto (fun x => -H x - D x * hi) (𝓝[>] 0) (𝓝 (-h0)) := by
      simpa only [zero_mul, sub_zero] using hH0.neg.sub (hD0.mul_const hi)
    have hc : ∀ᶠ x in 𝓝[>] (0 : ℝ), K x = hi := by
      filter_upwards [hS.eventually (lt_mem_nhds (neg_pos.mpr hn)), hDpos, hclip]
        with x hs hd hk
      have harg : hi ≤ -H x / D x := (le_div_iff₀ hd).mpr (by linarith)
      change K x = max lo (min hi (-H x / D x)) at hk
      rw [min_eq_left harg, max_eq_right hlohi] at hk
      exact hk
    exact ⟨hi, tendsto_const_nhds.congr' (Filter.EventuallyEq.symm hc)⟩
  · have hS : Tendsto (fun x => -H x - D x * lo) (𝓝[>] 0) (𝓝 (-h0)) := by
      simpa only [zero_mul, sub_zero] using hH0.neg.sub (hD0.mul_const lo)
    have hc : ∀ᶠ x in 𝓝[>] (0 : ℝ), K x = lo := by
      filter_upwards [hS.eventually (gt_mem_nhds (neg_neg_of_pos hp)), hDpos, hclip]
        with x hs hd hk
      have harg : -H x / D x ≤ lo := (div_le_iff₀ hd).mpr (by linarith)
      change K x = max lo (min hi (-H x / D x)) at hk
      rw [max_eq_left ((min_le_right hi _).trans harg)] at hk
      exact hk
    exact ⟨lo, tendsto_const_nhds.congr' (Filter.EventuallyEq.symm hc)⟩

/-- One actual scale box and multiplier give the accepted node laws and
finite curvature traces at every pole with nonzero probe trace. At a
cancelling residual the trace is selected by actual averaged feedback.
Zero probe-trace poles are deliberately not assigned a curvature limit. -/
theorem IsRecoverableAreaCompetitor.exists_curvature_pole_limits_at_nonzero_traces_of_minimum
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
      let R := fun x => r (1 / 2) + ∫ s in (1 / 2 : ℝ)..x, p s
      let q := fun x => weakProbeEulerMomentum K r p z 0 x / warp K x ^ 2
      let A := weakCurvatureWarpCoefficient K r p z
      let B := weakCurvatureSlopeCoefficient K r p z
      Kc =ᵐ[areaμ] K ∧ (∀ x : ℝ, κ ≤ Kc x ∧ Kc x ≤ C * κ) ∧
      (∀ c ∈ Ioo (0 : ℝ) 1, r c = 0 →
        p c ≠ 0 ∧
        (∃ kl kr : ℝ, Tendsto Kc (𝓝[<] c) (𝓝 kl) ∧ Tendsto Kc (𝓝[>] c) (𝓝 kr)) ∧
        (H c = 0 → deriv H c = 0 →
          let f := warp K c
          let b := warpSlope K c
          let qc := weakProbeEulerMomentum K r p z 0 c / f ^ 2
          let P := weakProbeEulerFlux K r p z 0 c
          let α := 2 * f * p c ^ 2
          let β := 3 * b ^ 2 * p c ^ 2 - 3 * b * qc * p c + 4 * P * p c / f
          Tendsto Kc (𝓝[≠] c) (𝓝 (max κ (min (C * κ) (-β / (3 * α))))))) ∧
      ∃ qL qR : ℝ,
        Tendsto (fun x => q x + r x * (2 - warpSlope K x) / (2 * warp K x))
          (𝓝[>] 0) (𝓝 qL) ∧
        Tendsto (fun x => q x + r x * (2 + warpSlope K x) / (2 * warp K x))
          (𝓝[<] 1) (𝓝 qR) ∧
        (R 0 ≠ 0 → ∃ k : ℝ, Tendsto Kc (𝓝[>] 0) (𝓝 k)) ∧
        (R 1 ≠ 0 → ∃ k : ℝ, Tendsto Kc (𝓝[<] 1) (𝓝 k)) ∧
        (R 0 ≠ 0 → t = 4 * R 0 ^ 2 →
          let L := -6 * R 0 * qL + 2 * (∫ s in (0 : ℝ)..1, (1 - s) * A s) -
            2 * (∫ s in (0 : ℝ)..1, B s) - t
          Tendsto Kc (𝓝[>] 0) (𝓝 (max κ (min (C * κ) (-L / (5 * R 0 ^ 2)))))) ∧
        (R 1 ≠ 0 → t = -4 * R 1 ^ 2 →
          let L := 6 * R 1 * qR - 2 * (∫ s in (0 : ℝ)..1, s * A s) -
            2 * (∫ s in (0 : ℝ)..1, B s) - t
          Tendsto Kc (𝓝[<] 1) (𝓝 (max κ (min (C * κ) (L / (5 * R 1 ^ 2)))))) := by
  obtain ⟨κ, t, hκ, hκ2, h2hi, hbox, hscale, hnodes⟩ :=
    h.exists_curvature_node_limits_of_zero_action_minimum hC hr hp hzero hmin
  let f := warp K
  let b := warpSlope K
  let q := fun x => weakProbeEulerMomentum K r p z 0 x / f x ^ 2
  let R := fun x => r (1 / 2) + ∫ s in (1 / 2 : ℝ)..x, p s
  let A := weakCurvatureWarpCoefficient K r p z
  let B := weakCurvatureSlopeCoefficient K r p z
  let H := fun x => weakCurvatureAdjointRegularPart K r p z 0 x - t * (x - 1 / 2)
  let D := fun x => 2 * f x * r x ^ 2
  let Kc := fun x => if r x = 0 then max κ (min (C * κ) (K x))
    else max κ (min (C * κ) (-H x / D x))
  change Kc =ᵐ[areaμ] K ∧ (∀ x : ℝ, κ ≤ Kc x ∧ Kc x ≤ C * κ) ∧ _ at hnodes
  have hKcI : IntegrableOn Kc (Ioo (0 : ℝ) 1) :=
    (h.1.integrable (by norm_num : (1 : ENNReal) ≤ 2)).congr hnodes.1.symm
  have hKcBox (x : ℝ) (_hx : x ∈ Ioo (0 : ℝ) 1) := hnodes.2.1 x
  have hKIc : IntervalIntegrable Kc volume 0 1 :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le zero_le_one).mpr hKcI
  have hKRi : IntegrableOn (fun x => Kc (1 - x)) (Ioo (0 : ℝ) 1) := by
    apply (intervalIntegrable_iff_integrableOn_Ioo_of_le zero_le_one).mp
    simpa only [sub_self, sub_zero] using (hKIc.comp_sub_left 1).symm
  obtain ⟨_, _, _, _, _, hrLT, hrRT, _⟩ :=
    h.probe_pole_integrability_of_minimum hC.le hr hp hmin
  change Tendsto r (𝓝[>] 0) (𝓝 (R 0)) at hrLT
  change Tendsto r (𝓝[<] 1) (𝓝 (R 1)) at hrRT
  have hAdj := h.curvature_adjoint_pole_traces_of_minimum hC.le hr hp hmin
  have hReg := h.curvature_adjoint_regularPart_of_minimum hC.le hr hp hmin
  have hRate := h.curvature_adjoint_polar_derivative_rate_of_minimum hC.le hr hp hmin
  rw [hzero] at hAdj hReg hRate
  simp only [zero_mul, sub_zero] at hReg hRate
  obtain ⟨_, qL, qR, hQL, hQR, hRates⟩ := hRate
  let LL := -6 * R 0 * qL + 2 * (∫ s in (0 : ℝ)..1, (1 - s) * A s) -
    2 * (∫ s in (0 : ℝ)..1, B s) - t
  let LR := 6 * R 1 * qR - 2 * (∫ s in (0 : ℝ)..1, s * A s) -
    2 * (∫ s in (0 : ℝ)..1, B s) - t
  have hRawL := (hRates t).1
  have hRawR := (hRates t).2
  change Tendsto (fun x => deriv H x - R 0 ^ 2 * (2 - b x) / f x)
    (𝓝[>] 0) (𝓝 LL) at hRawL
  change Tendsto (fun x => deriv H x + R 1 ^ 2 * (2 + b x) / f x)
    (𝓝[<] 1) (𝓝 LR) at hRawR
  have hHD : DifferentiableOn ℝ H (Ioo (0 : ℝ) 1) := by
    intro x hx
    have hh := (hReg.2.2.1 x hx).fun_sub
      (((hasDerivAt_id x).sub_const (1 / 2 : ℝ)).const_mul t)
    exact hh.differentiableAt.differentiableWithinAt
  have hFR := h.primitive_first_order_pole_rates hC.le
  have hAR := h.primitive_curvature_average_pole_rates hC.le
  have hADL : Tendsto (fun x => (2 - b x) / f x - (⨍ s in (0 : ℝ)..x, Kc s))
      (𝓝[>] 0) (𝓝 0) := by
    apply hAR.1.congr'
    filter_upwards [Ioo_mem_nhdsGT zero_lt_one] with x hx
    change (2 - b x) / f x - (⨍ s in (0 : ℝ)..x, K s) = _
    rw [average_eq_of_ae_eq le_rfl hx.1 hx.2.le hnodes.1]
  have hADR : Tendsto (fun x => (2 + b x) / f x - (⨍ s in x..(1 : ℝ), Kc s))
      (𝓝[<] 1) (𝓝 0) := by
    apply hAR.2.congr'
    filter_upwards [Ioo_mem_nhdsLT zero_lt_one] with x hx
    change (2 + b x) / f x - (⨍ s in x..(1 : ℝ), K s) = _
    rw [average_eq_of_ae_eq hx.1.le hx.2 le_rfl hnodes.1]
  have hLder : Tendsto (fun x => deriv H x - R 0 ^ 2 * (⨍ s in (0 : ℝ)..x, Kc s))
      (𝓝[>] 0) (𝓝 LL) := by
    apply (show Tendsto (fun x =>
      (deriv H x - R 0 ^ 2 * (2 - b x) / f x) +
        R 0 ^ 2 * ((2 - b x) / f x - (⨍ s in (0 : ℝ)..x, Kc s)))
      (𝓝[>] 0) (𝓝 LL) from
        by simpa only [mul_zero, add_zero] using hRawL.add (hADL.const_mul (R 0 ^ 2))).congr'
    filter_upwards [] with x
    ring
  have hRder : Tendsto (fun x => deriv H x + R 1 ^ 2 * (⨍ s in x..(1 : ℝ), Kc s))
      (𝓝[<] 1) (𝓝 LR) := by
    apply (show Tendsto (fun x =>
      (deriv H x + R 1 ^ 2 * (2 + b x) / f x) -
        R 1 ^ 2 * ((2 + b x) / f x - (⨍ s in x..(1 : ℝ), Kc s)))
      (𝓝[<] 1) (𝓝 LR) from
        by simpa only [mul_zero, sub_zero] using hRawR.sub (hADR.const_mul (R 1 ^ 2))).congr'
    filter_upwards [] with x
    ring
  have hLT := (hAdj.2.2 t).1
  have hRT := (hAdj.2.2 t).2
  change Tendsto H (𝓝[>] 0) (𝓝 (-2 * R 0 ^ 2 + t / 2)) at hLT
  change Tendsto H (𝓝[<] 1) (𝓝 (-2 * R 1 ^ 2 - t / 2)) at hRT
  have hLeft (ha : R 0 ≠ 0) := by
    have hn : ∀ᶠ x in 𝓝[>] (0 : ℝ), r x ≠ 0 :=
      hrLT.eventually (isOpen_compl_singleton.mem_nhds ha)
    have hc : ∀ᶠ x in 𝓝[>] (0 : ℝ),
        Kc x = max κ (min (C * κ) (-H x / (2 * f x * r x ^ 2))) := by
      filter_upwards [hn] with x hx
      dsimp only [Kc, D]
      rw [ite_eq_right hx]
    exact pole_limit_from_rate (hκ2.trans h2hi).le hKcI hKcBox hHD hFR.1 hrLT ha hLT
      hLder hc
  let HR := fun x => H (1 - x)
  let KR := fun x => Kc (1 - x)
  let fR := fun x => f (1 - x)
  let rR := fun x => r (1 - x)
  have hRefDom (x : ℝ) (hx : x ∈ Ioo (0 : ℝ) 1) : 1 - x ∈ Ioo (0 : ℝ) 1 :=
    ⟨sub_pos.mpr hx.2, by linarith [hx.1]⟩
  have hHRD (x : ℝ) (hx : x ∈ Ioo (0 : ℝ) 1) :
      HasDerivAt HR (-deriv H (1 - x)) x := by
    have hDH := ((hHD (1 - x) (hRefDom x hx)).differentiableAt
      (Ioo_mem_nhds (hRefDom x hx).1 (hRefDom x hx).2)).hasDerivAt
    simpa only [HR, Function.comp_def, zero_sub, mul_neg_one, id_eq] using
      hDH.comp x ((hasDerivAt_const x (1 : ℝ)).fun_sub (hasDerivAt_id x))
  have hHRDiff : DifferentiableOn ℝ HR (Ioo (0 : ℝ) 1) :=
    fun x hx => (hHRD x hx).differentiableAt.differentiableWithinAt
  have hRDerRef : Tendsto (fun x => deriv HR x - R 1 ^ 2 *
      (⨍ s in (0 : ℝ)..x, KR s)) (𝓝[>] 0) (𝓝 (-LR)) := by
    apply (hRder.neg.comp reflect_right_zero).congr'
    filter_upwards [Ioo_mem_nhdsGT zero_lt_one] with x hx
    dsimp only [Function.comp_def]
    rw [(hHRD x hx).deriv]
    dsimp only [KR]
    rw [reflected_average]
    ring
  have hfRef : Tendsto (fun x => fR x / x) (𝓝[>] 0) (𝓝 2) := by
    simpa only [fR, f, Function.comp_def, sub_sub_cancel] using
      hFR.2.comp reflect_right_zero
  have hrRef : Tendsto rR (𝓝[>] 0) (𝓝 (R 1)) := hrRT.comp reflect_right_zero
  have hHRef : Tendsto HR (𝓝[>] 0) (𝓝 (-2 * R 1 ^ 2 - t / 2)) :=
    hRT.comp reflect_right_zero
  have hRight (ha : R 1 ≠ 0) := by
    have hn : ∀ᶠ x in 𝓝[>] (0 : ℝ), rR x ≠ 0 :=
      hrRef.eventually (isOpen_compl_singleton.mem_nhds ha)
    have hc : ∀ᶠ x in 𝓝[>] (0 : ℝ),
        KR x = max κ (min (C * κ) (-HR x / (2 * fR x * rR x ^ 2))) := by
      filter_upwards [hn] with x hx
      dsimp only [KR, HR, fR, rR, Kc, D] at *
      rw [ite_eq_right hx]
    exact pole_limit_from_rate (hκ2.trans h2hi).le hKRi
      (fun x hx => hKcBox (1 - x) (hRefDom x hx)) hHRDiff hfRef hrRef ha hHRef hRDerRef hc
  refine ⟨κ, t, hκ, hκ2, h2hi, hbox, hscale, hnodes.1, hnodes.2.1, hnodes.2.2,
    qL, qR, hQL, hQR, ?_, ?_, ?_, ?_⟩
  · intro ha
    exact (hLeft ha).1
  · intro ha
    obtain ⟨k, hk⟩ := (hRight ha).1
    refine ⟨k, ?_⟩
    simpa only [KR, Function.comp_def, sub_sub_cancel] using hk.comp reflect_left_one
  · intro ha ht
    exact (hLeft ha).2 (by rw [ht]; ring)
  · intro ha ht
    have hh := (hRight ha).2 (by rw [ht]; ring)
    simpa only [KR, Function.comp_def, sub_sub_cancel, neg_neg] using
      hh.comp reflect_left_one

end RicciFlowSharpEstimate.Geometry.AreaProfile
