/-
Copyright (c) 2026 Ziyang Qin. All rights reserved.
No license is granted by this file.
Authors: Ziyang Qin
-/
import RicciFlowSharpEstimate.Geometry.WeakProbeZeroTraceRates
import RicciFlowSharpEstimate.Geometry.WeakCurvaturePolarRate
import RicciFlowSharpEstimate.Geometry.WeakCurvatureAdjointPoleTraces
import RicciFlowSharpEstimate.Analysis.QuadraticPoleRemainder

/-! # Quadratic polar rates of the complete regular adjoint at zero probe traces -/

noncomputable section
namespace RicciFlowSharpEstimate.Geometry.AreaProfile
open Set MeasureTheory Filter Topology
local notation "areaμ" => volume.restrict (Ioo (0 : ℝ) 1)

private theorem zero_mul_bounded {α : Type*} {l : Filter α} {u v : α → ℝ} {M : ℝ}
    (hu : Tendsto u l (𝓝 0)) (hv : ∀ᶠ x in l, |v x| ≤ M) :
    Tendsto (fun x => u x * v x) l (𝓝 0) := by
  apply squeeze_zero_norm'
  · filter_upwards [hv] with x hx
    simp only [norm_mul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left hx (abs_nonneg _)
  · simpa only [norm_zero, zero_mul, Real.norm_eq_abs] using hu.norm.mul_const M

private theorem adjoint_second_density_tendsto
    {l : Filter ℝ} {f b q p r P K d : ℝ → ℝ} {b0 q0 p0 M : ℝ}
    (hd : Tendsto d l (𝓝 0)) (hdn : ∀ᶠ x in l, d x ≠ 0)
    (hf : Tendsto (fun x => f x / d x) l (𝓝 2))
    (hb : Tendsto b l (𝓝 b0)) (hq : Tendsto q l (𝓝 q0))
    (hp : Tendsto p l (𝓝 p0)) (hr : Tendsto (fun x => r x / d x) l (𝓝 (q0 / 4)))
    (hP : Tendsto (fun x => P x / d x) l (𝓝 0))
    (hK : ∀ᶠ x in l, |K x| ≤ M) :
    Tendsto (fun x =>
      (2 * f x * p x ^ 2 + 6 * q x * r x - 4 * b x * r x * p x +
          b x ^ 2 * r x ^ 2 / (2 * f x)) * K x +
        3 * b x ^ 2 * p x ^ 2 - 3 * b x * q x * p x +
          4 * P x * p x / f x - b x * P x * r x / f x ^ 2) l
      (𝓝 (3 * b0 ^ 2 * p0 ^ 2 - 3 * b0 * q0 * p0)) := by
  have hfn : ∀ᶠ x in l, f x ≠ 0 := by
    filter_upwards [hf.eventually (isOpen_compl_singleton.mem_nhds
      (by norm_num : (2 : ℝ) ≠ 0))] with x hx
    intro he
    exact hx (by simp only [he, zero_div, mem_singleton_iff])
  have hf0 : Tendsto f l (𝓝 0) := by
    apply (show Tendsto (fun x => (f x / d x) * d x) l (𝓝 0) from
      by simpa only [mul_zero] using hf.mul hd).congr'
    filter_upwards [hdn] with x hx
    exact div_mul_cancel₀ (f x) hx
  have hr0 : Tendsto r l (𝓝 0) := by
    apply (show Tendsto (fun x => (r x / d x) * d x) l (𝓝 0) from
      by simpa only [mul_zero] using hr.mul hd).congr'
    filter_upwards [hdn] with x hx
    exact div_mul_cancel₀ (r x) hx
  have hrf : Tendsto (fun x => r x / f x) l (𝓝 ((q0 / 4) / 2)) := by
    apply (hr.div hf (by norm_num : (2 : ℝ) ≠ 0)).congr'
    filter_upwards [hdn, hfn] with x hx hxF
    change (r x / d x) / (f x / d x) = r x / f x
    field_simp
  have hPf : Tendsto (fun x => P x / f x) l (𝓝 0) := by
    have hh := hP.div hf (by norm_num : (2 : ℝ) ≠ 0)
    simp only [zero_div] at hh
    apply hh.congr'
    filter_upwards [hdn, hfn] with x hx hxF
    change (P x / d x) / (f x / d x) = P x / f x
    field_simp
  have hPrff : Tendsto (fun x => P x * r x / f x ^ 2) l (𝓝 0) := by
    have hh := (hP.mul hr).div (hf.pow 2) (by norm_num : (2 : ℝ) ^ 2 ≠ 0)
    simp only [zero_mul, zero_div] at hh
    apply hh.congr'
    filter_upwards [hdn, hfn] with x hx hxF
    change ((P x / d x) * (r x / d x)) / (f x / d x) ^ 2 = P x * r x / f x ^ 2
    field_simp
  have hcoef : Tendsto (fun x => 2 * f x * p x ^ 2 + 6 * q x * r x -
      4 * b x * r x * p x + b x ^ 2 * r x ^ 2 / (2 * f x)) l (𝓝 0) := by
    have ht := ((((hf0.mul (hp.pow 2)).const_mul 2).add
      ((hq.mul hr0).const_mul 6)).sub (((hb.mul hr0).mul hp).const_mul 4)).add
        ((((hb.pow 2).mul hr0).mul hrf).div_const 2)
    apply (show Tendsto (fun x => 2 * (f x * p x ^ 2) + 6 * (q x * r x) -
      4 * (b x * r x * p x) + (b x ^ 2 * r x * (r x / f x)) / 2) l
        (𝓝 0) from by simpa only [zero_mul, mul_zero, zero_add, add_zero,
          sub_zero, zero_sub, neg_zero, zero_div] using ht).congr'
    filter_upwards [hfn] with x hx
    field_simp
  have hKzero := zero_mul_bounded hcoef hK
  have hcore := (((hb.pow 2).mul (hp.pow 2)).const_mul 3).sub
    (((hb.mul hq).mul hp).const_mul 3)
  have hrest := ((hKzero.add hcore).add ((hPf.mul hp).const_mul 4)).sub (hb.mul hPrff)
  apply (show Tendsto (fun x =>
    (2 * f x * p x ^ 2 + 6 * q x * r x - 4 * b x * r x * p x +
      b x ^ 2 * r x ^ 2 / (2 * f x)) * K x +
      (3 * (b x ^ 2 * p x ^ 2) - 3 * (b x * q x * p x)) +
        4 * ((P x / f x) * p x) - b x * (P x * r x / f x ^ 2)) l
      (𝓝 (3 * b0 ^ 2 * p0 ^ 2 - 3 * b0 * q0 * p0)) from by
        simpa only [zero_add, add_zero, zero_mul, mul_zero, sub_zero, mul_assoc] using hrest).congr'
  filter_upwards [hfn] with x hx
  field_simp
  ring

private theorem zero_trace_flux_div_limit
    {l : Filter ℝ} {P u b R d : ℝ → ℝ} {b0 M : ℝ}
    (hE : Tendsto (fun x => (P x - u x * b x * R x / 2) / d x) l (𝓝 0))
    (hR : Tendsto R l (𝓝 0)) (hb : Tendsto b l (𝓝 b0))
    (hu : ∀ᶠ x in l, |u x / d x| ≤ M) :
    Tendsto (fun x => P x / d x) l (𝓝 0) := by
  have hprod := (zero_mul_bounded (show Tendsto (fun x => R x * b x) l (𝓝 0) from
    by simpa only [zero_mul] using hR.mul hb) hu).div_const 2
  apply (show Tendsto (fun x => (P x - u x * b x * R x / 2) / d x +
    (R x * b x * (u x / d x)) / 2) l (𝓝 0) from
      by simpa only [zero_div, zero_add] using hE.add hprod).congr'
  filter_upwards [] with x
  ring

private theorem node_free_and_cubic_rate
    {l : Filter ℝ} {f r d : ℝ → ℝ} {q0 : ℝ}
    (hq0 : q0 ≠ 0) (hd : ∀ᶠ x in l, d x ≠ 0)
    (hf : Tendsto (fun x => f x / d x) l (𝓝 2))
    (hr : Tendsto (fun x => r x / d x) l (𝓝 (q0 / 4))) :
    (∀ᶠ x in l, r x ≠ 0) ∧
      Tendsto (fun x => 2 * f x * r x ^ 2 / d x ^ 3) l (𝓝 (q0 ^ 2 / 4)) := by
  constructor
  · filter_upwards [hr.eventually (isOpen_compl_singleton.mem_nhds
      (div_ne_zero hq0 (by norm_num : (4 : ℝ) ≠ 0)))] with x hx
    intro he
    exact hx (by simp only [he, zero_div, mem_singleton_iff])
  · have hh := (hf.mul (hr.pow 2)).const_mul 2
    have he : 2 * ((2 : ℝ) * (q0 / 4) ^ 2) = q0 ^ 2 / 4 := by ring
    rw [he] at hh
    apply hh.congr'
    filter_upwards [hd] with x hx
    field_simp

/-- At a zero probe trace, the actual complete regular adjoint has a strictly
negative essential second-derivative pole rate. The actual denominator has its
cubic rate and the same probe is eventually nonzero. All coefficients and
traces are derived from the same global minimum, including the right signs. -/
theorem IsRecoverableAreaCompetitor.curvature_adjoint_zero_trace_second_pole_rates_of_minimum
    {C : ℝ} {K r p z : ℝ → ℝ} (hC : 1 ≤ C)
    (h : IsRecoverableAreaCompetitor C K r p z)
    (hr : ContinuousOn r (Ioo (0 : ℝ) 1))
    (hp : ContinuousOn p (Ioo (0 : ℝ) 1))
    (hmin : ∀ K' r' p' z' : ℝ → ℝ, IsRecoverableAreaCompetitor C K' r' p' z' →
      weakMeridionalAction K r p z ≤ weakMeridionalAction K' r' p' z') :
    let lam := weakMeridionalAction K r p z
    let f := warp K
    let b := warpSlope K
    let q := fun x => weakProbeEulerMomentum K r p z lam x / f x ^ 2
    let R := fun x => r (1 / 2) + ∫ s in (1 / 2 : ℝ)..x, p s
    let W := weakCurvatureAdjointRegularPart K r p z lam
    let D := fun x => 2 * f x * r x ^ 2
    ∃ qL qR : ℝ,
      Tendsto (fun x => q x + r x * (2 - b x) / (2 * f x)) (𝓝[>] 0) (𝓝 qL) ∧
      Tendsto (fun x => q x + r x * (2 + b x) / (2 * f x)) (𝓝[<] 1) (𝓝 qR) ∧
      ∀ t : ℝ, let H := fun x => W x - t * (x - 1 / 2)
        (R 0 = 0 → qL ≠ 0 ∧ (∀ᶠ x in 𝓝[>] (0 : ℝ), r x ≠ 0) ∧
          Tendsto (fun x => D x / x ^ 3) (𝓝[>] 0) (𝓝 (qL ^ 2 / 4)) ∧
          Tendsto (deriv (deriv H)) ((𝓝[>] (0 : ℝ)) ⊓ ae volume)
            (𝓝 (-3 * qL ^ 2 / 4))) ∧
        (R 1 = 0 → qR ≠ 0 ∧ (∀ᶠ x in 𝓝[<] (1 : ℝ), r x ≠ 0) ∧
          Tendsto (fun x => D x / (1 - x) ^ 3) (𝓝[<] 1) (𝓝 (qR ^ 2 / 4)) ∧
          Tendsto (deriv (deriv H)) ((𝓝[<] (1 : ℝ)) ⊓ ae volume)
            (𝓝 (-3 * qR ^ 2 / 4))) := by
  let lam := weakMeridionalAction K r p z
  let f := warp K
  let b := warpSlope K
  let q := fun x => weakProbeEulerMomentum K r p z lam x / f x ^ 2
  let P := weakProbeEulerFlux K r p z lam
  let R := fun x => r (1 / 2) + ∫ s in (1 / 2 : ℝ)..x, p s
  let W := weakCurvatureAdjointRegularPart K r p z lam
  let A := fun x => weakCurvatureWarpCoefficient K r p z x - lam * r x ^ 2
  let B := weakCurvatureSlopeCoefficient K r p z
  let J := fun x => (∫ s in x..1, (1 - s) * A s) - ∫ s in (0 : ℝ)..x, s * A s
  let F := fun x => 6 * f x * q x * p x - b x * f x * p x ^ 2 -
    3 * b x * q x * r x - 2 * P x * r x / f x + 2 * J x -
      2 * ∫ s in (0 : ℝ)..1, B s
  let S := fun x =>
    (2 * f x * p x ^ 2 + 6 * q x * r x - 4 * b x * r x * p x +
        b x ^ 2 * r x ^ 2 / (2 * f x)) * K x +
      3 * b x ^ 2 * p x ^ 2 - 3 * b x * q x * p x +
        4 * P x * p x / f x - b x * P x * r x / f x ^ 2
  have hC0 : 0 < C := zero_lt_one.trans_le hC
  have hg := h.geometry_bounds hC
  obtain ⟨qL, qR, hQL, hQR, hL, hR⟩ :=
    h.probe_zero_trace_leading_rates_of_minimum hC hr hp hmin
  obtain ⟨_, _, _, hReq, _, hrLT, hrRT, _⟩ :=
    h.probe_pole_integrability_of_minimum hC hr hp hmin
  change EqOn R r (Ioo (0 : ℝ) 1) at hReq
  change Tendsto r (𝓝[>] 0) (𝓝 (R 0)) at hrLT
  change Tendsto r (𝓝[<] 1) (𝓝 (R 1)) at hrRT
  obtain ⟨_, _, hEL, hER⟩ := h.polar_corrected_flux_bounds_of_minimum hC hr hp hmin
  change Tendsto (fun x => (P x - (2 - b x) * b x * R x / 2) / x)
    (𝓝[>] 0) (𝓝 0) at hEL
  change Tendsto (fun x => (P x - (2 + b x) * b x * R x / 2) / (1 - x))
    (𝓝[<] 1) (𝓝 0) at hER
  have hwarp := h.primitive_first_order_pole_rates hC
  have hslope := (h.slope_pole_quotient_bounds hC).2
  have hLD : ∀ᶠ x in 𝓝[>] (0 : ℝ), x ∈ Ioo (0 : ℝ) 1 := Ioo_mem_nhdsGT zero_lt_one
  have hRD : ∀ᶠ x in 𝓝[<] (1 : ℝ), x ∈ Ioo (0 : ℝ) 1 := Ioo_mem_nhdsLT zero_lt_one
  have hbL : Tendsto b (𝓝[>] 0) (𝓝 2) := by
    simpa only [b, hg.2.2.2.1.2.2.1] using
      ((hg.2.1.continuousWithinAt ⟨le_rfl, zero_le_one⟩).mono_of_mem_nhdsWithin
        (Icc_mem_nhdsGT zero_lt_one)).tendsto
  have hbR : Tendsto b (𝓝[<] 1) (𝓝 (-2)) := by
    simpa only [b, hg.2.2.2.1.2.2.2] using
      ((hg.2.1.continuousWithinAt ⟨zero_le_one, le_rfl⟩).mono_of_mem_nhdsWithin
        (Icc_mem_nhdsLT zero_lt_one)).tendsto
  have hKB : ∀ᵐ x ∂areaμ, |K x| ≤ 2 * C := by
    filter_upwards [hg.2.2.2.2] with x hx
    rw [abs_of_nonneg ((by positivity : (0 : ℝ) ≤ 2 / C).trans hx.1)]
    exact hx.2
  have hKL : ∀ᶠ x in (𝓝[>] (0 : ℝ)) ⊓ ae volume, |K x| ≤ 2 * C := by
    filter_upwards [hLD.filter_mono inf_le_left,
      (ae_imp_of_ae_restrict hKB).filter_mono inf_le_right] with x hx hKx
    exact hKx hx
  have hKR : ∀ᶠ x in (𝓝[<] (1 : ℝ)) ⊓ ae volume, |K x| ≤ 2 * C := by
    filter_upwards [hRD.filter_mono inf_le_left,
      (ae_imp_of_ae_restrict hKB).filter_mono inf_le_right] with x hx hKx
    exact hKx hx
  have hregular := h.curvature_adjoint_regularPart_of_minimum hC hr hp hmin
  have hWD := hregular.2.2.1
  have hSD := hregular.2.2.2.2
  change (∀ x ∈ Ioo (0 : ℝ) 1, HasDerivAt W (F x) x) at hWD
  change (∀ᵐ x ∂areaμ, HasDerivAt F (S x) x) at hSD
  refine ⟨qL, qR, hQL, hQR, ?_⟩
  intro t
  let H := fun x => W x - t * (x - 1 / 2)
  have hHD (x : ℝ) (hx : x ∈ Ioo (0 : ℝ) 1) : HasDerivAt H (F x - t) x := by
    simpa only [H, id_eq, mul_one] using (hWD x hx).fun_sub
      (((hasDerivAt_id x).sub_const (1 / 2 : ℝ)).const_mul t)
  have hSecond : ∀ᵐ x ∂areaμ, HasDerivAt (deriv H) (S x) x := by
    filter_upwards [hSD, ae_restrict_mem measurableSet_Ioo] with x hx hxI
    have he : deriv H =ᶠ[𝓝 x] (fun y => F y - t) :=
      (show ∀ᶠ y in 𝓝 x, y ∈ Ioo (0 : ℝ) 1 from isOpen_Ioo.mem_nhds hxI).mono
        (fun y hy => (hHD y hy).deriv)
    exact (hx.sub_const t).congr_of_eventuallyEq he
  constructor
  · intro hR0
    change R 0 = 0 at hR0
    obtain ⟨hqne, hqL, hpL, hrL⟩ := hL hR0
    have hr0 : Tendsto r (𝓝[>] (0 : ℝ)) (𝓝 0) := by simpa only [hR0] using hrLT
    have hRlim : Tendsto R (𝓝[>] (0 : ℝ)) (𝓝 0) :=
      hr0.congr' (hLD.mono fun x hx => (hReq hx).symm)
    have hP0 : Tendsto (fun x => P x / x) (𝓝[>] 0) (𝓝 0) :=
      zero_trace_flux_div_limit hEL hRlim hbL (hLD.mono fun x hx => (hslope x hx).1)
    have hdist : Tendsto (fun x : ℝ => x) (𝓝[>] 0) (𝓝 0) :=
      tendsto_id.mono_left nhdsWithin_le_nhds
    have hdistn : ∀ᶠ x in 𝓝[>] (0 : ℝ), x ≠ 0 := hLD.mono fun _ hx => hx.1.ne'
    have hNode := node_free_and_cubic_rate hqne hdistn hwarp.1 hrL
    refine ⟨hqne, hNode.1, hNode.2, ?_⟩
    have hs := adjoint_second_density_tendsto (hdist.mono_left inf_le_left)
      (hdistn.filter_mono inf_le_left) (hwarp.1.mono_left inf_le_left)
      (hbL.mono_left inf_le_left) (hqL.mono_left inf_le_left) (hpL.mono_left inf_le_left)
      (hrL.mono_left inf_le_left) (hP0.mono_left inf_le_left) hKL
    have hs' : Tendsto S ((𝓝[>] (0 : ℝ)) ⊓ ae volume) (𝓝 (-3 * qL ^ 2 / 4)) := by
      convert hs using 1
      congr 1
      ring
    apply hs'.congr'
    filter_upwards [hLD.filter_mono inf_le_left,
      (ae_imp_of_ae_restrict hSecond).filter_mono inf_le_right] with x hx hDx
    exact (hDx hx).deriv.symm
  · intro hR1
    change R 1 = 0 at hR1
    obtain ⟨hqne, hqR, hpR, hrR⟩ := hR hR1
    have hr1 : Tendsto r (𝓝[<] (1 : ℝ)) (𝓝 0) := by simpa only [hR1] using hrRT
    have hRlim : Tendsto R (𝓝[<] (1 : ℝ)) (𝓝 0) :=
      hr1.congr' (hRD.mono fun x hx => (hReq hx).symm)
    have hP1 : Tendsto (fun x => P x / (1 - x)) (𝓝[<] 1) (𝓝 0) :=
      zero_trace_flux_div_limit hER hRlim hbR (hRD.mono fun x hx => (hslope x hx).2)
    have hdist : Tendsto (fun x : ℝ => 1 - x) (𝓝[<] 1) (𝓝 0) := by
      simpa only [sub_self] using
        (tendsto_const_nhds.sub (tendsto_id.mono_left nhdsWithin_le_nhds) :
          Tendsto (fun x : ℝ => 1 - x) (𝓝[<] 1) (𝓝 (1 - 1)))
    have hdistn : ∀ᶠ x in 𝓝[<] (1 : ℝ), 1 - x ≠ 0 :=
      hRD.mono fun _ hx => (sub_pos.mpr hx.2).ne'
    have hNode := node_free_and_cubic_rate hqne hdistn hwarp.2 hrR
    refine ⟨hqne, hNode.1, hNode.2, ?_⟩
    have hs := adjoint_second_density_tendsto (hdist.mono_left inf_le_left)
      (hdistn.filter_mono inf_le_left) (hwarp.2.mono_left inf_le_left)
      (hbR.mono_left inf_le_left) (hqR.mono_left inf_le_left) (hpR.mono_left inf_le_left)
      (hrR.mono_left inf_le_left) (hP1.mono_left inf_le_left) hKR
    have hs' : Tendsto S ((𝓝[<] (1 : ℝ)) ⊓ ae volume) (𝓝 (-3 * qR ^ 2 / 4)) := by
      convert hs using 1
      congr 1
      ring
    apply hs'.congr'
    filter_upwards [hRD.filter_mono inf_le_left,
      (ae_imp_of_ae_restrict hSecond).filter_mono inf_le_right] with x hx hDx
    exact (hDx hx).deriv.symm

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

/-- Genuine endpoint FTC gives the quadratic remainder of the same centered
regular adjoint at either zero probe trace. Its coefficient is nonzero and
negative; the right linear coefficient has the inward orientation. -/
theorem IsRecoverableAreaCompetitor.curvature_adjoint_zero_trace_quadratic_pole_rates_of_minimum
    {C : ℝ} {K r p z : ℝ → ℝ} (hC : 1 ≤ C)
    (h : IsRecoverableAreaCompetitor C K r p z)
    (hr : ContinuousOn r (Ioo (0 : ℝ) 1))
    (hp : ContinuousOn p (Ioo (0 : ℝ) 1))
    (hmin : ∀ K' r' p' z' : ℝ → ℝ, IsRecoverableAreaCompetitor C K' r' p' z' →
      weakMeridionalAction K r p z ≤ weakMeridionalAction K' r' p' z') :
    let lam := weakMeridionalAction K r p z
    let f := warp K
    let b := warpSlope K
    let q := fun x => weakProbeEulerMomentum K r p z lam x / f x ^ 2
    let R := fun x => r (1 / 2) + ∫ s in (1 / 2 : ℝ)..x, p s
    let W := weakCurvatureAdjointRegularPart K r p z lam
    let A := fun x => weakCurvatureWarpCoefficient K r p z x - lam * r x ^ 2
    let B := weakCurvatureSlopeCoefficient K r p z
    let D := fun x => 2 * f x * r x ^ 2
    ∃ qL qR : ℝ,
      Tendsto (fun x => q x + r x * (2 - b x) / (2 * f x)) (𝓝[>] 0) (𝓝 qL) ∧
      Tendsto (fun x => q x + r x * (2 + b x) / (2 * f x)) (𝓝[<] 1) (𝓝 qR) ∧
      ∀ t : ℝ, let H := fun x => W x - t * (x - 1 / 2)
        let LL := 2 * (∫ s in (0 : ℝ)..1, (1 - s) * A s) -
          2 * (∫ s in (0 : ℝ)..1, B s) - t
        let LR := -2 * (∫ s in (0 : ℝ)..1, s * A s) -
          2 * (∫ s in (0 : ℝ)..1, B s) - t
        (R 0 = 0 → qL ≠ 0 ∧ (∀ᶠ x in 𝓝[>] (0 : ℝ), r x ≠ 0) ∧
          Tendsto (fun x => D x / x ^ 3) (𝓝[>] 0) (𝓝 (qL ^ 2 / 4)) ∧
          Tendsto (deriv (deriv H)) ((𝓝[>] (0 : ℝ)) ⊓ ae volume)
            (𝓝 (-3 * qL ^ 2 / 4)) ∧
          Tendsto (fun x => (H x - t / 2 - LL * x) / x ^ 2) (𝓝[>] 0)
            (𝓝 (-3 * qL ^ 2 / 8))) ∧
        (R 1 = 0 → qR ≠ 0 ∧ (∀ᶠ x in 𝓝[<] (1 : ℝ), r x ≠ 0) ∧
          Tendsto (fun x => D x / (1 - x) ^ 3) (𝓝[<] 1) (𝓝 (qR ^ 2 / 4)) ∧
          Tendsto (deriv (deriv H)) ((𝓝[<] (1 : ℝ)) ⊓ ae volume)
            (𝓝 (-3 * qR ^ 2 / 4)) ∧
          Tendsto (fun x => (H x + t / 2 + LR * (1 - x)) / (1 - x) ^ 2) (𝓝[<] 1)
            (𝓝 (-3 * qR ^ 2 / 8))) := by
  let lam := weakMeridionalAction K r p z
  let f := warp K
  let b := warpSlope K
  let q := fun x => weakProbeEulerMomentum K r p z lam x / f x ^ 2
  let P := weakProbeEulerFlux K r p z lam
  let R := fun x => r (1 / 2) + ∫ s in (1 / 2 : ℝ)..x, p s
  let W := weakCurvatureAdjointRegularPart K r p z lam
  let A := fun x => weakCurvatureWarpCoefficient K r p z x - lam * r x ^ 2
  let B := weakCurvatureSlopeCoefficient K r p z
  let J := fun x => (∫ s in x..1, (1 - s) * A s) - ∫ s in (0 : ℝ)..x, s * A s
  let F := fun x => 6 * f x * q x * p x - b x * f x * p x ^ 2 -
    3 * b x * q x * r x - 2 * P x * r x / f x + 2 * J x -
      2 * ∫ s in (0 : ℝ)..1, B s
  obtain ⟨qL, qR, hQL, hQR, hSecond⟩ :=
    h.curvature_adjoint_zero_trace_second_pole_rates_of_minimum hC hr hp hmin
  have hTraces := h.curvature_adjoint_pole_traces_of_minimum hC hr hp hmin
  obtain ⟨_, qA, qB, _, _, hRate⟩ :=
    h.curvature_adjoint_polar_derivative_rate_of_minimum hC hr hp hmin
  have hReg := h.curvature_adjoint_regularPart_of_minimum hC hr hp hmin
  have hWD := hReg.2.2.1
  have hFAC := hReg.2.2.2.1
  have hFSD := hReg.2.2.2.2
  change (∀ x ∈ Ioo (0 : ℝ) 1, HasDerivAt W (F x) x) at hWD
  change (∀ a ∈ Ioo (0 : ℝ) 1, ∀ c ∈ Ioo (0 : ℝ) 1,
    AbsolutelyContinuousOnInterval F a c) at hFAC
  refine ⟨qL, qR, hQL, hQR, ?_⟩
  intro t
  let H := fun x => W x - t * (x - 1 / 2)
  let LL := 2 * (∫ s in (0 : ℝ)..1, (1 - s) * A s) -
    2 * (∫ s in (0 : ℝ)..1, B s) - t
  let LR := -2 * (∫ s in (0 : ℝ)..1, s * A s) -
    2 * (∫ s in (0 : ℝ)..1, B s) - t
  have hHD (x : ℝ) (hx : x ∈ Ioo (0 : ℝ) 1) : HasDerivAt H (F x - t) x := by
    simpa only [H, id_eq, mul_one] using (hWD x hx).fun_sub
      (((hasDerivAt_id x).sub_const (1 / 2 : ℝ)).const_mul t)
  have hEq (x : ℝ) (hx : x ∈ Ioo (0 : ℝ) 1) : deriv H x = F x - t := (hHD x hx).deriv
  have hVAC (a : ℝ) (ha : a ∈ Ioo (0 : ℝ) 1) (c : ℝ) (hc : c ∈ Ioo (0 : ℝ) 1) :
      AbsolutelyContinuousOnInterval (deriv H) a c := by
    have ht : AbsolutelyContinuousOnInterval (fun _ : ℝ => t) a c :=
      (contDiff_const : ContDiff ℝ 1 (fun _ : ℝ => t)).contDiffOn.absolutelyContinuousOnInterval
    apply ((hFAC a ha c hc).fun_sub ht).congr
    intro x hx
    exact (hEq x (ordConnected_Ioo.uIcc_subset ha hc hx)).symm
  have hVD : ∀ᵐ x ∂areaμ, HasDerivAt (deriv H) (deriv (deriv H) x) x := by
    filter_upwards [hFSD, ae_restrict_mem measurableSet_Ioo] with x hx hxI
    change HasDerivAt F _ x at hx
    have he : deriv H =ᶠ[𝓝 x] (fun y => F y - t) :=
      (show ∀ᶠ y in 𝓝 x, y ∈ Ioo (0 : ℝ) 1 from isOpen_Ioo.mem_nhds hxI).mono
        (fun y hy => hEq y hy)
    exact ((hx.sub_const t).congr_of_eventuallyEq he).differentiableAt.hasDerivAt
  have hHact (x : ℝ) (hx : x ∈ Ioo (0 : ℝ) 1) : HasDerivAt H (deriv H x) x :=
    (hHD x hx).differentiableAt.hasDerivAt
  constructor
  · intro hR0
    change R 0 = 0 at hR0
    have hc := (hSecond t).1 hR0
    refine ⟨hc.1, hc.2.1, hc.2.2.1, hc.2.2.2, ?_⟩
    have hHT := (hTraces.2.2 t).1
    change Tendsto H (𝓝[>] 0) (𝓝 (-2 * R 0 ^ 2 + t / 2)) at hHT
    have hH0 : Tendsto H (𝓝[>] (0 : ℝ)) (𝓝 (t / 2)) := by
      simpa only [hR0, zero_pow (by decide : (2 : ℕ) ≠ 0), mul_zero, zero_add] using hHT
    have hVT := (hRate t).1
    change Tendsto (fun x => deriv H x - R 0 ^ 2 * (2 - b x) / f x) (𝓝[>] 0)
      (𝓝 (-6 * R 0 * qA + 2 * (∫ s in (0 : ℝ)..1, (1 - s) * A s) -
        2 * (∫ s in (0 : ℝ)..1, B s) - t)) at hVT
    have he : -6 * R 0 * qA + 2 * (∫ s in (0 : ℝ)..1, (1 - s) * A s) -
        2 * (∫ s in (0 : ℝ)..1, B s) - t = LL := by
      rw [hR0]
      dsimp only [LL]
      ring
    rw [he] at hVT
    have hV0 : Tendsto (deriv H) (𝓝[>] (0 : ℝ)) (𝓝 LL) := by
      simpa only [hR0, zero_pow (by decide : (2 : ℕ) ≠ 0), zero_mul,
        zero_div, sub_zero] using hVT
    have hquad := Analysis.tendsto_quadratic_remainder_of_ae_second_derivative_limit
      zero_lt_one hHact hVAC hVD hH0 hV0 hc.2.2.2
    convert hquad using 1
    congr 1
    ring
  · intro hR1
    change R 1 = 0 at hR1
    have hc := (hSecond t).2 hR1
    refine ⟨hc.1, hc.2.1, hc.2.2.1, hc.2.2.2, ?_⟩
    have hHT := (hTraces.2.2 t).2
    change Tendsto H (𝓝[<] 1) (𝓝 (-2 * R 1 ^ 2 - t / 2)) at hHT
    have hH1 : Tendsto H (𝓝[<] (1 : ℝ)) (𝓝 (-t / 2)) := by
      simpa only [hR1, zero_pow (by decide : (2 : ℕ) ≠ 0), mul_zero, zero_sub,
        neg_div] using hHT
    have hVT := (hRate t).2
    change Tendsto (fun x => deriv H x + R 1 ^ 2 * (2 + b x) / f x) (𝓝[<] 1)
      (𝓝 (6 * R 1 * qB - 2 * (∫ s in (0 : ℝ)..1, s * A s) -
        2 * (∫ s in (0 : ℝ)..1, B s) - t)) at hVT
    have he : 6 * R 1 * qB - 2 * (∫ s in (0 : ℝ)..1, s * A s) -
        2 * (∫ s in (0 : ℝ)..1, B s) - t = LR := by
      rw [hR1]
      dsimp only [LR]
      ring
    rw [he] at hVT
    have hV1 : Tendsto (deriv H) (𝓝[<] (1 : ℝ)) (𝓝 LR) := by
      simpa only [hR1, zero_pow (by decide : (2 : ℕ) ≠ 0), zero_mul,
        zero_div, add_zero] using hVT
    let HR := fun x => H (1 - x)
    let VR := fun x => -deriv H (1 - x)
    let AR := fun x => deriv (deriv H) (1 - x)
    have href (x : ℝ) (hx : x ∈ Ioo (0 : ℝ) 1) : 1 - x ∈ Ioo (0 : ℝ) 1 :=
      ⟨sub_pos.mpr hx.2, by linarith [hx.1]⟩
    have hHRD (x : ℝ) (hx : x ∈ Ioo (0 : ℝ) 1) : HasDerivAt HR (VR x) x := by
      simpa only [HR, VR, Function.comp_def, zero_sub, mul_neg_one, id_eq] using
        (hHact (1 - x) (href x hx)).comp x
          ((hasDerivAt_const x (1 : ℝ)).fun_sub (hasDerivAt_id x))
    have hVRAC (a : ℝ) (ha : a ∈ Ioo (0 : ℝ) 1) (c : ℝ) (hc' : c ∈ Ioo (0 : ℝ) 1) :
        AbsolutelyContinuousOnInterval VR a c := by
      simpa only [VR, sub_sub_cancel] using
        (Analysis.absolutelyContinuousOnInterval_comp_sub_left (c := 1)
          (hVAC (1 - c) (href c hc') (1 - a) (href a ha))).fun_neg
    have hVRD : ∀ᵐ x ∂areaμ, HasDerivAt VR (AR x) x := by
      have hh := (volume.measurePreserving_sub_left 1).quasiMeasurePreserving.ae
        (ae_imp_of_ae_restrict hVD)
      filter_upwards [hh.filter_mono (ae_mono Measure.restrict_le_self),
        ae_restrict_mem measurableSet_Ioo] with x hx hxI
      have hd := ((hx (href x hxI)).comp x
        ((hasDerivAt_const x (1 : ℝ)).fun_sub (hasDerivAt_id x))).fun_neg
      simpa only [VR, AR, Function.comp_def, zero_sub, mul_neg_one, neg_neg, id_eq] using hd
    have hRefAE : Tendsto (fun x : ℝ => 1 - x)
        ((𝓝[>] (0 : ℝ)) ⊓ ae volume) ((𝓝[<] (1 : ℝ)) ⊓ ae volume) := by
      apply tendsto_inf.mpr
      exact ⟨reflect_right_zero.mono_left inf_le_left,
        (volume.measurePreserving_sub_left 1).quasiMeasurePreserving.tendsto_ae.mono_left
          inf_le_right⟩
    have hVR0 : Tendsto VR (𝓝[>] (0 : ℝ)) (𝓝 (-LR)) := by
      simpa only [VR, Function.comp_def] using hV1.neg.comp reflect_right_zero
    have hquad := Analysis.tendsto_quadratic_remainder_of_ae_second_derivative_limit
      zero_lt_one hHRD hVRAC hVRD (hH1.comp reflect_right_zero) hVR0
      (hc.2.2.2.comp hRefAE)
    convert hquad.comp reflect_left_one using 1
    · funext x
      dsimp only [HR, Function.comp_def]
      rw [sub_sub_cancel]
      ring
    · congr 1
      ring

end RicciFlowSharpEstimate.Geometry.AreaProfile
