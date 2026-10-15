/-
Copyright (c) 2026 Ziyang Qin. All rights reserved.
No license is granted by this file.
Authors: Ziyang Qin
-/
import RicciFlowSharpEstimate.Geometry.WeakProbePoleTraces
import RicciFlowSharpEstimate.Geometry.WeakProbeDerivativeFlux
import RicciFlowSharpEstimate.Analysis.ZeroBoundaryExtension

/-! # Zero pole traces of the actual weighted minimizing states -/

noncomputable section
namespace RicciFlowSharpEstimate.Geometry.AreaProfile
open Set MeasureTheory Filter Topology
local notation "areaμ" => volume.restrict (Ioo (0 : ℝ) 1)

private theorem warp_product_div_integrable
    {C : ℝ} {K r p z u : ℝ → ℝ} (hC : 1 ≤ C)
    (h : IsRecoverableAreaCompetitor C K r p z) (hu : Integrable u areaμ) :
    Integrable (fun x => warp K x * u x / x) areaμ ∧
      Integrable (fun x => warp K x * u x / (1 - x)) areaμ := by
  have hg := h.geometry_bounds hC
  have hfM : AEStronglyMeasurable (warp K) areaμ :=
    (hg.1.mono Ioo_subset_Icc_self).aestronglyMeasurable measurableSet_Ioo
  have hC0 : 0 < C := zero_lt_one.trans_le hC
  have hb : ∀ᵐ x ∂areaμ,
      ‖warp K x / x‖ ≤ 2 * C ∧ ‖warp K x / (1 - x)‖ ≤ 2 * C := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
    have hgx := hg.2.2.1 x ⟨hx.1.le, hx.2.le⟩
    have hf0 : 0 ≤ warp K x :=
      (mul_nonneg (mul_nonneg (by positivity) hx.1.le) (by linarith [hx.2])).trans hgx.1
    rw [Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg (div_nonneg hf0 hx.1.le),
      abs_of_nonneg (div_nonneg hf0 (by linarith [hx.2]))]
    constructor
    · apply (div_le_iff₀ hx.1).mpr
      exact hgx.2.1.trans (by nlinarith [mul_nonneg (by positivity : 0 ≤ 2 * C) (sq_nonneg x)])
    · apply (div_le_iff₀ (sub_pos.mpr hx.2)).mpr
      exact hgx.2.1.trans (by
        nlinarith [mul_nonneg (by positivity : 0 ≤ 2 * C) (sq_nonneg (1 - x))])
  constructor
  · apply (hu.bdd_mul (hfM.div₀ continuous_id.aestronglyMeasurable)
      (hb.mono fun _ hx => hx.1)).congr
    filter_upwards [] with x
    change warp K x / x * u x = warp K x * u x / x
    ring
  · apply (hu.bdd_mul
      (hfM.div₀ (continuous_const.sub continuous_id).aestronglyMeasurable)
      (hb.mono fun _ hx => hx.2)).congr
    filter_upwards [] with x
    change warp K x / (1 - x) * u x = warp K x * u x / (1 - x)
    ring

private theorem euler_flux_div_warp_integrable
    {C : ℝ} {K r p z : ℝ → ℝ} (hC : 1 ≤ C)
    (h : IsRecoverableAreaCompetitor C K r p z)
    (hmin : ∀ K' r' p' z' : ℝ → ℝ, IsRecoverableAreaCompetitor C K' r' p' z' →
      weakMeridionalAction K r p z ≤ weakMeridionalAction K' r' p' z') :
    Integrable (fun x => weakProbeEulerFlux K r p z (weakMeridionalAction K r p z) x /
      warp K x) areaμ := by
  let P := weakProbeEulerFlux K r p z (weakMeridionalAction K r p z)
  let w := fun x : ℝ => x * (1 - x)
  have hg := h.geometry_bounds hC
  have hC0 : 0 < C := zero_lt_one.trans_le hC
  obtain ⟨_, hPAC, _, hP0, hP1, _, _, hPD, _⟩ :=
    h.probe_euler_flux_of_minimum hC hmin
  have hPM : MemLp (deriv P) 2 areaμ := by
    apply (h.probe_zeroth_coefficient_memLp_two hC (weakMeridionalAction K r p z)).neg.ae_eq
    exact hPD.mono fun x hx => hx.deriv.symm
  have hPQ :=
    Analysis.AbsolutelyContinuousOnInterval.integrable_div_endpoints_of_deriv_memLp_two
      hPAC hP0 hP1 hPM
  have hPL : Integrable (fun x => P x / x) areaμ := by
    change IntegrableOn (fun x => P x / x) (Ioo (0 : ℝ) 1) volume
    simpa only [sub_zero] using hPQ.1
  have hPw : Integrable (fun x => P x / w x) areaμ := by
    apply (hPL.add hPQ.2).congr
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
    change P x / x + P x / (1 - x) = P x / w x
    dsimp only [w]
    field_simp [hx.1.ne', (sub_pos.mpr hx.2).ne']; ring
  have hfM : AEStronglyMeasurable (warp K) areaμ :=
    (hg.1.mono Ioo_subset_Icc_self).aestronglyMeasurable measurableSet_Ioo
  have hdM : AEStronglyMeasurable (fun x => w x / warp K x) areaμ :=
    (continuous_id.mul (continuous_const.sub continuous_id)).aestronglyMeasurable.div₀ hfM
  have hdB : ∀ᵐ x ∂areaμ, ‖w x / warp K x‖ ≤ C / 2 := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
    have hw0 : 0 < w x := mul_pos hx.1 (sub_pos.mpr hx.2)
    have hlo : (2 / C) * w x ≤ warp K x := by
      simpa only [w, mul_assoc] using (hg.2.2.1 x ⟨hx.1.le, hx.2.le⟩).1
    have hf0 : 0 < warp K x := (mul_pos (by positivity) hw0).trans_le hlo
    rw [Real.norm_eq_abs, abs_of_pos (div_pos hw0 hf0)]
    apply (div_le_iff₀ hf0).mpr
    have hh := mul_le_mul_of_nonneg_left hlo (by positivity : 0 ≤ C / 2)
    have heq : C / 2 * ((2 / C) * w x) = w x := by field_simp [hC0.ne']
    rwa [heq] at hh
  apply (hPw.bdd_mul hdM hdB).congr
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
  change (w x / warp K x) * (P x / w x) = P x / warp K x
  have hwne : w x ≠ 0 := (mul_pos hx.1 (sub_pos.mpr hx.2)).ne'
  field_simp [hwne]

private theorem ac_from_zero_extension {u : ℝ → ℝ}
    (h0 : u 0 = 0) (h1 : u 1 = 0)
    (h : ∃ U : ℝ → ℝ, AbsolutelyContinuousOnInterval U 0 1 ∧
      EqOn U u (Ioo (0 : ℝ) 1) ∧ U 0 = 0 ∧ U 1 = 0 ∧
      Tendsto u (𝓝[>] 0) (𝓝 0) ∧ Tendsto u (𝓝[<] 1) (𝓝 0)) :
    AbsolutelyContinuousOnInterval u 0 1 ∧
      Tendsto u (𝓝[>] 0) (𝓝 0) ∧ Tendsto u (𝓝[<] 1) (𝓝 0) := by
  obtain ⟨U, hAC, hEq, hU0, hU1, hLT, hRT⟩ := h
  refine ⟨hAC.congr ?_, hLT, hRT⟩
  rw [uIcc_of_le zero_le_one]
  intro x hx
  by_cases hx0 : x = 0
  · simp only [hx0, hU0, h0]
  by_cases hx1 : x = 1
  · simp only [hx1, hU1, h1]
  exact hEq ⟨lt_of_le_of_ne hx.1 (Ne.symm hx0), lt_of_le_of_ne hx.2 hx1⟩

/-- Both actual weighted minimizing states extend absolutely continuously
through the physical poles with zero traces. The operator state uses the
canonical momentum quotient, not a pointwise assertion about a raw a.e. class. -/
theorem IsRecoverableAreaCompetitor.probe_weighted_state_pole_traces_of_minimum
    {C : ℝ} {K r p z : ℝ → ℝ} (hC : 1 ≤ C)
    (h : IsRecoverableAreaCompetitor C K r p z)
    (hp : ContinuousOn p (Ioo (0 : ℝ) 1))
    (hmin : ∀ K' r' p' z' : ℝ → ℝ, IsRecoverableAreaCompetitor C K' r' p' z' →
      weakMeridionalAction K r p z ≤ weakMeridionalAction K' r' p' z') :
    let f := warp K
    let q := fun x => weakProbeEulerMomentum K r p z (weakMeridionalAction K r p z) x /
      f x ^ 2
    AbsolutelyContinuousOnInterval (fun x => f x * p x) 0 1 ∧
      AbsolutelyContinuousOnInterval (fun x => f x * q x) 0 1 ∧
      Tendsto (fun x => f x * p x) (𝓝[>] 0) (𝓝 0) ∧
      Tendsto (fun x => f x * p x) (𝓝[<] 1) (𝓝 0) ∧
      Tendsto (fun x => f x * q x) (𝓝[>] 0) (𝓝 0) ∧
      Tendsto (fun x => f x * q x) (𝓝[<] 1) (𝓝 0) := by
  let f := warp K
  let b := warpSlope K
  let P := weakProbeEulerFlux K r p z (weakMeridionalAction K r p z)
  let q := fun x => weakProbeEulerMomentum K r p z (weakMeridionalAction K r p z) x / f x ^ 2
  let vp := fun x => q x + K x * r x - b x * p x
  let vq := fun x => b x * q x + P x / f x - K x * b x * r x / 2
  have hg := h.geometry_bounds hC
  have hC0 : 0 < C := zero_lt_one.trans_le hC
  obtain ⟨hUA, _, hAAC, _, _, _, _, _, hAD, _, hqeq⟩ :=
    h.probe_euler_flux_of_minimum hC hmin
  have hQI := h.weak_operator_integrable_of_minimum hC hmin
  have hqI : Integrable q areaμ := hQI.congr hqeq
  have hrI := h.2.1.memLp.integrable (by norm_num : (1 : ENNReal) ≤ 2)
  have hbM : AEStronglyMeasurable b areaμ :=
    (hg.2.1.mono Ioo_subset_Icc_self).aestronglyMeasurable measurableSet_Ioo
  have hbB : ∀ᵐ x ∂areaμ, ‖b x‖ ≤ 2 := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
    exact (hg.2.2.1 x ⟨hx.1.le, hx.2.le⟩).2.2
  have hKB : ∀ᵐ x ∂areaμ, ‖K x‖ ≤ 2 * C := by
    filter_upwards [hg.2.2.2.2] with x hx
    rw [Real.norm_eq_abs, abs_of_nonneg ((by positivity : (0 : ℝ) ≤ 2 / C).trans hx.1)]
    exact hx.2
  have hfM : AEStronglyMeasurable (warp K) areaμ :=
    (hg.1.mono Ioo_subset_Icc_self).aestronglyMeasurable measurableSet_Ioo
  have hrKI := hrI.bdd_mul h.1.aestronglyMeasurable hKB
  have hSI := hQI.add hrKI
  obtain ⟨hFAC, hF0, hF1, hFD⟩ := h.derivative_flux_absolutelyContinuous hC hp
  have hfbounds : ∀ᵐ x ∂areaμ,
      (2 / C) * (x * (1 - x)) ≤ f x ∧ f x ≤ (2 * C) * (x * (1 - x)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
    have hh := hg.2.2.1 x ⟨hx.1.le, hx.2.le⟩
    exact ⟨by simpa only [mul_assoc] using hh.1,
      by simpa only [mul_assoc] using hh.2.1⟩
  have hpI := Analysis.integrable_of_parabolic_divergence_flux hfM
    (by positivity : 0 < 2 / C) hfbounds hFAC hF0 hF1
      (Eventually.of_forall fun _ => rfl) hFD hSI
  have hvp : Integrable vp areaμ :=
    (hqI.add (hrI.bdd_mul h.1.aestronglyMeasurable hKB)).sub (hpI.bdd_mul hbM hbB)
  have hvq : Integrable vq areaμ := by
    apply (((hqI.bdd_mul hbM hbB).add (euler_flux_div_warp_integrable hC h hmin)).sub
      (((hrI.bdd_mul h.1.aestronglyMeasurable hKB).bdd_mul hbM hbB).div_const 2)).congr
    filter_upwards [] with x
    change b x * q x + P x / f x - b x * (K x * r x) / 2 = vq x
    dsimp only [vq]
    ring
  have hfD := (h.primitive_local_regularity hC).1
  have hfCD : ContDiffOn ℝ 1 f (Ioo (0 : ℝ) 1) :=
    (h.primitive_weak_derivatives hC).1.contDiffOn_one_of_continuousOn
      (hg.1.mono Ioo_subset_Icc_self) (hg.2.1.mono Ioo_subset_Icc_self)
  have hfne (x : ℝ) (hx : x ∈ Ioo (0 : ℝ) 1) : f x ≠ 0 := by
    exact ne_of_gt ((mul_pos (mul_pos (by positivity : (0 : ℝ) < 2 / C) hx.1)
      (sub_pos.mpr hx.2)).trans_le (hg.2.2.1 x ⟨hx.1.le, hx.2.le⟩).1)
  have hpAC (a : ℝ) (ha : a ∈ Ioo (0 : ℝ) 1)
      (d : ℝ) (hd : d ∈ Ioo (0 : ℝ) 1) :
      AbsolutelyContinuousOnInterval (fun x => f x * p x) a d :=
    ((hfCD.mono (ordConnected_Ioo.uIcc_subset ha hd)).absolutelyContinuousOnInterval).fun_mul
      (h.2.1.weakDeriv_deriv.absolutelyContinuousOnInterval hp ha hd)
  have hqAC (a : ℝ) (ha : a ∈ Ioo (0 : ℝ) 1)
      (d : ℝ) (hd : d ∈ Ioo (0 : ℝ) 1) :
      AbsolutelyContinuousOnInterval (fun x => f x * q x) a d :=
    ((hfCD.mono (ordConnected_Ioo.uIcc_subset ha hd)).absolutelyContinuousOnInterval).fun_mul
      (by
        have hab := ordConnected_Ioo.uIcc_subset ha hd
        have hAad := hAAC.mono (show uIcc a d ⊆ uIcc (0 : ℝ) 1 by
          simpa only [uIcc_of_le zero_le_one] using hab.trans Ioo_subset_Icc_self)
        have hInv : ContDiffOn ℝ 1 (fun x => (f x ^ 2)⁻¹) (uIcc a d) :=
          ((hfCD.pow 2).inv (fun x hx => pow_ne_zero 2 (hfne x hx))).mono hab
        simpa only [q, f, Pi.mul_def, div_eq_mul_inv] using
          hAad.mul hInv.absolutelyContinuousOnInterval)
  have hpD : ∀ᵐ x ∂areaμ, HasDerivAt (fun x => f x * p x) (vp x) x := by
    filter_upwards [h.2.1.weakDeriv_deriv.ae_hasDerivAt_of_continuousOn hp,
      hqeq, ae_restrict_mem measurableSet_Ioo] with x hx hqx hxI
    apply ((hfD x hxI).fun_mul hx).congr_deriv
    change weakMeridionalOperator K r p z x = q x at hqx
    dsimp only [weakMeridionalOperator] at hqx
    dsimp only [vp, f, b]
    nlinarith only [hqx]
  have hqD : ∀ᵐ x ∂areaμ, HasDerivAt (fun x => f x * q x) (vq x) x := by
    filter_upwards [hUA, hAD, hqeq, ae_restrict_mem measurableSet_Ioo]
      with x hxA hxAD hqx hxI
    have hQ := hxAD.div ((hfD x hxI).pow 2) (pow_ne_zero 2 (hfne x hxI))
    have hxA' : weakProbeEulerMomentum K r p z (weakMeridionalAction K r p z) x =
        f x ^ 2 * weakMeridionalOperator K r p z x := hxA.symm
    apply ((hfD x hxI).fun_mul hQ).congr_deriv
    simp only [weakProbeFirstCoefficient, Pi.pow_apply, Nat.cast_ofNat,
      Nat.reduceSub, pow_one]
    rw [hxA']
    change weakMeridionalOperator K r p z x = q x at hqx
    rw [hqx]
    dsimp only [vq, f, b, P, q]
    simp only [Pi.div_apply, Pi.pow_apply]
    have hfne' : warp K x ≠ 0 := hfne x hxI
    field_simp [hfne']
    ring
  have hpDiv := warp_product_div_integrable hC h hpI
  have hqDiv := warp_product_div_integrable hC h hqI
  have hpExt := Analysis.exists_zero_boundary_extension_of_integrable_deriv zero_lt_one
    hpAC hpD hvp (by simpa only [sub_zero, f, IntegrableOn] using hpDiv.1) hpDiv.2
  have hqExt := Analysis.exists_zero_boundary_extension_of_integrable_deriv zero_lt_one
    hqAC hqD hvq (by simpa only [sub_zero, f, IntegrableOn] using hqDiv.1) hqDiv.2
  have hpClosed := ac_from_zero_extension
    (by simp only [f, hg.2.2.2.1.1, zero_mul])
    (by simp only [f, hg.2.2.2.1.2.1, zero_mul]) hpExt
  have hqClosed := ac_from_zero_extension
    (by simp only [f, hg.2.2.2.1.1, zero_mul])
    (by simp only [f, hg.2.2.2.1.2.1, zero_mul]) hqExt
  exact ⟨hpClosed.1, hqClosed.1, hpClosed.2.1, hpClosed.2.2,
    hqClosed.2.1, hqClosed.2.2⟩

end RicciFlowSharpEstimate.Geometry.AreaProfile
