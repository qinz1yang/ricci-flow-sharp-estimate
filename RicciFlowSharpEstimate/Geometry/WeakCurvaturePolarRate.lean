/-
Copyright (c) 2026 Ziyang Qin. All rights reserved.
No license is granted by this file.
Authors: Ziyang Qin
-/
import RicciFlowSharpEstimate.Geometry.WeakProbeBoundedPolarStates
import RicciFlowSharpEstimate.Geometry.WeakCurvatureAdjointRegularity
import RicciFlowSharpEstimate.Geometry.WeakProbeWeightedPoleTraces

/-! # The actual polar first derivative of the complete curvature residual -/

noncomputable section
namespace RicciFlowSharpEstimate.Geometry.AreaProfile
open Set MeasureTheory Filter Topology
local notation "areaμ" => volume.restrict (Ioo (0 : ℝ) 1)

private theorem zero_mul_bounded {α : Type*} {l : Filter α} {u v : α → ℝ} {B : ℝ}
    (hu : Tendsto u l (𝓝 0)) (hv : ∀ᶠ x in l, |v x| ≤ B) :
    Tendsto (fun x => u x * v x) l (𝓝 0) := by
  apply squeeze_zero_norm'
  · filter_upwards [hv] with x hx
    simp only [norm_mul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left hx (abs_nonneg _)
  · simpa only [norm_zero, zero_mul, Real.norm_eq_abs] using hu.norm.mul_const B

/-- The complete regular-adjoint derivative has a polar rate with one explicitly
retained curvature-primitive term. All corrected traces and source integrability
are produced from the actual minimum. In the zero probe-trace cases the term
vanishes, giving a genuine finite derivative trace without nondegeneracy. -/
theorem IsRecoverableAreaCompetitor.curvature_adjoint_polar_derivative_rate_of_minimum
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
    let A := fun x => weakCurvatureWarpCoefficient K r p z x - lam * r x ^ 2
    let B := weakCurvatureSlopeCoefficient K r p z
    let W := weakCurvatureAdjointRegularPart K r p z lam
    Integrable A areaμ ∧ ∃ qL qR : ℝ,
      Tendsto (fun x => q x + r x * (2 - b x) / (2 * f x)) (𝓝[>] 0) (𝓝 qL) ∧
      Tendsto (fun x => q x + r x * (2 + b x) / (2 * f x)) (𝓝[<] 1) (𝓝 qR) ∧
      ∀ t : ℝ,
        let H := fun x => W x - t * (x - 1 / 2)
        Tendsto (fun x => deriv H x - R 0 ^ 2 * (2 - b x) / f x) (𝓝[>] 0)
          (𝓝 (-6 * R 0 * qL + 2 * (∫ s in (0 : ℝ)..1, (1 - s) * A s) -
            2 * (∫ s in (0 : ℝ)..1, B s) - t)) ∧
        Tendsto (fun x => deriv H x + R 1 ^ 2 * (2 + b x) / f x) (𝓝[<] 1)
          (𝓝 (6 * R 1 * qR - 2 * (∫ s in (0 : ℝ)..1, s * A s) -
            2 * (∫ s in (0 : ℝ)..1, B s) - t)) := by
  let lam := weakMeridionalAction K r p z
  let f := warp K
  let b := warpSlope K
  let P := weakProbeEulerFlux K r p z lam
  let q := fun x => weakProbeEulerMomentum K r p z lam x / f x ^ 2
  let R := fun x => r (1 / 2) + ∫ s in (1 / 2 : ℝ)..x, p s
  let uL := fun x => 2 - b x
  let uR := fun x => 2 + b x
  let EL := fun x => P x - uL x * b x * R x / 2
  let ER := fun x => P x - uR x * b x * R x / 2
  let QL := fun x => q x + r x * uL x / (2 * f x)
  let QR := fun x => q x + r x * uR x / (2 * f x)
  let A := fun x => weakCurvatureWarpCoefficient K r p z x - lam * r x ^ 2
  let B := weakCurvatureSlopeCoefficient K r p z
  let W := weakCurvatureAdjointRegularPart K r p z lam
  let J := fun x => (∫ s in x..1, (1 - s) * A s) - ∫ s in (0 : ℝ)..x, s * A s
  let F := fun x => 6 * f x * q x * p x - b x * f x * p x ^ 2 -
    3 * b x * q x * r x - 2 * P x * r x / f x + 2 * J x -
      2 * ∫ s in (0 : ℝ)..1, B s
  have hC0 : 0 < C := zero_lt_one.trans_le hC
  have hg := h.geometry_bounds hC
  obtain ⟨qL, qR, D, hD0, hQLT, hQRT, hBound⟩ :=
    h.probe_bounded_polar_states_of_minimum hC hr hp hmin
  change Tendsto QL (𝓝[>] 0) (𝓝 qL) at hQLT
  change Tendsto QR (𝓝[<] 1) (𝓝 qR) at hQRT
  obtain ⟨hQI, hpI, _, hReq, _, hrLT, hrRT, _⟩ :=
    h.probe_pole_integrability_of_minimum hC hr hp hmin
  change Tendsto r (𝓝[>] 0) (𝓝 (R 0)) at hrLT
  change Tendsto r (𝓝[<] 1) (𝓝 (R 1)) at hrRT
  have hqeq := (h.probe_euler_flux_of_minimum hC hmin).2.2.2.2.2.2.2.2.2.2
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
  have hpB : ∀ᵐ x ∂areaμ, ‖p x‖ ≤ D := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
    simpa only [Real.norm_eq_abs] using (hBound x hx).1
  have hqB : ∀ᵐ x ∂areaμ, ‖q x‖ ≤ D := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
    simpa only [Real.norm_eq_abs] using (hBound x hx).2
  have hK2B : ∀ᵐ x ∂areaμ, ‖K x ^ 2‖ ≤ (2 * C) ^ 2 := by
    filter_upwards [hKB] with x hx
    rw [norm_pow]
    exact pow_le_pow_left₀ (norm_nonneg _) hx 2
  have hqq := (hqI.bdd_mul hqI.aestronglyMeasurable hqB).const_mul 3
  have hbqp := ((hpI.bdd_mul hqI.aestronglyMeasurable hqB).bdd_mul hbM hbB).const_mul 4
  have hKqr := ((hrI.bdd_mul hqI.aestronglyMeasurable hqB).bdd_mul
    h.1.aestronglyMeasurable hKB).const_mul 2
  have hKbrp := ((hrI.bdd_mul hpI.aestronglyMeasurable hpB).bdd_mul hbM hbB).bdd_mul
    h.1.aestronglyMeasurable hKB
  have hK2r2 := h.2.1.integrable_sq.bdd_mul (h.1.aestronglyMeasurable.pow 2) hK2B
  have hMass := h.2.1.integrable_sq.const_mul lam
  have hfpos (x : ℝ) (hx : x ∈ Ioo (0 : ℝ) 1) : 0 < f x :=
    (mul_pos (mul_pos (by positivity : (0 : ℝ) < 2 / C) hx.1)
      (sub_pos.mpr hx.2)).trans_le (hg.2.2.1 x ⟨hx.1.le, hx.2.le⟩).1
  have hAI : Integrable A areaμ := by
    apply (((((hqq.sub hbqp).add hKqr).sub hKbrp).add hK2r2).sub hMass).congr
    filter_upwards [hqeq, ae_restrict_mem measurableSet_Ioo] with x hqx hx
    have hQval : f x * z x + 2 * b x * p x - K x * r x = q x := hqx
    have hz : z x = (q x - 2 * b x * p x + K x * r x) / f x := by
      apply (eq_div_iff (hfpos x hx).ne').mpr
      nlinarith only [hQval]
    change 3 * (q x * q x) - 4 * (b x * (q x * p x)) +
      2 * (K x * (q x * r x)) - K x * (b x * (p x * r x)) +
      K x ^ 2 * r x ^ 2 - lam * r x ^ 2 = A x
    dsimp only [A, weakCurvatureWarpCoefficient]
    change weakMeridionalOperator K r p z x = q x at hqx
    rw [hqx, hz]
    have hfne' : warp K x ≠ 0 := (hfpos x hx).ne'
    dsimp only [f, b, q]
    field_simp [hfne']
    ring
  have hsB : ∀ᵐ s ∂areaμ, ‖s‖ ≤ (1 : ℝ) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
    rw [Real.norm_eq_abs, abs_of_pos hs.1]
    exact hs.2.le
  have h1sB : ∀ᵐ s ∂areaμ, ‖1 - s‖ ≤ (1 : ℝ) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
    rw [Real.norm_eq_abs, abs_of_pos (sub_pos.mpr hs.2)]
    linarith [hs.1]
  have hAs := hAI.bdd_mul continuous_id.aestronglyMeasurable hsB
  have hAr := hAI.bdd_mul (continuous_const.sub continuous_id).aestronglyMeasurable h1sB
  have hAsI : IntervalIntegrable (fun s => s * A s) volume 0 1 :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le zero_le_one).mpr hAs
  have hArI : IntervalIntegrable (fun s => (1 - s) * A s) volume 0 1 :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le zero_le_one).mpr hAr
  have hLAC := hAsI.absolutelyContinuousOnInterval_intervalIntegral
    (show (0 : ℝ) ∈ uIcc (0 : ℝ) 1 by simp)
  have hRAC : AbsolutelyContinuousOnInterval
      (fun x => ∫ s in x..1, (1 - s) * A s) 0 1 := by
    apply (hArI.absolutelyContinuousOnInterval_intervalIntegral
      (show (1 : ℝ) ∈ uIcc (0 : ℝ) 1 by simp)).neg.congr
    intro x _
    change -(∫ s in (1 : ℝ)..x, (1 - s) * A s) = ∫ s in x..1, (1 - s) * A s
    rw [intervalIntegral.integral_symm, neg_neg]
  have hJAC : AbsolutelyContinuousOnInterval J 0 1 := hRAC.fun_sub hLAC
  have hJC : ContinuousOn J (Icc (0 : ℝ) 1) := by
    simpa only [uIcc_of_le zero_le_one] using hJAC.continuousOn
  have hJLT := ((hJC.continuousWithinAt ⟨le_rfl, zero_le_one⟩).mono_of_mem_nhdsWithin
    (Icc_mem_nhdsGT zero_lt_one)).tendsto
  have hJRT := ((hJC.continuousWithinAt ⟨zero_le_one, le_rfl⟩).mono_of_mem_nhdsWithin
    (Icc_mem_nhdsLT zero_lt_one)).tendsto
  have hbLT : Tendsto b (𝓝[>] 0) (𝓝 2) := by
    simpa only [b, hg.2.2.2.1.2.2.1] using
      ((hg.2.1.continuousWithinAt ⟨le_rfl, zero_le_one⟩).mono_of_mem_nhdsWithin
        (Icc_mem_nhdsGT zero_lt_one)).tendsto
  have hbRT : Tendsto b (𝓝[<] 1) (𝓝 (-2)) := by
    simpa only [b, hg.2.2.2.1.2.2.2] using
      ((hg.2.1.continuousWithinAt ⟨zero_le_one, le_rfl⟩).mono_of_mem_nhdsWithin
        (Icc_mem_nhdsLT zero_lt_one)).tendsto
  have hLDom : ∀ᶠ x in 𝓝[>] (0 : ℝ), x ∈ Ioo (0 : ℝ) (1 / 2) :=
    Ioo_mem_nhdsGT (by norm_num)
  have hRDom : ∀ᶠ x in 𝓝[<] (1 : ℝ), x ∈ Ioo (1 / 2 : ℝ) 1 :=
    Ioo_mem_nhdsLT (by norm_num)
  have hSubL : Ioo (0 : ℝ) (1 / 2) ⊆ Ioo (0 : ℝ) 1 :=
    fun _ hx => ⟨hx.1, by linarith [hx.2]⟩
  have hSubR : Ioo (1 / 2 : ℝ) 1 ⊆ Ioo (0 : ℝ) 1 :=
    fun _ hx => ⟨by linarith [hx.1], hx.2⟩
  have hRatios := h.primitive_polar_ratio_bounds hC
  obtain ⟨_, _, hELd, hERd⟩ := h.polar_corrected_flux_bounds_of_minimum hC hr hp hmin
  change Tendsto (fun x => EL x / x) (𝓝[>] 0) (𝓝 0) at hELd
  change Tendsto (fun x => ER x / (1 - x)) (𝓝[<] 1) (𝓝 0) at hERd
  have hELzero : Tendsto (fun x => EL x / f x) (𝓝[>] 0) (𝓝 0) := by
    apply (zero_mul_bounded hELd (hLDom.mono fun x hx => (hRatios.1 x hx).1)).congr'
    filter_upwards [hLDom] with x hx
    change (EL x / x) * (x / f x) = EL x / f x
    field_simp [hx.1.ne']
  have hERzero : Tendsto (fun x => ER x / f x) (𝓝[<] 1) (𝓝 0) := by
    apply (zero_mul_bounded hERd (hRDom.mono fun x hx => (hRatios.2 x hx).1)).congr'
    filter_upwards [hRDom] with x hx
    change (ER x / (1 - x)) * ((1 - x) / f x) = ER x / f x
    field_simp [(sub_pos.mpr hx.2).ne']
  obtain ⟨_, _, hFpL, hFpR, _, _⟩ :=
    h.probe_weighted_state_pole_traces_of_minimum hC hp hmin
  have hqBL : ∀ᶠ x in 𝓝[>] (0 : ℝ), |q x| ≤ D :=
    hLDom.mono fun x hx => (hBound x (hSubL hx)).2
  have hqBR : ∀ᶠ x in 𝓝[<] (1 : ℝ), |q x| ≤ D :=
    hRDom.mono fun x hx => (hBound x (hSubR hx)).2
  have hbpBL : ∀ᶠ x in 𝓝[>] (0 : ℝ), |b x * p x| ≤ 2 * D := by
    filter_upwards [hLDom] with x hx
    rw [abs_mul]
    exact mul_le_mul (hg.2.2.1 x (Ioo_subset_Icc_self (hSubL hx))).2.2
      (hBound x (hSubL hx)).1 (abs_nonneg _) (by norm_num)
  have hbpBR : ∀ᶠ x in 𝓝[<] (1 : ℝ), |b x * p x| ≤ 2 * D := by
    filter_upwards [hRDom] with x hx
    rw [abs_mul]
    exact mul_le_mul (hg.2.2.1 x (Ioo_subset_Icc_self (hSubR hx))).2.2
      (hBound x (hSubR hx)).1 (abs_nonneg _) (by norm_num)
  have h6L := (zero_mul_bounded hFpL hqBL).const_mul 6
  have h6R := (zero_mul_bounded hFpR hqBR).const_mul 6
  have h2L := zero_mul_bounded hFpL hbpBL
  have h2R := zero_mul_bounded hFpR hbpBR
  have hcL : Tendsto (fun x => b x * r x ^ 2 / 2 - R 0 ^ 2) (𝓝[>] 0) (𝓝 0) := by
    convert ((hbLT.mul (hrLT.pow 2)).div_const 2).sub_const (R 0 ^ 2) using 1
    congr 1
    ring
  have hcR : Tendsto (fun x => b x * r x ^ 2 / 2 + R 1 ^ 2) (𝓝[<] 1) (𝓝 0) := by
    convert ((hbRT.mul (hrRT.pow 2)).div_const 2).add_const (R 1 ^ 2) using 1
    congr 1
    ring
  have hcLT := zero_mul_bounded hcL (hLDom.mono fun x hx => (hRatios.1 x hx).2)
  have hcRT := zero_mul_bounded hcR (hRDom.mono fun x hx => (hRatios.2 x hx).2)
  have hWL := h.curvature_adjoint_regularPart_of_minimum hC hr hp hmin
  have hWD := hWL.2.2.1
  change (∀ x ∈ Ioo (0 : ℝ) 1, HasDerivAt W (F x) x) at hWD
  refine ⟨hAI, qL, qR, hQLT, hQRT, ?_⟩
  intro t
  let H := fun x => W x - t * (x - 1 / 2)
  have hHD (x : ℝ) (hx : x ∈ Ioo (0 : ℝ) 1) : HasDerivAt H (F x - t) x := by
    simpa only [H, id_eq, mul_one] using (hWD x hx).fun_sub
      (((hasDerivAt_id x).sub_const (1 / 2 : ℝ)).const_mul t)
  have hLL := ((((((h6L.sub h2L).sub
    (((hbLT.mul hrLT).mul hQLT).const_mul 3)).sub
      ((hELzero.mul hrLT).const_mul 2)).add hcLT).add (hJLT.const_mul 2)).sub_const
        (2 * ∫ s in (0 : ℝ)..1, B s)).sub_const t
  have hRR := ((((((h6R.sub h2R).sub
    (((hbRT.mul hrRT).mul hQRT).const_mul 3)).sub
      ((hERzero.mul hrRT).const_mul 2)).add hcRT).add (hJRT.const_mul 2)).sub_const
        (2 * ∫ s in (0 : ℝ)..1, B s)).sub_const t
  constructor
  · have hlim : Tendsto (fun x => 6 * ((f x * p x) * q x) -
        (f x * p x) * (b x * p x) - 3 * (b x * r x * QL x) -
        2 * (EL x / f x * r x) + (b x * r x ^ 2 / 2 - R 0 ^ 2) * (uL x / f x) +
        2 * J x - 2 * (∫ s in (0 : ℝ)..1, B s) - t) (𝓝[>] 0)
        (𝓝 (-6 * R 0 * qL + 2 * (∫ s in (0 : ℝ)..1, (1 - s) * A s) -
          2 * (∫ s in (0 : ℝ)..1, B s) - t)) := by
      convert hLL using 1
      congr 1
      simp only [J, intervalIntegral.integral_same, sub_zero]
      ring
    apply hlim.congr'
    filter_upwards [hLDom] with x hx
    rw [(hHD x (hSubL hx)).deriv]
    have hEq := hReq (hSubL hx)
    dsimp only at hEq
    dsimp only [F, QL, EL, R, f, b, uL, q, P, lam]
    rw [hEq]
    have hfne' : warp K x ≠ 0 := (hfpos x (hSubL hx)).ne'
    field_simp [hfne']
    ring
  · have hlim : Tendsto (fun x => 6 * ((f x * p x) * q x) -
        (f x * p x) * (b x * p x) - 3 * (b x * r x * QR x) -
        2 * (ER x / f x * r x) + (b x * r x ^ 2 / 2 + R 1 ^ 2) * (uR x / f x) +
        2 * J x - 2 * (∫ s in (0 : ℝ)..1, B s) - t) (𝓝[<] 1)
        (𝓝 (6 * R 1 * qR - 2 * (∫ s in (0 : ℝ)..1, s * A s) -
          2 * (∫ s in (0 : ℝ)..1, B s) - t)) := by
      convert hRR using 1
      congr 1
      simp only [J, intervalIntegral.integral_same, zero_sub]
      ring
    apply hlim.congr'
    filter_upwards [hRDom] with x hx
    rw [(hHD x (hSubR hx)).deriv]
    have hEq := hReq (hSubR hx)
    dsimp only at hEq
    dsimp only [F, QR, ER, R, f, b, uR, q, P, lam]
    rw [hEq]
    have hfne' : warp K x ≠ 0 := (hfpos x (hSubR hx)).ne'
    field_simp [hfne']
    ring

end RicciFlowSharpEstimate.Geometry.AreaProfile
