/-
Copyright (c) 2026 Ziyang Qin. All rights reserved.
No license is granted by this file.
Authors: Ziyang Qin
-/
import RicciFlowSharpEstimate.Geometry.WeakProbePolarFluxBounds
import RicciFlowSharpEstimate.Analysis.ParabolicDivergenceBound

/-! # Bounded actual states and finite curvature-corrected operator pole traces -/

noncomputable section
namespace RicciFlowSharpEstimate.Geometry.AreaProfile
open Set MeasureTheory Filter Topology
local notation "areaμ" => volume.restrict (Ioo (0 : ℝ) 1)

/-- The actual minimizing p and canonical q are bounded throughout the physical
interior. The two corrected operator coordinates have finite pole traces,
without a curvature limit or nonzero probe trace hypothesis. -/
theorem IsRecoverableAreaCompetitor.probe_bounded_polar_states_of_minimum
    {C : ℝ} {K r p z : ℝ → ℝ} (hC : 1 ≤ C)
    (h : IsRecoverableAreaCompetitor C K r p z)
    (hr : ContinuousOn r (Ioo (0 : ℝ) 1))
    (hp : ContinuousOn p (Ioo (0 : ℝ) 1))
    (hmin : ∀ K' r' p' z' : ℝ → ℝ, IsRecoverableAreaCompetitor C K' r' p' z' →
      weakMeridionalAction K r p z ≤ weakMeridionalAction K' r' p' z') :
    let f := warp K
    let b := warpSlope K
    let q := fun x => weakProbeEulerMomentum K r p z (weakMeridionalAction K r p z) x /
      f x ^ 2
    ∃ qL qR B : ℝ, 0 ≤ B ∧
      Tendsto (fun x => q x + r x * (2 - b x) / (2 * f x)) (𝓝[>] 0) (𝓝 qL) ∧
      Tendsto (fun x => q x + r x * (2 + b x) / (2 * f x)) (𝓝[<] 1) (𝓝 qR) ∧
      ∀ x ∈ Ioo (0 : ℝ) 1, |p x| ≤ B ∧ |q x| ≤ B := by
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
  let V := fun (e : ℝ) (E u : ℝ → ℝ) (x : ℝ) =>
    E x / f x ^ 2 + (e * K x * r x + p x) * u x / (2 * f x)
  let μL := volume.restrict (Ioo (0 : ℝ) (1 / 2))
  let μR := volume.restrict (Ioo (1 / 2 : ℝ) 1)
  have hC0 : 0 < C := zero_lt_one.trans_le hC
  have hg := h.geometry_bounds hC
  obtain ⟨hQI, hpI, _, hReq, _, _, _, Br, hBr⟩ :=
    h.probe_pole_integrability_of_minimum hC hr hp hmin
  obtain ⟨hrD, hrCD, _, hqeq, hLocal, hSys⟩ :=
    h.probe_first_order_system_of_minimum hC hr hp hmin
  have hqI : Integrable q areaμ := hQI.congr hqeq
  have hrI := h.2.1.memLp.integrable (by norm_num : (1 : ENNReal) ≤ 2)
  have hGeom := h.slope_pole_quotient_bounds hC
  obtain ⟨hELsq, hERsq, _, _⟩ := h.polar_corrected_flux_bounds_of_minimum hC hr hp hmin
  change Integrable (fun x => EL x / x ^ 2) areaμ at hELsq
  change Integrable (fun x => ER x / (1 - x) ^ 2) areaμ at hERsq
  have hSubL : Ioo (0 : ℝ) (1 / 2) ⊆ Ioo (0 : ℝ) 1 :=
    fun _ hx => ⟨hx.1, by linarith [hx.2]⟩
  have hSubR : Ioo (1 / 2 : ℝ) 1 ⊆ Ioo (0 : ℝ) 1 :=
    fun _ hx => ⟨by linarith [hx.1], hx.2⟩
  have hfpos (x : ℝ) (hx : x ∈ Ioo (0 : ℝ) 1) : 0 < f x :=
    (mul_pos (mul_pos (by positivity : (0 : ℝ) < 2 / C) hx.1)
      (sub_pos.mpr hx.2)).trans_le (hg.2.2.1 x ⟨hx.1.le, hx.2.le⟩).1
  have hRatios := h.primitive_polar_ratio_bounds hC
  have hRatioL (x : ℝ) (hx : x ∈ Ioo (0 : ℝ) (1 / 2)) :
      |x / f x| ≤ C ∧ |uL x / f x| ≤ 4 * C ^ 2 := hRatios.1 x hx
  have hRatioR (x : ℝ) (hx : x ∈ Ioo (1 / 2 : ℝ) 1) :
      |(1 - x) / f x| ≤ C ∧ |uR x / f x| ≤ 4 * C ^ 2 := hRatios.2 x hx
  have hEF (E d : ℝ → ℝ) (μ : Measure ℝ)
      (hI : Integrable (fun x => E x / d x ^ 2) μ)
      (hm : AEStronglyMeasurable (fun x => d x / f x) μ)
      (hb : ∀ᵐ x ∂μ, ‖d x / f x‖ ≤ C)
      (hne : ∀ᵐ x ∂μ, d x ≠ 0 ∧ f x ≠ 0) :
      Integrable (fun x => E x / f x ^ 2) μ := by
    have hb2 : ∀ᵐ x ∂μ, ‖(d x / f x) ^ 2‖ ≤ C ^ 2 := by
      filter_upwards [hb] with x hx
      rw [norm_pow]
      exact pow_le_pow_left₀ (norm_nonneg _) hx 2
    apply (hI.bdd_mul (hm.pow 2) hb2).congr
    filter_upwards [hne] with x hx
    change (d x / f x) ^ 2 * (E x / d x ^ 2) = E x / f x ^ 2
    field_simp [hx.1, hx.2]
  have hfML : AEStronglyMeasurable f μL :=
    (hg.1.mono (hSubL.trans Ioo_subset_Icc_self)).aestronglyMeasurable measurableSet_Ioo
  have hfMR : AEStronglyMeasurable f μR :=
    (hg.1.mono (hSubR.trans Ioo_subset_Icc_self)).aestronglyMeasurable measurableSet_Ioo
  have hbML : AEStronglyMeasurable b μL :=
    (hg.2.1.mono (hSubL.trans Ioo_subset_Icc_self)).aestronglyMeasurable measurableSet_Ioo
  have hbMR : AEStronglyMeasurable b μR :=
    (hg.2.1.mono (hSubR.trans Ioo_subset_Icc_self)).aestronglyMeasurable measurableSet_Ioo
  have hELI : Integrable (fun x => EL x / f x ^ 2) μL := hEF EL (fun x => x) μL
    (hELsq.mono_measure (Measure.restrict_mono hSubL le_rfl))
    (continuous_id.aestronglyMeasurable.div₀ hfML)
    (by
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
      exact (hRatioL x hx).1)
    (by
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
      exact ⟨hx.1.ne', (hfpos x (hSubL hx)).ne'⟩)
  have hERI : Integrable (fun x => ER x / f x ^ 2) μR := hEF ER (fun x => 1 - x) μR
    (hERsq.mono_measure (Measure.restrict_mono hSubR le_rfl))
    ((continuous_const.sub continuous_id).aestronglyMeasurable.div₀ hfMR)
    (by
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
      exact (hRatioR x hx).1)
    (by
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
      exact ⟨(sub_pos.mpr hx.2).ne', (hfpos x (hSubR hx)).ne'⟩)
  have hKB : ∀ᵐ x ∂areaμ, ‖K x‖ ≤ 2 * C := by
    filter_upwards [hg.2.2.2.2] with x hx
    rw [Real.norm_eq_abs, abs_of_nonneg ((by positivity : (0 : ℝ) ≤ 2 / C).trans hx.1)]
    exact hx.2
  have hVI (e : ℝ) (E u : ℝ → ℝ) (a d : ℝ)
      (hs : Ioo a d ⊆ Ioo (0 : ℝ) 1)
      (hEI : IntegrableOn (fun x => E x / f x ^ 2) (Ioo a d))
      (huM : AEStronglyMeasurable (fun x => u x / f x) (volume.restrict (Ioo a d)))
      (huB : ∀ᵐ x ∂volume.restrict (Ioo a d), ‖u x / f x‖ ≤ 4 * C ^ 2) :
      IntegrableOn (V e E u) (Ioo a d) := by
    have hKS := hKB.filter_mono (ae_mono (Measure.restrict_mono hs le_rfl))
    have hKM := h.1.aestronglyMeasurable.mono_measure (Measure.restrict_mono hs le_rfl)
    have hrIS := hrI.mono_measure (Measure.restrict_mono hs le_rfl)
    have hpIS := hpI.mono_measure (Measure.restrict_mono hs le_rfl)
    apply (hEI.add ((((hrIS.bdd_mul hKM hKS).const_mul e).add hpIS).bdd_mul
      huM huB |>.div_const 2)).congr
    filter_upwards [] with x
    change E x / f x ^ 2 + (u x / f x) * (e * (K x * r x) + p x) / 2 = V e E u x
    dsimp only [V]
    ring
  have hVLI : Integrable (V 1 EL uL) μL := hVI 1 EL uL 0 (1 / 2) hSubL hELI
    ((aestronglyMeasurable_const.sub hbML).div₀ hfML)
    (by
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
      exact (hRatioL x hx).2)
  have hVRI : Integrable (V (-1) ER uR) μR := hVI (-1) ER uR (1 / 2) 1 hSubR hERI
    ((aestronglyMeasurable_const.add hbMR).div₀ hfMR)
    (by
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
      exact (hRatioR x hx).2)
  have hfD := (h.primitive_local_regularity hC).1
  have hbD := (h.primitive_local_regularity hC).2.2
  have hfCD : ContDiffOn ℝ 1 f (Ioo (0 : ℝ) 1) :=
    (h.primitive_weak_derivatives hC).1.contDiffOn_one_of_continuousOn
      (hg.1.mono Ioo_subset_Icc_self) (hg.2.1.mono Ioo_subset_Icc_self)
  have hUAC (u : ℝ → ℝ) (hu : AbsolutelyContinuousOnInterval u 0 1)
      (a : ℝ) (ha : a ∈ Ioo (0 : ℝ) 1) (d : ℝ) (hd : d ∈ Ioo (0 : ℝ) 1) :
      AbsolutelyContinuousOnInterval (fun x => q x + r x * u x / (2 * f x)) a d := by
    have hs := ordConnected_Ioo.uIcc_subset ha hd
    have hrA := (hrCD.mono hs).absolutelyContinuousOnInterval
    have huA := hu.mono (show uIcc a d ⊆ uIcc (0 : ℝ) 1 by
      simpa only [uIcc_of_le zero_le_one] using hs.trans Ioo_subset_Icc_self)
    have h2f : ContDiffOn ℝ 1 (fun x => 2 * f x) (Ioo (0 : ℝ) 1) :=
      contDiffOn_const.mul hfCD
    have hInv : ContDiffOn ℝ 1 (fun x => (2 * f x)⁻¹) (uIcc a d) :=
      (h2f.inv (fun x hx => mul_ne_zero (by norm_num) (hfpos x hx).ne')).mono hs
    have hh := (hLocal a ha d hd).2.fun_add ((hrA.fun_mul huA).fun_mul
      hInv.absolutelyContinuousOnInterval)
    apply hh.congr
    intro x _
    simp only [q, f, lam, div_eq_mul_inv]
  have hc : AbsolutelyContinuousOnInterval (fun _ : ℝ => (2 : ℝ)) 0 1 :=
    (contDiff_const : ContDiff ℝ 1 (fun _ : ℝ => (2 : ℝ))).contDiffOn.absolutelyContinuousOnInterval
  have hQLD : ∀ᵐ x ∂areaμ, HasDerivAt QL (V 1 EL uL x) x := by
    filter_upwards [hSys, hbD, ae_restrict_mem measurableSet_Ioo] with x hx hbX hxI
    have hh := hx.2.1.fun_add (((hrD x hxI).fun_mul
      ((hasDerivAt_const x (2 : ℝ)).fun_sub hbX)).div
        ((hfD x hxI).const_mul 2) (mul_ne_zero (by norm_num) (hfpos x hxI).ne'))
    change HasDerivAt QL _ x at hh
    apply hh.congr_deriv
    have hEq := hReq hxI
    dsimp only at hEq
    change _ = EL x / f x ^ 2 + (1 * K x * r x + p x) * uL x / (2 * f x)
    dsimp only [EL, V, uL, R, f, b, P, q, lam]
    rw [hEq]
    have hfne' : warp K x ≠ 0 := (hfpos x hxI).ne'
    field_simp [hfne']
    ring
  have hQRD : ∀ᵐ x ∂areaμ, HasDerivAt QR (V (-1) ER uR x) x := by
    filter_upwards [hSys, hbD, ae_restrict_mem measurableSet_Ioo] with x hx hbX hxI
    have hh := hx.2.1.fun_add (((hrD x hxI).fun_mul
      ((hasDerivAt_const x (2 : ℝ)).fun_add hbX)).div
        ((hfD x hxI).const_mul 2) (mul_ne_zero (by norm_num) (hfpos x hxI).ne'))
    change HasDerivAt QR _ x at hh
    apply hh.congr_deriv
    have hEq := hReq hxI
    dsimp only at hEq
    change _ = ER x / f x ^ 2 + ((-1) * K x * r x + p x) * uR x / (2 * f x)
    dsimp only [ER, V, uR, R, f, b, P, q, lam]
    rw [hEq]
    have hfne' : warp K x ≠ 0 := (hfpos x hxI).ne'
    field_simp [hfne']
    ring
  have hQLlocal (a : ℝ) (ha : a ∈ Ioo (0 : ℝ) (1 / 2))
      (d : ℝ) (hd : d ∈ Ioo (0 : ℝ) (1 / 2)) : AbsolutelyContinuousOnInterval QL a d :=
    hUAC uL (hc.fun_sub hGeom.1) a (hSubL ha) d (hSubL hd)
  have hQRlocal (a : ℝ) (ha : a ∈ Ioo (1 / 2 : ℝ) 1)
      (d : ℝ) (hd : d ∈ Ioo (1 / 2 : ℝ) 1) : AbsolutelyContinuousOnInterval QR a d :=
    hUAC uR (hc.fun_add hGeom.1) a (hSubR ha) d (hSubR hd)
  have hQLDL : ∀ᵐ x ∂μL, HasDerivAt QL (V 1 EL uL x) x :=
    hQLD.filter_mono (ae_mono (Measure.restrict_mono hSubL le_rfl))
  have hQRDR : ∀ᵐ x ∂μR, HasDerivAt QR (V (-1) ER uR x) x :=
    hQRD.filter_mono (ae_mono (Measure.restrict_mono hSubR le_rfl))
  obtain ⟨UL, _, _, hQLT, _, BL, hBL⟩ :=
    Analysis.exists_boundary_extension_of_integrable_deriv (by norm_num : (0 : ℝ) < 1 / 2)
      hQLlocal hQLDL hVLI
  obtain ⟨UR, _, _, _, hQRT, BR, hBR⟩ :=
    Analysis.exists_boundary_extension_of_integrable_deriv (by norm_num : (1 / 2 : ℝ) < 1)
      hQRlocal hQRDR hVRI
  let Bq := |BL| + |BR| + |q (1 / 2)| + 4 * C ^ 2 * |Br|
  have hBq0 : 0 ≤ Bq := by positivity
  have hqStep (u Q : ℝ → ℝ) (x B : ℝ) (hx : x ∈ Ioo (0 : ℝ) 1)
      (heq : Q x = q x + r x * u x / (2 * f x))
      (hUB : |u x / f x| ≤ 4 * C ^ 2) (hQB : |Q x| ≤ B) :
      |q x| ≤ B + 2 * C ^ 2 * |Br| := by
    have hrB : |r x| ≤ |Br| := (hBr x hx).trans (le_abs_self Br)
    have he : q x = Q x - r x * (u x / f x) / 2 := by
      rw [heq]
      field_simp [(hfpos x hx).ne']
      ring
    rw [he]
    calc
      _ ≤ |Q x| + |r x * (u x / f x) / 2| := by
        simpa only [Real.norm_eq_abs] using norm_sub_le (Q x) (r x * (u x / f x) / 2)
      _ ≤ B + 2 * C ^ 2 * |Br| := by
        rw [abs_div, abs_mul]
        norm_num
        have hh := mul_le_mul hrB hUB (abs_nonneg _) (abs_nonneg _)
        nlinarith only [hh, hQB]
  have hqB : ∀ x ∈ Ioo (0 : ℝ) 1, |q x| ≤ Bq := by
    intro x hx
    rcases lt_trichotomy x (1 / 2 : ℝ) with hl | he | hr'
    · have hh := hqStep uL QL x BL hx rfl (hRatioL x ⟨hx.1, hl⟩).2 (hBL x ⟨hx.1, hl⟩)
      dsimp only [Bq]
      nlinarith [le_abs_self BL, abs_nonneg BR, abs_nonneg (q (1 / 2)),
        mul_nonneg (sq_nonneg C) (abs_nonneg Br)]
    · rw [he]
      dsimp only [Bq]
      nlinarith [abs_nonneg BL, abs_nonneg BR,
        mul_nonneg (sq_nonneg C) (abs_nonneg Br)]
    · have hh := hqStep uR QR x BR hx rfl (hRatioR x ⟨hr', hx.2⟩).2 (hBR x ⟨hr', hx.2⟩)
      dsimp only [Bq]
      nlinarith [le_abs_self BR, abs_nonneg BL, abs_nonneg (q (1 / 2)),
        mul_nonneg (sq_nonneg C) (abs_nonneg Br)]
  let M := Bq + 2 * C * |Br|
  have hSB : ∀ᵐ x ∂areaμ, |weakMeridionalOperator K r p z x + K x * r x| ≤ M := by
    filter_upwards [hqeq, hKB, ae_restrict_mem measurableSet_Ioo] with x hqx hK hx
    rw [hqx]
    calc
      _ ≤ |q x| + |K x * r x| := abs_add_le _ _
      _ ≤ M := by
        rw [abs_mul]
        have hKr := mul_le_mul (show |K x| ≤ 2 * C from hK)
          ((hBr x hx).trans (le_abs_self Br)) (abs_nonneg _) (by positivity : 0 ≤ 2 * C)
        dsimp only [M]
        linarith [hqB x hx]
  obtain ⟨hFAC, hF0, hF1, hFD⟩ := h.derivative_flux_absolutelyContinuous hC hp
  have hfb (x : ℝ) (hx : x ∈ Ioo (0 : ℝ) 1) :
      (2 / C) * (x * (1 - x)) ≤ f x ∧ f x ≤ (2 * C) * (x * (1 - x)) := by
    have hh := hg.2.2.1 x ⟨hx.1.le, hx.2.le⟩
    exact ⟨by simpa only [mul_assoc] using hh.1,
      by simpa only [mul_assoc] using hh.2.1⟩
  have hpB := Analysis.bounded_of_parabolic_divergence_flux
    (by positivity : 0 < 2 / C) hfb hFAC hF0 hF1
      (fun _ _ => rfl) hFD hSB
  let B := Bq + |2 * |2 * C| * |M| / (2 / C) ^ 2|
  refine ⟨UL 0, UR 1, B, ?_, hQLT, hQRT, ?_⟩
  · dsimp only [B]
    positivity
  · intro x hx
    constructor
    · exact (hpB x hx).trans ((le_abs_self _).trans (by dsimp only [B]; linarith))
    · exact (hqB x hx).trans (le_add_of_nonneg_right (abs_nonneg _))

end RicciFlowSharpEstimate.Geometry.AreaProfile
