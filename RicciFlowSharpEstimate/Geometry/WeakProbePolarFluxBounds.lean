/-
Copyright (c) 2026 Ziyang Qin. All rights reserved.
No license is granted by this file.
Authors: Ziyang Qin
-/
import RicciFlowSharpEstimate.Geometry.WeakProbePolarFlux
import RicciFlowSharpEstimate.Analysis.PolarFluxLimits

/-! # Squared-distance control and vanishing rates of the corrected polar fluxes -/

noncomputable section
namespace RicciFlowSharpEstimate.Geometry.AreaProfile
open Set MeasureTheory Filter Topology
local notation "areaμ" => volume.restrict (Ioo (0 : ℝ) 1)

/-- The corrected actual flux divided by the pole-distance square is L1,
and division by the first distance tends to zero at the corresponding pole.
The complete source and original geometry produce these rates. -/
theorem IsRecoverableAreaCompetitor.polar_corrected_flux_bounds_of_minimum
    {C : ℝ} {K r p z : ℝ → ℝ} (hC : 1 ≤ C)
    (h : IsRecoverableAreaCompetitor C K r p z)
    (hr : ContinuousOn r (Ioo (0 : ℝ) 1))
    (hp : ContinuousOn p (Ioo (0 : ℝ) 1))
    (hmin : ∀ K' r' p' z' : ℝ → ℝ, IsRecoverableAreaCompetitor C K' r' p' z' →
      weakMeridionalAction K r p z ≤ weakMeridionalAction K' r' p' z') :
    let lam := weakMeridionalAction K r p z
    let b := warpSlope K
    let P := weakProbeEulerFlux K r p z lam
    let R := fun x => r (1 / 2) + ∫ s in (1 / 2 : ℝ)..x, p s
    let EL := fun x => P x - (2 - b x) * b x * R x / 2
    let ER := fun x => P x - (2 + b x) * b x * R x / 2
    Integrable (fun x => EL x / x ^ 2) areaμ ∧
      Integrable (fun x => ER x / (1 - x) ^ 2) areaμ ∧
      Tendsto (fun x => EL x / x) (𝓝[>] 0) (𝓝 0) ∧
      Tendsto (fun x => ER x / (1 - x)) (𝓝[<] 1) (𝓝 0) := by
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
  let T := fun (u : ℝ → ℝ) (x : ℝ) => f x * K x * (q x - K x * r x) +
    b x * (f x * K x - u x) * p x / 2 + K x * u x ^ 2 * r x / 2 +
      lam * f x * r x
  let gL := fun x => T uL x / x
  let gR := fun x => T uR x / (1 - x)
  have hg := h.geometry_bounds hC
  have hC0 : 0 < C := zero_lt_one.trans_le hC
  have hPQ := h.probe_pole_integrability_of_minimum hC hr hp hmin
  have hpI := hPQ.2.1
  have hrI := h.2.1.memLp.integrable (by norm_num : (1 : ENNReal) ≤ 2)
  have hqeq := (h.probe_euler_flux_of_minimum hC hmin).2.2.2.2.2.2.2.2.2.2
  have hqI : Integrable q areaμ := hPQ.1.congr hqeq
  have hfM : AEStronglyMeasurable f areaμ :=
    (hg.1.mono Ioo_subset_Icc_self).aestronglyMeasurable measurableSet_Ioo
  have hbM : AEStronglyMeasurable b areaμ :=
    (hg.2.1.mono Ioo_subset_Icc_self).aestronglyMeasurable measurableSet_Ioo
  have hKB : ∀ᵐ x ∂areaμ, ‖K x‖ ≤ 2 * C := by
    filter_upwards [hg.2.2.2.2] with x hx
    rw [Real.norm_eq_abs, abs_of_nonneg ((by positivity : (0 : ℝ) ≤ 2 / C).trans hx.1)]
    exact hx.2
  have hbB : ∀ᵐ x ∂areaμ, ‖b x‖ ≤ 2 := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
    exact (hg.2.2.1 x ⟨hx.1.le, hx.2.le⟩).2.2
  have huLB : ∀ᵐ x ∂areaμ, ‖uL x‖ ≤ 4 := by
    filter_upwards [hbB] with x hx
    rw [Real.norm_eq_abs] at hx
    calc
      ‖2 - b x‖ ≤ ‖(2 : ℝ)‖ + ‖b x‖ := norm_sub_le _ _
      _ ≤ 4 := by norm_num; linarith
  have huRB : ∀ᵐ x ∂areaμ, ‖uR x‖ ≤ 4 := by
    filter_upwards [hbB] with x hx
    rw [Real.norm_eq_abs] at hx
    calc
      ‖2 + b x‖ ≤ ‖(2 : ℝ)‖ + ‖b x‖ := norm_add_le _ _
      _ ≤ 4 := by norm_num; linarith
  have hfB : ∀ᵐ x ∂areaμ, ‖f x / x‖ ≤ 2 * C ∧ ‖f x / (1 - x)‖ ≤ 2 * C := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
    have hgx := hg.2.2.1 x ⟨hx.1.le, hx.2.le⟩
    have hf0 : 0 ≤ f x :=
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
  have hGI (u d : ℝ → ℝ)
      (huM : AEStronglyMeasurable u areaμ) (huB : ∀ᵐ x ∂areaμ, ‖u x‖ ≤ 4)
      (hdM : AEStronglyMeasurable d areaμ) (hdne : ∀ᵐ x ∂areaμ, d x ≠ 0)
      (hudB : ∀ᵐ x ∂areaμ, ‖u x / d x‖ ≤ 4 * C)
      (hfdB : ∀ᵐ x ∂areaμ, ‖f x / d x‖ ≤ 2 * C) :
      Integrable (fun x => T u x / d x) areaμ := by
    have hfDM := hfM.div₀ hdM
    have huDM := huM.div₀ hdM
    have hQ := ((hqI.sub (hrI.bdd_mul h.1.aestronglyMeasurable hKB)).bdd_mul
      h.1.aestronglyMeasurable hKB).bdd_mul hfDM hfdB
    have hP := (((hpI.bdd_mul h.1.aestronglyMeasurable hKB).bdd_mul hfDM hfdB).sub
      (hpI.bdd_mul huDM hudB)).bdd_mul hbM hbB |>.div_const 2
    have hR := (((hrI.bdd_mul huM huB).bdd_mul huDM hudB).bdd_mul
      h.1.aestronglyMeasurable hKB).div_const 2
    have hMass := (hrI.bdd_mul hfDM hfdB).const_mul lam
    apply (((hQ.add hP).add hR).add hMass).congr
    filter_upwards [hdne] with x hx
    change f x / d x * (K x * (q x - K x * r x)) +
      b x * (f x / d x * (K x * p x) - u x / d x * p x) / 2 +
      K x * (u x / d x * (u x * r x)) / 2 +
      lam * (f x / d x * r x) = T u x / d x
    dsimp only [T]
    field_simp [hx]
  have huQuot := (h.slope_pole_quotient_bounds hC).2
  have hgL : Integrable gL areaμ := hGI uL (fun x : ℝ => x)
    (aestronglyMeasurable_const.sub hbM) huLB continuous_id.aestronglyMeasurable
    ((ae_restrict_mem measurableSet_Ioo).mono fun _ hx => hx.1.ne')
    (by
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
      exact (huQuot x hx).1)
    (hfB.mono fun _ hx => hx.1)
  have hgR : Integrable gR areaμ := hGI uR (fun x : ℝ => 1 - x)
    (aestronglyMeasurable_const.add hbM) huRB
    (continuous_const.sub continuous_id).aestronglyMeasurable
    ((ae_restrict_mem measurableSet_Ioo).mono fun _ hx => (sub_pos.mpr hx.2).ne')
    (by
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
      exact (huQuot x hx).2)
    (hfB.mono fun _ hx => hx.2)
  obtain ⟨hELAC, hERAC, hEL0, hER1, hED⟩ :=
    h.polar_corrected_flux_derivatives_of_minimum hC hr hp hmin
  change AbsolutelyContinuousOnInterval EL 0 1 at hELAC
  change AbsolutelyContinuousOnInterval ER 0 1 at hERAC
  change EL 0 = 0 at hEL0
  change ER 1 = 0 at hER1
  change (∀ᵐ x ∂areaμ, HasDerivAt EL (T uL x) x ∧ HasDerivAt ER (T uR x) x) at hED
  have hDL : ∀ᵐ x ∂areaμ, HasDerivAt EL (x * gL x) x := by
    filter_upwards [hED, ae_restrict_mem measurableSet_Ioo] with x hx hxI
    apply hx.1.congr_deriv
    dsimp only [gL]
    field_simp [hxI.1.ne']
  have hDR : ∀ᵐ x ∂areaμ, HasDerivAt ER ((1 - x) * gR x) x := by
    filter_upwards [hED, ae_restrict_mem measurableSet_Ioo] with x hx hxI
    apply hx.2.congr_deriv
    dsimp only [gR]
    field_simp [(sub_pos.mpr hxI.2).ne']
  exact ⟨Analysis.integrableOn_div_sq_of_coordinate_derivative hELAC hEL0 hDL hgL,
    Analysis.integrableOn_div_sub_sq_of_distance_derivative hERAC hER1 hDR hgR,
    Analysis.tendsto_div_zero_of_coordinate_derivative zero_lt_one hELAC hEL0 hDL hgL,
    Analysis.tendsto_div_sub_zero_of_distance_derivative zero_lt_one hERAC hER1 hDR hgR⟩

end RicciFlowSharpEstimate.Geometry.AreaProfile
