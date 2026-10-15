/-
Copyright (c) 2026 Ziyang Qin. All rights reserved.
No license is granted by this file.
Authors: Ziyang Qin
-/
import RicciFlowSharpEstimate.Geometry.WeakProbeEulerL2
import RicciFlowSharpEstimate.Geometry.WeakProbeEulerFlux
import RicciFlowSharpEstimate.Geometry.RecoverableAreaRegularity
import RicciFlowSharpEstimate.Analysis.H1EndpointIntegrability
import RicciFlowSharpEstimate.Analysis.WeightedDerivativeIntegrability

/-! # Unweighted integrability of the actual minimizing meridional operator -/

noncomputable section
namespace RicciFlowSharpEstimate.Geometry.AreaProfile
open Set MeasureTheory Filter
local notation "areaμ" => volume.restrict (Ioo (0 : ℝ) 1)

/-- The literal weak meridional operator of an actual recoverable minimum is
unweighted L1 through both poles. The complete Euler source and genuine zero
flux traces supply this improvement from the weighted graph; no operator sign
or polar state bound is assumed. -/
theorem IsRecoverableAreaCompetitor.weak_operator_integrable_of_minimum
    {C : ℝ} {K r p z : ℝ → ℝ} (hC : 1 ≤ C)
    (h : IsRecoverableAreaCompetitor C K r p z)
    (hmin : ∀ K' r' p' z' : ℝ → ℝ, IsRecoverableAreaCompetitor C K' r' p' z' →
      weakMeridionalAction K r p z ≤ weakMeridionalAction K' r' p' z') :
    Integrable (weakMeridionalOperator K r p z) areaμ := by
  let lam := weakMeridionalAction K r p z
  let f := warp K
  let b := warpSlope K
  let w := fun x : ℝ => x * (1 - x)
  let P := weakProbeEulerFlux K r p z lam
  let q := fun x => weakProbeEulerMomentum K r p z lam x / f x ^ 2
  let S := fun x => (P x - K x * b x * f x * r x / 2) / f x ^ 2
  let d := fun x => w x / f x
  have hC0 : 0 < C := zero_lt_one.trans_le hC
  have hg := h.geometry_bounds hC
  have hfM : AEStronglyMeasurable f areaμ :=
    ((hg.1.integrableOn_compact isCompact_Icc).mono_set Ioo_subset_Icc_self).aestronglyMeasurable
  have hbM : AEStronglyMeasurable b areaμ :=
    ((hg.2.1.integrableOn_compact isCompact_Icc).mono_set Ioo_subset_Icc_self).aestronglyMeasurable
  have hwpos (x : ℝ) (hx : x ∈ Ioo (0 : ℝ) 1) : 0 < w x :=
    mul_pos hx.1 (sub_pos.mpr hx.2)
  have hflo (x : ℝ) (hx : x ∈ Ioo (0 : ℝ) 1) : (2 / C) * w x ≤ f x := by
    simpa only [w, mul_assoc] using (hg.2.2.1 x ⟨hx.1.le, hx.2.le⟩).1
  have hfpos (x : ℝ) (hx : x ∈ Ioo (0 : ℝ) 1) : 0 < f x :=
    (mul_pos (by positivity) (hwpos x hx)).trans_le (hflo x hx)
  have hdM : AEStronglyMeasurable d areaμ := by
    exact (continuous_id.mul (continuous_const.sub continuous_id)).aestronglyMeasurable.div₀ hfM
  have hdB : ∀ᵐ x ∂areaμ, ‖d x‖ ≤ C / 2 := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
    change ‖w x / f x‖ ≤ C / 2
    rw [Real.norm_eq_abs, abs_of_pos (div_pos (hwpos x hx) (hfpos x hx))]
    apply (div_le_iff₀ (hfpos x hx)).mpr
    have hh := mul_le_mul_of_nonneg_left (hflo x hx) (by positivity : 0 ≤ C / 2)
    have heq : C / 2 * ((2 / C) * w x) = w x := by field_simp [hC0.ne']
    rwa [heq] at hh
  have hd2B : ∀ᵐ x ∂areaμ, ‖d x ^ 2‖ ≤ (C / 2) ^ 2 := by
    filter_upwards [hdB] with x hx
    rw [norm_pow]
    exact pow_le_pow_left₀ (norm_nonneg _) hx 2
  have hKB : ∀ᵐ x ∂areaμ, ‖K x‖ ≤ 2 * C := by
    filter_upwards [hg.2.2.2.2] with x hx
    rw [Real.norm_eq_abs, abs_of_nonneg ((by positivity : (0 : ℝ) ≤ 2 / C).trans hx.1)]
    exact hx.2
  have hbB : ∀ᵐ x ∂areaμ, ‖b x‖ ≤ 2 := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
    exact (hg.2.2.1 x ⟨hx.1.le, hx.2.le⟩).2.2
  obtain ⟨hUA, hPAC, hAAC, hP0, hP1, _hA0, _hA1, hPD, hAD, _hqC, hqeq⟩ :=
    h.probe_euler_flux_of_minimum hC hmin
  change AbsolutelyContinuousOnInterval P 0 1 at hPAC
  change P 0 = 0 at hP0
  change P 1 = 0 at hP1
  change (∀ᵐ x ∂areaμ, HasDerivAt P (-weakProbeZerothCoefficient K r p z lam x) x) at hPD
  have hPM : MemLp (deriv P) 2 areaμ := by
    apply (h.probe_zeroth_coefficient_memLp_two hC lam).neg.ae_eq
    exact hPD.mono fun x hx => hx.deriv.symm
  have hPquot :=
    Analysis.AbsolutelyContinuousOnInterval.integrable_div_endpoints_of_deriv_memLp_two
      hPAC hP0 hP1 hPM
  have hPL : Integrable (fun x => P x / x) areaμ := by
    change IntegrableOn (fun x => P x / x) (Ioo (0 : ℝ) 1) volume
    simpa only [sub_zero] using hPquot.1
  have hPR : Integrable (fun x => P x / (1 - x)) areaμ := hPquot.2
  have hPw : Integrable (fun x => P x / w x) areaμ := by
    apply (hPL.add hPR).congr
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
    change P x / x + P x / (1 - x) = P x / w x
    dsimp only [w]
    field_simp [hx.1.ne', (sub_pos.mpr hx.2).ne']; ring
  have hrI := h.2.1.memLp.integrable (by norm_num : (1 : ENNReal) ≤ 2)
  have htermP := hPw.bdd_mul (hdM.pow 2) hd2B
  have htermR := (((hrI.bdd_mul h.1.aestronglyMeasurable hKB).bdd_mul hbM hbB).const_mul
    (1 / 2 : ℝ)).bdd_mul hdM hdB
  have hSw : Integrable (fun x => w x * S x) areaμ := by
    apply (htermP.sub htermR).congr
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
    change d x ^ 2 * (P x / w x) - d x * ((1 / 2 : ℝ) * (b x * (K x * r x))) =
      w x * S x
    dsimp only [d, S]
    field_simp [(hfpos x hx).ne', (hwpos x hx).ne']
  change weakMeridionalOperator K r p z =ᵐ[areaμ] q at hqeq
  have hfD := (h.primitive_local_regularity hC).1
  have hfCD : ContDiffOn ℝ 1 f (Ioo (0 : ℝ) 1) :=
    (h.primitive_weak_derivatives hC).1.contDiffOn_one_of_continuousOn
      (hg.1.mono Ioo_subset_Icc_self) (hg.2.1.mono Ioo_subset_Icc_self)
  have hqAC (a : ℝ) (ha : a ∈ Ioo (0 : ℝ) 1)
      (d : ℝ) (hd : d ∈ Ioo (0 : ℝ) 1) : AbsolutelyContinuousOnInterval q a d := by
    have hab := ordConnected_Ioo.uIcc_subset ha hd
    have hAad := hAAC.mono (show uIcc a d ⊆ uIcc (0 : ℝ) 1 by
      simpa only [uIcc_of_le zero_le_one] using hab.trans Ioo_subset_Icc_self)
    have hInv : ContDiffOn ℝ 1 (fun x => (f x ^ 2)⁻¹) (uIcc a d) :=
      ((hfCD.pow 2).inv (fun x hx => pow_ne_zero 2 (hfpos x hx).ne')).mono hab
    simpa only [q, f, lam, Pi.mul_def, div_eq_mul_inv] using
      hAad.mul hInv.absolutelyContinuousOnInterval
  have hqD : ∀ᵐ x ∂areaμ, HasDerivAt q (S x) x := by
    filter_upwards [hUA, hAD, ae_restrict_mem measurableSet_Ioo] with x hxA hxAD hxI
    have hfne := (hfpos x hxI).ne'
    have hQ := hxAD.div ((hfD x hxI).pow 2) (pow_ne_zero 2 hfne)
    have hxA' : weakProbeEulerMomentum K r p z lam x =
        f x ^ 2 * weakMeridionalOperator K r p z x := hxA.symm
    change HasDerivAt q _ x
    convert hQ using 1
    simp only [weakProbeFirstCoefficient, Pi.pow_apply, Nat.cast_ofNat,
      Nat.reduceSub, pow_one]
    rw [hxA']
    dsimp only [S, f, b, P, lam]
    field_simp [hfne]
    ring
  have hqI := Analysis.integrable_of_parabolic_weighted_derivative hqAC hqD hSw
  exact hqI.congr hqeq.symm

end RicciFlowSharpEstimate.Geometry.AreaProfile
