/-
Copyright (c) 2026 Ziyang Qin. All rights reserved.
No license is granted by this file.
Authors: Ziyang Qin
-/
import RicciFlowSharpEstimate.Geometry.WeakProbeEulerCoefficients
import RicciFlowSharpEstimate.Analysis.L2WeakMultipliers

/-! # Unweighted square integrability of the complete Euler source -/

noncomputable section
namespace RicciFlowSharpEstimate.Geometry.AreaProfile
open Set MeasureTheory Filter
local notation "areaμ" => volume.restrict (Ioo (0 : ℝ) 1)

/-- The complete zeroth Euler coefficient lies in unweighted L2 for every
recoverable competitor and every mass multiplier. Its full mixed and potential
terms are retained; no endpoint state bound is supplied. -/
theorem IsRecoverableAreaCompetitor.probe_zeroth_coefficient_memLp_two
    {C : ℝ} {K r p z : ℝ → ℝ} (hC : 1 ≤ C)
    (h : IsRecoverableAreaCompetitor C K r p z) (lam : ℝ) :
    MemLp (weakProbeZerothCoefficient K r p z lam) 2 areaμ := by
  have hC0 : 0 < C := zero_lt_one.trans_le hC
  have hg := h.geometry_bounds hC
  let f := warp K
  let b := warpSlope K
  let Q := weakMeridionalOperator K r p z
  have hfM : AEStronglyMeasurable f areaμ :=
    ((hg.1.integrableOn_compact isCompact_Icc).mono_set Ioo_subset_Icc_self).aestronglyMeasurable
  have hbM : AEStronglyMeasurable b areaμ :=
    ((hg.2.1.integrableOn_compact isCompact_Icc).mono_set Ioo_subset_Icc_self).aestronglyMeasurable
  have hpM := h.2.1.weakDeriv.locallyIntegrable_deriv.aestronglyMeasurable
  have hKbox : ∀ᵐ x ∂areaμ, 0 ≤ K x ∧ K x ≤ 2 * C := by
    filter_upwards [hg.2.2.2.2] with x hx
    exact ⟨(by positivity : (0 : ℝ) ≤ 2 / C).trans hx.1, hx.2⟩
  have hfbox : ∀ᵐ x ∂areaμ, 0 ≤ f x ∧ f x ≤ (2 * C) * (x * (1 - x)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
    have hh := hg.2.2.1 x ⟨hx.1.le, hx.2.le⟩
    refine ⟨(mul_nonneg (mul_nonneg (by positivity) hx.1.le)
      (sub_nonneg.mpr hx.2.le)).trans hh.1, ?_⟩
    simpa only [mul_assoc] using hh.2.1
  have hw (x : ℝ) (hx : x ∈ Ioo (0 : ℝ) 1) :
      0 ≤ x * (1 - x) ∧ x * (1 - x) ≤ 1 :=
    ⟨mul_nonneg hx.1.le (sub_nonneg.mpr hx.2.le), by nlinarith [sq_nonneg x]⟩
  have hbnd : ∀ᵐ x ∂areaμ, |b x| ≤ 2 := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
    exact (hg.2.2.1 x ⟨hx.1.le, hx.2.le⟩).2.2
  have hfbnd : ∀ᵐ x ∂areaμ, |f x| ≤ 2 * C := by
    filter_upwards [hfbox, ae_restrict_mem measurableSet_Ioo] with x hx hxI
    rw [abs_of_nonneg hx.1]
    exact hx.2.trans (by nlinarith [(hw x hxI).2])
  have hKbnd : ∀ᵐ x ∂areaμ, |K x| ≤ 2 * C :=
    hKbox.mono fun x hx => by simpa only [abs_of_nonneg hx.1] using hx.2
  have hKM := h.1.aestronglyMeasurable
  have hmK (u : ℝ → ℝ) (hu : MemLp u 2 areaμ) :
      MemLp (fun x => K x * u x) 2 areaμ :=
    Analysis.memLp_mul_of_ae_abs_le hKM hKbnd hu
  have hmb (u : ℝ → ℝ) (hu : MemLp u 2 areaμ) :
      MemLp (fun x => b x * u x) 2 areaμ :=
    Analysis.memLp_mul_of_ae_abs_le hbM hbnd hu
  have hmf (u : ℝ → ℝ) (hu : MemLp u 2 areaμ) :
      MemLp (fun x => f x * u x) 2 areaμ :=
    Analysis.memLp_mul_of_ae_abs_le hfM hfbnd hu
  obtain ⟨hQ, _⟩ := memLp_weak_operator_and_potential_of_warp_bounds
    K r p z (2 * C) h.2.1 (by positivity) hKM hfM hbM hKbox hfbox hbnd
  have hsM := Real.continuous_sqrt.comp_aestronglyMeasurable hfM
  have hsbnd : ∀ᵐ x ∂areaμ, |Real.sqrt (f x)| ≤ Real.sqrt (2 * C) := by
    filter_upwards [hfbox, hfbnd] with x hx hb
    rw [abs_of_nonneg (Real.sqrt_nonneg _)]
    exact Real.sqrt_le_sqrt ((le_abs_self _).trans hb)
  have hfQ : MemLp (fun x => f x * Q x) 2 areaμ := by
    apply (Analysis.memLp_mul_of_ae_abs_le hsM hsbnd hQ).ae_eq
    filter_upwards [hfbox] with x hx
    change Real.sqrt (f x) * (Real.sqrt (f x) * Q x) = f x * Q x
    rw [← mul_assoc, Real.mul_self_sqrt hx.1]
  have hfp : MemLp (fun x => f x * p x) 2 areaμ := by
    apply h.2.1.memLp_weighted_deriv.of_le_mul (c := 2 * C) (hfM.mul hpM)
    filter_upwards [hfbox, ae_restrict_mem measurableSet_Ioo] with x hx hxI
    have hs0 := Real.sqrt_nonneg (x * (1 - x))
    have hs2 := Real.sq_sqrt (hw x hxI).1
    have hs1 : Real.sqrt (x * (1 - x)) ≤ 1 := by nlinarith [(hw x hxI).2]
    have hwle : x * (1 - x) ≤ Real.sqrt (x * (1 - x)) := by
      nlinarith [mul_nonneg hs0 (sub_nonneg.mpr hs1)]
    have hh : f x ≤ (2 * C) * Real.sqrt (x * (1 - x)) :=
      hx.2.trans (mul_le_mul_of_nonneg_left hwle (by positivity))
    change ‖f x * p x‖ ≤ 2 * C * ‖Real.sqrt (x * (1 - x)) * p x‖
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hx.1,
      Real.norm_eq_abs, abs_mul, abs_of_nonneg hs0]
    nlinarith [mul_le_mul_of_nonneg_right hh (abs_nonneg (p x))]
  have hrm := h.2.1.memLp
  have h1 := (hmK _ hfQ).neg
  have h2 := (hmK _ (hmb _ hfp)).const_mul (1 / 2 : ℝ)
  have h3 := hmK _ (hmK _ (hmf _ hrm))
  have h4 := (hmK _ (hmb _ (hmb _ hrm))).const_mul (1 / 2 : ℝ)
  have h5 := (hmf _ hrm).const_mul lam
  apply (((h1.sub h2).add (h3.sub h4)).sub h5).ae_eq
  filter_upwards [] with x
  dsimp only [Pi.sub_apply, Pi.add_apply, Pi.neg_apply, weakProbeZerothCoefficient, f, b, Q]
  ring

end RicciFlowSharpEstimate.Geometry.AreaProfile
