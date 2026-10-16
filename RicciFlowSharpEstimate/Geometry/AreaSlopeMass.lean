/-
Copyright (c) 2026 Ziyang Qin. All rights reserved.
No license is granted by this file.
Authors: Ziyang Qin
-/
import RicciFlowSharpEstimate.Geometry.RecoverableAreaGeometry

/-!
# Strict positivity of the slope-weighted probe mass

The primitive slope of an integrable curvature with a positive lower bound
is strictly decreasing. Its zero set is therefore negligible, so inserting
its square into the mass density of a recoverable unit-mass probe preserves
strict positivity without imposing continuity on that probe.
-/

noncomputable section

namespace RicciFlowSharpEstimate.Geometry.AreaProfile

open Set MeasureTheory Filter

local notation "areaμ" => volume.restrict (Ioo (0 : ℝ) 1)

private theorem strictAntiOn_warpSlope_of_positive_lower_bound
    {K : ℝ → ℝ} {κ : ℝ} (hK : IntegrableOn K (Ioo (0 : ℝ) 1))
    (hκ : 0 < κ) (hbound : ∀ᵐ x ∂areaμ, κ ≤ K x) :
    StrictAntiOn (warpSlope K) (Icc (0 : ℝ) 1) := by
  intro x hx y hy hxy
  have hsub : Ioo x y ⊆ Ioo (0 : ℝ) 1 := by
    intro t ht
    exact ⟨hx.1.trans_lt ht.1, ht.2.trans_le hy.2⟩
  have hKxy : IntegrableOn K (Ioo x y) := hK.mono_set hsub
  have hboundxy : ∀ᵐ t ∂volume.restrict (Ioo x y), κ ≤ K t :=
    ae_restrict_of_ae_restrict_of_subset hsub hbound
  have hlower : (y - x) * κ ≤ ∫ t in x..y, K t := by
    calc
      (y - x) * κ = ∫ _t in x..y, κ := by
        rw [intervalIntegral.integral_const, smul_eq_mul]
      _ = ∫ _t in Ioo x y, κ := by
        rw [intervalIntegral.integral_of_le hxy.le, integral_Ioc_eq_integral_Ioo]
      _ ≤ ∫ t in Ioo x y, K t :=
        integral_mono_ae (integrable_const κ) hKxy hboundxy
      _ = ∫ t in x..y, K t := by
        rw [intervalIntegral.integral_of_le hxy.le, integral_Ioc_eq_integral_Ioo]
  have hpos : 0 < ∫ t in x..y, K t :=
    (mul_pos (sub_pos.mpr hxy) hκ).trans_le hlower
  have hK0x : IntervalIntegrable K volume 0 x := by
    apply (intervalIntegrable_iff_integrableOn_Ioo_of_le hx.1).2
    apply hK.mono_set
    intro t ht
    exact ⟨ht.1, ht.2.trans_le hx.2⟩
  have hKxy' : IntervalIntegrable K volume x y :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le hxy.le).2 hKxy
  have hadd := intervalIntegral.integral_add_adjacent_intervals hK0x hKxy'
  dsimp only [warpSlope]
  linarith only [hadd, hpos]

/-- The actual slope square has strictly positive mass against every
recoverable unit-mass probe, including probes represented only in L². -/
theorem IsRecoverableAreaCompetitor.integral_warp_mul_slope_sq_mul_probe_sq_pos
    {C : ℝ} {K r p z : ℝ → ℝ} (hC : 1 ≤ C)
    (h : IsRecoverableAreaCompetitor C K r p z) :
    0 < ∫ x, warp K x * (warpSlope K x) ^ 2 * r x ^ 2 ∂areaμ := by
  have hgeometry := h.geometry_bounds hC
  have hCpos : 0 < C := zero_lt_one.trans_le hC
  obtain ⟨κ, Λ, hκ, hbox, _⟩ := h.2.2.1
  have hanti : StrictAntiOn (warpSlope K) (Icc (0 : ℝ) 1) :=
    strictAntiOn_warpSlope_of_positive_lower_bound
      (h.1.integrable (by norm_num)) hκ (hbox.mono fun _ hx => hx.1)
  have hbne : ∀ᵐ x ∂areaμ, warpSlope K x ≠ 0 := by
    by_cases hex : ∃ c ∈ Ioo (0 : ℝ) 1, warpSlope K c = 0
    · obtain ⟨c, hc, hc0⟩ := hex
      filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Ioo,
        (volume.restrict (Ioo (0 : ℝ) 1)).ae_ne c] with x hx hxc
      intro hx0
      exact hxc (hanti.injOn ⟨hx.1.le, hx.2.le⟩ ⟨hc.1.le, hc.2.le⟩
        (hx0.trans hc0.symm))
    · filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Ioo] with x hx
      intro hx0
      exact hex ⟨x, hx, hx0⟩
  have hf : AEStronglyMeasurable (warp K) areaμ :=
    ((hgeometry.1.integrableOn_compact isCompact_Icc).mono_set
      Ioo_subset_Icc_self).aestronglyMeasurable
  have hb : AEStronglyMeasurable (warpSlope K) areaμ :=
    ((hgeometry.2.1.integrableOn_compact isCompact_Icc).mono_set
      Ioo_subset_Icc_self).aestronglyMeasurable
  have hfnonneg : ∀ᵐ x ∂areaμ, 0 ≤ warp K x := by
    filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Ioo] with x hx
    have hfx := (hgeometry.2.2.1 x ⟨hx.1.le, hx.2.le⟩).1
    exact (mul_nonneg (mul_nonneg (by positivity : 0 ≤ 2 / C) hx.1.le)
      (sub_nonneg.mpr hx.2.le)).trans hfx
  have hfnorm : ∀ᵐ x ∂areaμ, ‖warp K x‖ ≤ 2 * C := by
    filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Ioo,
      hfnonneg] with x hx hfx0
    rw [Real.norm_eq_abs, abs_of_nonneg hfx0]
    have hw : x * (1 - x) ≤ 1 := by
      nlinarith only [hx.2, sq_nonneg x]
    calc
      warp K x ≤ (2 * C) * x * (1 - x) :=
        (hgeometry.2.2.1 x ⟨hx.1.le, hx.2.le⟩).2.1
      _ = (2 * C) * (x * (1 - x)) := by ring
      _ ≤ 2 * C := mul_le_of_le_one_right (by positivity) hw
  have hbnorm : ∀ᵐ x ∂areaμ, ‖warpSlope K x‖ ≤ 2 := by
    filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Ioo] with x hx
    simpa only [Real.norm_eq_abs] using
      (hgeometry.2.2.1 x ⟨hx.1.le, hx.2.le⟩).2.2
  have hmassInt : Integrable (fun x => warp K x * r x ^ 2) areaμ :=
    h.2.1.integrable_sq.bdd_mul hf hfnorm
  have htargetInt :
      Integrable (fun x => warp K x * (warpSlope K x) ^ 2 * r x ^ 2) areaμ := by
    apply ((hmassInt.bdd_mul hb hbnorm).bdd_mul hb hbnorm).congr
    exact ae_of_all _ (fun x => by ring)
  have htargetNonneg :
      0 ≤ᵐ[areaμ] (fun x => warp K x * (warpSlope K x) ^ 2 * r x ^ 2) := by
    filter_upwards [hfnonneg] with x hx
    exact mul_nonneg (mul_nonneg hx (sq_nonneg _)) (sq_nonneg _)
  by_contra hn
  have hzero : (∫ x, warp K x * (warpSlope K x) ^ 2 * r x ^ 2 ∂areaμ) = 0 :=
    le_antisymm (le_of_not_gt hn) (integral_nonneg_of_ae htargetNonneg)
  have hzeroae := (integral_eq_zero_iff_of_nonneg_ae htargetNonneg htargetInt).1 hzero
  have hmassae : (fun x => warp K x * r x ^ 2) =ᵐ[areaμ] 0 := by
    filter_upwards [hzeroae, hbne] with x hx hbx
    have heq : (warp K x * r x ^ 2) * (warpSlope K x) ^ 2 = 0 := by
      calc
        (warp K x * r x ^ 2) * (warpSlope K x) ^ 2 =
            warp K x * (warpSlope K x) ^ 2 * r x ^ 2 := by ring
        _ = 0 := hx
    exact (mul_eq_zero.mp heq).resolve_right (pow_ne_zero 2 hbx)
  have hmass0 : probeMass K r = 0 := by
    rw [probeMass, intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1),
      integral_Ioc_eq_integral_Ioo]
    exact integral_eq_zero_of_ae hmassae
  have hmass1 : probeMass K r = 1 := h.2.2.2.2.2.1
  linarith only [hmass0, hmass1]

end RicciFlowSharpEstimate.Geometry.AreaProfile
