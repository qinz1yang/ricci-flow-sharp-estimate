/-
Copyright (c) 2026 Ziyang Qin. All rights reserved.
No license is granted by this file.
Authors: Ziyang Qin
-/
import RicciFlowSharpEstimate.Geometry.AreaCurvatureResidualNonzero
import RicciFlowSharpEstimate.Geometry.AreaScaleBalancedMultiplier
import RicciFlowSharpEstimate.Geometry.AreaFreeCurvatureInterval

/-! # A free interval in the actual scale-balanced curvature box -/

noncomputable section
namespace RicciFlowSharpEstimate.Geometry.AreaProfile
open Set MeasureTheory Filter Topology
local notation "areaμ" => volume.restrict (Ioo (0 : ℝ) 1)

private theorem residual_parts_pos {Z : ℝ → ℝ} {C : ℝ}
    (hC : 0 < C) (hZ : Integrable Z areaμ)
    (hb : (∫ x, max (Z x) 0 ∂areaμ) = C * (∫ x, max (-Z x) 0 ∂areaμ))
    (hne : ¬ Z =ᵐ[areaμ] (fun _ => 0)) :
    0 < (∫ x, max (Z x) 0 ∂areaμ) ∧ 0 < (∫ x, max (-Z x) 0 ∂areaμ) := by
  have hiP : Integrable (fun x => max (Z x) 0) areaμ := hZ.sup (integrable_const 0)
  have hiN : Integrable (fun x => max (-Z x) 0) areaμ := hZ.neg.sup (integrable_const 0)
  have hN : 0 < (∫ x, max (-Z x) 0 ∂areaμ) := by
    by_contra hn
    have hN0 : (∫ x, max (-Z x) 0 ∂areaμ) = 0 :=
      le_antisymm (le_of_not_gt hn) (integral_nonneg fun _ => le_max_right _ _)
    have hP0 : (∫ x, max (Z x) 0 ∂areaμ) = 0 := by rw [hb, hN0, mul_zero]
    have hPAE := (integral_eq_zero_iff_of_nonneg_ae
      (Eventually.of_forall fun x => le_max_right (Z x) 0) hiP).mp hP0
    have hNAE := (integral_eq_zero_iff_of_nonneg_ae
      (Eventually.of_forall fun x => le_max_right (-Z x) 0) hiN).mp hN0
    apply hne
    filter_upwards [hPAE, hNAE] with x hxP hxN
    change max (Z x) 0 = 0 at hxP
    change max (-Z x) 0 = 0 at hxN
    have hp := (le_max_left (Z x) 0).trans (le_of_eq hxP)
    have hn := (le_max_left (-Z x) 0).trans (le_of_eq hxN)
    change Z x = 0
    linarith
  exact ⟨by rw [hb]; exact mul_pos hC hN, hN⟩

private theorem original_box_unique {K Z : ℝ → ℝ} {C κ κ' Λ' : ℝ}
    (hC : 0 < C)
    (hcomp : ∀ᵐ x ∂areaμ, (κ < K x → Z x ≤ 0) ∧ (K x < C * κ → 0 ≤ Z x))
    (hP : 0 < (∫ x, max (Z x) 0 ∂areaμ))
    (hN : 0 < (∫ x, max (-Z x) 0 ∂areaμ))
    (hκ' : 0 < κ') (hb : ∀ᵐ x ∂areaμ, κ' ≤ K x ∧ K x ≤ Λ')
    (hratio : Λ' / κ' ≤ C) : κ' = κ ∧ Λ' = C * κ := by
  have hlo : κ' ≤ κ := by
    by_contra hn
    have hh : κ < κ' := lt_of_not_ge hn
    have hzero : (fun x => max (Z x) 0) =ᵐ[areaμ] (fun _ => 0) := by
      filter_upwards [hcomp, hb] with x hx hxb
      exact max_eq_right (hx.1 (hh.trans_le hxb.1))
    have hi : (∫ x, max (Z x) 0 ∂areaμ) = 0 :=
      integral_eq_zero_of_ae hzero
    linarith
  have hhi : C * κ ≤ Λ' := by
    by_contra hn
    have hh : Λ' < C * κ := lt_of_not_ge hn
    have hzero : (fun x => max (-Z x) 0) =ᵐ[areaμ] (fun _ => 0) := by
      filter_upwards [hcomp, hb] with x hx hxb
      exact max_eq_right (neg_nonpos.mpr (hx.2 (hxb.2.trans_lt hh)))
    have hi : (∫ x, max (-Z x) 0 ∂areaμ) = 0 :=
      integral_eq_zero_of_ae hzero
    linarith
  have hcap : Λ' ≤ C * κ' := (div_le_iff₀ hκ').mp hratio
  have he : κ' = κ := le_antisymm hlo
    ((mul_le_mul_iff_of_pos_left hC).mp (hhi.trans hcap))
  refine ⟨he, le_antisymm ?_ hhi⟩
  simpa only [he] using hcap

/-- One actual scale-balanced box has strictly positive residual masses,
genuine lower/upper contacts and an actual free interval with zero centered
residual. The interval's previously existential box is identified by proof
with this chosen box; no common-box or free-region assumption is supplied. -/
theorem IsRecoverableAreaCompetitor.exists_scale_balanced_free_curvature_interval
    {C : ℝ} {K r p z : ℝ → ℝ} (hC : 1 < C)
    (h : IsRecoverableAreaCompetitor C K r p z)
    (hr : ContinuousOn r (Ioo (0 : ℝ) 1))
    (hp : ContinuousOn p (Ioo (0 : ℝ) 1))
    (hzero : weakMeridionalAction K r p z = 0)
    (hmin : ∀ K' r' p' z' : ℝ → ℝ, IsRecoverableAreaCompetitor C K' r' p' z' →
      weakMeridionalAction K r p z ≤ weakMeridionalAction K' r' p' z') :
    ∃ κ t a b η : ℝ, 0 < κ ∧ κ < 2 ∧ 2 < C * κ ∧
      (∀ᵐ x ∂areaμ, κ ≤ K x ∧ K x ≤ C * κ) ∧
      let Z := fun x => weakCurvatureAdjoint K r p z 0 x - t * (x - (1 / 2 : ℝ))
      Integrable Z areaμ ∧ Integrable (fun x => Z x * K x) areaμ ∧
      (∀ᵐ x ∂areaμ, (κ < K x → Z x ≤ 0) ∧ (K x < C * κ → 0 ≤ Z x)) ∧
      (∫ x, Z x * K x ∂areaμ) = 0 ∧
      (∫ x, max (Z x) 0 ∂areaμ) = C * (∫ x, max (-Z x) 0 ∂areaμ) ∧
      (∫ x, weakCurvatureAdjoint K r p z 0 x ∂areaμ) =
        (C - 1) * (∫ x, max (-Z x) 0 ∂areaμ) ∧
      0 < (∫ x, max (Z x) 0 ∂areaμ) ∧ 0 < (∫ x, max (-Z x) 0 ∂areaμ) ∧
      (∀ᵐ x ∂areaμ, (0 < Z x → K x = κ) ∧ (Z x < 0 → K x = C * κ)) ∧
      0 < a ∧ a < b ∧ b < 1 ∧ 0 < η ∧
      (∀ x ∈ Icc a b, η ≤ warp K x ∧ η ≤ |r x|) ∧
      (∀ᵐ x ∂areaμ, x ∈ Icc a b →
        κ + η ≤ K x ∧ K x ≤ C * κ - η ∧ Z x = 0) := by
  obtain ⟨κ, t, hκ, hκ2, h2hi, hbox, hZi, hZKi, hcomp, hZK, hbal, hWbal⟩ :=
    h.exists_scale_balanced_curvature_multiplier hC hzero hmin
  let Z := fun x => weakCurvatureAdjoint K r p z 0 x - t * (x - (1 / 2 : ℝ))
  have hC0 : 0 < C := zero_lt_one.trans hC
  have hnz : ¬ Z =ᵐ[areaμ] (fun _ => 0) :=
    h.curvature_centered_residual_ne_zero_of_minimum hC.le hr hp hzero hmin t
  have hparts := residual_parts_pos hC0 hZi hbal hnz
  have hcontacts : ∀ᵐ x ∂areaμ, (0 < Z x → K x = κ) ∧ (Z x < 0 → K x = C * κ) := by
    filter_upwards [hbox, hcomp] with x hx hc
    constructor
    · intro hz
      exact le_antisymm (le_of_not_gt fun hk => (not_le_of_gt hz) (hc.1 hk)) hx.1
    · intro hz
      exact le_antisymm hx.2 (le_of_not_gt fun hk => (not_le_of_gt hz) (hc.2 hk))
  obtain ⟨κ', Λ', a, b, η, hκ', _, _, hratio, hb', ha, hab, hb, hη, hfr, hmargin⟩ :=
    h.exists_free_curvature_interval hC hr hp hzero hmin
  obtain ⟨heκ, heΛ⟩ := original_box_unique hC0 hcomp hparts.1 hparts.2 hκ' hb' hratio
  rw [heκ, heΛ] at hmargin
  have hMG : ∀ᵐ x ∂areaμ, x ∈ Icc a b → κ + η ≤ K x ∧ K x ≤ C * κ - η :=
    (ae_imp_of_ae_restrict hmargin).filter_mono (ae_mono Measure.restrict_le_self)
  refine ⟨κ, t, a, b, η, hκ, hκ2, h2hi, hbox, hZi, hZKi, hcomp, hZK,
    hbal, hWbal, hparts.1, hparts.2, hcontacts, ha, hab, hb, hη, hfr, ?_⟩
  filter_upwards [hMG, hcomp] with x hx hc hxI
  have hh := hx hxI
  have hl : κ < K x := by linarith [hh.1]
  have hu : K x < C * κ := by linarith [hh.2]
  exact ⟨hh.1, hh.2, le_antisymm (hc.1 hl) (hc.2 hu)⟩

end RicciFlowSharpEstimate.Geometry.AreaProfile
