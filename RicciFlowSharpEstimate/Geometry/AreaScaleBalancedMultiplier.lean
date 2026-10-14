/-
Copyright (c) 2026 Ziyang Qin. All rights reserved.
No license is granted by this file.
Authors: Ziyang Qin
-/
import RicciFlowSharpEstimate.Analysis.BoxCenteredMomentMultiplier
import RicciFlowSharpEstimate.Analysis.BoxVariationalInequality
import RicciFlowSharpEstimate.Geometry.AreaAdjointScaling
import RicciFlowSharpEstimate.Geometry.AreaCurvatureBoxQualification
import RicciFlowSharpEstimate.Geometry.BoundedCurvatureOptimality

/-!
# Scale-balanced curvature multipliers at an actual zero minimum

Normalizing every positive box comparison by its actual integral preserves
both physical curvature moments and the original ratio cap. Whole-cap
minimality and the cubic adjoint identity therefore give a centered moment
multiplier and exact scalar obstacle balance for the same zero minimum.
No nonzero residual, pole regularity, or operator orientation is asserted.
-/

noncomputable section

namespace RicciFlowSharpEstimate.Geometry.AreaProfile

open Set MeasureTheory Filter
open scoped ENNReal

local notation "areaμ" => volume.restrict (Ioo (0 : ℝ) 1)

private theorem scale_box_integrable {V : ℝ → ℝ} {C : ℝ}
    (hV : AEStronglyMeasurable V areaμ)
    (hbox : ∀ᵐ x ∂areaμ, 1 ≤ V x ∧ V x ≤ C) :
    Integrable V areaμ := by
  refine (integrable_const C).mono' hV ?_
  filter_upwards [hbox] with x hx
  rw [Real.norm_eq_abs, abs_of_nonneg (zero_le_one.trans hx.1)]
  exact hx.2

private theorem scale_weighted_box_integrable {W V : ℝ → ℝ} {lo hi : ℝ}
    (hW : Integrable W areaμ) (hV : AEStronglyMeasurable V areaμ)
    (hlo : 0 ≤ lo) (hbox : ∀ᵐ x ∂areaμ, lo ≤ V x ∧ V x ≤ hi) :
    Integrable (fun x => W x * V x) areaμ := by
  apply hW.mul_bdd hV (c := hi)
  filter_upwards [hbox] with x hx
  rw [Real.norm_eq_abs, abs_of_nonneg (hlo.trans hx.1)]
  exact hx.2

private theorem scale_first_moment_integrable {V : ℝ → ℝ}
    (hV : Integrable V areaμ) :
    Integrable (fun x => x * V x) areaμ := by
  apply hV.bdd_mul continuous_id.aestronglyMeasurable (c := 1)
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
  rw [Real.norm_eq_abs]
  change |x| ≤ 1
  rw [abs_of_pos hx.1]
  exact hx.2.le

private theorem scale_centered_integral {V : ℝ → ℝ}
    (hV : Integrable V areaμ) :
    (∫ x, (x - (1 / 2 : ℝ)) * V x ∂areaμ) =
      (∫ x, x * V x ∂areaμ) - (1 / 2 : ℝ) * (∫ x, V x ∂areaμ) := by
  calc
    _ = ∫ x, x * V x - (1 / 2 : ℝ) * V x ∂areaμ := by
      apply integral_congr_ae
      exact Eventually.of_forall fun x => by ring
    _ = _ := by
      rw [integral_sub (scale_first_moment_integrable hV) (hV.const_mul (1 / 2)),
        integral_const_mul]

private theorem normalized_scale_box_curvature
    {C : ℝ} {V : ℝ → ℝ}
    (hV : AEStronglyMeasurable V areaμ)
    (hbox : ∀ᵐ x ∂areaμ, 1 ≤ V x ∧ V x ≤ C)
    (hm : (∫ x, (x - (1 / 2 : ℝ)) * V x ∂areaμ) = 0) :
    0 < 2 / (∫ x, V x ∂areaμ) ∧
      IsBoundedAreaCurvature C (fun x => (2 / (∫ y, V y ∂areaμ)) * V x) := by
  have hVi := scale_box_integrable hV hbox
  let M : ℝ := ∫ x, V x ∂areaμ
  have hMone : 1 ≤ M := by
    have hh := integral_mono_ae (integrable_const (1 : ℝ)) hVi
      (hbox.mono fun _ hx => hx.1)
    simpa [M] using hh
  have hM : 0 < M := zero_lt_one.trans_le hMone
  let α : ℝ := 2 / M
  have hα : 0 < α := div_pos (by norm_num) hM
  have hJm : AEStronglyMeasurable (fun x => α * V x) areaμ := hV.const_mul α
  have hJbox : ∀ᵐ x ∂areaμ, α ≤ α * V x ∧ α * V x ≤ C * α := by
    filter_upwards [hbox] with x hx
    constructor
    · simpa only [mul_one] using mul_le_mul_of_nonneg_left hx.1 hα.le
    · simpa only [mul_comm] using mul_le_mul_of_nonneg_left hx.2 hα.le
  have hratio : (C * α) / α ≤ C := by
    have heq : (C * α) / α = C := by field_simp [hα.ne']
    exact heq.le
  have hJ0 : (∫ x, α * V x ∂areaμ) = 2 := by
    rw [integral_const_mul]
    change (2 / M) * M = 2
    exact div_mul_cancel₀ _ hM.ne'
  have hVm : (∫ x, x * V x ∂areaμ) = M / 2 := by
    rw [scale_centered_integral hVi] at hm
    change (∫ x, x * V x ∂areaμ) - (1 / 2 : ℝ) * M = 0 at hm
    linarith
  have hJ1 : (∫ x, x * (α * V x) ∂areaμ) = 1 := by
    calc
      _ = α * (∫ x, x * V x ∂areaμ) := by
        rw [← integral_const_mul]
        apply integral_congr_ae
        exact Eventually.of_forall fun x => by ring
      _ = 1 := by
        rw [hVm]
        dsimp only [α]
        field_simp [hM.ne']
  refine ⟨hα, hJm, ⟨α, C * α, hα, hJbox, hratio⟩, ?_, ?_⟩
  · simpa only [intervalIntegral.integral_of_le zero_le_one,
      integral_Ioc_eq_integral_Ioo] using hJ0
  · simpa only [intervalIntegral.integral_of_le zero_le_one,
      integral_Ioc_eq_integral_Ioo] using hJ1

private theorem scale_complementarity_product (lo hi k w : ℝ)
    (hbox : lo ≤ k ∧ k ≤ hi)
    (hsign : (lo < k → w ≤ 0) ∧ (k < hi → 0 ≤ w)) :
    w * k = lo * max w 0 - hi * max (-w) 0 := by
  rcases lt_trichotomy w 0 with hw | hw | hw
  · have hk : k = hi := le_antisymm hbox.2
      (le_of_not_gt fun hlt => (not_le_of_gt hw) (hsign.2 hlt))
    rw [hk, max_eq_right hw.le, max_eq_left (neg_nonneg.mpr hw.le)]
    ring
  · simp only [hw, zero_mul, neg_zero, max_self, mul_zero, sub_self]
  · have hk : k = lo := le_antisymm
      (le_of_not_gt fun hlt => (not_le_of_gt hw) (hsign.1 hlt)) hbox.1
    rw [hk, max_eq_left hw.le, max_eq_right (neg_nonpos.mpr hw.le)]
    ring

/-- The actual zero-action global minimum has a centered moment multiplier
balanced under variation of the original positive box scale. The returned
curvature is the same K, with its own box [κ,Cκ]; all residual pairings and
positive-part balances are genuine integrals. Strict residual nonvanishing
and operator orientation are not assumed or concluded. -/
theorem IsRecoverableAreaCompetitor.exists_scale_balanced_curvature_multiplier
    {C : ℝ} {K r p z : ℝ → ℝ} (hC : 1 < C)
    (h : IsRecoverableAreaCompetitor C K r p z)
    (hzero : weakMeridionalAction K r p z = 0)
    (hmin : ∀ K' r' p' z' : ℝ → ℝ, IsRecoverableAreaCompetitor C K' r' p' z' →
      weakMeridionalAction K r p z ≤ weakMeridionalAction K' r' p' z') :
    ∃ κ t : ℝ, 0 < κ ∧ κ < 2 ∧ 2 < C * κ ∧
      (∀ᵐ x ∂areaμ, κ ≤ K x ∧ K x ≤ C * κ) ∧
      let Z : ℝ → ℝ := fun x =>
        weakCurvatureAdjoint K r p z 0 x - t * (x - (1 / 2 : ℝ))
      Integrable Z areaμ ∧ Integrable (fun x => Z x * K x) areaμ ∧
      (∀ᵐ x ∂areaμ, (κ < K x → Z x ≤ 0) ∧ (K x < C * κ → 0 ≤ Z x)) ∧
      (∫ x, Z x * K x ∂areaμ) = 0 ∧
      (∫ x, max (Z x) 0 ∂areaμ) = C * (∫ x, max (-Z x) 0 ∂areaμ) ∧
      (∫ x, weakCurvatureAdjoint K r p z 0 x ∂areaμ) =
        (C - 1) * (∫ x, max (-Z x) 0 ∂areaμ) := by
  let W : ℝ → ℝ := weakCurvatureAdjoint K r p z 0
  have hW : Integrable W areaμ := h.weakCurvatureAdjoint_integrable hC.le 0
  have hscale := h.curvature_adjoint_scale_identity hC.le 0
  have hWKi : Integrable (fun x => W x * K x) areaμ := hscale.1
  have hWKzero : (∫ x, W x * K x ∂areaμ) = 0 := by
    simpa only [W, hzero, zero_mul, mul_zero, sub_zero] using hscale.2
  obtain ⟨κ, Λ, hκ, hκ2, h2Λ, hKbox, hratio⟩ :=
    h.curvature_bounded.exists_strict_box hC
  have hΛ : Λ ≤ C * κ := (div_le_iff₀ hκ).mp hratio
  have h2Cκ : 2 < C * κ := h2Λ.trans_le hΛ
  have hbox : ∀ᵐ x ∂areaμ, κ ≤ K x ∧ K x ≤ C * κ := by
    filter_upwards [hKbox] with x hx
    exact ⟨hx.1, hx.2.trans hΛ⟩
  have hKi : Integrable K areaμ := h.1.integrable (by norm_num : (1 : ENNReal) ≤ 2)
  have hK0 : (∫ x, K x ∂areaμ) = 2 := by
    simpa only [intervalIntegral.integral_of_le zero_le_one, integral_Ioc_eq_integral_Ioo]
      using h.2.2.2.1
  have hK1 : (∫ x, x * K x ∂areaμ) = 1 := by
    simpa only [intervalIntegral.integral_of_le zero_le_one, integral_Ioc_eq_integral_Ioo]
      using h.2.2.2.2.1
  have hKcenter : (∫ x, (x - (1 / 2 : ℝ)) * K x ∂areaμ) = 0 := by
    rw [scale_centered_integral hKi, hK0, hK1]
    norm_num
  have hcost_nonneg (V : ℝ → ℝ) (hV : AEStronglyMeasurable V areaμ)
      (hVbox : ∀ᵐ x ∂areaμ, 1 ≤ V x ∧ V x ≤ C)
      (hVm : (∫ x, (x - (1 / 2 : ℝ)) * V x ∂areaμ) = 0) :
      0 ≤ ∫ x, W x * V x ∂areaμ := by
    obtain ⟨hα, hJ⟩ := normalized_scale_box_curvature hV hVbox hVm
    let α : ℝ := 2 / (∫ x, V x ∂areaμ)
    have hWV : Integrable (fun x => W x * V x) areaμ :=
      scale_weighted_box_integrable hW hV zero_le_one hVbox
    have hcomp := h.bounded_curvature_adjoint_inequality_of_minimum hC.le hmin
      (fun x => α * V x) hJ
    have hcomp' : 0 ≤ ∫ x, W x * (α * V x - K x) ∂areaμ := by
      simpa only [hzero, intervalIntegral.integral_of_le zero_le_one,
        integral_Ioc_eq_integral_Ioo, W] using hcomp
    have hidentity : (∫ x, W x * (α * V x - K x) ∂areaμ) =
        α * (∫ x, W x * V x ∂areaμ) := by
      calc
        _ = ∫ x, α * (W x * V x) - W x * K x ∂areaμ := by
          apply integral_congr_ae
          exact Eventually.of_forall fun x => by ring
        _ = _ := by
          rw [integral_sub (hWV.const_mul α) hWKi, integral_const_mul, hWKzero, sub_zero]
    rw [hidentity] at hcomp'
    change 0 < α at hα
    nlinarith
  let V0 : ℝ → ℝ := fun x => (1 / κ) * K x
  have hV0 : AEStronglyMeasurable V0 areaμ := h.1.aestronglyMeasurable.const_mul (1 / κ)
  have hinv : 0 < 1 / κ := one_div_pos.mpr hκ
  have hunit : (1 / κ) * κ = 1 := one_div_mul_cancel hκ.ne'
  have hcap : (1 / κ) * (C * κ) = C := by field_simp [hκ.ne']
  have hV0box : ∀ᵐ x ∂areaμ, 1 ≤ V0 x ∧ V0 x ≤ C := by
    filter_upwards [hbox] with x hx
    have hl := mul_le_mul_of_nonneg_left hx.1 hinv.le
    have hu := mul_le_mul_of_nonneg_left hx.2 hinv.le
    rw [hunit] at hl
    rw [hcap] at hu
    exact ⟨hl, hu⟩
  have hV0center : (∫ x, (x - (1 / 2 : ℝ)) * V0 x ∂areaμ) = 0 := by
    calc
      _ = (1 / κ) * (∫ x, (x - (1 / 2 : ℝ)) * K x ∂areaμ) := by
        rw [← integral_const_mul]
        apply integral_congr_ae
        exact Eventually.of_forall fun x => by dsimp only [V0]; ring
      _ = 0 := by rw [hKcenter, mul_zero]
  have hWV0zero : (∫ x, W x * V0 x ∂areaμ) = 0 := by
    calc
      _ = (1 / κ) * (∫ x, W x * K x ∂areaμ) := by
        rw [← integral_const_mul]
        apply integral_congr_ae
        exact Eventually.of_forall fun x => by dsimp only [V0]; ring
      _ = 0 := by rw [hWKzero, mul_zero]
  have hWV0 : Integrable (fun x => W x * V0 x) areaμ :=
    scale_weighted_box_integrable hW hV0 zero_le_one hV0box
  have hVmin (V : ℝ → ℝ) (hV : AEStronglyMeasurable V areaμ)
      (hVbox : ∀ᵐ x ∂areaμ, 1 ≤ V x ∧ V x ≤ C)
      (hVm : (∫ x, (x - (1 / 2 : ℝ)) * V x ∂areaμ) = 0) :
      0 ≤ ∫ x, W x * (V x - V0 x) ∂areaμ := by
    have hWV := scale_weighted_box_integrable hW hV zero_le_one hVbox
    have heq : (∫ x, W x * (V x - V0 x) ∂areaμ) =
        ∫ x, W x * V x ∂areaμ := by
      calc
        _ = ∫ x, W x * V x - W x * V0 x ∂areaμ := by
          apply integral_congr_ae
          exact Eventually.of_forall fun x => by ring
        _ = _ := by rw [integral_sub hWV hWV0, hWV0zero, sub_zero]
    rw [heq]
    exact hcost_nonneg V hV hVbox hVm
  obtain ⟨t, ht⟩ := Analysis.exists_box_centered_moment_multiplier
    W V0 1 C hC hW hV0 hV0box hV0center hVmin
  let Z : ℝ → ℝ := fun x => W x - t * (x - (1 / 2 : ℝ))
  have hgi : Integrable (fun x : ℝ => x - (1 / 2 : ℝ)) areaμ :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le zero_le_one).mp
      ((continuous_id.sub continuous_const).intervalIntegrable 0 1)
  have hZi : Integrable Z areaμ := hW.sub (hgi.const_mul t)
  have hsignV := (Analysis.box_variational_inequality_iff hZi hV0 hV0box).mp ht
  have hsign : ∀ᵐ x ∂areaμ,
      (κ < K x → Z x ≤ 0) ∧ (K x < C * κ → 0 ≤ Z x) := by
    filter_upwards [hsignV] with x hx
    constructor
    · intro hk
      have hh := mul_lt_mul_of_pos_left hk hinv
      rw [hunit] at hh
      exact hx.1 hh
    · intro hk
      have hh := mul_lt_mul_of_pos_left hk hinv
      rw [hcap] at hh
      exact hx.2 hh
  have hZKi : Integrable (fun x => Z x * K x) areaμ :=
    scale_weighted_box_integrable hZi h.1.aestronglyMeasurable hκ.le hbox
  have hgKi : Integrable (fun x => (x - (1 / 2 : ℝ)) * K x) areaμ := by
    apply ((scale_first_moment_integrable hKi).sub (hKi.const_mul (1 / 2))).congr
    filter_upwards [] with x
    change x * K x - (1 / 2 : ℝ) * K x = (x - (1 / 2 : ℝ)) * K x
    ring
  have hZKzero : (∫ x, Z x * K x ∂areaμ) = 0 := by
    calc
      _ = ∫ x, W x * K x - t * ((x - (1 / 2 : ℝ)) * K x) ∂areaμ := by
        apply integral_congr_ae
        exact Eventually.of_forall fun x => by dsimp only [Z]; ring
      _ = 0 := by
        rw [integral_sub hWKi (hgKi.const_mul t), integral_const_mul,
          hWKzero, hKcenter, mul_zero, sub_self]
  have hZp : Integrable (fun x => max (Z x) 0) areaμ :=
    hZi.sup (integrable_zero ℝ ℝ areaμ)
  have hZn : Integrable (fun x => max (-Z x) 0) areaμ :=
    hZi.neg.sup (integrable_zero ℝ ℝ areaμ)
  have hproduct : (∫ x, Z x * K x ∂areaμ) =
      κ * (∫ x, max (Z x) 0 ∂areaμ) -
        (C * κ) * (∫ x, max (-Z x) 0 ∂areaμ) := by
    calc
      _ = ∫ x, κ * max (Z x) 0 - (C * κ) * max (-Z x) 0 ∂areaμ := by
        apply integral_congr_ae
        filter_upwards [hbox, hsign] with x hb hs
        exact scale_complementarity_product κ (C * κ) (K x) (Z x) hb hs
      _ = _ := by
        rw [integral_sub (hZp.const_mul κ) (hZn.const_mul (C * κ)),
          integral_const_mul, integral_const_mul]
  have hbalance : (∫ x, max (Z x) 0 ∂areaμ) =
      C * (∫ x, max (-Z x) 0 ∂areaμ) := by
    have hz : κ * ((∫ x, max (Z x) 0 ∂areaμ) -
        C * (∫ x, max (-Z x) 0 ∂areaμ)) = 0 := by
      rw [hZKzero] at hproduct
      nlinarith only [hproduct]
    exact sub_eq_zero.mp ((mul_eq_zero.mp hz).resolve_left hκ.ne')
  have hgzero : (∫ x : ℝ, x - (1 / 2 : ℝ) ∂areaμ) = 0 := by
    rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le zero_le_one]
    have hxi : IntervalIntegrable (fun x : ℝ => x) volume 0 1 :=
      continuous_id.intervalIntegrable 0 1
    have hci : IntervalIntegrable (fun _ : ℝ => (1 / 2 : ℝ)) volume 0 1 :=
      continuous_const.intervalIntegrable 0 1
    rw [intervalIntegral.integral_sub hxi hci]
    norm_num [integral_id]
  have hZint : (∫ x, Z x ∂areaμ) = ∫ x, W x ∂areaμ := by
    dsimp only [Z]
    rw [integral_sub hW (hgi.const_mul t), integral_const_mul,
      hgzero, mul_zero, sub_zero]
  have hparts : (∫ x, Z x ∂areaμ) =
      (∫ x, max (Z x) 0 ∂areaμ) - (∫ x, max (-Z x) 0 ∂areaμ) := by
    calc
      _ = ∫ x, max (Z x) 0 - max (-Z x) 0 ∂areaμ := by
        apply integral_congr_ae
        filter_upwards [] with x
        by_cases hx : 0 ≤ Z x
        · rw [max_eq_left hx, max_eq_right (neg_nonpos.mpr hx), sub_zero]
        · have hx' : Z x ≤ 0 := (lt_of_not_ge hx).le
          rw [max_eq_right hx', max_eq_left (neg_nonneg.mpr hx')]
          ring
      _ = _ := integral_sub hZp hZn
  have hWbalance : (∫ x, W x ∂areaμ) =
      (C - 1) * (∫ x, max (-Z x) 0 ∂areaμ) := by
    rw [← hZint, hparts, hbalance]
    ring
  exact ⟨κ, t, hκ, hκ2, h2Cκ, hbox, hZi, hZKi, hsign, hZKzero, hbalance, hWbalance⟩

end RicciFlowSharpEstimate.Geometry.AreaProfile
