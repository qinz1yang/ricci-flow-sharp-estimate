/-
Copyright (c) 2026 Ziyang Qin. All rights reserved.
No license is granted by this file.
Authors: Ziyang Qin
-/
import RicciFlowSharpEstimate.Analysis.PolarHeadIntegralBounds
import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Integrability from a parabolic divergence flux

A zero-trace absolutely continuous flux of the form `f² p`, with derivative
`f S`, controls the unweighted integrability of `p` when `S` is integrable
and `f` is comparable to the parabolic weight. All coefficient bounds and
producer equations hold almost everywhere, and no measurability of `p` is assumed.
-/

noncomputable section

namespace RicciFlowSharpEstimate.Analysis

open Filter MeasureTheory Set

local notation "areaμ" => volume.restrict (Ioo (0 : ℝ) 1)

private theorem flux_integral_eq_sub {F A : ℝ → ℝ} {a b : ℝ}
    (hF : AbsolutelyContinuousOnInterval F 0 1)
    (hD : ∀ᵐ x ∂areaμ, HasDerivAt F (A x) x)
    (ha : a ∈ Icc (0 : ℝ) 1) (hb : b ∈ Icc (0 : ℝ) 1) :
    (∫ x in a..b, A x) = F b - F a := by
  have haU : a ∈ uIcc (0 : ℝ) 1 := by simpa only [uIcc_of_le zero_le_one] using ha
  have hbU : b ∈ uIcc (0 : ℝ) 1 := by simpa only [uIcc_of_le zero_le_one] using hb
  have hsub : uIcc a b ⊆ uIcc (0 : ℝ) 1 := uIcc_subset_uIcc haU hbU
  calc
    (∫ x in a..b, A x) = ∫ x in a..b, deriv F x := by
      apply intervalIntegral.integral_congr_ae
      filter_upwards [ae_imp_of_ae_restrict hD, volume.ae_ne (0 : ℝ),
        volume.ae_ne (1 : ℝ)] with x hx hx0 hx1 hxI
      have hxC : x ∈ Icc (0 : ℝ) 1 := by
        simpa only [uIcc_of_le zero_le_one] using hsub (uIoc_subset_uIcc hxI)
      exact (hx ⟨lt_of_le_of_ne hxC.1 (Ne.symm hx0),
        lt_of_le_of_ne hxC.2 hx1⟩).deriv.symm
    _ = F b - F a := (hF.mono hsub).integral_deriv_eq_sub

private theorem quotient_bound_of_weight_bound {v w d B : ℝ}
    (hv : 0 ≤ v) (hw : 0 ≤ w) (hd : 0 < d)
    (hvd : v ≤ B * w) (hwd : w ≤ d) : |v / d| ≤ |B| := by
  rw [abs_div, abs_of_nonneg hv, abs_of_pos hd]
  apply (div_le_iff₀ hd).mpr
  exact hvd.trans ((mul_le_mul_of_nonneg_right (le_abs_self B) hw).trans
    (mul_le_mul_of_nonneg_left hwd (abs_nonneg B)))

private theorem quotient_sq_bound {v d lo z : ℝ}
    (hv : 0 < v) (hd : 0 < d) (hlo : 0 < lo) (hvd : lo * d ≤ 2 * v) :
    |z / v ^ 2| ≤ (4 / lo ^ 2) * |z / d ^ 2| := by
  have hv2 : 0 < v ^ 2 := sq_pos_of_pos hv
  have hd2 : 0 < d ^ 2 := sq_pos_of_pos hd
  have hlo2 : 0 < lo ^ 2 := sq_pos_of_pos hlo
  have hsq : lo ^ 2 * d ^ 2 ≤ 4 * v ^ 2 := by
    have hs := mul_self_le_mul_self (mul_nonneg hlo.le hd.le) hvd
    nlinarith only [hs]
  rw [abs_div, abs_of_pos hv2, abs_div, abs_of_pos hd2]
  apply (div_le_iff₀ hv2).mpr
  rw [show (4 / lo ^ 2) * (|z| / d ^ 2) * v ^ 2 =
      (4 * |z| * v ^ 2) / (lo ^ 2 * d ^ 2) by
    field_simp [hlo2.ne', hd2.ne']]
  apply (le_div_iff₀ (mul_pos hlo2 hd2)).mpr
  nlinarith only [mul_le_mul_of_nonneg_left hsq (abs_nonneg z)]

/-- A zero-trace parabolic divergence flux with an integrable source forces
the unweighted coefficient in the flux to be integrable. Measurability of that
coefficient is derived from the flux equation and the positive lower bound. -/
theorem integrable_of_parabolic_divergence_flux
    {f F p S : ℝ → ℝ} {lo hi : ℝ}
    (hf : AEStronglyMeasurable f areaμ) (hlo : 0 < lo)
    (hbounds : ∀ᵐ x ∂areaμ,
      lo * (x * (1 - x)) ≤ f x ∧ f x ≤ hi * (x * (1 - x)))
    (hF : AbsolutelyContinuousOnInterval F 0 1) (h0 : F 0 = 0) (h1 : F 1 = 0)
    (hflux : ∀ᵐ x ∂areaμ, F x = f x ^ 2 * p x)
    (hD : ∀ᵐ x ∂areaμ, HasDerivAt F (f x * S x) x)
    (hS : Integrable S areaμ) : Integrable p areaμ := by
  have hpos : ∀ᵐ x ∂areaμ, 0 < f x := by
    filter_upwards [hbounds, ae_restrict_mem measurableSet_Ioo] with x hx hxI
    exact (mul_pos hlo (mul_pos hxI.1 (sub_pos.mpr hxI.2))).trans_le hx.1
  have hmL : AEStronglyMeasurable (fun x : ℝ => f x / x) areaμ :=
    hf.div₀ measurable_id.aestronglyMeasurable
  have hmR : AEStronglyMeasurable (fun x : ℝ => f x / (1 - x)) areaμ :=
    hf.div₀ (measurable_const.sub measurable_id).aestronglyMeasurable
  have hbL : ∀ᵐ x ∂areaμ, ‖f x / x‖ ≤ |hi| := by
    filter_upwards [hbounds, hpos, ae_restrict_mem measurableSet_Ioo] with x hx hfx hxI
    rw [Real.norm_eq_abs]
    exact quotient_bound_of_weight_bound hfx.le
      (mul_nonneg hxI.1.le (sub_nonneg.mpr hxI.2.le)) hxI.1 hx.2
      (by nlinarith [sq_nonneg x])
  have hbR : ∀ᵐ x ∂areaμ, ‖f x / (1 - x)‖ ≤ |hi| := by
    filter_upwards [hbounds, hpos, ae_restrict_mem measurableSet_Ioo] with x hx hfx hxI
    rw [Real.norm_eq_abs]
    exact quotient_bound_of_weight_bound hfx.le
      (mul_nonneg hxI.1.le (sub_nonneg.mpr hxI.2.le)) (sub_pos.mpr hxI.2) hx.2
      (by nlinarith [sq_nonneg (1 - x)])
  let gL : ℝ → ℝ := fun x => f x / x * S x
  let gR : ℝ → ℝ := fun x => f x / (1 - x) * S x
  have hgL : Integrable gL areaμ := hS.bdd_mul hmL hbL
  have hgR : Integrable gR areaμ := hS.bdd_mul hmR hbR
  have hprimitiveL (x : ℝ) (hx : x ∈ Ioo (0 : ℝ) 1) :
      (∫ t in 0..x, t * gL t) = F x := by
    calc
      (∫ t in 0..x, t * gL t) = ∫ t in 0..x, f t * S t := by
        apply intervalIntegral.integral_congr_Ioo_of_le hx.1.le
        intro t ht
        dsimp only [gL]
        field_simp [ht.1.ne']
      _ = F x - F 0 := flux_integral_eq_sub hF hD ⟨le_rfl, zero_le_one⟩
        ⟨hx.1.le, hx.2.le⟩
      _ = F x := by rw [h0, sub_zero]
  have hQL : Integrable (fun x => F x / x ^ 2) areaμ := by
    refine (integrableOn_div_sq_primitive_of_integrable hgL).congr ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
    exact congrArg (fun z : ℝ => z / x ^ 2) (hprimitiveL x hx)
  have hgRI : IntervalIntegrable gR volume 0 1 :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le zero_le_one).mpr hgR
  have hgRref : Integrable (fun t => gR (1 - t)) areaμ := by
    apply (intervalIntegrable_iff_integrableOn_Ioo_of_le zero_le_one).mp
    simpa only [sub_zero, sub_self] using (hgRI.comp_sub_left 1).symm
  have hprimitiveR (x : ℝ) (hx : x ∈ Ioo (0 : ℝ) 1) :
      (∫ t in 0..x, t * gR (1 - t)) = -F (1 - x) := by
    calc
      (∫ t in 0..x, t * gR (1 - t)) =
          ∫ t in 0..x, f (1 - t) * S (1 - t) := by
        apply intervalIntegral.integral_congr_Ioo_of_le hx.1.le
        intro t ht
        dsimp only [gR]
        rw [sub_sub_cancel]
        field_simp [ht.1.ne']
      _ = ∫ t in (1 - x)..1, f t * S t := by
        simpa only [sub_zero] using
          (intervalIntegral.integral_comp_sub_left (fun t => f t * S t) 1
            (a := 0) (b := x))
      _ = F 1 - F (1 - x) := flux_integral_eq_sub hF hD
        ⟨by linarith [hx.2], by linarith [hx.1]⟩ ⟨zero_le_one, le_rfl⟩
      _ = -F (1 - x) := by rw [h1, zero_sub]
  have hQRneg : Integrable (fun x => -F (1 - x) / x ^ 2) areaμ := by
    refine (integrableOn_div_sq_primitive_of_integrable hgRref).congr ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
    exact congrArg (fun z : ℝ => z / x ^ 2) (hprimitiveR x hx)
  have hQRref : Integrable (fun x => F (1 - x) / x ^ 2) areaμ := by
    apply hQRneg.neg.congr
    filter_upwards [] with x
    change -(-F (1 - x) / x ^ 2) = F (1 - x) / x ^ 2
    ring
  have hQRrefI : IntervalIntegrable (fun x => F (1 - x) / x ^ 2) volume 0 1 :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le zero_le_one).mpr hQRref
  have hQR : Integrable (fun x => F x / (1 - x) ^ 2) areaμ := by
    apply (intervalIntegrable_iff_integrableOn_Ioo_of_le zero_le_one).mp
    simpa only [sub_zero, sub_self, sub_sub_cancel] using (hQRrefI.comp_sub_left 1).symm
  have hFC : ContinuousOn F (Icc (0 : ℝ) 1) := by
    simpa only [uIcc_of_le zero_le_one] using hF.continuousOn
  have hFm : AEStronglyMeasurable F areaμ :=
    (hFC.integrableOn_Icc.mono_set Ioo_subset_Icc_self).aestronglyMeasurable
  have heq : (fun x => F x / f x ^ 2) =ᵐ[areaμ] p := by
    filter_upwards [hflux, hpos] with x hx hfx
    rw [hx]
    field_simp [hfx.ne']
  have hpm : AEStronglyMeasurable p areaμ :=
    (hFm.div₀ (hf.pow 2)).congr heq
  have hC : 0 ≤ 4 / lo ^ 2 := div_nonneg (by norm_num) (sq_nonneg lo)
  refine ((hQL.norm.add hQR.norm).const_mul (4 / lo ^ 2)).mono' hpm ?_
  filter_upwards [hbounds, hpos, heq, ae_restrict_mem measurableSet_Ioo]
    with x hx hfx hpx hxI
  simp only [Real.norm_eq_abs]
  rw [← hpx]
  rcases le_total x (1 / 2 : ℝ) with hhalf | hhalf
  · have hlin : lo * x ≤ 2 * f x := by
      have hm := mul_le_mul_of_nonneg_left (show (1 / 2 : ℝ) ≤ 1 - x by linarith)
        (mul_nonneg hlo.le hxI.1.le)
      nlinarith [hx.1]
    exact (quotient_sq_bound hfx hxI.1 hlo hlin).trans
      (mul_le_mul_of_nonneg_left (le_add_of_nonneg_right (abs_nonneg _)) hC)
  · have hlin : lo * (1 - x) ≤ 2 * f x := by
      have hm := mul_le_mul_of_nonneg_left hhalf
        (mul_nonneg hlo.le (sub_nonneg.mpr hxI.2.le))
      nlinarith [hx.1]
    exact (quotient_sq_bound hfx (sub_pos.mpr hxI.2) hlo hlin).trans
      (mul_le_mul_of_nonneg_left (le_add_of_nonneg_left (abs_nonneg _)) hC)

end RicciFlowSharpEstimate.Analysis
