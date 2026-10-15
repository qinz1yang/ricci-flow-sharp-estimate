/-
Copyright (c) 2026 Ziyang Qin. All rights reserved.
No license is granted by this file.
Authors: Ziyang Qin
-/
import RicciFlowSharpEstimate.Analysis.PolarHeadIntegralBounds
import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun

/-!
# Integrability of a polar flux divided by the coordinate square

An absolutely continuous flux anchored at zero has an integrable quotient
by the coordinate square when its derivative is the coordinate times an
integrable source. The flux is identified with its actual anchored primitive.
-/

noncomputable section

namespace RicciFlowSharpEstimate.Analysis

open Filter MeasureTheory Set

/-- An absolutely continuous flux vanishing at zero, whose derivative is the
coordinate times an integrable source, remains integrable after division by
the coordinate square. No separate measurability of the flux is required. -/
theorem integrableOn_div_sq_of_coordinate_derivative {b : ℝ} {F g : ℝ → ℝ}
    (hF : AbsolutelyContinuousOnInterval F 0 b) (h0 : F 0 = 0)
    (hD : ∀ᵐ x ∂volume.restrict (Ioo 0 b), HasDerivAt F (x * g x) x)
    (hg : IntegrableOn g (Ioo 0 b) volume) :
    IntegrableOn (fun x => F x / x ^ 2) (Ioo 0 b) volume := by
  have hprimitive (x : ℝ) (hx : x ∈ Ioo 0 b) :
      (∫ t in 0..x, t * g t) = F x := by
    have hb : 0 ≤ b := hx.1.le.trans hx.2.le
    have hsub : uIcc (0 : ℝ) x ⊆ uIcc (0 : ℝ) b := by
      rw [uIcc_of_le hx.1.le, uIcc_of_le hb]
      exact Icc_subset_Icc le_rfl hx.2.le
    calc
      (∫ t in 0..x, t * g t) = ∫ t in 0..x, deriv F t := by
        apply intervalIntegral.integral_congr_ae
        filter_upwards [ae_imp_of_ae_restrict hD] with t ht htI
        have ht' : t ∈ Ioc (0 : ℝ) x := by
          simpa only [uIoc_of_le hx.1.le] using htI
        exact (ht ⟨ht'.1, ht'.2.trans_lt hx.2⟩).deriv.symm
      _ = F x - F 0 := (hF.mono hsub).integral_deriv_eq_sub
      _ = F x := by rw [h0, sub_zero]
  refine (integrableOn_div_sq_primitive_of_integrable hg).congr ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
  exact congrArg (fun z : ℝ => z / x ^ 2) (hprimitive x hx)

/-- The corresponding right endpoint estimate uses the true zero flux at b.
No positivity assumption on b is needed for the possibly empty open domain. -/
theorem integrableOn_div_sub_sq_of_distance_derivative {b : ℝ} {F g : ℝ → ℝ}
    (hF : AbsolutelyContinuousOnInterval F 0 b) (hbF : F b = 0)
    (hD : ∀ᵐ x ∂volume.restrict (Ioo 0 b), HasDerivAt F ((b - x) * g x) x)
    (hg : IntegrableOn g (Ioo 0 b) volume) :
    IntegrableOn (fun x => F x / (b - x) ^ 2) (Ioo 0 b) volume := by
  by_cases hb : 0 < b
  · have hgI : IntervalIntegrable g volume 0 b :=
      (intervalIntegrable_iff_integrableOn_Ioo_of_le hb.le).mpr hg
    have hgref : IntegrableOn (fun x => g (b - x)) (Ioo 0 b) volume := by
      apply (intervalIntegrable_iff_integrableOn_Ioo_of_le hb.le).mp
      simpa only [sub_self, sub_zero] using (hgI.comp_sub_left b).symm
    have hprimitive (x : ℝ) (hx : x ∈ Ioo 0 b) :
        (∫ t in 0..x, t * g (b - t)) = -F (b - x) := by
      have ha : 0 < b - x := sub_pos.mpr hx.2
      have hab : b - x ≤ b := by linarith [hx.1]
      have hsub : uIcc (b - x) b ⊆ uIcc (0 : ℝ) b := by
        rw [uIcc_of_le hab, uIcc_of_le hb.le]
        exact Icc_subset_Icc ha.le le_rfl
      calc
        _ = ∫ t in 0..x, (b - (b - t)) * g (b - t) := by
          apply intervalIntegral.integral_congr
          intro t _
          change t * g (b - t) = (b - (b - t)) * g (b - t)
          rw [sub_sub_cancel]
        _ = ∫ t in (b - x)..b, (b - t) * g t := by
          simpa only [sub_zero] using
            (intervalIntegral.integral_comp_sub_left (fun t => (b - t) * g t) b
              (a := 0) (b := x))
        _ = ∫ t in (b - x)..b, deriv F t := by
          apply intervalIntegral.integral_congr_ae
          filter_upwards [ae_imp_of_ae_restrict hD, volume.ae_ne b] with t ht htb htI
          have htC : t ∈ Icc (b - x) b := by
            simpa only [uIcc_of_le hab] using uIoc_subset_uIcc htI
          exact (ht ⟨ha.trans_le htC.1, lt_of_le_of_ne htC.2 htb⟩).deriv.symm
        _ = F b - F (b - x) := (hF.mono hsub).integral_deriv_eq_sub
        _ = -F (b - x) := by rw [hbF, zero_sub]
    have hneg : IntegrableOn (fun x => -F (b - x) / x ^ 2) (Ioo 0 b) volume := by
      apply (integrableOn_div_sq_primitive_of_integrable hgref).congr
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
      exact congrArg (fun z : ℝ => z / x ^ 2) (hprimitive x hx)
    have href : IntegrableOn (fun x => F (b - x) / x ^ 2) (Ioo 0 b) volume := by
      apply hneg.neg.congr
      filter_upwards [] with x
      change -(-F (b - x) / x ^ 2) = F (b - x) / x ^ 2
      ring
    have hi := ((intervalIntegrable_iff_integrableOn_Ioo_of_le hb.le).mpr href).comp_sub_left b
    apply (intervalIntegrable_iff_integrableOn_Ioo_of_le hb.le).mp
    simpa only [sub_self, sub_zero, sub_sub_cancel] using hi.symm
  · simp only [Ioo_eq_empty hb, integrableOn_empty]

end RicciFlowSharpEstimate.Analysis
