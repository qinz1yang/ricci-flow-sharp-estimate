/-
Copyright (c) 2026 Ziyang Qin. All rights reserved.
No license is granted by this file.
Authors: Ziyang Qin
-/
import Mathlib.Analysis.SpecialFunctions.NonIntegrable
import Mathlib.Tactic.Linarith

/-!
# Endpoint traces forced by reciprocal integrability

A continuous function on a nondegenerate closed interval vanishes at an
endpoint if its quotient by the distance to that endpoint is integrable on
the open interval. These results obtain the trace from integrability itself.
-/

noncomputable section

namespace RicciFlowSharpEstimate.Analysis

open MeasureTheory Set

/-- Integrability after division by the distance to the left endpoint forces
the continuous endpoint value to vanish. -/
theorem eq_zero_of_integrableOn_div_left
    {a b : ℝ} {F : ℝ → ℝ} (hab : a < b)
    (hF : ContinuousOn F (Icc a b))
    (hI : IntegrableOn (fun x ↦ F x / (x - a)) (Ioo a b)) : F a = 0 := by
  by_contra hFa
  obtain ⟨δ, hδ, hδF⟩ :=
    Metric.continuousWithinAt_iff.mp (hF a ⟨le_rfl, hab.le⟩)
      |F a| (abs_pos.mpr hFa)
  obtain ⟨c, hac, hcb, hcδ⟩ : ∃ c : ℝ, a < c ∧ c < b ∧ c - a < δ := by
    have hm : 0 < min δ (b - a) := lt_min hδ (sub_pos.mpr hab)
    have hmδ : min δ (b - a) ≤ δ := min_le_left _ _
    have hmb : min δ (b - a) ≤ b - a := min_le_right _ _
    refine ⟨a + min δ (b - a) / 2, ?_, ?_, ?_⟩ <;> linarith
  have hsub : Icc a c ⊆ Icc a b := by
    intro x hx
    exact ⟨hx.1, hx.2.trans hcb.le⟩
  have hnonzero : ∀ x ∈ Icc a c, F x ≠ 0 := by
    intro x hx hzero
    have hdist : dist x a < δ := by
      rw [Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr hx.1)]
      exact (sub_le_sub_right hx.2 a).trans_lt hcδ
    have hclose := hδF (hsub hx) hdist
    simp [hzero, Real.dist_eq] at hclose
  have hInvF : ContinuousOn (fun x ↦ (F x)⁻¹) (uIcc a c) := by
    rw [uIcc_of_le hac.le]
    exact (hF.mono hsub).inv₀ hnonzero
  have hQ : IntervalIntegrable (fun x ↦ F x / (x - a)) volume a c := by
    apply (intervalIntegrable_iff_integrableOn_Ioo_of_le hac.le).2
    exact hI.mono_set fun x hx ↦ ⟨hx.1, hx.2.trans hcb⟩
  have hprod : IntegrableOn (fun x ↦ F x / (x - a) * (F x)⁻¹) (Ioo a c) :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le hac.le).1
      (hQ.mul_continuousOn hInvF)
  have hInv : IntegrableOn (fun x ↦ (x - a)⁻¹) (Ioo a c) := by
    refine hprod.congr_fun ?_ measurableSet_Ioo
    intro x hx
    have hFx := hnonzero x ⟨hx.1.le, hx.2.le⟩
    simp only [div_eq_mul_inv]
    rw [mul_right_comm, mul_inv_cancel₀ hFx, one_mul]
  have hInvInterval : IntervalIntegrable (fun x ↦ (x - a)⁻¹) volume a c :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le hac.le).2 hInv
  rcases intervalIntegrable_sub_inv_iff.mp hInvInterval with heq | hnotmem
  · exact hac.ne heq
  · exact hnotmem (by simp [hac.le])

/-- Integrability after division by the distance to the right endpoint forces
the continuous endpoint value to vanish. -/
theorem eq_zero_of_integrableOn_div_right
    {a b : ℝ} {F : ℝ → ℝ} (hab : a < b)
    (hF : ContinuousOn F (Icc a b))
    (hI : IntegrableOn (fun x ↦ F x / (b - x)) (Ioo a b)) : F b = 0 := by
  have hneg : -b < -a := neg_lt_neg hab
  have hFneg : ContinuousOn (fun x ↦ F (-x)) (Icc (-b) (-a)) := by
    apply hF.comp continuous_neg.continuousOn
    intro x hx
    constructor <;> linarith [hx.1, hx.2]
  have hQ : IntervalIntegrable (fun x ↦ F x / (b - x)) volume a b :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le hab.le).2 hI
  have hQneg : IntegrableOn (fun x ↦ F (-x) / (x - (-b))) (Ioo (-b) (-a)) := by
    apply (intervalIntegrable_iff_integrableOn_Ioo_of_le hneg.le).1
    simpa only [zero_sub, sub_neg_eq_add, add_comm] using (hQ.comp_sub_left 0).symm
  simpa only [neg_neg] using eq_zero_of_integrableOn_div_left hneg hFneg hQneg

end RicciFlowSharpEstimate.Analysis
