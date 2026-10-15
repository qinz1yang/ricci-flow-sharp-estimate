/-
Copyright (c) 2026 Ziyang Qin. All rights reserved.
No license is granted by this file.
Authors: Ziyang Qin
-/
import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Function.L2Space

/-! # Integrable endpoint quotients of a zero-trace H1 function -/

noncomputable section
namespace RicciFlowSharpEstimate.Analysis
open Set MeasureTheory Filter

private theorem integral_abs_le_sqrt_length
    {D : ℝ → ℝ} {a b u v : ℝ} (hab : a ≤ b)
    (hD : MemLp D 2 (volume.restrict (Ioo a b)))
    (hau : a ≤ u) (huv : u ≤ v) (hvb : v ≤ b) :
    |∫ t in u..v, D t| ≤ Real.sqrt (v - u) * Real.sqrt (∫ t in a..b, D t ^ 2) := by
  have hsub : Ioo u v ⊆ Ioo a b :=
    fun t ht => ⟨hau.trans_lt ht.1, ht.2.trans_le hvb⟩
  have hDu : MemLp D 2 (volume.restrict (Ioo u v)) :=
    hD.mono_measure (Measure.restrict_mono hsub le_rfl)
  have h1 : MemLp (fun _ : ℝ => (1 : ℝ)) 2 (volume.restrict (Ioo u v)) := memLp_const 1
  have hh := integral_mul_norm_le_Lp_mul_Lq Real.HolderConjugate.two_two
    (by simpa using hDu) (by simpa using h1)
  have hh' : (∫ t in Ioo u v, |D t|) ≤
      Real.sqrt (∫ t in Ioo u v, D t ^ 2) * Real.sqrt (v - u) := by
    simpa only [Real.norm_eq_abs, Real.rpow_two, sq_abs, norm_one, mul_one,
      Real.one_rpow, one_pow, integral_const, Measure.real, Measure.restrict_apply_univ,
      Real.volume_Ioo, ENNReal.toReal_ofReal (sub_nonneg.mpr huv), smul_eq_mul,
      mul_one, ← Real.sqrt_eq_rpow] using hh
  have hDb : IntervalIntegrable (fun t => D t ^ 2) volume a b :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le hab).mpr hD.integrable_sq
  have hmono : (∫ t in Ioo u v, D t ^ 2) ≤ ∫ t in a..b, D t ^ 2 := by
    rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le huv]
    exact intervalIntegral.integral_mono_interval hau huv hvb
      (Eventually.of_forall fun t => sq_nonneg _) hDb
  calc
    _ = |∫ t in Ioo u v, D t| := by
      rw [intervalIntegral.integral_of_le huv, integral_Ioc_eq_integral_Ioo]
    _ ≤ ∫ t in Ioo u v, |D t| := MeasureTheory.abs_integral_le_integral_abs
    _ ≤ Real.sqrt (∫ t in Ioo u v, D t ^ 2) * Real.sqrt (v - u) := hh'
    _ ≤ Real.sqrt (∫ t in a..b, D t ^ 2) * Real.sqrt (v - u) :=
      mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt hmono) (Real.sqrt_nonneg _)
    _ = _ := mul_comm _ _

/-- A zero-trace absolutely continuous function whose genuine derivative is
in L2 has integrable quotients by both endpoint distances. No trace rate or
separate pointwise derivative bound is assumed. Reversed intervals are empty. -/
theorem AbsolutelyContinuousOnInterval.integrable_div_endpoints_of_deriv_memLp_two
    {F : ℝ → ℝ} {a b : ℝ}
    (hF : AbsolutelyContinuousOnInterval F a b)
    (ha : F a = 0) (hb : F b = 0)
    (hD : MemLp (deriv F) 2 (volume.restrict (Ioo a b))) :
    IntegrableOn (fun x => F x / (x - a)) (Ioo a b) volume ∧
      IntegrableOn (fun x => F x / (b - x)) (Ioo a b) volume := by
  by_cases hab : a < b
  swap
  · have hempty : Ioo a b = ∅ := Ioo_eq_empty hab
    simp only [hempty, integrableOn_empty, and_self]
  let E := ∫ t in a..b, deriv F t ^ 2
  have hpow : IntervalIntegrable (fun x : ℝ => x ^ (-1 / 2 : ℝ)) volume 0 (b - a) :=
    intervalIntegral.intervalIntegrable_rpow' (by norm_num)
  have hleftI : IntegrableOn (fun x : ℝ => (x - a) ^ (-1 / 2 : ℝ)) (Ioo a b) volume := by
    have hi := hpow.comp_sub_right a
    have hi' : IntervalIntegrable (fun x : ℝ => (x - a) ^ (-1 / 2 : ℝ)) volume a b := by
      simpa only [zero_add, sub_add_cancel] using hi
    exact (intervalIntegrable_iff_integrableOn_Ioo_of_le hab.le).mp hi'
  have hrightI : IntegrableOn (fun x : ℝ => (b - x) ^ (-1 / 2 : ℝ)) (Ioo a b) volume := by
    have hi := (hpow.comp_sub_left b).symm
    have hi' : IntervalIntegrable (fun x : ℝ => (b - x) ^ (-1 / 2 : ℝ)) volume a b := by
      simpa only [sub_zero, sub_sub_cancel] using hi
    exact (intervalIntegrable_iff_integrableOn_Ioo_of_le hab.le).mp hi'
  have hC : ContinuousOn F (Ioo a b) := by
    apply hF.continuousOn.mono
    simpa only [uIcc_of_le hab.le] using (Ioo_subset_Icc_self : Ioo a b ⊆ Icc a b)
  have hbound (x : ℝ) (hx : x ∈ Ioo a b) :
      |F x| ≤ Real.sqrt (x - a) * Real.sqrt E ∧
      |F x| ≤ Real.sqrt (b - x) * Real.sqrt E := by
    have hA := (hF.mono (uIcc_subset_uIcc left_mem_uIcc (by
      simpa only [uIcc_of_le hab.le] using Ioo_subset_Icc_self hx))).integral_deriv_eq_sub
    have hB := (hF.mono (uIcc_subset_uIcc (by
      simpa only [uIcc_of_le hab.le] using Ioo_subset_Icc_self hx)
        right_mem_uIcc)).integral_deriv_eq_sub
    have hL := integral_abs_le_sqrt_length hab.le hD le_rfl hx.1.le hx.2.le
    have hR := integral_abs_le_sqrt_length hab.le hD hx.1.le hx.2.le le_rfl
    rw [hA, ha, sub_zero] at hL
    rw [hB, hb, zero_sub, abs_neg] at hR
    exact ⟨hL, hR⟩
  have hsqrt (x : ℝ) (hx : 0 < x) : Real.sqrt x / x = x ^ (-1 / 2 : ℝ) := by
    calc
      _ = x ^ (1 / 2 : ℝ) / x ^ (1 : ℝ) := by rw [Real.sqrt_eq_rpow, Real.rpow_one]
      _ = x ^ ((1 / 2 : ℝ) - 1) := (Real.rpow_sub hx _ _).symm
      _ = _ := by norm_num
  constructor
  · apply (hleftI.const_mul (Real.sqrt E)).mono'
      ((hC.div (continuousOn_id.sub continuousOn_const)
        (fun x hx => (sub_pos.mpr hx.1).ne')).aestronglyMeasurable measurableSet_Ioo)
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
    change ‖F x / (x - a)‖ ≤ Real.sqrt E * (x - a) ^ (-1 / 2 : ℝ)
    rw [Real.norm_eq_abs, abs_div, abs_of_pos (sub_pos.mpr hx.1)]
    calc
      _ ≤ (Real.sqrt (x - a) * Real.sqrt E) / (x - a) :=
        div_le_div_of_nonneg_right (hbound x hx).1 (sub_nonneg.mpr hx.1.le)
      _ = _ := by rw [mul_div_right_comm, hsqrt _ (sub_pos.mpr hx.1), mul_comm]
  · apply (hrightI.const_mul (Real.sqrt E)).mono'
      ((hC.div (continuousOn_const.sub continuousOn_id)
        (fun x hx => (sub_pos.mpr hx.2).ne')).aestronglyMeasurable measurableSet_Ioo)
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
    change ‖F x / (b - x)‖ ≤ Real.sqrt E * (b - x) ^ (-1 / 2 : ℝ)
    rw [Real.norm_eq_abs, abs_div, abs_of_pos (sub_pos.mpr hx.2)]
    calc
      _ ≤ (Real.sqrt (b - x) * Real.sqrt E) / (b - x) :=
        div_le_div_of_nonneg_right (hbound x hx).2 (sub_nonneg.mpr hx.2.le)
      _ = _ := by rw [mul_div_right_comm, hsqrt _ (sub_pos.mpr hx.2), mul_comm]

end RicciFlowSharpEstimate.Analysis
