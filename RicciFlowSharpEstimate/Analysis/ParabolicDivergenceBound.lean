/-
Copyright (c) 2026 Ziyang Qin. All rights reserved.
No license is granted by this file.
Authors: Ziyang Qin
-/
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Boundedness from a parabolic divergence flux

An absolutely continuous zero-trace flux `F = f² p` has a bounded coefficient
`p` when its derivative is `f S`, the source is bounded, and `f` is comparable
to the parabolic weight. The proof uses the actual flux derivative and its
two endpoint primitives, without source measurability hypotheses.
-/

noncomputable section

namespace RicciFlowSharpEstimate.Analysis

open Filter MeasureTheory Set

local notation "areaμ" => volume.restrict (Ioo (0 : ℝ) 1)

private theorem bound_of_flux_estimate {z v p d lo C : ℝ}
    (hlo : 0 < lo) (hd : 0 < d) (hlower : lo * d ≤ 2 * v)
    (hflux : z = v ^ 2 * p) (hbound : |z| ≤ C * d ^ 2 / 2) :
    |p| ≤ 2 * C / lo ^ 2 := by
  have hsq : lo ^ 2 * d ^ 2 ≤ 4 * v ^ 2 := by
    have hs := mul_self_le_mul_self (mul_nonneg hlo.le hd.le) hlower
    nlinarith only [hs]
  have habs : |z| = v ^ 2 * |p| := by
    rw [hflux, abs_mul, abs_of_nonneg (sq_nonneg v)]
  rw [habs] at hbound
  have hmul : (|p| * lo ^ 2) * d ^ 2 ≤ (2 * C) * d ^ 2 := by
    nlinarith only [hbound, mul_le_mul_of_nonneg_left hsq (abs_nonneg p)]
  exact (le_div_iff₀ (sq_pos_of_pos hlo)).mpr
    ((mul_le_mul_iff_right₀ (sq_pos_of_pos hd)).mp (by simpa only [mul_comm] using hmul))

/-- A bounded source in a zero-trace parabolic divergence flux gives a
pointwise bound on its coefficient throughout the open unit interval. The
derivative and source bound are only required almost everywhere. -/
theorem bounded_of_parabolic_divergence_flux
    {f F p S : ℝ → ℝ} {lo hi M : ℝ} (hlo : 0 < lo)
    (hbounds : ∀ x ∈ Ioo (0 : ℝ) 1,
      lo * (x * (1 - x)) ≤ f x ∧ f x ≤ hi * (x * (1 - x)))
    (hF : AbsolutelyContinuousOnInterval F 0 1) (h0 : F 0 = 0) (h1 : F 1 = 0)
    (hFp : ∀ x ∈ Ioo (0 : ℝ) 1, F x = f x ^ 2 * p x)
    (hD : ∀ᵐ x ∂areaμ, HasDerivAt F (f x * S x) x)
    (hS : ∀ᵐ x ∂areaμ, |S x| ≤ M) :
    ∀ x ∈ Ioo (0 : ℝ) 1, |p x| ≤ 2 * |hi| * |M| / lo ^ 2 := by
  let C : ℝ := |hi| * |M|
  have hfpos (x : ℝ) (hx : x ∈ Ioo (0 : ℝ) 1) : 0 < f x :=
    (mul_pos hlo (mul_pos hx.1 (sub_pos.mpr hx.2))).trans_le (hbounds x hx).1
  have hfL (x : ℝ) (hx : x ∈ Ioo (0 : ℝ) 1) : f x ≤ |hi| * x := by
    have hw : 0 ≤ x * (1 - x) := mul_nonneg hx.1.le (sub_nonneg.mpr hx.2.le)
    exact (hbounds x hx).2.trans
      ((mul_le_mul_of_nonneg_right (le_abs_self hi) hw).trans
        (mul_le_mul_of_nonneg_left (by nlinarith [sq_nonneg x]) (abs_nonneg hi)))
  have hfR (x : ℝ) (hx : x ∈ Ioo (0 : ℝ) 1) : f x ≤ |hi| * (1 - x) := by
    have hw : 0 ≤ x * (1 - x) := mul_nonneg hx.1.le (sub_nonneg.mpr hx.2.le)
    exact (hbounds x hx).2.trans
      ((mul_le_mul_of_nonneg_right (le_abs_self hi) hw).trans
        (mul_le_mul_of_nonneg_left (by nlinarith [sq_nonneg (1 - x)]) (abs_nonneg hi)))
  have hderiv : ∀ᵐ t ∂volume, t ∈ Ioo (0 : ℝ) 1 →
      |deriv F t| ≤ C * t ∧ |deriv F t| ≤ C * (1 - t) := by
    filter_upwards [ae_imp_of_ae_restrict hD, ae_imp_of_ae_restrict hS] with t htD htS ht
    have hM : |S t| ≤ |M| := (htS ht).trans (le_abs_self M)
    simp only [(htD ht).deriv, abs_mul, abs_of_pos (hfpos t ht)]
    constructor
    · calc
        f t * |S t| ≤ (|hi| * t) * |M| :=
          mul_le_mul (hfL t ht) hM (abs_nonneg _) (mul_nonneg (abs_nonneg _) ht.1.le)
        _ = C * t := by dsimp only [C]; ring
    · calc
        f t * |S t| ≤ (|hi| * (1 - t)) * |M| :=
          mul_le_mul (hfR t ht) hM (abs_nonneg _)
            (mul_nonneg (abs_nonneg _) (sub_nonneg.mpr ht.2.le))
        _ = C * (1 - t) := by dsimp only [C]; ring
  have hleft (x : ℝ) (hx : x ∈ Ioo (0 : ℝ) 1) : |F x| ≤ C * x ^ 2 / 2 := by
    have hsub : uIcc (0 : ℝ) x ⊆ uIcc (0 : ℝ) 1 := by
      rw [uIcc_of_le hx.1.le, uIcc_of_le zero_le_one]
      exact Icc_subset_Icc le_rfl hx.2.le
    have hFTC : (∫ t in 0..x, deriv F t) = F x := by
      simpa only [h0, sub_zero] using (hF.mono hsub).integral_deriv_eq_sub
    have hdom : ∀ᵐ t ∂volume, t ∈ Ioc (0 : ℝ) x → ‖deriv F t‖ ≤ C * t := by
      filter_upwards [hderiv] with t ht htI
      simpa only [Real.norm_eq_abs] using (ht ⟨htI.1, htI.2.trans_lt hx.2⟩).1
    calc
      |F x| = ‖∫ t in 0..x, deriv F t‖ := by rw [hFTC, Real.norm_eq_abs]
      _ ≤ ∫ t in 0..x, C * t :=
        intervalIntegral.norm_integral_le_of_norm_le hx.1.le hdom
          ((continuous_const.mul continuous_id).intervalIntegrable 0 x)
      _ = C * x ^ 2 / 2 := by
        rw [intervalIntegral.integral_const_mul, integral_id]
        ring
  have hright (x : ℝ) (hx : x ∈ Ioo (0 : ℝ) 1) :
      |F x| ≤ C * (1 - x) ^ 2 / 2 := by
    have hsub : uIcc x (1 : ℝ) ⊆ uIcc (0 : ℝ) 1 := by
      rw [uIcc_of_le hx.2.le, uIcc_of_le zero_le_one]
      exact Icc_subset_Icc hx.1.le le_rfl
    have hFTC : (∫ t in x..1, deriv F t) = -F x := by
      simpa only [h1, zero_sub] using (hF.mono hsub).integral_deriv_eq_sub
    have hdom : ∀ᵐ t ∂volume, t ∈ Ioc x (1 : ℝ) → ‖deriv F t‖ ≤ C * (1 - t) := by
      filter_upwards [hderiv, volume.ae_ne (1 : ℝ)] with t ht ht1 htI
      simpa only [Real.norm_eq_abs] using
        (ht ⟨hx.1.trans htI.1, lt_of_le_of_ne htI.2 ht1⟩).2
    calc
      |F x| = ‖∫ t in x..1, deriv F t‖ := by rw [hFTC, norm_neg, Real.norm_eq_abs]
      _ ≤ ∫ t in x..1, C * (1 - t) :=
        intervalIntegral.norm_integral_le_of_norm_le hx.2.le hdom
          ((continuous_const.mul (continuous_const.sub continuous_id)).intervalIntegrable x 1)
      _ = C * (1 - x) ^ 2 / 2 := by
        have hOne : IntervalIntegrable (fun _ : ℝ => (1 : ℝ)) volume x 1 :=
          continuous_const.intervalIntegrable x 1
        rw [intervalIntegral.integral_const_mul,
          intervalIntegral.integral_sub (f := fun _ : ℝ => (1 : ℝ))
            (g := fun t : ℝ => t) hOne (continuous_id.intervalIntegrable x 1),
          intervalIntegral.integral_const, integral_id]
        simp only [smul_eq_mul]
        ring
  intro x hx
  rcases le_total x (1 / 2 : ℝ) with hhalf | hhalf
  · have hlin : lo * x ≤ 2 * f x := by
      have hm := mul_le_mul_of_nonneg_left (show (1 / 2 : ℝ) ≤ 1 - x by linarith)
        (mul_nonneg hlo.le hx.1.le)
      nlinarith [(hbounds x hx).1]
    simpa only [C, mul_assoc] using
      bound_of_flux_estimate hlo hx.1 hlin (hFp x hx) (hleft x hx)
  · have hlin : lo * (1 - x) ≤ 2 * f x := by
      have hm := mul_le_mul_of_nonneg_left hhalf
        (mul_nonneg hlo.le (sub_nonneg.mpr hx.2.le))
      nlinarith [(hbounds x hx).1]
    simpa only [C, mul_assoc] using
      bound_of_flux_estimate hlo (sub_pos.mpr hx.2) hlin (hFp x hx) (hright x hx)

end RicciFlowSharpEstimate.Analysis
