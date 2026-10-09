/-
Copyright (c) 2026 Ziyang Qin. All rights reserved.
No license is granted by this file.
Authors: Ziyang Qin
-/
import RicciFlowSharpEstimate.Geometry.RotationalProfile
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Continuity of the constant-probe warp integral

A common positive box and uniform convergence of continuous profiles imply
convergence of the literal integral of `warp a / a`. Neither derivatives nor
balance are needed for this integral-continuity statement.
-/

noncomputable section

namespace RicciFlowSharpEstimate.Geometry.RotationalProfile

open Filter MeasureTheory Set intervalIntegral

/-- Continuity of the warping integral needs only continuity on the two-pole interval. -/
theorem continuousOn_warp {a : ℝ → ℝ}
    (ha : ContinuousOn a (Icc (-1 : ℝ) 1)) :
    ContinuousOn (warp a) (Icc (-1 : ℝ) 1) := by
  have hg : ContinuousOn (fun v : ℝ => v * a v) (Icc (-1 : ℝ) 1) :=
    continuousOn_id.mul ha
  have hInt : IntegrableOn (fun v : ℝ => v * a v) (uIcc (-1 : ℝ) 1) volume := by
    simpa only [uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 1)] using
      hg.integrableOn_Icc (μ := volume)
  change ContinuousOn (fun v => 2 * ∫ s in v..1, s * a s) (Icc (-1 : ℝ) 1)
  simpa only [uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 1)] using
    (continuousOn_primitive_interval_left hInt).const_mul 2

/-- The actual constant-probe integrand is integrable whenever the profile is
continuous and positive on the two-pole interval. -/
theorem intervalIntegrable_warp_div {a : ℝ → ℝ}
    (ha : ContinuousOn a (Icc (-1 : ℝ) 1))
    (hpos : ∀ v ∈ Icc (-1 : ℝ) 1, 0 < a v) :
    IntervalIntegrable (fun v => warp a v / a v) volume (-1) 1 := by
  exact ContinuousOn.intervalIntegrable_of_Icc (by norm_num)
    ((continuousOn_warp ha).div ha (fun v hv => (hpos v hv).ne'))

private theorem norm_weighted_profile_le {a : ℝ → ℝ} {lo hi : ℝ}
    (hlo : 0 < lo) (hbox : ∀ v ∈ Icc (-1 : ℝ) 1, lo ≤ a v ∧ a v ≤ hi)
    {v : ℝ} (hv : v ∈ Icc (-1 : ℝ) 1) : ‖v * a v‖ ≤ hi := by
  have hav := hbox v hv
  have hvabs : |v| ≤ 1 := abs_le.mpr hv
  rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (hlo.trans_le hav.1)]
  calc
    |v| * a v ≤ 1 * a v := mul_le_mul_of_nonneg_right hvabs (hlo.le.trans hav.1)
    _ ≤ hi := by simpa using hav.2

private theorem norm_warp_le {a : ℝ → ℝ} {lo hi : ℝ}
    (hlo : 0 < lo) (hbox : ∀ v ∈ Icc (-1 : ℝ) 1, lo ≤ a v ∧ a v ≤ hi)
    {v : ℝ} (hv : v ∈ Icc (-1 : ℝ) 1) : ‖warp a v‖ ≤ 4 * hi := by
  have hhi : 0 ≤ hi := (hlo.le.trans (hbox v hv).1).trans (hbox v hv).2
  have hInt : ‖∫ s in v..1, s * a s‖ ≤ hi * |1 - v| := by
    apply intervalIntegral.norm_integral_le_of_norm_le_const
    intro s hs
    rw [uIoc_of_le hv.2] at hs
    exact norm_weighted_profile_le hlo hbox ⟨hv.1.trans hs.1.le, hs.2⟩
  have hlen : |1 - v| ≤ 2 := by
    rw [abs_of_nonneg (sub_nonneg.mpr hv.2)]
    linarith [hv.1]
  calc
    ‖warp a v‖ = 2 * ‖∫ s in v..1, s * a s‖ := by simp [warp, norm_mul]
    _ ≤ 2 * (hi * |1 - v|) := mul_le_mul_of_nonneg_left hInt (by norm_num)
    _ ≤ 4 * hi := by nlinarith [mul_le_mul_of_nonneg_left hlen hhi]

/-- Under a common positive box, uniform profile convergence passes through the
literal constant-probe integral. All continuity assumptions are restricted to
the two-pole interval; the limiting lower bound is inherited from the profiles. -/
theorem tendsto_integral_warp_div_of_tendstoUniformlyOn
    {A : ℕ → ℝ → ℝ} {a : ℝ → ℝ} {lo hi : ℝ}
    (hlo : 0 < lo)
    (hA : ∀ n, ContinuousOn (A n) (Icc (-1 : ℝ) 1))
    (hbox : ∀ n v, v ∈ Icc (-1 : ℝ) 1 → lo ≤ A n v ∧ A n v ≤ hi)
    (hlim : TendstoUniformlyOn A a atTop (Icc (-1 : ℝ) 1)) :
    Tendsto (fun n => ∫ v in (-1 : ℝ)..1, warp (A n) v / A n v)
      atTop (nhds (∫ v in (-1 : ℝ)..1, warp a v / a v)) := by
  have halower (v : ℝ) (hv : v ∈ Icc (-1 : ℝ) 1) : lo ≤ a v :=
    ge_of_tendsto (hlim.tendsto_at hv) (Eventually.of_forall (fun n => (hbox n v hv).1))
  have hwarp (v : ℝ) (hv : v ∈ Icc (-1 : ℝ) 1) :
      Tendsto (fun n => warp (A n) v) atTop (nhds (warp a v)) := by
    unfold warp
    apply Tendsto.const_mul
    apply intervalIntegral.tendsto_integral_filter_of_dominated_convergence (fun _ => hi)
    · apply Eventually.of_forall
      intro n
      apply ContinuousOn.aestronglyMeasurable _ measurableSet_uIoc
      apply (continuousOn_id.mul (hA n)).mono
      intro s hs
      rw [uIoc_of_le hv.2] at hs
      exact ⟨hv.1.trans hs.1.le, hs.2⟩
    · apply Eventually.of_forall
      intro n
      apply ae_of_all
      intro s hs
      rw [uIoc_of_le hv.2] at hs
      exact norm_weighted_profile_le hlo (hbox n) ⟨hv.1.trans hs.1.le, hs.2⟩
    · exact intervalIntegrable_const
    · apply ae_of_all
      intro s hs
      rw [uIoc_of_le hv.2] at hs
      exact (hlim.tendsto_at ⟨hv.1.trans hs.1.le, hs.2⟩).const_mul s
  apply intervalIntegral.tendsto_integral_filter_of_dominated_convergence
    (fun _ => 4 * hi / lo)
  · apply Eventually.of_forall
    intro n
    rw [uIoc_of_le (by norm_num : (-1 : ℝ) ≤ 1)]
    exact (intervalIntegrable_warp_div (hA n)
      (fun v hv => hlo.trans_le (hbox n v hv).1)).aestronglyMeasurable
  · apply Eventually.of_forall
    intro n
    apply ae_of_all
    intro v hv
    rw [uIoc_of_le (by norm_num : (-1 : ℝ) ≤ 1)] at hv
    have hv' : v ∈ Icc (-1 : ℝ) 1 := ⟨hv.1.le, hv.2⟩
    rw [norm_div, Real.norm_eq_abs (A n v), abs_of_pos (hlo.trans_le (hbox n v hv').1)]
    calc
      ‖warp (A n) v‖ / A n v ≤ ‖warp (A n) v‖ / lo :=
        div_le_div_of_nonneg_left (norm_nonneg _) hlo (hbox n v hv').1
      _ ≤ 4 * hi / lo := div_le_div_of_nonneg_right (norm_warp_le hlo (hbox n) hv') hlo.le
  · exact intervalIntegrable_const
  · apply ae_of_all
    intro v hv
    rw [uIoc_of_le (by norm_num : (-1 : ℝ) ≤ 1)] at hv
    have hv' : v ∈ Icc (-1 : ℝ) 1 := ⟨hv.1.le, hv.2⟩
    exact (hwarp v hv').div (hlim.tendsto_at hv') (hlo.trans_le (halower v hv')).ne'

private theorem norm_warp_sub_le {a b : ℝ → ℝ} {ε : ℝ}
    (ha : ContinuousOn a (Icc (-1 : ℝ) 1))
    (hb : ContinuousOn b (Icc (-1 : ℝ) 1))
    (hclose : ∀ v ∈ Icc (-1 : ℝ) 1, |a v - b v| ≤ ε)
    {v : ℝ} (hv : v ∈ Icc (-1 : ℝ) 1) :
    ‖warp a v - warp b v‖ ≤ 4 * ε := by
  have hε : 0 ≤ ε := (abs_nonneg _).trans (hclose v hv)
  have hsub : Icc v 1 ⊆ Icc (-1 : ℝ) 1 := fun s hs => ⟨hv.1.trans hs.1, hs.2⟩
  have haint : IntervalIntegrable (fun s : ℝ => s * a s) volume v 1 :=
    ContinuousOn.intervalIntegrable_of_Icc hv.2 ((continuousOn_id.mul ha).mono hsub)
  have hbint : IntervalIntegrable (fun s : ℝ => s * b s) volume v 1 :=
    ContinuousOn.intervalIntegrable_of_Icc hv.2 ((continuousOn_id.mul hb).mono hsub)
  have hint : ‖∫ s in v..1, (s * a s - s * b s)‖ ≤ ε * |1 - v| := by
    apply intervalIntegral.norm_integral_le_of_norm_le_const
    intro s hs
    rw [uIoc_of_le hv.2] at hs
    have hs' : s ∈ Icc (-1 : ℝ) 1 := ⟨hv.1.trans hs.1.le, hs.2⟩
    rw [← mul_sub, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
    calc
      |s| * |a s - b s| ≤ 1 * ε :=
        mul_le_mul (abs_le.mpr hs') (hclose s hs') (abs_nonneg _) (by norm_num)
      _ = ε := one_mul _
  have hlen : |1 - v| ≤ 2 := by
    rw [abs_of_nonneg (sub_nonneg.mpr hv.2)]
    linarith [hv.1]
  rw [warp, warp, ← mul_sub, ← intervalIntegral.integral_sub haint hbint, norm_mul]
  norm_num only [Real.norm_ofNat]
  nlinarith [mul_le_mul_of_nonneg_left hlen hε]

/-- The literal constant-probe integral is uniformly Lipschitz on a common
positive profile box. The coefficient depends only on the two box endpoints. -/
theorem abs_integral_warp_div_sub_le
    {a b : ℝ → ℝ} {lo hi ε : ℝ}
    (hlo : 0 < lo)
    (ha : ContinuousOn a (Icc (-1 : ℝ) 1))
    (hb : ContinuousOn b (Icc (-1 : ℝ) 1))
    (habox : ∀ v ∈ Icc (-1 : ℝ) 1, lo ≤ a v ∧ a v ≤ hi)
    (hbbox : ∀ v ∈ Icc (-1 : ℝ) 1, lo ≤ b v ∧ b v ≤ hi)
    (hclose : ∀ v ∈ Icc (-1 : ℝ) 1, |a v - b v| ≤ ε) :
    |(∫ v in (-1 : ℝ)..1, warp a v / a v) -
      (∫ v in (-1 : ℝ)..1, warp b v / b v)| ≤
      8 * (1 / lo + hi / lo ^ 2) * ε := by
  have hhi : 0 ≤ hi := (hlo.le.trans (habox 0 ⟨by norm_num, by norm_num⟩).1).trans
    (habox 0 ⟨by norm_num, by norm_num⟩).2
  have hpoint (v : ℝ) (hv : v ∈ Icc (-1 : ℝ) 1) :
      ‖warp a v / a v - warp b v / b v‖ ≤ 4 * ε / lo + 4 * hi * ε / lo ^ 2 := by
    have hav : 0 < a v := hlo.trans_le (habox v hv).1
    have hbv : 0 < b v := hlo.trans_le (hbbox v hv).1
    have hden : lo ^ 2 ≤ a v * b v := by
      simpa only [pow_two] using
        mul_le_mul (habox v hv).1 (hbbox v hv).1 hlo.le hav.le
    have hfirst : ‖(warp a v - warp b v) / a v‖ ≤ 4 * ε / lo := by
      rw [norm_div, Real.norm_eq_abs (a v), abs_of_pos hav]
      exact (div_le_div_of_nonneg_left (norm_nonneg _) hlo (habox v hv).1).trans
        (div_le_div_of_nonneg_right (norm_warp_sub_le ha hb hclose hv) hlo.le)
    have hsecond : ‖warp b v * (b v - a v) / (a v * b v)‖ ≤ 4 * hi * ε / lo ^ 2 := by
      rw [norm_div, Real.norm_eq_abs (a v * b v), abs_of_pos (mul_pos hav hbv)]
      have hnum : ‖warp b v * (b v - a v)‖ ≤ 4 * hi * ε := by
        rw [norm_mul, Real.norm_eq_abs (b v - a v), abs_sub_comm]
        exact mul_le_mul (norm_warp_le hlo hbbox hv) (hclose v hv)
          (abs_nonneg _) (by positivity)
      exact (div_le_div_of_nonneg_left (norm_nonneg _) (sq_pos_of_pos hlo) hden).trans
        (div_le_div_of_nonneg_right hnum (sq_nonneg lo))
    have hsplit : warp a v / a v - warp b v / b v =
        (warp a v - warp b v) / a v + warp b v * (b v - a v) / (a v * b v) := by
      field_simp
      ring
    rw [hsplit]
    exact (norm_add_le _ _).trans (add_le_add hfirst hsecond)
  have haint := intervalIntegrable_warp_div ha (fun v hv => hlo.trans_le (habox v hv).1)
  have hbint := intervalIntegrable_warp_div hb (fun v hv => hlo.trans_le (hbbox v hv).1)
  rw [← intervalIntegral.integral_sub haint hbint, ← Real.norm_eq_abs]
  calc
    ‖∫ v in (-1 : ℝ)..1, (warp a v / a v - warp b v / b v)‖ ≤
        (4 * ε / lo + 4 * hi * ε / lo ^ 2) * |1 - (-1 : ℝ)| := by
      apply intervalIntegral.norm_integral_le_of_norm_le_const
      intro v hv
      rw [uIoc_of_le (by norm_num : (-1 : ℝ) ≤ 1)] at hv
      exact hpoint v ⟨hv.1.le, hv.2⟩
    _ = 8 * (1 / lo + hi / lo ^ 2) * ε := by
      rw [show |(1 : ℝ) - -1| = 2 by norm_num]
      ring

end RicciFlowSharpEstimate.Geometry.RotationalProfile
