/-
Copyright (c) 2026 Ziyang Qin. All rights reserved.
No license is granted by this file.
Authors: Ziyang Qin
-/
import RicciFlowSharpEstimate.Variational.EvenReciprocalProfile
import RicciFlowSharpEstimate.Variational.ReciprocalProfile
import RicciFlowSharpEstimate.Geometry.RotationalProfile

/-!
# Constant-probe integrals for continuous reciprocal profiles

The hemisphere identity extends to continuous balanced profiles, so it applies
to the nonsmooth reciprocal optimizer without assigning it a smooth metric.
-/

noncomputable section

namespace RicciFlowSharpEstimate.Geometry.RotationalProfile

open Set MeasureTheory intervalIntegral Variational

/-- Even profiles satisfy the exact two-pole balance equation. -/
theorem balance_eq_zero_of_even (a : ℝ → ℝ) (he : Function.Even a) :
    balance a = 0 := by
  have h := intervalIntegral.integral_comp_neg (fun v => v * a v) (a := -1) (b := 1)
  have heq (v : ℝ) : a (-v) = a v := he v
  simp only [neg_neg, heq, neg_mul, intervalIntegral.integral_neg] at h
  change -balance a = balance a at h
  linarith

/-- Reflection of a continuous balanced profile reflects its actual warping integral. -/
theorem warp_reflected_of_balance (a : ℝ → ℝ) (ha : Continuous a)
    (hb : balance a = 0) (v : ℝ) :
    warp (fun s => a (-s)) v = warp a (-v) := by
  have hchange : (∫ s in v..1, s * a (-s)) =
      -(∫ s in (-1 : ℝ)..(-v), s * a s) := by
    have hn := intervalIntegral.integral_comp_neg (fun s => s * a s) (a := v) (b := 1)
    simp only [neg_mul, intervalIntegral.integral_neg] at hn
    linarith
  rw [warp, warp, hchange, integral_from_eq_neg_integral_to_of_balance a ha hb]

/-- Both pair functionals reconstruct the literal warp-ratio integral for a
continuous balanced profile, without assuming a smooth metric at that profile. -/
theorem integral_warp_div_eq_pairFunctional_sum (a : ℝ → ℝ) (ha : Continuous a)
    (hpos : ∀ v ∈ Icc (-1 : ℝ) 1, 0 < a v) (hb : balance a = 0)
    (M : ℝ) (hM : 0 < M) :
    (∫ v in (-1 : ℝ)..1, warp a v / a v) =
      pairFunctional (fun v => Real.log (M / a v)) +
        pairFunctional (fun v => Real.log (M / a (-v))) := by
  have hnorth (v : ℝ) (hv : v ∈ Icc (0 : ℝ) 1) : v ∈ Icc (-1 : ℝ) 1 :=
    ⟨by linarith [hv.1], hv.2⟩
  have hsouth (v : ℝ) (hv : v ∈ Icc (0 : ℝ) 1) : -v ∈ Icc (-1 : ℝ) 1 := by
    constructor <;> linarith [hv.1, hv.2]
  have hw : Continuous (warp a) :=
    continuous_iff_continuousAt.mpr (fun v => (warp_hasDerivAt a ha v).continuousAt)
  have hq : ContinuousOn (fun v => warp a v / a v) (Icc (-1 : ℝ) 1) :=
    hw.continuousOn.div ha.continuousOn (fun v hv => (hpos v hv).ne')
  have hl : IntervalIntegrable (fun v => warp a v / a v) volume (-1) 0 :=
    (hq.mono (fun _ hv => ⟨hv.1, hv.2.trans zero_le_one⟩)).intervalIntegrable_of_Icc
      (by norm_num)
  have hr : IntervalIntegrable (fun v => warp a v / a v) volume 0 1 :=
    (hq.mono (fun v hv => hnorth v hv)).intervalIntegrable_of_Icc zero_le_one
  have hp : pairFunctional (fun v => Real.log (M / a v)) =
      ∫ v in 0..1, warp a v / a v :=
    pairFunctional_log_reciprocal a M hM ha.continuousOn
      (fun v hv => hpos v (hnorth v hv))
  have hm : pairFunctional (fun v => Real.log (M / a (-v))) =
      ∫ v in 0..1, warp a (-v) / a (-v) := by
    rw [pairFunctional_log_reciprocal (fun v => a (-v)) M hM
      (ha.comp continuous_neg).continuousOn (fun v hv => hpos (-v) (hsouth v hv))]
    apply intervalIntegral.integral_congr
    intro v _
    change warp (fun s => a (-s)) v / a (-v) = warp a (-v) / a (-v)
    rw [warp_reflected_of_balance a ha hb]
  have href : (∫ v in (0 : ℝ)..1, warp a (-v) / a (-v)) =
      ∫ v in (-1 : ℝ)..0, warp a v / a v := by
    simpa only [neg_zero] using
      (intervalIntegral.integral_comp_neg (fun v => warp a v / a v) (a := 0) (b := 1))
  rw [hp, hm, href, add_comm]
  exact (intervalIntegral.integral_add_adjacent_intervals hl hr).symm

/-- The continuous reciprocal optimizer has exactly twice the optimal pair integral. -/
theorem integral_warp_div_evenReciprocalProfile (C : ℝ) (hC : 1 ≤ C) :
    (∫ v in (-1 : ℝ)..1,
      warp (evenReciprocalProfile C) v / evenReciprocalProfile C v) =
        2 * pairFunctional (obstacleLogProfile C) := by
  have hpos (v : ℝ) (_hv : v ∈ Icc (-1 : ℝ) 1) :
      0 < evenReciprocalProfile C v :=
    (one_div_pos.mpr (zero_lt_one.trans_le hC)).trans_le
      (evenReciprocalProfile_bounds C hC v).1
  rw [integral_warp_div_eq_pairFunctional_sum (evenReciprocalProfile C)
    (uniformContinuous_evenReciprocalProfile C).continuous hpos
    (balance_eq_zero_of_even _ (even_evenReciprocalProfile C)) 1 zero_lt_one]
  have hlog : pairFunctional (fun v => Real.log (1 / evenReciprocalProfile C v)) =
      pairFunctional (obstacleLogProfile C) := by
    apply pairFunctional_congr
    intro v hv
    rw [evenReciprocalProfile_eq C v ⟨by linarith [hv.1], hv.2⟩]
    simp only [abs_of_nonneg hv.1, one_div, ← Real.exp_neg, neg_neg, Real.log_exp]
  have heq : (fun v => Real.log (1 / evenReciprocalProfile C (-v))) =
      (fun v => Real.log (1 / evenReciprocalProfile C v)) := by
    funext v
    rw [even_evenReciprocalProfile C v]
  rw [heq, hlog]
  ring

/-- The exact scalar integral approached by genuine unit meridional actions. -/
theorem constantProbeIntegral_evenReciprocalProfile (C : ℝ) (hC : 1 ≤ C) :
    2 * Real.pi * (2 * (∫ v in (-1 : ℝ)..1,
      warp (evenReciprocalProfile C) v / evenReciprocalProfile C v) - 4 / 3) =
        8 * Real.pi * (pairFunctional (obstacleLogProfile C) - 1 / 3) := by
  rw [integral_warp_div_evenReciprocalProfile C hC]
  ring

end RicciFlowSharpEstimate.Geometry.RotationalProfile
