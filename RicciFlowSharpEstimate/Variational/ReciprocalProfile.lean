/-
Copyright (c) 2026 Ziyang Qin. All rights reserved.
No license is granted by this file.
Authors: Ziyang Qin
-/
import RicciFlowSharpEstimate.Variational.PairIteration
import RicciFlowSharpEstimate.Analysis.ReciprocalLogarithm

/-!
# Reciprocal logarithmic profiles

The actual triangular pair integral has a forward-tail formula. Substitution
of `log (M / a)` cancels the normalization and recovers the reciprocal-profile
tail integral. Positivity and regularity are required only on the physical
interval; no globally positive extension is used.
-/

open MeasureTheory Set RicciFlowSharpEstimate.Analysis

namespace RicciFlowSharpEstimate.Variational

private theorem integrable_pairWeight_of_continuousOn {k : ℝ → ℝ}
    (hk : ContinuousOn k (Icc 0 1)) : Integrable (pairWeight k) := by
  have hdiff : ContinuousOn (fun p : ℝ × ℝ => k p.1 - k p.2)
      (Icc ((0 : ℝ), (0 : ℝ)) (1, 1)) :=
    (hk.comp continuous_fst.continuousOn (fun _ hp => ⟨hp.1.1, hp.2.1⟩)).sub
      (hk.comp continuous_snd.continuousOn (fun _ hp => ⟨hp.1.2, hp.2.2⟩))
  have hcont : ContinuousOn (fun p : ℝ × ℝ => 2 * p.2 * Real.exp (k p.1 - k p.2))
      (Icc ((0 : ℝ), (0 : ℝ)) (1, 1)) :=
    (continuous_const.mul continuous_snd).continuousOn.mul
      (Real.continuous_exp.comp_continuousOn hdiff)
  have hint : IntegrableOn (fun p : ℝ × ℝ => 2 * p.2 * Real.exp (k p.1 - k p.2))
      orderedTriangle := (hcont.integrableOn_compact isCompact_Icc).mono_set (by
    intro p hp
    exact ⟨⟨hp.1, hp.1.trans hp.2.1.le⟩, ⟨hp.2.1.le.trans hp.2.2, hp.2.2⟩⟩)
  exact hint.integrable_indicator measurableSet_orderedTriangle

/-- Fubini expresses the actual pair functional using its forward tails. -/
theorem pairFunctional_eq_forward_intervalIntegral (k : ℝ → ℝ)
    (hk : ContinuousOn k (Icc 0 1)) :
    pairFunctional k =
      ∫ v in 0..1, Real.exp (k v) * (∫ s in v..1, 2 * s / Real.exp (k s)) := by
  have hweight := integrable_pairWeight_of_continuousOn hk
  have hprod : Integrable (pairWeight k) (volume.prod volume) := by
    simpa only [Measure.volume_eq_prod] using hweight
  have hforward : (fun v => ∫ s, pairWeight k (v, s)) =
      (Icc 0 1).indicator
        (fun v => Real.exp (k v) * (∫ s in v..1, 2 * s / Real.exp (k s))) := by
    funext v
    by_cases hv : v ∈ Icc (0 : ℝ) 1
    · rw [indicator_of_mem hv]
      have hslice : (fun s => pairWeight k (v, s)) =
          (Ioc v 1).indicator (fun s => 2 * s * Real.exp (k v - k s)) := by
        funext s
        simp [pairWeight, orderedTriangle, indicator, hv.1]
      rw [hslice, integral_indicator measurableSet_Ioc,
        ← intervalIntegral.integral_of_le hv.2, ← intervalIntegral.integral_const_mul]
      apply intervalIntegral.integral_congr
      intro s _
      dsimp only
      rw [Real.exp_sub]
      ring
    · rw [indicator_of_notMem hv]
      have hzero : ∀ s, pairWeight k (v, s) = 0 := by
        intro s
        apply indicator_of_notMem
        intro hp
        exact hv ⟨hp.1, hp.2.1.le.trans hp.2.2⟩
      simp only [hzero, integral_zero]
  calc
    pairFunctional k = ∫ p : ℝ × ℝ, pairWeight k p :=
      (integral_indicator measurableSet_orderedTriangle).symm
    _ = ∫ v, ∫ s, pairWeight k (v, s) := by
      rw [Measure.volume_eq_prod]
      exact integral_prod _ hprod
    _ = ∫ v in Icc (0 : ℝ) 1,
        Real.exp (k v) * (∫ s in v..1, 2 * s / Real.exp (k s)) := by
      rw [hforward, integral_indicator measurableSet_Icc]
    _ = ∫ v in 0..1, Real.exp (k v) * (∫ s in v..1, 2 * s / Real.exp (k s)) := by
      rw [integral_Icc_eq_integral_Ioc, intervalIntegral.integral_of_le zero_le_one]

/-- The literal reciprocal logarithm converts the pair integral to its normalized tail. -/
theorem pairFunctional_log_reciprocal (a : ℝ → ℝ) (M : ℝ) (hM : 0 < M)
    (ha : ContinuousOn a (Icc 0 1)) (hpos : ∀ v ∈ Icc (0 : ℝ) 1, 0 < a v) :
    pairFunctional (fun v => Real.log (M / a v)) =
      ∫ v in 0..1, (2 * ∫ s in v..1, s * a s) / a v := by
  rw [pairFunctional_eq_forward_intervalIntegral _
    (continuousOn_log_reciprocal a M hM _ ha hpos)]
  apply intervalIntegral.integral_congr
  intro v hv
  rw [uIcc_of_le zero_le_one] at hv
  dsimp only
  rw [Real.exp_log (div_pos hM (hpos v hv))]
  have htail : (∫ s in v..1, 2 * s / Real.exp (Real.log (M / a s))) =
      (2 / M) * ∫ s in v..1, s * a s := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro s hs
    rw [uIcc_of_le hv.2] at hs
    have hs0 : s ∈ Icc (0 : ℝ) 1 := ⟨hv.1.trans hs.1, hs.2⟩
    dsimp only
    rw [Real.exp_log (div_pos hM (hpos s hs0))]
    field_simp [hM.ne', (hpos s hs0).ne']
  rw [htail]
  field_simp [hM.ne', (hpos v hv).ne']

end RicciFlowSharpEstimate.Variational
