/-
Copyright (c) 2026 Ziyang Qin. All rights reserved.
No license is granted by this file.
Authors: Ziyang Qin
-/
import RicciFlowSharpEstimate.Variational.PairFunctional

/-!
# Interval formulas for the actual triangular pair functional

The forward slice of the ordered triangle is `Ioc v 1`, whereas its backward
slice is `Ico 0 v`. Lebesgue endpoint equivalence identifies these with the
corresponding interval integrals. The marginal formula is an exact rewriting
identity for arbitrary profiles. The iterated formula for the pair functional
uses genuine compact-domain integrability and Fubini under interval continuity.
-/

open MeasureTheory Set

namespace RicciFlowSharpEstimate.Variational

private theorem pairWeight_eq_zero_of_first_not_mem (k : ℝ → ℝ) (v s : ℝ)
    (hv : v ∉ Icc (0 : ℝ) 1) : pairWeight k (v, s) = 0 := by
  apply indicator_of_notMem
  intro hp
  exact hv ⟨hp.1, hp.2.1.le.trans hp.2.2⟩

private theorem pairWeight_eq_zero_of_second_not_mem (k : ℝ → ℝ) (t v : ℝ)
    (hv : v ∉ Icc (0 : ℝ) 1) : pairWeight k (t, v) = 0 := by
  apply indicator_of_notMem
  intro hp
  exact hv ⟨hp.1.trans hp.2.1.le, hp.2.2⟩

/-- The actual marginal vanishes outside the unit interval. -/
theorem pairMarginal_eq_zero_of_not_mem (k : ℝ → ℝ) (v : ℝ)
    (hv : v ∉ Icc (0 : ℝ) 1) : pairMarginal k v = 0 := by
  simp only [pairMarginal, pairWeight_eq_zero_of_first_not_mem k v _ hv,
    pairWeight_eq_zero_of_second_not_mem k _ v hv, integral_zero, sub_self]

private theorem integral_pairWeight_forward (k : ℝ → ℝ) (v : ℝ)
    (hv : v ∈ Icc (0 : ℝ) 1) :
    (∫ s, pairWeight k (v, s)) =
      Real.exp (k v) * (∫ s in v..1, 2 * s / Real.exp (k s)) := by
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

private theorem integral_pairWeight_backward (k : ℝ → ℝ) (v : ℝ)
    (hv : v ∈ Icc (0 : ℝ) 1) :
    (∫ t, pairWeight k (t, v)) =
      (2 * v / Real.exp (k v)) * (∫ t in 0..v, Real.exp (k t)) := by
  have hslice : (fun t => pairWeight k (t, v)) =
      (Ico 0 v).indicator (fun t => 2 * v * Real.exp (k t - k v)) := by
    funext t
    simp [pairWeight, orderedTriangle, indicator, hv.2]
  rw [hslice, integral_indicator measurableSet_Ico, integral_Ico_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le hv.1, ← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro t _
  dsimp only
  rw [Real.exp_sub]
  ring

/-- The marginal is the forward tail minus the backward accumulated mass of the actual kernel. -/
theorem pairMarginal_eq_intervalIntegrals (k : ℝ → ℝ) (v : ℝ)
    (hv : v ∈ Icc (0 : ℝ) 1) :
    pairMarginal k v =
      Real.exp (k v) * (∫ s in v..1, 2 * s / Real.exp (k s)) -
        (2 * v / Real.exp (k v)) * (∫ t in 0..v, Real.exp (k t)) := by
  rw [pairMarginal, integral_pairWeight_forward k v hv, integral_pairWeight_backward k v hv]

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

/-- A continuous interval profile has an integrable actual marginal on the real line. -/
theorem integrable_pairMarginal (k : ℝ → ℝ) (hk : ContinuousOn k (Icc 0 1)) :
    Integrable (pairMarginal k) := by
  have hweight := integrable_pairWeight_of_continuousOn hk
  exact hweight.integral_prod_left.sub hweight.integral_prod_right

/-- Fubini rewrites the actual pair functional as the accumulated-profile interval integral. -/
theorem pairFunctional_eq_intervalIntegral (k : ℝ → ℝ)
    (hk : ContinuousOn k (Icc 0 1)) :
    pairFunctional k =
      ∫ s in 0..1, (2 * s / Real.exp (k s)) * (∫ v in 0..s, Real.exp (k v)) := by
  have hweight := integrable_pairWeight_of_continuousOn hk
  have hprod : Integrable (pairWeight k) (volume.prod volume) := by
    simpa only [Measure.volume_eq_prod] using hweight
  have hback : (fun s => ∫ t, pairWeight k (t, s)) =
      (Icc 0 1).indicator
        (fun s => (2 * s / Real.exp (k s)) * (∫ t in 0..s, Real.exp (k t))) := by
    funext s
    by_cases hs : s ∈ Icc (0 : ℝ) 1
    · rw [indicator_of_mem hs]
      exact integral_pairWeight_backward k s hs
    · rw [indicator_of_notMem hs]
      simp only [pairWeight_eq_zero_of_second_not_mem k _ s hs, integral_zero]
  calc
    pairFunctional k = ∫ p : ℝ × ℝ, pairWeight k p := by
      exact (integral_indicator measurableSet_orderedTriangle).symm
    _ = ∫ s, ∫ t, pairWeight k (t, s) := by
      rw [Measure.volume_eq_prod]
      exact integral_prod_symm _ hprod
    _ = ∫ s in Icc (0 : ℝ) 1,
        (2 * s / Real.exp (k s)) * (∫ t in 0..s, Real.exp (k t)) := by
      rw [hback, integral_indicator measurableSet_Icc]
    _ = ∫ s in 0..1, (2 * s / Real.exp (k s)) *
        (∫ t in 0..s, Real.exp (k t)) := by
      rw [integral_Icc_eq_integral_Ioc, intervalIntegral.integral_of_le (by norm_num)]

/-- The actual first variation has its marginal formula on the unit interval. -/
theorem pairFirstVariation_eq_intervalIntegral_marginal (k g : ℝ → ℝ)
    (hk : ContinuousOn k (Icc 0 1)) (hg : ContinuousOn g (Icc 0 1)) :
    pairFirstVariation k g = ∫ v in 0..1, pairMarginal g v * (k v - g v) := by
  rw [pairFirstVariation_eq_integral_marginal k g hk hg]
  have hs : (fun v => pairMarginal g v * (k v - g v)) =
      (Icc (0 : ℝ) 1).indicator (fun v => pairMarginal g v * (k v - g v)) := by
    funext v
    by_cases hv : v ∈ Icc (0 : ℝ) 1
    · rw [indicator_of_mem hv]
    · rw [indicator_of_notMem hv, pairMarginal_eq_zero_of_not_mem g v hv, zero_mul]
  conv_lhs => rw [hs]
  rw [integral_indicator measurableSet_Icc, integral_Icc_eq_integral_Ioc,
    intervalIntegral.integral_of_le (by norm_num)]

end RicciFlowSharpEstimate.Variational
