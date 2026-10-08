/-
Copyright (c) 2026 Ziyang Qin. All rights reserved.
No license is granted by this file.
Authors: Ziyang Qin
-/
import RicciFlowSharpEstimate.Variational.PairFunctional
import RicciFlowSharpEstimate.Analysis.ExponentialRemainder

/-!
# Quadratic control by the actual pair remainder

Profiles in the logarithmic cap box have pair differences at least `-log C`.
The exponential tangent estimate therefore has uniform coefficient `1/(2C)`.
Multiplication by the actual triangular weight and integration yields the
quadratic bound below, with compact-domain integrability proved explicitly.
-/

open MeasureTheory Set

namespace RicciFlowSharpEstimate.Variational

private theorem continuousOn_profilePairDifference {f : ℝ → ℝ}
    (hf : ContinuousOn f (Icc 0 1)) :
    ContinuousOn (fun p : ℝ × ℝ => f p.1 - f p.2) (Icc (0, 0) (1, 1)) := by
  apply ContinuousOn.sub
  · exact hf.comp continuous_fst.continuousOn (fun _ hp => ⟨hp.1.1, hp.2.1⟩)
  · exact hf.comp continuous_snd.continuousOn (fun _ hp => ⟨hp.1.2, hp.2.2⟩)

private theorem weighted_exp_remainder_ge_square (C x y w : ℝ) (hC : 0 < C)
    (hx : -Real.log C ≤ x) (hy : -Real.log C ≤ y) (hw : 0 ≤ w) :
    (1 / (2 * C)) * (w * (x - y) ^ 2) ≤
      w * Real.exp y * (Real.exp (x - y) - 1 - (x - y)) := by
  have h := Analysis.exp_tangent_quadratic_lower (-Real.log C) x y hx hy
  have he : Real.exp x = Real.exp y * Real.exp (x - y) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [Real.exp_neg, Real.exp_log hC, he] at h
  convert mul_le_mul_of_nonneg_left h hw using 1 <;> ring

/-- The actual exponential pair remainder controls the weighted squared difference of profiles. -/
theorem pairRemainder_ge_quadratic_integral (C : ℝ) (hC : 1 ≤ C) (k g : ℝ → ℝ)
    (hk : ContinuousOn k (Icc 0 1)) (hg : ContinuousOn g (Icc 0 1))
    (hkbox : ∀ v ∈ Icc (0 : ℝ) 1, 0 ≤ k v ∧ k v ≤ Real.log C)
    (hgbox : ∀ v ∈ Icc (0 : ℝ) 1, 0 ≤ g v ∧ g v ≤ Real.log C) :
    (1 / (2 * C)) *
        (∫ p in orderedTriangle, 2 * p.2 * ((k p.1 - g p.1) - (k p.2 - g p.2)) ^ 2) ≤
      pairRemainder k g := by
  let Q : ℝ × ℝ → ℝ := fun p =>
    2 * p.2 * ((k p.1 - g p.1) - (k p.2 - g p.2)) ^ 2
  let R : ℝ × ℝ → ℝ := fun p => 2 * p.2 * Real.exp (g p.1 - g p.2) *
    (Real.exp ((k p.1 - g p.1) - (k p.2 - g p.2)) - 1 -
      ((k p.1 - g p.1) - (k p.2 - g p.2)))
  have hTS : orderedTriangle ⊆ Icc ((0 : ℝ), (0 : ℝ)) (1, 1) := by
    rintro p ⟨h0, h12, h1⟩
    exact ⟨⟨h0, h0.trans h12.le⟩, ⟨h12.le.trans h1, h1⟩⟩
  have hgdiff := continuousOn_profilePairDifference hg
  have hδdiff := continuousOn_profilePairDifference (hk.sub hg)
  have hQcont : ContinuousOn Q (Icc (0, 0) (1, 1)) :=
    (continuous_const.mul continuous_snd).continuousOn.mul (hδdiff.pow 2)
  have hRcont : ContinuousOn R (Icc (0, 0) (1, 1)) :=
    ((continuous_const.mul continuous_snd).continuousOn.mul
      (Real.continuous_exp.comp_continuousOn hgdiff)).mul
      (((Real.continuous_exp.comp_continuousOn hδdiff).sub continuousOn_const).sub hδdiff)
  have hQint : IntegrableOn Q orderedTriangle :=
    (hQcont.integrableOn_compact isCompact_Icc).mono_set hTS
  have hRint : IntegrableOn R orderedTriangle :=
    (hRcont.integrableOn_compact isCompact_Icc).mono_set hTS
  change (1 / (2 * C)) * (∫ p in orderedTriangle, Q p) ≤ ∫ p in orderedTriangle, R p
  rw [← integral_const_mul]
  apply integral_mono_ae (hQint.const_mul (1 / (2 * C))) hRint
  filter_upwards [ae_restrict_mem measurableSet_orderedTriangle] with p hp
  have hp1 : p.1 ∈ Icc (0 : ℝ) 1 := ⟨hp.1, hp.2.1.le.trans hp.2.2⟩
  have hp2 : p.2 ∈ Icc (0 : ℝ) 1 := ⟨hp.1.trans hp.2.1.le, hp.2.2⟩
  have hx : -Real.log C ≤ k p.1 - k p.2 := by
    linarith [(hkbox p.1 hp1).1, (hkbox p.2 hp2).2]
  have hy : -Real.log C ≤ g p.1 - g p.2 := by
    linarith [(hgbox p.1 hp1).1, (hgbox p.2 hp2).2]
  have hδ : (k p.1 - g p.1) - (k p.2 - g p.2) =
      (k p.1 - k p.2) - (g p.1 - g p.2) := by ring
  dsimp only [Q, R]
  rw [hδ]
  exact weighted_exp_remainder_ge_square C (k p.1 - k p.2) (g p.1 - g p.2) (2 * p.2)
    (lt_of_lt_of_le zero_lt_one hC) hx hy (mul_nonneg (by norm_num) hp2.1)

end RicciFlowSharpEstimate.Variational
