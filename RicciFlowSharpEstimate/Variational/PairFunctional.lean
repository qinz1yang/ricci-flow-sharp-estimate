/-
Copyright (c) 2026 Ziyang Qin. All rights reserved.
No license is granted by this file.
Authors: Ziyang Qin
-/
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Exact convex deficit for the ordered exponential pair functional

The domain is the actual triangle `0 ≤ v < s ≤ 1`. Profiles need only be
continuous on `[0,1]`; their values outside this interval are irrelevant.
The exact identity separates the first variation from the nonnegative
exponential remainder. Explicit obstacle calibration is developed separately.

The triangle and marginal-calibration method follow the owner-provided
historical `PureRotationSharpThreshold` and `PureRotationSharpFunctional`
modules. This development uses interval continuity and no historical imports.
-/

open MeasureTheory Set

namespace RicciFlowSharpEstimate.Variational

/-- The ordered pairs in the unit interval. -/
def orderedTriangle : Set (ℝ × ℝ) := {p | 0 ≤ p.1 ∧ p.1 < p.2 ∧ p.2 ≤ 1}

theorem measurableSet_orderedTriangle : MeasurableSet orderedTriangle := by
  have h0 : MeasurableSet {p : ℝ × ℝ | 0 ≤ p.1} :=
    measurableSet_le measurable_const measurable_fst
  have h12 : MeasurableSet {p : ℝ × ℝ | p.1 < p.2} :=
    measurableSet_lt measurable_fst measurable_snd
  have h1 : MeasurableSet {p : ℝ × ℝ | p.2 ≤ 1} :=
    measurableSet_le measurable_snd measurable_const
  exact h0.inter (h12.inter h1)

private theorem orderedTriangle_subset_square :
    orderedTriangle ⊆ Icc ((0 : ℝ), (0 : ℝ)) (1, 1) := by
  rintro p ⟨h0, h12, h1⟩
  exact ⟨⟨h0, h0.trans h12.le⟩, ⟨h12.le.trans h1, h1⟩⟩

private theorem continuousOn_pairDifference {k : ℝ → ℝ}
    (hk : ContinuousOn k (Icc 0 1)) :
    ContinuousOn (fun p : ℝ × ℝ => k p.1 - k p.2) (Icc (0, 0) (1, 1)) := by
  apply ContinuousOn.sub
  · exact hk.comp continuous_fst.continuousOn (fun _ hp => ⟨hp.1.1, hp.2.1⟩)
  · exact hk.comp continuous_snd.continuousOn (fun _ hp => ⟨hp.1.2, hp.2.2⟩)

private theorem integrableOn_triangle_of_continuousOn {F : ℝ × ℝ → ℝ}
    (hF : ContinuousOn F (Icc (0, 0) (1, 1))) : IntegrableOn F orderedTriangle :=
  (hF.integrableOn_compact isCompact_Icc).mono_set orderedTriangle_subset_square

/-- The pair kernel, extended by zero away from the ordered triangle. -/
noncomputable def pairWeight (g : ℝ → ℝ) (p : ℝ × ℝ) : ℝ :=
  orderedTriangle.indicator (fun p => 2 * p.2 * Real.exp (g p.1 - g p.2)) p

/-- Forward marginal minus backward marginal of the actual pair kernel. -/
noncomputable def pairMarginal (g : ℝ → ℝ) (v : ℝ) : ℝ :=
  (∫ s, pairWeight g (v, s)) - ∫ t, pairWeight g (t, v)

/-- The triangular exponential pair integral. -/
noncomputable def pairFunctional (k : ℝ → ℝ) : ℝ :=
  ∫ p in orderedTriangle, 2 * p.2 * Real.exp (k p.1 - k p.2)

/-- The first variation at `g` in the direction `k - g`. -/
noncomputable def pairFirstVariation (k g : ℝ → ℝ) : ℝ :=
  ∫ p in orderedTriangle, 2 * p.2 * Real.exp (g p.1 - g p.2) *
    ((k p.1 - g p.1) - (k p.2 - g p.2))

/-- The exact exponential remainder after linearization at `g`. -/
noncomputable def pairRemainder (k g : ℝ → ℝ) : ℝ :=
  ∫ p in orderedTriangle, 2 * p.2 * Real.exp (g p.1 - g p.2) *
    (Real.exp ((k p.1 - g p.1) - (k p.2 - g p.2)) - 1 -
      ((k p.1 - g p.1) - (k p.2 - g p.2)))

private theorem integrableOn_pairKernel {k : ℝ → ℝ}
    (hk : ContinuousOn k (Icc 0 1)) :
    IntegrableOn (fun p : ℝ × ℝ => 2 * p.2 * Real.exp (k p.1 - k p.2))
      orderedTriangle := by
  apply integrableOn_triangle_of_continuousOn
  exact (continuous_const.mul continuous_snd).continuousOn.mul
    (Real.continuous_exp.comp_continuousOn (continuousOn_pairDifference hk))

private theorem integrableOn_firstVariation {k g : ℝ → ℝ}
    (hk : ContinuousOn k (Icc 0 1)) (hg : ContinuousOn g (Icc 0 1)) :
    IntegrableOn (fun p : ℝ × ℝ => 2 * p.2 * Real.exp (g p.1 - g p.2) *
      ((k p.1 - g p.1) - (k p.2 - g p.2))) orderedTriangle := by
  apply integrableOn_triangle_of_continuousOn
  exact ((continuous_const.mul continuous_snd).continuousOn.mul
    (Real.continuous_exp.comp_continuousOn (continuousOn_pairDifference hg))).mul
      (continuousOn_pairDifference (hk.sub hg))

private theorem integrableOn_remainder {k g : ℝ → ℝ}
    (hk : ContinuousOn k (Icc 0 1)) (hg : ContinuousOn g (Icc 0 1)) :
    IntegrableOn (fun p : ℝ × ℝ => 2 * p.2 * Real.exp (g p.1 - g p.2) *
      (Real.exp ((k p.1 - g p.1) - (k p.2 - g p.2)) - 1 -
        ((k p.1 - g p.1) - (k p.2 - g p.2)))) orderedTriangle := by
  apply integrableOn_triangle_of_continuousOn
  exact ((continuous_const.mul continuous_snd).continuousOn.mul
    (Real.continuous_exp.comp_continuousOn (continuousOn_pairDifference hg))).mul
      (((Real.continuous_exp.comp_continuousOn
        (continuousOn_pairDifference (hk.sub hg))).sub continuousOn_const).sub
        (continuousOn_pairDifference (hk.sub hg)))

/-- Exact first-variation-plus-remainder identity for any two continuous interval profiles. -/
theorem pairFunctional_sub_eq (k g : ℝ → ℝ)
    (hk : ContinuousOn k (Icc 0 1)) (hg : ContinuousOn g (Icc 0 1)) :
    pairFunctional k - pairFunctional g = pairFirstVariation k g + pairRemainder k g := by
  rw [pairFunctional, pairFunctional, ← integral_sub (integrableOn_pairKernel hk)
    (integrableOn_pairKernel hg), pairFirstVariation, pairRemainder,
    ← integral_add (integrableOn_firstVariation hk hg) (integrableOn_remainder hk hg)]
  apply integral_congr_ae
  filter_upwards with p
  have he : Real.exp (k p.1 - k p.2) =
      Real.exp (g p.1 - g p.2) *
        Real.exp ((k p.1 - g p.1) - (k p.2 - g p.2)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [he]
  ring

private theorem integrable_pairWeight_mul {g δ : ℝ → ℝ}
    (hg : ContinuousOn g (Icc 0 1)) (hδ : ContinuousOn δ (Icc 0 1)) :
    Integrable (fun p : ℝ × ℝ => pairWeight g p * δ p.1) ∧
      Integrable (fun p : ℝ × ℝ => pairWeight g p * δ p.2) := by
  have hw : ContinuousOn (fun p : ℝ × ℝ => 2 * p.2 * Real.exp (g p.1 - g p.2))
      (Icc (0, 0) (1, 1)) :=
    (continuous_const.mul continuous_snd).continuousOn.mul
      (Real.continuous_exp.comp_continuousOn (continuousOn_pairDifference hg))
  have hl := integrableOn_triangle_of_continuousOn (hw.mul
    (hδ.comp continuous_fst.continuousOn (fun _ hp => ⟨hp.1.1, hp.2.1⟩)))
  have hr := integrableOn_triangle_of_continuousOn (hw.mul
    (hδ.comp continuous_snd.continuousOn (fun _ hp => ⟨hp.1.2, hp.2.2⟩)))
  constructor
  · convert hl.integrable_indicator measurableSet_orderedTriangle using 1
    ext p
    by_cases hp : p ∈ orderedTriangle <;> simp [pairWeight, hp]
  · convert hr.integrable_indicator measurableSet_orderedTriangle using 1
    ext p
    by_cases hp : p ∈ orderedTriangle <;> simp [pairWeight, hp]

/-- Fubini expresses the actual first variation using its marginal density. -/
theorem pairFirstVariation_eq_integral_marginal (k g : ℝ → ℝ)
    (hk : ContinuousOn k (Icc 0 1)) (hg : ContinuousOn g (Icc 0 1)) :
    pairFirstVariation k g = ∫ v, pairMarginal g v * (k v - g v) := by
  let δ := fun v => k v - g v
  have hδ : ContinuousOn δ (Icc 0 1) := hk.sub hg
  obtain ⟨hl, hr⟩ := integrable_pairWeight_mul hg hδ
  have hleft : Integrable (fun v => (∫ s, pairWeight g (v, s)) * δ v) := by
    simpa only [δ, integral_mul_const] using hl.integral_prod_left
  have hright : Integrable (fun v => (∫ t, pairWeight g (t, v)) * δ v) := by
    simpa only [δ, integral_mul_const] using hr.integral_prod_right
  have hfirst : pairFirstVariation k g =
      ∫ p : ℝ × ℝ, pairWeight g p * δ p.1 - pairWeight g p * δ p.2 := by
    rw [pairFirstVariation, ← integral_indicator measurableSet_orderedTriangle]
    apply integral_congr_ae
    filter_upwards with p
    by_cases hp : p ∈ orderedTriangle
    · simp only [indicator_of_mem hp, pairWeight, δ]
      ring
    · simp [pairWeight, hp]
  rw [hfirst, integral_sub hl hr]
  simp only [Measure.volume_eq_prod]
  rw [integral_prod (fun p : ℝ × ℝ => pairWeight g p * δ p.1) hl,
    integral_prod_symm (fun p : ℝ × ℝ => pairWeight g p * δ p.2) hr]
  simp only [integral_mul_const]
  rw [← integral_sub hleft hright]
  apply integral_congr_ae
  filter_upwards with v
  dsimp [pairMarginal, δ]
  ring

/-- The exact deficit, with the linear term written as a one-dimensional marginal integral. -/
theorem pairFunctional_sub_eq_integral_marginal (k g : ℝ → ℝ)
    (hk : ContinuousOn k (Icc 0 1)) (hg : ContinuousOn g (Icc 0 1)) :
    pairFunctional k - pairFunctional g =
      (∫ v, pairMarginal g v * (k v - g v)) + pairRemainder k g := by
  rw [pairFunctional_sub_eq k g hk hg, pairFirstVariation_eq_integral_marginal k g hk hg]

/-- Convexity makes the exact exponential remainder nonnegative. -/
theorem pairRemainder_nonneg (k g : ℝ → ℝ) : 0 ≤ pairRemainder k g := by
  apply setIntegral_nonneg measurableSet_orderedTriangle
  intro p hp
  have hs : 0 ≤ p.2 := hp.1.trans hp.2.1.le
  apply mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hs) (Real.exp_pos _).le)
  have h := Real.add_one_le_exp ((k p.1 - g p.1) - (k p.2 - g p.2))
  linarith

/-- A nonnegative first variation certifies the corresponding comparison. -/
theorem pairFunctional_le_of_firstVariation_nonneg (k g : ℝ → ℝ)
    (hk : ContinuousOn k (Icc 0 1)) (hg : ContinuousOn g (Icc 0 1))
    (hfirst : 0 ≤ pairFirstVariation k g) : pairFunctional g ≤ pairFunctional k := by
  have h := pairFunctional_sub_eq k g hk hg
  have hr := pairRemainder_nonneg k g
  linarith

/-- The functional depends only on the values on the unit interval. -/
theorem pairFunctional_congr (k g : ℝ → ℝ)
    (h : ∀ v ∈ Icc (0 : ℝ) 1, k v = g v) : pairFunctional k = pairFunctional g := by
  unfold pairFunctional
  apply setIntegral_congr_fun measurableSet_orderedTriangle
  intro p hp
  dsimp only
  rw [h p.1 ⟨hp.1, hp.2.1.le.trans hp.2.2⟩,
    h p.2 ⟨hp.1.trans hp.2.1.le, hp.2.2⟩]

/-- Adding a constant to a profile leaves the pair integral unchanged. -/
theorem pairFunctional_add_const (k : ℝ → ℝ) (c : ℝ) :
    pairFunctional (fun v => k v + c) = pairFunctional k := by
  unfold pairFunctional
  congr 1
  ext p
  congr 2
  ring

end RicciFlowSharpEstimate.Variational
