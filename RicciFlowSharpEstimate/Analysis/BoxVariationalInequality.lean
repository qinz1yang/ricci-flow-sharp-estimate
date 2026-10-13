/-
Copyright (c) 2026 Ziyang Qin. All rights reserved.
No license is granted by this file.
Authors: Ziyang Qin
-/
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Variational inequalities for a pointwise box

The integral variational inequality over a real pointwise box is equivalent
to the almost-everywhere sign conditions on the sets where each obstacle is
inactive. Integrability of the weight and boundedness of the competitors
make every pairing integrable, without a finiteness assumption on the
measure. The result also includes zero measures and degenerate boxes.
-/

noncomputable section

namespace RicciFlowSharpEstimate.Analysis

open Filter MeasureTheory

private theorem integrable_box_pairing
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {W K J : α → ℝ} {lo hi : ℝ}
    (hW : Integrable W μ)
    (hK : AEStronglyMeasurable K μ) (hJ : AEStronglyMeasurable J μ)
    (hKbox : ∀ᵐ x ∂μ, lo ≤ K x ∧ K x ≤ hi)
    (hJbox : ∀ᵐ x ∂μ, lo ≤ J x ∧ J x ≤ hi) :
    Integrable (fun x ↦ W x * (J x - K x)) μ := by
  refine hW.mul_bdd (c := hi - lo) (hJ.sub hK) ?_
  filter_upwards [hKbox, hJbox] with x hKx hJx
  rw [Real.norm_eq_abs]
  refine abs_le.mpr ⟨?_, sub_le_sub hJx.2 hKx.1⟩
  simpa only [neg_sub] using sub_le_sub hJx.1 hKx.2

/-- A real function in a pointwise box satisfies the integral variational
inequality against every measurable box competitor exactly when its weight
has the appropriate sign wherever each obstacle is inactive. -/
theorem box_variational_inequality_iff
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {W K : α → ℝ} {lo hi : ℝ}
    (hW : Integrable W μ) (hK : AEStronglyMeasurable K μ)
    (hKbox : ∀ᵐ x ∂μ, lo ≤ K x ∧ K x ≤ hi) :
    (∀ J : α → ℝ, AEStronglyMeasurable J μ →
      (∀ᵐ x ∂μ, lo ≤ J x ∧ J x ≤ hi) →
      0 ≤ ∫ x, W x * (J x - K x) ∂μ) ↔
      ∀ᵐ x ∂μ, (lo < K x → W x ≤ 0) ∧ (K x < hi → 0 ≤ W x) := by
  classical
  constructor
  · intro hvi
    let V : α → ℝ := hW.aestronglyMeasurable.mk W
    have hV : Measurable V := hW.aestronglyMeasurable.measurable_mk
    have hWV : W =ᵐ[μ] V := hW.aestronglyMeasurable.ae_eq_mk
    let J : α → ℝ := fun x ↦ if 0 ≤ V x then lo else hi
    have hJ : AEStronglyMeasurable J μ :=
      (Measurable.ite (measurableSet_le measurable_const hV)
        measurable_const measurable_const).aestronglyMeasurable
    have hJbox : ∀ᵐ x ∂μ, lo ≤ J x ∧ J x ≤ hi := by
      filter_upwards [hKbox] with x hKx
      by_cases hs : 0 ≤ V x
      · simpa only [J, ite_eq_left hs] using
          (show lo ≤ lo ∧ lo ≤ hi from ⟨le_rfl, hKx.1.trans hKx.2⟩)
      · simpa only [J, ite_eq_right hs] using
          (show lo ≤ hi ∧ hi ≤ hi from ⟨hKx.1.trans hKx.2, le_rfl⟩)
    have hpair : Integrable (fun x ↦ W x * (J x - K x)) μ :=
      integrable_box_pairing hW hK hJ hKbox hJbox
    have hnonpos : ∀ᵐ x ∂μ, W x * (J x - K x) ≤ 0 := by
      filter_upwards [hKbox, hWV] with x hKx hWx
      by_cases hs : 0 ≤ V x
      · have hsign : 0 ≤ W x := by rwa [hWx]
        simpa only [J, ite_eq_left hs] using
          mul_nonpos_of_nonneg_of_nonpos hsign (sub_nonpos.mpr hKx.1)
      · have hsign : W x ≤ 0 := by
          rw [hWx]
          exact (lt_of_not_ge hs).le
        simpa only [J, ite_eq_right hs] using
          mul_nonpos_of_nonpos_of_nonneg hsign (sub_nonneg.mpr hKx.2)
    have hint : (∫ x, W x * (J x - K x) ∂μ) = ∫ x, (0 : ℝ) ∂μ := by
      rw [integral_zero]
      exact le_antisymm (integral_nonpos_of_ae hnonpos) (hvi J hJ hJbox)
    have hzero : ∀ᵐ x ∂μ, W x * (J x - K x) = 0 :=
      (integral_eq_iff_of_ae_le hpair (integrable_zero α ℝ μ) hnonpos).mp hint
    filter_upwards [hWV, hzero] with x hWx hzx
    by_cases hs : 0 ≤ V x
    · have hz : W x * (lo - K x) = 0 := by
        simpa only [J, ite_eq_left hs] using hzx
      constructor
      · intro hgap
        exact ((mul_eq_zero.mp hz).resolve_right
          (sub_ne_zero.mpr (ne_of_lt hgap))).le
      · intro _
        rwa [hWx]
    · have hz : W x * (hi - K x) = 0 := by
        simpa only [J, ite_eq_right hs] using hzx
      constructor
      · intro _
        rw [hWx]
        exact (lt_of_not_ge hs).le
      · intro hgap
        exact ((mul_eq_zero.mp hz).resolve_right
          (sub_ne_zero.mpr (ne_of_gt hgap))).ge
  · intro hsign J hJ hJbox
    have hpair : Integrable (fun x ↦ W x * (J x - K x)) μ :=
      integrable_box_pairing hW hK hJ hKbox hJbox
    have hnonneg : ∀ᵐ x ∂μ, 0 ≤ W x * (J x - K x) := by
      filter_upwards [hsign, hJbox] with x hs hJx
      rcases lt_trichotomy (J x) (K x) with hlt | heq | hgt
      · exact mul_nonneg_of_nonpos_of_nonpos
          (hs.1 (hJx.1.trans_lt hlt)) (sub_nonpos.mpr hlt.le)
      · simp only [heq, sub_self, mul_zero, le_refl]
      · exact mul_nonneg (hs.2 (hgt.trans_le hJx.2)) (sub_nonneg.mpr hgt.le)
    calc
      0 = ∫ x, (0 : ℝ) ∂μ := by rw [integral_zero]
      _ ≤ ∫ x, W x * (J x - K x) ∂μ :=
        integral_mono_ae (integrable_zero α ℝ μ) hpair hnonneg

end RicciFlowSharpEstimate.Analysis
