/-
Copyright (c) 2026 Ziyang Qin. All rights reserved.
No license is granted by this file.
Authors: Ziyang Qin
-/
import RicciFlowSharpEstimate.Analysis.BalancedMomentRecovery
import RicciFlowSharpEstimate.Geometry.SmoothAreaCurvature
import RicciFlowSharpEstimate.Geometry.RecoverableAreaCompetitor

/-!
# Bounded measurable area curvature and unrestricted smooth recovery

Admissibility retains the two exact physical moments and the actual positive
ratio box. Square integrability is derived from that box. The recovery
sequence keeps the same box witnesses, without symmetry or monotonicity.
-/

noncomputable section
namespace RicciFlowSharpEstimate.Geometry.AreaProfile
open Set MeasureTheory Filter
open scoped ENNReal Topology ContDiff
local notation "areaμ" => volume.restrict (Ioo (0 : ℝ) 1)

/-- Measurable area curvature with its original positive ratio box and exact moments. -/
def IsBoundedAreaCurvature (C : ℝ) (K : ℝ → ℝ) : Prop :=
  AEStronglyMeasurable K areaμ ∧
    (∃ κ Λ : ℝ, 0 < κ ∧ (∀ᵐ x ∂areaμ, κ ≤ K x ∧ K x ≤ Λ) ∧ Λ / κ ≤ C) ∧
    (∫ x in (0 : ℝ)..1, K x) = 2 ∧ (∫ x in (0 : ℝ)..1, x * K x) = 1

/-- The positive essential box gives actual square integrability. -/
theorem IsBoundedAreaCurvature.memLp_curvature {C : ℝ} {K : ℝ → ℝ}
    (h : IsBoundedAreaCurvature C K) : MemLp K 2 areaμ := by
  obtain ⟨hm, ⟨κ, Λ, hκ, hb, _⟩, _⟩ := h
  apply MemLp.of_bound hm Λ
  filter_upwards [hb] with x hx
  simpa only [Real.norm_eq_abs, abs_of_nonneg (hκ.le.trans hx.1)] using hx.2

/-- Every original smooth admissible curvature embeds in the measurable class. -/
theorem IsSmoothAreaCurvature.bounded {C : ℝ} {K : ℝ → ℝ}
    (h : IsSmoothAreaCurvature C K) : IsBoundedAreaCurvature C K := by
  obtain ⟨hm, ⟨κ, Λ, hκ, hb, hr⟩, h0, h1⟩ := h
  refine ⟨hm.continuous.aestronglyMeasurable, ⟨κ, Λ, hκ, ?_, hr⟩, h0, h1⟩
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
  exact hb x ⟨hx.1.le, hx.2.le⟩

/-- The curvature of a recoverable weak pair has the same primary measurable constraints. -/
theorem IsRecoverableAreaCompetitor.curvature_bounded {C : ℝ} {K r p z : ℝ → ℝ}
    (h : IsRecoverableAreaCompetitor C K r p z) : IsBoundedAreaCurvature C K :=
  ⟨h.1.aestronglyMeasurable, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1⟩

/-- Every bounded measurable curvature with both physical moments admits
strong L2 recovery by original smooth curvatures in the very same positive
box. The returned box witnesses control both the limit and every approximant;
the original ratio restriction is retained, including a degenerate box. -/
theorem IsBoundedAreaCurvature.exists_smooth_recovery
    {C : ℝ} {K : ℝ → ℝ} (h : IsBoundedAreaCurvature C K) :
    ∃ (κ Λ : ℝ) (Ks : ℕ → ℝ → ℝ), 0 < κ ∧
      (∀ᵐ x ∂areaμ, κ ≤ K x ∧ K x ≤ Λ) ∧ Λ / κ ≤ C ∧
      (∀ n, IsSmoothAreaCurvature C (Ks n)) ∧
      (∀ n x, κ ≤ Ks n x ∧ Ks n x ≤ Λ) ∧
      Tendsto (fun n => eLpNorm (Ks n - K) 2 areaμ) atTop (𝓝 0) := by
  have hm := h.memLp_curvature
  obtain ⟨_, ⟨κ, Λ, hκ, hb, hr⟩, h0, h1⟩ := h
  obtain ⟨Ks, hKs, hconv⟩ := Analysis.exists_contDiff_Icc_exact_balanced_moments_sequence
    K κ Λ 2 hm hb h0 (by simpa using h1)
  refine ⟨κ, Λ, Ks, hκ, hb, hr, ?_, fun n x => (hKs n).2.1 x, hconv⟩
  intro n
  exact ⟨(hKs n).1, ⟨κ, Λ, hκ, fun x _ => (hKs n).2.1 x, hr⟩,
    (hKs n).2.2.1, by simpa using (hKs n).2.2.2⟩

end RicciFlowSharpEstimate.Geometry.AreaProfile
