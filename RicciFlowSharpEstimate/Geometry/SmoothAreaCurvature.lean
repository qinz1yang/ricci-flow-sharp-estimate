/-
Copyright (c) 2026 Ziyang Qin. All rights reserved.
No license is granted by this file.
Authors: Ziyang Qin
-/
import RicciFlowSharpEstimate.Geometry.SmoothAreaInfimum
import RicciFlowSharpEstimate.Geometry.AreaIntegrableAffine

/-!
# The smooth normalized area curvature class

Curvature admissibility consists of smoothness, an actual positive box with
the prescribed ratio, and the two exact area moments. It does not depend on
a probe. Convex combinations retain the ratio through the corresponding
convex combinations of the original positive box witnesses.
-/

noncomputable section

namespace RicciFlowSharpEstimate.Geometry.AreaProfile

open MeasureTheory Set
open scoped ContDiff

local notation "areaμ" => volume.restrict (Ioo (0 : ℝ) 1)

/-- Smooth area curvature with its original positive ratio box and exact moments. -/
def IsSmoothAreaCurvature (C : ℝ) (K : ℝ → ℝ) : Prop :=
  ContDiff ℝ ∞ K ∧
    (∃ κ Λ : ℝ, 0 < κ ∧
      (∀ x ∈ Icc (0 : ℝ) 1, κ ≤ K x ∧ K x ≤ Λ) ∧ Λ / κ ≤ C) ∧
    (∫ x in (0 : ℝ)..1, K x) = 2 ∧
    (∫ x in (0 : ℝ)..1, x * K x) = 1

/-- The curvature of every original smooth competitor is admissible independently of its probe. -/
theorem IsSmoothAreaCompetitor.curvature_admissible {C : ℝ} {K r : ℝ → ℝ}
    (h : IsSmoothAreaCompetitor C K r) : IsSmoothAreaCurvature C K := by
  rcases h with ⟨hK, _, hbox, hzero, hone, _⟩
  exact ⟨hK, hbox, hzero, hone⟩

/-- Admissible curvature and any smooth unit-mass probe give an original smooth competitor. -/
theorem IsSmoothAreaCurvature.with_unit_probe {C : ℝ} {K : ℝ → ℝ}
    (h : IsSmoothAreaCurvature C K) (r : ℝ → ℝ) (hr : ContDiff ℝ ∞ r)
    (hmass : probeMass K r = 1) : IsSmoothAreaCompetitor C K r := by
  rcases h with ⟨hK, hbox, hzero, hone⟩
  exact ⟨hK, hr, hbox, hzero, hone, hmass⟩

/-- The original positive ratio box and zeroth moment give the common curvature bounds. -/
theorem IsSmoothAreaCurvature.common_bounds {C : ℝ} {K : ℝ → ℝ}
    (h : IsSmoothAreaCurvature C K) :
    ∀ x ∈ Icc (0 : ℝ) 1, 2 / C ≤ K x ∧ K x ≤ 2 * C := by
  rcases h with ⟨hK, ⟨κ, Λ, hκ, hbox, hratio⟩, hzero, _⟩
  exact curvature_bounds_of_ratio K hK.continuous κ Λ C hκ hbox hratio hzero

/-- The original positive curvature box gives square integrability on the area interval. -/
theorem IsSmoothAreaCurvature.memLp_curvature {C : ℝ} {K : ℝ → ℝ}
    (h : IsSmoothAreaCurvature C K) : MemLp K 2 areaμ := by
  rcases h with ⟨hK, ⟨κ, Λ, hκ, hbox, _⟩, _, _⟩
  apply MemLp.of_bound hK.continuous.aestronglyMeasurable Λ
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
  have hb := hbox x ⟨hx.1.le, hx.2.le⟩
  simpa only [Real.norm_eq_abs, abs_of_nonneg (hκ.le.trans hb.1)] using hb.2

/-- The actual warp and slope retain their common geometric bounds without a probe hypothesis. -/
theorem IsSmoothAreaCurvature.geometry_bounds {C : ℝ} {K : ℝ → ℝ}
    (h : IsSmoothAreaCurvature C K) (x : ℝ) (hx : x ∈ Icc (0 : ℝ) 1) :
    (2 / C) * x * (1 - x) ≤ warp K x ∧
      warp K x ≤ (2 * C) * x * (1 - x) ∧ |warpSlope K x| ≤ 2 := by
  have hcommon := h.common_bounds
  rcases h with ⟨hK, ⟨κ, Λ, hκ, hbox, _⟩, hzero, hone⟩
  have hb := warp_bounds_of_curvature_bounds K hK.continuous
    (2 / C) (2 * C) hcommon hzero hone x hx
  exact ⟨hb.1, hb.2, abs_warpSlope_le_two K hK.continuous
    (fun y hy => hκ.le.trans (hbox y hy).1) hzero x hx⟩

/-- Convex combinations remain in the actual smooth curvature-ratio class, using
the corresponding mixtures of the original positive box witnesses. -/
theorem IsSmoothAreaCurvature.convex_combination {C : ℝ} {K J : ℝ → ℝ}
    (hK : IsSmoothAreaCurvature C K) (hJ : IsSmoothAreaCurvature C J)
    (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
    IsSmoothAreaCurvature C (fun x => (1 - t) * K x + t * J x) := by
  rcases hK with ⟨hK, ⟨κK, ΛK, hκK, hboxK, hratioK⟩, hKzero, hKone⟩
  rcases hJ with ⟨hJ, ⟨κJ, ΛJ, hκJ, hboxJ, hratioJ⟩, hJzero, hJone⟩
  have hweight : 0 ≤ 1 - t := sub_nonneg.mpr ht.2
  have hκmix : 0 < (1 - t) * κK + t * κJ := by
    by_cases hlt : t < 1
    · exact add_pos_of_pos_of_nonneg (mul_pos (sub_pos.mpr hlt) hκK)
        (mul_nonneg ht.1 hκJ.le)
    · have htone : t = 1 := le_antisymm ht.2 (not_lt.mp hlt)
      simpa only [htone, sub_self, zero_mul, one_mul, zero_add] using hκJ
  have hKi : IntegrableOn K (Ioo (0 : ℝ) 1) volume :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le zero_le_one).mp
      (hK.continuous.intervalIntegrable 0 1)
  have hJi : IntegrableOn J (Ioo (0 : ℝ) 1) volume :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le zero_le_one).mp
      (hJ.continuous.intervalIntegrable 0 1)
  have hmoments := curvature_moments_affine_of_integrableOn K J hKi hJi
    hKzero hKone hJzero hJone t
  refine ⟨(contDiff_const.mul hK).add (contDiff_const.mul hJ),
    ⟨(1 - t) * κK + t * κJ, (1 - t) * ΛK + t * ΛJ, hκmix, ?_, ?_⟩,
    hmoments.1, hmoments.2⟩
  · intro x hx
    exact ⟨add_le_add
      (mul_le_mul_of_nonneg_left (hboxK x hx).1 hweight)
      (mul_le_mul_of_nonneg_left (hboxJ x hx).1 ht.1),
      add_le_add (mul_le_mul_of_nonneg_left (hboxK x hx).2 hweight)
        (mul_le_mul_of_nonneg_left (hboxJ x hx).2 ht.1)⟩
  · apply (div_le_iff₀ hκmix).mpr
    calc
      (1 - t) * ΛK + t * ΛJ ≤ (1 - t) * (C * κK) + t * (C * κJ) :=
        add_le_add
          (mul_le_mul_of_nonneg_left ((div_le_iff₀ hκK).mp hratioK) hweight)
          (mul_le_mul_of_nonneg_left ((div_le_iff₀ hκJ).mp hratioJ) ht.1)
      _ = C * ((1 - t) * κK + t * κJ) := by ring

/-- Round curvature witnesses nonemptiness for every ratio bound at least one. -/
theorem isSmoothAreaCurvature_round (C : ℝ) (hC : 1 ≤ C) :
    IsSmoothAreaCurvature C (fun _ => 2) :=
  (isSmoothAreaCompetitor_round C hC).curvature_admissible

end RicciFlowSharpEstimate.Geometry.AreaProfile
