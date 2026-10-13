/-
Copyright (c) 2026 Ziyang Qin. All rights reserved.
No license is granted by this file.
Authors: Ziyang Qin
-/
import RicciFlowSharpEstimate.Geometry.BoundedAreaCurvature

/-!
# Strict moment-feasible curvature boxes

At every ratio cap greater than one, an admissible measurable curvature has
positive box witnesses with two strictly between the endpoints. If an original
witness puts the mean on a boundary, the curvature is constant almost everywhere
and a centered positive ratio box supplies the strict witnesses. At cap one the
curvature is exactly the round curvature almost everywhere.
-/

noncomputable section
namespace RicciFlowSharpEstimate.Geometry.AreaProfile
open Set MeasureTheory
local notation "areaμ" => volume.restrict (Ioo (0 : ℝ) 1)

private theorem mean_bounds {K : ℝ → ℝ} {κ Λ : ℝ}
    (hi : Integrable K areaμ) (hb : ∀ᵐ x ∂areaμ, κ ≤ K x ∧ K x ≤ Λ)
    (hm : (∫ x in (0 : ℝ)..1, K x) = 2) : κ ≤ 2 ∧ 2 ≤ Λ := by
  have hm' : (∫ x, K x ∂areaμ) = 2 := by
    simpa only [intervalIntegral.integral_of_le zero_le_one, integral_Ioc_eq_integral_Ioo]
      using hm
  have hlo := integral_mono_ae (integrable_const κ) hi (hb.mono fun _ hx => hx.1)
  have hhi := integral_mono_ae hi (integrable_const Λ) (hb.mono fun _ hx => hx.2)
  simpa [hm'] using And.intro hlo hhi

private theorem strict_box_of_round {C : ℝ} {K : ℝ → ℝ} (hC : 1 < C)
    (hK : K =ᵐ[areaμ] fun _ => 2) :
    ∃ κ Λ : ℝ, 0 < κ ∧ κ < 2 ∧ 2 < Λ ∧
      (∀ᵐ x ∂areaμ, κ ≤ K x ∧ K x ≤ Λ) ∧ Λ / κ ≤ C := by
  have hCpos : 0 < C := zero_lt_one.trans hC
  have hκ : 0 < 1 + 1 / C := by positivity
  have hi : 1 / C < 1 := (div_lt_one hCpos).mpr hC
  have hprod : C * (1 + 1 / C) = C + 1 := by field_simp
  refine ⟨1 + 1 / C, C + 1, hκ, by linarith, by linarith, ?_, ?_⟩
  · filter_upwards [hK] with x hx
    rw [hx]
    constructor <;> linarith
  · apply (div_le_iff₀ hκ).mpr
    rw [hprod]

/-- At a cap greater than one, the original admissible curvature possesses
an actual positive ratio box in which the prescribed mean lies strictly.
No strictness or constraint qualification of the input box is assumed. -/
theorem IsBoundedAreaCurvature.exists_strict_box
    {C : ℝ} {K : ℝ → ℝ} (h : IsBoundedAreaCurvature C K) (hC : 1 < C) :
    ∃ κ Λ : ℝ, 0 < κ ∧ κ < 2 ∧ 2 < Λ ∧
      (∀ᵐ x ∂areaμ, κ ≤ K x ∧ K x ≤ Λ) ∧ Λ / κ ≤ C := by
  have hi := h.memLp_curvature.integrable (by norm_num : (1 : ENNReal) ≤ 2)
  have hm : (∫ x, K x ∂areaμ) = 2 := by
    simpa only [intervalIntegral.integral_of_le zero_le_one, integral_Ioc_eq_integral_Ioo]
      using h.2.2.1
  obtain ⟨κ, Λ, hκ, hb, hr⟩ := h.2.1
  have hmean := mean_bounds hi hb h.2.2.1
  by_cases hk : κ = 2
  · apply strict_box_of_round hC
    have hle : (fun _ : ℝ => 2) ≤ᵐ[areaμ] K := by
      filter_upwards [hb] with x hx
      simpa only [hk] using hx.1
    exact ((integral_eq_iff_of_ae_le (integrable_const 2) hi hle).mp (by simp [hm])).symm
  by_cases hl : Λ = 2
  · apply strict_box_of_round hC
    have hle : K ≤ᵐ[areaμ] (fun _ : ℝ => 2) := by
      filter_upwards [hb] with x hx
      simpa only [hl] using hx.2
    exact (integral_eq_iff_of_ae_le hi (integrable_const 2) hle).mp (by simp [hm])
  exact ⟨κ, Λ, hκ, lt_of_le_of_ne hmean.1 hk,
    lt_of_le_of_ne hmean.2 (Ne.symm hl), hb, hr⟩

/-- At cap one, every bounded measurable admissible curvature is round
almost everywhere on the physical interval. -/
theorem IsBoundedAreaCurvature.ae_eq_round_of_cap_one
    {K : ℝ → ℝ} (h : IsBoundedAreaCurvature 1 K) : K =ᵐ[areaμ] fun _ => 2 := by
  have hi := h.memLp_curvature.integrable (by norm_num : (1 : ENNReal) ≤ 2)
  obtain ⟨κ, Λ, hκ, hb, hr⟩ := h.2.1
  have hmean := mean_bounds hi hb h.2.2.1
  have hΛκ : Λ ≤ κ := by simpa only [one_mul] using (div_le_iff₀ hκ).mp hr
  have hk : κ = 2 := by linarith [hmean.1, hmean.2]
  have hl : Λ = 2 := by linarith [hmean.1, hmean.2]
  filter_upwards [hb] with x hx
  exact le_antisymm (by simpa only [hl] using hx.2) (by simpa only [hk] using hx.1)

end RicciFlowSharpEstimate.Geometry.AreaProfile
