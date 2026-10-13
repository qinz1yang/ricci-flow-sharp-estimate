/-
Copyright (c) 2026 Ziyang Qin. All rights reserved.
No license is granted by this file.
Authors: Ziyang Qin
-/
import RicciFlowSharpEstimate.Analysis.BoxMomentMultipliers
import RicciFlowSharpEstimate.Analysis.BoxVariationalInequality
import RicciFlowSharpEstimate.Geometry.AreaCurvatureBoxQualification
import RicciFlowSharpEstimate.Geometry.BoundedCurvatureOptimality

/-!
# Genuine moment multipliers for the actual joint weak minimum

The two curvature-moment multipliers follow from constrained linear
minimality and a proved strict-box qualification. Measurable variations give
almost-everywhere box complementarity for the complete mass-corrected adjoint.
The cap-one degeneracy is handled separately and implies no switching structure.
-/

noncomputable section
namespace RicciFlowSharpEstimate.Geometry.AreaProfile
open Set MeasureTheory Filter
open scoped ContDiff
local notation "areaμ" => volume.restrict (Ioo (0 : ℝ) 1)

private theorem corrected_adjoint_integrable {W : ℝ → ℝ}
    (hW : Integrable W areaμ) (a b : ℝ) :
    Integrable (fun x => W x - a - b * x) areaμ := by
  have hx : Integrable (fun x : ℝ => x) areaμ :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le zero_le_one).mp
      (continuous_id.intervalIntegrable 0 1)
  exact (hW.sub (integrable_const a)).sub (hx.const_mul b)

/-- Actual recoverable minimality at a cap greater than one produces two
moment multipliers and a.e. complementary signs in an original positive
ratio box. Strict mean feasibility of that box is derived, not assumed. -/
theorem IsRecoverableAreaCompetitor.exists_curvature_moment_multipliers
    {C : ℝ} {K r p z : ℝ → ℝ} (hC : 1 < C)
    (h : IsRecoverableAreaCompetitor C K r p z)
    (hmin : ∀ K' r' p' z' : ℝ → ℝ, IsRecoverableAreaCompetitor C K' r' p' z' →
      weakMeridionalAction K r p z ≤ weakMeridionalAction K' r' p' z') :
    ∃ κ Λ a b : ℝ, 0 < κ ∧ κ < 2 ∧ 2 < Λ ∧
      (∀ᵐ x ∂areaμ, κ ≤ K x ∧ K x ≤ Λ) ∧ Λ / κ ≤ C ∧
      (∀ᵐ x ∂areaμ,
        (κ < K x → weakCurvatureAdjoint K r p z (weakMeridionalAction K r p z) x -
          a - b * x ≤ 0) ∧
        (K x < Λ → 0 ≤ weakCurvatureAdjoint K r p z (weakMeridionalAction K r p z) x -
          a - b * x)) := by
  obtain ⟨κ, Λ, hκ, hκ2, h2Λ, hbox, hratio⟩ := h.curvature_bounded.exists_strict_box hC
  let W := weakCurvatureAdjoint K r p z (weakMeridionalAction K r p z)
  have hW : Integrable W areaμ := h.weakCurvatureAdjoint_integrable hC.le _
  have hzero : (∫ x, K x ∂areaμ) = 2 := by
    simpa only [intervalIntegral.integral_of_le zero_le_one, integral_Ioc_eq_integral_Ioo]
      using h.2.2.2.1
  have hone : (∫ x, x * K x ∂areaμ) = (2 : ℝ) / 2 := by
    simpa only [intervalIntegral.integral_of_le zero_le_one, integral_Ioc_eq_integral_Ioo,
      div_self (by norm_num : (2 : ℝ) ≠ 0)] using h.2.2.2.2.1
  have hlinear (J : ℝ → ℝ) (hJ : AEStronglyMeasurable J areaμ)
      (hb : ∀ᵐ x ∂areaμ, κ ≤ J x ∧ J x ≤ Λ)
      (h0 : (∫ x, J x ∂areaμ) = 2) (h1 : (∫ x, x * J x ∂areaμ) = (2 : ℝ) / 2) :
      0 ≤ ∫ x, W x * (J x - K x) ∂areaμ := by
    have hj : IsBoundedAreaCurvature C J := by
      refine ⟨hJ, ⟨κ, Λ, hκ, hb, hratio⟩, ?_, ?_⟩
      · simpa only [intervalIntegral.integral_of_le zero_le_one,
          integral_Ioc_eq_integral_Ioo] using h0
      · simpa only [intervalIntegral.integral_of_le zero_le_one,
          integral_Ioc_eq_integral_Ioo, div_self (by norm_num : (2 : ℝ) ≠ 0)] using h1
    simpa only [intervalIntegral.integral_of_le zero_le_one,
      integral_Ioc_eq_integral_Ioo] using
      h.bounded_curvature_adjoint_inequality_of_minimum hC.le hmin J hj
  obtain ⟨a, b, hab⟩ := Analysis.exists_box_moment_multipliers
    W K κ Λ 2 hW h.1.aestronglyMeasurable hbox hzero hone hκ2 h2Λ hlinear
  have hsign := (Analysis.box_variational_inequality_iff
    (corrected_adjoint_integrable hW a b) h.1.aestronglyMeasurable hbox).mp hab
  exact ⟨κ, Λ, a, b, hκ, hκ2, h2Λ, hbox, hratio, hsign⟩

/-- A cap alone produces the actual nonzero normalized joint minimum, its
complete weak probe equation, and genuine moment multipliers with a.e. box
complementarity for the full curvature adjoint. At cap one the returned box
is allowed to degenerate; above one its mean feasibility is strict. No
switch count, symmetry, zero eigenvalue or global sufficiency is asserted. -/
theorem exists_recoverable_area_minimizer_with_moment_multipliers
    (C : ℝ) (hC : 1 ≤ C) :
    ∃ (K r p z : ℝ → ℝ) (κ Λ a b : ℝ),
      IsRecoverableAreaCompetitor C K r p z ∧
      ContinuousOn r (Ioo (0 : ℝ) 1) ∧ ContinuousOn p (Ioo (0 : ℝ) 1) ∧
      (∃ x ∈ Ioo (0 : ℝ) 1, r x ≠ 0) ∧
      weakMeridionalAction K r p z = smoothAreaInfimum C ∧
      (∀ K' r' p' z' : ℝ → ℝ, IsRecoverableAreaCompetitor C K' r' p' z' →
        weakMeridionalAction K r p z ≤ weakMeridionalAction K' r' p' z') ∧
      (∀ s : ℝ → ℝ, ContDiff ℝ ∞ s →
        weakMeridionalPairing K r p z s (deriv s) (deriv (deriv s)) =
          smoothAreaInfimum C * (∫ x in (0 : ℝ)..1, warp K x * s x * r x)) ∧
      Integrable (weakCurvatureAdjoint K r p z (smoothAreaInfimum C)) areaμ ∧
      0 < κ ∧ (1 < C → κ < 2 ∧ 2 < Λ) ∧
      (∀ᵐ x ∂areaμ, κ ≤ K x ∧ K x ≤ Λ) ∧ Λ / κ ≤ C ∧
      (C = 1 → K =ᵐ[areaμ] fun _ => 2) ∧
      (∀ᵐ x ∂areaμ,
        (κ < K x → weakCurvatureAdjoint K r p z (smoothAreaInfimum C) x - a - b * x ≤ 0) ∧
        (K x < Λ → 0 ≤ weakCurvatureAdjoint K r p z (smoothAreaInfimum C) x - a - b * x)) := by
  obtain ⟨K, r, p, z, h, hrc, hpc, hnz, heq, hmin, hprobe, hW, _⟩ :=
    exists_recoverable_area_minimizer_with_bounded_curvature_adjoint C hC
  by_cases hCeq : C = 1
  · have hK : K =ᵐ[areaμ] fun _ => 2 := by
      exact (hCeq ▸ h.curvature_bounded).ae_eq_round_of_cap_one
    refine ⟨K, r, p, z, 2, 2, 0, 0, h, hrc, hpc, hnz, heq, hmin, hprobe, hW,
      by norm_num, ?_, ?_, by simpa using hC, fun _ => hK, ?_⟩
    · simp only [hCeq, lt_self_iff_false, false_implies]
    · filter_upwards [hK] with x hx
      simp only [hx, le_refl, and_self]
    · filter_upwards [hK] with x hx
      simp only [hx, lt_self_iff_false, false_implies, and_self]
  · have hClt : 1 < C := lt_of_le_of_ne hC (Ne.symm hCeq)
    obtain ⟨κ, Λ, a, b, hκ, hκ2, h2Λ, hb, hr, hs⟩ :=
      h.exists_curvature_moment_multipliers hClt hmin
    refine ⟨K, r, p, z, κ, Λ, a, b, h, hrc, hpc, hnz, heq, hmin, hprobe, hW,
      hκ, fun _ => ⟨hκ2, h2Λ⟩, hb, hr, fun he => (hCeq he).elim, ?_⟩
    simpa only [heq] using hs

end RicciFlowSharpEstimate.Geometry.AreaProfile
