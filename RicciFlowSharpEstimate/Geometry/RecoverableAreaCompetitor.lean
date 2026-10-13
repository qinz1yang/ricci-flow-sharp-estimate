/-
Copyright (c) 2026 Ziyang Qin. All rights reserved.
No license is granted by this file.
Authors: Ziyang Qin
-/
import RicciFlowSharpEstimate.Geometry.SmoothAreaInfimum
import RicciFlowSharpEstimate.Geometry.AreaStrongGraphContinuity
import RicciFlowSharpEstimate.Analysis.L2PointwiseProducts
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure

/-!
# Recoverable normalized weak area competitors

The class is defined by the actual weak derivatives, physical constraints,
and approximation in the strong curvature/parabolic graph topology by the
original normalized smooth class. Action convergence is a theorem about
this topology, not a field in the definition. No arbitrary maximal-domain
density or smooth attainment is asserted.
-/

noncomputable section
namespace RicciFlowSharpEstimate.Geometry.AreaProfile
open Set MeasureTheory Filter Topology
open scoped ContDiff ENNReal

local notation "areaμ" => volume.restrict (Ioo (0 : ℝ) 1)

/-- Normalized weak competitors in the strong graph closure of the original
smooth class. The weak jets are tied by test identities; the positive box
and ratio are the original physical restrictions. No action limit or
minimality condition occurs in the predicate. -/
def IsRecoverableAreaCompetitor (C : ℝ) (K r p z : ℝ → ℝ) : Prop :=
  MemLp K 2 areaμ ∧ Analysis.HasParabolicWeakDerivatives r p z ∧
  (∃ κ Λ : ℝ, 0 < κ ∧ (∀ᵐ x ∂areaμ, κ ≤ K x ∧ K x ≤ Λ) ∧ Λ / κ ≤ C) ∧
  (∫ x in (0 : ℝ)..1, K x) = 2 ∧ (∫ x in (0 : ℝ)..1, x * K x) = 1 ∧
  probeMass K r = 1 ∧
  ∃ Ks rs : ℕ → ℝ → ℝ,
    (∀ n, IsSmoothAreaCompetitor C (Ks n) (rs n)) ∧
    Tendsto (fun n => eLpNorm (Ks n - K) 2 areaμ) atTop (𝓝 0) ∧
    Tendsto (fun n => eLpNorm (rs n - r) 2 areaμ) atTop (𝓝 0) ∧
    Tendsto (fun n => eLpNorm
      ((fun x => Real.sqrt (x * (1 - x)) * deriv (rs n) x) -
        (fun x => Real.sqrt (x * (1 - x)) * p x)) 2 areaμ) atTop (𝓝 0) ∧
    Tendsto (fun n => eLpNorm
      ((fun x => x * (1 - x) * Real.sqrt (x * (1 - x)) * deriv (deriv (rs n)) x) -
        (fun x => x * (1 - x) * Real.sqrt (x * (1 - x)) * z x)) 2 areaμ) atTop (𝓝 0)

/-- Every original normalized smooth competitor embeds with its actual two
derivatives, by the constant approximation sequence. -/
theorem IsSmoothAreaCompetitor.recoverable {C : ℝ} {K r : ℝ → ℝ}
    (h : IsSmoothAreaCompetitor C K r) :
    IsRecoverableAreaCompetitor C K r (deriv r) (deriv (deriv r)) := by
  have hOriginal := h
  obtain ⟨hK, hr, ⟨κ, Λ, hκ, hbox, hratio⟩, hzero, hone, hmass⟩ := h
  refine ⟨hOriginal.memLp_curvature, Analysis.hasParabolicWeakDerivatives_of_contDiff
    (hr.of_le (by simp)), ⟨κ, Λ, hκ, ?_, hratio⟩, hzero, hone, hmass,
    fun _ => K, fun _ => r, fun _ => hOriginal, ?_, ?_, ?_, ?_⟩
  · filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
    exact hbox x ⟨hx.1.le, hx.2.le⟩
  all_goals
    simp only [sub_self, eLpNorm_zero]
    exact tendsto_const_nhds

/-- Every recoverable weak competitor has an actual original smooth
unit-mass recovery sequence for the complete action. Genuine integrability
of the limiting action and mass densities is proved at the same time. -/
theorem IsRecoverableAreaCompetitor.exists_action_recovery
    {C : ℝ} {K r p z : ℝ → ℝ} (hC : 1 ≤ C)
    (h : IsRecoverableAreaCompetitor C K r p z) :
    IntegrableOn (fun x => meridionalActionDensity (warp K x) (warpSlope K x)
      (K x) (r x) (p x) (z x)) (Ioo (0 : ℝ) 1) ∧
    IntegrableOn (fun x => warp K x * r x ^ 2) (Ioo (0 : ℝ) 1) ∧
    ∃ Ks rs : ℕ → ℝ → ℝ, (∀ n, IsSmoothAreaCompetitor C (Ks n) (rs n)) ∧
      Tendsto (fun n => meridionalAction (Ks n) (rs n)) atTop
        (𝓝 (weakMeridionalAction K r p z)) := by
  obtain ⟨hK, hgraph, _, hzero, hone, _, Ks, rs, hS, hKS, hRS, hPS, hZS⟩ := h
  have hCpos : 0 < C := zero_lt_one.trans_le hC
  have hKm (n : ℕ) := (hS n).memLp_curvature
  have hCommon (n : ℕ) := (hS n).common_bounds
  have hL1 : Tendsto (fun n => ∫ x, |Ks n x - K x| ∂areaμ) atTop (𝓝 0) := by
    have hc : MemLp (fun _ : ℝ => (1 : ℝ)) 2 areaμ := memLp_const 1
    have hh := Analysis.tendsto_integral_abs_mul_sub_of_tendsto_eLpNorm_two
      (f := Ks) (g := K) (u := fun (_ : ℕ) (_ : ℝ) => (1 : ℝ)) (v := fun _ => 1)
      hKm hK (fun _ => hc) (∫ _x, (1 : ℝ) ^ 2 ∂areaμ) (fun _ => le_rfl) hKS
      (Eventually.of_forall (fun _ => tendsto_const_nhds))
    simpa only [mul_one] using hh
  have hL1I : Tendsto (fun n => ∫ x in (0 : ℝ)..1, |Ks n x - K x|)
      atTop (𝓝 0) := by
    simpa only [intervalIntegral.integral_of_le zero_le_one, integral_Ioc_eq_integral_Ioo]
      using hL1
  have hMeasure := tendstoInMeasure_of_tendsto_eLpNorm (p := (2 : ENNReal)) (by norm_num) hKS
  obtain ⟨ψ, hψ, hKae⟩ := hMeasure.exists_seq_tendsto_ae
  have hKbox : ∀ᵐ x ∂areaμ, 0 ≤ K x ∧ K x ≤ 2 * C := by
    filter_upwards [hKae, ae_restrict_mem measurableSet_Ioo] with x hx hxI
    have hlo : 2 / C ≤ K x := ge_of_tendsto' hx
      (fun n => (hCommon (ψ n) x ⟨hxI.1.le, hxI.2.le⟩).1)
    exact ⟨(by positivity : (0 : ℝ) ≤ 2 / C).trans hlo, le_of_tendsto' hx
      (fun n => (hCommon (ψ n) x ⟨hxI.1.le, hxI.2.le⟩).2)⟩
  have hLimits := action_mass_tendsto_of_strong_area_graph
    (fun n => Ks (ψ n)) (fun n => rs (ψ n)) K r p z (2 / C) (2 * C) (by positivity)
    (fun n => (hS (ψ n)).1.continuous)
    (fun n => (hS (ψ n)).2.1.of_le (by simp)) (fun n => hCommon (ψ n))
    (fun n => (hS (ψ n)).2.2.2.1) (fun n => (hS (ψ n)).2.2.2.2.1)
    (hK.integrable (by norm_num)) hzero hone hKbox hgraph
    (hL1I.comp hψ.tendsto_atTop) hKae (hRS.comp hψ.tendsto_atTop)
    (hPS.comp hψ.tendsto_atTop) (hZS.comp hψ.tendsto_atTop)
  exact ⟨hLimits.1, hLimits.2.1, fun n => Ks (ψ n), fun n => rs (ψ n),
    fun n => hS (ψ n), hLimits.2.2.1⟩

/-- The actual smooth-class infimum is a lower bound for every competitor
in the recoverable weak class; the action limit is derived from topology. -/
theorem IsRecoverableAreaCompetitor.infimum_le_action
    {C : ℝ} {K r p z : ℝ → ℝ} (hC : 1 ≤ C)
    (h : IsRecoverableAreaCompetitor C K r p z) :
    smoothAreaInfimum C ≤ weakMeridionalAction K r p z := by
  obtain ⟨_, _, Ks, rs, hS, hA⟩ := h.exists_action_recovery hC
  exact ge_of_tendsto' hA (fun n => smoothAreaInfimum_le_action C hC (Ks n) (rs n) (hS n))

end RicciFlowSharpEstimate.Geometry.AreaProfile
