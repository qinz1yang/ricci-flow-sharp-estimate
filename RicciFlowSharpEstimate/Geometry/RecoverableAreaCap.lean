/-
Copyright (c) 2026 Ziyang Qin. All rights reserved.
No license is granted by this file.
Authors: Ziyang Qin
-/
import RicciFlowSharpEstimate.Geometry.BoundedAreaCurvature
import RicciFlowSharpEstimate.Analysis.ParabolicGraphConvergence

/-!
# Curvature-cap transport for recoverable area competitors

Recoverability at any original cap transfers to every cap satisfied by the
same limiting curvature. Smooth curvature recovery in the new positive box
is paired with the existing probe recovery. The resulting masses tend to
one, so literal normalization of a positive tail preserves all four strong
limits to the original curvature and weak probe graph.
-/

noncomputable section

namespace RicciFlowSharpEstimate.Geometry.AreaProfile

open Set MeasureTheory Filter Topology
open scoped ContDiff ENNReal

local notation "areaμ" => volume.restrict (Ioo (0 : ℝ) 1)

/-- A recoverable area competitor remains recoverable at every curvature cap
satisfied by its same limiting curvature. The probe and both weak derivatives
are unchanged, and the new recovery sequence has all four strong limits to
these original objects. No order relation between the two caps is required. -/
theorem IsRecoverableAreaCompetitor.of_curvature_cap
    {C₀ C : ℝ} {K r p z : ℝ → ℝ}
    (h : IsRecoverableAreaCompetitor C₀ K r p z)
    (hKC : IsBoundedAreaCurvature C K) :
    IsRecoverableAreaCompetitor C K r p z := by
  obtain ⟨hK, hgraph, _, hzero, hone, hmass, _, rs, hS, _, hRS, hPS, hZS⟩ := h
  obtain ⟨κ, Λ, Js, hκ, hbox, hratio, hJ, hJbox, hJS⟩ := hKC.exists_smooth_recovery
  have hL1 : Tendsto (fun n => ∫ x, |Js n x - K x| ∂areaμ) atTop (𝓝 0) := by
    have hc : MemLp (fun _ : ℝ => (1 : ℝ)) 2 areaμ := memLp_const 1
    have hh := Analysis.tendsto_integral_abs_mul_sub_of_tendsto_eLpNorm_two
      (f := Js) (g := K) (u := fun (_ : ℕ) (_ : ℝ) => (1 : ℝ)) (v := fun _ => 1)
      (fun n => (hJ n).memLp_curvature) hK (fun _ => hc)
      (∫ _x, (1 : ℝ) ^ 2 ∂areaμ) (fun _ => le_rfl) hJS
      (Eventually.of_forall (fun _ => tendsto_const_nhds))
    simpa only [mul_one] using hh
  have hL1I : Tendsto (fun n => ∫ x in (0 : ℝ)..1, |Js n x - K x|)
      atTop (𝓝 0) := by
    simpa only [intervalIntegral.integral_of_le zero_le_one, integral_Ioc_eq_integral_Ioo]
      using hL1
  have hMeasure := tendstoInMeasure_of_tendsto_eLpNorm (p := (2 : ENNReal))
    (by norm_num) hJS
  obtain ⟨ψ, hψ, hJae⟩ := hMeasure.exists_seq_tendsto_ae
  have hKbox : ∀ᵐ x ∂areaμ, 0 ≤ K x ∧ K x ≤ Λ := by
    filter_upwards [hbox] with x hx
    exact ⟨hκ.le.trans hx.1, hx.2⟩
  have hLimits := action_mass_tendsto_of_strong_area_graph
    (fun n => Js (ψ n)) (fun n => rs (ψ n)) K r p z κ Λ hκ
    (fun n => (hJ (ψ n)).1.continuous)
    (fun n => (hS (ψ n)).2.1.of_le (by simp))
    (fun n x _ => hJbox (ψ n) x)
    (fun n => (hJ (ψ n)).2.2.1) (fun n => (hJ (ψ n)).2.2.2)
    (hK.integrable (by norm_num)) hzero hone hKbox hgraph
    (hL1I.comp hψ.tendsto_atTop) hJae (hRS.comp hψ.tendsto_atTop)
    (hPS.comp hψ.tendsto_atTop) (hZS.comp hψ.tendsto_atTop)
  have hMass : Tendsto (fun n => probeMass (Js (ψ n)) (rs (ψ n)))
      atTop (𝓝 (1 : ℝ)) := by
    simpa only [hmass] using hLimits.2.2.2
  have hpos : ∀ᶠ n in atTop, 0 < probeMass (Js (ψ n)) (rs (ψ n)) :=
    hMass.eventually (lt_mem_nhds zero_lt_one)
  obtain ⟨N, hN⟩ := eventually_atTop.1 hpos
  have hmN (n : ℕ) : 0 < probeMass (Js (ψ (n + N))) (rs (ψ (n + N))) :=
    hN (n + N) (Nat.le_add_left N n)
  let α : ℕ → ℝ := fun n =>
    1 / Real.sqrt (probeMass (Js (ψ (n + N))) (rs (ψ (n + N))))
  have hα : Tendsto α atTop (𝓝 (1 : ℝ)) := by
    have hshift := hMass.comp (tendsto_add_atTop_nat N)
    have hh := (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1)).div
      hshift.sqrt (by norm_num : Real.sqrt (1 : ℝ) ≠ 0)
    simpa only [α, Function.comp_def, Pi.div_def, Real.sqrt_one, div_one] using hh
  have hNormGraph := Analysis.parabolicGraph_tendsto_const_mul
    (fun n => (hS (ψ (n + N))).2.1.of_le (by simp)) hgraph hα
    ((hRS.comp hψ.tendsto_atTop).comp (tendsto_add_atTop_nat N))
    ((hPS.comp hψ.tendsto_atTop).comp (tendsto_add_atTop_nat N))
    ((hZS.comp hψ.tendsto_atTop).comp (tendsto_add_atTop_nat N))
  refine ⟨hK, hgraph, ⟨κ, Λ, hκ, hbox, hratio⟩, hzero, hone, hmass,
    fun n => Js (ψ (n + N)),
    fun n x => α n * rs (ψ (n + N)) x, ?_,
    (hJS.comp hψ.tendsto_atTop).comp (tendsto_add_atTop_nat N), ?_, ?_, ?_⟩
  · intro n
    exact (hJ (ψ (n + N))).with_unit_probe _
      (contDiff_const.mul (hS (ψ (n + N))).2.1)
      (probeMass_normalizedProbe _ _ (hmN n))
  · simpa only [one_mul] using hNormGraph.1
  · simpa only [one_mul] using hNormGraph.2.1
  · simpa only [one_mul] using hNormGraph.2.2

end RicciFlowSharpEstimate.Geometry.AreaProfile
