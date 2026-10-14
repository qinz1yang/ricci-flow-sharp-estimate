/-
Copyright (c) 2026 Ziyang Qin. All rights reserved.
No license is granted by this file.
Authors: Ziyang Qin
-/
import RicciFlowSharpEstimate.Geometry.BoundedAreaCurvature
import RicciFlowSharpEstimate.Analysis.ParabolicWeakDerivativeAlgebra
import RicciFlowSharpEstimate.Analysis.ParabolicGraphConvergence

/-!
# Raw graph recovery and physical normalization

An original same-cap curvature sequence and strong convergence of the actual
probe graph imply complete-action and physical-mass convergence without any
normalization. Positive limiting mass then permits normalization of a positive
tail, scaling both genuine jets by the same factor. Zero raw probes are allowed.
-/

noncomputable section
namespace RicciFlowSharpEstimate.Geometry.AreaProfile
open Set MeasureTheory Filter Topology
open scoped ContDiff ENNReal
local notation "areaμ" => volume.restrict (Ioo (0 : ℝ) 1)

/-- Raw smooth graph recovery at the original cap gives genuine integrability
and both value limits. Every positive-mass limit has a normalized recoverable
competitor with the same curvature and the actual scaled weak jets. The raw
limit itself need not have mass one or be nonzero. -/
theorem IsBoundedAreaCurvature.raw_graph_recovery
    {C : ℝ} {K r p z : ℝ → ℝ} (hC : 1 ≤ C)
    (hK : IsBoundedAreaCurvature C K)
    (hgraph : Analysis.HasParabolicWeakDerivatives r p z)
    (Ks rs : ℕ → ℝ → ℝ)
    (hKs : ∀ n, IsSmoothAreaCurvature C (Ks n))
    (hrs : ∀ n, ContDiff ℝ ∞ (rs n))
    (hKS : Tendsto (fun n => eLpNorm (Ks n - K) 2 areaμ) atTop (𝓝 0))
    (hKae : ∀ᵐ x ∂areaμ, Tendsto (fun n => Ks n x) atTop (𝓝 (K x)))
    (hRS : Tendsto (fun n => eLpNorm (rs n - r) 2 areaμ) atTop (𝓝 0))
    (hPS : Tendsto (fun n => eLpNorm
      ((fun x => Real.sqrt (x * (1 - x)) * deriv (rs n) x) -
        (fun x => Real.sqrt (x * (1 - x)) * p x)) 2 areaμ) atTop (𝓝 0))
    (hZS : Tendsto (fun n => eLpNorm
      ((fun x => x * (1 - x) * Real.sqrt (x * (1 - x)) * deriv (deriv (rs n)) x) -
        (fun x => x * (1 - x) * Real.sqrt (x * (1 - x)) * z x)) 2 areaμ)
      atTop (𝓝 0)) :
    IntegrableOn (fun x => meridionalActionDensity (warp K x) (warpSlope K x)
      (K x) (r x) (p x) (z x)) (Ioo (0 : ℝ) 1) ∧
    IntegrableOn (fun x => warp K x * r x ^ 2) (Ioo (0 : ℝ) 1) ∧
    Tendsto (fun n => meridionalAction (Ks n) (rs n)) atTop
      (𝓝 (weakMeridionalAction K r p z)) ∧
    Tendsto (fun n => probeMass (Ks n) (rs n)) atTop (𝓝 (probeMass K r)) ∧
    (0 < probeMass K r → IsRecoverableAreaCompetitor C K (normalizedProbe K r)
      (fun x => (1 / Real.sqrt (probeMass K r)) * p x)
      (fun x => (1 / Real.sqrt (probeMass K r)) * z x)) := by
  have hCpos : 0 < C := zero_lt_one.trans_le hC
  have hKmem := hK.memLp_curvature
  have hL1 : Tendsto (fun n => ∫ x, |Ks n x - K x| ∂areaμ) atTop (𝓝 0) := by
    have hc : MemLp (fun _ : ℝ => (1 : ℝ)) 2 areaμ := memLp_const 1
    have hh := Analysis.tendsto_integral_abs_mul_sub_of_tendsto_eLpNorm_two
      (f := Ks) (g := K) (u := fun (_ : ℕ) (_ : ℝ) => (1 : ℝ)) (v := fun _ => 1)
      (fun n => (hKs n).memLp_curvature) hKmem (fun _ => hc)
      (∫ _x, (1 : ℝ) ^ 2 ∂areaμ) (fun _ => le_rfl) hKS
      (Eventually.of_forall (fun _ => tendsto_const_nhds))
    simpa only [mul_one] using hh
  have hL1I : Tendsto (fun n => ∫ x in (0 : ℝ)..1, |Ks n x - K x|)
      atTop (𝓝 0) := by
    simpa only [intervalIntegral.integral_of_le zero_le_one, integral_Ioc_eq_integral_Ioo]
      using hL1
  have hKbox : ∀ᵐ x ∂areaμ, 0 ≤ K x ∧ K x ≤ 2 * C := by
    filter_upwards [hKae, ae_restrict_mem measurableSet_Ioo] with x hx hxI
    have hlo : 2 / C ≤ K x := ge_of_tendsto' hx
      (fun n => ((hKs n).common_bounds x ⟨hxI.1.le, hxI.2.le⟩).1)
    exact ⟨(by positivity : (0 : ℝ) ≤ 2 / C).trans hlo, le_of_tendsto' hx
      (fun n => ((hKs n).common_bounds x ⟨hxI.1.le, hxI.2.le⟩).2)⟩
  have hLimits := action_mass_tendsto_of_strong_area_graph Ks rs K r p z
    (2 / C) (2 * C) (by positivity) (fun n => (hKs n).1.continuous)
    (fun n => (hrs n).of_le (by simp)) (fun n => (hKs n).common_bounds)
    (fun n => (hKs n).2.2.1) (fun n => (hKs n).2.2.2)
    (hKmem.integrable (by norm_num)) hK.2.2.1 hK.2.2.2 hKbox hgraph
    hL1I hKae hRS hPS hZS
  refine ⟨hLimits.1, hLimits.2.1, hLimits.2.2.1, hLimits.2.2.2, ?_⟩
  intro hm
  have hMassLimit := hLimits.2.2.2
  have hpos : ∀ᶠ n in atTop, 0 < probeMass (Ks n) (rs n) :=
    hMassLimit.eventually (lt_mem_nhds hm)
  obtain ⟨N, hN⟩ := eventually_atTop.1 hpos
  have hmN (n : ℕ) : 0 < probeMass (Ks (n + N)) (rs (n + N)) :=
    hN (n + N) (Nat.le_add_left N n)
  let β : ℝ := 1 / Real.sqrt (probeMass K r)
  let α : ℕ → ℝ := fun n => 1 / Real.sqrt (probeMass (Ks (n + N)) (rs (n + N)))
  have hα : Tendsto α atTop (𝓝 β) := by
    have hshift := hMassLimit.comp (tendsto_add_atTop_nat N)
    have hh := (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1)).div
      hshift.sqrt (Real.sqrt_pos.mpr hm).ne'
    simpa only [α, β, Function.comp_def, Pi.div_def] using hh
  have hNormGraph := Analysis.parabolicGraph_tendsto_const_mul
    (fun n => (hrs (n + N)).of_le (by simp)) hgraph hα
    (hRS.comp (tendsto_add_atTop_nat N))
    (hPS.comp (tendsto_add_atTop_nat N))
    (hZS.comp (tendsto_add_atTop_nat N))
  refine ⟨hKmem, hgraph.const_mul β, hK.2.1, hK.2.2.1, hK.2.2.2,
    probeMass_normalizedProbe K r hm, fun n => Ks (n + N),
    fun n => normalizedProbe (Ks (n + N)) (rs (n + N)), ?_,
    hKS.comp (tendsto_add_atTop_nat N), hNormGraph.1, hNormGraph.2.1, hNormGraph.2.2⟩
  intro n
  exact (hKs (n + N)).with_unit_probe _ (contDiff_const.mul (hrs (n + N)))
    (probeMass_normalizedProbe _ _ (hmN n))

end RicciFlowSharpEstimate.Geometry.AreaProfile
