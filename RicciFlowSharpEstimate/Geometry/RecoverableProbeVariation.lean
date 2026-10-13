/-
Copyright (c) 2026 Ziyang Qin. All rights reserved.
No license is granted by this file.
Authors: Ziyang Qin
-/
import RicciFlowSharpEstimate.Geometry.RecoverableAreaGeometry
import RicciFlowSharpEstimate.Analysis.ParabolicWeakDerivativeAlgebra
import RicciFlowSharpEstimate.Analysis.ParabolicGraphConvergence

/-!
# Feasible normalized probe variations in the recoverable weak class

A smooth perturbation is applied to each original smooth recovery probe.
The actual weak derivatives and all weighted graph limits follow the same
affine perturbation. Positive limiting mass yields a late positive tail;
its literal normalization preserves the graph and exact unit mass.
-/

noncomputable section
namespace RicciFlowSharpEstimate.Geometry.AreaProfile
open Set MeasureTheory Filter Topology
open scoped ContDiff ENNReal
local notation "areaμ" => volume.restrict (Ioo (0 : ℝ) 1)

/-- Every smooth probe direction gives a feasible normalized weak competitor
whenever its actual perturbed physical mass is positive. Curvature, its
moments and its original ratio witnesses remain the same. No pole trace or
compact-support condition is imposed on the direction. -/
theorem IsRecoverableAreaCompetitor.normalized_probe_add_mul
    {C : ℝ} {K r p z : ℝ → ℝ} (hC : 1 ≤ C)
    (h : IsRecoverableAreaCompetitor C K r p z)
    (s : ℝ → ℝ) (hs : ContDiff ℝ ∞ s) (t : ℝ)
    (hm : 0 < probeMass K (fun x => r x + t * s x)) :
    IsRecoverableAreaCompetitor C K
      (normalizedProbe K (fun x => r x + t * s x))
      (fun x => (1 / Real.sqrt (probeMass K (fun y => r y + t * s y))) *
        (p x + t * deriv s x))
      (fun x => (1 / Real.sqrt (probeMass K (fun y => r y + t * s y))) *
        (z x + t * deriv (deriv s) x)) := by
  have hCpos : 0 < C := zero_lt_one.trans_le hC
  have hKmem : MemLp K 2 areaμ := h.1
  have hgraph := h.2.1
  have hgraphS := Analysis.hasParabolicWeakDerivatives_of_contDiff (hs.of_le (by simp))
  let u : ℝ → ℝ := fun x => r x + t * s x
  let q : ℝ → ℝ := fun x => p x + t * deriv s x
  let v : ℝ → ℝ := fun x => z x + t * deriv (deriv s) x
  let β : ℝ := 1 / Real.sqrt (probeMass K u)
  have hgraphU : Analysis.HasParabolicWeakDerivatives u q v :=
    hgraph.add (hgraphS.const_mul t)
  obtain ⟨Ks, rs, hS, hKS, hRS, hPS, hZS, hKae⟩ := h.strong_curvature_subsequence
  let un : ℕ → ℝ → ℝ := fun n x => rs n x + t * s x
  have hun (n : ℕ) : ContDiff ℝ ∞ (un n) :=
    (hS n).2.1.add (contDiff_const.mul hs)
  have hStrongU := Analysis.parabolicGraph_tendsto_add_fixed_smooth
    (fun n => (hS n).2.1.of_le (by simp)) ⟨hRS, hPS, hZS⟩ s (hs.of_le (by simp)) t
  have hL1 : Tendsto (fun n => ∫ x, |Ks n x - K x| ∂areaμ) atTop (𝓝 0) := by
    have hc : MemLp (fun _ : ℝ => (1 : ℝ)) 2 areaμ := memLp_const 1
    have hh := Analysis.tendsto_integral_abs_mul_sub_of_tendsto_eLpNorm_two
      (f := Ks) (g := K) (u := fun (_ : ℕ) (_ : ℝ) => (1 : ℝ)) (v := fun _ => 1)
      (fun n => (hS n).memLp_curvature) hKmem (fun _ => hc)
      (∫ _x, (1 : ℝ) ^ 2 ∂areaμ) (fun _ => le_rfl) hKS
      (Eventually.of_forall (fun _ => tendsto_const_nhds))
    simpa only [mul_one] using hh
  have hL1I : Tendsto (fun n => ∫ x in (0 : ℝ)..1, |Ks n x - K x|)
      atTop (𝓝 0) := by
    simpa only [intervalIntegral.integral_of_le zero_le_one, integral_Ioc_eq_integral_Ioo]
      using hL1
  have hGeo := h.geometry_bounds hC
  have hKbox : ∀ᵐ x ∂areaμ, 0 ≤ K x ∧ K x ≤ 2 * C := by
    filter_upwards [hGeo.2.2.2.2] with x hx
    exact ⟨(by positivity : (0 : ℝ) ≤ 2 / C).trans hx.1, hx.2⟩
  have hLimits := action_mass_tendsto_of_strong_area_graph Ks un K u q v
    (2 / C) (2 * C) (by positivity) (fun n => (hS n).1.continuous)
    (fun n => (hun n).of_le (by simp)) (fun n => (hS n).common_bounds)
    (fun n => (hS n).2.2.2.1) (fun n => (hS n).2.2.2.2.1)
    (hKmem.integrable (by norm_num)) h.2.2.2.1 h.2.2.2.2.1 hKbox hgraphU
    hL1I hKae hStrongU.1 hStrongU.2.1 hStrongU.2.2
  have hMassLimit : Tendsto (fun n => probeMass (Ks n) (un n)) atTop
      (𝓝 (probeMass K u)) := hLimits.2.2.2
  have hpos : ∀ᶠ n in atTop, 0 < probeMass (Ks n) (un n) :=
    hMassLimit.eventually (lt_mem_nhds hm)
  obtain ⟨N, hN⟩ := eventually_atTop.1 hpos
  have hmN (n : ℕ) : 0 < probeMass (Ks (n + N)) (un (n + N)) :=
    hN (n + N) (Nat.le_add_left N n)
  let α : ℕ → ℝ := fun n => 1 / Real.sqrt (probeMass (Ks (n + N)) (un (n + N)))
  have hα : Tendsto α atTop (𝓝 β) := by
    have hshift := hMassLimit.comp (tendsto_add_atTop_nat N)
    have hh := (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1)).div
      hshift.sqrt (Real.sqrt_pos.mpr hm).ne'
    simpa only [α, β, Function.comp_def, Pi.div_def] using hh
  have hNormGraph := Analysis.parabolicGraph_tendsto_const_mul
    (fun n => (hun (n + N)).of_le (by simp)) hgraphU hα
    (hStrongU.1.comp (tendsto_add_atTop_nat N))
    (hStrongU.2.1.comp (tendsto_add_atTop_nat N))
    (hStrongU.2.2.comp (tendsto_add_atTop_nat N))
  refine ⟨hKmem, hgraphU.const_mul β, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1,
    probeMass_normalizedProbe K u hm, fun n => Ks (n + N),
    fun n => normalizedProbe (Ks (n + N)) (un (n + N)), ?_,
    hKS.comp (tendsto_add_atTop_nat N), hNormGraph.1, hNormGraph.2.1, hNormGraph.2.2⟩
  intro n
  exact ⟨(hS (n + N)).1, contDiff_const.mul (hun (n + N)), (hS (n + N)).2.2.1,
    (hS (n + N)).2.2.2.1, (hS (n + N)).2.2.2.2.1,
    probeMass_normalizedProbe _ _ (hmN n)⟩

end RicciFlowSharpEstimate.Geometry.AreaProfile
