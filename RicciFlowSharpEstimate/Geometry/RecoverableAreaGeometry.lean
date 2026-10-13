/-
Copyright (c) 2026 Ziyang Qin. All rights reserved.
No license is granted by this file.
Authors: Ziyang Qin
-/
import RicciFlowSharpEstimate.Geometry.RecoverableAreaCompetitor
import RicciFlowSharpEstimate.Geometry.AreaUniformPrimitives
import RicciFlowSharpEstimate.Analysis.L2StrongMultipliers

/-!
# Geometry of recoverable normalized area competitors

The actual smooth approximation in the recoverable class has a subsequence
whose curvatures converge almost everywhere and whose full strong graph
convergence is preserved. Its common curvature box and weak L² pairings
give continuity, quadratic bounds and the normalized pole values of the
original limiting primitives.
-/

noncomputable section

namespace RicciFlowSharpEstimate.Geometry.AreaProfile

open Set MeasureTheory Filter Topology
open scoped ENNReal

local notation "areaμ" => volume.restrict (Ioo (0 : ℝ) 1)

/-- An original smooth unit-mass approximation can be chosen with
almost-everywhere curvature convergence while retaining all four strong
curvature and parabolic graph limits. -/
theorem IsRecoverableAreaCompetitor.strong_curvature_subsequence
    {C : ℝ} {K r p z : ℝ → ℝ}
    (h : IsRecoverableAreaCompetitor C K r p z) :
    ∃ Ks rs : ℕ → ℝ → ℝ,
      (∀ n, IsSmoothAreaCompetitor C (Ks n) (rs n)) ∧
      Tendsto (fun n => eLpNorm (Ks n - K) 2 areaμ) atTop (𝓝 0) ∧
      Tendsto (fun n => eLpNorm (rs n - r) 2 areaμ) atTop (𝓝 0) ∧
      Tendsto (fun n => eLpNorm
        ((fun x => Real.sqrt (x * (1 - x)) * deriv (rs n) x) -
          (fun x => Real.sqrt (x * (1 - x)) * p x)) 2 areaμ) atTop (𝓝 0) ∧
      Tendsto (fun n => eLpNorm
        ((fun x => x * (1 - x) * Real.sqrt (x * (1 - x)) * deriv (deriv (rs n)) x) -
          (fun x => x * (1 - x) * Real.sqrt (x * (1 - x)) * z x)) 2 areaμ)
        atTop (𝓝 0) ∧
      (∀ᵐ x ∂areaμ, Tendsto (fun n => Ks n x) atTop (𝓝 (K x))) := by
  obtain ⟨_, _, _, _, _, _, Ks, rs, hS, hKS, hRS, hPS, hZS⟩ := h
  have hMeasure := tendstoInMeasure_of_tendsto_eLpNorm
    (p := (2 : ENNReal)) (by norm_num) hKS
  obtain ⟨ψ, hψ, hKae⟩ := hMeasure.exists_seq_tendsto_ae
  exact ⟨fun n => Ks (ψ n), fun n => rs (ψ n), fun n => hS (ψ n),
    hKS.comp hψ.tendsto_atTop, hRS.comp hψ.tendsto_atTop,
    hPS.comp hψ.tendsto_atTop, hZS.comp hψ.tendsto_atTop, hKae⟩

/-- The actual primitives of every recoverable competitor retain the
closed-interval geometry of the original smooth class, and the actual
limiting curvature retains its common normalized box almost everywhere. -/
theorem IsRecoverableAreaCompetitor.geometry_bounds
    {C : ℝ} {K r p z : ℝ → ℝ} (hC : 1 ≤ C)
    (h : IsRecoverableAreaCompetitor C K r p z) :
    ContinuousOn (warp K) (Icc (0 : ℝ) 1) ∧
    ContinuousOn (warpSlope K) (Icc (0 : ℝ) 1) ∧
    (∀ x ∈ Icc (0 : ℝ) 1,
      (2 / C) * x * (1 - x) ≤ warp K x ∧
      warp K x ≤ (2 * C) * x * (1 - x) ∧ |warpSlope K x| ≤ 2) ∧
    (warp K 0 = 0 ∧ warp K 1 = 0 ∧ warpSlope K 0 = 2 ∧ warpSlope K 1 = -2) ∧
    (∀ᵐ x ∂areaμ, 2 / C ≤ K x ∧ K x ≤ 2 * C) := by
  have hK : MemLp K 2 areaμ := h.1
  obtain ⟨Ks, rs, hS, hKS, _, _, _, hKae⟩ := h.strong_curvature_subsequence
  have hCpos : 0 < C := zero_lt_one.trans_le hC
  have hlo : 0 < 2 / C := by positivity
  have hcont (n : ℕ) : Continuous (Ks n) := (hS n).1.continuous
  have hbox (n : ℕ) :
      ∀ x ∈ Icc (0 : ℝ) 1, 2 / C ≤ Ks n x ∧ Ks n x ≤ 2 * C :=
    (hS n).common_bounds
  have hzero (n : ℕ) : (∫ x in (0 : ℝ)..1, Ks n x) = 2 :=
    (hS n).2.2.2.1
  have hone (n : ℕ) : (∫ x in (0 : ℝ)..1, x * Ks n x) = 1 :=
    (hS n).2.2.2.2.1
  have hweak : ∀ v : Lp ℝ 2 areaμ,
      Tendsto (fun n => ∫ x, Ks n x * v x ∂areaμ) atTop
        (𝓝 (∫ x, K x * v x ∂areaμ)) := by
    intro v
    have hvstrong : Tendsto
        (fun (_ : ℕ) => eLpNorm ((v : ℝ → ℝ) - (v : ℝ → ℝ)) 2 areaμ)
        atTop (𝓝 0) := by
      simp only [sub_self, eLpNorm_zero]
      exact tendsto_const_nhds
    exact (Analysis.tendsto_integral_mul_of_tendsto_eLpNorm_two
      (u := Ks) (u0 := K) (v := fun _ => (v : ℝ → ℝ)) (v0 := (v : ℝ → ℝ))
      (fun n => (hS n).memLp_curvature) hK
      (fun _ => Lp.memLp v) (Lp.memLp v) hKS hvstrong).2.2
  refine ⟨continuousOn_warp_of_weak_L2
      Ks K hcont (2 / C) (2 * C) hlo hbox hK hweak hzero,
    continuousOn_warpSlope_of_weak_L2
      Ks K hcont (2 / C) (2 * C) hlo hbox hK hweak, ?_,
    warp_endpoints_of_weak_L2
      Ks K hcont (2 / C) (2 * C) hlo hbox hK hweak hzero hone, ?_⟩
  · intro x hx
    have hb := warp_bounds_of_weak_L2
      Ks K hcont (2 / C) (2 * C) hlo hbox hK hweak hzero hone x hx
    exact ⟨hb.1, hb.2, abs_warpSlope_le_two_of_weak_L2
      Ks K hcont (2 / C) (2 * C) hlo hbox hK hweak hzero x hx⟩
  · filter_upwards [hKae, ae_restrict_mem measurableSet_Ioo] with x hx hxI
    exact ⟨ge_of_tendsto' hx (fun n => (hbox n x ⟨hxI.1.le, hxI.2.le⟩).1),
      le_of_tendsto' hx (fun n => (hbox n x ⟨hxI.1.le, hxI.2.le⟩).2)⟩

end RicciFlowSharpEstimate.Geometry.AreaProfile
