/-
Copyright (c) 2026 Ziyang Qin. All rights reserved.
No license is granted by this file.
Authors: Ziyang Qin
-/
import RicciFlowSharpEstimate.Geometry.AreaSmoothConvexity
import RicciFlowSharpEstimate.Analysis.L2ConvexApproximation
import RicciFlowSharpEstimate.Analysis.ParabolicSobolev
import Mathlib.Tactic.FinCases

/-!
# Smooth convex recovery in the actual weighted area graph

One family of convex mixtures simultaneously approximates the curvature,
probe, and both weighted actual probe derivatives. Smoothness, exact
curvature moments and the original ratio are preserved before the separate
nonlinear physical mass normalization. The limit probe jets remain tied
by the genuine weak derivative graph.
-/

noncomputable section

namespace RicciFlowSharpEstimate.Geometry.AreaProfile

open Set MeasureTheory Filter Topology
open scoped ContDiff BigOperators

local notation "areaμ" => volume.restrict (Ioo (0 : ℝ) 1)

/-- Weak convergence of the actual four area graph coordinates yields
simultaneous smooth convex recovery, with exact moments and ratio. No
symmetry, monotonicity or pole value condition is imposed. -/
theorem exists_smooth_convex_recovery_of_weak_graph_pairings
    (K r : ℕ → ℝ → ℝ) (κ Λ : ℕ → ℝ) (C : ℝ) (K0 r0 p0 z0 : ℝ → ℝ)
    (hK : ∀ n, ContDiff ℝ ∞ (K n)) (hr : ∀ n, ContDiff ℝ ∞ (r n))
    (hκ : ∀ n, 0 < κ n)
    (hbox : ∀ n x, x ∈ Icc (0 : ℝ) 1 → κ n ≤ K n x ∧ K n x ≤ Λ n)
    (hratio : ∀ n, Λ n / κ n ≤ C)
    (hzero : ∀ n, (∫ x in (0 : ℝ)..1, K n x) = 2)
    (hone : ∀ n, (∫ x in (0 : ℝ)..1, x * K n x) = 1)
    (hK0 : MemLp K0 2 areaμ) (hgraph : Analysis.HasParabolicWeakDerivatives r0 p0 z0)
    (hKW : ∀ v : Lp ℝ 2 areaμ,
      Tendsto (fun n => ∫ x, K n x * v x ∂areaμ) atTop (𝓝 (∫ x, K0 x * v x ∂areaμ)))
    (hRW : ∀ v : Lp ℝ 2 areaμ,
      Tendsto (fun n => ∫ x, r n x * v x ∂areaμ) atTop (𝓝 (∫ x, r0 x * v x ∂areaμ)))
    (hPW : ∀ v : Lp ℝ 2 areaμ,
      Tendsto (fun n => ∫ x, (Real.sqrt (x * (1 - x)) * deriv (r n) x) * v x ∂areaμ)
        atTop (𝓝 (∫ x, (Real.sqrt (x * (1 - x)) * p0 x) * v x ∂areaμ)))
    (hZW : ∀ v : Lp ℝ 2 areaμ,
      Tendsto (fun n => ∫ x,
        (x * (1 - x) * Real.sqrt (x * (1 - x)) * deriv (deriv (r n)) x) * v x ∂areaμ)
        atTop (𝓝 (∫ x,
          (x * (1 - x) * Real.sqrt (x * (1 - x)) * z0 x) * v x ∂areaμ))) :
    ∃ (s : ℕ → Finset ℕ) (w : ℕ → ℕ → ℝ),
      (∀ n i, 0 ≤ w n i) ∧
      (∀ n i, i ∉ s n → w n i = 0) ∧
      (∀ n, ∀ i ∈ s n, n ≤ i) ∧
      (∀ n, (∑ i ∈ s n, w n i) = 1) ∧
      let Km : ℕ → ℝ → ℝ := fun n x => ∑ i ∈ s n, w n i * K i x
      let rm : ℕ → ℝ → ℝ := fun n x => ∑ i ∈ s n, w n i * r i x
      let κm : ℕ → ℝ := fun n => ∑ i ∈ s n, w n i * κ i
      let Λm : ℕ → ℝ := fun n => ∑ i ∈ s n, w n i * Λ i
      (∀ n, ContDiff ℝ ∞ (Km n) ∧ ContDiff ℝ ∞ (rm n) ∧ 0 < κm n ∧
        (∀ x ∈ Icc (0 : ℝ) 1, κm n ≤ Km n x ∧ Km n x ≤ Λm n) ∧
        Λm n / κm n ≤ C ∧ (∫ x in (0 : ℝ)..1, Km n x) = 2 ∧
        (∫ x in (0 : ℝ)..1, x * Km n x) = 1) ∧
      Tendsto (fun n => eLpNorm (Km n - K0) 2 areaμ) atTop (𝓝 0) ∧
      Tendsto (fun n => eLpNorm (rm n - r0) 2 areaμ) atTop (𝓝 0) ∧
      Tendsto (fun n => eLpNorm (fun x => Real.sqrt (x * (1 - x)) *
        deriv (rm n) x - Real.sqrt (x * (1 - x)) * p0 x) 2 areaμ) atTop (𝓝 0) ∧
      Tendsto (fun n => eLpNorm (fun x => x * (1 - x) * Real.sqrt (x * (1 - x)) *
        deriv (deriv (rm n)) x - x * (1 - x) * Real.sqrt (x * (1 - x)) * z0 x) 2 areaμ)
        atTop (𝓝 0) := by
  have hKm (n : ℕ) : MemLp (K n) 2 areaμ := by
    apply MemLp.of_bound (hK n).continuous.aestronglyMeasurable (Λ n)
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
    have hb := hbox n x ⟨hx.1.le, hx.2.le⟩
    simpa only [Real.norm_eq_abs, abs_of_nonneg ((hκ n).le.trans hb.1)] using hb.2
  have hGN (n : ℕ) := Analysis.hasParabolicWeakDerivatives_of_contDiff
    ((hr n).of_le (show (2 : ℕ∞) ≤ ∞ by simp))
  let U : ℕ → Fin 4 → ℝ → ℝ := fun n => ![K n, r n,
    fun x => Real.sqrt (x * (1 - x)) * deriv (r n) x,
    fun x => x * (1 - x) * Real.sqrt (x * (1 - x)) * deriv (deriv (r n)) x]
  let V : Fin 4 → ℝ → ℝ := ![K0, r0,
    fun x => Real.sqrt (x * (1 - x)) * p0 x,
    fun x => x * (1 - x) * Real.sqrt (x * (1 - x)) * z0 x]
  have hUm : ∀ n j, MemLp (U n j) 2 areaμ := by
    intro n j
    fin_cases j
    · exact hKm n
    · exact (hGN n).memLp
    · exact (hGN n).memLp_weighted_deriv
    · exact (hGN n).memLp_weighted_secondDeriv
  have hVm : ∀ j, MemLp (V j) 2 areaμ := by
    intro j
    fin_cases j
    · exact hK0
    · exact hgraph.memLp
    · exact hgraph.memLp_weighted_deriv
    · exact hgraph.memLp_weighted_secondDeriv
  have hUW : ∀ j, ∀ v : Lp ℝ 2 areaμ,
      Tendsto (fun n => ∫ x, U n j x * v x ∂areaμ) atTop
        (𝓝 (∫ x, V j x * v x ∂areaμ)) := by
    intro j v
    fin_cases j
    · exact hKW v
    · exact hRW v
    · exact hPW v
    · exact hZW v
  obtain ⟨s, w, hw, hoff, htail, hsum, _, hstrong⟩ :=
    Analysis.exists_tail_convexCombination_tendsto_eLpNorm_two U V hUm hVm hUW
  have hmix (n : ℕ) := smooth_area_pair_convexCombination (s n) (w n) K r κ Λ C
    (fun i _ => hw n i) (hsum n) (fun i _ => hK i) (fun i _ => hr i)
    (fun i _ => hκ i) (fun i _ => hbox i) (fun i _ => hratio i)
    (fun i _ => hzero i) (fun i _ => hone i)
  refine ⟨s, w, hw, hoff, htail, hsum, ?_, ?_, ?_, ?_, ?_⟩
  · intro n
    obtain ⟨hkm, hrm, _, _, hκm, hbm, hratm, hzm, hom⟩ := hmix n
    exact ⟨hkm, hrm, hκm, hbm, hratm, hzm, hom⟩
  · exact hstrong 0
  · exact hstrong 1
  · have heq (n : ℕ) :
        (fun x => Real.sqrt (x * (1 - x)) * deriv (fun y => ∑ i ∈ s n, w n i * r i y) x -
          Real.sqrt (x * (1 - x)) * p0 x) =
        (fun x => (∑ i ∈ s n, w n i * U i 2 x) - V 2 x) := by
      funext x
      rw [(hmix n).2.2.1]
      change Real.sqrt (x * (1 - x)) * (∑ i ∈ s n, w n i * deriv (r i) x) -
        Real.sqrt (x * (1 - x)) * p0 x =
        (∑ i ∈ s n, w n i * (Real.sqrt (x * (1 - x)) * deriv (r i) x)) -
          Real.sqrt (x * (1 - x)) * p0 x
      rw [Finset.mul_sum]
      congr 1
      apply Finset.sum_congr rfl
      intro i _
      ring
    simpa only [← heq] using hstrong 2
  · have heq (n : ℕ) :
        (fun x => x * (1 - x) * Real.sqrt (x * (1 - x)) *
          deriv (deriv (fun y => ∑ i ∈ s n, w n i * r i y)) x -
          x * (1 - x) * Real.sqrt (x * (1 - x)) * z0 x) =
        (fun x => (∑ i ∈ s n, w n i * U i 3 x) - V 3 x) := by
      funext x
      rw [(hmix n).2.2.2.1]
      change (x * (1 - x) * Real.sqrt (x * (1 - x))) *
        (∑ i ∈ s n, w n i * deriv (deriv (r i)) x) -
        (x * (1 - x) * Real.sqrt (x * (1 - x))) * z0 x =
        (∑ i ∈ s n, w n i * ((x * (1 - x) * Real.sqrt (x * (1 - x))) *
          deriv (deriv (r i)) x)) - (x * (1 - x) * Real.sqrt (x * (1 - x))) * z0 x
      rw [Finset.mul_sum]
      congr 1
      apply Finset.sum_congr rfl
      intro i _
      ring
    simpa only [← heq] using hstrong 3

end RicciFlowSharpEstimate.Geometry.AreaProfile
