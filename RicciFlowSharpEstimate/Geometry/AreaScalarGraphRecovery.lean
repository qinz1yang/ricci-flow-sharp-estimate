/-
Copyright (c) 2026 Ziyang Qin. All rights reserved.
No license is granted by this file.
Authors: Ziyang Qin
-/
import RicciFlowSharpEstimate.Geometry.AreaConvexGraphRecovery
import RicciFlowSharpEstimate.Geometry.AreaStrongGraphContinuity
import RicciFlowSharpEstimate.Analysis.L2PointwiseProducts
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure

/-!
# Complete scalar recovery of weak limits of smooth area pairs

The weak graph pairings produce actual smooth convex mixtures. One further
curvature subsequence gives almost-everywhere convergence; strong graph
continuity then supplies the complete action and physical mass limits.
The original ratio and both moments remain exact throughout recovery.
-/

noncomputable section

namespace RicciFlowSharpEstimate.Geometry.AreaProfile

open Set MeasureTheory Filter Topology
open scoped ContDiff BigOperators ENNReal

local notation "areaμ" => volume.restrict (Ioo (0 : ℝ) 1)

/-- A unit-mass weak graph limit of original smooth pairs has genuinely
constructed smooth scalar approximants with the same ratio cap, exact
moments, strong graph convergence, and full action and mass convergence.
This concerns limits of the displayed smooth sequence, not density for
arbitrary members of the maximal weak derivative graph. -/
theorem exists_smooth_scalar_recovery_of_weak_graph_pairings
    (K r : ℕ → ℝ → ℝ) (κ Λ : ℕ → ℝ) (C : ℝ) (K0 r0 p0 z0 : ℝ → ℝ)
    (hC : 1 ≤ C) (hK : ∀ n, ContDiff ℝ ∞ (K n)) (hr : ∀ n, ContDiff ℝ ∞ (r n))
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
          (x * (1 - x) * Real.sqrt (x * (1 - x)) * z0 x) * v x ∂areaμ)))
    (hzero0 : (∫ x in (0 : ℝ)..1, K0 x) = 2)
    (hone0 : (∫ x in (0 : ℝ)..1, x * K0 x) = 1)
    (hmass0 : probeMass K0 r0 = 1) :
    ∃ (Ks rs : ℕ → ℝ → ℝ) (κs Λs : ℕ → ℝ),
      (∀ n, ContDiff ℝ ∞ (Ks n) ∧ ContDiff ℝ ∞ (rs n) ∧ 0 < κs n ∧
        (∀ x ∈ Icc (0 : ℝ) 1, κs n ≤ Ks n x ∧ Ks n x ≤ Λs n) ∧
        Λs n / κs n ≤ C ∧ (∫ x in (0 : ℝ)..1, Ks n x) = 2 ∧
        (∫ x in (0 : ℝ)..1, x * Ks n x) = 1) ∧
      Tendsto (fun n => eLpNorm (Ks n - K0) 2 areaμ) atTop (𝓝 0) ∧
      (∀ᵐ x ∂areaμ, Tendsto (fun n => Ks n x) atTop (𝓝 (K0 x))) ∧
      Tendsto (fun n => eLpNorm (rs n - r0) 2 areaμ) atTop (𝓝 0) ∧
      Tendsto (fun n => eLpNorm ((fun x => Real.sqrt (x * (1 - x)) * deriv (rs n) x) -
        (fun x => Real.sqrt (x * (1 - x)) * p0 x)) 2 areaμ) atTop (𝓝 0) ∧
      Tendsto (fun n => eLpNorm
        ((fun x => x * (1 - x) * Real.sqrt (x * (1 - x)) * deriv (deriv (rs n)) x) -
          (fun x => x * (1 - x) * Real.sqrt (x * (1 - x)) * z0 x)) 2 areaμ)
        atTop (𝓝 0) ∧
      Tendsto (fun n => probeMass (Ks n) (rs n)) atTop (𝓝 1) ∧
      Tendsto (fun n => meridionalAction (Ks n) (rs n)) atTop
        (𝓝 (weakMeridionalAction K0 r0 p0 z0)) := by
  have hCpos : 0 < C := zero_lt_one.trans_le hC
  obtain ⟨s, w, _, _, _, _, hSmooth, hKS, hRS, hPS, hZS⟩ :=
    exists_smooth_convex_recovery_of_weak_graph_pairings K r κ Λ C K0 r0 p0 z0
      hK hr hκ hbox hratio hzero hone hK0 hgraph hKW hRW hPW hZW
  let Km : ℕ → ℝ → ℝ := fun n x => ∑ i ∈ s n, w n i * K i x
  let rm : ℕ → ℝ → ℝ := fun n x => ∑ i ∈ s n, w n i * r i x
  let κm : ℕ → ℝ := fun n => ∑ i ∈ s n, w n i * κ i
  let Λm : ℕ → ℝ := fun n => ∑ i ∈ s n, w n i * Λ i
  have hCommon (n : ℕ) : ∀ x ∈ Icc (0 : ℝ) 1,
      2 / C ≤ Km n x ∧ Km n x ≤ 2 * C :=
    curvature_bounds_of_ratio (Km n) (hSmooth n).1.continuous (κm n) (Λm n) C
      (hSmooth n).2.2.1 (hSmooth n).2.2.2.1 (hSmooth n).2.2.2.2.1
      (hSmooth n).2.2.2.2.2.1
  have hKm (n : ℕ) : MemLp (Km n) 2 areaμ := by
    apply MemLp.of_bound (hSmooth n).1.continuous.aestronglyMeasurable (2 * C)
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
    have h := hCommon n x ⟨hx.1.le, hx.2.le⟩
    change ‖Km n x‖ ≤ 2 * C
    rw [Real.norm_eq_abs, abs_of_nonneg
      ((by positivity : (0 : ℝ) ≤ 2 / C).trans h.1)]
    exact h.2
  have hL1 : Tendsto (fun n => ∫ x, |Km n x - K0 x| ∂areaμ) atTop (𝓝 0) := by
    have hc : MemLp (fun _ : ℝ => (1 : ℝ)) 2 areaμ := memLp_const 1
    have h := Analysis.tendsto_integral_abs_mul_sub_of_tendsto_eLpNorm_two
      (f := Km) (g := K0) (u := fun (_ : ℕ) (_ : ℝ) => (1 : ℝ)) (v := fun _ => 1)
      hKm hK0 (fun _ => hc) (∫ _x, (1 : ℝ) ^ 2 ∂areaμ) (fun _ => le_rfl) hKS
      (Eventually.of_forall (fun _ => tendsto_const_nhds))
    simpa only [mul_one] using h
  have hL1I : Tendsto (fun n => ∫ x in (0 : ℝ)..1, |Km n x - K0 x|) atTop (𝓝 0) := by
    simpa only [intervalIntegral.integral_of_le zero_le_one, integral_Ioc_eq_integral_Ioo]
      using hL1
  have hMeasure := tendstoInMeasure_of_tendsto_eLpNorm (p := (2 : ENNReal)) (by norm_num) hKS
  obtain ⟨ψ, hψ, hKae⟩ := hMeasure.exists_seq_tendsto_ae
  have hK0box : ∀ᵐ x ∂areaμ, 0 ≤ K0 x ∧ K0 x ≤ 2 * C := by
    filter_upwards [hKae, ae_restrict_mem measurableSet_Ioo] with x hx hxI
    have hl : 2 / C ≤ K0 x := ge_of_tendsto' hx
      (fun n => (hCommon (ψ n) x ⟨hxI.1.le, hxI.2.le⟩).1)
    exact ⟨(by positivity : (0 : ℝ) ≤ 2 / C).trans hl, le_of_tendsto' hx
      (fun n => (hCommon (ψ n) x ⟨hxI.1.le, hxI.2.le⟩).2)⟩
  have hPS' : Tendsto (fun n => eLpNorm
      ((fun x => Real.sqrt (x * (1 - x)) * deriv (rm (ψ n)) x) -
        (fun x => Real.sqrt (x * (1 - x)) * p0 x)) 2 areaμ) atTop (𝓝 0) := by
    simpa only [Function.comp_def, Pi.sub_def, rm] using hPS.comp hψ.tendsto_atTop
  have hZS' : Tendsto (fun n => eLpNorm
      ((fun x => x * (1 - x) * Real.sqrt (x * (1 - x)) * deriv (deriv (rm (ψ n))) x) -
        (fun x => x * (1 - x) * Real.sqrt (x * (1 - x)) * z0 x)) 2 areaμ)
      atTop (𝓝 0) := by
    simpa only [Function.comp_def, Pi.sub_def, rm] using hZS.comp hψ.tendsto_atTop
  have hLimits := action_mass_tendsto_of_strong_area_graph
    (fun n => Km (ψ n)) (fun n => rm (ψ n)) K0 r0 p0 z0 (2 / C) (2 * C) (by positivity)
    (fun n => (hSmooth (ψ n)).1.continuous)
    (fun n => (hSmooth (ψ n)).2.1.of_le (by simp)) (fun n => hCommon (ψ n))
    (fun n => (hSmooth (ψ n)).2.2.2.2.2.1) (fun n => (hSmooth (ψ n)).2.2.2.2.2.2)
    (hK0.integrable (by norm_num)) hzero0 hone0 hK0box hgraph
    (hL1I.comp hψ.tendsto_atTop) hKae (hRS.comp hψ.tendsto_atTop) hPS' hZS'
  refine ⟨fun n => Km (ψ n), fun n => rm (ψ n), fun n => κm (ψ n), fun n => Λm (ψ n),
    fun n => hSmooth (ψ n), hKS.comp hψ.tendsto_atTop, hKae,
    hRS.comp hψ.tendsto_atTop, hPS', hZS', ?_, hLimits.2.2.1⟩
  simpa only [hmass0] using hLimits.2.2.2

end RicciFlowSharpEstimate.Geometry.AreaProfile
