/-
Copyright (c) 2026 Ziyang Qin. All rights reserved.
No license is granted by this file.
Authors: Ziyang Qin
-/
import RicciFlowSharpEstimate.Geometry.AreaCurvatureCompactness
import RicciFlowSharpEstimate.Geometry.AreaProbeCompactness
import RicciFlowSharpEstimate.Geometry.AreaUniformPrimitives
import RicciFlowSharpEstimate.Geometry.WeakAreaAction
import RicciFlowSharpEstimate.Analysis.BoundedWeakPairing
import RicciFlowSharpEstimate.Analysis.L2WeightedMassContinuity

/-!
# Joint normalized weak limits of the original smooth area competitors

The curvature and both bounding scalars, probe and its two weak derivatives
are extracted on one subsequence. Actual area primitives converge uniformly,
probes converge strongly in L², and the physical weighted mass is retained.
-/

noncomputable section

namespace RicciFlowSharpEstimate.Geometry.AreaProfile

open Set MeasureTheory Filter Topology
open scoped ContDiff ENNReal

local notation "areaμ" => volume.restrict (Ioo (0 : ℝ) 1)

private theorem probeMass_tendsto_of_uniform_warp_strong_probe
    (K : ℕ → ℝ → ℝ) (K0 : ℝ → ℝ) (r : ℕ → ℝ → ℝ) (r0 : ℝ → ℝ)
    (hK : ∀ n, Continuous (K n)) (hr : ∀ n, MemLp (r n) 2 areaμ) (hr0 : MemLp r0 2 areaμ)
    (hf0 : ContinuousOn (warp K0) (Icc (0 : ℝ) 1))
    (D : ℝ) (hfB : ∀ n x, x ∈ Icc (0 : ℝ) 1 → |warp (K n) x| ≤ D)
    (hf0B : ∀ x ∈ Icc (0 : ℝ) 1, |warp K0 x| ≤ D)
    (hwarp : TendstoUniformlyOn (fun n => warp (K n)) (warp K0) atTop (Icc (0 : ℝ) 1))
    (hprobe : Tendsto (fun n => eLpNorm (r n - r0) 2 areaμ) atTop (𝓝 0)) :
    Integrable (fun x => warp K0 x * r0 x ^ 2) areaμ ∧
      Tendsto (fun n => probeMass (K n) (r n)) atTop (𝓝 (probeMass K0 r0)) := by
  have hFmem (n : ℕ) : MemLp (warp (K n)) ∞ areaμ := by
    apply MemLp.of_bound (warp_continuous (K n) (hK n)).aestronglyMeasurable D
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
    simpa only [Real.norm_eq_abs] using hfB n x ⟨hx.1.le, hx.2.le⟩
  have hF0meas : AEStronglyMeasurable (warp K0) areaμ :=
    ((hf0.mono Ioo_subset_Icc_self).locallyIntegrableOn measurableSet_Ioo).aestronglyMeasurable
  have hF0norm : ∀ᵐ x ∂areaμ, ‖warp K0 x‖ ≤ D := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
    simpa only [Real.norm_eq_abs] using hf0B x ⟨hx.1.le, hx.2.le⟩
  have hF0mem : MemLp (warp K0) ∞ areaμ := MemLp.of_bound hF0meas D hF0norm
  let F : ℕ → Lp ℝ ∞ areaμ := fun n => (hFmem n).toLp (warp (K n))
  let F0 : Lp ℝ ∞ areaμ := hF0mem.toLp (warp K0)
  let R : ℕ → Lp ℝ 2 areaμ := fun n => (hr n).toLp (r n)
  let R0 : Lp ℝ 2 areaμ := hr0.toLp r0
  have hFconv : Tendsto F atTop (𝓝 F0) := by
    apply Analysis.L2WeightedMassContinuity.tendsto_top_of_eventually_ae_abs_sub_le
    intro ε hε
    filter_upwards [(Metric.tendstoUniformlyOn_iff.mp hwarp) ε hε] with n hn
    filter_upwards [(hFmem n).coeFn_toLp, hF0mem.coeFn_toLp,
      ae_restrict_mem measurableSet_Ioo] with x hx hx0 hxI
    change F n x = warp (K n) x at hx
    change F0 x = warp K0 x at hx0
    rw [hx, hx0]
    have h := (hn x ⟨hxI.1.le, hxI.2.le⟩).le
    simpa only [Real.dist_eq, abs_sub_comm] using h
  have hRconv : Tendsto R atTop (𝓝 R0) := by
    apply tendsto_iff_edist_tendsto_0.mpr
    simpa only [R, R0, Lp.edist_toLp_toLp] using hprobe
  have hvalue (n : ℕ) : (∫ x, F n x * (R n x) ^ 2 ∂areaμ) = probeMass (K n) (r n) := by
    rw [probeMass, intervalIntegral.integral_of_le zero_le_one, integral_Ioc_eq_integral_Ioo]
    apply integral_congr_ae
    filter_upwards [(hFmem n).coeFn_toLp, (hr n).coeFn_toLp] with x hx hy
    change F n x = warp (K n) x at hx
    change R n x = r n x at hy
    rw [hx, hy]
  have hvalue0 : (∫ x, F0 x * (R0 x) ^ 2 ∂areaμ) = probeMass K0 r0 := by
    rw [probeMass, intervalIntegral.integral_of_le zero_le_one, integral_Ioc_eq_integral_Ioo]
    apply integral_congr_ae
    filter_upwards [hF0mem.coeFn_toLp, hr0.coeFn_toLp] with x hx hy
    change F0 x = warp K0 x at hx
    change R0 x = r0 x at hy
    rw [hx, hy]
  refine ⟨hr0.integrable_sq.bdd_mul hF0meas hF0norm, ?_⟩
  simpa only [hvalue, hvalue0] using
    Analysis.L2WeightedMassContinuity.tendsto_integral_mul_sq hFconv hRconv

/-- A sequence in the original normalized smooth ratio class with bounded
complete action has an actual joint weak limit of unit physical mass. The
original scalar boxes and ratio are retained on the same subsequence. -/
theorem exists_normalized_joint_weak_limit
    (K r : ℕ → ℝ → ℝ) (κ Λ : ℕ → ℝ) (C B : ℝ) (hC : 1 ≤ C)
    (hK : ∀ n, Continuous (K n)) (hr : ∀ n, ContDiff ℝ 2 (r n))
    (hκ : ∀ n, 0 < κ n)
    (hbox : ∀ n x, x ∈ Icc (0 : ℝ) 1 → κ n ≤ K n x ∧ K n x ≤ Λ n)
    (hratio : ∀ n, Λ n / κ n ≤ C)
    (hzero : ∀ n, (∫ x in (0 : ℝ)..1, K n x) = 2)
    (hone : ∀ n, (∫ x in (0 : ℝ)..1, x * K n x) = 1)
    (hmass : ∀ n, probeMass (K n) (r n) = 1)
    (hA : ∀ n, meridionalAction (K n) (r n) ≤ B) :
    ∃ K0 r0 p0 z0 : ℝ → ℝ, ∃ κ0 Λ0 : ℝ, ∃ φ : ℕ → ℕ,
      StrictMono φ ∧ MemLp K0 2 areaμ ∧ MemLp K0 ∞ areaμ ∧ 0 < κ0 ∧ Λ0 / κ0 ≤ C ∧
      (∀ᵐ x ∂areaμ, κ0 ≤ K0 x ∧ K0 x ≤ Λ0) ∧
      Tendsto (fun n => κ (φ n)) atTop (𝓝 κ0) ∧
      Tendsto (fun n => Λ (φ n)) atTop (𝓝 Λ0) ∧
      (∫ x in (0 : ℝ)..1, K0 x) = 2 ∧ (∫ x in (0 : ℝ)..1, x * K0 x) = 1 ∧
      Analysis.HasParabolicWeakDerivatives r0 p0 z0 ∧
      ContinuousOn r0 (Ioo 0 1) ∧ ContinuousOn p0 (Ioo 0 1) ∧
      ContinuousOn (warp K0) (Icc (0 : ℝ) 1) ∧
      ContinuousOn (warpSlope K0) (Icc (0 : ℝ) 1) ∧
      Analysis.HasWeakDerivOn (Ioo 0 1) (warp K0) (warpSlope K0) ∧
      Analysis.HasWeakDerivOn (Ioo 0 1) (warpSlope K0) (fun x => -2 * K0 x) ∧
      IntervalIntegrable (fun x => meridionalActionDensity (warp K0 x) (warpSlope K0 x)
        (K0 x) (r0 x) (p0 x) (z0 x)) volume 0 1 ∧
      MemLp (fun x => Real.sqrt (warp K0 x) * weakMeridionalOperator K0 r0 p0 z0 x) 2 areaμ ∧
      MemLp (fun x => Real.sqrt (warp K0 x) * (K0 x * r0 x)) 2 areaμ ∧
      (∀ x ∈ Icc (0 : ℝ) 1, (2 / C) * x * (1 - x) ≤ warp K0 x ∧
        warp K0 x ≤ (2 * C) * x * (1 - x) ∧ |warpSlope K0 x| ≤ 2) ∧
      (warp K0 0 = 0 ∧ warp K0 1 = 0 ∧ warpSlope K0 0 = 2 ∧ warpSlope K0 1 = -2) ∧
      Integrable (fun x => warp K0 x * r0 x ^ 2) areaμ ∧ probeMass K0 r0 = 1 ∧
      (∃ x ∈ Ioo (0 : ℝ) 1, r0 x ≠ 0) ∧
      Tendsto (fun n => eLpNorm (r (φ n) - r0) 2 areaμ) atTop (𝓝 0) ∧
      TendstoLocallyUniformlyOn (fun n => r (φ n)) r0 atTop (Ioo 0 1) ∧
      TendstoLocallyUniformlyOn (fun n => deriv (r (φ n))) p0 atTop (Ioo 0 1) ∧
      TendstoUniformlyOn (fun n => warp (K (φ n))) (warp K0) atTop (Icc (0 : ℝ) 1) ∧
      TendstoUniformlyOn (fun n => warpSlope (K (φ n))) (warpSlope K0) atTop (Icc (0 : ℝ) 1) ∧
      (∀ v : ℝ → ℝ, Integrable v areaμ →
        Tendsto (fun n => ∫ x, K (φ n) x * v x ∂areaμ) atTop
          (𝓝 (∫ x, K0 x * v x ∂areaμ))) ∧
      (∀ v : Lp ℝ 2 areaμ,
        Tendsto (fun n => ∫ x, (x * (1 - x) * Real.sqrt (x * (1 - x)) *
          deriv (deriv (r (φ n))) x) * v x ∂areaμ) atTop
          (𝓝 (∫ x, (x * (1 - x) * Real.sqrt (x * (1 - x)) * z0 x) * v x ∂areaμ))) := by
  have hCpos : 0 < C := zero_lt_one.trans_le hC
  have hcommon (n : ℕ) : ∀ x ∈ Icc (0 : ℝ) 1, 2 / C ≤ K n x ∧ K n x ≤ 2 * C :=
    curvature_bounds_of_ratio (K n) (hK n) (κ n) (Λ n) C (hκ n) (hbox n)
      (hratio n) (hzero n)
  have hboxAE (n : ℕ) : ∀ᵐ x ∂areaμ, κ n ≤ K n x ∧ K n x ≤ Λ n := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
    exact hbox n x ⟨hx.1.le, hx.2.le⟩
  have hzeroμ (n : ℕ) : (∫ x, K n x ∂areaμ) = 2 := by
    simpa only [intervalIntegral.integral_of_le zero_le_one, integral_Ioc_eq_integral_Ioo]
      using hzero n
  have honeμ (n : ℕ) : (∫ x, x * K n x ∂areaμ) = 1 := by
    simpa only [intervalIntegral.integral_of_le zero_le_one, integral_Ioc_eq_integral_Ioo]
      using hone n
  obtain ⟨K0, κ0, Λ0, σ, hK0mem, hσ, hκconv, hΛconv, hKweak, hKzero,
      hKone, hκrange, hΛrange, hκ0, hratio0, hbox0⟩ :=
    exists_curvature_subsequence_of_ratio_bound K κ Λ C hC
      (fun n => (hK n).aestronglyMeasurable) hκ hboxAE hratio hzeroμ honeμ
  obtain ⟨r0, p0, z0, τ, hτ, hgraph, hr0c, hp0c, hstrong, hrlocal, hplocal,
      hzweak, _, hnz⟩ := exists_subseq_weak_probe_of_action_bound
    (fun n => K (σ n)) (fun n => r (σ n)) (fun n => hK (σ n)) (fun n => hr (σ n))
    (2 / C) (2 * C) (by positivity) (fun n => hcommon (σ n))
    (fun n => hzero (σ n)) (fun n => hone (σ n)) (fun n => hmass (σ n)) B
    (fun n => hA (σ n))
  let φ : ℕ → ℕ := σ ∘ τ
  have hweakFinal : ∀ v : Lp ℝ 2 areaμ,
      Tendsto (fun n => ∫ x, K (φ n) x * v x ∂areaμ) atTop
        (𝓝 (∫ x, K0 x * v x ∂areaμ)) :=
    fun v => (hKweak v).comp hτ.tendsto_atTop
  have hF := tendstoUniformlyOn_warp_of_weak_L2 (fun n => K (φ n)) K0
    (fun n => hK (φ n)) (2 / C) (2 * C) (by positivity)
    (fun n => hcommon (φ n)) hK0mem hweakFinal (fun n => hzero (φ n))
  have hb := tendstoUniformlyOn_warpSlope_of_weak_L2 (fun n => K (φ n)) K0
    (fun n => hK (φ n)) (2 / C) (2 * C) (by positivity)
    (fun n => hcommon (φ n)) hK0mem hweakFinal
  have hf0c := continuousOn_warp_of_weak_L2 (fun n => K (φ n)) K0
    (fun n => hK (φ n)) (2 / C) (2 * C) (by positivity)
    (fun n => hcommon (φ n)) hK0mem hweakFinal (fun n => hzero (φ n))
  have hb0c := continuousOn_warpSlope_of_weak_L2 (fun n => K (φ n)) K0
    (fun n => hK (φ n)) (2 / C) (2 * C) (by positivity)
    (fun n => hcommon (φ n)) hK0mem hweakFinal
  have hfB (n : ℕ) (x : ℝ) (hx : x ∈ Icc (0 : ℝ) 1) : |warp (K (φ n)) x| ≤ 1 := by
    have h := warp_nonneg_le_two_mul_min (K (φ n)) (hK (φ n))
      (fun y hy => (hκ (φ n)).le.trans (hbox (φ n) y hy).1)
      (hzero (φ n)) (hone (φ n)) x hx
    rw [abs_of_nonneg h.1]
    linarith only [h.2, min_le_left x (1 - x), min_le_right x (1 - x)]
  have hf0B (x : ℝ) (hx : x ∈ Icc (0 : ℝ) 1) : |warp K0 x| ≤ 1 :=
    le_of_tendsto' (hF.tendsto_at hx).abs (fun n => hfB n x hx)
  have hmassLimit := probeMass_tendsto_of_uniform_warp_strong_probe
    (fun n => K (φ n)) K0 (fun n => r (φ n)) r0 (fun n => hK (φ n))
    (fun n => (Analysis.hasParabolicWeakDerivatives_of_contDiff (hr (φ n))).memLp)
    hgraph.memLp hf0c 1 hfB hf0B hF hstrong
  have hmass0 : probeMass K0 r0 = 1 := by
    have ht : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 (probeMass K0 r0)) := by
      simpa only [hmass] using hmassLimit.2
    exact tendsto_nhds_unique ht tendsto_const_nhds
  have hKabs (n : ℕ) : ∀ᵐ x ∂areaμ, |K (φ n) x| ≤ 2 * C := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
    have h := hcommon (φ n) x ⟨hx.1.le, hx.2.le⟩
    rw [abs_of_nonneg ((by positivity : (0 : ℝ) ≤ 2 / C).trans h.1)]
    exact h.2
  have hK0abs : ∀ᵐ x ∂areaμ, |K0 x| ≤ 2 * C := by
    filter_upwards [hbox0] with x hx
    rw [abs_of_nonneg (hκ0.le.trans hx.1)]
    exact hx.2.trans hΛrange.2
  have hweakStar := Analysis.tendsto_integral_mul_of_bounded_L2_pairings
    (fun n => (hK (φ n)).aestronglyMeasurable) hK0mem.aestronglyMeasurable
    hKabs hK0abs hweakFinal
  have hgeom (x : ℝ) (hx : x ∈ Icc (0 : ℝ) 1) :
      (2 / C) * x * (1 - x) ≤ warp K0 x ∧
        warp K0 x ≤ (2 * C) * x * (1 - x) ∧ |warpSlope K0 x| ≤ 2 := by
    have hf := warp_bounds_of_weak_L2 (fun n => K (φ n)) K0
      (fun n => hK (φ n)) (2 / C) (2 * C) (by positivity)
      (fun n => hcommon (φ n)) hK0mem hweakFinal (fun n => hzero (φ n))
      (fun n => hone (φ n)) x hx
    exact ⟨hf.1, hf.2, abs_warpSlope_le_two_of_weak_L2 (fun n => K (φ n)) K0
      (fun n => hK (φ n)) (2 / C) (2 * C) (by positivity)
      (fun n => hcommon (φ n)) hK0mem hweakFinal (fun n => hzero (φ n)) x hx⟩
  have hf0meas : AEStronglyMeasurable (warp K0) areaμ :=
    ((hf0c.mono Ioo_subset_Icc_self).locallyIntegrableOn measurableSet_Ioo).aestronglyMeasurable
  have hb0meas : AEStronglyMeasurable (warpSlope K0) areaμ :=
    ((hb0c.mono Ioo_subset_Icc_self).locallyIntegrableOn measurableSet_Ioo).aestronglyMeasurable
  have hKbox0 : ∀ᵐ x ∂areaμ, 0 ≤ K0 x ∧ K0 x ≤ 2 * C := by
    filter_upwards [hbox0] with x hx
    exact ⟨hκ0.le.trans hx.1, hx.2.trans hΛrange.2⟩
  have hFbox0 : ∀ᵐ x ∂areaμ,
      0 ≤ warp K0 x ∧ warp K0 x ≤ (2 * C) * (x * (1 - x)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
    have h := hgeom x ⟨hx.1.le, hx.2.le⟩
    refine ⟨?_, by simpa only [mul_assoc] using h.2.1⟩
    exact (mul_nonneg (mul_nonneg (by positivity : (0 : ℝ) ≤ 2 / C) hx.1.le)
      (sub_nonneg.mpr hx.2.le)).trans h.1
  have hbbox0 : ∀ᵐ x ∂areaμ, |warpSlope K0 x| ≤ 2 := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
    exact (hgeom x ⟨hx.1.le, hx.2.le⟩).2.2
  have hActionInt := weakMeridionalAction_intervalIntegrable_of_warp_bounds
    K0 r0 p0 z0 (2 * C) hgraph (by positivity) hK0mem.aestronglyMeasurable
    hf0meas hb0meas hKbox0 hFbox0 hbbox0
  have hSquareFactors := memLp_weak_operator_and_potential_of_warp_bounds
    K0 r0 p0 z0 (2 * C) hgraph (by positivity) hK0mem.aestronglyMeasurable
    hf0meas hb0meas hKbox0 hFbox0 hbbox0
  have hK0top : MemLp K0 ∞ areaμ := by
    apply memLp_top_of_bound hK0mem.aestronglyMeasurable (2 * C)
    simpa only [Real.norm_eq_abs] using hK0abs
  have hfD := hasWeakDerivOn_warp_of_weak_L2 (fun n => K (φ n)) K0
    (fun n => hK (φ n)) (2 / C) (2 * C) (by positivity)
    (fun n => hcommon (φ n)) hK0mem hweakFinal (fun n => hzero (φ n))
  have hbD := hasWeakDerivOn_warpSlope_of_weak_L2 (fun n => K (φ n)) K0
    (fun n => hK (φ n)) (2 / C) (2 * C) (by positivity)
    (fun n => hcommon (φ n)) hK0mem hweakFinal
  refine ⟨K0, r0, p0, z0, κ0, Λ0, φ, hσ.comp hτ, hK0mem, hK0top, hκ0, hratio0, hbox0,
    hκconv.comp hτ.tendsto_atTop, hΛconv.comp hτ.tendsto_atTop, ?_, ?_, hgraph,
    hr0c, hp0c, hf0c, hb0c, hfD, hbD, hActionInt, hSquareFactors.1, hSquareFactors.2,
    hgeom, ?_, hmassLimit.1, hmass0, hnz,
    hstrong, hrlocal, hplocal, hF, hb, hweakStar, hzweak⟩
  · simpa only [intervalIntegral.integral_of_le zero_le_one, integral_Ioc_eq_integral_Ioo]
      using hKzero
  · simpa only [intervalIntegral.integral_of_le zero_le_one, integral_Ioc_eq_integral_Ioo]
      using hKone
  · exact warp_endpoints_of_weak_L2 (fun n => K (φ n)) K0
      (fun n => hK (φ n)) (2 / C) (2 * C) (by positivity)
      (fun n => hcommon (φ n)) hK0mem hweakFinal (fun n => hzero (φ n))
      (fun n => hone (φ n))

end RicciFlowSharpEstimate.Geometry.AreaProfile
