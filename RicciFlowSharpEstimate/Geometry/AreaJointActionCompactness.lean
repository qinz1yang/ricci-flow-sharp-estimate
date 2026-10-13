/-
Copyright (c) 2026 Ziyang Qin. All rights reserved.
No license is granted by this file.
Authors: Ziyang Qin
-/
import RicciFlowSharpEstimate.Geometry.AreaJointCompactness
import RicciFlowSharpEstimate.Geometry.AreaActionLowerSemicontinuity

/-!
# Joint weak limits with the complete-action liminf inequality

A liminf subsequence is selected before applying the actual joint compactness
producer. All original constraints and unit physical mass are retained, both
positive factors have identified weak limits, and the literal complete weak
action is at most the liminf of the original smooth sequence.
-/

noncomputable section

namespace RicciFlowSharpEstimate.Geometry.AreaProfile

open Set MeasureTheory Filter Topology
open scoped ContDiff ENNReal

local notation "areaμ" => volume.restrict (Ioo (0 : ℝ) 1)

private theorem strictMono_liminf_subsequence (a : ℕ → ℝ)
    (hupper : IsBoundedUnder (· ≤ ·) atTop a)
    (hlower : IsBoundedUnder (· ≥ ·) atTop a) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ Tendsto (a ∘ φ) atTop (𝓝 (liminf a atTop)) := by
  obtain ⟨ψ, hlim, htop⟩ := exists_seq_tendsto_liminf hupper.isCoboundedUnder_ge hlower
  obtain ⟨θ, hθ, hψθ⟩ := strictMono_subseq_of_tendsto_atTop htop
  exact ⟨ψ ∘ θ, hψθ, hlim.comp hθ.tendsto_atTop⟩

/-- Original normalized complete-action sublevels produce one joint weak
limit retaining all constraints and physical mass, with both positive-square
factors identified and complete action at most the original sequence liminf. -/
theorem exists_normalized_joint_weak_limit_le_liminf_action
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
          (𝓝 (∫ x, (x * (1 - x) * Real.sqrt (x * (1 - x)) * z0 x) * v x ∂areaμ))) ∧
      (∀ v : Lp ℝ 2 areaμ,
        Tendsto (fun n => ∫ x, (Real.sqrt (warp (K (φ n)) x) *
          meridionalOperator (K (φ n)) (r (φ n)) x) * v x ∂areaμ) atTop
          (𝓝 (∫ x, (Real.sqrt (warp K0 x) * weakMeridionalOperator K0 r0 p0 z0 x) * v x ∂areaμ))) ∧
      (∀ v : Lp ℝ 2 areaμ,
        Tendsto (fun n => ∫ x, (Real.sqrt (warp (K (φ n)) x) *
          (K (φ n) x * r (φ n) x)) * v x ∂areaμ) atTop
          (𝓝 (∫ x, (Real.sqrt (warp K0 x) * (K0 x * r0 x)) * v x ∂areaμ))) ∧
      weakMeridionalAction K0 r0 p0 z0 ≤
        liminf (fun n => meridionalAction (K n) (r n)) atTop := by
  have hCpos : 0 < C := zero_lt_one.trans_le hC
  have hcommon (n : ℕ) : ∀ x ∈ Icc (0 : ℝ) 1, 2 / C ≤ K n x ∧ K n x ≤ 2 * C :=
    curvature_bounds_of_ratio (K n) (hK n) (κ n) (Λ n) C (hκ n)
      (hbox n) (hratio n) (hzero n)
  have hAlower (n : ℕ) : -actionMassCorrection (2 / C) (2 * C) ≤
      meridionalAction (K n) (r n) := by
    have h := meridionalAction_coercive (K n) (r n) (hK n) (hr n)
      (2 / C) (2 * C) (by positivity) (hcommon n) (hzero n) (hone n)
    rw [hmass n, mul_one] at h
    have hE := probeOperatorEnergy_nonneg (K n) (r n) (hK n)
      (fun x hx => (by positivity : (0 : ℝ) ≤ 2 / C).trans (hcommon n x hx).1)
      (hzero n) (hone n)
    have hU : 0 ≤ ∫ x in (0 : ℝ)..1, r n x ^ 2 :=
      intervalIntegral.integral_nonneg zero_le_one (fun x _ => sq_nonneg (r n x))
    linarith
  have hUpper : IsBoundedUnder (· ≤ ·) atTop (fun n => meridionalAction (K n) (r n)) :=
    ⟨B, eventually_map.mpr (Eventually.of_forall hA)⟩
  have hLower : IsBoundedUnder (· ≥ ·) atTop (fun n => meridionalAction (K n) (r n)) :=
    ⟨-actionMassCorrection (2 / C) (2 * C), eventually_map.mpr (Eventually.of_forall hAlower)⟩
  obtain ⟨ρ, hρ, hAlim⟩ := strictMono_liminf_subsequence
    (fun n => meridionalAction (K n) (r n)) hUpper hLower
  obtain ⟨K0, r0, p0, z0, κ0, Λ0, τ, hτ, hK02, hK0inf, hκ0, hratio0,
    hbox0, hκconv, hΛconv, hzero0, hone0, hgraph, hr0c, hp0c, hf0c, hb0c,
    hDf, hDb, hActionInt, hQmem, hVmem, hgeom, hpoles, hMassInt, hmass0, hnz,
    hstrong, hrlocal, hplocal, hF, hbF, hKweak, hzweak⟩ :=
    exists_normalized_joint_weak_limit
      (fun n => K (ρ n)) (fun n => r (ρ n)) (fun n => κ (ρ n)) (fun n => Λ (ρ n)) C B hC
      (fun n => hK (ρ n)) (fun n => hr (ρ n)) (fun n => hκ (ρ n))
      (fun n => hbox (ρ n)) (fun n => hratio (ρ n)) (fun n => hzero (ρ n))
      (fun n => hone (ρ n)) (fun n => hmass (ρ n)) (fun n => hA (ρ n))
  let φ : ℕ → ℕ := ρ ∘ τ
  let hi : ℝ := max (2 * C) Λ0
  have hboxFinal (n : ℕ) : ∀ x ∈ Icc (0 : ℝ) 1, 2 / C ≤ K (φ n) x ∧ K (φ n) x ≤ hi :=
    fun x hx => ⟨(hcommon (φ n) x hx).1, (hcommon (φ n) x hx).2.trans (le_max_left _ _)⟩
  have hK0box : ∀ᵐ x ∂areaμ, 0 ≤ K0 x ∧ K0 x ≤ hi := by
    filter_upwards [hbox0] with x hx
    exact ⟨hκ0.le.trans hx.1, hx.2.trans (le_max_right _ _)⟩
  have hLSC := weak_factors_and_action_liminf_of_area_limits
    (fun n => K (φ n)) (fun n => r (φ n)) K0 r0 p0 z0 (2 / C) hi B (by positivity)
    (fun n => hK (φ n)) (fun n => hr (φ n)) hboxFinal
    (fun n => hzero (φ n)) (fun n => hone (φ n))
    (fun n => hmass (φ n)) (fun n => hA (φ n)) hgraph hstrong
    (fun x hx => hrlocal.tendsto_at hx) (fun x hx => hplocal.tendsto_at hx)
    (fun x hx => hF.tendsto_at hx) (fun x hx => hbF.tendsto_at hx)
    hf0c hb0c hK02.aestronglyMeasurable hK0box hKweak hzweak
  have hFinalAction : Tendsto (fun n => meridionalAction (K (φ n)) (r (φ n))) atTop
      (𝓝 (liminf (fun n => meridionalAction (K n) (r n)) atTop)) :=
    hAlim.comp hτ.tendsto_atTop
  refine ⟨K0, r0, p0, z0, κ0, Λ0, φ, hρ.comp hτ, hK02, hK0inf, hκ0, hratio0,
    hbox0, hκconv, hΛconv, hzero0, hone0, hgraph, hr0c, hp0c, hf0c, hb0c,
    hDf, hDb, hActionInt, hQmem, hVmem, hgeom, hpoles, hMassInt, hmass0, hnz,
    hstrong, hrlocal, hplocal, hF, hbF, hKweak, hzweak, hLSC.1, hLSC.2.1, ?_⟩
  exact hLSC.2.2.trans_eq hFinalAction.liminf_eq

end RicciFlowSharpEstimate.Geometry.AreaProfile
