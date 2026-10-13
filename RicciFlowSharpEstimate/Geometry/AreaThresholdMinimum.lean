/-
Copyright (c) 2026 Ziyang Qin. All rights reserved.
No license is granted by this file.
Authors: Ziyang Qin
-/
import RicciFlowSharpEstimate.Geometry.RecoverableAreaCap
import RicciFlowSharpEstimate.Geometry.RotationalEndpointSafety
import RicciFlowSharpEstimate.Geometry.RecoverableProbeStationarity
import RicciFlowSharpEstimate.Geometry.SmoothAreaSafety
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# A zero-action recoverable minimum at the original threshold

Negative smooth competitors at decreasing superthreshold caps have a common
compactness cap. The original box witnesses pass to the same joint limit.
Genuine recovery at its exact limiting cap and endpoint safety force zero
action. No operator orientation or determining threshold characterization is
inferred from this critical-object construction.
-/

noncomputable section
namespace RicciFlowSharpEstimate.Geometry.AreaProfile
open Set MeasureTheory Filter Topology
open scoped ContDiff ENNReal
local notation "areaμ" => volume.restrict (Ioo (0 : ℝ) 1)

private theorem exists_threshold_nonpositive_limit :
    ∃ (D : ℝ) (K r p z : ℝ → ℝ),
      IsRecoverableAreaCompetitor D K r p z ∧
      IsBoundedAreaCurvature rotationalThreshold K ∧
      ContinuousOn r (Ioo (0 : ℝ) 1) ∧ ContinuousOn p (Ioo (0 : ℝ) 1) ∧
      (∃ x ∈ Ioo (0 : ℝ) 1, r x ≠ 0) ∧ weakMeridionalAction K r p z ≤ 0 := by
  classical
  obtain ⟨D, hD, _⟩ := exists_between rotationalThreshold_lt_conformalKillingThreshold
  have hDone : 1 ≤ D := one_le_rotationalThreshold.trans hD.le
  let c : ℕ → ℝ := fun n => rotationalThreshold +
    (D - rotationalThreshold) * (1 / ((n : ℝ) + 1))
  have hcgt (n : ℕ) : rotationalThreshold < c n := by
    dsimp only [c]
    exact lt_add_of_pos_right _ (mul_pos (sub_pos.mpr hD) (by positivity))
  have hcle (n : ℕ) : c n ≤ D := by
    have hi : (1 : ℝ) / ((n : ℝ) + 1) ≤ 1 := by
      apply (div_le_one (by positivity : (0 : ℝ) < (n : ℝ) + 1)).mpr
      linarith [Nat.cast_nonneg (α := ℝ) n]
    have hm := mul_le_mul_of_nonneg_left hi (sub_pos.mpr hD).le
    dsimp only [c]
    linarith
  have hct : Tendsto c atTop (𝓝 rotationalThreshold) := by
    have hh := (tendsto_const_nhds : Tendsto (fun _ : ℕ => rotationalThreshold)
      atTop (𝓝 rotationalThreshold)).add
      ((tendsto_const_nhds : Tendsto (fun _ : ℕ => D - rotationalThreshold)
        atTop (𝓝 (D - rotationalThreshold))).mul
          (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)))
    simpa only [mul_zero, add_zero] using hh
  have hneg (n : ℕ) : ∃ K r : ℝ → ℝ,
      IsSmoothAreaCompetitor (c n) K r ∧ meridionalAction K r < 0 := by
    obtain ⟨a, ⟨K, r, h, rfl⟩, ha⟩ := exists_lt_of_csInf_lt
      (smoothAreaActionValues_nonempty (c n) (one_le_rotationalThreshold.trans (hcgt n).le))
      (smoothAreaInfimum_neg_of_rotationalThreshold_lt (hcgt n))
    exact ⟨K, r, h, ha⟩
  choose K r hS hA using hneg
  choose κ Λ hκ hbox hratio using fun n => (hS n).2.2.1
  have hCommon (n : ℕ) : IsSmoothAreaCompetitor D (K n) (r n) :=
    ⟨(hS n).1, (hS n).2.1, ⟨κ n, Λ n, hκ n, hbox n, (hratio n).trans (hcle n)⟩,
      (hS n).2.2.2.1, (hS n).2.2.2.2.1, (hS n).2.2.2.2.2⟩
  have hLower : IsBoundedUnder (· ≥ ·) atTop
      (fun n => meridionalAction (K n) (r n)) :=
    ⟨-actionMassCorrection (2 / D) (2 * D),
      eventually_map.mpr (Eventually.of_forall (fun n => (hCommon n).action_lower_bound hDone))⟩
  have hliminf : liminf (fun n => meridionalAction (K n) (r n)) atTop ≤ 0 :=
    liminf_le_of_frequently_le (Eventually.of_forall (fun n => (hA n).le)).frequently hLower
  obtain ⟨K0, r0, p0, z0, κ0, Λ0, φ, hφ, hK02, hK0inf, hκ0, hratio0,
    hbox0, hκconv, hΛconv, hzero0, hone0, hgraph, hr0c, hp0c, hf0c, hb0c,
    hDf, hDb, hActionInt, hQmem, hVmem, hgeom, hpoles, hMassInt, hmass0, hnz,
    hstrong, hrlocal, hplocal, hF, hbF, hKweak, hzweak, hQweak, hVweak, hAliminf,
    Ks, rs, κs, Λs, hScalar, hKsStrong, hKsAE, hRsStrong, hPsStrong, hZsStrong,
    hMassLimit, hActionLimit, N, α, X, Ds, R, hR, hα, hαpos, hαconv, hsmooth,
    hmassN, hnzN, hscale, hactN, hboxN, htie, hmap, hcurv, hnonzero, hgeomlimit⟩ :=
    exists_joint_weak_limit_with_smooth_geometric_recovery K r κ Λ D 0 hDone
      (fun n => (hS n).1) (fun n => (hS n).2.1) hκ hbox
      (fun n => (hratio n).trans (hcle n))
      (fun n => (hS n).2.2.2.1) (fun n => (hS n).2.2.2.2.1)
      (fun n => (hS n).2.2.2.2.2) (fun n => (hA n).le)
  have hlimbox : Λ0 ≤ rotationalThreshold * κ0 :=
    le_of_tendsto_of_tendsto' hΛconv ((hct.comp hφ.tendsto_atTop).mul hκconv)
      (fun n => (div_le_iff₀ (hκ (φ n))).mp (hratio (φ n)))
  have hBounded : IsBoundedAreaCurvature rotationalThreshold K0 :=
    ⟨hK02.aestronglyMeasurable, ⟨κ0, Λ0, hκ0, hbox0,
      (div_le_iff₀ hκ0).mpr hlimbox⟩, hzero0, hone0⟩
  have hNormGraph := Analysis.parabolicGraph_tendsto_const_mul
    (fun n => (hScalar (n + N)).2.1.of_le (by simp)) hgraph hαconv
    (hRsStrong.comp (tendsto_add_atTop_nat N))
    (hPsStrong.comp (tendsto_add_atTop_nat N))
    (hZsStrong.comp (tendsto_add_atTop_nat N))
  have hRecoverable : IsRecoverableAreaCompetitor D K0 r0 p0 z0 := by
    refine ⟨hK02, hgraph, ⟨κ0, Λ0, hκ0, hbox0, hratio0⟩, hzero0, hone0, hmass0,
      fun n => Ks (n + N), fun n x => α n * rs (n + N) x, ?_,
      hKsStrong.comp (tendsto_add_atTop_nat N), ?_, ?_, ?_⟩
    · intro n
      refine ⟨(hScalar (n + N)).1, hsmooth n, ?_,
        (hScalar (n + N)).2.2.2.2.2.1, (hScalar (n + N)).2.2.2.2.2.2, hmassN n⟩
      exact ⟨κs (n + N), Λs (n + N), (hScalar (n + N)).2.2.1,
        (hScalar (n + N)).2.2.2.1, (hScalar (n + N)).2.2.2.2.1⟩
    · simpa only [one_mul] using hNormGraph.1
    · simpa only [one_mul] using hNormGraph.2.1
    · simpa only [one_mul] using hNormGraph.2.2
  exact ⟨D, K0, r0, p0, z0, hRecoverable, hBounded, hr0c, hp0c, hnz,
    hAliminf.trans hliminf⟩

/-- At the original safety boundary, the complete normalized smooth value
vanishes. The value is derived from endpoint safety and changing-cap compactness;
this does not identify the threshold by a determining equation. -/
theorem smoothAreaInfimum_rotationalThreshold :
    smoothAreaInfimum rotationalThreshold = 0 := by
  have hnonneg := (smoothAreaInfimum_nonneg_iff_rotationalSafeCap
    rotationalThreshold one_le_rotationalThreshold).mpr
      rotationalThreshold_mem_rotationalSafeCaps
  obtain ⟨D, K, r, p, z, hD, hK, _, _, _, hA⟩ := exists_threshold_nonpositive_limit
  have h := hD.of_curvature_cap hK
  exact le_antisymm ((h.infimum_le_action one_le_rotationalThreshold).trans hA) hnonneg

/-- The original threshold has an actual nonzero unit-mass recoverable minimum
with zero complete action and genuine smooth recovery to that same quadruple.
The unrestricted weak probe equation has zero multiplier. No operator sign,
smooth attainment, symmetry, or selected stationary branch is assumed. -/
theorem exists_zero_action_recoverable_area_minimizer :
    ∃ K r p z : ℝ → ℝ,
      IsRecoverableAreaCompetitor rotationalThreshold K r p z ∧
      ContinuousOn r (Ioo (0 : ℝ) 1) ∧ ContinuousOn p (Ioo (0 : ℝ) 1) ∧
      (∃ x ∈ Ioo (0 : ℝ) 1, r x ≠ 0) ∧
      probeMass K r = 1 ∧ weakMeridionalAction K r p z = 0 ∧
      (∀ K' r' p' z' : ℝ → ℝ,
        IsRecoverableAreaCompetitor rotationalThreshold K' r' p' z' →
          weakMeridionalAction K r p z ≤ weakMeridionalAction K' r' p' z') ∧
      (∀ s : ℝ → ℝ, ContDiff ℝ ∞ s →
        weakMeridionalPairing K r p z s (deriv s) (deriv (deriv s)) = 0) ∧
      ∃ Ks rs : ℕ → ℝ → ℝ,
        (∀ n, IsSmoothAreaCompetitor rotationalThreshold (Ks n) (rs n)) ∧
        Tendsto (fun n => eLpNorm (Ks n - K) 2 areaμ) atTop (𝓝 0) ∧
        Tendsto (fun n => eLpNorm (rs n - r) 2 areaμ) atTop (𝓝 0) ∧
        Tendsto (fun n => eLpNorm
          ((fun x => Real.sqrt (x * (1 - x)) * deriv (rs n) x) -
            (fun x => Real.sqrt (x * (1 - x)) * p x)) 2 areaμ) atTop (𝓝 0) ∧
        Tendsto (fun n => eLpNorm
          ((fun x => x * (1 - x) * Real.sqrt (x * (1 - x)) * deriv (deriv (rs n)) x) -
            (fun x => x * (1 - x) * Real.sqrt (x * (1 - x)) * z x)) 2 areaμ) atTop (𝓝 0) ∧
        Tendsto (fun n => meridionalAction (Ks n) (rs n)) atTop (𝓝 0) := by
  obtain ⟨D, K, r, p, z, hD, hK, hrc, hpc, hnz, hA⟩ := exists_threshold_nonpositive_limit
  have h := hD.of_curvature_cap hK
  have hzero : weakMeridionalAction K r p z = 0 := by
    have hlo := h.infimum_le_action one_le_rotationalThreshold
    rw [smoothAreaInfimum_rotationalThreshold] at hlo
    exact le_antisymm hA hlo
  have hmin : ∀ K' r' p' z' : ℝ → ℝ,
      IsRecoverableAreaCompetitor rotationalThreshold K' r' p' z' →
        weakMeridionalAction K r p z ≤ weakMeridionalAction K' r' p' z' := by
    intro K' r' p' z' h'
    rw [hzero, ← smoothAreaInfimum_rotationalThreshold]
    exact h'.infimum_le_action one_le_rotationalThreshold
  obtain ⟨_, _, Ks, rs, hS, hKS, hRS, hPS, hZS, hALimit⟩ :=
    h.exists_action_recovery one_le_rotationalThreshold
  refine ⟨K, r, p, z, h, hrc, hpc, hnz, h.2.2.2.2.2.1, hzero, hmin, ?_,
    Ks, rs, hS, hKS, hRS, hPS, hZS, ?_⟩
  · intro s hs
    simpa only [hzero, zero_mul] using
      (IsRecoverableAreaCompetitor.weak_probe_equation_of_minimum
        one_le_rotationalThreshold h hmin s hs)
  · simpa only [hzero] using hALimit

end RicciFlowSharpEstimate.Geometry.AreaProfile
