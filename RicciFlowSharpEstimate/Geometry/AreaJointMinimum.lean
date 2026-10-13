/-
Copyright (c) 2026 Ziyang Qin. All rights reserved.
No license is granted by this file.
Authors: Ziyang Qin
-/
import RicciFlowSharpEstimate.Geometry.RecoverableAreaCompetitor
import RicciFlowSharpEstimate.Geometry.AreaJointSmoothRecovery
import RicciFlowSharpEstimate.Analysis.ParabolicGraphConvergence

/-!
# Attainment of the original smooth infimum in the recoverable weak class

An actual minimizing smooth sequence supplies the joint limit. Full-action
lower semicontinuity gives one inequality, and genuine smooth recovery gives
the reverse inequality. Thus the produced weak pair is a joint minimum on
the stated recoverable class, without assuming smooth attainment or a
zero eigenvalue. The smooth-class infimum is not a determining threshold.
-/

noncomputable section
namespace RicciFlowSharpEstimate.Geometry.AreaProfile
open Set MeasureTheory Filter Topology
open scoped ContDiff ENNReal

local notation "areaμ" => volume.restrict (Ioo (0 : ℝ) 1)

/-- The actual normalized smooth-class infimum is attained by a physically
nonzero pair in the recoverable weak class. Its action is minimal against
every member of that class. No minimizing pair or minimizing sequence is
an input, and no smooth attainment is asserted. -/
theorem exists_recoverable_area_minimizer (C : ℝ) (hC : 1 ≤ C) :
    ∃ K r p z : ℝ → ℝ,
      IsRecoverableAreaCompetitor C K r p z ∧
      ContinuousOn r (Ioo (0 : ℝ) 1) ∧ ContinuousOn p (Ioo (0 : ℝ) 1) ∧
      (∃ x ∈ Ioo (0 : ℝ) 1, r x ≠ 0) ∧
      weakMeridionalAction K r p z = smoothAreaInfimum C ∧
      (∀ K' r' p' z' : ℝ → ℝ, IsRecoverableAreaCompetitor C K' r' p' z' →
        weakMeridionalAction K r p z ≤ weakMeridionalAction K' r' p' z') := by
  classical
  obtain ⟨K, r, hS, hSub, hALimit⟩ := exists_smooth_area_minimizing_sequence C hC
  choose κ Λ hκ hbox hratio using fun n => (hS n).2.2.1
  obtain ⟨K0, r0, p0, z0, κ0, Λ0, φ, hφ, hK02, hK0inf, hκ0, hratio0,
    hbox0, hκconv, hΛconv, hzero0, hone0, hgraph, hr0c, hp0c, hf0c, hb0c,
    hDf, hDb, hActionInt, hQmem, hVmem, hgeom, hpoles, hMassInt, hmass0, hnz,
    hstrong, hrlocal, hplocal, hF, hbF, hKweak, hzweak, hQweak, hVweak, hAliminf,
    Ks, rs, κs, Λs, hScalar, hKsStrong, hKsAE, hRsStrong, hPsStrong, hZsStrong,
    hMassLimit, hActionLimit, N, α, X, D, R, hR, hα, hαpos, hαconv, hsmooth,
    hmassN, hnzN, hscale, hactN, hboxN, htie, hmap, hcurv, hnonzero, hgeomlimit⟩ :=
    exists_joint_weak_limit_with_smooth_geometric_recovery K r κ Λ C 5 hC
      (fun n => (hS n).1) (fun n => (hS n).2.1) hκ hbox hratio
      (fun n => (hS n).2.2.2.1) (fun n => (hS n).2.2.2.2.1)
      (fun n => (hS n).2.2.2.2.2) hSub
  have hNormGraph := Analysis.parabolicGraph_tendsto_const_mul
    (fun n => (hScalar (n + N)).2.1.of_le (by simp)) hgraph hαconv
    (hRsStrong.comp (tendsto_add_atTop_nat N))
    (hPsStrong.comp (tendsto_add_atTop_nat N))
    (hZsStrong.comp (tendsto_add_atTop_nat N))
  have hRecoverable : IsRecoverableAreaCompetitor C K0 r0 p0 z0 := by
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
  have hAle : weakMeridionalAction K0 r0 p0 z0 ≤ smoothAreaInfimum C :=
    hAliminf.trans_eq hALimit.liminf_eq
  have hEq := le_antisymm hAle (hRecoverable.infimum_le_action hC)
  refine ⟨K0, r0, p0, z0, hRecoverable, hr0c, hp0c, hnz, hEq, ?_⟩
  intro K' r' p' z' h'
  rw [hEq]
  exact h'.infimum_le_action hC

end RicciFlowSharpEstimate.Geometry.AreaProfile
