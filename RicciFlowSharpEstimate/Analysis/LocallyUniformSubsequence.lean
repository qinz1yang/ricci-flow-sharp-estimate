/-
Copyright (c) 2026 Ziyang Qin. All rights reserved.
No license is granted by this file.
Authors: Ziyang Qin
-/
import Mathlib.Topology.UniformSpace.Ascoli
import Mathlib.Topology.UniformSpace.CompleteSeparated
import Mathlib.Topology.Sequences
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Analysis.Normed.Group.Basic

/-!
# Locally uniform subsequences of equicontinuous families

On a locally compact sigma-compact domain, pointwise bounded equicontinuous
families with values in a proper normed group have locally uniform subsequences.
-/

noncomputable section

namespace RicciFlowSharpEstimate.Analysis

open Set Filter Topology
open scoped UniformConvergence

/-- Sequential Arzela-Ascoli on a locally compact sigma-compact domain. -/
theorem exists_subseq_tendstoLocallyUniformly_of_equicontinuous
    {X E : Type*} [TopologicalSpace X] [LocallyCompactSpace X]
    [SigmaCompactSpace X] [NormedAddCommGroup E] [ProperSpace E]
    (u : ℕ → C(X, E)) (heq : Equicontinuous (fun n => (u n : X → E)))
    (hb : ∀ x : X, ∃ B : ℝ, ∀ n, ‖u n x‖ ≤ B) :
    ∃ g : C(X, E), ∃ φ : ℕ → ℕ, StrictMono φ ∧
      TendstoLocallyUniformly (fun n x => u (φ n) x) g atTop := by
  classical
  have heqRange : Equicontinuous (fun f : range u => (f.val : X → E)) := by
    have h := heq.comp (fun f : range u => f.property.choose)
    convert h using 1
    funext f x
    exact congrArg (fun z : C(X, E) => z x) f.property.choose_spec.symm
  let : T2Space (X →ᵤ[{K : Set X | IsCompact K}] E) :=
    UniformOnFun.t2Space_of_covering
      (eq_univ_iff_forall.mpr fun x => mem_sUnion_of_mem (mem_singleton x) isCompact_singleton)
  have hcompact : IsCompact (closure (range u)) := by
    apply ArzelaAscoli.isCompact_closure_of_isClosedEmbedding
      (F := fun f : C(X, E) => (f : X → E))
      (𝔖 := {s : Set X | IsCompact s}) (fun _ h => h)
      ContinuousMap.isUniformEmbedding_toUniformOnFunIsCompact.isClosedEmbedding
    · intro K _
      exact heqRange.equicontinuousOn K
    · intro K _ x _
      obtain ⟨B, hB⟩ := hb x
      refine ⟨Metric.closedBall (0 : E) B, isCompact_closedBall _ _, ?_⟩
      rintro f ⟨n, rfl⟩
      simpa only [Metric.mem_closedBall, dist_zero_right] using hB n
  obtain ⟨g, _, φ, hφ, hg⟩ := hcompact.tendsto_subseq
    (fun n => subset_closure (mem_range_self n))
  exact ⟨g, φ, hφ, ContinuousMap.tendsto_iff_tendstoLocallyUniformly.mp hg⟩

end RicciFlowSharpEstimate.Analysis
