/-
Copyright (c) 2026 Ziyang Qin. All rights reserved.
No license is granted by this file.
Authors: Ziyang Qin
-/
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.Normed.Module.WeakDual

/-!
# Weakly convergent subsequences in separable real Hilbert spaces

A norm-bounded sequence has a weakly convergent subsequence, with the same
norm bound on its limit. The subsequence comes from sequential Banach-Alaoglu
in the weak dual; the Riesz isometry realizes the limiting functional in the
original Hilbert space.
-/

noncomputable section

open Filter

namespace RicciFlowSharpEstimate.Analysis.HilbertWeakSubsequence

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- A constant norm bound passes to a pointwise limit of the inner-product
pairings. This form of weak lower semicontinuity does not require completeness
or separability. -/
theorem norm_le_of_tendsto_inner (u : ℕ → E) (x : E) (B : ℝ)
    (hbound : ∀ n, ‖u n‖ ≤ B)
    (hweak : ∀ v : E,
      Tendsto (fun n ↦ inner ℝ (u n) v) atTop (nhds (inner ℝ x v))) :
    ‖x‖ ≤ B := by
  have hB : 0 ≤ B := (norm_nonneg (u 0)).trans (hbound 0)
  by_cases hx : x = 0
  · simpa only [hx, norm_zero] using hB
  have hxpos : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have hinner : inner ℝ x x ≤ B * ‖x‖ :=
    le_of_tendsto' (hweak x) fun n ↦
      (real_inner_le_norm (u n) x).trans
        (mul_le_mul_of_nonneg_right (hbound n) (norm_nonneg x))
  rw [real_inner_self_eq_norm_mul_norm] at hinner
  exact le_of_mul_le_mul_right hinner hxpos

/-- Every norm-bounded sequence in a separable complete real inner-product
space admits a strictly increasing weakly convergent subsequence, whose limit
satisfies the same norm bound. -/
theorem exists_subseq_tendsto_inner_of_norm_le
    [CompleteSpace E] [TopologicalSpace.SeparableSpace E]
    (u : ℕ → E) (B : ℝ) (hbound : ∀ n, ‖u n‖ ≤ B) :
    ∃ x : E, ‖x‖ ≤ B ∧ ∃ φ : ℕ → ℕ, StrictMono φ ∧
      ∀ v : E,
        Tendsto (fun n ↦ inner ℝ (u (φ n)) v) atTop (nhds (inner ℝ x v)) := by
  let F : ℕ → WeakDual ℝ E := fun n ↦
    StrongDual.toWeakDual (InnerProductSpace.toDual ℝ E (u n))
  have hF : ∀ n, F n ∈
      WeakDual.toStrongDual ⁻¹' Metric.closedBall (0 : StrongDual ℝ E) B := by
    intro n
    simpa only [F, Set.mem_preimage, StrongDual.toStrongDual_toWeakDual,
      Metric.mem_closedBall, dist_zero_right, LinearIsometryEquiv.norm_map] using hbound n
  obtain ⟨g, hg, φ, hφ, hconv⟩ :=
    WeakDual.isSeqCompact_closedBall ℝ E (0 : StrongDual ℝ E) B hF
  let x : E := (InnerProductSpace.toDual ℝ E).symm g.toStrongDual
  refine ⟨x, ?_, φ, hφ, ?_⟩
  · change ‖(InnerProductSpace.toDual ℝ E).symm g.toStrongDual‖ ≤ B
    rw [(InnerProductSpace.toDual ℝ E).symm.norm_map]
    simpa only [Set.mem_preimage, Metric.mem_closedBall, dist_zero_right] using hg
  · intro v
    have hv := ((WeakDual.eval_continuous (𝕜 := ℝ) v).tendsto g).comp hconv
    simpa only [Function.comp_def, F, StrongDual.toWeakDual_apply,
      InnerProductSpace.toDual_apply_apply, x, InnerProductSpace.toDual_symm_apply,
      WeakDual.toStrongDual_apply] using hv

end RicciFlowSharpEstimate.Analysis.HilbertWeakSubsequence

end
