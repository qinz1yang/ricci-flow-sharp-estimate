/-
Copyright (c) 2026 Ziyang Qin. All rights reserved.
No license is granted by this file.
Authors: Ziyang Qin
-/
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Algebra.Support
import Mathlib.Tactic.Linarith

/-!
# Affine interval feasibility

A positive continuous function on a compact set remains positive under every
sufficiently small affine variation in a continuous direction. Applying this
uniform margin argument to both endpoints preserves a strict interval constraint.
Real closed intervals are included without a nonemptiness assumption. Convex
segments preserve closed interval constraints without regularity assumptions.
-/

namespace RicciFlowSharpEstimate.Analysis

open Set

/-- A continuous affine variation of a positive function on a compact set is
positive for all sufficiently small parameters of either sign. -/
theorem exists_pos_add_mul_pos_of_isCompact {X : Type*} [TopologicalSpace X]
    (s : Set X) (hs : IsCompact s) (K ξ : X → ℝ)
    (hK : ContinuousOn K s) (hξ : ContinuousOn ξ s)
    (hpos : ∀ x ∈ s, 0 < K x) :
    ∃ δ > 0, ∀ t : ℝ, |t| < δ → ∀ x ∈ s, 0 < K x + t * ξ x := by
  obtain ⟨m, hm, hKm⟩ := hs.exists_forall_le' hK hpos
  obtain ⟨M, hM⟩ := hs.bddAbove_image hξ.abs
  have hB : 0 < |M| + 1 := by linarith [abs_nonneg M]
  refine ⟨m / (|M| + 1), div_pos hm hB, ?_⟩
  intro t ht x hx
  have hξM : |ξ x| ≤ M := hM (mem_image_of_mem (fun y => |ξ y|) hx)
  have hξB : |ξ x| ≤ |M| + 1 := by linarith [le_abs_self M]
  have htm : |t| * (|M| + 1) < m := (lt_div_iff₀ hB).mp ht
  have hpert : |t * ξ x| < m := by
    calc
      |t * ξ x| = |t| * |ξ x| := abs_mul _ _
      _ ≤ |t| * (|M| + 1) :=
        mul_le_mul_of_nonneg_left hξB (abs_nonneg t)
      _ < m := htm
  have hbase := hKm x hx
  have hlower := neg_abs_le (t * ξ x)
  linarith

/-- A continuous function strictly inside a real interval on a compact set
remains inside that interval under every sufficiently small affine variation. -/
theorem exists_pos_add_mul_mem_Ioo_of_isCompact {X : Type*} [TopologicalSpace X]
    (s : Set X) (hs : IsCompact s) (K ξ : X → ℝ) (lo hi : ℝ)
    (hK : ContinuousOn K s) (hξ : ContinuousOn ξ s)
    (hbox : ∀ x ∈ s, K x ∈ Ioo lo hi) :
    ∃ δ > 0, ∀ t : ℝ, |t| < δ → ∀ x ∈ s, K x + t * ξ x ∈ Ioo lo hi := by
  obtain ⟨δlo, hδlo, hlo⟩ := exists_pos_add_mul_pos_of_isCompact s hs
    (fun x => K x - lo) ξ (hK.sub continuousOn_const) hξ
    (fun x hx => sub_pos.mpr (hbox x hx).1)
  obtain ⟨δhi, hδhi, hhi⟩ := exists_pos_add_mul_pos_of_isCompact s hs
    (fun x => hi - K x) (fun x => -ξ x) (continuousOn_const.sub hK) hξ.neg
    (fun x hx => sub_pos.mpr (hbox x hx).2)
  refine ⟨min δlo δhi, lt_min hδlo hδhi, ?_⟩
  intro t ht x hx
  have hlower := hlo t (ht.trans_le (min_le_left _ _)) x hx
  have hupper := hhi t (ht.trans_le (min_le_right _ _)) x hx
  change 0 < K x - lo + t * ξ x at hlower
  change 0 < hi - K x + t * (-ξ x) at hupper
  constructor <;> nlinarith

/-- A segment joining two points of a closed real interval stays in the interval. -/
theorem add_mul_sub_mem_Icc {lo hi k g t : ℝ}
    (hk : k ∈ Icc lo hi) (hg : g ∈ Icc lo hi) (ht : t ∈ Icc (0 : ℝ) 1) :
    k + t * (g - k) ∈ Icc lo hi := by
  constructor
  · nlinarith [mul_nonneg (sub_nonneg.mpr ht.2) (sub_nonneg.mpr hk.1),
      mul_nonneg ht.1 (sub_nonneg.mpr hg.1)]
  · nlinarith [mul_nonneg (sub_nonneg.mpr ht.2) (sub_nonneg.mpr hk.2),
      mul_nonneg ht.1 (sub_nonneg.mpr hg.2)]

/-- A direction supported away from the obstacle contacts is genuinely feasible
for both signs of a sufficiently small parameter. The closed support is essential. -/
theorem exists_pos_add_mul_mem_Icc_of_isCompact_of_free_support
    {X : Type*} [TopologicalSpace X] (s : Set X) (hs : IsCompact s)
    (K ξ : X → ℝ) (lo hi : ℝ) (hK : ContinuousOn K s) (hξ : ContinuousOn ξ s)
    (hbox : ∀ x ∈ s, K x ∈ Icc lo hi)
    (hfree : ∀ x ∈ s ∩ tsupport ξ, K x ∈ Ioo lo hi) :
    ∃ δ > 0, ∀ t : ℝ, |t| < δ → ∀ x ∈ s, K x + t * ξ x ∈ Icc lo hi := by
  obtain ⟨δ, hδ, hd⟩ := exists_pos_add_mul_mem_Ioo_of_isCompact
    (s ∩ tsupport ξ) (hs.inter_right (isClosed_tsupport ξ)) K ξ lo hi
    (hK.mono inter_subset_left) (hξ.mono inter_subset_left) hfree
  refine ⟨δ, hδ, ?_⟩
  intro t ht x hx
  by_cases hmem : x ∈ tsupport ξ
  · exact ⟨(hd t ht x ⟨hx, hmem⟩).1.le, (hd t ht x ⟨hx, hmem⟩).2.le⟩
  · have hz : ξ x = 0 := (notMem_tsupport_iff_eventuallyEq.mp hmem).eq_of_nhds
    simpa only [hz, mul_zero, add_zero] using hbox x hx

end RicciFlowSharpEstimate.Analysis
