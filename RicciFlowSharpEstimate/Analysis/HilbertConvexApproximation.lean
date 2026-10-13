/-
Copyright (c) 2026 Ziyang Qin. All rights reserved.
No license is granted by this file.
Authors: Ziyang Qin
-/
import Mathlib.Analysis.Convex.Combination
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Analysis.LocallyConvex.WithSeminorms
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Norm approximation by convex combinations of weakly convergent tails

Mazur's theorem for a real Hilbert space, with coefficients on the original
natural-number indices. Every approximant is an actual finite convex sum of a
tail of the given sequence. The coefficient data includes positivity, finite
support, unit total weight, and a quantitative norm approximation bound.
-/

noncomputable section

open Filter
open scoped BigOperators

namespace RicciFlowSharpEstimate.Analysis

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

private theorem mem_closure_convexHull_tail_of_tendsto_inner [CompleteSpace E]
    (u : ℕ → E) (x : E)
    (hweak : ∀ v : E,
      Tendsto (fun i ↦ inner ℝ (u i) v) atTop (nhds (inner ℝ x v)))
    (n : ℕ) :
    x ∈ closure (convexHull ℝ (Set.range (fun i : {i : ℕ // n ≤ i} ↦ u i))) := by
  by_contra hx
  obtain ⟨f, a, hsep, hxa⟩ := geometric_hahn_banach_closed_point
    (convex_convexHull ℝ _).closure isClosed_closure hx
  have hrepr (y : E) :
      inner ℝ y ((InnerProductSpace.toDual ℝ E).symm f) = f y := by
    rw [real_inner_comm, InnerProductSpace.toDual_symm_apply]
  have hf : Tendsto (fun i ↦ f (u i)) atTop (nhds (f x)) := by
    simpa only [hrepr] using hweak ((InnerProductSpace.toDual ℝ E).symm f)
  have hle : f x ≤ a := le_of_tendsto hf <|
    (eventually_ge_atTop n).mono fun i hi ↦
      (hsep (u i) (subset_closure
        (subset_convexHull ℝ _ ⟨⟨i, hi⟩, rfl⟩))).le
  exact (not_lt_of_ge hle) hxa

private theorem exists_tail_convexCombination_of_mem_convexHull
    (u : ℕ → E) (n : ℕ) (y : E)
    (hy : y ∈ convexHull ℝ (Set.range (fun i : {i : ℕ // n ≤ i} ↦ u i))) :
    ∃ (s : Finset ℕ) (w : ℕ → ℝ),
      (∀ i, 0 ≤ w i) ∧
      (∀ i, i ∉ s → w i = 0) ∧
      (∀ i ∈ s, n ≤ i) ∧
      (∑ i ∈ s, w i) = 1 ∧
      (∑ i ∈ s, w i • u i) = y := by
  classical
  rw [convexHull_range_eq_exists_affineCombination] at hy
  obtain ⟨t, a, ha, hasum, hay⟩ := hy
  let s : Finset ℕ := t.map (Function.Embedding.subtype fun i : ℕ ↦ n ≤ i)
  let w : ℕ → ℝ := fun i ↦
    if hi : n ≤ i then if (⟨i, hi⟩ : {i : ℕ // n ≤ i}) ∈ t then a ⟨i, hi⟩ else 0
    else 0
  have hw (j : {i : ℕ // n ≤ i}) (hj : j ∈ t) : w j = a j := by
    simp only [w, dite_eq_left j.property, Subtype.coe_eta, ite_eq_left hj]
  refine ⟨s, w, ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    dsimp only [w]
    split_ifs with hni hi
    · exact ha _ hi
    · exact le_rfl
    · exact le_rfl
  · intro i hi
    by_cases hni : n ≤ i
    · have hit : (⟨i, hni⟩ : {i : ℕ // n ≤ i}) ∉ t := by
        intro hit
        exact hi (Finset.mem_map.mpr ⟨⟨i, hni⟩, hit, rfl⟩)
      simp only [w, dite_eq_left hni, ite_eq_right hit]
    · simp only [w, dite_eq_right hni]
  · intro i hi
    obtain ⟨j, _, rfl⟩ := Finset.mem_map.mp hi
    exact j.property
  · change (∑ i ∈ t.map (Function.Embedding.subtype fun i : ℕ ↦ n ≤ i), w i) = 1
    rw [Finset.sum_map]
    exact (Finset.sum_congr rfl hw).trans hasum
  · rw [Finset.affineCombination_eq_linear_combination t
      (fun i : {i : ℕ // n ≤ i} ↦ u i) a hasum] at hay
    change (∑ i ∈ t.map (Function.Embedding.subtype fun i : ℕ ↦ n ≤ i), w i • u i) = y
    rw [Finset.sum_map]
    calc
      (∑ j ∈ t, w j • u j) = ∑ j ∈ t, a j • u j := by
        apply Finset.sum_congr rfl
        intro j hj
        rw [hw j hj]
      _ = y := hay

/-- Mazur's theorem in a complete real Hilbert space. If every inner-product
pairing of `u` converges to the corresponding pairing of `x`, finite convex
combinations of the successive tails converge to `x` in norm. The returned
weights use the original indices of `u`, vanish off their finite support, and
give norm error strictly less than `1 / (n + 1)`. -/
theorem exists_tail_convexCombination_tendsto_of_tendsto_inner [CompleteSpace E]
    (u : ℕ → E) (x : E)
    (hweak : ∀ v : E,
      Tendsto (fun i ↦ inner ℝ (u i) v) atTop (nhds (inner ℝ x v))) :
    ∃ (s : ℕ → Finset ℕ) (w : ℕ → ℕ → ℝ),
      (∀ n i, 0 ≤ w n i) ∧
      (∀ n i, i ∉ s n → w n i = 0) ∧
      (∀ n, ∀ i ∈ s n, n ≤ i) ∧
      (∀ n, (∑ i ∈ s n, w n i) = 1) ∧
      (∀ n, ‖(∑ i ∈ s n, w n i • u i) - x‖ < 1 / ((n : ℝ) + 1)) ∧
      Tendsto (fun n ↦ ∑ i ∈ s n, w n i • u i) atTop (nhds x) := by
  classical
  have happrox (n : ℕ) :
      ∃ (s : Finset ℕ) (w : ℕ → ℝ),
        (∀ i, 0 ≤ w i) ∧
        (∀ i, i ∉ s → w i = 0) ∧
        (∀ i ∈ s, n ≤ i) ∧
        (∑ i ∈ s, w i) = 1 ∧
        ‖(∑ i ∈ s, w i • u i) - x‖ < 1 / ((n : ℝ) + 1) := by
    obtain ⟨y, hy, hdist⟩ :=
      (Metric.mem_closure_iff.mp
        (mem_closure_convexHull_tail_of_tendsto_inner u x hweak n))
        (1 / ((n : ℝ) + 1)) (by positivity)
    obtain ⟨s, w, hnonneg, hzero, htail, hsum, hvalue⟩ :=
      exists_tail_convexCombination_of_mem_convexHull u n y hy
    refine ⟨s, w, hnonneg, hzero, htail, hsum, ?_⟩
    rw [hvalue]
    calc
      ‖y - x‖ = dist y x := (dist_eq_norm y x).symm
      _ = dist x y := dist_comm y x
      _ < 1 / ((n : ℝ) + 1) := hdist
  choose s w hnonneg hzero htail hsum herror using happrox
  refine ⟨s, w, hnonneg, hzero, htail, hsum, herror, ?_⟩
  apply tendsto_iff_dist_tendsto_zero.mpr
  exact squeeze_zero (fun _ ↦ dist_nonneg)
    (fun n ↦ by simpa only [dist_eq_norm] using (herror n).le)
    (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))

/-- A finite family of weak Hilbert limits admits one common sequence of
finite convex tail mixtures converging strongly in every coordinate. -/
theorem exists_tail_convexCombination_tendsto_family
    {ι : Type*} [Finite ι] {F : ι → Type*}
    [∀ i, NormedAddCommGroup (F i)] [∀ i, InnerProductSpace ℝ (F i)]
    [∀ i, CompleteSpace (F i)]
    (u : ℕ → ∀ i, F i) (x : ∀ i, F i)
    (hweak : ∀ i, ∀ v : F i,
      Tendsto (fun n => inner ℝ (u n i) v) atTop (nhds (inner ℝ (x i) v))) :
    ∃ (s : ℕ → Finset ℕ) (w : ℕ → ℕ → ℝ),
      (∀ n i, 0 ≤ w n i) ∧
      (∀ n i, i ∉ s n → w n i = 0) ∧
      (∀ n, ∀ i ∈ s n, n ≤ i) ∧
      (∀ n, (∑ i ∈ s n, w n i) = 1) ∧
      ∀ i, Tendsto (fun n => ∑ j ∈ s n, w n j • u j i) atTop (nhds (x i)) := by
  classical
  let : Fintype ι := Fintype.ofFinite ι
  let U : ℕ → PiLp 2 F := fun n => WithLp.toLp 2 (u n)
  let X : PiLp 2 F := WithLp.toLp 2 x
  have hUweak : ∀ v : PiLp 2 F,
      Tendsto (fun n => inner ℝ (U n) v) atTop (nhds (inner ℝ X v)) := by
    intro v
    simpa only [U, X, PiLp.inner_apply, PiLp.toLp_apply] using
      tendsto_finsetSum Finset.univ (fun i _ => hweak i (v i))
  obtain ⟨s, w, hw, hwzero, htail, hsum, _, hconv⟩ :=
    exists_tail_convexCombination_tendsto_of_tendsto_inner U X hUweak
  refine ⟨s, w, hw, hwzero, htail, hsum, ?_⟩
  intro i
  have h := ((PiLp.proj (𝕜 := ℝ) 2 F i).continuous.tendsto X).comp hconv
  simpa only [Function.comp_def, map_sum, map_smul, PiLp.proj_apply,
    U, X, PiLp.toLp_apply] using h

end RicciFlowSharpEstimate.Analysis

end
