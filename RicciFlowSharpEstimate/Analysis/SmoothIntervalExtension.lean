/-
Copyright (c) 2026 Ziyang Qin. All rights reserved.
No license is granted by this file.
Authors: Ziyang Qin
-/
import DifferentialGeometry.Analysis.Calculus.SmoothExtension.BorelHalfLine.Parametric

/-!
# Smooth extension from a closed real interval

A smooth real function on a nondegenerate closed interval admits a globally
smooth extension agreeing with it on that closed interval. The proof specializes the
parameter-dependent Borel interval extension theorem.

Adapted from Ziyang Qin's historical rotational area-coordinate interval
extension argument.
-/

noncomputable section

namespace RicciFlowSharpEstimate.Analysis

open Set
open scoped ContDiff Topology

/-- A smooth function on a nondegenerate closed real interval has a globally
smooth extension agreeing with it on the entire closed interval. -/
theorem exists_contDiff_extension_Icc (f : ℝ → ℝ) (a b : ℝ) (hab : a < b)
    (hf : ContDiffOn ℝ ∞ f (Icc a b)) :
    ∃ F : ℝ → ℝ, ContDiff ℝ ∞ F ∧ EqOn F f (Icc a b) := by
  let g : ℝ → ℝ → ℝ := fun t _ => f (a + t)
  let K : Set ℝ := Icc (-1 : ℝ) 1
  have hzeroInterior : (0 : ℝ) ∈ interior K := by
    rw [interior_Icc]
    exact ⟨by norm_num, by norm_num⟩
  have hg : ContDiffOn ℝ ∞ (Function.uncurry g) (Icc (0 : ℝ) (b - a) ×ˢ K) := by
    have hmap : ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => a + p.1)
        (Icc (0 : ℝ) (b - a) ×ˢ K) :=
      (contDiff_const.add contDiff_fst).contDiffOn
    apply hf.comp hmap
    rintro ⟨t, z⟩ ⟨ht, _⟩
    exact ⟨by linarith [ht.1], by linarith [ht.2]⟩
  obtain ⟨gext, U, hUnhds, hgext, hEq⟩ :=
    DifferentialGeometry.Analysis.borel_interval_extend_param
      g (b - a) (sub_pos.mpr hab) K 0 hzeroInterior hg
  have hzeroU : (0 : ℝ) ∈ U := mem_of_mem_nhds hUnhds
  let F : ℝ → ℝ := fun x => gext (x - a) 0
  have hF : ContDiff ℝ ∞ F := by
    rw [← contDiffOn_univ]
    have hsection : ContDiffOn ℝ ∞
        (fun x : ℝ => ((x - a : ℝ), (0 : ℝ))) univ :=
      ((contDiff_id.sub contDiff_const).prodMk contDiff_const).contDiffOn
    exact hgext.comp hsection (fun x _ => ⟨mem_univ x, hzeroU⟩)
  refine ⟨F, hF, ?_⟩
  intro x hx
  have hxa : x - a ∈ Icc (0 : ℝ) (b - a) :=
    ⟨by linarith [hx.1], by linarith [hx.2]⟩
  change gext (x - a) 0 = f x
  calc
    gext (x - a) 0 = g (x - a) 0 := hEq (x - a) hxa 0 hzeroU
    _ = f x := by
      simp only [g]
      congr 1
      ring

end RicciFlowSharpEstimate.Analysis
