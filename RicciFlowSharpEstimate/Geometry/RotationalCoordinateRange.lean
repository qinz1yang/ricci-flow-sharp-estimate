/-
Copyright (c) 2026 Ziyang Qin. All rights reserved.
No license is granted by this file.
Authors: Ziyang Qin
-/
import RicciFlowSharpEstimate.Geometry.RotationalCoordinates
import Mathlib.Analysis.SpecialFunctions.Complex.Arg

/-!
# Range and density of height-cylinder coordinates

The actual height-cylinder map covers precisely the sphere away from its two
poles. Its image is dense in the entire sphere.
-/

noncomputable section

namespace RicciFlowSharpEstimate.Geometry

open Set Metric
open scoped RealInnerProductSpace Topology

local instance : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 2 + 1) :=
  ⟨finrank_euclideanSpace_fin⟩

private theorem sphere_coord_sq_sum (p : RotationalSphere) :
    (p : EuclideanSpace ℝ (Fin 3)) 0 ^ 2 +
      (p : EuclideanSpace ℝ (Fin 3)) 1 ^ 2 +
        (p : EuclideanSpace ℝ (Fin 3)) 2 ^ 2 = 1 := by
  have hn : ‖(p : EuclideanSpace ℝ (Fin 3))‖ = 1 := by
    simpa only [mem_sphere, dist_zero_right] using p.property
  have hs := congrArg (fun r : ℝ => r ^ 2) hn
  rw [EuclideanSpace.real_norm_sq_eq] at hs
  simpa [Fin.sum_univ_succ, add_assoc] using hs

private def planarCoordinate (p : RotationalSphere) : ℂ :=
  ⟨(p : EuclideanSpace ℝ (Fin 3)) 0, (p : EuclideanSpace ℝ (Fin 3)) 1⟩

private theorem norm_planarCoordinate (p : RotationalSphere) :
    ‖planarCoordinate p‖ = Real.sqrt (1 - sphereHeight p ^ 2) := by
  have hs := sphere_coord_sq_sum p
  have hr : 0 ≤ 1 - sphereHeight p ^ 2 := by
    rw [sphereHeight_apply]
    nlinarith [sq_nonneg ((p : EuclideanSpace ℝ (Fin 3)) 0),
      sq_nonneg ((p : EuclideanSpace ℝ (Fin 3)) 1)]
  rw [← sq_eq_sq₀ (norm_nonneg _) (Real.sqrt_nonneg _), Real.sq_sqrt hr,
    Complex.sq_norm, Complex.normSq_apply, sphereHeight_apply]
  change (p : EuclideanSpace ℝ (Fin 3)) 0 * (p : EuclideanSpace ℝ (Fin 3)) 0 +
    (p : EuclideanSpace ℝ (Fin 3)) 1 * (p : EuclideanSpace ℝ (Fin 3)) 1 = _
  nlinarith [hs]

/-- The actual cylinder coordinates cover exactly the complement of the two poles. -/
theorem range_cylinderMap :
    Set.range cylinderMap = {p : RotationalSphere | sphereHeight p ∈ Ioo (-1 : ℝ) 1} := by
  ext p
  constructor
  · rintro ⟨q, rfl⟩
    change sphereHeight (cylinderMap q) ∈ Ioo (-1 : ℝ) 1
    rw [sphereHeight_cylinderMap]
    exact q.property
  · intro hp
    let q : cylinderDomain :=
      ⟨WithLp.toLp 2 ![sphereHeight p, (planarCoordinate p).arg], hp⟩
    refine ⟨q, ?_⟩
    apply Subtype.ext
    rw [cylinderMap_coe]
    ext i
    fin_cases i
    · change Real.sqrt (1 - sphereHeight p ^ 2) * Real.cos (planarCoordinate p).arg = _
      rw [← norm_planarCoordinate]
      exact Complex.norm_mul_cos_arg _
    · change Real.sqrt (1 - sphereHeight p ^ 2) * Real.sin (planarCoordinate p).arg = _
      rw [← norm_planarCoordinate]
      exact Complex.norm_mul_sin_arg _
    · exact sphereHeight_apply p

private theorem height_endpoint_fiber_subsingleton (t : ℝ) (ht : t ^ 2 = 1) :
    Set.Subsingleton {p : RotationalSphere | sphereHeight p = t} := by
  intro p hp q hq
  have hp2 : (p : EuclideanSpace ℝ (Fin 3)) 2 = t := by
    simpa only [mem_ofPred_eq, sphereHeight_apply] using hp
  have hq2 : (q : EuclideanSpace ℝ (Fin 3)) 2 = t := by
    simpa only [mem_ofPred_eq, sphereHeight_apply] using hq
  have hsp := sphere_coord_sq_sum p
  have hsq := sphere_coord_sq_sum q
  rw [hp2, ht] at hsp
  rw [hq2, ht] at hsq
  have hp0 : (p : EuclideanSpace ℝ (Fin 3)) 0 = 0 := by nlinarith
  have hp1 : (p : EuclideanSpace ℝ (Fin 3)) 1 = 0 := by nlinarith
  have hq0 : (q : EuclideanSpace ℝ (Fin 3)) 0 = 0 := by nlinarith
  have hq1 : (q : EuclideanSpace ℝ (Fin 3)) 1 = 0 := by nlinarith
  apply Subtype.ext
  ext i
  fin_cases i
  · exact hp0.trans hq0.symm
  · exact hp1.trans hq1.symm
  · exact hp2.trans hq2.symm

private theorem sphere_punctured_nhds_neBot (p : RotationalSphere) :
    Filter.NeBot (𝓝[≠] p) := by
  constructor
  intro hbot
  have ho : IsOpen ({p} : Set RotationalSphere) :=
    (isOpen_singleton_iff_punctured_nhds p).mpr hbot
  have hsub : ({p} : Set RotationalSphere) ⊆
      (chartAt (EuclideanSpace ℝ (Fin 2)) p).source := by
    simpa only [singleton_subset_iff] using mem_chart_source (EuclideanSpace ℝ (Fin 2)) p
  have him := (chartAt (EuclideanSpace ℝ (Fin 2)) p).isOpen_image_of_subset_source ho hsub
  simp only [image_singleton] at him
  have he := (isOpen_singleton_iff_punctured_nhds _).mp him
  have hne : Filter.NeBot (𝓝[≠] (chartAt (EuclideanSpace ℝ (Fin 2)) p p)) := inferInstance
  exact hne.ne he

/-- The height-cylinder coordinates have dense image in the entire sphere. -/
theorem denseRange_cylinderMap : DenseRange cylinderMap := by
  have hs := (height_endpoint_fiber_subsingleton (-1) (by norm_num)).finite
  have hn := (height_endpoint_fiber_subsingleton 1 (by norm_num)).finite
  have hf : ((Set.range cylinderMap)ᶜ).Finite := by
    apply (hs.union hn).subset
    intro p hp
    rw [range_cylinderMap] at hp
    have hz := sphereHeight_mem_Icc p
    simp only [mem_compl_iff, mem_ofPred_eq, mem_Ioo] at hp
    change sphereHeight p = -1 ∨ sphereHeight p = 1
    rcases eq_or_lt_of_le hz.1 with h | h
    · exact Or.inl h.symm
    · exact Or.inr (le_antisymm hz.2 (le_of_not_gt (fun h' => hp ⟨h, h'⟩)))
  let : ∀ p : RotationalSphere, Filter.NeBot (𝓝[≠] p) := sphere_punctured_nhds_neBot
  have hd := dense_univ.sdiff_finite hf
  change Dense (Set.range cylinderMap)
  simpa using hd

end RicciFlowSharpEstimate.Geometry
