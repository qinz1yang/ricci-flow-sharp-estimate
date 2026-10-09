/-
Copyright (c) 2026 Ziyang Qin. All rights reserved.
No license is granted by this file.
Authors: Ziyang Qin
-/
import RicciFlowSharpEstimate.Geometry.RotationalCurvature
import RicciFlowSharpEstimate.Geometry.RotationalPolarCoordinates

/-!
# Actual curvature bounds and reciprocal-profile bounds

Every physical height is realized by the original sphere map, including both
poles. Thus positive curvature boxes are exactly the reciprocal profile boxes.
-/

namespace RicciFlowSharpEstimate.Geometry.RotationalProfile.PoleData

open DifferentialGeometry DifferentialGeometry.Geometry.Curvature Set
open scoped Manifold

local instance : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 2 + 1) :=
  ⟨finrank_euclideanSpace_fin⟩

/-- Positive bounds for the same metric's Gauss curvature are equivalent to
the reciprocal bounds on the original profile over its full physical interval. -/
theorem curvature_bounds_iff_profile_bounds (D : PoleData) (κ Λ : ℝ)
    (hκ : 0 < κ) (hΛ : 0 < Λ) :
    (∀ x : RotationalSphere, κ ≤ metricScalarAt D.metric x / 2 ∧
      metricScalarAt D.metric x / 2 ≤ Λ) ↔
      ∀ v ∈ Icc (-1 : ℝ) 1, 1 / Λ ≤ D.a v ∧ D.a v ≤ 1 / κ := by
  have hK (x : RotationalSphere) : metricScalarAt D.metric x / 2 =
      1 / D.a (sphereHeight x) := by
    rw [D.metricScalarAt_metric]
    ring
  simp_rw [hK]
  constructor
  · intro hb v hv
    have h := hb (polarSpherePoint (Real.arccos v) 0)
    rw [sphereHeight_polarSpherePoint, Real.cos_arccos hv.1 hv.2] at h
    have ha := D.a_pos v hv
    constructor
    · apply (div_le_iff₀ hΛ).2
      simpa only [mul_comm] using (div_le_iff₀ ha).1 h.2
    · apply (le_div_iff₀ hκ).2
      simpa only [mul_comm] using (le_div_iff₀ ha).1 h.1
  · intro hb x
    have h := hb (sphereHeight x) (sphereHeight_mem_Icc x)
    have ha := D.a_pos _ (sphereHeight_mem_Icc x)
    constructor
    · apply (le_div_iff₀ ha).2
      simpa only [mul_comm] using (le_div_iff₀ hκ).1 h.2
    · apply (div_le_iff₀ ha).2
      simpa only [mul_comm] using (div_le_iff₀ hΛ).1 h.1

end RicciFlowSharpEstimate.Geometry.RotationalProfile.PoleData
