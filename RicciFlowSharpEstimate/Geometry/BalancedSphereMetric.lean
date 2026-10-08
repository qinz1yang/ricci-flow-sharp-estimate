/-
Copyright (c) 2026 Ziyang Qin. All rights reserved.
No license is granted by this file.
Authors: Ziyang Qin
-/
import RicciFlowSharpEstimate.Geometry.RotationalPoleData
import RicciFlowSharpEstimate.Geometry.RotationalSphereMetric

/-!
# Genuine sphere metrics from smooth balanced profiles

The removable pole factors produce a smooth positive metric on the standard unit
two-sphere. Its evaluation law retains the same profile factors and height map.

Adapted from Ziyang Qin's historical `BalancedRotationalSphereMetric.lean`.
-/

noncomputable section

namespace RicciFlowSharpEstimate.Geometry

open DifferentialGeometry DifferentialGeometry.Geometry
open Set
open scoped Manifold ContDiff

local instance : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 2 + 1) :=
  ⟨finrank_euclideanSpace_fin⟩

namespace RotationalProfile.PoleData

/-- The radial coefficient of the reconstructed tensor is exactly `a²/b`. -/
theorem radial_identity (D : PoleData) (z : ℝ) (hz : z ∈ Icc (-1 : ℝ) 1) :
    D.b z + D.c z / D.b z * (1 - z ^ 2) = D.a z ^ 2 / D.b z := by
  have hb := (D.b_pos z hz).ne'
  have hf := D.radial_factor z
  field_simp [hb]
  nlinarith

/-- The actual smooth height coefficients of the reconstructed sphere metric. -/
def coefficients (D : PoleData) : HeightMetricCoefficients where
  b := fun x => D.b (sphereHeight x)
  q := fun x => D.c (sphereHeight x) / D.b (sphereHeight x)
  b_contMDiff := D.b_contDiff.comp_contMDiff sphereHeight_contMDiff
  q_contMDiff := (D.c_contDiff.comp_contMDiff sphereHeight_contMDiff).div₀
    (D.b_contDiff.comp_contMDiff sphereHeight_contMDiff)
    (fun x => (D.b_pos _ (sphereHeight_mem_Icc x)).ne')
  b_pos := fun x => D.b_pos _ (sphereHeight_mem_Icc x)
  radial_pos := fun x => by
    rw [D.radial_identity _ (sphereHeight_mem_Icc x)]
    exact div_pos (sq_pos_of_pos (D.a_pos _ (sphereHeight_mem_Icc x)))
      (D.b_pos _ (sphereHeight_mem_Icc x))

/-- The actual smooth Riemannian metric on the closed unit two-sphere. -/
def metric (D : PoleData) : SmoothRiemannianMetric (𝓡 2) RotationalSphere :=
  D.coefficients.metric

/-- The produced metric is the specified rank-one correction of the round metric. -/
theorem metric_inner (D : PoleData) (x : RotationalSphere)
    (v w : TangentSpace (𝓡 2) x) :
    D.metric.inner x v w =
      D.b (sphereHeight x) * HeightMetricCoefficients.round.inner x v w +
        D.c (sphereHeight x) / D.b (sphereHeight x) *
          (heightOneForm x (fun _ : Fin 1 => v) * heightOneForm x (fun _ : Fin 1 => w)) :=
  D.coefficients.metric_inner_apply x v w

/-- Constant positive profiles produce exactly the corresponding multiple
of the actual round metric, on every pair of tangent vectors. -/
theorem constant_metric_inner (r : ℝ) (hr : 0 < r) (x : RotationalSphere)
    (v w : TangentSpace (𝓡 2) x) :
    (constant r hr).metric.inner x v w = r * HeightMetricCoefficients.round.inner x v w := by
  rw [metric_inner]
  simp [constant]

end RotationalProfile.PoleData

/-- Every globally smooth positive balanced profile produces a genuine smooth
sphere metric, retaining the original profile, both pole values and the metric's
identity with the explicit constructor. -/
theorem exists_metric_of_smooth_positive_balanced_profile (a : ℝ → ℝ)
    (ha : ContDiff ℝ ∞ a) (haPos : ∀ z ∈ Icc (-1 : ℝ) 1, 0 < a z)
    (hBalance : RotationalProfile.balance a = 0) :
    ∃ (D : RotationalProfile.PoleData) (g : SmoothRiemannianMetric (𝓡 2) RotationalSphere),
      D.a = a ∧ D.b (-1) = a (-1) ∧ D.b 1 = a 1 ∧ g = D.metric := by
  obtain ⟨D, hDa, hSouth, hNorth⟩ := RotationalProfile.exists_poleData a ha haPos hBalance
  exact ⟨D, D.metric, hDa, hSouth, hNorth, rfl⟩

end RicciFlowSharpEstimate.Geometry
