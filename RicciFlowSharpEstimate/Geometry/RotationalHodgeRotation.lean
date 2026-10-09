/-
Copyright (c) 2026 Ziyang Qin. All rights reserved.
No license is granted by this file.
Authors: Ziyang Qin
-/
import RicciFlowSharpEstimate.Geometry.RotationalAreaForm
import RicciFlowSharpEstimate.Geometry.RotationalCometric

/-!
# Actual area rotation of the two rotational one-form families

Contraction of the outward area form with the metric dual of a meridional
one-form gives the negative azimuthal one-form. The sign follows from the actual
ambient determinant and the actual round height gradient, including at the poles.

The calculation adapts Ziyang Qin's historical `RotationalZonalHodgeStar.lean`.
-/

noncomputable section

namespace RicciFlowSharpEstimate.Geometry

open Bundle DifferentialGeometry DifferentialGeometry.Geometry
open DifferentialGeometry.Geometry.Operator DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Tensor0SBundle Metric
open scoped Manifold ContDiff RealInnerProductSpace

local instance : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 2 + 1) :=
  ⟨finrank_euclideanSpace_fin⟩

/-- The genuine round gradient of height is the ambient tangent projection of the height axis. -/
theorem dIncl_round_grad_sphereHeight (x : RotationalSphere) :
    dIncl (n := 2) x (gradFun HeightMetricCoefficients.round sphereHeight x) =
      EuclideanSpace.single (2 : Fin 3) (1 : ℝ) -
        sphereHeight x • (x : EuclideanSpace ℝ (Fin 3)) := by
  let e : EuclideanSpace ℝ (Fin 3) := EuclideanSpace.single (2 : Fin 3) (1 : ℝ)
  let P : EuclideanSpace ℝ (Fin 3) := e - sphereHeight x • (x : EuclideanSpace ℝ (Fin 3))
  have hex : ⟪e, (x : EuclideanSpace ℝ (Fin 3))⟫ = sphereHeight x := rfl
  have hxe : ⟪(x : EuclideanSpace ℝ (Fin 3)), e⟫ = sphereHeight x := by
    rw [real_inner_comm, hex]
  have hxx : ⟪(x : EuclideanSpace ℝ (Fin 3)), (x : EuclideanSpace ℝ (Fin 3))⟫ = 1 := by
    rw [real_inner_self_eq_norm_sq, norm_eq_of_mem_sphere x]
    norm_num
  have hP : P ∈ (ℝ ∙ (x : EuclideanSpace ℝ (Fin 3)))ᗮ := by
    apply Submodule.mem_orthogonal_singleton_iff_inner_right.mpr
    simp only [P, inner_sub_right, real_inner_smul_right, hxe, hxx, mul_one, sub_self]
  let Z : TangentSpace (𝓡 2) x := (dInclEquiv (n := 2) x).symm ⟨P, hP⟩
  have hZ : dIncl (n := 2) x Z = P := by
    rw [← dInclEquiv_coe (n := 2) x]
    exact congrArg Subtype.val ((dInclEquiv (n := 2) x).apply_symm_apply ⟨P, hP⟩)
  have hGrad : Z = gradFun HeightMetricCoefficients.round sphereHeight x := by
    apply metricFlatLinear_injective HeightMetricCoefficients.round x
    ext v
    change HeightMetricCoefficients.round.inner x Z v =
      HeightMetricCoefficients.round.inner x
        (gradFun HeightMetricCoefficients.round sphereHeight x) v
    rw [inner_gradFun, roundMetric_inner, hZ]
    have hv : ⟪(x : EuclideanSpace ℝ (Fin 3)), dIncl (n := 2) x v⟫ = 0 := by
      apply Submodule.mem_orthogonal_singleton_iff_inner_right.mp
      rw [← range_mvfderiv_subtypeVal (n := 2) x]
      exact ⟨v, rfl⟩
    rw [show sphereHeight = ⇑(innerCoordFun (n := 2) e) from rfl,
      mfderiv_innerCoordFun]
    simp only [P, inner_sub_left, real_inner_smul_left, hv, mul_zero, sub_zero]
  rw [← hGrad]
  exact hZ

/-- Contracting outward round area with the round height gradient gives minus the angular form. -/
theorem roundSphereAreaForm_round_grad_sphereHeight (x : RotationalSphere)
    (v : TangentSpace (𝓡 2) x) :
    roundSphereAreaForm x (vec2 (gradFun HeightMetricCoefficients.round sphereHeight x) v) =
      -sphereAzimuthalOneForm x (fun _ : Fin 1 => v) := by
  rw [roundSphereAreaForm_apply, sphereAzimuthalOneForm_apply, dIncl_round_grad_sphereHeight]
  simp [EuclideanSpace.single, sphereHeight_apply]
  ring

/-- The actual metric dual of the accepted meridional form is the scaled round height gradient. -/
theorem RotationalProfile.PoleData.inverseMetricSharpFib_meridionalOneForm
    (D : RotationalProfile.PoleData) (r : ℝ → ℝ) (hr : ContDiff ℝ ∞ r)
    (x : RotationalSphere) :
    inverseMetricSharpFib D.metric x (D.meridionalOneForm r hr x) =
      ((D.b (sphereHeight x) / D.a (sphereHeight x)) * r (sphereHeight x)) •
        gradFun HeightMetricCoefficients.round sphereHeight x := by
  change inverseMetricSharpFib D.metric x
    ((D.a (sphereHeight x) * r (sphereHeight x)) • heightOneForm x) = _
  rw [map_smul, D.inverseMetricSharpFib_heightOneForm, smul_smul]
  congr 1
  field_simp [(D.a_pos _ (sphereHeight_mem_Icc x)).ne']

private theorem tensor2_smul_left {x : RotationalSphere}
    (A : Tensor0SSpace (𝕜 := ℝ) (I := 𝓡 2) (M := RotationalSphere) 2 x)
    (c : ℝ) (u v : TangentSpace (𝓡 2) x) :
    A (vec2 (c • u) v) = c * A (vec2 u v) := by
  have h := Tensor0SSpace.map_update_smul (I := 𝓡 2) A (vec2 u v) 0 c u
  have h0 : Function.update (vec2 (I := 𝓡 2) u v) 0 (c • u) = vec2 (c • u) v := by
    funext i
    fin_cases i <;> simp [vec2, Function.update]
  have h1 : Function.update (vec2 (I := 𝓡 2) u v) 0 u = vec2 u v := by
    funext i
    fin_cases i <;> simp [vec2, Function.update]
  rwa [h0, h1, smul_eq_mul] at h

/-- The actual outward metric area rotation sends every meridional form
to minus its azimuthal form. -/
theorem RotationalProfile.PoleData.areaForm_inverseMetricSharpFib_meridionalOneForm
    (D : RotationalProfile.PoleData) (r : ℝ → ℝ) (hr : ContDiff ℝ ∞ r)
    (x : RotationalSphere) (v : TangentSpace (𝓡 2) x) :
    D.areaForm x (vec2 (inverseMetricSharpFib D.metric x (D.meridionalOneForm r hr x)) v) =
      -D.azimuthalOneForm r hr x (fun _ : Fin 1 => v) := by
  rw [D.inverseMetricSharpFib_meridionalOneForm, D.areaForm_apply, tensor2_smul_left,
    roundSphereAreaForm_round_grad_sphereHeight, D.azimuthalOneForm_apply]
  field_simp [(D.a_pos _ (sphereHeight_mem_Icc x)).ne']

end RicciFlowSharpEstimate.Geometry
