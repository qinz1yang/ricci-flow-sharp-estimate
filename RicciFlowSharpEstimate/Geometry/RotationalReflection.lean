/-
Copyright (c) 2026 Ziyang Qin. All rights reserved.
No license is granted by this file.
Authors: Ziyang Qin
-/
import RicciFlowSharpEstimate.Geometry.RotationalOneForms
import DifferentialGeometry.Geometry.Metric.Sphere.Isometry.OrthogonalAction

/-!
# Actual meridian reflection of the rotational sphere

The ambient orthogonal reflection `(x,y,z) ↦ (x,-y,z)` preserves the accepted
rotational metric. Its genuine derivative fixes meridional one-forms and reverses
azimuthal one-forms, with no equatorial symmetry assumption on the profile.

The construction adapts Ziyang Qin's historical `HeightAxisMeridianReflection.lean`
and `BalancedRotationalSphereSymmetry.lean` to the pinned geometric producers.
-/

noncomputable section

namespace RicciFlowSharpEstimate.Geometry

open DifferentialGeometry DifferentialGeometry.Geometry
open scoped Manifold ContDiff RealInnerProductSpace

local instance : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 2 + 1) :=
  ⟨finrank_euclideanSpace_fin⟩

private theorem fixed_height_coordinate
    (e : EuclideanSpace ℝ (Fin 3) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 3))
    (he : e (EuclideanSpace.single (2 : Fin 3) (1 : ℝ)) =
      EuclideanSpace.single (2 : Fin 3) (1 : ℝ))
    (v : EuclideanSpace ℝ (Fin 3)) : (e v) 2 = v 2 := by
  have h := e.inner_map_map (EuclideanSpace.single (2 : Fin 3) (1 : ℝ)) v
  rw [he] at h
  simpa only [EuclideanSpace.inner_single_left, map_one, one_mul] using h

/-- An actual ambient orthogonal map fixing the height axis preserves sphere height. -/
theorem sphereHeight_sphereDiffeo
    (e : EuclideanSpace ℝ (Fin 3) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 3))
    (he : e (EuclideanSpace.single (2 : Fin 3) (1 : ℝ)) =
      EuclideanSpace.single (2 : Fin 3) (1 : ℝ))
    (x : RotationalSphere) : sphereHeight (sphereDiffeo (n := 2) e x) = sphereHeight x := by
  rw [sphereHeight_apply, sphereDiffeo_coe, sphereHeight_apply]
  exact fixed_height_coordinate e he x

/-- The actual derivative of a fixed-height orthogonal action preserves the height covector. -/
theorem heightOneForm_sphereDiffeo
    (e : EuclideanSpace ℝ (Fin 3) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 3))
    (he : e (EuclideanSpace.single (2 : Fin 3) (1 : ℝ)) =
      EuclideanSpace.single (2 : Fin 3) (1 : ℝ))
    (x : RotationalSphere) (v : TangentSpace (𝓡 2) x) :
    heightOneForm (sphereDiffeo (n := 2) e x) (fun _ : Fin 1 =>
      mfderiv (𝓡 2) (𝓡 2) (sphereDiffeo (n := 2) e) x v) =
        heightOneForm x (fun _ : Fin 1 => v) := by
  rw [heightOneForm_apply_dIncl, heightOneForm_apply_dIncl, mfderiv_incl_sphereDiffeo]
  exact fixed_height_coordinate e he _

/-- Every ambient orthogonal map fixing the height axis preserves the same accepted metric. -/
theorem RotationalProfile.PoleData.metric_inner_sphereDiffeo (D : RotationalProfile.PoleData)
    (e : EuclideanSpace ℝ (Fin 3) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 3))
    (he : e (EuclideanSpace.single (2 : Fin 3) (1 : ℝ)) =
      EuclideanSpace.single (2 : Fin 3) (1 : ℝ))
    (x : RotationalSphere) (v w : TangentSpace (𝓡 2) x) :
    D.metric.inner (sphereDiffeo (n := 2) e x)
        (mfderiv (𝓡 2) (𝓡 2) (sphereDiffeo (n := 2) e) x v)
        (mfderiv (𝓡 2) (𝓡 2) (sphereDiffeo (n := 2) e) x w) =
      D.metric.inner x v w := by
  have hround : HeightMetricCoefficients.round.inner (sphereDiffeo (n := 2) e x)
      (mfderiv (𝓡 2) (𝓡 2) (sphereDiffeo (n := 2) e) x v)
      (mfderiv (𝓡 2) (𝓡 2) (sphereDiffeo (n := 2) e) x w) =
      HeightMetricCoefficients.round.inner x v w := roundInner_sphereDiffeo e x v w
  rw [D.metric_inner, D.metric_inner, sphereHeight_sphereDiffeo e he,
    heightOneForm_sphereDiffeo e he, heightOneForm_sphereDiffeo e he, hround]

/-- Pulling the metric back by any fixed-height ambient orthogonal action gives that metric. -/
theorem RotationalProfile.PoleData.pullbackMetric_sphereDiffeo (D : RotationalProfile.PoleData)
    (e : EuclideanSpace ℝ (Fin 3) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 3))
    (he : e (EuclideanSpace.single (2 : Fin 3) (1 : ℝ)) =
      EuclideanSpace.single (2 : Fin 3) (1 : ℝ)) :
    Diffeomorph.pullbackMetric D.metric (sphereDiffeo (n := 2) e) = D.metric := by
  apply SmoothRiemannianMetric.ext_inner
  intro x v w
  rw [Diffeomorph.pullbackMetric_inner]
  exact D.metric_inner_sphereDiffeo e he x v w

/-- Reflection in the actual ambient meridian `y = 0`, as a native orthogonal equivalence. -/
def meridianReflection :
    EuclideanSpace ℝ (Fin 3) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 3) where
  toLinearEquiv :=
    { toFun := fun x => WithLp.toLp 2 ![x 0, -x 1, x 2]
      invFun := fun x => WithLp.toLp 2 ![x 0, -x 1, x 2]
      left_inv := by intro x; ext i; fin_cases i <;> simp
      right_inv := by intro x; ext i; fin_cases i <;> simp
      map_add' := by
        intro x y
        ext i
        fin_cases i <;> simp
        all_goals ring
      map_smul' := by intro c x; ext i; fin_cases i <;> simp }
  norm_map' := by
    intro x
    rw [← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _),
      EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq]
    simp [Fin.sum_univ_succ]

/-- The orthogonal equivalence retains its literal ambient reflection formula. -/
@[simp] theorem meridianReflection_apply (x : EuclideanSpace ℝ (Fin 3)) :
    meridianReflection x = WithLp.toLp 2 ![x 0, -x 1, x 2] := rfl

/-- The reflection fixes the designated height axis. -/
theorem meridianReflection_fix_heightAxis :
    meridianReflection (EuclideanSpace.single (2 : Fin 3) (1 : ℝ)) =
      EuclideanSpace.single (2 : Fin 3) (1 : ℝ) := by
  ext i
  fin_cases i <;> simp

/-- The genuine smooth meridian reflection of the actual unit sphere. -/
def meridianReflectionSphereDiffeo : RotationalSphere ≃ₘ⟮𝓡 2, 𝓡 2⟯ RotationalSphere :=
  sphereDiffeo (n := 2) meridianReflection

/-- The sphere map retains the exact coordinate normalization `(x,y,z) ↦ (x,-y,z)`. -/
@[simp] theorem meridianReflectionSphereDiffeo_coe (x : RotationalSphere) :
    (meridianReflectionSphereDiffeo x : EuclideanSpace ℝ (Fin 3)) =
      WithLp.toLp 2 ![(x : EuclideanSpace ℝ (Fin 3)) 0,
        -(x : EuclideanSpace ℝ (Fin 3)) 1, (x : EuclideanSpace ℝ (Fin 3)) 2] := rfl

/-- Reflection on the sphere is an actual involution. -/
theorem meridianReflectionSphereDiffeo_involutive (x : RotationalSphere) :
    meridianReflectionSphereDiffeo (meridianReflectionSphereDiffeo x) = x := by
  apply Subtype.ext
  ext i
  fin_cases i <;> simp

/-- The derivative is exactly the ambient reflection on genuine included tangent vectors. -/
theorem meridianReflectionSphereDiffeo_dIncl_mfderiv (x : RotationalSphere)
    (v : TangentSpace (𝓡 2) x) :
    dIncl (n := 2) (meridianReflectionSphereDiffeo x)
        (mfderiv (𝓡 2) (𝓡 2) meridianReflectionSphereDiffeo x v) =
      meridianReflection (dIncl (n := 2) x v) :=
  mfderiv_incl_sphereDiffeo meridianReflection x v

/-- Meridian reflection preserves height, with no profile parity hypothesis. -/
@[simp] theorem sphereHeight_meridianReflectionSphereDiffeo (x : RotationalSphere) :
    sphereHeight (meridianReflectionSphereDiffeo x) = sphereHeight x :=
  sphereHeight_sphereDiffeo meridianReflection meridianReflection_fix_heightAxis x

/-- The same accepted sphere metric is preserved by the genuine reflection derivative. -/
theorem RotationalProfile.PoleData.metric_inner_meridianReflectionSphereDiffeo
    (D : RotationalProfile.PoleData) (x : RotationalSphere) (v w : TangentSpace (𝓡 2) x) :
    D.metric.inner (meridianReflectionSphereDiffeo x)
        (mfderiv (𝓡 2) (𝓡 2) meridianReflectionSphereDiffeo x v)
        (mfderiv (𝓡 2) (𝓡 2) meridianReflectionSphereDiffeo x w) =
      D.metric.inner x v w :=
  D.metric_inner_sphereDiffeo meridianReflection meridianReflection_fix_heightAxis x v w

/-- Meridian reflection is an isometry of the actual profile metric. -/
theorem RotationalProfile.PoleData.pullbackMetric_meridianReflectionSphereDiffeo
    (D : RotationalProfile.PoleData) :
    Diffeomorph.pullbackMetric D.metric meridianReflectionSphereDiffeo = D.metric :=
  D.pullbackMetric_sphereDiffeo meridianReflection meridianReflection_fix_heightAxis

/-- The smooth global angular covector changes sign under the genuine reflection derivative. -/
theorem sphereAzimuthalOneForm_meridianReflectionSphereDiffeo (x : RotationalSphere)
    (v : TangentSpace (𝓡 2) x) :
    sphereAzimuthalOneForm (meridianReflectionSphereDiffeo x) (fun _ : Fin 1 =>
        mfderiv (𝓡 2) (𝓡 2) meridianReflectionSphereDiffeo x v) =
      -sphereAzimuthalOneForm x (fun _ : Fin 1 => v) := by
  rw [sphereAzimuthalOneForm_apply, sphereAzimuthalOneForm_apply,
    meridianReflectionSphereDiffeo_dIncl_mfderiv, meridianReflectionSphereDiffeo_coe,
    meridianReflection_apply]
  simp
  ring

/-- Meridian reflection fixes every accepted meridional one-form under actual pullback. -/
theorem RotationalProfile.PoleData.meridionalOneForm_meridianReflectionSphereDiffeo
    (D : RotationalProfile.PoleData) (r : ℝ → ℝ) (hr : ContDiff ℝ ∞ r)
    (x : RotationalSphere) (v : TangentSpace (𝓡 2) x) :
    D.meridionalOneForm r hr (meridianReflectionSphereDiffeo x) (fun _ : Fin 1 =>
        mfderiv (𝓡 2) (𝓡 2) meridianReflectionSphereDiffeo x v) =
      D.meridionalOneForm r hr x (fun _ : Fin 1 => v) := by
  rw [D.meridionalOneForm_apply, D.meridionalOneForm_apply,
    sphereHeight_meridianReflectionSphereDiffeo]
  rw [show meridianReflectionSphereDiffeo = sphereDiffeo (n := 2) meridianReflection from rfl,
    heightOneForm_sphereDiffeo meridianReflection meridianReflection_fix_heightAxis]

/-- Meridian reflection reverses every accepted azimuthal one-form under actual pullback. -/
theorem RotationalProfile.PoleData.azimuthalOneForm_meridianReflectionSphereDiffeo
    (D : RotationalProfile.PoleData) (r : ℝ → ℝ) (hr : ContDiff ℝ ∞ r)
    (x : RotationalSphere) (v : TangentSpace (𝓡 2) x) :
    D.azimuthalOneForm r hr (meridianReflectionSphereDiffeo x) (fun _ : Fin 1 =>
        mfderiv (𝓡 2) (𝓡 2) meridianReflectionSphereDiffeo x v) =
      -D.azimuthalOneForm r hr x (fun _ : Fin 1 => v) := by
  rw [D.azimuthalOneForm_apply, D.azimuthalOneForm_apply,
    sphereHeight_meridianReflectionSphereDiffeo,
    sphereAzimuthalOneForm_meridianReflectionSphereDiffeo]
  ring

end RicciFlowSharpEstimate.Geometry
