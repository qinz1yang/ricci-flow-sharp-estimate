/-
Copyright (c) 2026 Ziyang Qin. All rights reserved.
No license is granted by this file.
Authors: Ziyang Qin
-/
import RicciFlowSharpEstimate.Geometry.RotationalReflection

/-!
# The isometric circle action on the rotational sphere

The native unit circle acts by rotation in the first two ambient coordinates and
fixes height. The real-angle action is jointly smooth on the whole sphere, including
the poles, and preserves the same accepted rotational metric.

The coordinate construction adapts Ziyang Qin's historical
`HeightAxisCircleRotation.lean` and `HeightAxisAngleRotation.lean`.
-/

noncomputable section

namespace RicciFlowSharpEstimate.Geometry

open DifferentialGeometry DifferentialGeometry.Geometry
open scoped Manifold ContDiff

local instance : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 2 + 1) :=
  ⟨finrank_euclideanSpace_fin⟩

private def axisRotationFun (z : Circle) (x : EuclideanSpace ℝ (Fin 3)) :
    EuclideanSpace ℝ (Fin 3) :=
  WithLp.toLp 2 ![z.1.re * x 0 - z.1.im * x 1,
    z.1.im * x 0 + z.1.re * x 1, x 2]

private theorem axisRotationFun_inv_apply (z : Circle) (x : EuclideanSpace ℝ (Fin 3)) :
    axisRotationFun z⁻¹ (axisRotationFun z x) = x := by
  have hz : z.1.re * z.1.re + z.1.im * z.1.im = 1 := by
    simpa [Complex.normSq_apply] using Circle.normSq_coe z
  ring_nf at hz
  ext i
  fin_cases i
  · have hx := congrArg (fun t : ℝ => t * x 0) hz
    simp [axisRotationFun]
    ring_nf at hx ⊢
    exact hx
  · have hx := congrArg (fun t : ℝ => t * x 1) hz
    simp [axisRotationFun]
    ring_nf at hx ⊢
    linarith
  · simp [axisRotationFun]

private theorem axisRotationFun_norm (z : Circle) (x : EuclideanSpace ℝ (Fin 3)) :
    ‖axisRotationFun z x‖ = ‖x‖ := by
  have hz : z.1.re ^ 2 + z.1.im ^ 2 = 1 := by
    simpa [Complex.normSq_apply, pow_two] using Circle.normSq_coe z
  rw [← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _),
    EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq]
  simp [axisRotationFun, Fin.sum_univ_succ]
  ring_nf at hz ⊢
  have hx0 := congrArg (fun t : ℝ => t * (x 0) ^ 2) hz
  have hx1 := congrArg (fun t : ℝ => t * (x 1) ^ 2) hz
  ring_nf at hx0 hx1 ⊢
  linarith

/-- Ambient orthogonal rotation by the native unit complex number `z`. -/
def axisRotation (z : Circle) :
    EuclideanSpace ℝ (Fin 3) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 3) where
  toLinearEquiv :=
    { toFun := axisRotationFun z
      invFun := axisRotationFun z⁻¹
      left_inv := axisRotationFun_inv_apply z
      right_inv x := by simpa only [inv_inv] using axisRotationFun_inv_apply z⁻¹ x
      map_add' := by
        intro x y
        ext i
        fin_cases i <;> simp [axisRotationFun] <;> ring
      map_smul' := by
        intro c x
        ext i
        fin_cases i <;> simp [axisRotationFun] <;> ring }
  norm_map' := axisRotationFun_norm z

/-- The ambient rotation has its literal coordinate formula. -/
@[simp] theorem axisRotation_apply (z : Circle) (x : EuclideanSpace ℝ (Fin 3)) :
    axisRotation z x = WithLp.toLp 2 ![z.1.re * x 0 - z.1.im * x 1,
      z.1.im * x 0 + z.1.re * x 1, x 2] := rfl

/-- The orthogonal rotations form a representation of the native circle group. -/
def axisRotationRepresentation :
    Circle →* (EuclideanSpace ℝ (Fin 3) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 3)) where
  toFun := axisRotation
  map_one' := by
    ext x i
    fin_cases i <;> simp
  map_mul' z w := by
    ext x i
    fin_cases i <;> simp <;> ring

/-- The representation is the explicit orthogonal rotation. -/
@[simp] theorem axisRotationRepresentation_apply (z : Circle) :
    axisRotationRepresentation z = axisRotation z := rfl

/-- Multiplication in the circle composes the actual ambient rotations. -/
theorem axisRotation_mul_apply (z w : Circle) (x : EuclideanSpace ℝ (Fin 3)) :
    axisRotation (z * w) x = axisRotation z (axisRotation w x) := by
  exact congrArg (fun e => e x) (axisRotationRepresentation.map_mul z w)

/-- The ambient derivative is exactly the same orthogonal linear map. -/
theorem axisRotation_fderiv (z : Circle) (x : EuclideanSpace ℝ (Fin 3)) :
    fderiv ℝ (axisRotation z) x = (axisRotation z).toContinuousLinearMap :=
  (axisRotation z).fderiv

/-- Every rotation fixes the height axis. -/
theorem axisRotation_fix_heightAxis (z : Circle) :
    axisRotation z (EuclideanSpace.single (2 : Fin 3) (1 : ℝ)) =
      EuclideanSpace.single (2 : Fin 3) (1 : ℝ) := by
  ext i
  fin_cases i <;> simp

/-- The induced genuine diffeomorphism of the accepted unit sphere. -/
def circleSphereDiffeo (z : Circle) : RotationalSphere ≃ₘ⟮𝓡 2, 𝓡 2⟯ RotationalSphere :=
  sphereDiffeo (n := 2) (axisRotation z)

/-- The sphere action retains its actual ambient map. -/
@[simp] theorem circleSphereDiffeo_coe (z : Circle) (x : RotationalSphere) :
    (circleSphereDiffeo z x : EuclideanSpace ℝ (Fin 3)) =
      axisRotation z (x : EuclideanSpace ℝ (Fin 3)) := rfl

/-- The circle identity acts as the identity on the sphere. -/
@[simp] theorem circleSphereDiffeo_one (x : RotationalSphere) :
    circleSphereDiffeo 1 x = x := by
  apply Subtype.ext
  ext i
  fin_cases i <;> simp

/-- The native circle group law holds for the sphere action. -/
theorem circleSphereDiffeo_mul (z w : Circle) (x : RotationalSphere) :
    circleSphereDiffeo (z * w) x = circleSphereDiffeo z (circleSphereDiffeo w x) := by
  apply Subtype.ext
  exact axisRotation_mul_apply z w x

/-- The explicit sphere rotations give a native action of the circle group. -/
@[instance_reducible] def circleSphereAction : MulAction Circle RotationalSphere where
  smul z x := circleSphereDiffeo z x
  one_smul := circleSphereDiffeo_one
  mul_smul := circleSphereDiffeo_mul

/-- Inverse circle elements give inverse diffeomorphisms. -/
@[simp] theorem circleSphereDiffeo_inv (z : Circle) :
    circleSphereDiffeo z⁻¹ = (circleSphereDiffeo z).symm := by
  apply Diffeomorph.ext
  intro x
  apply (circleSphereDiffeo z).injective
  change circleSphereDiffeo z (circleSphereDiffeo z⁻¹ x) =
    circleSphereDiffeo z ((circleSphereDiffeo z).symm x)
  rw [Diffeomorph.apply_symm_apply, ← circleSphereDiffeo_mul]
  simp

/-- The derivative of the action is the ambient rotation on included tangent vectors. -/
theorem circleSphereDiffeo_dIncl_mfderiv (z : Circle) (x : RotationalSphere)
    (v : TangentSpace (𝓡 2) x) :
    dIncl (n := 2) (circleSphereDiffeo z x)
        (mfderiv (𝓡 2) (𝓡 2) (circleSphereDiffeo z) x v) =
      axisRotation z (dIncl (n := 2) x v) :=
  mfderiv_incl_sphereDiffeo (axisRotation z) x v

/-- Rotation preserves the height coordinate on the whole sphere. -/
@[simp] theorem sphereHeight_circleSphereDiffeo (z : Circle) (x : RotationalSphere) :
    sphereHeight (circleSphereDiffeo z x) = sphereHeight x :=
  sphereHeight_sphereDiffeo (axisRotation z) (axisRotation_fix_heightAxis z) x

/-- The action's actual tangent derivative preserves the accepted metric. -/
theorem RotationalProfile.PoleData.metric_inner_circleSphereDiffeo
    (D : RotationalProfile.PoleData) (z : Circle) (x : RotationalSphere)
    (v w : TangentSpace (𝓡 2) x) :
    D.metric.inner (circleSphereDiffeo z x)
        (mfderiv (𝓡 2) (𝓡 2) (circleSphereDiffeo z) x v)
        (mfderiv (𝓡 2) (𝓡 2) (circleSphereDiffeo z) x w) = D.metric.inner x v w :=
  D.metric_inner_sphereDiffeo (axisRotation z) (axisRotation_fix_heightAxis z) x v w

/-- Pullback by the circle action preserves the same accepted rotational metric. -/
theorem RotationalProfile.PoleData.pullbackMetric_circleSphereDiffeo
    (D : RotationalProfile.PoleData) (z : Circle) :
    Diffeomorph.pullbackMetric D.metric (circleSphereDiffeo z) = D.metric :=
  D.pullbackMetric_sphereDiffeo (axisRotation z) (axisRotation_fix_heightAxis z)

/-- Rotation through a real angle, using the native circle exponential. -/
def angleRotation (theta : ℝ) : RotationalSphere ≃ₘ⟮𝓡 2, 𝓡 2⟯ RotationalSphere :=
  circleSphereDiffeo (Circle.exp theta)

/-- The real-angle parametrization is the native circle action. -/
theorem angleRotation_eq (theta : ℝ) :
    angleRotation theta = circleSphereDiffeo (Circle.exp theta) := rfl

/-- Zero angle gives the identity. -/
@[simp] theorem angleRotation_zero (x : RotationalSphere) : angleRotation 0 x = x := by
  simp [angleRotation]

/-- Angle addition composes the actual rotations. -/
theorem angleRotation_add (theta phi : ℝ) (x : RotationalSphere) :
    angleRotation (theta + phi) x = angleRotation theta (angleRotation phi x) := by
  simp only [angleRotation, Circle.exp_add, circleSphereDiffeo_mul]

/-- Negating an angle inverts the actual rotation diffeomorphism. -/
@[simp] theorem angleRotation_neg (theta : ℝ) :
    angleRotation (-theta) = (angleRotation theta).symm := by
  simp [angleRotation]

/-- The actual diffeomorphism family has period `2*pi`. -/
theorem angleRotation_periodic : Function.Periodic angleRotation (2 * Real.pi) := by
  intro theta
  apply congrArg circleSphereDiffeo
  apply Subtype.ext
  simpa only [Circle.coe_exp, Complex.ofReal_add, Complex.ofReal_mul,
    Complex.ofReal_ofNat] using Complex.exp_mul_I_periodic (theta : ℂ)

/-- The angle derivative on included tangent vectors is the stated ambient rotation. -/
theorem angleRotation_dIncl_mfderiv (theta : ℝ) (x : RotationalSphere)
    (v : TangentSpace (𝓡 2) x) :
    dIncl (n := 2) (angleRotation theta x)
        (mfderiv (𝓡 2) (𝓡 2) (angleRotation theta) x v) =
      axisRotation (Circle.exp theta) (dIncl (n := 2) x v) :=
  circleSphereDiffeo_dIncl_mfderiv (Circle.exp theta) x v

/-- The actual angle derivative preserves the accepted metric inner product. -/
theorem RotationalProfile.PoleData.metric_inner_angleRotation
    (D : RotationalProfile.PoleData) (theta : ℝ) (x : RotationalSphere)
    (v w : TangentSpace (𝓡 2) x) :
    D.metric.inner (angleRotation theta x)
        (mfderiv (𝓡 2) (𝓡 2) (angleRotation theta) x v)
        (mfderiv (𝓡 2) (𝓡 2) (angleRotation theta) x w) = D.metric.inner x v w :=
  D.metric_inner_circleSphereDiffeo (Circle.exp theta) x v w

/-- Every angle rotation preserves the accepted metric. -/
theorem RotationalProfile.PoleData.pullbackMetric_angleRotation
    (D : RotationalProfile.PoleData) (theta : ℝ) :
    Diffeomorph.pullbackMetric D.metric (angleRotation theta) = D.metric :=
  D.pullbackMetric_circleSphereDiffeo (Circle.exp theta)

private def axisRotationAmbientExtension (p : ℂ × EuclideanSpace ℝ (Fin 3)) :
    EuclideanSpace ℝ (Fin 3) :=
  WithLp.toLp 2 ![p.1.re * p.2 0 - p.1.im * p.2 1,
    p.1.im * p.2 0 + p.1.re * p.2 1, p.2 2]

private theorem axisRotationAmbientExtension_contDiff :
    ContDiff ℝ ∞ axisRotationAmbientExtension := by
  have hx0 : ContDiff ℝ ∞ (fun p : ℂ × EuclideanSpace ℝ (Fin 3) => p.2 0) := by fun_prop
  have hx1 : ContDiff ℝ ∞ (fun p : ℂ × EuclideanSpace ℝ (Fin 3) => p.2 1) := by fun_prop
  have hx2 : ContDiff ℝ ∞ (fun p : ℂ × EuclideanSpace ℝ (Fin 3) => p.2 2) := by fun_prop
  apply contDiff_piLp'
  intro i
  fin_cases i
  · change ContDiff ℝ ∞ (fun p : ℂ × EuclideanSpace ℝ (Fin 3) =>
      p.1.re * p.2 0 - p.1.im * p.2 1)
    exact ((Complex.reCLM.contDiff.comp contDiff_fst).mul hx0).sub
      ((Complex.imCLM.contDiff.comp contDiff_fst).mul hx1)
  · change ContDiff ℝ ∞ (fun p : ℂ × EuclideanSpace ℝ (Fin 3) =>
      p.1.im * p.2 0 + p.1.re * p.2 1)
    exact ((Complex.imCLM.contDiff.comp contDiff_fst).mul hx0).add
      ((Complex.reCLM.contDiff.comp contDiff_fst).mul hx1)
  · exact hx2

/-- The angle action on ambient Euclidean space is jointly smooth. -/
theorem angleAxisRotation_contMDiff :
    ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin 3)))
      𝓘(ℝ, EuclideanSpace ℝ (Fin 3)) ∞
      (fun p : ℝ × EuclideanSpace ℝ (Fin 3) => axisRotation (Circle.exp p.1) p.2) := by
  have hexp : ContDiff ℝ ∞ (fun t : ℝ => Complex.exp (t * Complex.I)) :=
    Complex.contDiff_exp.comp (Complex.ofRealCLM.contDiff.mul contDiff_const)
  have hpair :
      ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin 3)))
        𝓘(ℝ, ℂ × EuclideanSpace ℝ (Fin 3)) ∞
        (fun p : ℝ × EuclideanSpace ℝ (Fin 3) => (Complex.exp (p.1 * Complex.I), p.2)) :=
    (hexp.contMDiff.comp contMDiff_fst).prodMk_space contMDiff_snd
  exact axisRotationAmbientExtension_contDiff.contMDiff.comp hpair

/-- The genuine angle action is jointly smooth on the entire sphere, including both poles. -/
theorem angleRotation_contMDiff :
    ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 2)) (𝓡 2) ∞
      (fun p : ℝ × RotationalSphere => angleRotation p.1 p.2) := by
  have hpair :
      ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 2))
        (𝓘(ℝ, ℝ).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin 3))) ∞
        (fun p : ℝ × RotationalSphere => (p.1, (p.2 : EuclideanSpace ℝ (Fin 3)))) :=
    contMDiff_fst.prodMk (contMDiff_coe_sphere.comp contMDiff_snd)
  exact ContMDiff.codRestrict_sphere (angleAxisRotation_contMDiff.comp hpair)
    (fun p => (angleRotation p.1 p.2).property)

end RicciFlowSharpEstimate.Geometry
