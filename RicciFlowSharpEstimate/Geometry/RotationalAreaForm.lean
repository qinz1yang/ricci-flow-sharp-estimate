/-
Copyright (c) 2026 Ziyang Qin. All rights reserved.
No license is granted by this file.
Authors: Ziyang Qin
-/
import RicciFlowSharpEstimate.Geometry.AlternatingSurfaceTensors
import RicciFlowSharpEstimate.Geometry.RotationalOneForms
import RicciFlowSharpEstimate.Geometry.RotationalVolume

/-!
# The parallel area form of the rotational sphere metric

The area form is the original profile times the ambient determinant form on the unit sphere.
This construction and its determinant calculation adapt Ziyang Qin's historical
`RotationalSphereAreaForm.lean`.
-/

noncomputable section

namespace RicciFlowSharpEstimate.Geometry

open Bundle DifferentialGeometry DifferentialGeometry.Geometry DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Geometry.Operator DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Tensor.RSTensor DifferentialGeometry.PDE.RicciFlow
open scoped Manifold ContDiff RealInnerProductSpace BigOperators

local instance : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 2 + 1) :=
  ⟨finrank_euclideanSpace_fin⟩

local notation "Ambient3" => EuclideanSpace ℝ (Fin 3)

private def coordinateWedge (i j : Fin 3) :
    Tensor0SField (𝕜 := ℝ) (I := 𝓡 2) (M := RotationalSphere) (n := ∞) 2 :=
  MultilinearSection.product (𝕜 := ℝ) (F := EuclideanSpace ℝ (Fin 2)) (IB := 𝓡 2)
      (E := TangentSpace (𝓡 2)) (n := ∞) (sphereCoordinateOneForm i) (sphereCoordinateOneForm j) -
    MultilinearSection.product (𝕜 := ℝ) (F := EuclideanSpace ℝ (Fin 2)) (IB := 𝓡 2)
      (E := TangentSpace (𝓡 2)) (n := ∞) (sphereCoordinateOneForm j) (sphereCoordinateOneForm i)

private theorem coordinateWedge_apply (i j : Fin 3) (x : RotationalSphere)
    (u v : TangentSpace (𝓡 2) x) :
    coordinateWedge i j x (vec2 u v) =
      (dIncl (n := 2) x u) i * (dIncl (n := 2) x v) j -
        (dIncl (n := 2) x u) j * (dIncl (n := 2) x v) i := by
  change Bundle.continuousMultilinearMap.productFun (sphereCoordinateOneForm i x)
      (sphereCoordinateOneForm j x) (vec2 u v) -
    Bundle.continuousMultilinearMap.productFun (sphereCoordinateOneForm j x)
      (sphereCoordinateOneForm i x) (vec2 u v) = _
  erw [Bundle.continuousMultilinearMap.product_fun_apply,
    Bundle.continuousMultilinearMap.product_fun_apply]
  have h0 : vec2 u v ∘ Fin.castAdd 1 = fun _ : Fin 1 => u := by
    funext k; fin_cases k; rfl
  have h1 : vec2 u v ∘ Fin.natAdd 1 = fun _ : Fin 1 => v := by
    funext k; fin_cases k; rfl
  simp only [h0, h1]
  erw [sphereCoordinateOneForm_apply, sphereCoordinateOneForm_apply,
    sphereCoordinateOneForm_apply, sphereCoordinateOneForm_apply]

/-- The global smooth determinant area form on the round unit sphere. -/
def roundSphereAreaForm :
    Tensor0SField (𝕜 := ℝ) (I := 𝓡 2) (M := RotationalSphere) (n := ∞) 2 :=
  tensor0SFieldSmulByFun (I := 𝓡 2) (n := ∞)
      (innerCoordFun (n := 2) (EuclideanSpace.single (2 : Fin 3) (1 : ℝ)))
      (innerCoordFun (n := 2) (EuclideanSpace.single (2 : Fin 3) (1 : ℝ))).contMDiff
      (coordinateWedge 0 1) +
    tensor0SFieldSmulByFun (I := 𝓡 2) (n := ∞)
      (innerCoordFun (n := 2) (EuclideanSpace.single (0 : Fin 3) (1 : ℝ)))
      (innerCoordFun (n := 2) (EuclideanSpace.single (0 : Fin 3) (1 : ℝ))).contMDiff
      (coordinateWedge 1 2) +
    tensor0SFieldSmulByFun (I := 𝓡 2) (n := ∞)
      (innerCoordFun (n := 2) (EuclideanSpace.single (1 : Fin 3) (1 : ℝ)))
      (innerCoordFun (n := 2) (EuclideanSpace.single (1 : Fin 3) (1 : ℝ))).contMDiff
      (coordinateWedge 2 0)

/-- Evaluation of the smooth round area form is the ambient scalar triple product. -/
theorem roundSphereAreaForm_apply (x : RotationalSphere) (u v : TangentSpace (𝓡 2) x) :
    roundSphereAreaForm x (vec2 u v) =
      (x : Ambient3) 2 *
          ((dIncl (n := 2) x u) 0 * (dIncl (n := 2) x v) 1 -
            (dIncl (n := 2) x u) 1 * (dIncl (n := 2) x v) 0) +
        (x : Ambient3) 0 *
          ((dIncl (n := 2) x u) 1 * (dIncl (n := 2) x v) 2 -
            (dIncl (n := 2) x u) 2 * (dIncl (n := 2) x v) 1) +
        (x : Ambient3) 1 *
          ((dIncl (n := 2) x u) 2 * (dIncl (n := 2) x v) 0 -
            (dIncl (n := 2) x u) 0 * (dIncl (n := 2) x v) 2) := by
  simp [roundSphereAreaForm, tensor0SField_smulByFun_apply, coordinateWedge_apply,
    innerCoordFun, EuclideanSpace.inner_single_left]

/-- The determinant form is alternating in its two tangent arguments. -/
theorem roundSphereAreaForm_alternating (x : RotationalSphere)
    (u v : TangentSpace (𝓡 2) x) :
    roundSphereAreaForm x (vec2 u v) = -roundSphereAreaForm x (vec2 v u) := by
  rw [roundSphereAreaForm_apply, roundSphereAreaForm_apply]
  ring

private theorem real_inner_real_eq_mul
    (a b : ℝ) :
    inner ℝ a b = a * b := by
  rw [show a = a • (1 : ℝ) by simp,
    show b = b • (1 : ℝ) by simp,
    real_inner_smul_left, real_inner_smul_right]
  simp

private theorem scalarTriple_sq_eq_gram
    (x0 x1 x2 u0 u1 u2 v0 v1 v2 : ℝ)
    (hxx : x0 ^ 2 + x1 ^ 2 + x2 ^ 2 = 1)
    (hxu : x0 * u0 + x1 * u1 + x2 * u2 = 0)
    (hxv : x0 * v0 + x1 * v1 + x2 * v2 = 0) :
    (x2 * (u0 * v1 - u1 * v0)
        + x0 * (u1 * v2 - u2 * v1)
        + x1 * (u2 * v0 - u0 * v2)) ^ 2 =
      (u0 ^ 2 + u1 ^ 2 + u2 ^ 2) *
          (v0 ^ 2 + v1 ^ 2 + v2 ^ 2)
        - (u0 * v0 + u1 * v1 + u2 * v2) ^ 2 := by
  have hid :
      (x2 * (u0 * v1 - u1 * v0)
          + x0 * (u1 * v2 - u2 * v1)
          + x1 * (u2 * v0 - u0 * v2)) ^ 2 =
        (x0 ^ 2 + x1 ^ 2 + x2 ^ 2) *
            ((u0 ^ 2 + u1 ^ 2 + u2 ^ 2) *
                (v0 ^ 2 + v1 ^ 2 + v2 ^ 2)
              - (u0 * v0 + u1 * v1 + u2 * v2) ^ 2)
          - (x0 * u0 + x1 * u1 + x2 * u2) ^ 2 *
              (v0 ^ 2 + v1 ^ 2 + v2 ^ 2)
          + 2 * (x0 * u0 + x1 * u1 + x2 * u2) *
              (x0 * v0 + x1 * v1 + x2 * v2) *
              (u0 * v0 + u1 * v1 + u2 * v2)
          - (x0 * v0 + x1 * v1 + x2 * v2) ^ 2 *
              (u0 ^ 2 + u1 ^ 2 + u2 ^ 2) := by
    ring
  rw [hxx, hxu, hxv] at hid
  simpa using hid

/-- The square of the ambient-determinant form is the determinant of
the round Gram matrix of its two arguments. -/
theorem roundSphereAreaForm_sq
    (x : RotationalSphere)
    (u v : TangentSpace (𝓡 2) x) :
    roundSphereAreaForm x (vec2 (I := 𝓡 2) u v) ^ 2 =
      HeightMetricCoefficients.round.inner x u u * HeightMetricCoefficients.round.inner x v v
        - HeightMetricCoefficients.round.inner x u v ^ 2 := by
  let X : Ambient3 := (x : Ambient3)
  let U : Ambient3 := dIncl (n := 2) x u
  let V : Ambient3 := dIncl (n := 2) x v
  have hXU : inner ℝ X U = 0 := by
    rw [real_inner_comm]
    refine Submodule.inner_left_of_mem_orthogonal
      (Submodule.mem_span_singleton_self X) ?_
    change U ∈ (ℝ ∙ X)ᗮ
    dsimp only [U, X]
    rw [← range_mvfderiv_subtypeVal (n := 2) x]
    exact ⟨u, rfl⟩
  have hXV : inner ℝ X V = 0 := by
    rw [real_inner_comm]
    refine Submodule.inner_left_of_mem_orthogonal
      (Submodule.mem_span_singleton_self X) ?_
    change V ∈ (ℝ ∙ X)ᗮ
    dsimp only [V, X]
    rw [← range_mvfderiv_subtypeVal (n := 2) x]
    exact ⟨v, rfl⟩
  have hXX : inner ℝ X X = 1 := by
    have hxnorm : ‖X‖ = 1 := by
      exact mem_sphere_zero_iff_norm.mp x.property
    calc
      inner ℝ X X = ‖X‖ * ‖X‖ :=
        real_inner_self_eq_norm_mul_norm X
      _ = 1 := by rw [hxnorm]; norm_num
  have hxx :
      X 0 ^ 2 + X 1 ^ 2 + X 2 ^ 2 = 1 := by
    rw [PiLp.inner_apply] at hXX
    simp only [Fin.sum_univ_succ, Fin.sum_univ_zero,
      real_inner_real_eq_mul, add_zero] at hXX
    norm_num at hXX
    nlinarith
  have hxu :
      X 0 * U 0 + X 1 * U 1 + X 2 * U 2 = 0 := by
    rw [PiLp.inner_apply] at hXU
    simp only [Fin.sum_univ_succ, Fin.sum_univ_zero,
      real_inner_real_eq_mul, add_zero] at hXU
    norm_num at hXU
    linarith
  have hxv :
      X 0 * V 0 + X 1 * V 1 + X 2 * V 2 = 0 := by
    rw [PiLp.inner_apply] at hXV
    simp only [Fin.sum_univ_succ, Fin.sum_univ_zero,
      real_inner_real_eq_mul, add_zero] at hXV
    norm_num at hXV
    linarith
  have htriple :=
    scalarTriple_sq_eq_gram
      (X 0) (X 1) (X 2)
      (U 0) (U 1) (U 2)
      (V 0) (V 1) (V 2)
      hxx hxu hxv
  have hUU :
      inner ℝ U U = U 0 ^ 2 + U 1 ^ 2 + U 2 ^ 2 := by
    rw [PiLp.inner_apply]
    simp only [Fin.sum_univ_succ, Fin.sum_univ_zero,
      real_inner_real_eq_mul, add_zero]
    norm_num
    ring
  have hVV :
      inner ℝ V V = V 0 ^ 2 + V 1 ^ 2 + V 2 ^ 2 := by
    rw [PiLp.inner_apply]
    simp only [Fin.sum_univ_succ, Fin.sum_univ_zero,
      real_inner_real_eq_mul, add_zero]
    norm_num
    ring
  have hUV :
      inner ℝ U V = U 0 * V 0 + U 1 * V 1 + U 2 * V 2 := by
    rw [PiLp.inner_apply]
    simp only [Fin.sum_univ_succ, Fin.sum_univ_zero,
      real_inner_real_eq_mul, add_zero]
    norm_num
    ring
  rw [roundSphereAreaForm_apply,
    roundMetric_inner, roundMetric_inner,
    roundMetric_inner, hUU, hVV, hUV]
  simpa [X, U, V, pow_two] using htriple

namespace RotationalProfile.PoleData

private theorem det_metricGram (D : PoleData) (x : RotationalSphere)
    (B : Module.Basis (Fin 2) ℝ (TangentSpace (𝓡 2) x)) :
    (Matrix.of fun i j => D.metric.inner x (B i) (B j)).det =
      D.a (sphereHeight x) ^ 2 *
        (Matrix.of fun i j => HeightMetricCoefficients.round.inner x (B i) (B j)).det := by
  let Z := gradFun HeightMetricCoefficients.round sphereHeight x
  let G := metricFlatLinear HeightMetricCoefficients.round x
  have hu (i : Fin 2) : G Z (B i) = heightOneForm x (fun _ : Fin 1 => B i) := by
    change HeightMetricCoefficients.round.inner x Z (B i) = _
    rw [inner_gradFun, heightOneForm_apply, mvfderiv_real_eq_mfderiv]
    rfl
  have hZZ : G Z Z = 1 - sphereHeight x ^ 2 := round_grad_sphereHeight_inner_self x
  have hdet := LinearMap.det_smul_add_rankOne_gram_fin_two G
    (HeightMetricCoefficients.round.symm x) B Z
    (D.b (sphereHeight x)) (D.c (sphereHeight x) / D.b (sphereHeight x))
  have hmetric : (Matrix.of fun i j =>
      D.b (sphereHeight x) * G (B i) (B j) + D.c (sphereHeight x) / D.b (sphereHeight x) *
        (G Z (B i) * G Z (B j))) = (Matrix.of fun i j => D.metric.inner x (B i) (B j)) := by
    ext i j
    rw [Matrix.of_apply, Matrix.of_apply, hu i, hu j]
    exact (D.metric_inner x _ _).symm
  rw [hmetric, hZZ, D.radial_identity _ (sphereHeight_mem_Icc x)] at hdet
  rw [hdet]
  change D.b (sphereHeight x) * (D.a (sphereHeight x) ^ 2 / D.b (sphereHeight x)) * _ = _
  field_simp [(D.b_pos _ (sphereHeight_mem_Icc x)).ne']
  rfl

/-- The globally smooth area form of the original rotational metric. -/
def areaForm (D : PoleData) :
    Tensor0SField (𝕜 := ℝ) (I := 𝓡 2) (M := RotationalSphere) (n := ∞) 2 :=
  tensor0SFieldSmulByFun (I := 𝓡 2) (n := ∞)
    (fun x => D.a (sphereHeight x))
    (D.a_contDiff.comp_contMDiff sphereHeight_contMDiff) roundSphereAreaForm

/-- The area form retains its literal profile-scaled ambient determinant formula. -/
@[simp] theorem areaForm_apply (D : PoleData) (x : RotationalSphere)
    (slots : Fin 2 → TangentSpace (𝓡 2) x) :
    D.areaForm x slots = D.a (sphereHeight x) * roundSphereAreaForm x slots := by
  rw [areaForm, tensor0SField_smulByFun_apply]
  rfl

/-- The metric area form is alternating. -/
theorem areaForm_alternating (D : PoleData) (x : RotationalSphere)
    (u v : TangentSpace (𝓡 2) x) :
    D.areaForm x (vec2 u v) = -D.areaForm x (vec2 v u) := by
  rw [areaForm_apply, areaForm_apply, roundSphereAreaForm_alternating]
  ring

/-- Every orthonormal basis has area one up to orientation. -/
theorem areaForm_unit_on_orthonormal (D : PoleData) (x : RotationalSphere)
    (B : Module.Basis (Fin 2) ℝ (TangentSpace (𝓡 2) x))
    (hON : ∀ i j, D.metric.inner x (B i) (B j) = if i = j then 1 else 0) :
    D.areaForm x (vec2 (B 0) (B 1)) ^ 2 = 1 := by
  have hdet := D.det_metricGram x B
  have hdetMetric : (Matrix.of fun i j => D.metric.inner x (B i) (B j)).det = 1 := by
    simp [Matrix.det_fin_two, hON]
  rw [hdetMetric, Matrix.det_fin_two] at hdet
  simp only [Matrix.of_apply] at hdet
  rw [HeightMetricCoefficients.round.symm x (B 1) (B 0)] at hdet
  rw [areaForm_apply, mul_pow, roundSphereAreaForm_sq]
  nlinarith [hdet]

/-- The squared tensor norm of the actual metric area form is two. -/
theorem areaForm_normSq (D : PoleData) (x : RotationalSphere) :
    normSq0S D.metric x 2 (D.areaForm x) = 2 :=
  normSq0S_eq_two_of_unit_alternating finrank_euclideanSpace_fin D.metric x (D.areaForm x)
    (D.areaForm_alternating x) (D.areaForm_unit_on_orthonormal x)

/-- The area form constructed from the profile is Levi-Civita parallel. -/
theorem metricNabla0S_areaForm (D : PoleData) : metricNabla0S D.metric D.areaForm = 0 :=
  metricNabla0S_eq_zero_of_alternating_const_normSq finrank_euclideanSpace_fin D.metric
    D.areaForm D.areaForm_alternating 2 D.areaForm_normSq

end RotationalProfile.PoleData

end RicciFlowSharpEstimate.Geometry
