/-
Copyright (c) 2026 Ziyang Qin. All rights reserved.
No license is granted by this file.
Authors: Ziyang Qin
-/
import DifferentialGeometry.Geometry.Metric.Construction.BumpExtension
import DifferentialGeometry.Geometry.Metric.Sphere.Round.ProjectedConnectionLeviCivita
import DifferentialGeometry.Geometry.Operator.Hessian.Trace.Realization

/-!
# Smooth rank-one metrics on the actual unit sphere

The metric is constructed globally as `b g_round + q dz ⊗ dz` using the
actual differential of the sphere's height. Its positivity is proved from
ambient tangent orthogonality and Cauchy–Schwarz, including at both poles.

The rank-one construction adapts Ziyang Qin's historical
`Geometry/Surface/RotationalSphereMetric.lean`; all geometric APIs and proofs
are checked against the pinned DifferentialGeometry release.
-/

open Bundle DifferentialGeometry DifferentialGeometry.Geometry
open DifferentialGeometry.Geometry.Operator DifferentialGeometry.Tensor.RicciIdentity
open DifferentialGeometry.Tensor0SBundle Metric
open scoped Manifold ContDiff RealInnerProductSpace

noncomputable section

namespace RicciFlowSharpEstimate.Geometry

local instance : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 2 + 1) :=
  ⟨finrank_euclideanSpace_fin⟩

/-- The actual unit two-sphere in Euclidean three-space. -/
abbrev RotationalSphere := sphere (0 : EuclideanSpace ℝ (Fin 3)) 1

/-- The height coordinate for the fixed third axis of the actual unit sphere. -/
def sphereHeight : RotationalSphere → ℝ :=
  innerCoordFun (n := 2) (EuclideanSpace.single (2 : Fin 3) (1 : ℝ))

/-- The actual height coordinate is globally smooth, including at both poles. -/
theorem sphereHeight_contMDiff : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ sphereHeight :=
  (innerCoordFun (n := 2) (EuclideanSpace.single (2 : Fin 3) (1 : ℝ))).contMDiff

/-- The height is the third ambient coordinate. -/
theorem sphereHeight_apply (x : RotationalSphere) :
    sphereHeight x = (x : EuclideanSpace ℝ (Fin 3)) 2 := by
  simp [sphereHeight, innerCoordFun, EuclideanSpace.inner_single_left]

private theorem sphere_norm (x : RotationalSphere) :
    ‖(x : EuclideanSpace ℝ (Fin 3))‖ = 1 := by
  simpa only [mem_sphere, dist_zero_right] using x.property

/-- The height takes values in the closed unit interval. -/
theorem sphereHeight_mem_Icc (x : RotationalSphere) : sphereHeight x ∈ Set.Icc (-1 : ℝ) 1 := by
  have h := abs_real_inner_le_norm (EuclideanSpace.single (2 : Fin 3) (1 : ℝ))
    (x : EuclideanSpace ℝ (Fin 3))
  have he : ‖EuclideanSpace.single (2 : Fin 3) (1 : ℝ)‖ = 1 := by simp
  rw [he, sphere_norm, one_mul] at h
  exact abs_le.mp h

/-- The genuine smooth one-form `d(sphereHeight)`. -/
def heightOneForm : OneFormSection (I := 𝓡 2) (M := RotationalSphere) :=
  duSec (I := 𝓡 2) sphereHeight sphereHeight_contMDiff

/-- The one-form is tied to the actual manifold derivative of height. -/
theorem heightOneForm_apply (x : RotationalSphere) (v : TangentSpace (𝓡 2) x) :
    heightOneForm x (fun _ : Fin 1 => v) = mvfderiv (𝓡 2) sphereHeight x v := by
  rw [heightOneForm, duSec_apply]
  exact differential1FormFun_apply_eq_mvfderiv (I := 𝓡 2) sphereHeight x v

private def heightCLM (x : RotationalSphere) : TangentSpace (𝓡 2) x →L[ℝ] ℝ :=
  mvfderiv (𝓡 2) sphereHeight x

private theorem heightCLM_apply (x : RotationalSphere) (v : TangentSpace (𝓡 2) x) :
    heightCLM x v = heightOneForm x (fun _ : Fin 1 => v) :=
  (heightOneForm_apply x v).symm

private theorem heightCLM_eq_inner (x : RotationalSphere) (v : TangentSpace (𝓡 2) x) :
    heightCLM x v =
      ⟪EuclideanSpace.single (2 : Fin 3) (1 : ℝ), dIncl (n := 2) x v⟫ := by
  rw [heightCLM, mvfderiv_real_eq_mfderiv]
  exact mfderiv_innerCoordFun _ x v

/-- Smooth scalar coefficients with the two genuine positivity conditions. -/
structure HeightMetricCoefficients where
  b : RotationalSphere → ℝ
  q : RotationalSphere → ℝ
  b_contMDiff : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ b
  q_contMDiff : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ q
  b_pos : ∀ x, 0 < b x
  radial_pos : ∀ x, 0 < b x + q x * (1 - sphereHeight x ^ 2)

namespace HeightMetricCoefficients

/-- The genuine round metric on the fixed unit sphere. -/
abbrev round : SmoothRiemannianMetric (𝓡 2) RotationalSphere :=
  roundMetric (E := EuclideanSpace ℝ (Fin 3)) (n := 2)

/-- The height differential obeys the sharp round tangent bound. -/
theorem heightOneForm_sq_le (x : RotationalSphere) (v : TangentSpace (𝓡 2) x) :
    (heightOneForm x (fun _ : Fin 1 => v)) ^ 2 ≤
      (1 - sphereHeight x ^ 2) * round.inner x v v := by
  let e : EuclideanSpace ℝ (Fin 3) := EuclideanSpace.single (2 : Fin 3) (1 : ℝ)
  let P : EuclideanSpace ℝ (Fin 3) := e - sphereHeight x • (x : EuclideanSpace ℝ (Fin 3))
  have horth : ⟪(x : EuclideanSpace ℝ (Fin 3)), dIncl (n := 2) x v⟫ = 0 := by
    apply Submodule.mem_orthogonal_singleton_iff_inner_right.mp
    rw [← range_mvfderiv_subtypeVal (n := 2) x]
    exact ⟨v, rfl⟩
  have hex : ⟪e, (x : EuclideanSpace ℝ (Fin 3))⟫ = sphereHeight x := rfl
  have hxe : ⟪(x : EuclideanSpace ℝ (Fin 3)), e⟫ = sphereHeight x := by
    rw [real_inner_comm, hex]
  have hee : ⟪e, e⟫ = 1 := by simp [e]
  have hxx : ⟪(x : EuclideanSpace ℝ (Fin 3)), (x : EuclideanSpace ℝ (Fin 3))⟫ = 1 := by
    rw [real_inner_self_eq_norm_sq, sphere_norm]
    norm_num
  have hPP : ⟪P, P⟫ = 1 - sphereHeight x ^ 2 := by
    dsimp only [P]
    simp only [inner_sub_left, inner_sub_right, real_inner_smul_left,
      real_inner_smul_right, hee, hex, hxe, hxx]
    ring
  have hPv : ⟪P, dIncl (n := 2) x v⟫ = heightCLM x v := by
    dsimp only [P]
    rw [inner_sub_left, real_inner_smul_left, horth, mul_zero, sub_zero]
    exact (heightCLM_eq_inner x v).symm
  have hCS := real_inner_mul_inner_self_le P (dIncl (n := 2) x v)
  rw [hPP, hPv, heightCLM_apply, ← roundMetric_inner] at hCS
  simpa only [pow_two] using hCS

private def bilinearForm (D : HeightMetricCoefficients) (x : RotationalSphere) :
    TangentSpace (𝓡 2) x →L[ℝ] TangentSpace (𝓡 2) x →L[ℝ] ℝ :=
  D.b x • round.inner x + D.q x • (heightCLM x).smulRight (heightCLM x)

private theorem bilinearForm_apply (D : HeightMetricCoefficients) (x : RotationalSphere)
    (v w : TangentSpace (𝓡 2) x) :
    D.bilinearForm x v w = D.b x * round.inner x v w +
      D.q x * (heightOneForm x (fun _ : Fin 1 => v) *
        heightOneForm x (fun _ : Fin 1 => w)) := by
  simp only [bilinearForm, add_apply, smul_apply,
    ContinuousLinearMap.smulRight_apply, smul_eq_mul, heightCLM_apply]

private theorem bilinearForm_symm (D : HeightMetricCoefficients) (x : RotationalSphere)
    (v w : TangentSpace (𝓡 2) x) :
    D.bilinearForm x v w = D.bilinearForm x w v := by
  rw [D.bilinearForm_apply, D.bilinearForm_apply, round.symm x v w]
  ring

private theorem bilinearForm_pos (D : HeightMetricCoefficients) (x : RotationalSphere)
    (v : TangentSpace (𝓡 2) x) (hv : v ≠ 0) : 0 < D.bilinearForm x v v := by
  rw [D.bilinearForm_apply]
  have hround : 0 < round.inner x v v := round.pos x v hv
  have hheight := heightOneForm_sq_le x v
  by_cases hq : 0 ≤ D.q x
  · have hbproduct := mul_pos (D.b_pos x) hround
    have hqproduct := mul_nonneg hq (sq_nonneg (heightOneForm x (fun _ : Fin 1 => v)))
    nlinarith
  · have hqnonpos : D.q x ≤ 0 := le_of_not_ge hq
    have hqmul := mul_le_mul_of_nonpos_left hheight hqnonpos
    have hproduct := mul_pos (D.radial_pos x) hround
    nlinarith

private theorem heightOneForm_frame_contMDiffAt (x₀ : RotationalSphere)
    (i : Fin (Module.finrank ℝ (EuclideanSpace ℝ (Fin 2)))) {x : RotationalSphere}
    (hx : x ∈ (trivializationAt (EuclideanSpace ℝ (Fin 2)) (TangentSpace (𝓡 2)) x₀).baseSet) :
    ContMDiffAt (𝓡 2) 𝓘(ℝ, ℝ) ∞
      (fun y : RotationalSphere =>
        heightOneForm y (fun _ : Fin 1 => frameVec (I := 𝓡 2) x₀ i y)) x := by
  have hframe := frameVec_cmdiffAt (I := 𝓡 2) x₀ i hx
  have hderiv := mvfderiv_apply_contMDiffAt_of_section (I := 𝓡 2)
    (f := sphereHeight) (X := frameVec (I := 𝓡 2) x₀ i)
    sphereHeight_contMDiff.contMDiffAt hframe
  simpa only [heightOneForm_apply] using hderiv

private theorem bilinearForm_coeff (D : HeightMetricCoefficients) (x₀ : RotationalSphere)
    (i j : Fin (Module.finrank ℝ (EuclideanSpace ℝ (Fin 2)))) :
    ContMDiffOn (𝓡 2) 𝓘(ℝ) ∞
      (fun x => D.bilinearForm x (frameVec (I := 𝓡 2) x₀ i x) (frameVec (I := 𝓡 2) x₀ j x))
      (trivializationAt (EuclideanSpace ℝ (Fin 2)) (TangentSpace (𝓡 2)) x₀).baseSet := by
  intro x hx
  have hi := heightOneForm_frame_contMDiffAt x₀ i hx
  have hj := heightOneForm_frame_contMDiffAt x₀ j hx
  have hg : ContMDiffAt (𝓡 2) 𝓘(ℝ, ℝ) ∞
      (fun y : RotationalSphere =>
        round.inner y (frameVec (I := 𝓡 2) x₀ i y) (frameVec (I := 𝓡 2) x₀ j y)) x :=
    Curvature.CovariantDerivative.metric_inner_contMDiffAt (I := 𝓡 2) round
      (frameVec_cmdiffAt (I := 𝓡 2) x₀ i hx) (frameVec_cmdiffAt (I := 𝓡 2) x₀ j hx) le_rfl
  have hcoeff : ContMDiffAt (𝓡 2) 𝓘(ℝ, ℝ) ∞
      (fun y : RotationalSphere =>
        D.b y * round.inner y (frameVec (I := 𝓡 2) x₀ i y) (frameVec (I := 𝓡 2) x₀ j y) +
          D.q y * (heightOneForm y (fun _ : Fin 1 => frameVec (I := 𝓡 2) x₀ i y) *
            heightOneForm y (fun _ : Fin 1 => frameVec (I := 𝓡 2) x₀ j y))) x :=
    ((D.b_contMDiff x).mul hg).add ((D.q_contMDiff x).mul (hi.mul hj))
  simpa only [bilinearForm_apply] using hcoeff.contMDiffWithinAt

/-- The smooth global sphere metric determined by the height coefficients. -/
def metric (D : HeightMetricCoefficients) : SmoothRiemannianMetric (𝓡 2) RotationalSphere :=
  (smoothMetric_of_localCoeff (I := 𝓡 2)
    D.bilinearForm D.bilinearForm_symm D.bilinearForm_pos D.bilinearForm_coeff).choose

/-- The produced metric retains the exact rank-one formula on genuine tangent vectors. -/
theorem metric_inner_apply (D : HeightMetricCoefficients) (x : RotationalSphere)
    (v w : TangentSpace (𝓡 2) x) :
    D.metric.inner x v w = D.b x * round.inner x v w +
      D.q x * (heightOneForm x (fun _ : Fin 1 => v) *
        heightOneForm x (fun _ : Fin 1 => w)) := by
  unfold metric
  rw [(smoothMetric_of_localCoeff (I := 𝓡 2)
    D.bilinearForm D.bilinearForm_symm D.bilinearForm_pos D.bilinearForm_coeff).choose_spec x v w]
  exact D.bilinearForm_apply x v w

end HeightMetricCoefficients

end RicciFlowSharpEstimate.Geometry
