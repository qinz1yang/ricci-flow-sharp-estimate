/-
Copyright (c) 2026 Ziyang Qin. All rights reserved.
No license is granted by this file.
Authors: Ziyang Qin
-/
import RicciFlowSharpEstimate.Geometry.RotationalCircleAction
import Mathlib.Analysis.Calculus.FDeriv.WithLp
import Mathlib.Analysis.SpecialFunctions.Complex.Arg

/-!
# Genuine polar coordinates and their tangent basis

The actual polar parametrization is smooth at both poles. Its genuine radial
and angular derivatives diagonalize the accepted rotational metric, and form a
basis wherever the angular derivative is nonzero.

The meridian construction adapts Ziyang Qin's historical
`RotationalSpherePolarCoordinates.lean`.
-/

noncomputable section

namespace RicciFlowSharpEstimate.Geometry

open DifferentialGeometry DifferentialGeometry.Geometry
open Set Metric
open scoped Manifold ContDiff RealInnerProductSpace

local instance : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 2 + 1) :=
  ⟨finrank_euclideanSpace_fin⟩

private def polarMeridianAmbient (s : ℝ) : EuclideanSpace ℝ (Fin 3) :=
  WithLp.toLp 2 ![Real.sin s, 0, Real.cos s]

private theorem polarMeridianAmbient_norm (s : ℝ) : ‖polarMeridianAmbient s‖ = 1 := by
  rw [← sq_eq_sq₀ (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)]
  rw [EuclideanSpace.real_norm_sq_eq]
  simp [polarMeridianAmbient, Fin.sum_univ_succ]

private def polarMeridian (s : ℝ) : RotationalSphere :=
  ⟨polarMeridianAmbient s, mem_sphere_zero_iff_norm.mpr (polarMeridianAmbient_norm s)⟩

private theorem polarMeridian_contMDiff : ContMDiff 𝓘(ℝ, ℝ) (𝓡 2) ∞ polarMeridian := by
  apply ContMDiff.codRestrict_sphere
  have h : ContDiff ℝ ∞ polarMeridianAmbient := by
    apply contDiff_piLp'
    intro i
    fin_cases i
    · exact Real.contDiff_sin
    · exact contDiff_const
    · exact Real.contDiff_cos
  exact h.contMDiff

/-- The actual polar point, obtained by rotating the standard meridian. -/
def polarSpherePoint (s theta : ℝ) : RotationalSphere :=
  angleRotation theta (polarMeridian s)

/-- Literal ambient coordinates of the actual polar parametrization. -/
theorem polarSpherePoint_coe (s theta : ℝ) :
    (polarSpherePoint s theta : EuclideanSpace ℝ (Fin 3)) =
      WithLp.toLp 2 ![Real.sin s * Real.cos theta,
        Real.sin s * Real.sin theta, Real.cos s] := by
  ext i
  fin_cases i <;>
    simp [polarSpherePoint, angleRotation, polarMeridian, polarMeridianAmbient,
      Circle.coe_exp, Complex.exp_mul_I, Complex.cos_ofReal_re,
      Complex.sin_ofReal_re] <;> ring

/-- Polar height is the cosine of the meridian parameter, including at both poles. -/
@[simp] theorem sphereHeight_polarSpherePoint (s theta : ℝ) :
    sphereHeight (polarSpherePoint s theta) = Real.cos s := by
  rw [sphereHeight_apply, polarSpherePoint_coe]
  rfl

/-- The polar parametrization is jointly smooth on the entire real parameter plane. -/
theorem polarSpherePoint_contMDiff :
    ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) (𝓡 2) ∞
      (fun p : ℝ × ℝ => polarSpherePoint p.1 p.2) := by
  have hpair : ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ))
      (𝓘(ℝ, ℝ).prod (𝓡 2)) ∞
      (fun p : ℝ × ℝ => (p.2, polarMeridian p.1)) :=
    contMDiff_snd.prodMk (polarMeridian_contMDiff.comp contMDiff_fst)
  simpa only [Function.comp_def, polarSpherePoint] using!
    angleRotation_contMDiff.comp hpair

/-- The angular parameter has period `2*pi`. -/
theorem polarSpherePoint_periodic (s : ℝ) :
    Function.Periodic (polarSpherePoint s) (2 * Real.pi) := by
  intro theta
  exact congrArg (fun e => e (polarMeridian s)) (angleRotation_periodic theta)

/-- Rotation adds its angle to the polar angular coordinate. -/
theorem angleRotation_polarSpherePoint (phi s theta : ℝ) :
    angleRotation phi (polarSpherePoint s theta) = polarSpherePoint s (phi + theta) :=
  (angleRotation_add phi theta (polarMeridian s)).symm

/-- The north endpoint is the fixed positive height-axis point. -/
@[simp] theorem polarSpherePoint_zero (theta : ℝ) :
    polarSpherePoint 0 theta =
      ⟨EuclideanSpace.single (2 : Fin 3) (1 : ℝ), by simp⟩ := by
  apply Subtype.ext
  rw [polarSpherePoint_coe]
  ext i
  fin_cases i <;> simp

/-- The south endpoint is the fixed negative height-axis point. -/
@[simp] theorem polarSpherePoint_pi (theta : ℝ) :
    polarSpherePoint Real.pi theta =
      ⟨EuclideanSpace.single (2 : Fin 3) (-1 : ℝ), by simp⟩ := by
  apply Subtype.ext
  rw [polarSpherePoint_coe]
  ext i
  fin_cases i <;> simp

/-- The radial coordinate tangent is the actual derivative of the meridian curve. -/
def polarRadialVelocity (s theta : ℝ) : TangentSpace (𝓡 2) (polarSpherePoint s theta) :=
  mfderiv 𝓘(ℝ, ℝ) (𝓡 2) (fun t => polarSpherePoint t theta) s 1

/-- The angular coordinate tangent is the actual derivative of the orbit curve. -/
def polarAngularVelocity (s theta : ℝ) : TangentSpace (𝓡 2) (polarSpherePoint s theta) :=
  mfderiv 𝓘(ℝ, ℝ) (𝓡 2) (polarSpherePoint s) theta 1

private theorem polarRadialCurve_contMDiff (theta : ℝ) :
    ContMDiff 𝓘(ℝ, ℝ) (𝓡 2) ∞ (fun s => polarSpherePoint s theta) := by
  have hslice : ContMDiff 𝓘(ℝ, ℝ) (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) ∞
      (fun s : ℝ => (s, theta)) := contMDiff_id.prodMk contMDiff_const
  simpa only [Function.comp_def] using! polarSpherePoint_contMDiff.comp hslice

private theorem polarAngularCurve_contMDiff (s : ℝ) :
    ContMDiff 𝓘(ℝ, ℝ) (𝓡 2) ∞ (polarSpherePoint s) := by
  have hslice : ContMDiff 𝓘(ℝ, ℝ) (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) ∞
      (fun theta : ℝ => (s, theta)) := contMDiff_const.prodMk contMDiff_id
  simpa only [Function.comp_def] using! polarSpherePoint_contMDiff.comp hslice

private theorem polarRadialAmbient_hasDerivAt (s theta : ℝ) :
    HasDerivAt (fun t : ℝ =>
      (polarSpherePoint t theta : EuclideanSpace ℝ (Fin 3)))
      (WithLp.toLp 2 ![Real.cos s * Real.cos theta,
        Real.cos s * Real.sin theta, -Real.sin s]) s := by
  let raw : ℝ → Fin 3 → ℝ := fun t =>
    ![Real.sin t * Real.cos theta, Real.sin t * Real.sin theta, Real.cos t]
  have hraw : HasDerivAt raw
      ![Real.cos s * Real.cos theta, Real.cos s * Real.sin theta, -Real.sin s] s := by
    rw [hasDerivAt_pi]
    intro i
    fin_cases i
    · exact (Real.hasDerivAt_sin s).mul_const (Real.cos theta)
    · exact (Real.hasDerivAt_sin s).mul_const (Real.sin theta)
    · exact Real.hasDerivAt_cos s
  simpa only [raw, polarSpherePoint_coe, Function.comp_apply] using!
    (PiLp.hasFDerivAt_toLp 2 (raw s)).comp_hasDerivAt s hraw

private theorem polarAngularAmbient_hasDerivAt (s theta : ℝ) :
    HasDerivAt (fun t : ℝ =>
      (polarSpherePoint s t : EuclideanSpace ℝ (Fin 3)))
      (WithLp.toLp 2 ![-Real.sin s * Real.sin theta,
        Real.sin s * Real.cos theta, 0]) theta := by
  let raw : ℝ → Fin 3 → ℝ := fun t =>
    ![Real.sin s * Real.cos t, Real.sin s * Real.sin t, Real.cos s]
  have hraw : HasDerivAt raw
      ![-Real.sin s * Real.sin theta, Real.sin s * Real.cos theta, 0] theta := by
    rw [hasDerivAt_pi]
    intro i
    fin_cases i
    · simpa only [raw, Matrix.cons_val_zero, neg_mul, mul_neg] using!
        (Real.hasDerivAt_cos theta).const_mul (Real.sin s)
    · exact (Real.hasDerivAt_sin theta).const_mul (Real.sin s)
    · exact hasDerivAt_const theta (Real.cos s)
  simpa only [raw, polarSpherePoint_coe, Function.comp_apply] using!
    (PiLp.hasFDerivAt_toLp 2 (raw theta)).comp_hasDerivAt theta hraw

/-- The included radial tangent has the derivative of the literal ambient formula. -/
theorem polarRadialVelocity_dIncl (s theta : ℝ) :
    dIncl (n := 2) (polarSpherePoint s theta) (polarRadialVelocity s theta) =
      WithLp.toLp 2 ![Real.cos s * Real.cos theta,
        Real.cos s * Real.sin theta, -Real.sin s] := by
  have hc := (polarRadialCurve_contMDiff theta).mdifferentiableAt (x := s) (by simp)
  have hi := (contMDiff_coe_sphere (m := ∞) (n := 2)
    (E := EuclideanSpace ℝ (Fin 3))).mdifferentiableAt
    (x := polarSpherePoint s theta) (by simp)
  have hchain := mvfderiv_comp_apply (x := s) (f := fun t => polarSpherePoint t theta)
    (g := ((↑) : RotationalSphere → EuclideanSpace ℝ (Fin 3))) hi hc 1
  change dIncl (n := 2) (polarSpherePoint s theta)
    (mfderiv 𝓘(ℝ, ℝ) (𝓡 2) (fun t => polarSpherePoint t theta) s 1) = _
  apply hchain.symm.trans
  rw [mvfderiv_eq_fderiv]
  change fderiv ℝ (fun t : ℝ =>
    (polarSpherePoint t theta : EuclideanSpace ℝ (Fin 3))) s 1 = _
  rw [(polarRadialAmbient_hasDerivAt s theta).hasFDerivAt.fderiv]
  exact ContinuousLinearMap.toSpanSingleton_apply_one (R₁ := ℝ) _

/-- The included angular tangent has the derivative of the literal ambient formula. -/
theorem polarAngularVelocity_dIncl (s theta : ℝ) :
    dIncl (n := 2) (polarSpherePoint s theta) (polarAngularVelocity s theta) =
      WithLp.toLp 2 ![-Real.sin s * Real.sin theta,
        Real.sin s * Real.cos theta, 0] := by
  have hc := (polarAngularCurve_contMDiff s).mdifferentiableAt (x := theta) (by simp)
  have hi := (contMDiff_coe_sphere (m := ∞) (n := 2)
    (E := EuclideanSpace ℝ (Fin 3))).mdifferentiableAt
    (x := polarSpherePoint s theta) (by simp)
  have hchain := mvfderiv_comp_apply (x := theta) (f := polarSpherePoint s)
    (g := ((↑) : RotationalSphere → EuclideanSpace ℝ (Fin 3))) hi hc 1
  change dIncl (n := 2) (polarSpherePoint s theta)
    (mfderiv 𝓘(ℝ, ℝ) (𝓡 2) (polarSpherePoint s) theta 1) = _
  apply hchain.symm.trans
  rw [mvfderiv_eq_fderiv]
  change fderiv ℝ (fun t : ℝ =>
    (polarSpherePoint s t : EuclideanSpace ℝ (Fin 3))) theta 1 = _
  rw [(polarAngularAmbient_hasDerivAt s theta).hasFDerivAt.fderiv]
  exact ContinuousLinearMap.toSpanSingleton_apply_one (R₁ := ℝ) _

private theorem polar_round_radial_inner (s theta : ℝ) :
    HeightMetricCoefficients.round.inner (polarSpherePoint s theta)
      (polarRadialVelocity s theta) (polarRadialVelocity s theta) = 1 := by
  rw [roundMetric_inner, polarRadialVelocity_dIncl]
  simp only [PiLp.inner_apply, Fin.sum_univ_succ, Matrix.cons_val_zero,
    Matrix.cons_val_succ, Fin.sum_univ_zero, add_zero, RCLike.inner_apply, conj_trivial]
  have ht := Real.cos_sq_add_sin_sq theta
  have hs := Real.cos_sq_add_sin_sq s
  nlinarith [congrArg (fun x : ℝ => Real.cos s ^ 2 * x) ht]

private theorem polar_round_angular_inner (s theta : ℝ) :
    HeightMetricCoefficients.round.inner (polarSpherePoint s theta)
      (polarAngularVelocity s theta) (polarAngularVelocity s theta) = Real.sin s ^ 2 := by
  rw [roundMetric_inner, polarAngularVelocity_dIncl]
  simp only [PiLp.inner_apply, Fin.sum_univ_succ, Matrix.cons_val_zero,
    Matrix.cons_val_succ, Fin.sum_univ_zero, add_zero, RCLike.inner_apply, conj_trivial]
  have ht := Real.cos_sq_add_sin_sq theta
  nlinarith [congrArg (fun x : ℝ => Real.sin s ^ 2 * x) ht]

private theorem polar_round_cross_inner (s theta : ℝ) :
    HeightMetricCoefficients.round.inner (polarSpherePoint s theta)
      (polarRadialVelocity s theta) (polarAngularVelocity s theta) = 0 := by
  rw [roundMetric_inner, polarRadialVelocity_dIncl, polarAngularVelocity_dIncl]
  simp only [PiLp.inner_apply, Fin.sum_univ_succ, Matrix.cons_val_zero,
    Matrix.cons_val_succ, Fin.sum_univ_zero, add_zero, RCLike.inner_apply, conj_trivial]
  ring

private theorem polarRadialVelocity_heightOneForm (s theta : ℝ) :
    heightOneForm (polarSpherePoint s theta)
      (fun _ : Fin 1 => polarRadialVelocity s theta) = -Real.sin s := by
  rw [heightOneForm_apply, mvfderiv_real_eq_mfderiv]
  change mfderiv (𝓡 2) 𝓘(ℝ, ℝ)
    (innerCoordFun (n := 2) (EuclideanSpace.single (2 : Fin 3) (1 : ℝ)))
    (polarSpherePoint s theta) _ = _
  rw [mfderiv_innerCoordFun, polarRadialVelocity_dIncl]
  simp only [EuclideanSpace.inner_single_left, map_one, one_mul]
  rfl

private theorem polarAngularVelocity_heightOneForm (s theta : ℝ) :
    heightOneForm (polarSpherePoint s theta)
      (fun _ : Fin 1 => polarAngularVelocity s theta) = 0 := by
  rw [heightOneForm_apply, mvfderiv_real_eq_mfderiv]
  change mfderiv (𝓡 2) 𝓘(ℝ, ℝ)
    (innerCoordFun (n := 2) (EuclideanSpace.single (2 : Fin 3) (1 : ℝ)))
    (polarSpherePoint s theta) _ = _
  rw [mfderiv_innerCoordFun, polarAngularVelocity_dIncl]
  simp only [EuclideanSpace.inner_single_left, map_one, one_mul]
  rfl

namespace RotationalProfile.PoleData

/-- The actual radial derivative has squared length `a(cos s)² / b(cos s)` everywhere. -/
theorem metric_inner_polarRadialVelocity (D : PoleData) (s theta : ℝ) :
    D.metric.inner (polarSpherePoint s theta)
      (polarRadialVelocity s theta) (polarRadialVelocity s theta) =
        D.a (Real.cos s) ^ 2 / D.b (Real.cos s) := by
  rw [D.metric_inner, sphereHeight_polarSpherePoint, polar_round_radial_inner,
    polarRadialVelocity_heightOneForm, mul_one, neg_mul_neg]
  have hs : Real.sin s * Real.sin s = 1 - Real.cos s ^ 2 := by
    nlinarith [Real.sin_sq_add_cos_sq s]
  rw [hs]
  exact D.radial_identity _ ⟨Real.neg_one_le_cos s, Real.cos_le_one s⟩

/-- The actual angular derivative has squared length `b(cos s) sin(s)²` everywhere. -/
theorem metric_inner_polarAngularVelocity (D : PoleData) (s theta : ℝ) :
    D.metric.inner (polarSpherePoint s theta)
      (polarAngularVelocity s theta) (polarAngularVelocity s theta) =
        D.b (Real.cos s) * Real.sin s ^ 2 := by
  rw [D.metric_inner, sphereHeight_polarSpherePoint, polar_round_angular_inner,
    polarAngularVelocity_heightOneForm]
  ring

/-- The actual radial and angular derivatives are metric orthogonal everywhere. -/
theorem metric_inner_polarRadialAngular (D : PoleData) (s theta : ℝ) :
    D.metric.inner (polarSpherePoint s theta)
      (polarRadialVelocity s theta) (polarAngularVelocity s theta) = 0 := by
  rw [D.metric_inner, sphereHeight_polarSpherePoint, polar_round_cross_inner,
    polarRadialVelocity_heightOneForm, polarAngularVelocity_heightOneForm]
  ring

end RotationalProfile.PoleData

/-- The two genuine coordinate derivatives are independent wherever `sin s` is nonzero. -/
theorem polarVelocities_linearIndependent (s theta : ℝ) (hs : Real.sin s ≠ 0) :
    LinearIndependent ℝ ![polarRadialVelocity s theta, polarAngularVelocity s theta] := by
  rw [Fintype.linearIndependent_iff]
  intro c hc i
  have h0 := congrArg (fun v => HeightMetricCoefficients.round.inner
    (polarSpherePoint s theta) (polarRadialVelocity s theta) v) hc
  have h1 := congrArg (fun v => HeightMetricCoefficients.round.inner
    (polarSpherePoint s theta) (polarAngularVelocity s theta) v) hc
  have hcross : HeightMetricCoefficients.round.inner (polarSpherePoint s theta)
      (polarAngularVelocity s theta) (polarRadialVelocity s theta) = 0 := by
    rw [HeightMetricCoefficients.round.symm, polar_round_cross_inner]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero, Matrix.cons_val_zero,
    Matrix.cons_val_succ, map_add, map_smul, smul_eq_mul, map_zero,
    polar_round_radial_inner, polar_round_cross_inner, mul_one, mul_zero] at h0
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero, Matrix.cons_val_zero,
    Matrix.cons_val_succ, map_add, map_smul, smul_eq_mul, map_zero,
    polar_round_angular_inner, hcross, mul_zero, zero_add] at h1
  have hc1 : c 1 = 0 := (mul_eq_zero.mp h1).resolve_right (pow_ne_zero 2 hs)
  fin_cases i
  · exact h0
  · exact hc1

/-- The genuine polar coordinate derivatives span the tangent space away from the poles. -/
theorem polarVelocities_span (s theta : ℝ) (hs : Real.sin s ≠ 0) :
    Submodule.span ℝ (Set.range ![polarRadialVelocity s theta, polarAngularVelocity s theta]) =
      ⊤ := by
  apply (polarVelocities_linearIndependent s theta hs).span_eq_top_of_card_eq_finrank'
  change Fintype.card (Fin 2) = Module.finrank ℝ (EuclideanSpace ℝ (Fin 2))
  simp

/-- The genuine radial and angular coordinate derivatives as a tangent basis. -/
def polarTangentBasis (s theta : ℝ) (hs : Real.sin s ≠ 0) :
    Module.Basis (Fin 2) ℝ (TangentSpace (𝓡 2) (polarSpherePoint s theta)) :=
  Module.Basis.mk (polarVelocities_linearIndependent s theta hs)
    (polarVelocities_span s theta hs).ge

/-- The first polar basis vector is the actual radial derivative. -/
@[simp] theorem polarTangentBasis_zero (s theta : ℝ) (hs : Real.sin s ≠ 0) :
    polarTangentBasis s theta hs 0 = polarRadialVelocity s theta := by
  simp [polarTangentBasis, Module.Basis.mk_apply]

/-- The second polar basis vector is the actual angular derivative. -/
@[simp] theorem polarTangentBasis_one (s theta : ℝ) (hs : Real.sin s ≠ 0) :
    polarTangentBasis s theta hs 1 = polarAngularVelocity s theta := by
  simp [polarTangentBasis, Module.Basis.mk_apply]

/-- Every sphere point lies on the actual polar orbit at colatitude `arccos(height)`.
This includes both poles. -/
theorem exists_polarSpherePoint_arccos (x : RotationalSphere) :
    ∃ theta : ℝ, polarSpherePoint (Real.arccos (sphereHeight x)) theta = x := by
  let z : ℂ := ⟨(x : EuclideanSpace ℝ (Fin 3)) 0, (x : EuclideanSpace ℝ (Fin 3)) 1⟩
  have hxnorm : ‖(x : EuclideanSpace ℝ (Fin 3))‖ = 1 := by
    simpa only [mem_sphere, dist_zero_right] using x.property
  have hsq := congrArg (fun r : ℝ => r ^ 2) hxnorm
  rw [EuclideanSpace.real_norm_sq_eq] at hsq
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hsq
  change (x : EuclideanSpace ℝ (Fin 3)) 0 ^ 2 +
    ((x : EuclideanSpace ℝ (Fin 3)) 1 ^ 2 + (x : EuclideanSpace ℝ (Fin 3)) 2 ^ 2) = 1 ^ 2 at hsq
  have hv := sphereHeight_mem_Icc x
  have hr : 0 ≤ 1 - sphereHeight x ^ 2 := by nlinarith [hv.1, hv.2]
  have hnorm : ‖z‖ = Real.sqrt (1 - sphereHeight x ^ 2) := by
    rw [← sq_eq_sq₀ (norm_nonneg _) (Real.sqrt_nonneg _), Real.sq_sqrt hr,
      Complex.sq_norm, Complex.normSq_apply, sphereHeight_apply]
    change (x : EuclideanSpace ℝ (Fin 3)) 0 * (x : EuclideanSpace ℝ (Fin 3)) 0 +
      (x : EuclideanSpace ℝ (Fin 3)) 1 * (x : EuclideanSpace ℝ (Fin 3)) 1 = _
    nlinarith [hsq]
  have hsin : Real.sin (Real.arccos (sphereHeight x)) = ‖z‖ := by
    rw [Real.sin_arccos, hnorm]
  refine ⟨z.arg, ?_⟩
  apply Subtype.ext
  rw [polarSpherePoint_coe]
  ext i
  fin_cases i
  · change Real.sin (Real.arccos (sphereHeight x)) * Real.cos z.arg = _
    rw [hsin]
    exact Complex.norm_mul_cos_arg z
  · change Real.sin (Real.arccos (sphereHeight x)) * Real.sin z.arg = _
    rw [hsin]
    exact Complex.norm_mul_sin_arg z
  · change Real.cos (Real.arccos (sphereHeight x)) = _
    rw [Real.cos_arccos hv.1 hv.2]
    exact sphereHeight_apply x

end RicciFlowSharpEstimate.Geometry
