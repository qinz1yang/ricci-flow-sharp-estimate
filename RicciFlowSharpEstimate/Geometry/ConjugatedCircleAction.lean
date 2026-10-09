/-
Copyright (c) 2026 Ziyang Qin. All rights reserved.
No license is granted by this file.
Authors: Ziyang Qin
-/
import RicciFlowSharpEstimate.Geometry.ConjugatedRotationalAverage

/-!
# The conjugated circle action and its genuine Haar projector

The same diffeomorphism conjugates the actual sphere action and pulls back the
produced rotational metric. The already defined transported projector is exactly
the normalized integral of this action's derivatives in every tensor slot.
-/

noncomputable section

namespace RicciFlowSharpEstimate.Geometry

open Bundle DifferentialGeometry DifferentialGeometry.Tensor0SBundle
open MeasureTheory
open scoped Manifold ContDiff

/-- Conjugate the actual native circle action by the representing diffeomorphism. -/
def conjugatedCircleSphereDiffeo
    (F : RotationalSphere ≃ₘ⟮𝓡 2, 𝓡 2⟯ RotationalSphere) (z : Circle) :
    RotationalSphere ≃ₘ⟮𝓡 2, 𝓡 2⟯ RotationalSphere :=
  (F.trans (circleSphereDiffeo z)).trans F.symm

/-- The conjugated action is literally `F⁻¹ ∘ ρ(z) ∘ F`. -/
theorem conjugatedCircleSphereDiffeo_apply
    (F : RotationalSphere ≃ₘ⟮𝓡 2, 𝓡 2⟯ RotationalSphere) (z : Circle)
    (x : RotationalSphere) :
    conjugatedCircleSphereDiffeo F z x = F.symm (circleSphereDiffeo z (F x)) := rfl

/-- The circle identity acts as the identity on the same sphere. -/
@[simp]
theorem conjugatedCircleSphereDiffeo_one
    (F : RotationalSphere ≃ₘ⟮𝓡 2, 𝓡 2⟯ RotationalSphere) (x : RotationalSphere) :
    conjugatedCircleSphereDiffeo F 1 x = x := by
  simp only [conjugatedCircleSphereDiffeo_apply, circleSphereDiffeo_one,
    Diffeomorph.symm_apply_apply]

/-- Circle multiplication composes the actual conjugated maps. -/
theorem conjugatedCircleSphereDiffeo_mul
    (F : RotationalSphere ≃ₘ⟮𝓡 2, 𝓡 2⟯ RotationalSphere) (z w : Circle)
    (x : RotationalSphere) :
    conjugatedCircleSphereDiffeo F (z * w) x =
      conjugatedCircleSphereDiffeo F z (conjugatedCircleSphereDiffeo F w x) := by
  simp only [conjugatedCircleSphereDiffeo_apply, circleSphereDiffeo_mul,
    Diffeomorph.apply_symm_apply]

/-- The explicit conjugated maps define an actual circle action. -/
@[instance_reducible]
def conjugatedCircleSphereAction
    (F : RotationalSphere ≃ₘ⟮𝓡 2, 𝓡 2⟯ RotationalSphere) :
    MulAction Circle RotationalSphere where
  smul z x := conjugatedCircleSphereDiffeo F z x
  one_smul := conjugatedCircleSphereDiffeo_one F
  mul_smul := conjugatedCircleSphereDiffeo_mul F

/-- Circle inversion is inversion of the actual conjugated diffeomorphism. -/
@[simp]
theorem conjugatedCircleSphereDiffeo_inv
    (F : RotationalSphere ≃ₘ⟮𝓡 2, 𝓡 2⟯ RotationalSphere) (z : Circle) :
    conjugatedCircleSphereDiffeo F z⁻¹ = (conjugatedCircleSphereDiffeo F z).symm := by
  apply Diffeomorph.ext
  intro x
  apply (conjugatedCircleSphereDiffeo F z).injective
  change conjugatedCircleSphereDiffeo F z (conjugatedCircleSphereDiffeo F z⁻¹ x) =
    conjugatedCircleSphereDiffeo F z ((conjugatedCircleSphereDiffeo F z).symm x)
  rw [Diffeomorph.apply_symm_apply, ← conjugatedCircleSphereDiffeo_mul]
  simp

/-- The actual real-angle parametrization of the conjugated circle action. -/
def conjugatedAngleRotation
    (F : RotationalSphere ≃ₘ⟮𝓡 2, 𝓡 2⟯ RotationalSphere) (theta : ℝ) :
    RotationalSphere ≃ₘ⟮𝓡 2, 𝓡 2⟯ RotationalSphere :=
  conjugatedCircleSphereDiffeo F (Circle.exp theta)

/-- Literal evaluation of the conjugated angle map. -/
theorem conjugatedAngleRotation_apply
    (F : RotationalSphere ≃ₘ⟮𝓡 2, 𝓡 2⟯ RotationalSphere) (theta : ℝ)
    (x : RotationalSphere) :
    conjugatedAngleRotation F theta x = F.symm (angleRotation theta (F x)) := rfl

@[simp]
theorem conjugatedAngleRotation_zero
    (F : RotationalSphere ≃ₘ⟮𝓡 2, 𝓡 2⟯ RotationalSphere) (x : RotationalSphere) :
    conjugatedAngleRotation F 0 x = x := by
  simp only [conjugatedAngleRotation_apply, angleRotation_zero, Diffeomorph.symm_apply_apply]

/-- Angle addition composes the same conjugated rotations. -/
theorem conjugatedAngleRotation_add
    (F : RotationalSphere ≃ₘ⟮𝓡 2, 𝓡 2⟯ RotationalSphere) (theta phi : ℝ)
    (x : RotationalSphere) :
    conjugatedAngleRotation F (theta + phi) x =
      conjugatedAngleRotation F theta (conjugatedAngleRotation F phi x) := by
  simp only [conjugatedAngleRotation, Circle.exp_add, conjugatedCircleSphereDiffeo_mul]

@[simp]
theorem conjugatedAngleRotation_neg
    (F : RotationalSphere ≃ₘ⟮𝓡 2, 𝓡 2⟯ RotationalSphere) (theta : ℝ) :
    conjugatedAngleRotation F (-theta) = (conjugatedAngleRotation F theta).symm := by
  simp only [conjugatedAngleRotation, Circle.exp_neg, conjugatedCircleSphereDiffeo_inv]

/-- The conjugated diffeomorphism family retains the actual `2*pi` period. -/
theorem conjugatedAngleRotation_periodic
    (F : RotationalSphere ≃ₘ⟮𝓡 2, 𝓡 2⟯ RotationalSphere) :
    Function.Periodic (conjugatedAngleRotation F) (2 * Real.pi) := by
  intro theta
  change (F.trans (angleRotation (theta + 2 * Real.pi))).trans F.symm =
    (F.trans (angleRotation theta)).trans F.symm
  rw [angleRotation_periodic theta]

/-- The conjugated angle action is jointly smooth on the entire sphere. -/
theorem conjugatedAngleRotation_contMDiff
    (F : RotationalSphere ≃ₘ⟮𝓡 2, 𝓡 2⟯ RotationalSphere) :
    ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 2)) (𝓡 2) ∞
      (fun p : ℝ × RotationalSphere => conjugatedAngleRotation F p.1 p.2) :=
  F.symm.contMDiff.comp (angleRotation_contMDiff.comp
    (contMDiff_fst.prodMk (F.contMDiff.comp contMDiff_snd)))

/-- The actual conjugated action preserves the metric pulled back by the same map. -/
theorem RotationalProfile.PoleData.pullbackMetric_conjugatedCircleSphereDiffeo
    (D : RotationalProfile.PoleData)
    (F : RotationalSphere ≃ₘ⟮𝓡 2, 𝓡 2⟯ RotationalSphere) (z : Circle) :
    Diffeomorph.pullbackMetric (Diffeomorph.pullbackMetric D.metric F)
      (conjugatedCircleSphereDiffeo F z) = Diffeomorph.pullbackMetric D.metric F := by
  simp only [conjugatedCircleSphereDiffeo, ← Diffeomorph.pullbackMetric_trans,
    pullbackMetric_symm_apply, D.pullbackMetric_circleSphereDiffeo]

/-- The actual tangent derivative preserves the same pulled-back metric inner product. -/
theorem RotationalProfile.PoleData.metric_inner_conjugatedCircleSphereDiffeo
    (D : RotationalProfile.PoleData)
    (F : RotationalSphere ≃ₘ⟮𝓡 2, 𝓡 2⟯ RotationalSphere) (z : Circle)
    (x : RotationalSphere) (v w : TangentSpace (𝓡 2) x) :
    (Diffeomorph.pullbackMetric D.metric F).inner (conjugatedCircleSphereDiffeo F z x)
      (mfderiv (𝓡 2) (𝓡 2) (conjugatedCircleSphereDiffeo F z) x v)
      (mfderiv (𝓡 2) (𝓡 2) (conjugatedCircleSphereDiffeo F z) x w) =
      (Diffeomorph.pullbackMetric D.metric F).inner x v w := by
  have h := congrArg (fun g => g.inner x v w)
    (D.pullbackMetric_conjugatedCircleSphereDiffeo F z)
  simpa only [Diffeomorph.pullbackMetric_inner] using h

/-- Every conjugated angle rotation preserves the represented metric. -/
theorem RotationalProfile.PoleData.pullbackMetric_conjugatedAngleRotation
    (D : RotationalProfile.PoleData)
    (F : RotationalSphere ≃ₘ⟮𝓡 2, 𝓡 2⟯ RotationalSphere) (theta : ℝ) :
    Diffeomorph.pullbackMetric (Diffeomorph.pullbackMetric D.metric F)
      (conjugatedAngleRotation F theta) = Diffeomorph.pullbackMetric D.metric F :=
  D.pullbackMetric_conjugatedCircleSphereDiffeo F (Circle.exp theta)

/-- Pullback by the actual conjugated action is the conjugated derivative pullback. -/
theorem diffeomorphTensorPullback_conjugatedCircleSphereDiffeo
    (F : RotationalSphere ≃ₘ⟮𝓡 2, 𝓡 2⟯ RotationalSphere) (z : Circle) {s : ℕ}
    (A : Tensor0SField (𝕜 := ℝ) (I := 𝓡 2) (M := RotationalSphere) (n := ∞) s) :
    diffeomorphTensorPullback (conjugatedCircleSphereDiffeo F z) A =
      diffeomorphTensorPullback F (diffeomorphTensorPullback (circleSphereDiffeo z)
        (diffeomorphTensorPullback F.symm A)) := by
  simp only [conjugatedCircleSphereDiffeo, diffeomorphTensorPullback_trans]

/-- The tensor orbit of the actual conjugated angle action is jointly smooth. -/
theorem contMDiff_diffeomorphTensorPullback_conjugatedAngleRotation
    (F : RotationalSphere ≃ₘ⟮𝓡 2, 𝓡 2⟯ RotationalSphere) {s : ℕ}
    (A : Tensor0SField (𝕜 := ℝ) (I := 𝓡 2) (M := RotationalSphere) (n := ∞) s) :
    ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 2))
      ((𝓡 2).prod 𝓘(ℝ, Tensor0SModel s ℝ (EuclideanSpace ℝ (Fin 2)))) ∞
      (fun p : ℝ × RotationalSphere => TotalSpace.mk'
        (Tensor0SModel s ℝ (EuclideanSpace ℝ (Fin 2))) p.2
        (diffeomorphTensorPullback (conjugatedAngleRotation F p.1) A p.2)) :=
  contMDiff_diffeomorphTensorPullback_family (conjugatedAngleRotation F)
    (conjugatedAngleRotation_contMDiff F) A

/-- The literal all-slot conjugated orbit is integrable on every compact interval. -/
theorem intervalIntegrable_conjugatedAngleRotation_apply
    (F : RotationalSphere ≃ₘ⟮𝓡 2, 𝓡 2⟯ RotationalSphere) {s : ℕ}
    (A : Tensor0SField (𝕜 := ℝ) (I := 𝓡 2) (M := RotationalSphere) (n := ∞) s)
    (x : RotationalSphere) (v : Fin s → TangentSpace (𝓡 2) x) (a b : ℝ) :
    IntervalIntegrable
      (fun theta => A (conjugatedAngleRotation F theta x)
        (fun i => mfderiv (𝓡 2) (𝓡 2) (conjugatedAngleRotation F theta) x (v i)))
      volume a b := by
  simpa only [diffeomorphTensorPullback_apply] using
    intervalIntegrable_diffeomorphTensorPullback_family_eval (conjugatedAngleRotation F)
      (conjugatedAngleRotation_contMDiff F) A x v volume a b

/-- The existing transported projector is the normalized integral of the actual conjugated orbit. -/
theorem conjugatedRotationalAverage_eval
    (F : RotationalSphere ≃ₘ⟮𝓡 2, 𝓡 2⟯ RotationalSphere) {s : ℕ}
    (A : Tensor0SField (𝕜 := ℝ) (I := 𝓡 2) (M := RotationalSphere) (n := ∞) s)
    (x : RotationalSphere) (v : Fin s → TangentSpace (𝓡 2) x) :
    conjugatedRotationalAverage F A x v = (2 * Real.pi)⁻¹ *
      ∫ theta in (0 : ℝ)..2 * Real.pi,
        diffeomorphTensorPullback (conjugatedAngleRotation F theta) A x v := by
  change diffeomorphTensorPullback F
    (rotationalAverage (diffeomorphTensorPullback F.symm A)) x v = _
  rw [diffeomorphTensorPullback_apply, rotationalAverage_eval]
  congr 1
  apply intervalIntegral.integral_congr
  intro theta _
  simp only [conjugatedAngleRotation, diffeomorphTensorPullback_conjugatedCircleSphereDiffeo,
    diffeomorphTensorPullback_apply, angleRotation]

/-- Every tensor rank and slot tuple has the literal normalized derivative-pullback formula. -/
theorem conjugatedRotationalAverage_apply
    (F : RotationalSphere ≃ₘ⟮𝓡 2, 𝓡 2⟯ RotationalSphere) {s : ℕ}
    (A : Tensor0SField (𝕜 := ℝ) (I := 𝓡 2) (M := RotationalSphere) (n := ∞) s)
    (x : RotationalSphere) (v : Fin s → TangentSpace (𝓡 2) x) :
    conjugatedRotationalAverage F A x v = (2 * Real.pi)⁻¹ *
      ∫ theta in (0 : ℝ)..2 * Real.pi,
        A (conjugatedAngleRotation F theta x)
          (fun i => mfderiv (𝓡 2) (𝓡 2) (conjugatedAngleRotation F theta) x (v i)) := by
  simp only [conjugatedRotationalAverage_eval, diffeomorphTensorPullback_apply]

/-- The transported average is invariant under every actual conjugated circle element. -/
theorem diffeomorphTensorPullback_conjugatedCircle_conjugatedRotationalAverage
    (F : RotationalSphere ≃ₘ⟮𝓡 2, 𝓡 2⟯ RotationalSphere) (z : Circle) {s : ℕ}
    (A : Tensor0SField (𝕜 := ℝ) (I := 𝓡 2) (M := RotationalSphere) (n := ∞) s) :
    diffeomorphTensorPullback (conjugatedCircleSphereDiffeo F z)
      (conjugatedRotationalAverage F A) = conjugatedRotationalAverage F A := by
  rw [diffeomorphTensorPullback_conjugatedCircleSphereDiffeo,
    diffeomorphTensorPullback_symm_conjugatedRotationalAverage,
    diffeomorphTensorPullback_circle_rotationalAverage]
  rfl

/-- The projector fixes exactly the tensors invariant under every conjugated circle element. -/
theorem conjugatedRotationalAverage_eq_self_iff
    (F : RotationalSphere ≃ₘ⟮𝓡 2, 𝓡 2⟯ RotationalSphere) {s : ℕ}
    (A : Tensor0SField (𝕜 := ℝ) (I := 𝓡 2) (M := RotationalSphere) (n := ∞) s) :
    conjugatedRotationalAverage F A = A ↔
      ∀ z : Circle, diffeomorphTensorPullback (conjugatedCircleSphereDiffeo F z) A = A := by
  rw [conjugatedRotationalAverage_eq_self_iff_pullback, rotationalAverage_eq_self_iff]
  constructor
  · intro h z
    rw [diffeomorphTensorPullback_conjugatedCircleSphereDiffeo, h z,
      diffeomorphTensorPullback_apply_symm]
  · intro h z
    have heq := congrArg (diffeomorphTensorPullback F.symm) (h z)
    simpa only [diffeomorphTensorPullback_conjugatedCircleSphereDiffeo,
      diffeomorphTensorPullback_symm_apply] using heq

end RicciFlowSharpEstimate.Geometry
