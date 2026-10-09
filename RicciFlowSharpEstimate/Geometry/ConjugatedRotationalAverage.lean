/-
Copyright (c) 2026 Ziyang Qin. All rights reserved.
No license is granted by this file.
Authors: Ziyang Qin
-/
import RicciFlowSharpEstimate.Geometry.PullbackAlgebra
import RicciFlowSharpEstimate.Geometry.RotationalAverage

/-!
# Conjugating the genuine rotational projector

The same diffeomorphism transports the original tensor into the produced
geometry, applies its actual Haar average, and pulls the result back.
-/

noncomputable section

namespace RicciFlowSharpEstimate.Geometry

open DifferentialGeometry DifferentialGeometry.Tensor0SBundle
open scoped Manifold ContDiff

/-- The smooth tensor projector transported by the actual derivative of F. -/
def conjugatedRotationalAverage (F : RotationalSphere ≃ₘ⟮𝓡 2, 𝓡 2⟯ RotationalSphere)
    {s : ℕ} (A : Tensor0SField (𝕜 := ℝ) (I := 𝓡 2) (M := RotationalSphere) (n := ∞) s) :
    Tensor0SField (𝕜 := ℝ) (I := 𝓡 2) (M := RotationalSphere) (n := ∞) s :=
  diffeomorphTensorPullback F (rotationalAverage (diffeomorphTensorPullback F.symm A))

@[simp]
theorem conjugatedRotationalAverage_refl {s : ℕ}
    (A : Tensor0SField (𝕜 := ℝ) (I := 𝓡 2) (M := RotationalSphere) (n := ∞) s) :
    conjugatedRotationalAverage (_root_.Diffeomorph.refl (𝓡 2) RotationalSphere ∞) A =
      rotationalAverage A := by
  change diffeomorphTensorPullback (_root_.Diffeomorph.refl (𝓡 2) RotationalSphere ∞)
    (rotationalAverage (diffeomorphTensorPullback
      (_root_.Diffeomorph.refl (𝓡 2) RotationalSphere ∞) A)) = rotationalAverage A
  simp only [diffeomorphTensorPullback_refl]

/-- Pulling an original tensor back intertwines the two actual projectors. -/
theorem conjugatedRotationalAverage_diffeomorphTensorPullback
    (F : RotationalSphere ≃ₘ⟮𝓡 2, 𝓡 2⟯ RotationalSphere) {s : ℕ}
    (A : Tensor0SField (𝕜 := ℝ) (I := 𝓡 2) (M := RotationalSphere) (n := ∞) s) :
    conjugatedRotationalAverage F (diffeomorphTensorPullback F A) =
      diffeomorphTensorPullback F (rotationalAverage A) := by
  simp only [conjugatedRotationalAverage, diffeomorphTensorPullback_symm_apply]

/-- Inverse pullback retains the actual original Haar projector. -/
theorem diffeomorphTensorPullback_symm_conjugatedRotationalAverage
    (F : RotationalSphere ≃ₘ⟮𝓡 2, 𝓡 2⟯ RotationalSphere) {s : ℕ}
    (A : Tensor0SField (𝕜 := ℝ) (I := 𝓡 2) (M := RotationalSphere) (n := ∞) s) :
    diffeomorphTensorPullback F.symm (conjugatedRotationalAverage F A) =
      rotationalAverage (diffeomorphTensorPullback F.symm A) := by
  simp only [conjugatedRotationalAverage, diffeomorphTensorPullback_symm_apply]

@[simp]
theorem conjugatedRotationalAverage_zero
    (F : RotationalSphere ≃ₘ⟮𝓡 2, 𝓡 2⟯ RotationalSphere) (s : ℕ) :
    conjugatedRotationalAverage F
      (0 : Tensor0SField (𝕜 := ℝ) (I := 𝓡 2) (M := RotationalSphere) (n := ∞) s) = 0 := by
  simp only [conjugatedRotationalAverage, diffeomorphTensorPullback_zero, rotationalAverage_zero]

theorem conjugatedRotationalAverage_add
    (F : RotationalSphere ≃ₘ⟮𝓡 2, 𝓡 2⟯ RotationalSphere) {s : ℕ}
    (A B : Tensor0SField (𝕜 := ℝ) (I := 𝓡 2) (M := RotationalSphere) (n := ∞) s) :
    conjugatedRotationalAverage F (A + B) =
      conjugatedRotationalAverage F A + conjugatedRotationalAverage F B := by
  simp only [conjugatedRotationalAverage, diffeomorphTensorPullback_add, rotationalAverage_add]

theorem conjugatedRotationalAverage_smul
    (F : RotationalSphere ≃ₘ⟮𝓡 2, 𝓡 2⟯ RotationalSphere) {s : ℕ} (c : ℝ)
    (A : Tensor0SField (𝕜 := ℝ) (I := 𝓡 2) (M := RotationalSphere) (n := ∞) s) :
    conjugatedRotationalAverage F (c • A) = c • conjugatedRotationalAverage F A := by
  simp only [conjugatedRotationalAverage, diffeomorphTensorPullback_smul, rotationalAverage_smul]

theorem conjugatedRotationalAverage_sub
    (F : RotationalSphere ≃ₘ⟮𝓡 2, 𝓡 2⟯ RotationalSphere) {s : ℕ}
    (A B : Tensor0SField (𝕜 := ℝ) (I := 𝓡 2) (M := RotationalSphere) (n := ∞) s) :
    conjugatedRotationalAverage F (A - B) =
      conjugatedRotationalAverage F A - conjugatedRotationalAverage F B := by
  simp only [conjugatedRotationalAverage, diffeomorphTensorPullback_sub, rotationalAverage_sub]

/-- The transported smooth projector is genuinely idempotent. -/
theorem conjugatedRotationalAverage_idempotent
    (F : RotationalSphere ≃ₘ⟮𝓡 2, 𝓡 2⟯ RotationalSphere) {s : ℕ}
    (A : Tensor0SField (𝕜 := ℝ) (I := 𝓡 2) (M := RotationalSphere) (n := ∞) s) :
    conjugatedRotationalAverage F (conjugatedRotationalAverage F A) =
      conjugatedRotationalAverage F A := by
  simp only [conjugatedRotationalAverage, diffeomorphTensorPullback_symm_apply,
    rotationalAverage_idempotent]

theorem conjugatedRotationalAverage_sub_average
    (F : RotationalSphere ≃ₘ⟮𝓡 2, 𝓡 2⟯ RotationalSphere) {s : ℕ}
    (A : Tensor0SField (𝕜 := ℝ) (I := 𝓡 2) (M := RotationalSphere) (n := ∞) s) :
    conjugatedRotationalAverage F (A - conjugatedRotationalAverage F A) = 0 := by
  rw [conjugatedRotationalAverage_sub, conjugatedRotationalAverage_idempotent, sub_self]

/-- Fixed points are retained in both directions by the same inverse pullback. -/
theorem conjugatedRotationalAverage_eq_self_iff_pullback
    (F : RotationalSphere ≃ₘ⟮𝓡 2, 𝓡 2⟯ RotationalSphere) {s : ℕ}
    (A : Tensor0SField (𝕜 := ℝ) (I := 𝓡 2) (M := RotationalSphere) (n := ∞) s) :
    conjugatedRotationalAverage F A = A ↔
      rotationalAverage (diffeomorphTensorPullback F.symm A) =
        diffeomorphTensorPullback F.symm A := by
  constructor
  · intro h
    simpa only [diffeomorphTensorPullback_symm_conjugatedRotationalAverage] using
      congrArg (diffeomorphTensorPullback F.symm) h
  · intro h
    simpa only [conjugatedRotationalAverage, diffeomorphTensorPullback_apply_symm] using
      congrArg (diffeomorphTensorPullback F) h

end RicciFlowSharpEstimate.Geometry
