/-
Copyright (c) 2026 Ziyang Qin. All rights reserved.
No license is granted by this file.
Authors: Ziyang Qin
-/
import RicciFlowSharpEstimate.Geometry.OneFormDissipationNaturality

/-!
# Algebra of actual smooth pullbacks

The genuine derivative pullback preserves zero, negation and subtraction,
and its actual inverse makes it injective. Metric pullback has the same
two inverse composition laws.
-/

namespace RicciFlowSharpEstimate.Geometry

open DifferentialGeometry DifferentialGeometry.Tensor0SBundle
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

@[simp]
theorem diffeomorphTensorPullback_zero (F : M ≃ₘ⟮I, I⟯ M) (s : ℕ) :
    diffeomorphTensorPullback F
      (0 : Tensor0SField (𝕜 := ℝ) (I := I) (M := M) (n := ∞) s) = 0 := by
  ext x v
  simp

theorem diffeomorphTensorPullback_neg (F : M ≃ₘ⟮I, I⟯ M) {s : ℕ}
    (A : Tensor0SField (𝕜 := ℝ) (I := I) (M := M) (n := ∞) s) :
    diffeomorphTensorPullback F (-A) = -diffeomorphTensorPullback F A := by
  simpa only [neg_one_smul] using diffeomorphTensorPullback_smul F (-1) A

theorem diffeomorphTensorPullback_sub (F : M ≃ₘ⟮I, I⟯ M) {s : ℕ}
    (A B : Tensor0SField (𝕜 := ℝ) (I := I) (M := M) (n := ∞) s) :
    diffeomorphTensorPullback F (A - B) =
      diffeomorphTensorPullback F A - diffeomorphTensorPullback F B := by
  simp only [sub_eq_add_neg, diffeomorphTensorPullback_add, diffeomorphTensorPullback_neg]

/-- The inverse derivative pullback detects equality of the original tensors. -/
theorem diffeomorphTensorPullback_injective (F : M ≃ₘ⟮I, I⟯ M) (s : ℕ) :
    Function.Injective (diffeomorphTensorPullback F (s := s)) := by
  intro A B h
  simpa only [diffeomorphTensorPullback_symm_apply] using
    congrArg (diffeomorphTensorPullback F.symm) h

@[simp]
theorem diffeomorphTensorPullback_eq_zero_iff (F : M ≃ₘ⟮I, I⟯ M) {s : ℕ}
    (A : Tensor0SField (𝕜 := ℝ) (I := I) (M := M) (n := ∞) s) :
    diffeomorphTensorPullback F A = 0 ↔ A = 0 := by
  constructor
  · intro h
    simpa only [diffeomorphTensorPullback_symm_apply, diffeomorphTensorPullback_zero] using
      congrArg (diffeomorphTensorPullback F.symm) h
  · rintro rfl
    exact diffeomorphTensorPullback_zero F s

variable [T2Space M]

@[simp]
theorem pullbackMetric_symm_apply (g : SmoothRiemannianMetric I M)
    (F : M ≃ₘ⟮I, I⟯ M) :
    Diffeomorph.pullbackMetric (Diffeomorph.pullbackMetric g F) F.symm = g := by
  rw [Diffeomorph.pullbackMetric_trans, F.symm_trans_self, Diffeomorph.pullbackMetric_refl]

@[simp]
theorem pullbackMetric_apply_symm (g : SmoothRiemannianMetric I M)
    (F : M ≃ₘ⟮I, I⟯ M) :
    Diffeomorph.pullbackMetric (Diffeomorph.pullbackMetric g F.symm) F = g := by
  rw [Diffeomorph.pullbackMetric_trans, F.self_trans_symm, Diffeomorph.pullbackMetric_refl]

end RicciFlowSharpEstimate.Geometry
