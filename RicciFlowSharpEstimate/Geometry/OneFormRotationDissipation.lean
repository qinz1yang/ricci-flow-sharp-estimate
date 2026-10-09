/-
Copyright (c) 2026 Ziyang Qin. All rights reserved.
No license is granted by this file.
Authors: Ziyang Qin
-/
import RicciFlowSharpEstimate.Geometry.OneFormRotation
import RicciFlowSharpEstimate.Geometry.SurfaceRotationContractions
import RicciFlowSharpEstimate.Geometry.OneFormDissipation

/-!
# Hodge rotation preserves the complete one-form action

Parallelness is derived from the smooth unit alternating area tensor. All four
terms use the actual canonical derivatives, not independently supplied jets.
-/

noncomputable section

namespace RicciFlowSharpEstimate.Geometry

open DifferentialGeometry DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Tensor.RicciIdentity
open DifferentialGeometry.PDE.RicciFlow
open scoped Manifold ContDiff

local notation "𝓡₂" => 𝓘(ℝ, EuclideanSpace ℝ (Fin 2))

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M]
variable [IsManifold 𝓡₂ ∞ M] [T2Space M]

/-- Hodge rotation preserves the literal complete density on a smooth surface. -/
theorem oneFormDissipationDensity_oneFormAreaContraction
    (g : SmoothRiemannianMetric 𝓡₂ M)
    (Ω : TwoTensorSection (I := 𝓡₂) (M := M))
    (hΩalt : ∀ x U V, Ω x (vec2 U V) = -Ω x (vec2 V U))
    (hΩnorm : ∀ x, normSq0S g x 2 (Ω x) = 2)
    (h : OneFormSection (I := 𝓡₂) (M := M)) (x : M) :
    oneFormDissipationDensity g (oneFormAreaContraction g Ω h) x =
      oneFormDissipationDensity g h x := by
  have hnorm (k : OneFormSection (I := 𝓡₂) (M := M)) :
      normSq0S g x 1 (oneFormAreaContraction g Ω k x) = normSq0S g x 1 (k x) :=
    normSq0S_one_eq_of_rotation finrank_euclideanSpace_fin g x (Ω x)
      (hΩalt x) (hΩnorm x) _ _ (oneFormAreaContraction_apply g Ω k x)
  have hnabla := normSq0S_two_eq_of_rotation finrank_euclideanSpace_fin g x (Ω x)
    (hΩalt x) (hΩnorm x) (metricNabla0S g h x)
    (metricNabla0S g (oneFormAreaContraction g Ω h) x)
    (metricNabla0S_oneFormAreaContraction finrank_euclideanSpace_fin g Ω hΩalt hΩnorm h x)
  have hahlfors := normSq0S_ahlforsPart_eq_of_rotation finrank_euclideanSpace_fin g x (Ω x)
    (hΩalt x) (hΩnorm x) (metricNabla0S g h)
    (metricNabla0S g (oneFormAreaContraction g Ω h))
    (metricNabla0S_oneFormAreaContraction finrank_euclideanSpace_fin g Ω hΩalt hΩnorm h x)
  simp only [oneFormDissipationDensity,
    roughLap0SField_oneFormAreaContraction finrank_euclideanSpace_fin g Ω hΩalt hΩnorm,
    hnorm, hnabla, hahlfors]

/-- Hodge rotation preserves the full four-term action, with no curvature sign assumption. -/
theorem oneFormDissipation_oneFormAreaContraction [CompactSpace M]
    (g : SmoothRiemannianMetric 𝓡₂ M)
    (Ω : TwoTensorSection (I := 𝓡₂) (M := M))
    (hΩalt : ∀ x U V, Ω x (vec2 U V) = -Ω x (vec2 V U))
    (hΩnorm : ∀ x, normSq0S g x 2 (Ω x) = 2)
    (h : OneFormSection (I := 𝓡₂) (M := M)) :
    oneFormDissipation g (oneFormAreaContraction g Ω h) = oneFormDissipation g h := by
  unfold oneFormDissipation
  simp_rw [oneFormDissipationDensity_oneFormAreaContraction g Ω hΩalt hΩnorm]

end RicciFlowSharpEstimate.Geometry
