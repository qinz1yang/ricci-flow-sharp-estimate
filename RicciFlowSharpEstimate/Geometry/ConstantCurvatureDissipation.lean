/-
Copyright (c) 2026 Ziyang Qin. All rights reserved.
No license is granted by this file.
Authors: Ziyang Qin
-/
import RicciFlowSharpEstimate.Geometry.OneFormDissipation
import RicciFlowSharpEstimate.Geometry.CanonicalTensorIntegration

/-!
# One-form dissipation at constant curvature

Canonical Green integration completes the original four-term action into three
nonnegative squares when the actual Gauss curvature is a nonnegative constant.
Every smooth one-form on a compact surface is allowed.
-/

noncomputable section

namespace RicciFlowSharpEstimate.Geometry

open Bundle MeasureTheory DifferentialGeometry DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Geometry.Operator DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow DifferentialGeometry.Tensor.RSTensor
open DifferentialGeometry.Integral.Connection DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Tensor.RicciIdentity
open scoped Manifold ContDiff

local notation "𝓡₂" => 𝓘(ℝ, EuclideanSpace ℝ (Fin 2))

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M]
variable [IsManifold 𝓡₂ ∞ M] [T2Space M] [CompactSpace M]

private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

private theorem normSq_field_integrable (g : SmoothRiemannianMetric 𝓡₂ M) {s : ℕ}
    (T : Tensor0SField (𝕜 := ℝ) (I := 𝓡₂) (M := M) (n := ∞) s) :
    Integrable (fun x => normSq0S g x s (T x)) (riemannianVolumeMeasure 𝓡₂ M g) := by
  let := riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace g
  exact (normSq0S_smooth g T).continuous.integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

private theorem inner_field_integrable (g : SmoothRiemannianMetric 𝓡₂ M) {s : ℕ}
    (T U : Tensor0SField (𝕜 := ℝ) (I := 𝓡₂) (M := M) (n := ∞) s) :
    Integrable (fun x => inner0S g x s (T x) (U x))
      (riemannianVolumeMeasure 𝓡₂ M g) := by
  have heq : (fun x => inner0S g x s (T x) (U x)) = fun x =>
      (normSq0S g x s ((T + U) x) - normSq0S g x s (T x) -
        normSq0S g x s (U x)) / 2 := by
    funext x
    change inner0S g x s (T x) (U x) =
      (normSq0S g x s (T x + U x) - normSq0S g x s (T x) -
        normSq0S g x s (U x)) / 2
    rw [normSq0S_add]
    ring
  rw [heq]
  exact (((normSq_field_integrable g (T + U)).sub
    (normSq_field_integrable g T)).sub (normSq_field_integrable g U)).div_const 2

/-- The completed-square density is integrable for every smooth form and every
real constant, independently of the curvature constraint. -/
theorem oneFormDissipation_squares_integrable (g : SmoothRiemannianMetric 𝓡₂ M)
    (κ : ℝ) (h : OneFormSection (I := 𝓡₂) (M := M)) :
    Integrable (fun x =>
      normSq0S g x 1 (roughLap0SField g h x + κ • h x) +
        κ * normSq0S g x 2 (metricNabla0S g h x) +
        2 * κ * normSq0S g x 2 (ahlforsPart g (metricNabla0S g h) x))
      (riemannianVolumeMeasure 𝓡₂ M g) := by
  exact ((normSq_field_integrable g (roughLap0SField g h + κ • h)).add
    ((normSq_field_integrable g (metricNabla0S g h)).const_mul κ)).add
      ((normSq_field_integrable g (ahlforsPart g (metricNabla0S g h))).const_mul (2 * κ))

/-- Green's identity completes the original dissipation into squares for a
metric whose actual Gauss curvature is constant. -/
theorem oneFormDissipation_eq_integral_squares_of_constant_curvature
    (g : SmoothRiemannianMetric 𝓡₂ M) (κ : ℝ)
    (hK : ∀ x : M, metricScalarAt g x / 2 = κ)
    (h : OneFormSection (I := 𝓡₂) (M := M)) :
    oneFormDissipation g h =
      ∫ x, (normSq0S g x 1 (roughLap0SField g h x + κ • h x) +
        κ * normSq0S g x 2 (metricNabla0S g h x) +
        2 * κ * normSq0S g x 2 (ahlforsPart g (metricNabla0S g h) x))
        ∂(riemannianVolumeMeasure 𝓡₂ M g) := by
  let : NeZero (Module.finrank ℝ (EuclideanSpace ℝ (Fin 2))) :=
    ⟨by rw [finrank_euclideanSpace_fin]; decide⟩
  have hgrad : Integrable (fun x => normSq0S g x 2 (metricNabla0S g h x))
      (riemannianVolumeMeasure 𝓡₂ M g) :=
    normSq_field_integrable g (metricNabla0S g h)
  have hcross := inner_field_integrable g h (roughLap0SField g h)
  have hcorrection : Integrable (fun x => 2 * κ *
      (normSq0S g x 2 (metricNabla0S g h x) +
        inner0S g x 1 (h x) (roughLap0SField g h x)))
      (riemannianVolumeMeasure 𝓡₂ M g) := (hgrad.add hcross).const_mul (2 * κ)
  have hgreen : (∫ x, normSq0S g x 2 (metricNabla0S g h x)
      ∂(riemannianVolumeMeasure 𝓡₂ M g)) =
      -(∫ x, inner0S g x 1 (h x) (roughLap0SField g h x)
        ∂(riemannianVolumeMeasure 𝓡₂ M g)) := by
    simpa only [normSq0S_eq_inner] using
      integral_inner0S_metricNabla0S_eq_neg_roughLap0SField g h h
  have hpoint (x : M) :
      normSq0S g x 1 (roughLap0SField g h x + κ • h x) +
        κ * normSq0S g x 2 (metricNabla0S g h x) +
        2 * κ * normSq0S g x 2 (ahlforsPart g (metricNabla0S g h) x) =
      oneFormDissipationDensity g h x + 2 * κ *
        (normSq0S g x 2 (metricNabla0S g h x) +
          inner0S g x 1 (h x) (roughLap0SField g h x)) := by
    rw [normSq0S_add]
    simp only [oneFormDissipationDensity, hK x, normSq0S_eq_inner,
      inner0S_smul_left, inner0S_smul_right]
    rw [inner0S_symm g x (roughLap0SField g h x) (h x)]
    ring
  symm
  calc
    _ = ∫ x, (oneFormDissipationDensity g h x + 2 * κ *
        (normSq0S g x 2 (metricNabla0S g h x) +
          inner0S g x 1 (h x) (roughLap0SField g h x)))
        ∂(riemannianVolumeMeasure 𝓡₂ M g) :=
      integral_congr_ae (Filter.Eventually.of_forall hpoint)
    _ = oneFormDissipation g h + 2 * κ *
        ((∫ x, normSq0S g x 2 (metricNabla0S g h x)
          ∂(riemannianVolumeMeasure 𝓡₂ M g)) +
        ∫ x, inner0S g x 1 (h x) (roughLap0SField g h x)
          ∂(riemannianVolumeMeasure 𝓡₂ M g)) := by
      rw [integral_add (oneFormDissipationDensity_integrable g h) hcorrection, integral_const_mul,
        integral_add hgrad hcross]
      rfl
    _ = _ := by rw [hgreen]; ring

/-- Every smooth one-form has nonnegative original dissipation when the actual
Gauss curvature is a nonnegative constant. -/
theorem oneFormDissipation_nonneg_of_constant_curvature
    (g : SmoothRiemannianMetric 𝓡₂ M) (κ : ℝ) (hκ : 0 ≤ κ)
    (hK : ∀ x : M, metricScalarAt g x / 2 = κ)
    (h : OneFormSection (I := 𝓡₂) (M := M)) :
    0 ≤ oneFormDissipation g h := by
  rw [oneFormDissipation_eq_integral_squares_of_constant_curvature g κ hK h]
  apply integral_nonneg
  intro x
  exact add_nonneg
    (add_nonneg (normSq0S_nonneg g x 1 _)
      (mul_nonneg hκ (normSq0S_nonneg g x 2 _)))
    (mul_nonneg (mul_nonneg (by norm_num) hκ) (normSq0S_nonneg g x 2 _))

end RicciFlowSharpEstimate.Geometry
