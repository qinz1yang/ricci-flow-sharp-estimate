/-
Copyright (c) 2026 Ziyang Qin. All rights reserved.
No license is granted by this file.
Authors: Ziyang Qin
-/
import RicciFlowSharpEstimate.Geometry.CanonicalTensorIntegration
import RicciFlowSharpEstimate.Geometry.SurfaceCovariantCommutator
import RicciFlowSharpEstimate.Geometry.SurfaceTensorDecomposition

/-!
# The integrated gradient-slot pairing on a surface

The mixed gradient pairing follows from canonical integration by parts and the
actual covariant commutator. Continuity and compactness supply integrability
before the commutator's two summands are integrated separately.
-/

noncomputable section

namespace RicciFlowSharpEstimate.Geometry

open Bundle MeasureTheory DifferentialGeometry DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Geometry.Operator DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow DifferentialGeometry.Tensor.RSTensor
open DifferentialGeometry.Integral.Connection DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem DifferentialGeometry.Tensor.RicciIdentity
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
variable [IsManifold I ∞ M] [T2Space M] [CompactSpace M]
variable [I.Boundaryless] [BoundarylessManifold I M]

private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

omit [T2Space M] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] in
private theorem continuous_inner0S_field {s : ℕ}
    (g : SmoothRiemannianMetric I M)
    (T U : Tensor0SField (𝕜 := ℝ) (I := I) (M := M) (n := ∞) s) :
    Continuous (fun x => inner0S g x s (T x) (U x)) := by
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
  exact ((((normSq0S_smooth g (T + U)).sub (normSq0S_smooth g T)).sub
    (normSq0S_smooth g U)).div_const 2).continuous

omit [I.Boundaryless] [BoundarylessManifold I M] in
private theorem integrable_inner0S_field {s : ℕ}
    (g : SmoothRiemannianMetric I M)
    (T U : Tensor0SField (𝕜 := ℝ) (I := I) (M := M) (n := ∞) s) :
    Integrable (fun x => inner0S g x s (T x) (U x))
      (riemannianVolumeMeasure (I := I) (M := M) g) :=
  Continuous.integrable_of_hasCompactSupport_riemannianVolumeMeasure
    (I := I) g (continuous_inner0S_field g T U) (HasCompactSupport.of_compactSpace _)

/-- On a closed surface, the mixed gradient-slot pairing equals the divergence
energy minus scalar curvature paired with the squared Ahlfors norm. -/
theorem integral_inner0S_gradSlotSwap (hdim : Module.finrank ℝ E = 2)
    (g : SmoothRiemannianMetric I M) (S : TwoTensorSection (I := I) (M := M)) :
    (∫ x, inner0S g x 3
        ((metricNabla0S g S x).domDomCongr (Equiv.swap (0 : Fin 3) 1))
        (metricNabla0S g S x) ∂(riemannianVolumeMeasure (I := I) (M := M) g)) =
      (∫ x, normSq0S g x 1 (covDiv0SField g S x)
        ∂(riemannianVolumeMeasure (I := I) (M := M) g)) -
      ∫ x, metricScalarAt g x * normSq0S g x 2 (ahlforsPart g S x)
        ∂(riemannianVolumeMeasure (I := I) (M := M) g) := by
  let : NeZero (Module.finrank ℝ E) := ⟨by rw [hdim]; decide⟩
  let D := covDiv0SField g S
  let W := Tensor0SField.domDomCongr ∞ (Equiv.swap (0 : Fin 3) 1) (metricNabla0S g S)
  have hgrad_int := integrable_inner0S_field g S (metricNabla0S g D)
  have hcurv_cont : Continuous
      (fun x => metricScalarAt g x * normSq0S g x 2 (ahlforsPart g S x)) :=
    (metricScalar_smooth g).continuous.mul (normSq0S_smooth g (ahlforsPart g S)).continuous
  have hcurv_int : Integrable
      (fun x => metricScalarAt g x * normSq0S g x 2 (ahlforsPart g S x))
      (riemannianVolumeMeasure (I := I) (M := M) g) :=
    Continuous.integrable_of_hasCompactSupport_riemannianVolumeMeasure
      (I := I) g hcurv_cont (HasCompactSupport.of_compactSpace _)
  have hcomm : covDiv0SField g W = metricNabla0S g D +
      tensor0SFieldSmulByFun ∞ (metricScalarAt g) (metricScalar_smooth g)
        (ahlforsPart g S) :=
    covDiv0SField_gradSlotSwap_commutator_of_finrank_eq_two hdim g S
  have hpoint (x : M) : inner0S g x 2 (S x) (covDiv0SField g W x) =
      inner0S g x 2 (S x) (metricNabla0S g D x) +
        metricScalarAt g x * normSq0S g x 2 (ahlforsPart g S x) := by
    have hx := congrArg (fun T => T x) hcomm
    change covDiv0SField g W x = metricNabla0S g D x +
      metricScalarAt g x • ahlforsPart g S x at hx
    rw [hx, inner0S_add_right, inner0S_smul_right,
      inner0S_symm g x (S x) (ahlforsPart g S x), inner0S_ahlforsPart_self hdim]
  have hdiv : (∫ x, inner0S g x 2 (S x) (metricNabla0S g D x)
      ∂(riemannianVolumeMeasure (I := I) (M := M) g)) =
      -(∫ x, normSq0S g x 1 (D x)
        ∂(riemannianVolumeMeasure (I := I) (M := M) g)) := by
    calc
      _ = ∫ x, inner0S g x 2 (metricNabla0S g D x) (S x)
          ∂(riemannianVolumeMeasure (I := I) (M := M) g) :=
        integral_congr_ae (Filter.Eventually.of_forall fun x => inner0S_symm g x _ _)
      _ = _ := by
        simpa only [D, normSq0S_eq_inner] using
          integral_inner0S_metricNabla0S_eq_neg_covDiv0SField g D S
  calc
    _ = ∫ x, inner0S g x 3 (metricNabla0S g S x) (W x)
        ∂(riemannianVolumeMeasure (I := I) (M := M) g) :=
      integral_congr_ae (Filter.Eventually.of_forall fun x => inner0S_symm g x _ _)
    _ = -(∫ x, inner0S g x 2 (S x) (covDiv0SField g W x)
        ∂(riemannianVolumeMeasure (I := I) (M := M) g)) :=
      integral_inner0S_metricNabla0S_eq_neg_covDiv0SField g S W
    _ = -((∫ x, inner0S g x 2 (S x) (metricNabla0S g D x)
          ∂(riemannianVolumeMeasure (I := I) (M := M) g)) +
        ∫ x, metricScalarAt g x * normSq0S g x 2 (ahlforsPart g S x)
          ∂(riemannianVolumeMeasure (I := I) (M := M) g)) := by
      rw [integral_congr_ae (Filter.Eventually.of_forall hpoint),
        integral_add hgrad_int hcurv_int]
    _ = _ := by
      rw [hdiv]
      ring

end RicciFlowSharpEstimate.Geometry
