/-
Copyright (c) 2026 Ziyang Qin. All rights reserved.
No license is granted by this file.
Authors: Ziyang Qin
-/
import RicciFlowSharpEstimate.Geometry.CanonicalDerivatives
import DifferentialGeometry.Geometry.Operator.HessianDivergence
import DifferentialGeometry.Geometry.Curvature.DimensionTwo.RicciScalar

/-!
# Rough Laplacian of an exact one-form

The native metric covariant derivatives of `duSec` are the Hessian and its
covariant derivative. Tracing the latter gives the differential of the scalar
Laplacian plus the Ricci contraction. On a surface the curvature term is
scalar curvature divided by two times the original exact form.
-/

noncomputable section

namespace RicciFlowSharpEstimate.Geometry

open Bundle DifferentialGeometry DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.PDE.RicciFlow
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [T2Space M]

/-- The native metric derivative of an exact form is its scalar Hessian. -/
theorem metricNabla0S_duSec (g : SmoothRiemannianMetric I M)
    (f : M → ℝ) (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) :
    metricNabla0S g (duSec f hf) =
      hessianSec (metricCov g) (metricCov_smooth g) f hf := rfl

/-- The second native metric derivative of an exact form is the Hessian derivative. -/
theorem metricNabla0S_metricNabla0S_duSec (g : SmoothRiemannianMetric I M)
    (f : M → ℝ) (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) :
    metricNabla0S g (metricNabla0S g (duSec f hf)) =
      nablaHessSec (metricCov g) (metricCov_smooth g) f hf := rfl

/-- The rough Laplacian commutes with the differential up to the Ricci contraction. -/
theorem roughLap0SField_duSec_apply (g : SmoothRiemannianMetric I M)
    (f : M → ℝ) (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
    (x : M) (Y : TangentSpace I x) :
    roughLap0SField g (duSec f hf) x (fun _ : Fin 1 => Y) =
      differential1FormFun (laplacian (metricCov g) g f) x (fun _ : Fin 1 => Y) +
        metricRicciAt g x (vec2 (gradientFun g f x) Y) := by
  rw [roughLap0SField_apply, metricNabla0S_metricNabla0S_duSec,
    roughLap0STensor_apply]
  exact (hessian_divergence g ⟨f, hf⟩ x Y).trans
    (congrArg (_ + ·) (metricRicciAt_symm g x Y (gradientFun g f x)))

/-- On a surface the Ricci term in the exact-form commutator is `K * df`. -/
theorem roughLap0SField_duSec_apply_of_finrank_eq_two [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (hdim : Module.finrank ℝ E = 2)
    (f : M → ℝ) (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
    (x : M) (Y : TangentSpace I x) :
    roughLap0SField g (duSec f hf) x (fun _ : Fin 1 => Y) =
      differential1FormFun (laplacian (metricCov g) g f) x (fun _ : Fin 1 => Y) +
        (metricScalarAt g x / 2) * duSec f hf x (fun _ : Fin 1 => Y) := by
  rw [roughLap0SField_duSec_apply,
    metricRicciAt_eq_half_metricScalarAt_smul_metric_of_finrank_eq_two g hdim x,
    Tensor0SSpace.smul_apply, metricTensor0S_apply, duSec_apply,
    differential1FormFun_apply_eq_inner_gradientFun g f x Y]
  rfl

/-- The surface commutator as an equality of the actual cotangent tensors. -/
theorem roughLap0SField_duSec_of_finrank_eq_two [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (hdim : Module.finrank ℝ E = 2)
    (f : M → ℝ) (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) (x : M) :
    roughLap0SField g (duSec f hf) x =
      differential1FormFun (laplacian (metricCov g) g f) x +
        (metricScalarAt g x / 2) • duSec f hf x := by
  ext slots
  have hslots : slots = fun _ : Fin 1 => slots 0 := by
    funext i
    exact congrArg slots (Fin.eq_zero i)
  rw [hslots]
  exact roughLap0SField_duSec_apply_of_finrank_eq_two g hdim f hf x (slots 0)

end RicciFlowSharpEstimate.Geometry
