/-
Copyright (c) 2026 Ziyang Qin. All rights reserved.
No license is granted by this file.
Authors: Ziyang Qin
-/
import DifferentialGeometry.Geometry.Operator.CovariantTensor
import DifferentialGeometry.Geometry.Connection.RicciIdentity.OneForm.Realization

/-!
# Canonical metric covariant derivatives

This module uses the released DifferentialGeometry total covariant derivative and its
smooth-connection package. The uniqueness proof uses Mathlib's smooth section extension.
-/

noncomputable section

open Bundle DifferentialGeometry DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Tensor.RSTensor
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
variable [IsManifold I ∞ M] [T2Space M]

namespace DifferentialGeometry.Tensor0SBundle

/-- A total covariant derivative is determined by its values on smooth vector fields. -/
theorem TotalNabla0SRealizes.unique {s : ℕ}
    {cov : CovariantDerivative I E (TangentSpace I : M → Type _)}
    {A : Tensor0SField (𝕜 := Real) (I := I) (M := M) (∞ : WithTop ℕ∞) s}
    {B C : Tensor0SField (𝕜 := Real) (I := I) (M := M) (∞ : WithTop ℕ∞) (s + 1)}
    (hB : TotalNabla0SRealizes s cov A B)
    (hC : TotalNabla0SRealizes s cov A C) : B = C := by
  classical
  refine DFunLike.ext _ _ fun x => ?_
  let b : Module.Basis (Fin (Module.finrank Real (TangentSpace I x))) Real
      (TangentSpace I x) := Module.finBasis Real (TangentSpace I x)
  apply ext0S_basis (I := I) b
  intro idx
  obtain ⟨X, hX⟩ := ContMDiffSection.exists_eq_at
    (I := I) (F := E) (V := TangentSpace I) (n := (⊤ : ℕ∞)) x (b (idx 0))
  have hslots : Fin.cons (X x) (fun a : Fin s => b (idx a.succ)) =
      fun a : Fin (s + 1) => b (idx a) := by
    funext a
    cases a using Fin.cases with
    | zero => exact hX
    | succ a => rfl
  have h := (hB X x (fun a : Fin s => b (idx a.succ))).trans
    (hC X x (fun a : Fin s => b (idx a.succ))).symm
  simpa only [hslots, component0S_apply] using h

/-- Both fields in the existing two-derivative package are uniquely determined. -/
theorem CanonicalSpatialDerivs0S.unique {s : ℕ}
    {cov : CovariantDerivative I E (TangentSpace I : M → Type _)}
    {A : Tensor0SField (𝕜 := Real) (I := I) (M := M) (∞ : WithTop ℕ∞) s}
    (D₁ D₂ : CanonicalSpatialDerivs0S cov A) : D₁ = D₂ := by
  rcases D₁ with ⟨B₁, C₁, hB₁, hC₁⟩
  rcases D₂ with ⟨B₂, C₂, hB₂, hC₂⟩
  have hB : B₁ = B₂ := hB₁.unique hB₂
  subst B₂
  have hC : C₁ = C₂ := hC₁.unique hC₂
  subst C₂
  rfl

end DifferentialGeometry.Tensor0SBundle

namespace RicciFlowSharpEstimate.Geometry

variable {s : ℕ}

theorem roughLap0SField_add (g : SmoothRiemannianMetric I M) {s : ℕ}
    (A B : Tensor0SField (𝕜 := ℝ) (I := I) (M := M) (n := ∞) s) :
    roughLap0SField g (A + B) = roughLap0SField g A + roughLap0SField g B := by
  simp only [roughLap0SField, covDiv0SField, metricNabla0S_add, metricTraceFirstTwoField_add]

theorem roughLap0SField_smul (g : SmoothRiemannianMetric I M) {s : ℕ} (c : ℝ)
    (A : Tensor0SField (𝕜 := ℝ) (I := I) (M := M) (n := ∞) s) :
    roughLap0SField g (c • A) = c • roughLap0SField g A := by
  simp only [roughLap0SField, covDiv0SField, metricNabla0S_smul, metricTraceFirstTwoField_smul]

/-- The native first and second derivatives produced by the metric's smooth connection. -/
def canonicalDerivatives (g : SmoothRiemannianMetric I M)
    (A : Tensor0SField (𝕜 := Real) (I := I) (M := M) (∞ : WithTop ℕ∞) s) :
    CanonicalSpatialDerivs0S (metricCov (I := I) g) A :=
  CanonicalSpatialDerivs0S.ofSmoothConnection
    (metricCov (I := I) g) (metricCov_smooth (I := I) g) A

@[simp]
theorem canonicalDerivatives_nablaA (g : SmoothRiemannianMetric I M)
    (A : Tensor0SField (𝕜 := Real) (I := I) (M := M) (∞ : WithTop ℕ∞) s) :
    (canonicalDerivatives g A).nablaA = metricNabla0S g A := rfl

@[simp]
theorem canonicalDerivatives_nabla2A (g : SmoothRiemannianMetric I M)
    (A : Tensor0SField (𝕜 := Real) (I := I) (M := M) (∞ : WithTop ℕ∞) s) :
    (canonicalDerivatives g A).nabla2A = metricNabla0S g (metricNabla0S g A) := rfl

theorem canonicalDerivatives_first (g : SmoothRiemannianMetric I M)
    (A : Tensor0SField (𝕜 := Real) (I := I) (M := M) (∞ : WithTop ℕ∞) s) :
    TotalNabla0SRealizes s (metricCov (I := I) g) A (metricNabla0S g A) :=
  (canonicalDerivatives g A).first

theorem canonicalDerivatives_second (g : SmoothRiemannianMetric I M)
    (A : Tensor0SField (𝕜 := Real) (I := I) (M := M) (∞ : WithTop ℕ∞) s) :
    TotalNabla0SRealizes (s + 1) (metricCov (I := I) g)
      (metricNabla0S g A) (metricNabla0S g (metricNabla0S g A)) :=
  (canonicalDerivatives g A).second

/-- Any pair realizing the first two derivatives equals the native metric derivative package. -/
theorem canonicalDerivatives_unique (g : SmoothRiemannianMetric I M)
    (A : Tensor0SField (𝕜 := Real) (I := I) (M := M) (∞ : WithTop ℕ∞) s)
    (D : CanonicalSpatialDerivs0S (metricCov (I := I) g) A) :
    D = canonicalDerivatives g A :=
  D.unique (canonicalDerivatives g A)

theorem canonicalDerivatives_nabla2A_add (g : SmoothRiemannianMetric I M)
    (A B : Tensor0SField (𝕜 := Real) (I := I) (M := M) (∞ : WithTop ℕ∞) s) :
    (canonicalDerivatives g (A + B)).nabla2A =
      (canonicalDerivatives g A).nabla2A + (canonicalDerivatives g B).nabla2A := by
  simp only [canonicalDerivatives_nabla2A, metricNabla0S_add]

theorem canonicalDerivatives_nabla2A_smul (g : SmoothRiemannianMetric I M)
    (c : Real)
    (A : Tensor0SField (𝕜 := Real) (I := I) (M := M) (∞ : WithTop ℕ∞) s) :
    (canonicalDerivatives g (c • A)).nabla2A =
      c • (canonicalDerivatives g A).nabla2A := by
  simp only [canonicalDerivatives_nabla2A, metricNabla0S_smul]

/-- The native metric derivatives satisfy the one-form second-derivative realization law. -/
theorem canonicalDerivatives_nabla2OneFormRealizesAt
    (g : SmoothRiemannianMetric I M)
    (A : Tensor0SField (𝕜 := Real) (I := I) (M := M) (∞ : WithTop ℕ∞) 1)
    (x : M) :
    DifferentialGeometry.Tensor.RicciIdentity.Nabla2OneFormRealizesAt
      (metricCov (I := I) g) A (metricNabla0S g A) x
      (metricNabla0S g (metricNabla0S g A) x) :=
  DifferentialGeometry.Tensor.RicciIdentity.nabla2OneFormRealizesAt_of_totalNabla
    (metricCov (I := I) g) A (metricNabla0S g A)
    (metricNabla0S g (metricNabla0S g A))
    (canonicalDerivatives_first g A) (canonicalDerivatives_second g A) x

end RicciFlowSharpEstimate.Geometry
