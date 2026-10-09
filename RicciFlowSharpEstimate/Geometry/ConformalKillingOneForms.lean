/-
Copyright (c) 2026 Ziyang Qin. All rights reserved.
No license is granted by this file.
Authors: Ziyang Qin
-/
import RicciFlowSharpEstimate.Geometry.OneFormDissipationNaturality

/-!
# Conformal Killing one-forms

The conformal Killing equation is the vanishing of the trace-free symmetric
part of the actual metric covariant derivative of a smooth one-form.
It is linear and natural under simultaneous pullback of the metric and form.
-/

namespace RicciFlowSharpEstimate.Geometry

open DifferentialGeometry DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Tensor.RicciIdentity DifferentialGeometry.PDE.RicciFlow
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [T2Space M]

/-- A smooth one-form is conformal Killing when its actual metric derivative
has vanishing trace-free symmetric part. -/
def IsConformalKillingOneForm (g : SmoothRiemannianMetric I M)
    (h : OneFormSection (I := I) (M := M)) : Prop :=
  ahlforsPart g (metricNabla0S g h) = 0

/-- The section equation is equivalent to the equation in every tensor fiber. -/
theorem isConformalKillingOneForm_iff (g : SmoothRiemannianMetric I M)
    (h : OneFormSection (I := I) (M := M)) :
    IsConformalKillingOneForm g h ↔ ∀ x, ahlforsPart g (metricNabla0S g h) x = 0 := by
  constructor
  · intro hh x
    exact congrArg (fun A => A x) hh
  · intro hh
    exact DFunLike.ext _ _ hh

/-- Vanishing of the actual Ahlfors squared norm detects the conformal Killing equation. -/
theorem isConformalKillingOneForm_iff_normSq_eq_zero (g : SmoothRiemannianMetric I M)
    (h : OneFormSection (I := I) (M := M)) :
    IsConformalKillingOneForm g h ↔
      ∀ x, normSq0S g x 2 (ahlforsPart g (metricNabla0S g h) x) = 0 := by
  rw [isConformalKillingOneForm_iff]
  exact forall_congr' fun x => (normSq0S_eq_zero_iff g x 2 _).symm

namespace IsConformalKillingOneForm

theorem add {g : SmoothRiemannianMetric I M}
    {h k : OneFormSection (I := I) (M := M)}
    (hh : IsConformalKillingOneForm g h) (hk : IsConformalKillingOneForm g k) :
    IsConformalKillingOneForm g (h + k) := by
  unfold IsConformalKillingOneForm at *
  rw [metricNabla0S_add, ahlforsPart_add, hh, hk, add_zero]

theorem smul {g : SmoothRiemannianMetric I M}
    {h : OneFormSection (I := I) (M := M)}
    (hh : IsConformalKillingOneForm g h) (c : ℝ) :
    IsConformalKillingOneForm g (c • h) := by
  unfold IsConformalKillingOneForm at *
  rw [metricNabla0S_smul, ahlforsPart_smul, hh, smul_zero]

theorem neg {g : SmoothRiemannianMetric I M}
    {h : OneFormSection (I := I) (M := M)} (hh : IsConformalKillingOneForm g h) :
    IsConformalKillingOneForm g (-h) := by
  simpa only [neg_one_smul] using hh.smul (-1)

theorem sub {g : SmoothRiemannianMetric I M}
    {h k : OneFormSection (I := I) (M := M)}
    (hh : IsConformalKillingOneForm g h) (hk : IsConformalKillingOneForm g k) :
    IsConformalKillingOneForm g (h - k) := by
  simpa only [sub_eq_add_neg] using hh.add hk.neg

/-- Simultaneous pullback uses the same genuine diffeomorphism for metric and form. -/
theorem diffeomorphTensorPullback {g : SmoothRiemannianMetric I M}
    {h : OneFormSection (I := I) (M := M)}
    (hh : IsConformalKillingOneForm g h) (f : M ≃ₘ⟮I, I⟯ M) :
    IsConformalKillingOneForm (Diffeomorph.pullbackMetric g f)
      (Geometry.diffeomorphTensorPullback f h) := by
  unfold IsConformalKillingOneForm at *
  rw [metricNabla0S_diffeomorphTensorPullback, ahlforsPart_diffeomorphTensorPullback, hh]
  ext x slots
  rw [Geometry.diffeomorphTensorPullback_apply]
  rfl

/-- Every smooth isometry preserves the conformal Killing equation of the original metric. -/
theorem diffeomorphTensorPullback_of_isometry {g : SmoothRiemannianMetric I M}
    {h : OneFormSection (I := I) (M := M)}
    (hh : IsConformalKillingOneForm g h) (f : M ≃ₘ⟮I, I⟯ M)
    (hf : Diffeomorph.pullbackMetric g f = g) :
    IsConformalKillingOneForm g (Geometry.diffeomorphTensorPullback f h) := by
  simpa only [hf] using hh.diffeomorphTensorPullback f

end IsConformalKillingOneForm

end RicciFlowSharpEstimate.Geometry
