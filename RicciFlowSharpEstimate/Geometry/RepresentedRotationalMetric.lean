/-
Copyright (c) 2026 Ziyang Qin. All rights reserved.
No license is granted by this file.
Authors: Ziyang Qin
-/
import RicciFlowSharpEstimate.Geometry.ConformalKillingSafety
import RicciFlowSharpEstimate.Geometry.OneFormScalarNaturality
import RicciFlowSharpEstimate.Geometry.PullbackAlgebra

/-!
# Actual diffeomorphic pullbacks of produced rotational metrics

A represented metric retains a produced pole profile and the actual diffeomorphism
whose metric pullback it is. The same diffeomorphism transports curvature, volume,
the produced area form and the conformal Killing safety theorem. Pulling an arbitrary
original form back by the inverse preserves the full quantifier over smooth forms.
-/

noncomputable section

namespace RicciFlowSharpEstimate.Geometry

open Bundle DifferentialGeometry DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Tensor.RicciIdentity
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Geometry.Riemannian.VolumeComparison
open Set Variational
open scoped Manifold ContDiff

local instance : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 2 + 1) :=
  ⟨finrank_euclideanSpace_fin⟩
local instance : CompactSpace RotationalSphere := Metric.sphere.compactSpace _ _

/-- The actual class of diffeomorphic pullbacks of produced rotational metrics. -/
def IsRepresentedRotationalMetric
    (g : SmoothRiemannianMetric (𝓡 2) RotationalSphere) : Prop :=
  ∃ D : RotationalProfile.PoleData,
    ∃ F : RotationalSphere ≃ₘ⟮𝓡 2, 𝓡 2⟯ RotationalSphere,
      g = Diffeomorph.pullbackMetric D.metric F

namespace RotationalProfile.PoleData

/-- Every produced metric is represented using the identity diffeomorphism. -/
theorem isRepresentedRotationalMetric (D : PoleData) :
    IsRepresentedRotationalMetric D.metric := by
  exact ⟨D, Diffeomorph.refl (𝓡 2) RotationalSphere ∞,
    (Diffeomorph.pullbackMetric_refl D.metric).symm⟩

/-- The represented class contains each literal diffeomorphic pullback. -/
theorem isRepresentedRotationalMetric_pullback (D : PoleData)
    (F : RotationalSphere ≃ₘ⟮𝓡 2, 𝓡 2⟯ RotationalSphere) :
    IsRepresentedRotationalMetric (Diffeomorph.pullbackMetric D.metric F) :=
  ⟨D, F, rfl⟩

/-- The actual Gauss curvature is transported by the representing map. -/
theorem metricScalarAt_pullback (D : PoleData)
    (F : RotationalSphere ≃ₘ⟮𝓡 2, 𝓡 2⟯ RotationalSphere) (x : RotationalSphere) :
    metricScalarAt (Diffeomorph.pullbackMetric D.metric F) x / 2 =
      metricScalarAt D.metric (F x) / 2 := by
  rw [← Diffeomorph.pullbackMetricCross_eq_pullbackMetric,
    DifferentialGeometry.CheegerGromovCompactness.metricScalar_cross]

/-- Curvature boxes concern the same actual metrics on both sides of pullback. -/
theorem curvature_bounds_pullback_iff (D : PoleData)
    (F : RotationalSphere ≃ₘ⟮𝓡 2, 𝓡 2⟯ RotationalSphere) (κ Λ : ℝ) :
    (∀ x : RotationalSphere,
      κ ≤ metricScalarAt (Diffeomorph.pullbackMetric D.metric F) x / 2 ∧
        metricScalarAt (Diffeomorph.pullbackMetric D.metric F) x / 2 ≤ Λ) ↔
    (∀ x : RotationalSphere,
      κ ≤ metricScalarAt D.metric x / 2 ∧ metricScalarAt D.metric x / 2 ≤ Λ) := by
  simp only [D.metricScalarAt_pullback]
  constructor
  · intro h x
    simpa using h (F.symm x)
  · intro h x
    exact h (F x)

section Volume

private local instance : MeasurableSpace RotationalSphere := borel RotationalSphere
private local instance : BorelSpace RotationalSphere := ⟨rfl⟩

/-- The representing map preserves the Riemannian measures of the actual two metrics. -/
theorem riemannianVolume_measurePreserving_pullback (D : PoleData)
    (F : RotationalSphere ≃ₘ⟮𝓡 2, 𝓡 2⟯ RotationalSphere) :
    MeasureTheory.MeasurePreserving F
      (riemannianVolumeMeasure (I := 𝓡 2) (M := RotationalSphere)
        (Diffeomorph.pullbackMetric D.metric F))
      (riemannianVolumeMeasure (I := 𝓡 2) (M := RotationalSphere) D.metric) :=
  measurePreserving_riemannianVolume_pullback D.metric F

/-- The pushforward identity uses the same map as the metric and area pullbacks. -/
theorem riemannianVolume_map_pullback (D : PoleData)
    (F : RotationalSphere ≃ₘ⟮𝓡 2, 𝓡 2⟯ RotationalSphere) :
    MeasureTheory.Measure.map F
      (riemannianVolumeMeasure (I := 𝓡 2) (M := RotationalSphere)
        (Diffeomorph.pullbackMetric D.metric F)) =
      riemannianVolumeMeasure (I := 𝓡 2) (M := RotationalSphere) D.metric :=
  riemannianVolumeMeasure_map_pullback D.metric F

end Volume

/-- Evaluation of the transported produced area uses the derivative of the same map. -/
theorem areaForm_pullback_apply (D : PoleData)
    (F : RotationalSphere ≃ₘ⟮𝓡 2, 𝓡 2⟯ RotationalSphere) (x : RotationalSphere)
    (slots : Fin 2 → TangentSpace (𝓡 2) x) :
    diffeomorphTensorPullback F D.areaForm x slots =
      D.a (sphereHeight (F x)) *
        roundSphereAreaForm (F x) (fun i => mfderiv (𝓡 2) (𝓡 2) F x (slots i)) := by
  rw [diffeomorphTensorPullback_apply, D.areaForm_apply]

/-- The actual transported area has squared tensor norm two, in either orientation. -/
theorem areaForm_pullback_normSq (D : PoleData)
    (F : RotationalSphere ≃ₘ⟮𝓡 2, 𝓡 2⟯ RotationalSphere) (x : RotationalSphere) :
    normSq0S (Diffeomorph.pullbackMetric D.metric F) x 2
      (diffeomorphTensorPullback F D.areaForm x) = 2 := by
  rw [normSq0S_diffeomorphTensorPullback, D.areaForm_normSq]

/-- The chosen transported area is parallel for the same pulled-back metric. -/
theorem metricNabla0S_areaForm_pullback (D : PoleData)
    (F : RotationalSphere ≃ₘ⟮𝓡 2, 𝓡 2⟯ RotationalSphere) :
    metricNabla0S (Diffeomorph.pullbackMetric D.metric F)
      (diffeomorphTensorPullback F D.areaForm) = 0 := by
  rw [metricNabla0S_diffeomorphTensorPullback, D.metricNabla0S_areaForm,
    diffeomorphTensorPullback_zero]

/-- Curl uses the same chosen area form, including for orientation-reversing maps. -/
theorem oneFormCurl_areaForm_pullback (D : PoleData)
    (F : RotationalSphere ≃ₘ⟮𝓡 2, 𝓡 2⟯ RotationalSphere)
    (h : OneFormSection (I := 𝓡 2) (M := RotationalSphere)) (x : RotationalSphere) :
    oneFormCurl (Diffeomorph.pullbackMetric D.metric F)
      (diffeomorphTensorPullback F D.areaForm) (diffeomorphTensorPullback F h) x =
      oneFormCurl D.metric D.areaForm h (F x) :=
  oneFormCurl_diffeomorphTensorPullback D.metric F D.areaForm h x

/-- Safety for an arbitrary original CK form on the actual pulled-back metric. -/
theorem oneFormDissipation_nonneg_pullback_of_conformalKilling_curvature_bounds
    (D : PoleData) (F : RotationalSphere ≃ₘ⟮𝓡 2, 𝓡 2⟯ RotationalSphere)
    (κ Λ : ℝ) (hκ : 0 < κ)
    (hb : ∀ x : RotationalSphere,
      κ ≤ metricScalarAt (Diffeomorph.pullbackMetric D.metric F) x / 2 ∧
        metricScalarAt (Diffeomorph.pullbackMetric D.metric F) x / 2 ≤ Λ)
    (hcap : Λ / κ ≤ criticalCap)
    (h : OneFormSection (I := 𝓡 2) (M := RotationalSphere))
    (hCK : IsConformalKillingOneForm (Diffeomorph.pullbackMetric D.metric F) h) :
    0 ≤ oneFormDissipation (Diffeomorph.pullbackMetric D.metric F) h := by
  have hCK' : IsConformalKillingOneForm D.metric (diffeomorphTensorPullback F.symm h) := by
    simpa only [pullbackMetric_symm_apply] using hCK.diffeomorphTensorPullback F.symm
  have hsafe := D.oneFormDissipation_nonneg_of_conformalKilling_curvature_bounds
    κ Λ hκ ((D.curvature_bounds_pullback_iff F κ Λ).mp hb) hcap _ hCK'
  have hQ := oneFormDissipation_diffeomorphTensorPullback
    D.metric F (diffeomorphTensorPullback F.symm h)
  rw [diffeomorphTensorPullback_apply_symm] at hQ
  exact hsafe.trans hQ.ge

/-- Full equality for arbitrary original CK forms on the represented pullback. -/
theorem oneFormDissipation_eq_zero_iff_pullback_of_conformalKilling_curvature_bounds
    (D : PoleData) (F : RotationalSphere ≃ₘ⟮𝓡 2, 𝓡 2⟯ RotationalSphere)
    (κ Λ : ℝ) (hκ : 0 < κ)
    (hb : ∀ x : RotationalSphere,
      κ ≤ metricScalarAt (Diffeomorph.pullbackMetric D.metric F) x / 2 ∧
        metricScalarAt (Diffeomorph.pullbackMetric D.metric F) x / 2 ≤ Λ)
    (hcap : Λ / κ ≤ criticalCap)
    (h : OneFormSection (I := 𝓡 2) (M := RotationalSphere))
    (hCK : IsConformalKillingOneForm (Diffeomorph.pullbackMetric D.metric F) h) :
    oneFormDissipation (Diffeomorph.pullbackMetric D.metric F) h = 0 ↔ h = 0 := by
  have hCK' : IsConformalKillingOneForm D.metric (diffeomorphTensorPullback F.symm h) := by
    simpa only [pullbackMetric_symm_apply] using hCK.diffeomorphTensorPullback F.symm
  have hsafe := D.oneFormDissipation_eq_zero_iff_of_conformalKilling_curvature_bounds
    κ Λ hκ ((D.curvature_bounds_pullback_iff F κ Λ).mp hb) hcap _ hCK'
  have hQ := oneFormDissipation_diffeomorphTensorPullback
    D.metric F (diffeomorphTensorPullback F.symm h)
  rw [diffeomorphTensorPullback_apply_symm] at hQ
  rw [hQ, hsafe, diffeomorphTensorPullback_eq_zero_iff]

end RotationalProfile.PoleData

namespace IsRepresentedRotationalMetric

/-- The actual represented metric class is closed under further diffeomorphic pullback. -/
theorem pullback {g : SmoothRiemannianMetric (𝓡 2) RotationalSphere}
    (hg : IsRepresentedRotationalMetric g)
    (F : RotationalSphere ≃ₘ⟮𝓡 2, 𝓡 2⟯ RotationalSphere) :
    IsRepresentedRotationalMetric (Diffeomorph.pullbackMetric g F) := by
  obtain ⟨D, G, rfl⟩ := hg
  exact ⟨D, F.trans G, Diffeomorph.pullbackMetric_trans D.metric F G⟩

/-- Every represented metric in a safe actual curvature box has nonnegative CK action. -/
theorem oneFormDissipation_nonneg_of_conformalKilling_curvature_bounds
    {g : SmoothRiemannianMetric (𝓡 2) RotationalSphere}
    (hg : IsRepresentedRotationalMetric g) (κ Λ : ℝ) (hκ : 0 < κ)
    (hb : ∀ x : RotationalSphere,
      κ ≤ metricScalarAt g x / 2 ∧ metricScalarAt g x / 2 ≤ Λ)
    (hcap : Λ / κ ≤ criticalCap)
    (h : OneFormSection (I := 𝓡 2) (M := RotationalSphere))
    (hCK : IsConformalKillingOneForm g h) :
    0 ≤ oneFormDissipation g h := by
  obtain ⟨D, F, rfl⟩ := hg
  exact D.oneFormDissipation_nonneg_pullback_of_conformalKilling_curvature_bounds
    F κ Λ hκ hb hcap h hCK

/-- At the safe cap, equality for every original smooth CK form means the form is zero. -/
theorem oneFormDissipation_eq_zero_iff_of_conformalKilling_curvature_bounds
    {g : SmoothRiemannianMetric (𝓡 2) RotationalSphere}
    (hg : IsRepresentedRotationalMetric g) (κ Λ : ℝ) (hκ : 0 < κ)
    (hb : ∀ x : RotationalSphere,
      κ ≤ metricScalarAt g x / 2 ∧ metricScalarAt g x / 2 ≤ Λ)
    (hcap : Λ / κ ≤ criticalCap)
    (h : OneFormSection (I := 𝓡 2) (M := RotationalSphere))
    (hCK : IsConformalKillingOneForm g h) :
    oneFormDissipation g h = 0 ↔ h = 0 := by
  obtain ⟨D, F, rfl⟩ := hg
  exact D.oneFormDissipation_eq_zero_iff_pullback_of_conformalKilling_curvature_bounds
    F κ Λ hκ hb hcap h hCK

end IsRepresentedRotationalMetric
end RicciFlowSharpEstimate.Geometry
