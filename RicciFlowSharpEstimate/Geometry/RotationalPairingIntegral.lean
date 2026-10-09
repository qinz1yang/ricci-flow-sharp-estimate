/-
Copyright (c) 2026 Ziyang Qin. All rights reserved.
No license is granted by this file.
Authors: Ziyang Qin
-/
import RicciFlowSharpEstimate.Geometry.RotationalTensorAction
import DifferentialGeometry.Geometry.Metric.TensorInner.FiberMetric.Tensor0SMetricContinuity
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Parameter integration of the full rotated dissipation pairing

The original polarized density, including its rough-Laplacian and Ahlfors terms,
is jointly continuous under the genuine rotation action. Compactness gives the
product integrability required to interchange the angle and sphere integrals.

The bundle-inner-product and Fubini arguments adapt Ziyang Qin's historical
`RotationalHaarDissipationProjection.lean` to the actual accepted rotation and tensor producers.
-/

noncomputable section

namespace RicciFlowSharpEstimate.Geometry

open Bundle MeasureTheory Set
open DifferentialGeometry DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.Integral.Connection DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Tensor.RicciIdentity
open scoped Manifold ContDiff Interval

local instance : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 2 + 1) :=
  ⟨finrank_euclideanSpace_fin⟩

private local instance : MeasurableSpace RotationalSphere := borel RotationalSphere
private local instance : BorelSpace RotationalSphere := ⟨rfl⟩

private theorem continuous_inner0S_rotation
    (g : SmoothRiemannianMetric (𝓡 2) RotationalSphere) {s : ℕ}
    (A B : Tensor0SField (𝕜 := ℝ) (I := 𝓡 2) (M := RotationalSphere) (n := ∞) s) :
    Continuous (fun p : ℝ × RotationalSphere =>
      inner0S g p.2 s (diffeomorphTensorPullback (angleRotation p.1) A p.2) (B p.2)) := by
  have hA := (contMDiff_diffeomorphTensorPullback_angleRotation A).continuous
  have hB : Continuous (fun p : ℝ × RotationalSphere =>
      TotalSpace.mk' (Tensor0SModel s ℝ (EuclideanSpace ℝ (Fin 2)))
        (E := fun x : RotationalSphere => Tensor0SSpace s (𝓡 2) x) p.2 (B p.2)) :=
    B.contMDiff.continuous.comp continuous_snd
  have hsum : Continuous (fun p : ℝ × RotationalSphere =>
      TotalSpace.mk' (Tensor0SModel s ℝ (EuclideanSpace ℝ (Fin 2))) p.2
        (diffeomorphTensorPullback (angleRotation p.1) A p.2 + B p.2)) := by
    rw [continuous_iff_continuousAt]
    intro p₀
    have ha := hA.continuousAt (x := p₀)
    have hb := hB.continuousAt (x := p₀)
    rw [FiberBundle.continuousAt_totalSpace] at ha hb ⊢
    refine ⟨continuous_snd.continuousAt, ?_⟩
    let e := trivializationAt (Tensor0SModel s ℝ (EuclideanSpace ℝ (Fin 2)))
      (fun x : RotationalSphere => Tensor0SSpace s (𝓡 2) x) p₀.2
    apply (ha.2.add hb.2).congr_of_eventuallyEq
    have hbase : ∀ᶠ p : ℝ × RotationalSphere in nhds p₀, p.2 ∈ e.baseSet :=
      continuous_snd.continuousAt.preimage_mem_nhds
        (e.open_baseSet.mem_nhds (FiberBundle.mem_baseSet_trivializationAt' p₀.2))
    filter_upwards [hbase] with p hp
    exact (e.linear ℝ hp).1 _ _
  have heq : (fun p : ℝ × RotationalSphere =>
      inner0S g p.2 s (diffeomorphTensorPullback (angleRotation p.1) A p.2) (B p.2)) =
      fun p => (normSq0S g p.2 s
        (diffeomorphTensorPullback (angleRotation p.1) A p.2 + B p.2) -
          normSq0S g p.2 s (diffeomorphTensorPullback (angleRotation p.1) A p.2) -
          normSq0S g p.2 s (B p.2)) / 2 := by
    funext p
    rw [normSq0S_add]
    ring
  rw [heq]
  exact ((((normSq0S_total_cont g).comp hsum).sub
    ((normSq0S_total_cont g).comp hA)).sub
      ((normSq0S_total_cont g).comp hB)).div_const 2

namespace RotationalProfile.PoleData

/-- The full polarized density is jointly continuous in the actual angle and sphere point. -/
theorem continuous_oneFormDissipationPairingDensity_angleRotation (D : PoleData)
    (h k : OneFormSection (I := 𝓡 2) (M := RotationalSphere)) :
    Continuous (fun p : ℝ × RotationalSphere => oneFormDissipationPairingDensity D.metric
      (diffeomorphTensorPullback (angleRotation p.1) h) k p.2) := by
  have hR (θ : ℝ) : roughLap0SField D.metric
      (diffeomorphTensorPullback (angleRotation θ) h) =
        diffeomorphTensorPullback (angleRotation θ) (roughLap0SField D.metric h) := by
    simpa only [D.pullbackMetric_angleRotation] using
      roughLap0SField_diffeomorphTensorPullback D.metric (angleRotation θ) h
  have hA (θ : ℝ) : ahlforsPart D.metric
      (diffeomorphTensorPullback (angleRotation θ) (metricNabla0S D.metric h)) =
        diffeomorphTensorPullback (angleRotation θ)
          (ahlforsPart D.metric (metricNabla0S D.metric h)) := by
    simpa only [D.pullbackMetric_angleRotation] using
      ahlforsPart_diffeomorphTensorPullback D.metric (angleRotation θ) (metricNabla0S D.metric h)
  have hK : Continuous (fun p : ℝ × RotationalSphere => metricScalarAt D.metric p.2 / 2) :=
    ((metricScalar_smooth D.metric).continuous.comp continuous_snd).div_const 2
  simp only [oneFormDissipationPairingDensity, hR, D.metricNabla0S_angleRotation, hA]
  exact (((continuous_inner0S_rotation D.metric (roughLap0SField D.metric h)
    (roughLap0SField D.metric k)).add
      ((hK.pow 2).mul (continuous_inner0S_rotation D.metric h k))).sub
        (hK.mul (continuous_inner0S_rotation D.metric (metricNabla0S D.metric h)
          (metricNabla0S D.metric k)))).add
            ((continuous_const.mul hK).mul (continuous_inner0S_rotation D.metric
              (ahlforsPart D.metric (metricNabla0S D.metric h))
              (ahlforsPart D.metric (metricNabla0S D.metric k))))

/-- The actual full density is integrable on every finite angle interval times the sphere. -/
theorem integrable_oneFormDissipationPairingDensity_angleRotation (D : PoleData)
    (h k : OneFormSection (I := 𝓡 2) (M := RotationalSphere)) (a b : ℝ) :
    Integrable (fun p : ℝ × RotationalSphere => oneFormDissipationPairingDensity D.metric
      (diffeomorphTensorPullback (angleRotation p.1) h) k p.2)
      ((volume.restrict (uIoc a b)).prod
        (riemannianVolumeMeasure (𝓡 2) RotationalSphere D.metric)) := by
  let μ := riemannianVolumeMeasure (𝓡 2) RotationalSphere D.metric
  let := riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace D.metric
  have hIntOn : IntegrableOn
      (fun p : ℝ × RotationalSphere => oneFormDissipationPairingDensity D.metric
        (diffeomorphTensorPullback (angleRotation p.1) h) k p.2)
      (uIcc a b ×ˢ (univ : Set RotationalSphere)) (volume.prod μ) :=
    (D.continuous_oneFormDissipationPairingDensity_angleRotation h k).continuousOn
      |>.integrableOn_compact (isCompact_uIcc.prod isCompact_univ)
  have hProdEq : (volume.restrict (uIoc a b)).prod μ =
      (volume.prod μ).restrict (uIoc a b ×ˢ (univ : Set RotationalSphere)) := by
    conv_lhs => rw [← Measure.restrict_univ (μ := μ)]
    rw [Measure.prod_restrict]
  change Integrable _ ((volume.restrict (uIoc a b)).prod μ)
  rw [hProdEq]
  exact hIntOn.mono_set (Set.prod_mono uIoc_subset_uIcc (Subset.rfl))

/-- The actual full dissipation pairing along a rotation orbit is interval integrable. -/
theorem intervalIntegrable_oneFormDissipationPairing_angleRotation (D : PoleData)
    (h k : OneFormSection (I := 𝓡 2) (M := RotationalSphere)) (a b : ℝ) :
    IntervalIntegrable (fun θ => oneFormDissipationPairing D.metric
      (diffeomorphTensorPullback (angleRotation θ) h) k) volume a b := by
  let := riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace D.metric
  rw [intervalIntegrable_iff]
  exact (D.integrable_oneFormDissipationPairingDensity_angleRotation h k a b).integral_prod_left

/-- Fubini interchanges the actual angle integral and the sphere integral of all four terms. -/
theorem integral_intervalIntegral_oneFormDissipationPairingDensity_angleRotation (D : PoleData)
    (h k : OneFormSection (I := 𝓡 2) (M := RotationalSphere)) (a b : ℝ) :
    (∫ x, (∫ θ in a..b, oneFormDissipationPairingDensity D.metric
      (diffeomorphTensorPullback (angleRotation θ) h) k x)
      ∂(riemannianVolumeMeasure (𝓡 2) RotationalSphere D.metric)) =
      ∫ θ in a..b, oneFormDissipationPairing D.metric
        (diffeomorphTensorPullback (angleRotation θ) h) k := by
  let := riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace D.metric
  exact (MeasureTheory.intervalIntegral_integral_swap
    (D.integrable_oneFormDissipationPairingDensity_angleRotation h k a b)).symm

end RotationalProfile.PoleData

end RicciFlowSharpEstimate.Geometry
