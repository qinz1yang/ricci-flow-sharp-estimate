/-
Copyright (c) 2026 Ziyang Qin. All rights reserved.
No license is granted by this file.
Authors: Ziyang Qin
-/
import RicciFlowSharpEstimate.Geometry.OneFormDissipation
import RicciFlowSharpEstimate.Geometry.OneFormScalars
import RicciFlowSharpEstimate.Geometry.SurfaceTensorDecomposition

/-!
# Rigidity of the actual one-form derivative

The accepted pointwise tensor decomposition forces the canonical first derivative
to vanish when its Ahlfors part, trace, and curl vanish. Differentiating that section
equality also kills the actual second derivative and rough trace. The original
four-term dissipation then reduces exactly to its curvature energy.
-/

noncomputable section

namespace RicciFlowSharpEstimate.Geometry

open Bundle MeasureTheory
open DifferentialGeometry DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Tensor.RSTensor DifferentialGeometry.Tensor.RicciIdentity
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Integral.Connection DifferentialGeometry.Integral.Measure
open DifferentialGeometry.PDE.RicciFlow
open scoped Manifold ContDiff

section Derivatives

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
variable [IsManifold I ∞ M] [T2Space M]

/-- The canonical metric derivative sends the genuine zero tensor section to zero. -/
@[simp] theorem metricNabla0S_zero {s : ℕ} (g : SmoothRiemannianMetric I M) :
    metricNabla0S g (0 : Tensor0SField (𝕜 := ℝ) (I := I) (M := M) (n := ∞) s) = 0 := by
  simpa only [zero_smul] using
    metricNabla0S_smul g 0 (0 : Tensor0SField (𝕜 := ℝ) (I := I) (M := M) (n := ∞) s)

/-- Vanishing of the actual first derivative forces the actual second derivative to vanish. -/
theorem metricNabla0S_second_eq_zero_of_first_eq_zero {s : ℕ}
    (g : SmoothRiemannianMetric I M)
    (T : Tensor0SField (𝕜 := ℝ) (I := I) (M := M) (n := ∞) s)
    (hParallel : metricNabla0S g T = 0) :
    metricNabla0S g (metricNabla0S g T) = 0 := by
  rw [hParallel, metricNabla0S_zero]

/-- The rough trace of a tensor with vanishing actual first derivative is zero. -/
theorem roughLap0SField_eq_zero_of_metricNabla0S_eq_zero {s : ℕ}
    (g : SmoothRiemannianMetric I M)
    (T : Tensor0SField (𝕜 := ℝ) (I := I) (M := M) (n := ∞) s)
    (hParallel : metricNabla0S g T = 0) : roughLap0SField g T = 0 := by
  unfold roughLap0SField covDiv0SField
  rw [metricNabla0S_second_eq_zero_of_first_eq_zero g T hParallel,
    metricTraceFirstTwoField_zero]

/-- Vanishing Ahlfors, trace, and curl parts force the original one-form to be parallel. -/
theorem metricNabla0S_eq_zero_of_ahlfors_trace_curl_eq_zero
    (hdim : Module.finrank ℝ E = 2) (g : SmoothRiemannianMetric I M)
    (Ω : TwoTensorSection (I := I) (M := M))
    (h : OneFormSection (I := I) (M := M))
    (hAlt : ∀ x v w, Ω x (vec2 v w) = -Ω x (vec2 w v))
    (hUnit : ∀ x, normSq0S g x 2 (Ω x) = 2)
    (hA : ahlforsPart g (metricNabla0S g h) = 0)
    (hTrace : oneFormTrace g h = 0) (hCurl : oneFormCurl g Ω h = 0) :
    metricNabla0S g h = 0 := by
  refine DFunLike.ext _ _ fun x => ?_
  have htr : metricTracePair0SAt g (metricNabla0S g h x) = 0 := congrFun hTrace x
  have hcu : inner0S g x 2 (Ω x) (metricNabla0S g h x) = 0 := congrFun hCurl x
  have hsplit := twoTensor_eq_ahlforsPart_add_trace_add_curl
    hdim g (metricNabla0S g h) x (Ω x) (hAlt x) (hUnit x)
  simpa only [hA, htr, hcu, ContMDiffSection.coe_zero, Pi.zero_apply,
    zero_div, zero_smul, add_zero] using hsplit

end Derivatives

local notation "𝓡₂" => 𝓘(ℝ, EuclideanSpace ℝ (Fin 2))

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M]
variable [IsManifold 𝓡₂ ∞ M] [T2Space M]

private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

private theorem dissipationDensity_eq_curvature_energy_of_parallel
    (g : SmoothRiemannianMetric 𝓡₂ M)
    (h : OneFormSection (I := 𝓡₂) (M := M))
    (hParallel : metricNabla0S g h = 0) (x : M) :
    oneFormDissipationDensity g h x =
      (metricScalarAt g x / 2) ^ 2 * normSq0S g x 1 (h x) := by
  have hrough := roughLap0SField_eq_zero_of_metricNabla0S_eq_zero g h hParallel
  have hA : ahlforsPart g (0 : TwoTensorSection (I := 𝓡₂) (M := M)) = 0 := by
    simpa only [zero_smul] using
      ahlforsPart_smul g 0 (0 : TwoTensorSection (I := 𝓡₂) (M := M))
  have hnorm (s : ℕ) :
      normSq0S g x s (0 : Tensor0SSpace (𝕜 := ℝ) (I := 𝓡₂) s x) = 0 :=
    (normSq0S_eq_zero_iff g x s 0).mpr rfl
  simp only [oneFormDissipationDensity, hrough, hParallel, hA,
    ContMDiffSection.coe_zero, Pi.zero_apply, hnorm, mul_zero, zero_add, sub_zero, add_zero]

/-- For an actually parallel one-form, the original action is exactly its curvature energy. -/
theorem oneFormDissipation_eq_curvature_energy_of_metricNabla0S_eq_zero [CompactSpace M]
    (g : SmoothRiemannianMetric 𝓡₂ M)
    (h : OneFormSection (I := 𝓡₂) (M := M))
    (hParallel : metricNabla0S g h = 0) :
    oneFormDissipation g h =
      ∫ x, (metricScalarAt g x / 2) ^ 2 * normSq0S g x 1 (h x)
        ∂(riemannianVolumeMeasure 𝓡₂ M g) := by
  apply integral_congr_ae
  exact Filter.Eventually.of_forall
    (dissipationDensity_eq_curvature_energy_of_parallel g h hParallel)

end RicciFlowSharpEstimate.Geometry
