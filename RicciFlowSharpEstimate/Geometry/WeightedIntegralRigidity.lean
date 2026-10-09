/-
Copyright (c) 2026 Ziyang Qin. All rights reserved.
No license is granted by this file.
Authors: Ziyang Qin
-/
import DifferentialGeometry.Analysis.Integration.Measure.Riemannian.Properties
import DifferentialGeometry.Geometry.Metric.TensorInner.FiberMetric.Tensor0SMetricContinuity
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Function.LocallyIntegrable

/-!
# Rigidity of positive weighted tensor and scalar energies

On a compact Riemannian manifold, the native volume is finite and positive on
nonempty open sets. Consequently a continuous nonnegative energy has zero
integral exactly when it vanishes everywhere. Strict positivity of the weight
then detects the original tensor or scalar function.
-/

noncomputable section

namespace RicciFlowSharpEstimate.Geometry

open MeasureTheory DifferentialGeometry DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Integral.Measure
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
variable [IsManifold I ∞ M] [T2Space M] [CompactSpace M]

private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

/-- A strictly positive continuous weight detects the zero smooth covariant tensor
through its squared metric norm and the actual Riemannian volume. -/
theorem integral_weight_mul_normSq_eq_zero_iff {s : ℕ}
    (g : SmoothRiemannianMetric I M)
    (T : Tensor0SField (𝕜 := ℝ) (I := I) (M := M) (n := ∞) s)
    (w : M → ℝ) (hw : Continuous w) (hpos : ∀ x, 0 < w x) :
    (∫ x, w x * normSq0S g x s (T x)
      ∂(riemannianVolumeMeasure (I := I) (M := M) g)) = 0 ↔ T = 0 := by
  let μ := riemannianVolumeMeasure (I := I) (M := M) g
  let : IsFiniteMeasure μ := riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace g
  let : μ.IsOpenPosMeasure := riemannianVolumeMeasure_isOpenPosMeasure g
  have hc : Continuous (fun x => w x * normSq0S g x s (T x)) :=
    hw.mul (normSq0S_cont g T)
  have hi : Integrable (fun x => w x * normSq0S g x s (T x)) μ :=
    hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hn : 0 ≤ (fun x => w x * normSq0S g x s (T x)) :=
    fun x => mul_nonneg (hpos x).le (normSq0S_nonneg g x s (T x))
  constructor
  · intro h
    have hae := (integral_eq_zero_iff_of_nonneg hn hi).mp h
    have hz := MeasureTheory.Measure.eq_of_ae_eq hae hc continuous_const
    apply DFunLike.ext
    intro x
    apply (normSq0S_eq_zero_iff g x s (T x)).mp
    exact (mul_eq_zero.mp (congrFun hz x)).resolve_left (hpos x).ne'
  · rintro rfl
    have hzero : (fun x => w x * normSq0S g x s
        ((0 : Tensor0SField (𝕜 := ℝ) (I := I) (M := M) (n := ∞) s) x)) = 0 := by
      funext x
      change w x * normSq0S g x s 0 = 0
      rw [(normSq0S_eq_zero_iff g x s _).mpr rfl, mul_zero]
    rw [hzero]
    exact integral_zero M ℝ

/-- A strictly positive continuous weight detects the zero continuous real
function through its square and the actual Riemannian volume. -/
theorem integral_weight_mul_sq_eq_zero_iff (g : SmoothRiemannianMetric I M)
    (u : M → ℝ) (hu : Continuous u)
    (w : M → ℝ) (hw : Continuous w) (hpos : ∀ x, 0 < w x) :
    (∫ x, w x * u x ^ 2 ∂(riemannianVolumeMeasure (I := I) (M := M) g)) = 0 ↔
      u = 0 := by
  let μ := riemannianVolumeMeasure (I := I) (M := M) g
  let : IsFiniteMeasure μ := riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace g
  let : μ.IsOpenPosMeasure := riemannianVolumeMeasure_isOpenPosMeasure g
  have hc : Continuous (fun x => w x * u x ^ 2) := hw.mul (hu.pow 2)
  have hi : Integrable (fun x => w x * u x ^ 2) μ :=
    hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hn : 0 ≤ (fun x => w x * u x ^ 2) :=
    fun x => mul_nonneg (hpos x).le (sq_nonneg (u x))
  constructor
  · intro h
    have hae := (integral_eq_zero_iff_of_nonneg hn hi).mp h
    have hz := MeasureTheory.Measure.eq_of_ae_eq hae hc continuous_const
    funext x
    exact (sq_eq_zero_iff).mp ((mul_eq_zero.mp (congrFun hz x)).resolve_left (hpos x).ne')
  · rintro rfl
    simp

end RicciFlowSharpEstimate.Geometry
