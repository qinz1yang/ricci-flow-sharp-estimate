/-
Copyright (c) 2026 Ziyang Qin. All rights reserved.
No license is granted by this file.
Authors: Ziyang Qin
-/
import RicciFlowSharpEstimate.Geometry.CanonicalDerivatives
import RicciFlowSharpEstimate.Geometry.TraceFreeSymmetric
import DifferentialGeometry.Analysis.Integration.Measure.Riemannian.Properties
import DifferentialGeometry.Geometry.Metric.TensorInner.FiberMetric.Tensor0SMetricIneq

/-!
# Complete canonical one-form Hodge dissipation

The four-term action uses the actual metric derivative, its rough trace and its
trace-free symmetric part. All integrability is proved for smooth forms on a
compact surface. The polarization retains all four geometric terms.
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

local notation "𝓡₂" => 𝓘(ℝ, EuclideanSpace ℝ (Fin 2))

section Operators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]

omit [T2Space M] in
private theorem innerField_smooth (g : SmoothRiemannianMetric I M) {s : ℕ}
    (A B : Tensor0SField (𝕜 := ℝ) (I := I) (M := M) (n := ∞) s) :
    ContMDiff I 𝓘(ℝ, ℝ) ∞ (fun x => inner0S g x s (A x) (B x)) := by
  have heq : (fun x => inner0S g x s (A x) (B x)) = fun x =>
      (normSq0S g x s ((A + B) x) - normSq0S g x s (A x) - normSq0S g x s (B x)) / 2 := by
    funext x
    change inner0S g x s (A x) (B x) =
      (normSq0S g x s (A x + B x) - normSq0S g x s (A x) - normSq0S g x s (B x)) / 2
    rw [normSq0S_add]
    ring
  rw [heq]
  exact (((normSq0S_smooth g (A + B)).sub (normSq0S_smooth g A)).sub
    (normSq0S_smooth g B)).div_const 2

end Operators

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M]
variable [IsManifold 𝓡₂ ∞ M] [T2Space M]

private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

/-- The full one-form dissipation density with the genuine scalar/2 Gauss curvature. -/
def oneFormDissipationDensity (g : SmoothRiemannianMetric 𝓡₂ M)
    (h : OneFormSection (I := 𝓡₂) (M := M)) (x : M) : ℝ :=
  let K := metricScalarAt g x / 2
  normSq0S g x 1 (roughLap0SField g h x) + K ^ 2 * normSq0S g x 1 (h x) -
    K * normSq0S g x 2 (metricNabla0S g h x) +
    2 * K * normSq0S g x 2 (ahlforsPart g (metricNabla0S g h) x)

/-- The polarization density, retaining every term of the actual action. -/
def oneFormDissipationPairingDensity (g : SmoothRiemannianMetric 𝓡₂ M)
    (h k : OneFormSection (I := 𝓡₂) (M := M)) (x : M) : ℝ :=
  let K := metricScalarAt g x / 2
  inner0S g x 1 (roughLap0SField g h x) (roughLap0SField g k x) +
    K ^ 2 * inner0S g x 1 (h x) (k x) -
    K * inner0S g x 2 (metricNabla0S g h x) (metricNabla0S g k x) +
    2 * K * inner0S g x 2 (ahlforsPart g (metricNabla0S g h) x)
      (ahlforsPart g (metricNabla0S g k) x)

theorem oneFormDissipationDensity_smooth (g : SmoothRiemannianMetric 𝓡₂ M)
    (h : OneFormSection (I := 𝓡₂) (M := M)) :
    ContMDiff 𝓡₂ 𝓘(ℝ, ℝ) ∞ (oneFormDissipationDensity g h) := by
  have hK := (metricScalar_smooth g).div_const 2
  exact (((normSq0S_smooth g (roughLap0SField g h)).add
    ((hK.pow 2).mul (normSq0S_smooth g h))).sub
      (hK.mul (normSq0S_smooth g (metricNabla0S g h)))).add
        ((contMDiff_const.mul hK).mul (normSq0S_smooth g (ahlforsPart g (metricNabla0S g h))))

theorem oneFormDissipationPairingDensity_smooth (g : SmoothRiemannianMetric 𝓡₂ M)
    (h k : OneFormSection (I := 𝓡₂) (M := M)) :
    ContMDiff 𝓡₂ 𝓘(ℝ, ℝ) ∞ (oneFormDissipationPairingDensity g h k) := by
  have hK := (metricScalar_smooth g).div_const 2
  exact (((innerField_smooth g (roughLap0SField g h) (roughLap0SField g k)).add
    ((hK.pow 2).mul (innerField_smooth g h k))).sub
      (hK.mul (innerField_smooth g (metricNabla0S g h) (metricNabla0S g k)))).add
        ((contMDiff_const.mul hK).mul
          (innerField_smooth g (ahlforsPart g (metricNabla0S g h))
            (ahlforsPart g (metricNabla0S g k))))

private theorem pairingDensity_symm (g : SmoothRiemannianMetric 𝓡₂ M)
    (h k : OneFormSection (I := 𝓡₂) (M := M)) (x : M) :
    oneFormDissipationPairingDensity g h k x = oneFormDissipationPairingDensity g k h x := by
  simp only [oneFormDissipationPairingDensity, inner0S_symm]

private theorem pairingDensity_add_left (g : SmoothRiemannianMetric 𝓡₂ M)
    (h k l : OneFormSection (I := 𝓡₂) (M := M)) (x : M) :
    oneFormDissipationPairingDensity g (h + k) l x =
      oneFormDissipationPairingDensity g h l x + oneFormDissipationPairingDensity g k l x := by
  simp only [oneFormDissipationPairingDensity, roughLap0SField_add,
    metricNabla0S_add]
  rw [ahlforsPart_add]
  simp only [ContMDiffSection.coe_add, Pi.add_apply, inner0S_add_left]
  ring

private theorem pairingDensity_smul_left (g : SmoothRiemannianMetric 𝓡₂ M)
    (c : ℝ) (h k : OneFormSection (I := 𝓡₂) (M := M)) (x : M) :
    oneFormDissipationPairingDensity g (c • h) k x =
      c * oneFormDissipationPairingDensity g h k x := by
  simp only [oneFormDissipationPairingDensity, roughLap0SField_smul,
    metricNabla0S_smul]
  rw [ahlforsPart_smul]
  simp only [ContMDiffSection.coe_smul, Pi.smul_apply, inner0S_smul_left]
  ring

section Compact

variable [CompactSpace M]

theorem oneFormDissipationDensity_integrable (g : SmoothRiemannianMetric 𝓡₂ M)
    (h : OneFormSection (I := 𝓡₂) (M := M)) :
    Integrable (oneFormDissipationDensity g h) (riemannianVolumeMeasure 𝓡₂ M g) := by
  let := riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace g
  exact (oneFormDissipationDensity_smooth g h).continuous.integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

theorem oneFormDissipationPairingDensity_integrable (g : SmoothRiemannianMetric 𝓡₂ M)
    (h k : OneFormSection (I := 𝓡₂) (M := M)) :
    Integrable (oneFormDissipationPairingDensity g h k)
      (riemannianVolumeMeasure 𝓡₂ M g) := by
  let := riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace g
  exact (oneFormDissipationPairingDensity_smooth g h k).continuous.integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

/-- Complete canonical one-form Hodge dissipation on a compact smooth surface. -/
def oneFormDissipation (g : SmoothRiemannianMetric 𝓡₂ M)
    (h : OneFormSection (I := 𝓡₂) (M := M)) : ℝ :=
  ∫ x, oneFormDissipationDensity g h x ∂(riemannianVolumeMeasure 𝓡₂ M g)

/-- The actual four-term polarized dissipation pairing. -/
def oneFormDissipationPairing (g : SmoothRiemannianMetric 𝓡₂ M)
    (h k : OneFormSection (I := 𝓡₂) (M := M)) : ℝ :=
  ∫ x, oneFormDissipationPairingDensity g h k x ∂(riemannianVolumeMeasure 𝓡₂ M g)

theorem oneFormDissipationPairing_self (g : SmoothRiemannianMetric 𝓡₂ M)
    (h : OneFormSection (I := 𝓡₂) (M := M)) :
    oneFormDissipationPairing g h h = oneFormDissipation g h := rfl

theorem oneFormDissipationPairing_symm (g : SmoothRiemannianMetric 𝓡₂ M)
    (h k : OneFormSection (I := 𝓡₂) (M := M)) :
    oneFormDissipationPairing g h k = oneFormDissipationPairing g k h := by
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (pairingDensity_symm g h k)

theorem oneFormDissipationPairing_add_left (g : SmoothRiemannianMetric 𝓡₂ M)
    (h k l : OneFormSection (I := 𝓡₂) (M := M)) :
    oneFormDissipationPairing g (h + k) l =
      oneFormDissipationPairing g h l + oneFormDissipationPairing g k l := by
  simp only [oneFormDissipationPairing, pairingDensity_add_left]
  exact integral_add (oneFormDissipationPairingDensity_integrable g h l)
    (oneFormDissipationPairingDensity_integrable g k l)

theorem oneFormDissipationPairing_smul_left (g : SmoothRiemannianMetric 𝓡₂ M)
    (c : ℝ) (h k : OneFormSection (I := 𝓡₂) (M := M)) :
    oneFormDissipationPairing g (c • h) k = c * oneFormDissipationPairing g h k := by
  simp only [oneFormDissipationPairing, pairingDensity_smul_left]
  exact integral_const_mul c _

theorem oneFormDissipationPairing_add_right (g : SmoothRiemannianMetric 𝓡₂ M)
    (h k l : OneFormSection (I := 𝓡₂) (M := M)) :
    oneFormDissipationPairing g h (k + l) =
      oneFormDissipationPairing g h k + oneFormDissipationPairing g h l := by
  rw [oneFormDissipationPairing_symm g h (k + l), oneFormDissipationPairing_add_left,
    oneFormDissipationPairing_symm g k h, oneFormDissipationPairing_symm g l h]

theorem oneFormDissipationPairing_smul_right (g : SmoothRiemannianMetric 𝓡₂ M)
    (c : ℝ) (h k : OneFormSection (I := 𝓡₂) (M := M)) :
    oneFormDissipationPairing g h (c • k) = c * oneFormDissipationPairing g h k := by
  rw [oneFormDissipationPairing_symm g h (c • k), oneFormDissipationPairing_smul_left,
    oneFormDissipationPairing_symm g k h]

theorem oneFormDissipation_smul (g : SmoothRiemannianMetric 𝓡₂ M)
    (c : ℝ) (h : OneFormSection (I := 𝓡₂) (M := M)) :
    oneFormDissipation g (c • h) = c ^ 2 * oneFormDissipation g h := by
  rw [← oneFormDissipationPairing_self, oneFormDissipationPairing_smul_left,
    oneFormDissipationPairing_smul_right, oneFormDissipationPairing_self]
  ring

@[simp] theorem oneFormDissipation_zero (g : SmoothRiemannianMetric 𝓡₂ M) :
    oneFormDissipation g 0 = 0 := by
  simpa using oneFormDissipation_smul g 0 (0 : OneFormSection (I := 𝓡₂) (M := M))

theorem oneFormDissipation_add (g : SmoothRiemannianMetric 𝓡₂ M)
    (h k : OneFormSection (I := 𝓡₂) (M := M)) :
    oneFormDissipation g (h + k) = oneFormDissipation g h +
      2 * oneFormDissipationPairing g h k + oneFormDissipation g k := by
  rw [← oneFormDissipationPairing_self, oneFormDissipationPairing_add_left,
    oneFormDissipationPairing_add_right, oneFormDissipationPairing_add_right,
    oneFormDissipationPairing_self, oneFormDissipationPairing_self,
    oneFormDissipationPairing_symm g k h]
  ring

theorem oneFormDissipation_sub (g : SmoothRiemannianMetric 𝓡₂ M)
    (h k : OneFormSection (I := 𝓡₂) (M := M)) :
    oneFormDissipation g (h - k) = oneFormDissipation g h -
      2 * oneFormDissipationPairing g h k + oneFormDissipation g k := by
  rw [show h - k = h + (-1 : ℝ) • k by rw [neg_one_smul, sub_eq_add_neg],
    oneFormDissipation_add, oneFormDissipation_smul, oneFormDissipationPairing_smul_right]
  ring

theorem oneFormDissipation_parallelogram (g : SmoothRiemannianMetric 𝓡₂ M)
    (h k : OneFormSection (I := 𝓡₂) (M := M)) :
    oneFormDissipation g (h + k) + oneFormDissipation g (h - k) =
      2 * (oneFormDissipation g h + oneFormDissipation g k) := by
  rw [oneFormDissipation_add, oneFormDissipation_sub]
  ring

end Compact

end RicciFlowSharpEstimate.Geometry
