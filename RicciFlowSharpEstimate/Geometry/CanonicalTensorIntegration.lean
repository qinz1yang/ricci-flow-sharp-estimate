/-
Copyright (c) 2026 Ziyang Qin. All rights reserved.
No license is granted by this file.
Authors: Ziyang Qin
-/
import DifferentialGeometry.Geometry.Operator.CovariantTensor
import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.IntegrationByParts.Divergence
import DifferentialGeometry.Geometry.Connection.ChartTensorNabla.Agreement.Tensor0SRSCovariantDerivativeAgreement
import DifferentialGeometry.Geometry.Connection.ChartTensorNabla.Agreement.Nabla0SFunAgreement
import DifferentialGeometry.Geometry.Metric.TensorInner.TensorRS.Pairing

/-!
# Integration by parts for canonical covariant tensors

The covariant tensor operators in this module are the metric's native smooth
covariant derivative and its metric trace. Compactness supplies compact support
when passing a smooth covariant tensor to the released tensor integration theorem.
-/

noncomputable section

open Bundle MeasureTheory DifferentialGeometry DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Integral.Connection DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2 DifferentialGeometry.Analysis.Elliptic
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Geometry.Connection DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Operator DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.Tensor.RSTensor DifferentialGeometry.TensorMetric
open DifferentialGeometry.Tensor0SNabla DifferentialGeometry.TensorRSNabla
open scoped Manifold ContDiff BigOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
variable [IsManifold I ∞ M] [T2Space M] [CompactSpace M]
variable [I.Boundaryless] [BoundarylessManifold I M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E
private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

namespace RicciFlowSharpEstimate.Geometry

variable {s : ℕ}

/-- A smooth covariant tensor on a compact manifold, in the tensor integration API. -/
def compactTensor0S (g : SmoothRiemannianMetric I M)
    (T : Tensor0SField (𝕜 := ℝ) (I := I) (M := M) (n := ∞) s) :
    SmoothCcTensor g 0 s where
  toSection := T.toTensorRSField (∞ : WithTop ℕ∞)
  hasCompactSupport := HasCompactSupport.of_compactSpace _

omit [NeZero (Module.finrank ℝ E)] [T2Space M] [I.Boundaryless]
    [BoundarylessManifold I M] in
theorem compactTensor0S_toSection (g : SmoothRiemannianMetric I M)
    (T : Tensor0SField (𝕜 := ℝ) (I := I) (M := M) (n := ∞) s) (x : M) :
    (compactTensor0S g T).toSection x = Tensor0SSpace.toRS0 (T x) :=
  Tensor0SField.toRS0_eq (I := I) (M := M) (∞ : WithTop ℕ∞) T x

omit [NeZero (Module.finrank ℝ E)] [T2Space M] [I.Boundaryless]
    [BoundarylessManifold I M] in
theorem compactTensor0S_toFun (g : SmoothRiemannianMetric I M)
    (T : Tensor0SField (𝕜 := ℝ) (I := I) (M := M) (n := ∞) s) (x : M) :
    (compactTensor0S g T).toFun x = TensorRSSpace.toModel (Tensor0SSpace.toRS0 (T x)) := by
  rw [SmoothCcTensor.toFun_apply, compactTensor0S_toSection]

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless]
    [BoundarylessManifold I M] in
/-- Evaluation of the canonical derivative along a smooth tangent field. -/
theorem metricNabla0S_apply_section (g : SmoothRiemannianMetric I M)
    (T : Tensor0SField (𝕜 := ℝ) (I := I) (M := M) (n := ∞) s)
    (X : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M → Type _))
    (x : M) (v : Fin s → TangentSpace I x) :
    metricNabla0S g T x (Fin.cons (X x) v) =
      nabla0SFun s (metricCov (I := I) g) X T x v :=
  totalNabla0SFun_apply_section s (metricCov (I := I) g) X T x v

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] in
/-- The canonical derivative agrees with the chart tensor connection on every fiber. -/
theorem metricNabla0S_apply_cons (g : SmoothRiemannianMetric I M)
    (T : Tensor0SField (𝕜 := ℝ) (I := I) (M := M) (n := ∞) s)
    (x : M) (v₀ : TangentSpace I x) (v : Fin s → TangentSpace I x) :
    metricNabla0S g T x (Fin.cons v₀ v) =
      tensor0SCovariantDerivative I M s (LeviCivita (I := I) g)
        (fun y => T y) x v₀ v := by
  obtain ⟨X, hX⟩ := ContMDiffSection.exists_eq_at
    (I := I) (F := E) (V := TangentSpace I) (n := (⊤ : ℕ∞)) x v₀
  rw [← hX, metricNabla0S_apply_section]
  change nabla0SFun s (LeviCivita (I := I) g) X T x v = _
  rw [nabla0SFun_eq_tensor0SCovariantDerivative]

omit [NeZero (Module.finrank ℝ E)] [T2Space M] [CompactSpace M]
    [I.Boundaryless] [BoundarylessManifold I M] in
private theorem toRS0_apply_unitZero (x : M) (T : Tensor0SSpace s I x) :
    (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from Tensor0SSpace.toRS0 T)
      (unitZeroSec (I := I) (M := M) x) = T := by
  rw [Tensor0SSpace.toRS0_apply]
  have hone : tensor0SSpaceEvalScalar (𝕜 := ℝ) (I := I) x
      (unitZeroSec (I := I) (M := M) x) = 1 := by
    rw [Tensor0SSpace.evalScalar_apply, unitZeroSec_apply]
    rfl
  rw [hone, one_smul]

omit [NeZero (Module.finrank ℝ E)] [T2Space M] [CompactSpace M]
    [I.Boundaryless] [BoundarylessManifold I M] in
private theorem rs0_ext_unitZero (x : M) {A B : TensorRSSpace 0 s I x}
    (h : (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from A)
          (unitZeroSec (I := I) (M := M) x) =
        (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from B)
          (unitZeroSec (I := I) (M := M) x)) : A = B := by
  apply ContinuousLinearMap.ext
  intro D
  have hD : D = (tensor0Iso (I := I) M x D) • unitZeroSec (I := I) (M := M) x := by
    apply (tensor0Iso (I := I) M x).injective
    rw [map_smul]
    have hone : tensor0Iso (I := I) M x (unitZeroSec (I := I) (M := M) x) = 1 := by
      have hunit := congrFun (scalarFn_unitZero (I := I) (M := M)) x
      simpa only [scalarFn_apply, unitZeroSec_apply] using hunit
    rw [hone, smul_eq_mul, mul_one]
  rw [hD, map_smul, map_smul, h]

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
private theorem covariantDerivative_compactTensor0S_unit
    (g : SmoothRiemannianMetric I M)
    (T : Tensor0SField (𝕜 := ℝ) (I := I) (M := M) (n := ∞) s)
    (x : M) (v : TangentSpace I x) :
    (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from
      tensorRSCovariantDerivative I M 0 s (LeviCivita (I := I) g)
        (fun y => (compactTensor0S g T).toSection y) x v)
      (unitZeroSec (I := I) (M := M) x) =
    tensor0SCovariantDerivative I M s (LeviCivita (I := I) g)
      (fun y => T y) x v := by
  rw [tensorRSCovariantDerivative_zeroS_unit_eval]
  congr 2
  funext y
  rw [compactTensor0S_toSection, toRS0_apply_unitZero]

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
theorem covariantDerivative_compactTensor0S
    (g : SmoothRiemannianMetric I M)
    (T : Tensor0SField (𝕜 := ℝ) (I := I) (M := M) (n := ∞) s)
    (x : M) (v : TangentSpace I x) :
    tensorRSCovariantDerivative I M 0 s (LeviCivita (I := I) g)
        (fun y => (compactTensor0S g T).toSection y) x v =
      Tensor0SSpace.toRS0 (tensor0SCovariantDerivative I M s
        (LeviCivita (I := I) g) (fun y => T y) x v) := by
  apply rs0_ext_unitZero
  rw [covariantDerivative_compactTensor0S_unit, toRS0_apply_unitZero]

omit [NeZero (Module.finrank ℝ E)] in
/-- The spectral covariant gradient is the canonical metric covariant derivative. -/
theorem covGrad_compactTensor0S_toSection (g : SmoothRiemannianMetric I M)
    (T : Tensor0SField (𝕜 := ℝ) (I := I) (M := M) (n := ∞) s) (x : M) :
    (covGrad g 0 s (compactTensor0S g T)).toSection x =
      Tensor0SSpace.toRS0 (metricNabla0S g T x) := by
  apply rs0_ext_unitZero
  rw [toRS0_apply_unitZero]
  apply ContinuousMultilinearMap.ext
  intro v
  change Tensor0SSpace.eval
      ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 1) I x from
        (covGrad g 0 s (compactTensor0S g T)).toSection x)
        (unitZeroSec (I := I) (M := M) x)) v =
    Tensor0SSpace.eval (metricNabla0S g T x) v
  rw [covGrad_toSection_apply_natural, tensorCovDerivAt_def,
    ContinuousLinearEquiv.symm_apply_apply, covariantDerivative_compactTensor0S_unit]
  change tensor0SCovariantDerivative I M s (LeviCivita (I := I) g)
      (fun y => T y) x (v 0) (Matrix.vecTail v) = metricNabla0S g T x v
  rw [← metricNabla0S_apply_cons]
  congr 1
  funext i
  cases i using Fin.cases with
  | zero => rfl
  | succ i => rfl

omit [NeZero (Module.finrank ℝ E)] [T2Space M] [CompactSpace M]
    [I.Boundaryless] [BoundarylessManifold I M] in
private theorem metricTraceFirstTwoField_apply_orthonormal
    (g : SmoothRiemannianMetric I M)
    (A : Tensor0SField (𝕜 := ℝ) (I := I) (M := M) (n := ∞) (s + 2))
    (x : M)
    (b : Module.Basis (Fin (Module.finrank ℝ E)) ℝ (TangentSpace I x))
    (hb : ∀ i j, g.inner x (b i) (b j) = if i = j then 1 else 0)
    (v : Fin s → TangentSpace I x) :
    metricTraceFirstTwoField g A x v =
      ∑ i, A x (Fin.cons (b i) (Fin.cons (b i) v)) := by
  classical
  let gInv : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → ℝ :=
    fun i j => if i = j then 1 else 0
  have hinv : MetricInverseInBasis (I := I) g x b gInv := by
    intro i j
    constructor <;> simp [gInv, hb]
  rw [metricTraceFirstTwoField_apply, metricTraceFirstTwo0STensor_apply,
    metricTraceFirstTwo0SAt_eq_sum_basis (I := I) g b gInv hinv]
  simp only [metricTrace0S2InBasis, gInv, ite_mul, one_mul, zero_mul,
    Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  rfl

omit [NeZero (Module.finrank ℝ E)] [T2Space M] [CompactSpace M]
    [I.Boundaryless] [BoundarylessManifold I M] in
private theorem contractCovariant_eval {x : M} (v : TangentSpace I x)
    (A : TensorRSSpace 0 (s + 1) I x) (D : Tensor0SSpace 0 I x)
    (w : Fin s → TangentSpace I x) :
    ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from
      contractCovariant 0 s x v A) D) w =
    ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 1) I x from A) D)
      (Fin.cons v w) := by
  unfold contractCovariant
  simp only [ContinuousLinearMap.comp_apply]
  rw [tensorRSSpace_continuousLinearEquiv_symm_toContinuousLinearMap_apply_apply]
  simp only [ContinuousLinearMap.compL_apply, ContinuousLinearMap.comp_apply]
  change tensorRSSpaceContinuousLinearEquiv (I := I) 0 (s + 1) x A
      (Tensor0SSpace.toModel D)
      (Fin.cons (tangentSpaceModelContinuousLinearEquiv (I := I) x v)
        (fun i => tangentSpaceModelContinuousLinearEquiv (I := I) x (w i))) = _
  rw [tensorRSSpace_continuousLinearEquiv_apply_apply]
  rfl

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [T2Space M]
    [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] in
private theorem tensor0S_sum_apply {ι : Type*} [Fintype ι] (x : M)
    (A : ι → Tensor0SSpace s I x) (v : Fin s → TangentSpace I x) :
    (∑ i, A i) v = ∑ i, A i v := by
  change (tensor0SSpaceFiberContinuousLinearEquiv (I := I) s x (∑ i, A i)) v = _
  rw [map_sum, sum_apply]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- The spectral covariant divergence is the trace of the canonical derivative. -/
theorem covDivergence_compactTensor0S_toSection (g : SmoothRiemannianMetric I M)
    (V : Tensor0SField (𝕜 := ℝ) (I := I) (M := M) (n := ∞) (s + 1)) (x : M) :
    (covDivergence g s (compactTensor0S g V)).toSection x =
      Tensor0SSpace.toRS0 (covDiv0SField g V x) := by
  classical
  have hfr : ∀ i j : Fin (Module.finrank ℝ E),
      g.inner x (smoothOrthoFrame (I := I) g x i x)
        (smoothOrthoFrame (I := I) g x j x) = if i = j then 1 else 0 :=
    smoothOrthoFrame_orthonormal_at_center (I := I) g x
  have hli : LinearIndependent ℝ (fun i : Fin (Module.finrank ℝ E) =>
      smoothOrthoFrame (I := I) g x i x) := by
    rw [linearIndependent_iff']
    intro fs c hsum j hj
    have h := congrArg (fun v : TangentSpace I x =>
      g.inner x (smoothOrthoFrame (I := I) g x j x) v) hsum
    simp only [map_sum, map_smul, smul_eq_mul, map_zero, hfr] at h
    simpa [Finset.sum_ite_eq', hj] using h
  let b : Module.Basis (Fin (Module.finrank ℝ E)) ℝ (TangentSpace I x) :=
    basisOfLinearIndependentOfCardEqFinrank hli (by rw [Fintype.card_fin]; rfl)
  have hb : ∀ i, b i = smoothOrthoFrame (I := I) g x i x := fun i => by
    simp [b, coe_basisOfLinearIndependentOfCardEqFinrank]
  have horth : ∀ i j, g.inner x (b i) (b j) = if i = j then 1 else 0 := by
    intro i j
    rw [hb, hb]
    exact hfr i j
  rw [covDivergence_toSection_apply, covDivergenceRaw]
  apply rs0_ext_unitZero
  rw [toRS0_apply_unitZero, sum_apply]
  apply ContinuousMultilinearMap.ext
  intro w
  rw [tensor0S_sum_apply]
  change _ = metricTraceFirstTwoField g (metricNabla0S g V) x w
  rw [metricTraceFirstTwoField_apply_orthonormal g (metricNabla0S g V) x b horth]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hsm : MDifferentiableAt I (I.prod 𝓘(ℝ, E))
      (fun y : M => TotalSpace.mk' E (E := TangentSpace I) y
        (smoothOrthoFrame (I := I) g x i y)) x :=
    (smoothOrthoFrame_smooth (I := I) g x i).contMDiffAt.mdifferentiableAt (by simp)
  rw [codiffPsi_apply g s (compactTensor0S g V) x hsm hsm,
    contractCovariant_eval, covariantDerivative_compactTensor0S_unit, hb,
    ← metricNabla0S_apply_cons]

omit [NeZero (Module.finrank ℝ E)] [T2Space M] [CompactSpace M]
    [I.Boundaryless] [BoundarylessManifold I M] in
/-- The scalar lift preserves the actual fiber metric pairing. -/
theorem tensorInnerPointwise_toRS0_eq_inner0S (g : SmoothRiemannianMetric I M)
    (x : M) (A B : Tensor0SSpace s I x) :
    tensorInnerPointwise g 0 s x
        (TensorRSSpace.toModel (Tensor0SSpace.toRS0 A))
        (TensorRSSpace.toModel (Tensor0SSpace.toRS0 B)) =
      inner0S g x s A B := by
  rw [tensorInnerPointwise_eq_inner0S, toRS0_apply_unitZero, toRS0_apply_unitZero]

/-- Covariant differentiation and negative covariant divergence are formal adjoints
for the Riemannian volume of a compact manifold without boundary. -/
theorem integral_inner0S_metricNabla0S_eq_neg_covDiv0SField
    (g : SmoothRiemannianMetric I M)
    (T : Tensor0SField (𝕜 := ℝ) (I := I) (M := M) (n := ∞) s)
    (V : Tensor0SField (𝕜 := ℝ) (I := I) (M := M) (n := ∞) (s + 1)) :
    (∫ x, inner0S g x (s + 1) (metricNabla0S g T x) (V x)
      ∂(riemannianVolumeMeasure (I := I) (M := M) g)) =
      -(∫ x, inner0S g x s (T x) (covDiv0SField g V x)
        ∂(riemannianVolumeMeasure (I := I) (M := M) g)) := by
  have h := tensorL2Inner_covGrad_eq_neg_tensorL2Inner_covDivergence g s
    (compactTensor0S g T) (compactTensor0S g V)
  simpa only [tensorL2Inner, SmoothCcTensor.toFun_apply,
    compactTensor0S_toSection, covGrad_compactTensor0S_toSection,
    covDivergence_compactTensor0S_toSection, tensorInnerPointwise_toRS0_eq_inner0S] using h

/-- Green's identity for the native rough Laplacian. -/
theorem integral_inner0S_metricNabla0S_eq_neg_roughLap0SField
    (g : SmoothRiemannianMetric I M)
    (T U : Tensor0SField (𝕜 := ℝ) (I := I) (M := M) (n := ∞) s) :
    (∫ x, inner0S g x (s + 1) (metricNabla0S g T x) (metricNabla0S g U x)
      ∂(riemannianVolumeMeasure (I := I) (M := M) g)) =
      -(∫ x, inner0S g x s (T x) (roughLap0SField g U x)
        ∂(riemannianVolumeMeasure (I := I) (M := M) g)) :=
  integral_inner0S_metricNabla0S_eq_neg_covDiv0SField g T (metricNabla0S g U)

/-- The native rough Laplacian is formally self-adjoint. -/
theorem integral_inner0S_roughLap0SField_left_eq_right
    (g : SmoothRiemannianMetric I M)
    (T U : Tensor0SField (𝕜 := ℝ) (I := I) (M := M) (n := ∞) s) :
    (∫ x, inner0S g x s (roughLap0SField g T x) (U x)
      ∂(riemannianVolumeMeasure (I := I) (M := M) g)) =
      ∫ x, inner0S g x s (T x) (roughLap0SField g U x)
        ∂(riemannianVolumeMeasure (I := I) (M := M) g) := by
  have hTU := integral_inner0S_metricNabla0S_eq_neg_roughLap0SField g T U
  have hUT := integral_inner0S_metricNabla0S_eq_neg_roughLap0SField g U T
  have hgrad : (∫ x, inner0S g x (s + 1) (metricNabla0S g U x)
      (metricNabla0S g T x) ∂(riemannianVolumeMeasure (I := I) (M := M) g)) =
      ∫ x, inner0S g x (s + 1) (metricNabla0S g T x)
        (metricNabla0S g U x) ∂(riemannianVolumeMeasure (I := I) (M := M) g) := by
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun x => inner0S_symm g x _ _
  have hpair : (∫ x, inner0S g x s (roughLap0SField g T x) (U x)
      ∂(riemannianVolumeMeasure (I := I) (M := M) g)) =
      ∫ x, inner0S g x s (U x) (roughLap0SField g T x)
        ∂(riemannianVolumeMeasure (I := I) (M := M) g) := by
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun x => inner0S_symm g x _ _
  rw [hpair]
  rw [hgrad, hTU] at hUT
  exact neg_injective hUT.symm

end RicciFlowSharpEstimate.Geometry
