/-
Copyright (c) 2026 Ziyang Qin. All rights reserved.
No license is granted by this file.
Authors: Ziyang Qin
-/
import RicciFlowSharpEstimate.Geometry.AlternatingSurfaceTensors
import DifferentialGeometry.Geometry.Connection.TensorNabla.Tensor0S.PartialEvaluation
import DifferentialGeometry.Geometry.Operator.Gradient.CotangentSharpSmoothness
import DifferentialGeometry.Geometry.Metric.TensorInner.Cotangent.InverseMetricField

/-!
# One-form rotation and metric derivatives

The smooth contraction construction adapts Ziyang Qin's historical
`SurfaceHodgeCurlMeanZero.lean`. A unit alternating area tensor is automatically
parallel, and rotation acts on the final covector slot of both native metric
derivatives, including the second derivative's connection corrections.
-/

noncomputable section

namespace RicciFlowSharpEstimate.Geometry

open Bundle DifferentialGeometry DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Tensor.RicciIdentity DifferentialGeometry.PDE.RicciFlow
open scoped Manifold ContDiff BigOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

private def partialOneForm (T : TwoTensorSection (I := I) (M := M))
    (V : ContMDiffSection I E ∞ (TangentSpace I : M → Type _)) :
    OneFormSection (I := I) (M := M) :=
  ⟨fun x => tensor0SCurry 1 x (T x) (V x),
    Tensor0SPartialEval.contMDiff_tensor0SPartialEval I M
      (fun x => T x) T.contMDiff (fun x => V x) V.contMDiff⟩

private theorem partialOneForm_apply (T : TwoTensorSection (I := I) (M := M))
    (V : ContMDiffSection I E ∞ (TangentSpace I : M → Type _))
    (x : M) (Y : TangentSpace I x) :
    partialOneForm T V x (fun _ : Fin 1 => Y) = T x (vec2 (V x) Y) := by
  exact tensor0S_curry_one_apply (T x) (V x) Y

private def sharpSection (g : SmoothRiemannianMetric I M)
    (h : OneFormSection (I := I) (M := M)) :
    ContMDiffSection I E ∞ (TangentSpace I : M → Type _) :=
  ⟨fun x => cotangentSharp g x (h x),
    cotangentSharp_gen_contMDiff_total (I := I) g (fun a j => by
      apply (cotangentSection_chartComponent_contMDiffOn (I := I) h a j).congr
      intro x hx
      exact congrArg (fun T : Tensor0SModel 1 ℝ E =>
        T (fun _ : Fin 1 => DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber
          (I := I) a j x))
        (tensor0SSpace_continuousLinearEquiv_apply 1 x (h x)).symm)⟩

private def areaContractionAt (g : SmoothRiemannianMetric I M)
    (Ω : TwoTensorSection (I := I) (M := M)) (x : M) :
    Tensor0SSpace (I := I) 1 x →ₗ[ℝ] Tensor0SSpace (I := I) 1 x :=
  (tensor0SCurry 1 x (Ω x)).toLinearMap.comp (cotangentSharpLinear g x)

private theorem areaContractionAt_apply (g : SmoothRiemannianMetric I M)
    (Ω : TwoTensorSection (I := I) (M := M)) (x : M)
    (α : Tensor0SSpace (I := I) 1 x) (Y : TangentSpace I x) :
    areaContractionAt g Ω x α (fun _ : Fin 1 => Y) = Ω x (vec2 (cotangentSharp g x α) Y) :=
  tensor0S_curry_one_apply (Ω x) (cotangentSharp g x α) Y

/-- The smooth one-form `Ω(h♯, -)`, giving Hodge rotation when `Ω` is a unit area tensor. -/
def oneFormAreaContraction (g : SmoothRiemannianMetric I M)
    (Ω : TwoTensorSection (I := I) (M := M))
    (h : OneFormSection (I := I) (M := M)) : OneFormSection (I := I) (M := M) :=
  partialOneForm Ω (sharpSection g h)

@[simp]
theorem oneFormAreaContraction_apply (g : SmoothRiemannianMetric I M)
    (Ω : TwoTensorSection (I := I) (M := M))
    (h : OneFormSection (I := I) (M := M)) (x : M) (Y : TangentSpace I x) :
    oneFormAreaContraction g Ω h x (fun _ : Fin 1 => Y) =
      Ω x (vec2 (cotangentSharp g x (h x)) Y) :=
  partialOneForm_apply Ω (sharpSection g h) x Y

theorem oneFormAreaContraction_add (g : SmoothRiemannianMetric I M)
    (Ω : TwoTensorSection (I := I) (M := M))
    (h k : OneFormSection (I := I) (M := M)) :
    oneFormAreaContraction g Ω (h + k) =
      oneFormAreaContraction g Ω h + oneFormAreaContraction g Ω k := by
  refine DFunLike.ext _ _ fun x => ?_
  exact (areaContractionAt g Ω x).map_add (h x) (k x)

theorem oneFormAreaContraction_smul (g : SmoothRiemannianMetric I M)
    (Ω : TwoTensorSection (I := I) (M := M)) (c : ℝ)
    (h : OneFormSection (I := I) (M := M)) :
    oneFormAreaContraction g Ω (c • h) = c • oneFormAreaContraction g Ω h := by
  refine DFunLike.ext _ _ fun x => ?_
  exact (areaContractionAt g Ω x).map_smul c (h x)

variable [T2Space M]

private theorem nablaOne_apply_sections (g : SmoothRiemannianMetric I M)
    (A : OneFormSection (I := I) (M := M))
    (X Y : ContMDiffSection I E ∞ (TangentSpace I : M → Type _)) (x : M) :
    metricNabla0S g A x (vec2 (X x) (Y x)) =
      mvfderiv (I := I) (fun y => A y (fun _ : Fin 1 => Y y)) x (X x) -
        A x (fun _ : Fin 1 => metricCov g (fun y => Y y) x (X x)) := by
  have h := (canonicalDerivatives_first g A).eval_smooth_slots X (fun _ : Fin 1 => Y) x
  have hcons : Fin.cons (X x) (fun _ : Fin 1 => Y x) = vec2 (X x) (Y x) := by
    funext i
    fin_cases i <;> rfl
  have hup : Function.update (fun _ : Fin 1 => Y x) 0
      (metricCov g (fun y => Y y) x (X x)) =
        fun _ : Fin 1 => metricCov g (fun y => Y y) x (X x) := by
    funext i
    fin_cases i
    simp
  simpa only [hcons, Fin.sum_univ_one, hup] using h

private theorem nablaTwo_apply_sections (g : SmoothRiemannianMetric I M)
    (T : TwoTensorSection (I := I) (M := M))
    (X V Y : ContMDiffSection I E ∞ (TangentSpace I : M → Type _)) (x : M) :
    metricNabla0S g T x (vec3 (X x) (V x) (Y x)) =
      mvfderiv (I := I) (fun y => T y (vec2 (V y) (Y y))) x (X x) -
        T x (vec2 (metricCov g (fun y => V y) x (X x)) (Y x)) -
          T x (vec2 (V x) (metricCov g (fun y => Y y) x (X x))) := by
  have h := (canonicalDerivatives_first g T).eval_smooth_slots X
    (Fin.cons V (fun _ : Fin 1 => Y)) x
  have hfields (y : M) : (fun i : Fin 2 =>
      ((Fin.cons V (fun _ : Fin 1 => Y) :
        Fin 2 → ContMDiffSection I E ∞ (TangentSpace I : M → Type _)) i) y) =
      vec2 (V y) (Y y) := by
    funext i
    fin_cases i <;> rfl
  simp_rw [hfields] at h
  have hcons : Fin.cons (X x) (vec2 (V x) (Y x)) = vec3 (X x) (V x) (Y x) := by
    funext i
    fin_cases i <;> rfl
  have hup₀ : Function.update (vec2 (V x) (Y x)) 0
      (metricCov g (fun y => V y) x (X x)) =
        vec2 (metricCov g (fun y => V y) x (X x)) (Y x) := by
    funext i
    fin_cases i <;> simp [vec2]
  have hup₁ : Function.update (vec2 (V x) (Y x)) 1
      (metricCov g (fun y => Y y) x (X x)) =
        vec2 (V x) (metricCov g (fun y => Y y) x (X x)) := by
    funext i
    fin_cases i <;> simp [vec2]
  have hfield₁ : (Fin.cons V (fun _ : Fin 1 => Y) :
      Fin 2 → ContMDiffSection I E ∞ (TangentSpace I : M → Type _)) 1 = Y := rfl
  simpa only [hcons, Fin.sum_univ_two, Fin.cons_zero, hfield₁, hup₀, hup₁,
    sub_sub] using h

private theorem metricNabla_partialOneForm (g : SmoothRiemannianMetric I M)
    (T : TwoTensorSection (I := I) (M := M))
    (V : ContMDiffSection I E ∞ (TangentSpace I : M → Type _))
    (x : M) (X Y : TangentSpace I x) :
    metricNabla0S g (partialOneForm T V) x (vec2 X Y) =
      metricNabla0S g T x (vec3 X (V x) Y) +
        T x (vec2 (metricCov g (fun y => V y) x X) Y) := by
  obtain ⟨Xs, hX⟩ := ContMDiffSection.exists_eq_at
    (I := I) (F := E) (V := TangentSpace I) (n := (⊤ : ℕ∞)) x X
  obtain ⟨Ys, hY⟩ := ContMDiffSection.exists_eq_at
    (I := I) (F := E) (V := TangentSpace I) (n := (⊤ : ℕ∞)) x Y
  have hp := nablaOne_apply_sections g (partialOneForm T V) Xs Ys x
  have ht := nablaTwo_apply_sections g T Xs V Ys x
  simp only [partialOneForm_apply, hX, hY] at hp ht
  rw [hp, ht]
  ring

private theorem metricNabla_partialOneForm_tensor (g : SmoothRiemannianMetric I M)
    (T : TwoTensorSection (I := I) (M := M))
    (V : ContMDiffSection I E ∞ (TangentSpace I : M → Type _))
    (x : M) (X : TangentSpace I x) :
    tensor0SCurry 1 x (metricNabla0S g (partialOneForm T V) x) X =
      freezeFirstTwoArgs0S (metricNabla0S g T x) X (V x) +
        tensor0SCurry 1 x (T x) (metricCov g (fun y => V y) x X) := by
  ext slots
  have hs : slots = fun _ : Fin 1 => slots 0 := by
    funext i
    exact congrArg slots (Fin.eq_zero i)
  have hvec (U W : TangentSpace I x) :
      (fun a : Fin 2 => if a = 0 then U else W) = vec2 U W := by
    funext i
    fin_cases i <;> rfl
  rw [hs, tensor0S_curry_one_apply, hvec]
  rw [metricNabla_partialOneForm, Tensor0SSpace.add_apply,
    freezeFirstTwoArgs0S_apply, tensor0S_curry_one_apply, hvec]
  congr 2
  funext i
  fin_cases i <;> rfl

private theorem metricNabla_contraction_parallel_apply (g : SmoothRiemannianMetric I M)
    (Ω : TwoTensorSection (I := I) (M := M)) (hΩ : metricNabla0S g Ω = 0)
    (h : OneFormSection (I := I) (M := M)) (x : M) (X Y : TangentSpace I x) :
    metricNabla0S g (oneFormAreaContraction g Ω h) x (vec2 X Y) =
      Ω x (vec2 (cotangentSharp g x (tensor0SCurry 1 x (metricNabla0S g h x) X)) Y) := by
  obtain ⟨Xs, hX⟩ := ContMDiffSection.exists_eq_at
    (I := I) (F := E) (V := TangentSpace I) (n := (⊤ : ℕ∞)) x X
  have hsharp := cotangentSharp_cov_eq_sharp_curry_of_mdiffAt (metricCov g) g
    (DifferentialGeometry.Geometry.Connection.leviCivitaConnectionOfMetric_isMetricCompatible g)
    h (metricNabla0S g h) (canonicalDerivatives_first g h) Xs x
    (sharpSection g h).mdifferentiableAt
  rw [hX] at hsharp
  have hp := metricNabla_partialOneForm g Ω (sharpSection g h) x X Y
  rw [hΩ] at hp
  change metricNabla0S g (oneFormAreaContraction g Ω h) x (vec2 X Y) =
    (0 : Tensor0SSpace (I := I) 3 x) (vec3 X (sharpSection g h x) Y) +
      Ω x (vec2 (metricCov g (fun y => cotangentSharp g y (h y)) x X) Y) at hp
  rw [Tensor0SSpace.zero_apply, zero_add, hsharp] at hp
  exact hp

private theorem metricNabla_contraction_parallel (g : SmoothRiemannianMetric I M)
    (Ω : TwoTensorSection (I := I) (M := M)) (hΩ : metricNabla0S g Ω = 0)
    (h : OneFormSection (I := I) (M := M)) (x : M) (X : TangentSpace I x) :
    tensor0SCurry 1 x (metricNabla0S g (oneFormAreaContraction g Ω h) x) X =
      areaContractionAt g Ω x (tensor0SCurry 1 x (metricNabla0S g h x) X) := by
  ext slots
  have hs : slots = fun _ : Fin 1 => slots 0 := by
    funext i
    exact congrArg slots (Fin.eq_zero i)
  rw [hs, tensor0S_curry_one_apply, areaContractionAt_apply]
  exact metricNabla_contraction_parallel_apply g Ω hΩ h x X (slots 0)

private theorem metricNabla_twice_contraction_parallel (g : SmoothRiemannianMetric I M)
    (Ω : TwoTensorSection (I := I) (M := M)) (hΩ : metricNabla0S g Ω = 0)
    (h : OneFormSection (I := I) (M := M)) (x : M) (X Y : TangentSpace I x) :
    freezeFirstTwoArgs0S
        (metricNabla0S g (metricNabla0S g (oneFormAreaContraction g Ω h)) x) X Y =
      areaContractionAt g Ω x
        (freezeFirstTwoArgs0S (metricNabla0S g (metricNabla0S g h) x) X Y) := by
  obtain ⟨V, hV⟩ := ContMDiffSection.exists_eq_at
    (I := I) (F := E) (V := TangentSpace I) (n := (⊤ : ℕ∞)) x Y
  have hpartial : partialOneForm (metricNabla0S g (oneFormAreaContraction g Ω h)) V =
      oneFormAreaContraction g Ω (partialOneForm (metricNabla0S g h) V) := by
    refine DFunLike.ext _ _ fun y => ?_
    exact metricNabla_contraction_parallel g Ω hΩ h y (V y)
  have hb := metricNabla_partialOneForm_tensor g
    (metricNabla0S g (oneFormAreaContraction g Ω h)) V x X
  rw [hpartial, metricNabla_contraction_parallel g Ω hΩ,
    metricNabla_partialOneForm_tensor, map_add,
    metricNabla_contraction_parallel g Ω hΩ] at hb
  have hc := (add_right_cancel hb).symm
  simpa only [hV] using hc

/-- Rotation acts on the final covector slot of the actual first metric derivative. -/
theorem metricNabla0S_oneFormAreaContraction
    (hdim : Module.finrank ℝ E = 2) (g : SmoothRiemannianMetric I M)
    (Ω : TwoTensorSection (I := I) (M := M))
    (hΩalt : ∀ x U V, Ω x (vec2 U V) = -Ω x (vec2 V U))
    (hΩnorm : ∀ x, normSq0S g x 2 (Ω x) = 2)
    (h : OneFormSection (I := I) (M := M)) (x : M) (X Y : TangentSpace I x) :
    metricNabla0S g (oneFormAreaContraction g Ω h) x (vec2 X Y) =
      Ω x (vec2 (cotangentSharp g x (tensor0SCurry 1 x (metricNabla0S g h x) X)) Y) :=
  metricNabla_contraction_parallel_apply g Ω
    (metricNabla0S_eq_zero_of_alternating_const_normSq hdim g Ω hΩalt 2 hΩnorm) h x X Y

/-- Rotation acts on the final covector slot of the actual second metric derivative. -/
theorem metricNabla0S_twice_oneFormAreaContraction
    (hdim : Module.finrank ℝ E = 2) (g : SmoothRiemannianMetric I M)
    (Ω : TwoTensorSection (I := I) (M := M))
    (hΩalt : ∀ x U V, Ω x (vec2 U V) = -Ω x (vec2 V U))
    (hΩnorm : ∀ x, normSq0S g x 2 (Ω x) = 2)
    (h : OneFormSection (I := I) (M := M)) (x : M) (X Y Z : TangentSpace I x) :
    metricNabla0S g (metricNabla0S g (oneFormAreaContraction g Ω h)) x (vec3 X Y Z) =
      Ω x (vec2 (cotangentSharp g x
        (freezeFirstTwoArgs0S (metricNabla0S g (metricNabla0S g h) x) X Y)) Z) := by
  have hc := metricNabla_twice_contraction_parallel g Ω
    (metricNabla0S_eq_zero_of_alternating_const_normSq hdim g Ω hΩalt 2 hΩnorm) h x X Y
  have he := congrArg (fun α : Tensor0SSpace (I := I) 1 x => α (fun _ : Fin 1 => Z)) hc
  rw [freezeFirstTwoArgs0S_apply, areaContractionAt_apply] at he
  convert he using 1
  congr 1
  funext i
  fin_cases i <;> rfl

/-- Hodge rotation commutes with the actual rough Laplacian. -/
theorem roughLap0SField_oneFormAreaContraction
    (hdim : Module.finrank ℝ E = 2) (g : SmoothRiemannianMetric I M)
    (Ω : TwoTensorSection (I := I) (M := M))
    (hΩalt : ∀ x U V, Ω x (vec2 U V) = -Ω x (vec2 V U))
    (hΩnorm : ∀ x, normSq0S g x 2 (Ω x) = 2)
    (h : OneFormSection (I := I) (M := M)) :
    roughLap0SField g (oneFormAreaContraction g Ω h) =
      oneFormAreaContraction g Ω (roughLap0SField g h) := by
  have hΩ := metricNabla0S_eq_zero_of_alternating_const_normSq hdim g Ω hΩalt 2 hΩnorm
  refine DFunLike.ext _ _ fun x => ?_
  change roughLap0STensor g
      (metricNabla0S g (metricNabla0S g (oneFormAreaContraction g Ω h)) x) =
    areaContractionAt g Ω x (roughLap0STensor g (metricNabla0S g (metricNabla0S g h) x))
  unfold roughLap0STensor metricTraceFirstTwo0STensor metricTrace0S2TensorInBasis
  simp only [map_sum, map_smul]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  congr 1
  exact metricNabla_twice_contraction_parallel g Ω hΩ h x _ _

end RicciFlowSharpEstimate.Geometry
