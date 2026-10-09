/-
Copyright (c) 2026 Ziyang Qin. All rights reserved.
No license is granted by this file.
Authors: Ziyang Qin
-/
import RicciFlowSharpEstimate.Analysis.ManifoldIntervalIntegral
import RicciFlowSharpEstimate.Geometry.CanonicalDerivatives

/-!
# Smooth interval integrals of covariant tensor fields

A jointly smooth family of covariant tensor fields has a smooth interval integral.
The tensor is integrated in its native fiber, and both evaluation and metric
covariant differentiation commute with this integral.
-/

noncomputable section

namespace RicciFlowSharpEstimate.Geometry

open Bundle DifferentialGeometry DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Tensor.Multilinear DifferentialGeometry.Tensor.Coordinates
open DifferentialGeometry.Integral.Connection DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.Geometry.Curvature
open MeasureTheory Set
open scoped Manifold ContDiff Topology Interval BigOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

@[instance_reducible]
private def tensorFiberENormedAddMonoid (s : ℕ) (x : M) :
    ENormedAddMonoid (Tensor0SSpace (𝕜 := ℝ) (E := E) (I := I) s x) :=
  @NormedAddGroup.toENormedAddMonoid _
    (tensor0SSpaceNormedAddCommGroup (𝕜 := ℝ) (E := E) (I := I) s x).toNormedAddGroup

attribute [local instance] tensorFiberENormedAddMonoid

private def tensorEvaluationCLM {s : ℕ} (x : M) (v : Fin s → TangentSpace I x) :
    Tensor0SSpace (𝕜 := ℝ) (E := E) (I := I) s x →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun T => T v
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }

/-- A jointly smooth tensor family is continuous in each fixed tensor fiber. -/
theorem continuous_tensorFamily_at {s : ℕ}
    (A : ℝ → Tensor0SField (𝕜 := ℝ) (I := I) (M := M) (n := ∞) s)
    (hA : ContMDiff (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, Tensor0SModel s ℝ E)) ∞
      (fun p : ℝ × M => TotalSpace.mk' (Tensor0SModel s ℝ E) p.2 (A p.1 p.2)))
    (x : M) : Continuous (fun t => A t x) := by
  apply (FiberBundle.totalSpaceMk_isInducing (Tensor0SModel s ℝ E)
    (fun y : M => Tensor0SSpace (𝕜 := ℝ) (E := E) (I := I) s y) x).continuous_iff.mpr
  exact hA.continuous.comp (continuous_id.prodMk continuous_const)

/-- Jointly smooth covariant tensor fields are integrable in every fixed fiber
on each finite interval. -/
theorem intervalIntegrable_tensorFamily_at {s : ℕ}
    (A : ℝ → Tensor0SField (𝕜 := ℝ) (I := I) (M := M) (n := ∞) s)
    (hA : ContMDiff (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, Tensor0SModel s ℝ E)) ∞
      (fun p : ℝ × M => TotalSpace.mk' (Tensor0SModel s ℝ E) p.2 (A p.1 p.2)))
    (x : M) (a b : ℝ) :
    IntervalIntegrable
      (fun t => (A t x : Tensor0SSpace (𝕜 := ℝ) (E := E) (I := I) s x)) volume a b :=
  (continuous_tensorFamily_at A hA x).intervalIntegrable a b

/-- Joint evaluation of a jointly smooth tensor family against smooth source
vector fields is smooth. -/
theorem contMDiff_tensorFamily_apply_sections {s : ℕ}
    (A : ℝ → Tensor0SField (𝕜 := ℝ) (I := I) (M := M) (n := ∞) s)
    (hA : ContMDiff (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, Tensor0SModel s ℝ E)) ∞
      (fun p : ℝ × M => TotalSpace.mk' (Tensor0SModel s ℝ E) p.2 (A p.1 p.2)))
    (V : Fin s → ContMDiffSection I E ∞ (TangentSpace I : M → Type _)) :
    ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M => A p.1 p.2 (fun i => V i p.2)) := by
  intro p₀
  exact TensorMultilinear.contMDiffWithinAt_section_apply_base s Prod.snd contMDiffAt_snd
    (fun p => A p.1 p.2) hA.contMDiffAt (fun i p => V i p.2)
    (fun i => ((V i).contMDiff.comp contMDiff_snd).contMDiffAt)

variable [I.Boundaryless]

private theorem tensorIntervalIntegral_contMDiff {s : ℕ}
    (A : ℝ → Tensor0SField (𝕜 := ℝ) (I := I) (M := M) (n := ∞) s)
    (hA : ContMDiff (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, Tensor0SModel s ℝ E)) ∞
      (fun p : ℝ × M => TotalSpace.mk' (Tensor0SModel s ℝ E) p.2 (A p.1 p.2)))
    (a b : ℝ) :
    ContMDiff I (I.prod 𝓘(ℝ, Tensor0SModel s ℝ E)) ∞
      (fun x => TotalSpace.mk' (Tensor0SModel s ℝ E) x (∫ t in a..b, A t x)) := by
  intro x₀
  let e := trivializationAt (Tensor0SModel s ℝ E)
    (fun x : M => Tensor0SSpace (𝕜 := ℝ) (E := E) (I := I) s x) x₀
  have hcoord : ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, Tensor0SModel s ℝ E) ∞
      (fun p : ℝ × M => (e ⟨p.2, A p.1 p.2⟩).2) (univ ×ˢ e.baseSet) :=
    (e.contMDiffOn_iff (fun _ hp => hp.2)).mp hA.contMDiffOn |>.2
  have hint := Analysis.contMDiffOn_intervalIntegral (⊤ : ℕ∞) a b e.open_baseSet
    isOpen_univ (subset_univ _) hcoord
  have hx₀ : x₀ ∈ e.baseSet := mem_baseSet_trivializationAt _ _ x₀
  apply (e.contMDiffAt_iff (e.mem_source.mpr hx₀)).mpr
  refine ⟨contMDiffAt_id, ?_⟩
  apply (hint.contMDiffAt
    (e.open_baseSet.mem_nhds (mem_baseSet_trivializationAt _ _ x₀))).congr_of_eventuallyEq
  filter_upwards [e.open_baseSet.mem_nhds (mem_baseSet_trivializationAt _ _ x₀)] with x hx
  change (e ⟨x, ∫ t in a..b, A t x⟩).2 = ∫ t in a..b, (e ⟨x, A t x⟩).2
  calc
    (e ⟨x, ∫ t in a..b, A t x⟩).2 =
        (e.continuousLinearMapAt ℝ x) (∫ t in a..b, A t x) :=
      (e.continuousLinearMapAt_apply_of_mem (R := ℝ) hx _).symm
    _ = ∫ t in a..b, (e.continuousLinearMapAt ℝ x) (A t x) :=
      ((e.continuousLinearMapAt ℝ x).intervalIntegral_comp_comm
        (intervalIntegrable_tensorFamily_at A hA x a b)).symm
    _ = ∫ t in a..b, (e ⟨x, A t x⟩).2 :=
      intervalIntegral.integral_congr fun t _ =>
        e.continuousLinearMapAt_apply_of_mem (R := ℝ) hx (A t x)

/-- The smooth interval integral of a jointly smooth covariant tensor family,
formed by the literal Bochner integral in each native tensor fiber. -/
def tensorIntervalIntegral {s : ℕ}
    (A : ℝ → Tensor0SField (𝕜 := ℝ) (I := I) (M := M) (n := ∞) s)
    (hA : ContMDiff (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, Tensor0SModel s ℝ E)) ∞
      (fun p : ℝ × M => TotalSpace.mk' (Tensor0SModel s ℝ E) p.2 (A p.1 p.2)))
    (a b : ℝ) : Tensor0SField (𝕜 := ℝ) (I := I) (M := M) (n := ∞) s :=
  ⟨fun x => ∫ t in a..b, A t x, tensorIntervalIntegral_contMDiff A hA a b⟩

/-- The interval-integral field is the Bochner integral of the original fields
at every base point. -/
theorem tensorIntervalIntegral_apply {s : ℕ}
    (A : ℝ → Tensor0SField (𝕜 := ℝ) (I := I) (M := M) (n := ∞) s)
    (hA : ContMDiff (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, Tensor0SModel s ℝ E)) ∞
      (fun p : ℝ × M => TotalSpace.mk' (Tensor0SModel s ℝ E) p.2 (A p.1 p.2)))
    (a b : ℝ) (x : M) : tensorIntervalIntegral A hA a b x = ∫ t in a..b, A t x := rfl

/-- Evaluation of the smooth tensor integral commutes with interval integration. -/
theorem tensorIntervalIntegral_eval {s : ℕ}
    (A : ℝ → Tensor0SField (𝕜 := ℝ) (I := I) (M := M) (n := ∞) s)
    (hA : ContMDiff (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, Tensor0SModel s ℝ E)) ∞
      (fun p : ℝ × M => TotalSpace.mk' (Tensor0SModel s ℝ E) p.2 (A p.1 p.2)))
    (a b : ℝ) (x : M) (v : Fin s → TangentSpace I x) :
    tensorIntervalIntegral A hA a b x v = ∫ t in a..b, A t x v :=
  ((tensorEvaluationCLM x v).intervalIntegral_comp_comm
    (intervalIntegrable_tensorFamily_at A hA x a b)).symm

variable [T2Space M]

private theorem metricNabla0S_tensorIntervalIntegral_sections {s : ℕ}
    (g : SmoothRiemannianMetric I M)
    (A : ℝ → Tensor0SField (𝕜 := ℝ) (I := I) (M := M) (n := ∞) s)
    (hA : ContMDiff (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, Tensor0SModel s ℝ E)) ∞
      (fun p : ℝ × M => TotalSpace.mk' (Tensor0SModel s ℝ E) p.2 (A p.1 p.2)))
    (a b : ℝ)
    (X : ContMDiffSection I E ∞ (TangentSpace I : M → Type _))
    (V : Fin s → ContMDiffSection I E ∞ (TangentSpace I : M → Type _)) (x : M) :
    metricNabla0S g (tensorIntervalIntegral A hA a b) x
        (Fin.cons (X x) (fun i => V i x)) =
      ∫ t in a..b, metricNabla0S g (A t) x (Fin.cons (X x) (fun i => V i x)) := by
  let F : ℝ × M → ℝ := fun p => A p.1 p.2 (fun i => V i p.2)
  have hF : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞ F :=
    contMDiff_tensorFamily_apply_sections A hA V
  have hscalar : (fun y => tensorIntervalIntegral A hA a b y (fun i => V i y)) =
      (fun y => ∫ t in a..b, F (t, y)) :=
    funext fun y => tensorIntervalIntegral_eval A hA a b y (fun i => V i y)
  rw [(canonicalDerivatives_first g (tensorIntervalIntegral A hA a b)).eval_smooth_slots X V x,
    hscalar, Analysis.mvfderiv_intervalIntegral_apply a b hF x (X x)]
  let W : Fin s → Fin s → TangentSpace I x :=
    fun i => Function.update (fun j => V j x) i (metricCov g (fun y => V i y) x (X x))
  have hcorr (i : Fin s) : IntervalIntegrable (fun t => A t x (W i)) volume a b :=
    ((tensorEvaluationCLM x (W i)).continuous.comp
      (continuous_tensorFamily_at A hA x)).intervalIntegrable a b
  have hder : IntervalIntegrable
      (fun t => mvfderiv I (fun y => F (t, y)) x (X x)) volume a b :=
    Analysis.intervalIntegrable_mvfderiv_apply a b hF x (X x)
  have hsum : IntervalIntegrable (fun t => ∑ i : Fin s, A t x (W i)) volume a b := by
    simpa only [Finset.sum_fn] using
      IntervalIntegrable.sum Finset.univ (fun i _ => hcorr i)
  simp_rw [tensorIntervalIntegral_eval]
  change (∫ t in a..b, mvfderiv I (fun y => F (t, y)) x (X x)) -
      ∑ i : Fin s, ∫ t in a..b, A t x (W i) = _
  rw [← intervalIntegral.integral_finsetSum (fun i _ => hcorr i)]
  rw [← intervalIntegral.integral_sub hder hsum]
  apply intervalIntegral.integral_congr
  intro t _
  exact ((canonicalDerivatives_first g (A t)).eval_smooth_slots X V x).symm

/-- The actual metric covariant derivative commutes with integration of a
jointly smooth covariant tensor family. -/
theorem metricNabla0S_tensorIntervalIntegral {s : ℕ}
    (g : SmoothRiemannianMetric I M)
    (A : ℝ → Tensor0SField (𝕜 := ℝ) (I := I) (M := M) (n := ∞) s)
    (hA : ContMDiff (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, Tensor0SModel s ℝ E)) ∞
      (fun p : ℝ × M => TotalSpace.mk' (Tensor0SModel s ℝ E) p.2 (A p.1 p.2)))
    (a b : ℝ) (x : M) (v : Fin (s + 1) → TangentSpace I x) :
    metricNabla0S g (tensorIntervalIntegral A hA a b) x v =
      ∫ t in a..b, metricNabla0S g (A t) x v := by
  obtain ⟨X, hX⟩ := ContMDiffSection.exists_eq_at
    (I := I) (F := E) (V := TangentSpace I) (n := (⊤ : ℕ∞)) x (v 0)
  choose V hV using fun i : Fin s => ContMDiffSection.exists_eq_at
    (I := I) (F := E) (V := TangentSpace I) (n := (⊤ : ℕ∞)) x (v i.succ)
  have hv : Fin.cons (X x) (fun i => V i x) = v := by
    funext i
    exact Fin.cases hX hV i
  rw [← hv]
  exact metricNabla0S_tensorIntervalIntegral_sections g A hA a b X V x

end RicciFlowSharpEstimate.Geometry
