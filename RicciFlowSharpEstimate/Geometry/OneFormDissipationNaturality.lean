/-
Copyright (c) 2026 Ziyang Qin. All rights reserved.
No license is granted by this file.
Authors: Ziyang Qin
-/
import RicciFlowSharpEstimate.Geometry.OneFormDissipation
import DifferentialGeometry.Geometry.Curvature.Naturality.Pullback.Basic
import DifferentialGeometry.Geometry.Metric.TensorInner.FiberMetric.Tensor0SMetricPullback
import DifferentialGeometry.Geometry.Metric.Convergence.Naturality.PullbackCross
import DifferentialGeometry.Analysis.Integration.Measure.Riemannian.Naturality

/-!
# Naturality of one-form dissipation

Smooth tensor pullback uses the actual derivative of the diffeomorphism.
Metric covariant differentiation, rough Laplacian, tensor norms and the Ahlfors
projection commute with pullback. Consequently the full one-form action and
its polarization are invariant under every smooth isometry, without an
orientation restriction.
-/

noncomputable section

namespace RicciFlowSharpEstimate.Geometry

open Bundle DifferentialGeometry DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.PDE.RicciFlow DifferentialGeometry.Tensor.Multilinear
open DifferentialGeometry.Tensor.Coordinates
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.Measure DifferentialGeometry.Tensor.RicciIdentity
open DifferentialGeometry.Geometry.Riemannian.VolumeComparison
open scoped Manifold ContDiff Topology BigOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

private def diffeomorphTensorPullbackAt (f : M ≃ₘ⟮I, I⟯ M) (s : ℕ) (x : M) :
    Tensor0SSpace (I := I) s (f x) ≃L[ℝ] Tensor0SSpace (I := I) s x :=
  tensor0SPullbackCLE s
    (Diffeomorph.mfderivToContinuousLinearEquiv f (by simp) x).toLinearEquiv

private theorem diffeomorphTensorPullbackAt_apply (f : M ≃ₘ⟮I, I⟯ M) (s : ℕ) (x : M)
    (A : Tensor0SSpace (I := I) s (f x)) (v : Fin s → TangentSpace I x) :
    diffeomorphTensorPullbackAt f s x A v =
      A (fun i => mfderiv I I f x (v i)) := by
  simp only [diffeomorphTensorPullbackAt, tensor0SPullbackCLE_apply,
    tensor0SPullbackCLM_apply]
  congr 1

private theorem diffeomorphTensorPullback_smooth (f : M ≃ₘ⟮I, I⟯ M) {s : ℕ}
    (A : Tensor0SField (𝕜 := ℝ) (I := I) (M := M) (n := ∞) s) :
    ContMDiff I (I.prod 𝓘(ℝ, Tensor0SModel s ℝ E)) ∞
      (fun x => TotalSpace.mk' (Tensor0SModel s ℝ E) x
        (diffeomorphTensorPullbackAt f s x (A (f x)))) := by
  let b := Module.finBasis ℝ E
  apply (contMDiff_multilinearSection_iff_coord (TangentSpace I) ∞ b _).mpr
  intro σ x₀
  let V : Fin s → (x : M) → TangentSpace I x :=
    fun i => coordinateFrameAt (I := I) x₀ (σ i)
  have hV (i : Fin s) : ContMDiffAt I (I.prod 𝓘(ℝ, E)) ∞
      (fun x => TotalSpace.mk' E x (V i x)) x₀ :=
    (coordinateFrameAt_isLocalFrame (I := I) x₀).contMDiffAt
      (coordinateFrameSet_open (I := I) x₀) (coordinateFrameAt_mem (I := I) x₀) (σ i)
  have hdf (i : Fin s) : ContMDiffAt I (I.prod 𝓘(ℝ, E)) ∞
      (fun x => TotalSpace.mk' E (f x) (mfderiv I I f x (V i x))) x₀ :=
    (f.contMDiff.contMDiff_tangentMap (le_refl _)).contMDiffAt.comp x₀ (hV i)
  have hA := A.contMDiff.comp f.contMDiff
  have hev : ContMDiffAt I 𝓘(ℝ, ℝ) ∞
      (fun x => A (f x) (fun i => mfderiv I I f x (V i x))) x₀ :=
    TensorMultilinear.contMDiffWithinAt_section_apply_base s f f.contMDiff.contMDiffAt
      (fun x => A (f x)) hA.contMDiffAt
      (fun i x => mfderiv I I f x (V i x)) hdf
  apply hev.congr_of_eventuallyEq
  filter_upwards [(coordinateFrameSet_open (I := I) x₀).mem_nhds
    (coordinateFrameAt_mem (I := I) x₀)] with x hx
  rw [continuousMultilinearMap_basis_repr]
  change diffeomorphTensorPullbackAt f s x (A (f x))
      (fun i => (trivializationAt E (TangentSpace I) x₀).symmL ℝ x (b (σ i))) = _
  rw [diffeomorphTensorPullbackAt_apply]
  congr 1
  funext i
  congr 1
  have hxsource : x ∈ (chartAt H x₀).source := by
    simpa [coordinateFrameSet, coordinateTrivializationAt] using hx
  rw [show V i x = coordinateFrameAt (I := I) x₀ (σ i) x from rfl,
    coordinateFrameAt_apply_of_mem (I := I) hx (σ i)]
  exact congrArg (fun L : E →L[ℝ] TangentSpace I x => L (b (σ i)))
    (TangentBundle.symmL_trivializationAt (I := I) (𝕜 := ℝ) hxsource)

/-- Pullback of a smooth covariant tensor by the actual derivative of a diffeomorphism. -/
def diffeomorphTensorPullback (f : M ≃ₘ⟮I, I⟯ M) {s : ℕ}
    (A : Tensor0SField (𝕜 := ℝ) (I := I) (M := M) (n := ∞) s) :
    Tensor0SField (𝕜 := ℝ) (I := I) (M := M) (n := ∞) s :=
  ⟨fun x => diffeomorphTensorPullbackAt f s x (A (f x)),
    diffeomorphTensorPullback_smooth f A⟩

@[simp]
theorem diffeomorphTensorPullback_apply (f : M ≃ₘ⟮I, I⟯ M) {s : ℕ}
    (A : Tensor0SField (𝕜 := ℝ) (I := I) (M := M) (n := ∞) s)
    (x : M) (v : Fin s → TangentSpace I x) :
    diffeomorphTensorPullback f A x v = A (f x) (fun i => mfderiv I I f x (v i)) :=
  diffeomorphTensorPullbackAt_apply f s x (A (f x)) v

theorem diffeomorphTensorPullback_add (f : M ≃ₘ⟮I, I⟯ M) {s : ℕ}
    (A B : Tensor0SField (𝕜 := ℝ) (I := I) (M := M) (n := ∞) s) :
    diffeomorphTensorPullback f (A + B) =
      diffeomorphTensorPullback f A + diffeomorphTensorPullback f B := by
  refine DFunLike.ext _ _ fun x => ?_
  exact (diffeomorphTensorPullbackAt f s x).map_add (A (f x)) (B (f x))

theorem diffeomorphTensorPullback_smul (f : M ≃ₘ⟮I, I⟯ M) {s : ℕ} (c : ℝ)
    (A : Tensor0SField (𝕜 := ℝ) (I := I) (M := M) (n := ∞) s) :
    diffeomorphTensorPullback f (c • A) = c • diffeomorphTensorPullback f A := by
  refine DFunLike.ext _ _ fun x => ?_
  exact (diffeomorphTensorPullbackAt f s x).map_smul c (A (f x))

@[simp]
theorem diffeomorphTensorPullback_refl {s : ℕ}
    (A : Tensor0SField (𝕜 := ℝ) (I := I) (M := M) (n := ∞) s) :
    diffeomorphTensorPullback (_root_.Diffeomorph.refl I M ∞) A = A := by
  refine DFunLike.ext _ _ fun x => ?_
  ext slots
  rw [diffeomorphTensorPullback_apply]
  change A x (fun i => mfderiv I I (id : M → M) x (slots i)) = A x slots
  rw [mfderiv_id]
  rfl

/-- Tensor pullback reverses the order of composition of diffeomorphisms. -/
theorem diffeomorphTensorPullback_trans (f g : M ≃ₘ⟮I, I⟯ M) {s : ℕ}
    (A : Tensor0SField (𝕜 := ℝ) (I := I) (M := M) (n := ∞) s) :
    diffeomorphTensorPullback (f.trans g) A =
      diffeomorphTensorPullback f (diffeomorphTensorPullback g A) := by
  refine DFunLike.ext _ _ fun x => ?_
  ext slots
  simp only [diffeomorphTensorPullback_apply]
  have hchain : mfderiv I I (f.trans g : M → M) x =
      (mfderiv I I g (f x)).comp (mfderiv I I f x) :=
    mfderiv_comp x (g.mdifferentiable (by simp) (f x)) (f.mdifferentiable (by simp) x)
  change A (g (f x)) (fun i => mfderiv I I (f.trans g : M → M) x (slots i)) = _
  rw [hchain]
  rfl

@[simp]
theorem diffeomorphTensorPullback_symm_apply (f : M ≃ₘ⟮I, I⟯ M) {s : ℕ}
    (A : Tensor0SField (𝕜 := ℝ) (I := I) (M := M) (n := ∞) s) :
    diffeomorphTensorPullback f.symm (diffeomorphTensorPullback f A) = A := by
  rw [← diffeomorphTensorPullback_trans, f.symm_trans_self, diffeomorphTensorPullback_refl]

@[simp]
theorem diffeomorphTensorPullback_apply_symm (f : M ≃ₘ⟮I, I⟯ M) {s : ℕ}
    (A : Tensor0SField (𝕜 := ℝ) (I := I) (M := M) (n := ∞) s) :
    diffeomorphTensorPullback f (diffeomorphTensorPullback f.symm A) = A := by
  rw [← diffeomorphTensorPullback_trans, f.self_trans_symm, diffeomorphTensorPullback_refl]

variable [T2Space M]

private theorem metricNabla0S_diffeomorphTensorPullback_sections
    (g : SmoothRiemannianMetric I M) (f : M ≃ₘ⟮I, I⟯ M) {s : ℕ}
    (A : Tensor0SField (𝕜 := ℝ) (I := I) (M := M) (n := ∞) s)
    (X : ContMDiffSection I E ∞ (TangentSpace I : M → Type _))
    (V : Fin s → ContMDiffSection I E ∞ (TangentSpace I : M → Type _)) (x : M) :
    metricNabla0S (Diffeomorph.pullbackMetric g f) (diffeomorphTensorPullback f A) x
        (Fin.cons (X x) (fun i => V i x)) =
      metricNabla0S g A (f x)
        (Fin.cons (mfderiv I I f x (X x)) (fun i => mfderiv I I f x (V i x))) := by
  classical
  let F : M → ℝ := fun y => A y (fun i => pushFwdSection f (V i) y)
  have hF : ContMDiff I 𝓘(ℝ, ℝ) ∞ F :=
    TensorMultilinear.contMDiff_tensor0SField_apply A (fun i => pushFwdSection f (V i))
  have hscalar : (fun y => diffeomorphTensorPullback f A y (fun i => V i y)) = F ∘ f := by
    funext y
    simp only [diffeomorphTensorPullback_apply, F, Function.comp_apply,
      pushFwdSection_apply_at_image]
  have hleft := (canonicalDerivatives_first (Diffeomorph.pullbackMetric g f)
    (diffeomorphTensorPullback f A)).eval_smooth_slots X V x
  have hright := (canonicalDerivatives_first g A).eval_smooth_slots
    (pushFwdSection f X) (fun i => pushFwdSection f (V i)) (f x)
  simp only [pushFwdSection_apply_at_image] at hright
  rw [hleft, hscalar, mvfderiv_comp_apply x (hF.mdifferentiable (by simp) (f x))
    (f.mdifferentiable (by simp) x) (X x), hright]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [diffeomorphTensorPullback_apply]
  congr 1
  funext j
  by_cases hji : j = i
  · subst j
    simp only [Function.update_self]
    exact metricCov_pullback g f (V i) x (X x)
  · simp only [Function.update_of_ne hji]

/-- Metric covariant differentiation intertwines the genuine diffeomorphism pullback. -/
theorem metricNabla0S_diffeomorphTensorPullback
    (g : SmoothRiemannianMetric I M) (f : M ≃ₘ⟮I, I⟯ M) {s : ℕ}
    (A : Tensor0SField (𝕜 := ℝ) (I := I) (M := M) (n := ∞) s) :
    metricNabla0S (Diffeomorph.pullbackMetric g f) (diffeomorphTensorPullback f A) =
      diffeomorphTensorPullback f (metricNabla0S g A) := by
  classical
  refine DFunLike.ext _ _ fun x => ?_
  ext slots
  obtain ⟨X, hX⟩ := ContMDiffSection.exists_eq_at
    (I := I) (F := E) (V := TangentSpace I) (n := (⊤ : ℕ∞)) x (slots 0)
  choose V hV using fun i : Fin s => ContMDiffSection.exists_eq_at
    (I := I) (F := E) (V := TangentSpace I) (n := (⊤ : ℕ∞)) x (slots i.succ)
  have hslots : Fin.cons (X x) (fun i => V i x) = slots := by
    funext i
    exact Fin.cases hX hV i
  rw [← hslots, diffeomorphTensorPullback_apply]
  have hcons : (fun i : Fin (s + 1) =>
      mfderiv I I f x ((Fin.cons (X x) (fun j => V j x) :
        Fin (s + 1) → TangentSpace I x) i)) =
      Fin.cons (mfderiv I I f x (X x)) (fun i => mfderiv I I f x (V i x)) := by
    funext i
    exact Fin.cases rfl (fun _ => rfl) i
  rw [hcons]
  exact metricNabla0S_diffeomorphTensorPullback_sections g f A X V x

/-- The genuine second metric derivative also intertwines pullback. -/
theorem metricNabla0S_twice_diffeomorphTensorPullback
    (g : SmoothRiemannianMetric I M) (f : M ≃ₘ⟮I, I⟯ M) {s : ℕ}
    (A : Tensor0SField (𝕜 := ℝ) (I := I) (M := M) (n := ∞) s) :
    metricNabla0S (Diffeomorph.pullbackMetric g f)
        (metricNabla0S (Diffeomorph.pullbackMetric g f) (diffeomorphTensorPullback f A)) =
      diffeomorphTensorPullback f (metricNabla0S g (metricNabla0S g A)) := by
  rw [metricNabla0S_diffeomorphTensorPullback, metricNabla0S_diffeomorphTensorPullback]

private theorem inner0S_diffeomorphTensorPullbackAt
    (g : SmoothRiemannianMetric I M) (f : M ≃ₘ⟮I, I⟯ M) (s : ℕ) (x : M)
    (A B : Tensor0SSpace (I := I) s (f x)) :
    inner0S (Diffeomorph.pullbackMetric g f) x s
        (diffeomorphTensorPullbackAt f s x A) (diffeomorphTensorPullbackAt f s x B) =
      inner0S g (f x) s A B := by
  apply inner0S_tensor0SPullbackCLE
  intro u v
  exact (Diffeomorph.pullbackMetric_inner g f x u v).symm

/-- Tensor norms are preserved when the metric and tensor are pulled back together. -/
theorem normSq0S_diffeomorphTensorPullback
    (g : SmoothRiemannianMetric I M) (f : M ≃ₘ⟮I, I⟯ M) {s : ℕ}
    (A : Tensor0SField (𝕜 := ℝ) (I := I) (M := M) (n := ∞) s) (x : M) :
    normSq0S (Diffeomorph.pullbackMetric g f) x s (diffeomorphTensorPullback f A x) =
      normSq0S g (f x) s (A (f x)) :=
  inner0S_diffeomorphTensorPullbackAt g f s x (A (f x)) (A (f x))

private theorem metricTensor0S_diffeomorphTensorPullbackAt
    (g : SmoothRiemannianMetric I M) (f : M ≃ₘ⟮I, I⟯ M) (x : M) :
    metricTensor0S (Diffeomorph.pullbackMetric g f) x =
      diffeomorphTensorPullbackAt f 2 x (metricTensor0S g (f x)) := by
  ext slots
  rw [diffeomorphTensorPullbackAt_apply, metricTensor0S_apply, metricTensor0S_apply]
  exact Diffeomorph.pullbackMetric_inner g f x (slots 0) (slots 1)

private theorem metricTracePair0SAt_diffeomorphTensorPullbackAt
    (g : SmoothRiemannianMetric I M) (f : M ≃ₘ⟮I, I⟯ M) (x : M)
    (A : Tensor0SSpace (I := I) 2 (f x)) :
    metricTracePair0SAt (Diffeomorph.pullbackMetric g f)
        (diffeomorphTensorPullbackAt f 2 x A) = metricTracePair0SAt g A := by
  unfold metricTracePair0SAt
  rw [metricTensor0S_diffeomorphTensorPullbackAt, inner0S_diffeomorphTensorPullbackAt]

private theorem metricTraceFirstTwo0SAt_diffeomorphTensorPullbackAt
    (g : SmoothRiemannianMetric I M) (f : M ≃ₘ⟮I, I⟯ M) {s : ℕ} (x : M)
    (A : Tensor0SSpace (I := I) (s + 2) (f x)) (tail : Fin s → TangentSpace I x) :
    metricTraceFirstTwo0SAt (Diffeomorph.pullbackMetric g f)
        (diffeomorphTensorPullbackAt f (s + 2) x A) tail =
      metricTraceFirstTwo0SAt g A (fun i => mfderiv I I f x (tail i)) := by
  have hfreeze : freezeFirstTwo0S (diffeomorphTensorPullbackAt f (s + 2) x A) tail =
      diffeomorphTensorPullbackAt f 2 x
        (freezeFirstTwo0S A (fun i => mfderiv I I f x (tail i))) := by
    ext v
    have hv : v = vec2 (v 0) (v 1) := by
      funext i
      fin_cases i <;> rfl
    rw [hv, freezeFirstTwo0S_apply, diffeomorphTensorPullbackAt_apply,
      diffeomorphTensorPullbackAt_apply]
    have hvec : (fun i => mfderiv I I f x (vec2 (v 0) (v 1) i)) =
        vec2 (mfderiv I I f x (v 0)) (mfderiv I I f x (v 1)) := by
      funext i
      fin_cases i <;> rfl
    rw [hvec, freezeFirstTwo0S_apply]
    congr 1
    funext i
    exact Fin.cases rfl (fun j => Fin.cases rfl (fun _ => rfl) j) i
  unfold metricTraceFirstTwo0SAt
  rw [hfreeze, metricTracePair0SAt_diffeomorphTensorPullbackAt]

/-- The rough Laplacian intertwines the genuine tensor and metric pullbacks. -/
theorem roughLap0SField_diffeomorphTensorPullback
    (g : SmoothRiemannianMetric I M) (f : M ≃ₘ⟮I, I⟯ M) {s : ℕ}
    (A : Tensor0SField (𝕜 := ℝ) (I := I) (M := M) (n := ∞) s) :
    roughLap0SField (Diffeomorph.pullbackMetric g f) (diffeomorphTensorPullback f A) =
      diffeomorphTensorPullback f (roughLap0SField g A) := by
  refine DFunLike.ext _ _ fun x => ?_
  ext slots
  rw [roughLap0SField_apply, metricNabla0S_twice_diffeomorphTensorPullback,
    diffeomorphTensorPullback_apply, roughLap0SField_apply,
    roughLap0STensor_apply, roughLap0STensor_apply]
  exact metricTraceFirstTwo0SAt_diffeomorphTensorPullbackAt g f x
    (metricNabla0S g (metricNabla0S g A) (f x)) slots

omit [T2Space M] in
private theorem diffeomorphTensorPullbackAt_domDomCongr
    (f : M ≃ₘ⟮I, I⟯ M) (s : ℕ) (x : M)
    (A : Tensor0SSpace (I := I) s (f x)) (e : Equiv.Perm (Fin s)) :
    diffeomorphTensorPullbackAt f s x (A.domDomCongr e) =
      (diffeomorphTensorPullbackAt f s x A).domDomCongr e := by
  ext v
  rfl

/-- The trace-free symmetric projection commutes with metric and tensor pullback. -/
theorem ahlforsPart_diffeomorphTensorPullback
    (g : SmoothRiemannianMetric I M) (f : M ≃ₘ⟮I, I⟯ M)
    (A : Tensor0SField (𝕜 := ℝ) (I := I) (M := M) (n := ∞) 2) :
    ahlforsPart (Diffeomorph.pullbackMetric g f) (diffeomorphTensorPullback f A) =
      diffeomorphTensorPullback f (ahlforsPart g A) := by
  refine DFunLike.ext _ _ fun x => ?_
  change ahlforsPart (Diffeomorph.pullbackMetric g f) (diffeomorphTensorPullback f A) x =
    diffeomorphTensorPullbackAt f 2 x (ahlforsPart g A (f x))
  rw [ahlforsPart_apply, ahlforsPart_apply, map_sub, map_smul, map_add, map_smul,
    diffeomorphTensorPullbackAt_domDomCongr,
    ← metricTensor0S_diffeomorphTensorPullbackAt]
  have htrace := metricTracePair0SAt_diffeomorphTensorPullbackAt g f x (A (f x))
  change metricTracePair0SAt (Diffeomorph.pullbackMetric g f)
      (diffeomorphTensorPullback f A x) = metricTracePair0SAt g (A (f x)) at htrace
  rw [htrace]
  rfl

section Surface

local notation "𝓡₂" => 𝓘(ℝ, EuclideanSpace ℝ (Fin 2))

variable {S : Type*} [TopologicalSpace S] [ChartedSpace (EuclideanSpace ℝ (Fin 2)) S]
variable [IsManifold 𝓡₂ ∞ S] [T2Space S]

/-- The full four-term dissipation density is natural under smooth diffeomorphisms. -/
theorem oneFormDissipationDensity_diffeomorphTensorPullback
    (g : SmoothRiemannianMetric 𝓡₂ S) (f : S ≃ₘ⟮𝓡₂, 𝓡₂⟯ S)
    (h : OneFormSection (I := 𝓡₂) (M := S)) (x : S) :
    oneFormDissipationDensity (Diffeomorph.pullbackMetric g f)
        (diffeomorphTensorPullback f h) x =
      oneFormDissipationDensity g h (f x) := by
  have hcurv : metricScalarAt (Diffeomorph.pullbackMetric g f) x =
      metricScalarAt g (f x) := by
    rw [← Diffeomorph.pullbackMetricCross_eq_pullbackMetric]
    exact DifferentialGeometry.CheegerGromovCompactness.metricScalar_cross g f x
  simp only [oneFormDissipationDensity, roughLap0SField_diffeomorphTensorPullback,
    metricNabla0S_diffeomorphTensorPullback, ahlforsPart_diffeomorphTensorPullback,
    normSq0S_diffeomorphTensorPullback, hcurv]

/-- Every smooth isometry preserves the full one-form dissipation density. -/
theorem oneFormDissipationDensity_diffeomorphTensorPullback_of_isometry
    (g : SmoothRiemannianMetric 𝓡₂ S) (f : S ≃ₘ⟮𝓡₂, 𝓡₂⟯ S)
    (hf : Diffeomorph.pullbackMetric g f = g)
    (h : OneFormSection (I := 𝓡₂) (M := S)) (x : S) :
    oneFormDissipationDensity g (diffeomorphTensorPullback f h) x =
      oneFormDissipationDensity g h (f x) := by
  simpa only [hf] using oneFormDissipationDensity_diffeomorphTensorPullback g f h x

variable [CompactSpace S]

private local instance : MeasurableSpace S := borel S
private local instance : BorelSpace S := ⟨rfl⟩

/-- The complete one-form action is unchanged by pulling back both metric and form. -/
theorem oneFormDissipation_diffeomorphTensorPullback
    (g : SmoothRiemannianMetric 𝓡₂ S) (f : S ≃ₘ⟮𝓡₂, 𝓡₂⟯ S)
    (h : OneFormSection (I := 𝓡₂) (M := S)) :
    oneFormDissipation (Diffeomorph.pullbackMetric g f) (diffeomorphTensorPullback f h) =
      oneFormDissipation g h := by
  unfold oneFormDissipation
  simp_rw [oneFormDissipationDensity_diffeomorphTensorPullback]
  exact (measurePreserving_riemannianVolume_pullback g f).integral_comp
    f.toHomeomorph.measurableEmbedding _

/-- Every smooth isometry preserves the complete one-form action. -/
theorem oneFormDissipation_diffeomorphTensorPullback_of_isometry
    (g : SmoothRiemannianMetric 𝓡₂ S) (f : S ≃ₘ⟮𝓡₂, 𝓡₂⟯ S)
    (hf : Diffeomorph.pullbackMetric g f = g)
    (h : OneFormSection (I := 𝓡₂) (M := S)) :
    oneFormDissipation g (diffeomorphTensorPullback f h) = oneFormDissipation g h := by
  simpa only [hf] using oneFormDissipation_diffeomorphTensorPullback g f h

/-- Pullback preserves the polarization of the full one-form action. -/
theorem oneFormDissipationPairing_diffeomorphTensorPullback
    (g : SmoothRiemannianMetric 𝓡₂ S) (f : S ≃ₘ⟮𝓡₂, 𝓡₂⟯ S)
    (h k : OneFormSection (I := 𝓡₂) (M := S)) :
    oneFormDissipationPairing (Diffeomorph.pullbackMetric g f)
        (diffeomorphTensorPullback f h) (diffeomorphTensorPullback f k) =
      oneFormDissipationPairing g h k := by
  have hsum := oneFormDissipation_diffeomorphTensorPullback g f (h + k)
  rw [diffeomorphTensorPullback_add, oneFormDissipation_add, oneFormDissipation_add,
    oneFormDissipation_diffeomorphTensorPullback,
    oneFormDissipation_diffeomorphTensorPullback] at hsum
  linarith

/-- The full polarized action is invariant under every smooth isometry. -/
theorem oneFormDissipationPairing_diffeomorphTensorPullback_of_isometry
    (g : SmoothRiemannianMetric 𝓡₂ S) (f : S ≃ₘ⟮𝓡₂, 𝓡₂⟯ S)
    (hf : Diffeomorph.pullbackMetric g f = g)
    (h k : OneFormSection (I := 𝓡₂) (M := S)) :
    oneFormDissipationPairing g
        (diffeomorphTensorPullback f h) (diffeomorphTensorPullback f k) =
      oneFormDissipationPairing g h k := by
  simpa only [hf] using oneFormDissipationPairing_diffeomorphTensorPullback g f h k

end Surface

end RicciFlowSharpEstimate.Geometry
