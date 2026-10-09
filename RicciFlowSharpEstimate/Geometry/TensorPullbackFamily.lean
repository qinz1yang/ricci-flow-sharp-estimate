/-
Copyright (c) 2026 Ziyang Qin. All rights reserved.
No license is granted by this file.
Authors: Ziyang Qin
-/
import RicciFlowSharpEstimate.Geometry.OneFormDissipationNaturality
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# Smooth families of covariant tensor pullbacks

Joint smoothness of a family of diffeomorphisms implies joint smoothness of the
actual derivative pullbacks of every smooth covariant tensor field.
-/

noncomputable section

namespace RicciFlowSharpEstimate.Geometry

open Bundle DifferentialGeometry DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Tensor.Multilinear DifferentialGeometry.Tensor.Coordinates
open scoped Manifold ContDiff Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable {EP : Type*} [NormedAddCommGroup EP] [NormedSpace ℝ EP]
variable {HP : Type*} [TopologicalSpace HP] {IP : ModelWithCorners ℝ EP HP}
variable {P : Type*} [TopologicalSpace P] [ChartedSpace HP P] [IsManifold IP ∞ P]

omit [IsManifold I ∞ M] [IsManifold IP ∞ P] in
/-- Restricting the derivative of a joint family to the manifold direction gives
its fixed-parameter derivative. -/
theorem mfderiv_family_zero_parameter (f : P → M ≃ₘ⟮I, I⟯ M)
    (hf : ContMDiff (IP.prod I) I ∞ (fun p : P × M => f p.1 p.2))
    (t : P) (x : M) (v : TangentSpace I x) :
    mfderiv (IP.prod I) I (fun p : P × M => f p.1 p.2) (t, x) (0, v) =
      mfderiv I I (f t) x v := by
  have hslice : ContMDiff I (IP.prod I) ∞ (fun y : M => (t, y)) :=
    contMDiff_const.prodMk contMDiff_id
  have hc := tangentMap_comp_at
    (I := I) (I' := IP.prod I) (I'' := I)
    (f := fun y : M => (t, y)) (g := fun p : P × M => f p.1 p.2)
    (⟨x, v⟩ : TangentBundle I M)
    (hf.mdifferentiableAt (by simp)) (hslice.mdifferentiableAt (by simp))
  rw [tangentMap_prod_right] at hc
  exact (congrArg TotalSpace.snd hc).symm

private theorem contMDiffAt_mfderiv_family_apply
    (f : P → M ≃ₘ⟮I, I⟯ M)
    (hf : ContMDiff (IP.prod I) I ∞ (fun p : P × M => f p.1 p.2))
    (V : (p : P × M) → TangentSpace I p.2) {p₀ : P × M}
    (hV : ContMDiffAt (IP.prod I) (I.prod 𝓘(ℝ, E)) ∞
      (fun p => TotalSpace.mk' E p.2 (V p)) p₀) :
    ContMDiffAt (IP.prod I) (I.prod 𝓘(ℝ, E)) ∞
      (fun p => TotalSpace.mk' E (f p.1 p.2)
        (mfderiv I I (f p.1) p.2 (V p))) p₀ := by
  have hz : ContMDiffAt (IP.prod I) (IP.tangent) ∞
      (fun p : P × M => TotalSpace.mk' EP p.1 (0 : TangentSpace IP p.1)) p₀ :=
    ((Bundle.contMDiff_zeroSection ℝ (TangentSpace IP : P → Type _)).comp
      contMDiff_fst).contMDiffAt
  have hlift : ContMDiffAt (IP.prod I) ((IP.prod I).tangent) ∞
      (fun p : P × M => (⟨p, (0, V p)⟩ : TangentBundle (IP.prod I) (P × M))) p₀ :=
    contMDiff_equivTangentBundleProd_symm.contMDiffAt.comp p₀ (hz.prodMk hV)
  have hder := (hf.contMDiff_tangentMap (m := ∞) (by simp)).contMDiffAt.comp p₀ hlift
  convert hder using 1
  funext p
  change TotalSpace.mk' E _ _ = TotalSpace.mk' E _ _
  congr 1
  exact (mfderiv_family_zero_parameter f hf p.1 p.2 (V p)).symm

/-- Applying the actual derivative of a jointly smooth family to a smooth
source vector field is jointly smooth. -/
theorem contMDiff_mfderiv_family_apply
    (f : P → M ≃ₘ⟮I, I⟯ M)
    (hf : ContMDiff (IP.prod I) I ∞ (fun p : P × M => f p.1 p.2))
    (V : (p : P × M) → TangentSpace I p.2)
    (hV : ContMDiff (IP.prod I) (I.prod 𝓘(ℝ, E)) ∞
      (fun p => TotalSpace.mk' E p.2 (V p))) :
    ContMDiff (IP.prod I) (I.prod 𝓘(ℝ, E)) ∞
      (fun p => TotalSpace.mk' E (f p.1 p.2)
        (mfderiv I I (f p.1) p.2 (V p))) :=
  fun _ => contMDiffAt_mfderiv_family_apply f hf V hV.contMDiffAt

variable [FiniteDimensional ℝ E]

/-- Pullback by the actual derivatives of a jointly smooth diffeomorphism
family is jointly smooth as a map to the covariant tensor bundle. -/
theorem contMDiff_diffeomorphTensorPullback_family
    (f : P → M ≃ₘ⟮I, I⟯ M)
    (hf : ContMDiff (IP.prod I) I ∞ (fun p : P × M => f p.1 p.2)) {s : ℕ}
    (A : Tensor0SField (𝕜 := ℝ) (I := I) (M := M) (n := ∞) s) :
    ContMDiff (IP.prod I) (I.prod 𝓘(ℝ, Tensor0SModel s ℝ E)) ∞
      (fun p : P × M => TotalSpace.mk' (Tensor0SModel s ℝ E) p.2
        (diffeomorphTensorPullback (f p.1) A p.2)) := by
  intro p₀
  apply Bundle.contMDiffAt_totalSpace.mpr
  refine ⟨contMDiffAt_snd, ?_⟩
  let b := Module.finBasis ℝ E
  let B := Tensor.Multilinear.continuousMultilinearMapBasis b s
  let g := fun p : P × M =>
    (trivializationAt (Tensor0SModel s ℝ E)
      (fun x : M => Tensor0SSpace (I := I) s x) p₀.2
      ⟨p.2, diffeomorphTensorPullback (f p.1) A p.2⟩).2
  change ContMDiffAt (IP.prod I) 𝓘(ℝ, Tensor0SModel s ℝ E) ∞ g p₀
  rw [show g = fun p => B.equivFun.symm (B.equivFun (g p)) from
    funext fun p => (B.equivFun.symm_apply_apply (g p)).symm]
  apply B.equivFun.symm.toContinuousLinearEquiv.toContinuousLinearMap.contMDiffAt.comp p₀
  apply contMDiffAt_pi_space.mpr
  intro σ
  let V : Fin s → (p : P × M) → TangentSpace I p.2 :=
    fun i p => coordinateFrameAt (I := I) p₀.2 (σ i) p.2
  have hV (i : Fin s) : ContMDiffAt (IP.prod I) (I.prod 𝓘(ℝ, E)) ∞
      (fun p => TotalSpace.mk' E p.2 (V i p)) p₀ :=
    ((coordinateFrameAt_isLocalFrame (I := I) p₀.2).contMDiffAt
      (coordinateFrameSet_open (I := I) p₀.2)
      (coordinateFrameAt_mem (I := I) p₀.2) (σ i)).comp p₀ contMDiffAt_snd
  have hdf (i : Fin s) := contMDiffAt_mfderiv_family_apply f hf (V i) (hV i)
  have hA := A.contMDiff.comp hf
  have hev : ContMDiffAt (IP.prod I) 𝓘(ℝ, ℝ) ∞
      (fun p : P × M => A (f p.1 p.2)
        (fun i => mfderiv I I (f p.1) p.2 (V i p))) p₀ :=
    TensorMultilinear.contMDiffWithinAt_section_apply_base s
      (fun p : P × M => f p.1 p.2) hf.contMDiffAt
      (fun p => A (f p.1 p.2)) hA.contMDiffAt
      (fun i p => mfderiv I I (f p.1) p.2 (V i p)) hdf
  apply hev.congr_of_eventuallyEq
  have hU : {p : P × M | p.2 ∈ coordinateFrameSet (I := I) p₀.2} ∈ 𝓝 p₀ :=
    continuous_snd.continuousAt.preimage_mem_nhds
      ((coordinateFrameSet_open (I := I) p₀.2).mem_nhds
        (coordinateFrameAt_mem (I := I) p₀.2))
  filter_upwards [hU] with p hp
  change (Tensor.Multilinear.continuousMultilinearMapBasis b s).repr (g p) σ = _
  rw [continuousMultilinearMap_basis_repr]
  change diffeomorphTensorPullback (f p.1) A p.2
      (fun i => (trivializationAt E (TangentSpace I) p₀.2).symmL ℝ p.2 (b (σ i))) = _
  rw [diffeomorphTensorPullback_apply]
  congr 1
  funext i
  congr 1
  have hpsource : p.2 ∈ (chartAt H p₀.2).source := by
    simpa [coordinateFrameSet, coordinateTrivializationAt] using hp
  rw [show V i p = coordinateFrameAt (I := I) p₀.2 (σ i) p.2 from rfl,
    coordinateFrameAt_apply_of_mem (I := I) hp (σ i)]
  exact congrArg (fun L : E →L[ℝ] TangentSpace I p.2 => L (b (σ i)))
    (TangentBundle.symmL_trivializationAt (I := I) (𝕜 := ℝ) hpsource)

/-- Evaluation of a pullback family against jointly smooth source vectors is
jointly smooth. -/
theorem contMDiff_diffeomorphTensorPullback_family_apply
    (f : P → M ≃ₘ⟮I, I⟯ M)
    (hf : ContMDiff (IP.prod I) I ∞ (fun p : P × M => f p.1 p.2)) {s : ℕ}
    (A : Tensor0SField (𝕜 := ℝ) (I := I) (M := M) (n := ∞) s)
    (V : Fin s → (p : P × M) → TangentSpace I p.2)
    (hV : ∀ i, ContMDiff (IP.prod I) (I.prod 𝓘(ℝ, E)) ∞
      (fun p => TotalSpace.mk' E p.2 (V i p))) :
    ContMDiff (IP.prod I) 𝓘(ℝ, ℝ) ∞
      (fun p : P × M => diffeomorphTensorPullback (f p.1) A p.2 (fun i => V i p)) := by
  intro p₀
  exact TensorMultilinear.contMDiffWithinAt_section_apply_base s Prod.snd contMDiffAt_snd
    (fun p => diffeomorphTensorPullback (f p.1) A p.2)
    (contMDiff_diffeomorphTensorPullback_family f hf A).contMDiffAt V
    (fun i => (hV i).contMDiffAt)

/-- Evaluation against arbitrary smooth vector fields on the source manifold
is jointly smooth in the parameter and base point. -/
theorem contMDiff_diffeomorphTensorPullback_family_apply_sections
    (f : P → M ≃ₘ⟮I, I⟯ M)
    (hf : ContMDiff (IP.prod I) I ∞ (fun p : P × M => f p.1 p.2)) {s : ℕ}
    (A : Tensor0SField (𝕜 := ℝ) (I := I) (M := M) (n := ∞) s)
    (V : Fin s → ContMDiffSection I E ∞ (TangentSpace I : M → Type _)) :
    ContMDiff (IP.prod I) 𝓘(ℝ, ℝ) ∞
      (fun p : P × M => diffeomorphTensorPullback (f p.1) A p.2 (fun i => V i p.2)) :=
  contMDiff_diffeomorphTensorPullback_family_apply f hf A
    (fun i p => V i p.2) (fun i => (V i).contMDiff.comp contMDiff_snd)

/-- At each fixed base point the tensor pullbacks depend continuously on the
parameter in the native tensor fiber. -/
theorem continuous_diffeomorphTensorPullback_family_at
    (f : P → M ≃ₘ⟮I, I⟯ M)
    (hf : ContMDiff (IP.prod I) I ∞ (fun p : P × M => f p.1 p.2)) {s : ℕ}
    (A : Tensor0SField (𝕜 := ℝ) (I := I) (M := M) (n := ∞) s) (x : M) :
    Continuous (fun t => diffeomorphTensorPullback (f t) A x) := by
  apply (FiberBundle.totalSpaceMk_isInducing (Tensor0SModel s ℝ E)
    (fun y : M => Tensor0SSpace (I := I) s y) x).continuous_iff.mpr
  exact (contMDiff_diffeomorphTensorPullback_family f hf A).continuous.comp
    (continuous_id.prodMk continuous_const)

/-- Evaluation of a fixed-fiber pullback on any fixed tensor slots is continuous
in the parameter. -/
theorem continuous_diffeomorphTensorPullback_family_eval
    (f : P → M ≃ₘ⟮I, I⟯ M)
    (hf : ContMDiff (IP.prod I) I ∞ (fun p : P × M => f p.1 p.2)) {s : ℕ}
    (A : Tensor0SField (𝕜 := ℝ) (I := I) (M := M) (n := ∞) s)
    (x : M) (v : Fin s → TangentSpace I x) :
    Continuous (fun t => diffeomorphTensorPullback (f t) A x v) :=
  TensorMultilinear.continuous_section_apply_base (fun _ : P => x) continuous_const
    (fun t => diffeomorphTensorPullback (f t) A x)
    ((contMDiff_diffeomorphTensorPullback_family f hf A).continuous.comp
      (continuous_id.prodMk continuous_const))
    (fun i _ => v i) (fun _ => continuous_const)

/-- Fixed-vector evaluations of real-parameter tensor pullbacks are integrable
on every compact interval. -/
theorem intervalIntegrable_diffeomorphTensorPullback_family_eval
    (f : ℝ → M ≃ₘ⟮I, I⟯ M)
    (hf : ContMDiff (𝓘(ℝ, ℝ).prod I) I ∞ (fun p : ℝ × M => f p.1 p.2)) {s : ℕ}
    (A : Tensor0SField (𝕜 := ℝ) (I := I) (M := M) (n := ∞) s)
    (x : M) (v : Fin s → TangentSpace I x)
    (μ : MeasureTheory.Measure ℝ) [MeasureTheory.IsLocallyFiniteMeasure μ] (a b : ℝ) :
    IntervalIntegrable (fun t => diffeomorphTensorPullback (f t) A x v) μ a b :=
  (continuous_diffeomorphTensorPullback_family_eval f hf A x v).intervalIntegrable a b

end RicciFlowSharpEstimate.Geometry
