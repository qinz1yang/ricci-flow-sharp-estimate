/-
Copyright (c) 2026 Ziyang Qin. All rights reserved.
No license is granted by this file.
Authors: Ziyang Qin
-/
import RicciFlowSharpEstimate.Geometry.RotationalStereographic
import RicciFlowSharpEstimate.Geometry.OneFormDissipationNaturality
import RicciFlowSharpEstimate.Analysis.RotationCovectorPlane

/-!
# Smooth invariant one-forms in stereographic coordinates

The actual pullback of an invariant one-form has smooth radial and tangential
coefficients at either pole. This uses stereographic derivatives and the smooth
rotation-equivariant covector theorem, adapting Ziyang Qin's historical invariant
one-form classification.
-/

noncomputable section

namespace RicciFlowSharpEstimate.Geometry

open Bundle DifferentialGeometry DifferentialGeometry.Geometry DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Tensor.RicciIdentity
open RicciFlowSharpEstimate.Analysis
open scoped Manifold ContDiff

private def pullbackEval (f : ℝ × ℝ → RotationalSphere)
    (h : OneFormSection (I := 𝓡 2) (M := RotationalSphere)) (p v : ℝ × ℝ) : ℝ :=
  h (f p) (fun _ : Fin 1 => mfderiv 𝓘(ℝ, ℝ × ℝ) (𝓡 2) f p v)

private theorem pullbackEval_contDiff (f : ℝ × ℝ → RotationalSphere)
    (hf : ContMDiff 𝓘(ℝ, ℝ × ℝ) (𝓡 2) ∞ f)
    (h : OneFormSection (I := 𝓡 2) (M := RotationalSphere)) (v : ℝ × ℝ) :
    ContDiff ℝ ∞ (fun p => pullbackEval f h p v) := by
  rw [← contMDiff_iff_contDiff]
  have hv : ContMDiff 𝓘(ℝ, ℝ × ℝ) (𝓘(ℝ, ℝ × ℝ).prod 𝓘(ℝ, ℝ × ℝ)) ∞
      (fun p => TotalSpace.mk' (ℝ × ℝ) p v :
        (ℝ × ℝ) → TangentBundle 𝓘(ℝ, ℝ × ℝ) (ℝ × ℝ)) := by
    intro p
    apply Bundle.contMDiffAt_totalSpace.mpr
    refine ⟨contMDiffAt_id, ?_⟩
    simpa using (contMDiffAt_const (c := v))
  have hdf := (hf.contMDiff_tangentMap (by simp : (∞ : WithTop ℕ∞) + 1 ≤ ∞)).comp hv
  intro p
  exact TensorMultilinear.contMDiffWithinAt_section_apply_base 1 f hf.contMDiffAt
    (fun p => h (f p)) (h.contMDiff.comp hf).contMDiffAt
    (fun _ p => mfderiv 𝓘(ℝ, ℝ × ℝ) (𝓡 2) f p v) (fun _ => hdf.contMDiffAt)

private theorem oneForm_apply_linearCombination
    (h : OneFormSection (I := 𝓡 2) (M := RotationalSphere)) (x : RotationalSphere)
    (a b : ℝ) (u v : TangentSpace (𝓡 2) x) :
    h x (fun _ : Fin 1 => a • u + b • v) =
      a * h x (fun _ : Fin 1 => u) + b * h x (fun _ : Fin 1 => v) := by
  have hupdate (w : TangentSpace (𝓡 2) x) :
      Function.update (fun _ : Fin 1 => u) 0 w = fun _ : Fin 1 => w := by
    funext i
    fin_cases i
    simp
  have hadd := (h x).map_update_add (fun _ : Fin 1 => u) 0 (a • u) (b • v)
  have ha := (h x).map_update_smul (fun _ : Fin 1 => u) 0 a u
  have hb := (h x).map_update_smul (fun _ : Fin 1 => u) 0 b v
  simp only [hupdate, smul_eq_mul] at ha hb hadd
  rw [ha, hb] at hadd
  exact hadd

private theorem pullbackEval_coordinates (f : ℝ × ℝ → RotationalSphere)
    (h : OneFormSection (I := 𝓡 2) (M := RotationalSphere)) (p v : ℝ × ℝ) :
    pullbackEval f h p v =
      v.1 * pullbackEval f h p (1, 0) + v.2 * pullbackEval f h p (0, 1) := by
  have hv : v = v.1 • (1, 0) + v.2 • (0, 1) := by ext <;> simp
  let L : (ℝ × ℝ) →L[ℝ] TangentSpace (𝓡 2) (f p) :=
    mfderiv 𝓘(ℝ, ℝ × ℝ) (𝓡 2) f p
  change h (f p) (fun _ : Fin 1 => L v) =
    v.1 * h (f p) (fun _ : Fin 1 => L (1, 0)) +
      v.2 * h (f p) (fun _ : Fin 1 => L (0, 1))
  have hlin : L v = v.1 • L (1, 0) + v.2 • L (0, 1) := by
    conv_lhs => rw [hv, map_add, map_smul, map_smul]
  rw [hlin]
  exact oneForm_apply_linearCombination h (f p) v.1 v.2 _ _

private def planeRotationLinear (c s : ℝ) : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ) :=
  (c • ContinuousLinearMap.fst ℝ ℝ ℝ - s • ContinuousLinearMap.snd ℝ ℝ ℝ).prod
    (s • ContinuousLinearMap.fst ℝ ℝ ℝ + c • ContinuousLinearMap.snd ℝ ℝ ℝ)

private theorem planeRotationLinear_apply (c s : ℝ) (p : ℝ × ℝ) :
    planeRotationLinear c s p = planeRotate c s p := by
  simp [planeRotationLinear, planeRotate]

private theorem planeRotate_contMDiff (c s : ℝ) :
    ContMDiff 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, ℝ × ℝ) ∞ (planeRotate c s) := by
  have heq : (planeRotationLinear c s : (ℝ × ℝ) → ℝ × ℝ) = planeRotate c s :=
    funext (planeRotationLinear_apply c s)
  rw [← heq]
  exact (planeRotationLinear c s).contDiff.contMDiff

private theorem planeRotate_mfderiv (c s : ℝ) (p v : ℝ × ℝ) :
    mfderiv 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, ℝ × ℝ) (planeRotate c s) p v =
      planeRotate c s v := by
  have heq : (planeRotationLinear c s : (ℝ × ℝ) → ℝ × ℝ) = planeRotate c s :=
    funext (planeRotationLinear_apply c s)
  rw [← heq, mfderiv_eq_fderiv, (planeRotationLinear c s).fderiv]
  rfl

private theorem pullbackEval_comp_planeRotate (f : ℝ × ℝ → RotationalSphere)
    (hf : ContMDiff 𝓘(ℝ, ℝ × ℝ) (𝓡 2) ∞ f)
    (h : OneFormSection (I := 𝓡 2) (M := RotationalSphere)) (c s : ℝ) (p v : ℝ × ℝ) :
    pullbackEval (f ∘ planeRotate c s) h p v =
      pullbackEval f h (planeRotate c s p) (planeRotate c s v) := by
  unfold pullbackEval
  congr 1
  funext i
  exact (mfderiv_comp_apply p (hf.mdifferentiableAt (by simp))
    ((planeRotate_contMDiff c s).mdifferentiableAt (by simp)) v).trans
      (congrArg (fun w : TangentSpace 𝓘(ℝ, ℝ × ℝ) (planeRotate c s p) =>
        mfderiv 𝓘(ℝ, ℝ × ℝ) (𝓡 2) f (planeRotate c s p) w)
        (planeRotate_mfderiv c s p v))

private theorem pullbackEval_comp_diffeomorph (f : ℝ × ℝ → RotationalSphere)
    (hf : ContMDiff 𝓘(ℝ, ℝ × ℝ) (𝓡 2) ∞ f)
    (h : OneFormSection (I := 𝓡 2) (M := RotationalSphere))
    (g : RotationalSphere ≃ₘ⟮𝓡 2, 𝓡 2⟯ RotationalSphere) (p v : ℝ × ℝ) :
    pullbackEval (g ∘ f) h p v = pullbackEval f (diffeomorphTensorPullback g h) p v := by
  unfold pullbackEval
  rw [diffeomorphTensorPullback_apply]
  congr 1
  funext i
  exact mfderiv_comp_apply p (g.mdifferentiable (by simp) (f p))
    (hf.mdifferentiableAt (by simp)) v

private theorem stereo_pullbackEval_rotation
    (h : OneFormSection (I := 𝓡 2) (M := RotationalSphere))
    (hinv : ∀ z : Circle, diffeomorphTensorPullback (circleSphereDiffeo z) h = h)
    (epsilon : ℝ) (he : epsilon ^ 2 = 1) (z : Circle) (p v : ℝ × ℝ) :
    pullbackEval (stereoPoint epsilon he) h (planeRotate z.1.re z.1.im p)
        (planeRotate z.1.re z.1.im v) = pullbackEval (stereoPoint epsilon he) h p v := by
  have hcomp : stereoPoint epsilon he ∘ planeRotate z.1.re z.1.im =
      circleSphereDiffeo z ∘ stereoPoint epsilon he := by
    funext q
    exact stereoPoint_planeRotate epsilon he z q
  rw [← pullbackEval_comp_planeRotate _ (stereoPoint_contMDiff epsilon he), hcomp,
    pullbackEval_comp_diffeomorph _ (stereoPoint_contMDiff epsilon he), hinv]

private def circleOfUnitPair (c s : ℝ) (hcs : c ^ 2 + s ^ 2 = 1) : Circle :=
  ⟨⟨c, s⟩, by
    change (⟨c, s⟩ : ℂ) ∈ Metric.sphere 0 1
    rw [mem_sphere_zero_iff_norm]
    rw [← sq_eq_sq₀ (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)]
    rw [Complex.sq_norm, Complex.normSq_apply]
    simpa [pow_two] using hcs⟩

private theorem stereo_pullbackEval_isRotationCovectorPair
    (h : OneFormSection (I := 𝓡 2) (M := RotationalSphere))
    (hinv : ∀ z : Circle, diffeomorphTensorPullback (circleSphereDiffeo z) h = h)
    (epsilon : ℝ) (he : epsilon ^ 2 = 1) :
    IsRotationCovectorPair
      (fun p => pullbackEval (stereoPoint epsilon he) h p (1, 0))
      (fun p => pullbackEval (stereoPoint epsilon he) h p (0, 1)) := by
  intro c s hcs p
  have hzero : planeRotate c s (c, -s) = (1, 0) := by
    ext <;> simp [planeRotate] <;> nlinarith [hcs]
  have hone : planeRotate c s (s, c) = (0, 1) := by
    ext <;> simp [planeRotate] <;> nlinarith [hcs]
  have h0 := stereo_pullbackEval_rotation h hinv epsilon he (circleOfUnitPair c s hcs) p (c, -s)
  have h1 := stereo_pullbackEval_rotation h hinv epsilon he (circleOfUnitPair c s hcs) p (s, c)
  change pullbackEval (stereoPoint epsilon he) h (planeRotate c s p) (planeRotate c s (c, -s)) =
    pullbackEval (stereoPoint epsilon he) h p (c, -s) at h0
  change pullbackEval (stereoPoint epsilon he) h (planeRotate c s p) (planeRotate c s (s, c)) =
    pullbackEval (stereoPoint epsilon he) h p (s, c) at h1
  rw [hzero] at h0
  rw [hone] at h1
  constructor
  · calc
      _ = pullbackEval (stereoPoint epsilon he) h p (c, -s) := h0
      _ = _ := by rw [pullbackEval_coordinates]; simp [sub_eq_add_neg]
  · calc
      _ = pullbackEval (stereoPoint epsilon he) h p (s, c) := h1
      _ = _ := pullbackEval_coordinates _ h p (s, c)

/-- The genuine stereographic pullback of a smooth invariant one-form has smooth
radial and tangential coefficients depending only on squared radius, including at the pole. -/
theorem exists_smooth_stereographic_coefficients
    (h : OneFormSection (I := 𝓡 2) (M := RotationalSphere))
    (hinv : ∀ z : Circle, diffeomorphTensorPullback (circleSphereDiffeo z) h = h)
    (epsilon : ℝ) (he : epsilon ^ 2 = 1) :
    ∃ A B : ℝ → ℝ, ContDiff ℝ ∞ A ∧ ContDiff ℝ ∞ B ∧
      ∀ p v : ℝ × ℝ,
        h (stereoPoint epsilon he p) (fun _ : Fin 1 =>
          mfderiv 𝓘(ℝ, ℝ × ℝ) (𝓡 2) (stereoPoint epsilon he) p v) =
          A (p.1 ^ 2 + p.2 ^ 2) * (p.1 * v.1 + p.2 * v.2) +
            B (p.1 ^ 2 + p.2 ^ 2) * (p.1 * v.2 - p.2 * v.1) := by
  obtain ⟨A, B, hA, hB, hab⟩ := exists_smooth_radial_tangential_coefficients
    (fun p => pullbackEval (stereoPoint epsilon he) h p (1, 0))
    (fun p => pullbackEval (stereoPoint epsilon he) h p (0, 1))
    (pullbackEval_contDiff _ (stereoPoint_contMDiff epsilon he) h (1, 0))
    (pullbackEval_contDiff _ (stereoPoint_contMDiff epsilon he) h (0, 1))
    (stereo_pullbackEval_isRotationCovectorPair h hinv epsilon he)
  refine ⟨A, B, hA, hB, ?_⟩
  intro p v
  change pullbackEval (stereoPoint epsilon he) h p v = _
  rw [pullbackEval_coordinates, (hab p.1 p.2).1, (hab p.1 p.2).2]
  ring

end RicciFlowSharpEstimate.Geometry
