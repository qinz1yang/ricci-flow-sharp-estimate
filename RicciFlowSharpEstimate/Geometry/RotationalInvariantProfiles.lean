/-
Copyright (c) 2026 Ziyang Qin. All rights reserved.
No license is granted by this file.
Authors: Ziyang Qin
-/
import RicciFlowSharpEstimate.Geometry.RotationalInvariantPoleForms
import Mathlib.Analysis.SpecialFunctions.SmoothTransition

/-!
# Smooth height profiles of invariant sphere one-forms

An actual smooth one-form fixed by every circle pullback has a global smooth
normal form `P(z) dz + Q(z) κ`. Signed stereographic coordinates give smooth
profiles through each pole; positive safe denominators and a height cutoff glue
them to globally smooth real functions. No metric or extra pole hypothesis enters.

The cutoff construction adapts Ziyang Qin's historical
`RotationalInvariantOneFormClassification.lean`.
-/

noncomputable section

namespace RicciFlowSharpEstimate.Geometry

open DifferentialGeometry DifferentialGeometry.Geometry DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Geometry.Operator DifferentialGeometry.Tensor.RicciIdentity
open scoped Manifold ContDiff

local instance : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 2 + 1) :=
  ⟨finrank_euclideanSpace_fin⟩

private def safeHeightDenominator (v : ℝ) : ℝ :=
  1 + Real.smoothTransition (4 * v + 3) * v

private theorem safeHeightDenominator_contDiff :
    ContDiff ℝ (⊤ : ℕ∞) safeHeightDenominator := by
  exact contDiff_const.add
    ((Real.smoothTransition.contDiff.comp (by fun_prop)).mul contDiff_id)

private theorem safeHeightDenominator_pos (v : ℝ) :
    0 < safeHeightDenominator v := by
  by_cases hv : v ≤ -(3 / 4 : ℝ)
  · have hc : Real.smoothTransition (4 * v + 3) = 0 :=
      Real.smoothTransition.zero_of_nonpos (by linarith)
    simp [safeHeightDenominator, hc]
  · have hv' : -(3 / 4 : ℝ) < v := lt_of_not_ge hv
    by_cases hv0 : 0 ≤ v
    · have hc0 := Real.smoothTransition.nonneg (4 * v + 3)
      dsimp only [safeHeightDenominator]
      nlinarith [mul_nonneg hc0 hv0]
    · have hvneg : v < 0 := lt_of_not_ge hv0
      have hc1 := Real.smoothTransition.le_one (4 * v + 3)
      have hmul : v ≤ Real.smoothTransition (4 * v + 3) * v := by
        simpa using mul_le_mul_of_nonpos_right hc1 hvneg.le
      dsimp only [safeHeightDenominator]
      linarith

private theorem safeHeightDenominator_eq {v : ℝ} (hv : -(1 / 2 : ℝ) ≤ v) :
    safeHeightDenominator v = 1 + v := by
  have hc : Real.smoothTransition (4 * v + 3) = 1 :=
    Real.smoothTransition.one_of_one_le (by linarith)
  simp [safeHeightDenominator, hc]

private def localHeightProfile (k epsilon : ℝ) (A : ℝ → ℝ) (v : ℝ) : ℝ :=
  k * A (4 * (1 - epsilon * v) / safeHeightDenominator (epsilon * v)) /
    safeHeightDenominator (epsilon * v) ^ 2

private theorem localHeightProfile_contDiff (k epsilon : ℝ) (A : ℝ → ℝ)
    (hA : ContDiff ℝ (⊤ : ℕ∞) A) :
    ContDiff ℝ (⊤ : ℕ∞) (localHeightProfile k epsilon A) := by
  have hd : ContDiff ℝ (⊤ : ℕ∞) (fun v => safeHeightDenominator (epsilon * v)) :=
    safeHeightDenominator_contDiff.comp (contDiff_const.mul contDiff_id)
  have hdne : ∀ v : ℝ, safeHeightDenominator (epsilon * v) ≠ 0 :=
    fun v => (safeHeightDenominator_pos (epsilon * v)).ne'
  exact (contDiff_const.mul
    (hA.comp ((contDiff_const.mul
      (contDiff_const.sub (contDiff_const.mul contDiff_id))).div hd hdne))).div
        (hd.pow 2) (fun v => pow_ne_zero 2 (hdne v))

private theorem stereoPoint_height_radius (epsilon : ℝ) (he : epsilon ^ 2 = 1)
    (p : ℝ × ℝ) :
    4 * (1 - epsilon * sphereHeight (stereoPoint epsilon he p)) /
      (1 + epsilon * sphereHeight (stereoPoint epsilon he p)) = p.1 ^ 2 + p.2 ^ 2 := by
  calc
    _ = 4 * (2 - (1 + epsilon * sphereHeight (stereoPoint epsilon he p))) /
        (1 + epsilon * sphereHeight (stereoPoint epsilon he p)) := by ring
    _ = _ := by
      rw [stereoPoint_height_denominator]
      have hd := (stereoDenominator_pos p).ne'
      field_simp [hd]
      unfold stereoDenominator
      ring

private theorem oneForm_eq_localHeightProfiles_at
    (h : OneFormSection (I := 𝓡 2) (M := RotationalSphere))
    (epsilon : ℝ) (he : epsilon ^ 2 = 1) (A B : ℝ → ℝ)
    (hdecomp : ∀ p V : ℝ × ℝ,
      h (stereoPoint epsilon he p) (fun _ : Fin 1 =>
        mfderiv 𝓘(ℝ, ℝ × ℝ) (𝓡 2) (stereoPoint epsilon he) p V) =
          A (p.1 ^ 2 + p.2 ^ 2) * (p.1 * V.1 + p.2 * V.2) +
            B (p.1 ^ 2 + p.2 ^ 2) * (p.1 * V.2 - p.2 * V.1))
    (p V : ℝ × ℝ)
    (hv : -(1 / 2 : ℝ) ≤ epsilon * sphereHeight (stereoPoint epsilon he p)) :
    h (stereoPoint epsilon he p) (fun _ : Fin 1 =>
      mfderiv 𝓘(ℝ, ℝ × ℝ) (𝓡 2) (stereoPoint epsilon he) p V) =
        localHeightProfile (-4 * epsilon) epsilon A
          (sphereHeight (stereoPoint epsilon he p)) *
            heightOneForm (stereoPoint epsilon he p) (fun _ : Fin 1 =>
              mfderiv 𝓘(ℝ, ℝ × ℝ) (𝓡 2) (stereoPoint epsilon he) p V) +
        localHeightProfile 4 epsilon B (sphereHeight (stereoPoint epsilon he p)) *
          sphereAzimuthalOneForm (stereoPoint epsilon he p) (fun _ : Fin 1 =>
            mfderiv 𝓘(ℝ, ℝ × ℝ) (𝓡 2) (stereoPoint epsilon he) p V) := by
  rw [hdecomp, heightOneForm_stereoPoint_mfderiv,
    sphereAzimuthalOneForm_stereoPoint_mfderiv]
  unfold localHeightProfile
  rw [safeHeightDenominator_eq hv, stereoPoint_height_radius,
    stereoPoint_height_denominator]
  have hd := (stereoDenominator_pos p).ne'
  field_simp [hd]
  ring_nf
  rw [he]
  ring

private theorem oneForm_eq_localHeightProfiles
    (h : OneFormSection (I := 𝓡 2) (M := RotationalSphere))
    (epsilon : ℝ) (he : epsilon ^ 2 = 1) (A B : ℝ → ℝ)
    (hdecomp : ∀ p V : ℝ × ℝ,
      h (stereoPoint epsilon he p) (fun _ : Fin 1 =>
        mfderiv 𝓘(ℝ, ℝ × ℝ) (𝓡 2) (stereoPoint epsilon he) p V) =
          A (p.1 ^ 2 + p.2 ^ 2) * (p.1 * V.1 + p.2 * V.2) +
            B (p.1 ^ 2 + p.2 ^ 2) * (p.1 * V.2 - p.2 * V.1))
    (x : RotationalSphere) (hv : -(1 / 2 : ℝ) ≤ epsilon * sphereHeight x) :
    ∀ V : TangentSpace (𝓡 2) x,
      h x (fun _ : Fin 1 => V) =
        localHeightProfile (-4 * epsilon) epsilon A (sphereHeight x) *
          heightOneForm x (fun _ : Fin 1 => V) +
        localHeightProfile 4 epsilon B (sphereHeight x) *
          sphereAzimuthalOneForm x (fun _ : Fin 1 => V) := by
  let p := stereoInversePoint epsilon x
  have hp : stereoPoint epsilon he p = x :=
    stereoPoint_inverse epsilon he x (by linarith)
  have hlocal : ∀ V : TangentSpace (𝓡 2) (stereoPoint epsilon he p),
      h (stereoPoint epsilon he p) (fun _ : Fin 1 => V) =
        localHeightProfile (-4 * epsilon) epsilon A
          (sphereHeight (stereoPoint epsilon he p)) *
          heightOneForm (stereoPoint epsilon he p) (fun _ : Fin 1 => V) +
        localHeightProfile 4 epsilon B (sphereHeight (stereoPoint epsilon he p)) *
          sphereAzimuthalOneForm (stereoPoint epsilon he p) (fun _ : Fin 1 => V) := by
    intro V
    obtain ⟨W, rfl⟩ := stereoPoint_mfderiv_surjective epsilon he p V
    exact oneForm_eq_localHeightProfiles_at h epsilon he A B hdecomp p W
      (by simpa only [hp] using hv)
  have hclaim := congrArg (fun y : RotationalSphere =>
    ∀ V : TangentSpace (𝓡 2) y,
      h y (fun _ : Fin 1 => V) =
        localHeightProfile (-4 * epsilon) epsilon A (sphereHeight y) *
          heightOneForm y (fun _ : Fin 1 => V) +
        localHeightProfile 4 epsilon B (sphereHeight y) *
          sphereAzimuthalOneForm y (fun _ : Fin 1 => V)) hp
  exact hclaim.mp hlocal

private def heightGlueCutoff (v : ℝ) : ℝ :=
  Real.smoothTransition (v + 1 / 2)

private theorem heightGlueCutoff_contDiff : ContDiff ℝ (⊤ : ℕ∞) heightGlueCutoff :=
  Real.smoothTransition.contDiff.comp (by fun_prop)

private theorem heightGlueCutoff_eq_zero {v : ℝ} (hv : v ≤ -(1 / 2 : ℝ)) :
    heightGlueCutoff v = 0 :=
  Real.smoothTransition.zero_of_nonpos (by linarith)

private theorem heightGlueCutoff_eq_one {v : ℝ} (hv : (1 / 2 : ℝ) ≤ v) :
    heightGlueCutoff v = 1 :=
  Real.smoothTransition.one_of_one_le (by linarith)

private def glueHeightProfile (north south : ℝ → ℝ) (v : ℝ) : ℝ :=
  heightGlueCutoff v * north v + (1 - heightGlueCutoff v) * south v

private theorem glueHeightProfile_contDiff (north south : ℝ → ℝ)
    (hnorth : ContDiff ℝ (⊤ : ℕ∞) north) (hsouth : ContDiff ℝ (⊤ : ℕ∞) south) :
    ContDiff ℝ (⊤ : ℕ∞) (glueHeightProfile north south) :=
  (heightGlueCutoff_contDiff.mul hnorth).add
    ((contDiff_const.sub heightGlueCutoff_contDiff).mul hsouth)

private theorem glueHeightProfile_eval (PN QN PS QS : ℝ → ℝ) (v a b w : ℝ)
    (hN : -(1 / 2 : ℝ) ≤ v → w = PN v * a + QN v * b)
    (hS : v ≤ (1 / 2 : ℝ) → w = PS v * a + QS v * b) :
    w = glueHeightProfile PN PS v * a + glueHeightProfile QN QS v * b := by
  by_cases hsouth : v ≤ -(1 / 2 : ℝ)
  · simpa only [glueHeightProfile, heightGlueCutoff_eq_zero hsouth,
      zero_mul, sub_zero, one_mul, zero_add] using hS (by linarith)
  · by_cases hnorth : (1 / 2 : ℝ) ≤ v
    · simpa only [glueHeightProfile, heightGlueCutoff_eq_one hnorth,
        one_mul, sub_self, zero_mul, add_zero] using hN (by linarith)
    · have hN' := hN (by linarith)
      have hS' := hS (by linarith)
      unfold glueHeightProfile
      linear_combination heightGlueCutoff v * hN' + (1 - heightGlueCutoff v) * hS'

/-- Every smooth sphere one-form fixed by all circle pullbacks is a global smooth
height combination of the height differential and the angular covector. The
formula applies to every genuine tangent vector, including at both poles. -/
theorem exists_smooth_height_azimuthal_profiles
    (h : OneFormSection (I := 𝓡 2) (M := RotationalSphere))
    (hinv : ∀ z : Circle, diffeomorphTensorPullback (circleSphereDiffeo z) h = h) :
    ∃ P Q : ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) P ∧ ContDiff ℝ (⊤ : ℕ∞) Q ∧
      ∀ (x : RotationalSphere) (V : TangentSpace (𝓡 2) x),
        h x (fun _ : Fin 1 => V) =
          P (sphereHeight x) * heightOneForm x (fun _ : Fin 1 => V) +
            Q (sphereHeight x) * sphereAzimuthalOneForm x (fun _ : Fin 1 => V) := by
  obtain ⟨AN, BN, hAN, hBN, hN⟩ :=
    exists_smooth_stereographic_coefficients h hinv 1 (by norm_num)
  obtain ⟨AS, BS, hAS, hBS, hS⟩ :=
    exists_smooth_stereographic_coefficients h hinv (-1) (by norm_num)
  let PN := localHeightProfile (-4 * 1) 1 AN
  let QN := localHeightProfile 4 1 BN
  let PS := localHeightProfile (-4 * (-1)) (-1) AS
  let QS := localHeightProfile 4 (-1) BS
  refine ⟨glueHeightProfile PN PS, glueHeightProfile QN QS,
    glueHeightProfile_contDiff PN PS
      (localHeightProfile_contDiff _ _ AN hAN) (localHeightProfile_contDiff _ _ AS hAS),
    glueHeightProfile_contDiff QN QS
      (localHeightProfile_contDiff _ _ BN hBN) (localHeightProfile_contDiff _ _ BS hBS), ?_⟩
  intro x V
  apply glueHeightProfile_eval
  · intro hx
    exact oneForm_eq_localHeightProfiles h 1 (by norm_num) AN BN hN x
      (by simpa only [one_mul] using hx) V
  · intro hx
    exact oneForm_eq_localHeightProfiles h (-1) (by norm_num) AS BS hS x
      (by linarith) V

end RicciFlowSharpEstimate.Geometry
