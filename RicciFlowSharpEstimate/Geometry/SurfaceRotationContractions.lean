/-
Copyright (c) 2026 Ziyang Qin. All rights reserved.
No license is granted by this file.
Authors: Ziyang Qin
-/
import RicciFlowSharpEstimate.Geometry.TraceFreeSymmetric
import DifferentialGeometry.Geometry.Metric.TensorInner.FiberMetric.Tensor0SMetricIneq

/-!
# Norms under surface rotation

Rotation is tied to the original metric sharp map and unit alternating tensor.
The private basis calculations adapt Ziyang Qin's historical
`OneFormPointwiseSpinSplit.lean` and `SurfaceHodgeCurlMeanZero.lean`.
-/

noncomputable section

namespace RicciFlowSharpEstimate.Geometry

open Bundle DifferentialGeometry DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Geometry.Operator DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Tensor.RSTensor DifferentialGeometry.Tensor.Coordinates
open scoped Manifold ContDiff BigOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

private theorem exists_basis_two (hdim : Module.finrank Real E = 2)
    (g : SmoothRiemannianMetric I M) (x : M) :
    ∃ B : Module.Basis (Fin 2) Real (TangentSpace I x),
      ∀ i j, g.inner x (B i) (B j) = if i = j then 1 else 0 := by
  obtain ⟨basis, hbasis⟩ := exists_orthonormal_basis g x
  let B := basis.reindex (finCongr hdim)
  refine ⟨B, fun i j => ?_⟩
  have hij : (finCongr hdim).symm i = (finCongr hdim).symm j ↔ i = j :=
    (finCongr hdim).symm.injective.eq_iff
  dsimp only [B]
  rw [Module.Basis.reindex_apply, Module.Basis.reindex_apply]
  exact (hbasis _ _).trans (if_congr hij rfl rfl)

private theorem norm_one (g : SmoothRiemannianMetric I M) {x : M}
    (B : Module.Basis (Fin 2) Real (TangentSpace I x))
    (hON : ∀ i j, g.inner x (B i) (B j) = if i = j then 1 else 0)
    (α : Tensor0SSpace (𝕜 := Real) (I := I) 1 x) :
    normSq0S g x 1 α = α (fun _ => B 0) ^ 2 + α (fun _ => B 1) ^ 2 := by
  rw [normSq0S_eq_inner, inner0S_one_eq_cotangent,
    cotangentInner_eq_coord g x B identityInvMetric
      (metricInverseInBasis_identity_of_orthonormal g B hON)]
  simp [Fin.sum_univ_two, identityInvMetric, diagonalInvMetric, cotangentToDual_apply, pow_two]

private theorem norm_two (g : SmoothRiemannianMetric I M) {x : M}
    (B : Module.Basis (Fin 2) Real (TangentSpace I x))
    (hON : ∀ i j, g.inner x (B i) (B j) = if i = j then 1 else 0)
    (T : Tensor0SSpace (𝕜 := Real) (I := I) 2 x) :
    normSq0S g x 2 T = T (vec2 (B 0) (B 0)) ^ 2 + T (vec2 (B 0) (B 1)) ^ 2 +
      T (vec2 (B 1) (B 0)) ^ 2 + T (vec2 (B 1) (B 1)) ^ 2 := by
  rw [normSq0S_eq_inner, inner0S_two_eq_coord g x B identityInvMetric
    (metricInverseInBasis_identity_of_orthonormal g B hON)]
  simp only [Fin.sum_univ_two, identityInvMetric, diagonalInvMetric, ite_true,
    zero_ne_one, one_ne_zero, ite_false, one_mul, zero_mul, zero_add, add_zero]
  change T (vec2 (B 0) (B 0)) * T (vec2 (B 0) (B 0)) +
      T (vec2 (B 0) (B 1)) * T (vec2 (B 0) (B 1)) +
      (T (vec2 (B 1) (B 0)) * T (vec2 (B 1) (B 0)) +
        T (vec2 (B 1) (B 1)) * T (vec2 (B 1) (B 1))) = _
  ring

private theorem trace_two (g : SmoothRiemannianMetric I M) {x : M}
    (B : Module.Basis (Fin 2) Real (TangentSpace I x))
    (hON : ∀ i j, g.inner x (B i) (B j) = if i = j then 1 else 0)
    (T : Tensor0SSpace (𝕜 := Real) (I := I) 2 x) :
    metricTracePair0SAt g T = T (vec2 (B 0) (B 0)) + T (vec2 (B 1) (B 1)) := by
  rw [metricTracePair0SAt_eq_sum_basis g B identityInvMetric
    (metricInverseInBasis_identity_of_orthonormal g B hON)]
  simp [Fin.sum_univ_two, identityInvMetric, diagonalInvMetric]

omit [FiniteDimensional Real E] in
private theorem curry_one_apply {x : M} (T : Tensor0SSpace (𝕜 := Real) (I := I) 2 x)
    (X Y : TangentSpace I x) :
    (tensor0SCurry (I := I) (𝕜 := Real) (M := M) 1 x T X) (fun _ : Fin 1 => Y) =
      T (vec2 X Y) := by
  exact tensor0S_curry_one_apply T X Y

private theorem rotation_coefficients (g : SmoothRiemannianMetric I M) {x : M}
    (B : Module.Basis (Fin 2) Real (TangentSpace I x))
    (hON : ∀ i j, g.inner x (B i) (B j) = if i = j then 1 else 0)
    (Ω : Tensor0SSpace (𝕜 := Real) (I := I) 2 x)
    (hΩ : ∀ v w, Ω (vec2 v w) = -Ω (vec2 w v))
    (α : Tensor0SSpace (𝕜 := Real) (I := I) 1 x) :
    Ω (vec2 (cotangentSharp g x α) (B 0)) =
        -Ω (vec2 (B 0) (B 1)) * α (fun _ => B 1) ∧
      Ω (vec2 (cotangentSharp g x α) (B 1)) =
        Ω (vec2 (B 0) (B 1)) * α (fun _ => B 0) := by
  have h00 : Ω (vec2 (B 0) (B 0)) = 0 := by have h := hΩ (B 0) (B 0); linarith
  have h11 : Ω (vec2 (B 1) (B 1)) = 0 := by have h := hΩ (B 1) (B 1); linarith
  have h10 := hΩ (B 1) (B 0)
  have hsharp := cotangentSharp_eq_sum_inv g x B identityInvMetric
    (metricInverseInBasis_identity_of_orthonormal g B hON) α
  simp only [Fin.sum_univ_two, identityInvMetric, diagonalInvMetric, ite_true,
    zero_ne_one, one_ne_zero, ite_false, one_mul, zero_mul, zero_add, add_zero,
    cotangentToDual_apply] at hsharp
  have heval (Y : TangentSpace I x) : Ω (vec2 (cotangentSharp g x α) Y) =
      α (fun _ => B 0) * Ω (vec2 (B 0) Y) +
        α (fun _ => B 1) * Ω (vec2 (B 1) Y) := by
    rw [← curry_one_apply, hsharp, map_add, map_smul, map_smul]
    simp only [Tensor0SSpace.add_apply, Tensor0SSpace.smul_apply, smul_eq_mul, curry_one_apply]
  constructor
  · rw [heval, h00, h10]
    ring
  · rw [heval, h11]
    ring

private theorem area_coefficient_sq (g : SmoothRiemannianMetric I M) {x : M}
    (B : Module.Basis (Fin 2) Real (TangentSpace I x))
    (hON : ∀ i j, g.inner x (B i) (B j) = if i = j then 1 else 0)
    (Ω : Tensor0SSpace (𝕜 := Real) (I := I) 2 x)
    (hΩ : ∀ v w, Ω (vec2 v w) = -Ω (vec2 w v))
    (hunit : normSq0S g x 2 Ω = 2) : Ω (vec2 (B 0) (B 1)) ^ 2 = 1 := by
  have h00 : Ω (vec2 (B 0) (B 0)) = 0 := by have h := hΩ (B 0) (B 0); linarith
  have h11 : Ω (vec2 (B 1) (B 1)) = 0 := by have h := hΩ (B 1) (B 1); linarith
  rw [norm_two g B hON, h00, h11, hΩ (B 1) (B 0)] at hunit
  nlinarith

/-- Rotation by a unit alternating surface tensor preserves the norm of a covector. -/
theorem normSq0S_one_eq_of_rotation (hdim : Module.finrank Real E = 2)
    (g : SmoothRiemannianMetric I M) (x : M)
    (Ω : Tensor0SSpace (𝕜 := Real) (I := I) 2 x)
    (hΩ : ∀ v w, Ω (vec2 v w) = -Ω (vec2 w v))
    (hunit : normSq0S g x 2 Ω = 2)
    (α β : Tensor0SSpace (𝕜 := Real) (I := I) 1 x)
    (hRot : ∀ Y, β (fun _ => Y) = Ω (vec2 (cotangentSharp g x α) Y)) :
    normSq0S g x 1 β = normSq0S g x 1 α := by
  obtain ⟨B, hON⟩ := exists_basis_two hdim g x
  have hs := area_coefficient_sq g B hON Ω hΩ hunit
  obtain ⟨h0, h1⟩ := rotation_coefficients g B hON Ω hΩ α
  rw [norm_one g B hON, norm_one g B hON, hRot, hRot, h0, h1]
  calc
    _ = Ω (vec2 (B 0) (B 1)) ^ 2 *
        (α (fun _ => B 0) ^ 2 + α (fun _ => B 1) ^ 2) := by ring
    _ = _ := by rw [hs, one_mul]

private theorem rotation_two_coefficients (g : SmoothRiemannianMetric I M) {x : M}
    (B : Module.Basis (Fin 2) Real (TangentSpace I x))
    (hON : ∀ i j, g.inner x (B i) (B j) = if i = j then 1 else 0)
    (Ω : Tensor0SSpace (𝕜 := Real) (I := I) 2 x)
    (hΩ : ∀ v w, Ω (vec2 v w) = -Ω (vec2 w v))
    (T S : Tensor0SSpace (𝕜 := Real) (I := I) 2 x)
    (hRot : ∀ X Y, S (vec2 X Y) =
      Ω (vec2 (cotangentSharp g x (tensor0SCurry (I := I) (𝕜 := Real) 1 x T X)) Y)) :
    (∀ i, S (vec2 (B i) (B 0)) = -Ω (vec2 (B 0) (B 1)) * T (vec2 (B i) (B 1))) ∧
      (∀ i, S (vec2 (B i) (B 1)) = Ω (vec2 (B 0) (B 1)) * T (vec2 (B i) (B 0))) := by
  constructor
  · intro i
    rw [hRot, (rotation_coefficients g B hON Ω hΩ _).1, curry_one_apply]
  · intro i
    rw [hRot, (rotation_coefficients g B hON Ω hΩ _).2, curry_one_apply]

/-- Rotation of the second covariant slot preserves the full two-tensor norm. -/
theorem normSq0S_two_eq_of_rotation (hdim : Module.finrank Real E = 2)
    (g : SmoothRiemannianMetric I M) (x : M)
    (Ω : Tensor0SSpace (𝕜 := Real) (I := I) 2 x)
    (hΩ : ∀ v w, Ω (vec2 v w) = -Ω (vec2 w v))
    (hunit : normSq0S g x 2 Ω = 2)
    (T S : Tensor0SSpace (𝕜 := Real) (I := I) 2 x)
    (hRot : ∀ X Y, S (vec2 X Y) =
      Ω (vec2 (cotangentSharp g x (tensor0SCurry (I := I) (𝕜 := Real) 1 x T X)) Y)) :
    normSq0S g x 2 S = normSq0S g x 2 T := by
  obtain ⟨B, hON⟩ := exists_basis_two hdim g x
  have hs := area_coefficient_sq g B hON Ω hΩ hunit
  obtain ⟨h0, h1⟩ := rotation_two_coefficients g B hON Ω hΩ T S hRot
  rw [norm_two g B hON, norm_two g B hON, h0 0, h1 0, h0 1, h1 1]
  calc
    _ = Ω (vec2 (B 0) (B 1)) ^ 2 *
        (T (vec2 (B 0) (B 0)) ^ 2 + T (vec2 (B 0) (B 1)) ^ 2 +
          T (vec2 (B 1) (B 0)) ^ 2 + T (vec2 (B 1) (B 1)) ^ 2) := by ring
    _ = _ := by rw [hs, one_mul]

private theorem ahlfors_norm (hdim : Module.finrank Real E = 2)
    (g : SmoothRiemannianMetric I M) {x : M}
    (B : Module.Basis (Fin 2) Real (TangentSpace I x))
    (hON : ∀ i j, g.inner x (B i) (B j) = if i = j then 1 else 0)
    (T : Tensor0SField (𝕜 := Real) (I := I) (M := M) (n := ∞) 2) :
    normSq0S g x 2 (ahlforsPart g T x) =
      ((T x (vec2 (B 0) (B 0)) - T x (vec2 (B 1) (B 1))) ^ 2 +
        (T x (vec2 (B 0) (B 1)) + T x (vec2 (B 1) (B 0))) ^ 2) / 2 := by
  have hcomp (i j : Fin 2) : ahlforsPart g T x (vec2 (B i) (B j)) =
      (T x (vec2 (B i) (B j)) + T x (vec2 (B j) (B i))) / 2 -
        (T x (vec2 (B 0) (B 0)) + T x (vec2 (B 1) (B 1))) / 2 *
          (if i = j then 1 else 0) := by
    rw [ahlforsPart_apply_of_finrank_eq_two hdim]
    simp only [Tensor0SSpace.sub_apply, Tensor0SSpace.smul_apply,
      Tensor0SSpace.add_apply, smul_eq_mul, metricTensor0S_apply]
    change (2 : Real)⁻¹ * (T x (vec2 (B i) (B j)) +
        T x (fun k => vec2 (B i) (B j) ((Equiv.swap (0 : Fin 2) 1).symm k))) -
        metricTracePair0SAt g (T x) / 2 * g.inner x (B i) (B j) = _
    rw [Equiv.symm_swap]
    have hswap : (fun k => vec2 (B i) (B j) (Equiv.swap (0 : Fin 2) 1 k)) =
        vec2 (B j) (B i) := by
      funext k
      fin_cases k <;> simp [vec2]
    rw [hswap, hON, trace_two g B hON]
    ring
  rw [norm_two g B hON, hcomp 0 0, hcomp 0 1, hcomp 1 0, hcomp 1 1]
  norm_num
  ring

/-- Rotation of the second covariant slot preserves the norm of the actual Ahlfors projection. -/
theorem normSq0S_ahlforsPart_eq_of_rotation (hdim : Module.finrank Real E = 2)
    (g : SmoothRiemannianMetric I M) (x : M)
    (Ω : Tensor0SSpace (𝕜 := Real) (I := I) 2 x)
    (hΩ : ∀ v w, Ω (vec2 v w) = -Ω (vec2 w v))
    (hunit : normSq0S g x 2 Ω = 2)
    (T S : Tensor0SField (𝕜 := Real) (I := I) (M := M) (n := ∞) 2)
    (hRot : ∀ X Y, S x (vec2 X Y) =
      Ω (vec2 (cotangentSharp g x (tensor0SCurry (I := I) (𝕜 := Real) 1 x (T x) X)) Y)) :
    normSq0S g x 2 (ahlforsPart g S x) = normSq0S g x 2 (ahlforsPart g T x) := by
  obtain ⟨B, hON⟩ := exists_basis_two hdim g x
  have hs := area_coefficient_sq g B hON Ω hΩ hunit
  obtain ⟨h0, h1⟩ := rotation_two_coefficients g B hON Ω hΩ (T x) (S x) hRot
  rw [ahlfors_norm hdim g B hON, ahlfors_norm hdim g B hON,
    h0 0, h1 1, h1 0, h0 1]
  calc
    _ = Ω (vec2 (B 0) (B 1)) ^ 2 *
        ((T x (vec2 (B 0) (B 0)) - T x (vec2 (B 1) (B 1))) ^ 2 +
          (T x (vec2 (B 0) (B 1)) + T x (vec2 (B 1) (B 0))) ^ 2) / 2 := by ring
    _ = _ := by rw [hs, one_mul]

end RicciFlowSharpEstimate.Geometry
