/-
Copyright (c) 2026 Ziyang Qin. All rights reserved.
No license is granted by this file.
Authors: Ziyang Qin
-/
import RicciFlowSharpEstimate.Geometry.TraceFreeSymmetric
import DifferentialGeometry.Geometry.Metric.TensorInner.FiberMetric.Tensor0SMetricIneq

/-!
# Pointwise decomposition of surface two-tensors

A smooth covariant two-tensor is the sum of its actual Ahlfors projection,
metric trace part, and alternating part. The alternating coefficient is its
contraction with the given unit area tensor.

The private orthonormal-basis calculations adapt Ziyang Qin's historical
`OneFormPointwiseSpinSplit.lean` and `SurfaceHodgeScalarization.lean`, and the
accepted calculations in `SurfaceRotationContractions.lean`.
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

private theorem ahlfors_coefficients (hdim : Module.finrank Real E = 2)
    (g : SmoothRiemannianMetric I M) {x : M}
    (B : Module.Basis (Fin 2) Real (TangentSpace I x))
    (hON : ∀ i j, g.inner x (B i) (B j) = if i = j then 1 else 0)
    (T : Tensor0SField (𝕜 := Real) (I := I) (M := M) (n := ∞) 2)
    (i j : Fin 2) : ahlforsPart g T x (vec2 (B i) (B j)) =
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

private theorem ahlfors_norm (hdim : Module.finrank Real E = 2)
    (g : SmoothRiemannianMetric I M) {x : M}
    (B : Module.Basis (Fin 2) Real (TangentSpace I x))
    (hON : ∀ i j, g.inner x (B i) (B j) = if i = j then 1 else 0)
    (T : Tensor0SField (𝕜 := Real) (I := I) (M := M) (n := ∞) 2) :
    normSq0S g x 2 (ahlforsPart g T x) =
      ((T x (vec2 (B 0) (B 0)) - T x (vec2 (B 1) (B 1))) ^ 2 +
        (T x (vec2 (B 0) (B 1)) + T x (vec2 (B 1) (B 0))) ^ 2) / 2 := by
  rw [norm_two g B hON, ahlfors_coefficients hdim g B hON T 0 0,
    ahlfors_coefficients hdim g B hON T 0 1,
    ahlfors_coefficients hdim g B hON T 1 0,
    ahlfors_coefficients hdim g B hON T 1 1]
  norm_num
  ring

private theorem inner_two (g : SmoothRiemannianMetric I M) {x : M}
    (B : Module.Basis (Fin 2) Real (TangentSpace I x))
    (hON : ∀ i j, g.inner x (B i) (B j) = if i = j then 1 else 0)
    (S T : Tensor0SSpace (𝕜 := Real) (I := I) 2 x) :
    inner0S g x 2 S T =
      S (vec2 (B 0) (B 0)) * T (vec2 (B 0) (B 0)) +
      S (vec2 (B 0) (B 1)) * T (vec2 (B 0) (B 1)) +
      S (vec2 (B 1) (B 0)) * T (vec2 (B 1) (B 0)) +
      S (vec2 (B 1) (B 1)) * T (vec2 (B 1) (B 1)) := by
  rw [inner0S_two_eq_coord g x B identityInvMetric
    (metricInverseInBasis_identity_of_orthonormal g B hON)]
  simp only [Fin.sum_univ_two, identityInvMetric, diagonalInvMetric, ite_true,
    zero_ne_one, one_ne_zero, ite_false, one_mul, zero_mul, zero_add, add_zero]
  change S (vec2 (B 0) (B 0)) * T (vec2 (B 0) (B 0)) +
      S (vec2 (B 0) (B 1)) * T (vec2 (B 0) (B 1)) +
      (S (vec2 (B 1) (B 0)) * T (vec2 (B 1) (B 0)) +
        S (vec2 (B 1) (B 1)) * T (vec2 (B 1) (B 1))) = _
  ring

private theorem curl_two (g : SmoothRiemannianMetric I M) {x : M}
    (B : Module.Basis (Fin 2) Real (TangentSpace I x))
    (hON : ∀ i j, g.inner x (B i) (B j) = if i = j then 1 else 0)
    (Ω T : Tensor0SSpace (𝕜 := Real) (I := I) 2 x)
    (hAlt : ∀ v w, Ω (vec2 v w) = -Ω (vec2 w v)) :
    inner0S g x 2 Ω T = Ω (vec2 (B 0) (B 1)) *
      (T (vec2 (B 0) (B 1)) - T (vec2 (B 1) (B 0))) := by
  have h00 : Ω (vec2 (B 0) (B 0)) = 0 := by have h := hAlt (B 0) (B 0); linarith
  have h11 : Ω (vec2 (B 1) (B 1)) = 0 := by have h := hAlt (B 1) (B 1); linarith
  rw [inner_two g B hON, h00, h11, hAlt (B 1) (B 0)]
  ring

private theorem area_coefficient_sq (g : SmoothRiemannianMetric I M) {x : M}
    (B : Module.Basis (Fin 2) Real (TangentSpace I x))
    (hON : ∀ i j, g.inner x (B i) (B j) = if i = j then 1 else 0)
    (Ω : Tensor0SSpace (𝕜 := Real) (I := I) 2 x)
    (hAlt : ∀ v w, Ω (vec2 v w) = -Ω (vec2 w v))
    (hUnit : normSq0S g x 2 Ω = 2) : Ω (vec2 (B 0) (B 1)) ^ 2 = 1 := by
  have h00 : Ω (vec2 (B 0) (B 0)) = 0 := by have h := hAlt (B 0) (B 0); linarith
  have h11 : Ω (vec2 (B 1) (B 1)) = 0 := by have h := hAlt (B 1) (B 1); linarith
  rw [norm_two g B hON, h00, h11, hAlt (B 1) (B 0)] at hUnit
  nlinarith

/-- A surface two-tensor is the sum of its actual Ahlfors, trace, and curl parts. -/
theorem twoTensor_eq_ahlforsPart_add_trace_add_curl
    (hdim : Module.finrank Real E = 2) (g : SmoothRiemannianMetric I M)
    (T : Tensor0SField (𝕜 := Real) (I := I) (M := M) (n := ∞) 2) (x : M)
    (Ω : Tensor0SSpace (𝕜 := Real) (I := I) 2 x)
    (hAlt : ∀ v w, Ω (vec2 v w) = -Ω (vec2 w v))
    (hUnit : normSq0S g x 2 Ω = 2) :
    T x = ahlforsPart g T x +
      (metricTracePair0SAt g (T x) / 2) • metricTensor0S g x +
      (inner0S g x 2 Ω (T x) / 2) • Ω := by
  obtain ⟨B, hON⟩ := exists_basis_two hdim g x
  have h00 : Ω (vec2 (B 0) (B 0)) = 0 := by have h := hAlt (B 0) (B 0); linarith
  have h11 : Ω (vec2 (B 1) (B 1)) = 0 := by have h := hAlt (B 1) (B 1); linarith
  have h10 := hAlt (B 1) (B 0)
  have hs := area_coefficient_sq g B hON Ω hAlt hUnit
  have hs01 := congrArg (fun r : Real => r * T x (vec2 (B 0) (B 1))) hs
  have hs10 := congrArg (fun r : Real => r * T x (vec2 (B 1) (B 0))) hs
  have hcomp (i j : Fin 2) : T x (vec2 (B i) (B j)) =
      (ahlforsPart g T x +
        (metricTracePair0SAt g (T x) / 2) • metricTensor0S g x +
        (inner0S g x 2 Ω (T x) / 2) • Ω) (vec2 (B i) (B j)) := by
    simp only [Tensor0SSpace.add_apply, Tensor0SSpace.smul_apply,
      smul_eq_mul, metricTensor0S_apply]
    change T x (vec2 (B i) (B j)) = ahlforsPart g T x (vec2 (B i) (B j)) +
      metricTracePair0SAt g (T x) / 2 * g.inner x (B i) (B j) +
      inner0S g x 2 Ω (T x) / 2 * Ω (vec2 (B i) (B j))
    rw [ahlfors_coefficients hdim g B hON, trace_two g B hON, hON,
      curl_two g B hON Ω (T x) hAlt]
    fin_cases i <;> fin_cases j <;> norm_num [h00, h11, h10] <;> nlinarith
  apply ext0S_basis B
  intro idx
  have hvec : (fun a => B (idx a)) = vec2 (B (idx 0)) (B (idx 1)) := by
    funext a
    fin_cases a <;> simp [vec2]
  simpa only [component0S_apply, hvec] using hcomp (idx 0) (idx 1)

/-- The trace and curl account for exactly the norm outside the Ahlfors part. -/
theorem normSq0S_twoTensor_eq_ahlforsPart_trace_curl
    (hdim : Module.finrank Real E = 2) (g : SmoothRiemannianMetric I M)
    (T : Tensor0SField (𝕜 := Real) (I := I) (M := M) (n := ∞) 2) (x : M)
    (Ω : Tensor0SSpace (𝕜 := Real) (I := I) 2 x)
    (hAlt : ∀ v w, Ω (vec2 v w) = -Ω (vec2 w v))
    (hUnit : normSq0S g x 2 Ω = 2) :
    normSq0S g x 2 (T x) = normSq0S g x 2 (ahlforsPart g T x) +
      (metricTracePair0SAt g (T x) ^ 2 + inner0S g x 2 Ω (T x) ^ 2) / 2 := by
  obtain ⟨B, hON⟩ := exists_basis_two hdim g x
  have hs := area_coefficient_sq g B hON Ω hAlt hUnit
  have hcurl : inner0S g x 2 Ω (T x) ^ 2 =
      (T x (vec2 (B 0) (B 1)) - T x (vec2 (B 1) (B 0))) ^ 2 := by
    rw [curl_two g B hON Ω (T x) hAlt, mul_pow, hs, one_mul]
  rw [norm_two g B hON, ahlfors_norm hdim g B hON, trace_two g B hON, hcurl]
  ring

/-- Pairing the Ahlfors projection with its source gives the projection's squared norm. -/
theorem inner0S_ahlforsPart_self
    (hdim : Module.finrank Real E = 2) (g : SmoothRiemannianMetric I M)
    (T : Tensor0SField (𝕜 := Real) (I := I) (M := M) (n := ∞) 2) (x : M) :
    inner0S g x 2 (ahlforsPart g T x) (T x) =
      normSq0S g x 2 (ahlforsPart g T x) := by
  obtain ⟨B, hON⟩ := exists_basis_two hdim g x
  rw [inner_two g B hON, ahlfors_norm hdim g B hON,
    ahlfors_coefficients hdim g B hON T 0 0,
    ahlfors_coefficients hdim g B hON T 0 1,
    ahlfors_coefficients hdim g B hON T 1 0,
    ahlfors_coefficients hdim g B hON T 1 1]
  norm_num
  ring

end RicciFlowSharpEstimate.Geometry
