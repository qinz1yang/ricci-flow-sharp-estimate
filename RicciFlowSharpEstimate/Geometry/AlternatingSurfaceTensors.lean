/-
Copyright (c) 2026 Ziyang Qin. All rights reserved.
No license is granted by this file.
Authors: Ziyang Qin
-/
import RicciFlowSharpEstimate.Geometry.CanonicalDerivatives
import DifferentialGeometry.Geometry.Connection.TensorNabla.Naturality.SlotPermutation
import DifferentialGeometry.Geometry.Metric.TensorInner.Tensor0S.Calculus.CovariantDerivative
import DifferentialGeometry.Geometry.Metric.TensorInner.FiberMetric.Tensor0SMetricIneq

/-!
# Parallel alternating tensors on surfaces

The argument adapts Ziyang Qin's historical `UnitAlternatingAreaFormParallel.lean`.
It uses the native covariant derivative and metric pairing, and includes the zero-norm case.
-/

noncomputable section

namespace RicciFlowSharpEstimate.Geometry

open Bundle DifferentialGeometry DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Tensor.RSTensor DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow DifferentialGeometry.Tensor.Coordinates
open scoped Manifold ContDiff BigOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

private theorem alternating_two_tensor_ext {x : M}
    (basis : Module.Basis (Fin 2) Real (TangentSpace I x))
    (A B : Tensor0SSpace (𝕜 := Real) (I := I) 2 x)
    (hA : ∀ v w, A (vec2 v w) = -A (vec2 w v))
    (hB : ∀ v w, B (vec2 v w) = -B (vec2 w v))
    (h01 : A (vec2 (basis 0) (basis 1)) = B (vec2 (basis 0) (basis 1))) : A = B := by
  have hA00 := hA (basis 0) (basis 0)
  have hA11 := hA (basis 1) (basis 1)
  have hB00 := hB (basis 0) (basis 0)
  have hB11 := hB (basis 1) (basis 1)
  apply ext0S_basis (I := I) basis
  intro slots
  have hslots : (fun i : Fin 2 => basis (slots i)) =
      vec2 (basis (slots 0)) (basis (slots 1)) := by
    funext i
    fin_cases i <;> rfl
  simp only [component0S_apply]
  rw [hslots]
  have h0 : slots 0 = 0 ∨ slots 0 = 1 := by omega
  have h1 : slots 1 = 0 ∨ slots 1 = 1 := by omega
  rcases h0 with h0 | h0 <;> rcases h1 with h1 | h1
  · rw [h0, h1]; linarith
  · rw [h0, h1]; exact h01
  · rw [h0, h1, hA, hB, h01]
  · rw [h0, h1]; linarith

private theorem alternating_two_tensor_eq_zero_of_orthogonal
    (hdim : Module.finrank Real E = 2)
    (g : SmoothRiemannianMetric I M) (x : M)
    (A B : Tensor0SSpace (𝕜 := Real) (I := I) 2 x)
    (hA : ∀ v w, A (vec2 v w) = -A (vec2 w v))
    (hB : ∀ v w, B (vec2 v w) = -B (vec2 w v))
    (hne : normSq0S g x 2 A ≠ 0)
    (horth : inner0S g x 2 B A = 0) : B = 0 := by
  classical
  let basis : Module.Basis (Fin 2) Real (TangentSpace I x) :=
    (Module.finBasis Real (TangentSpace I x)).reindex (finCongr hdim)
  let a := A (vec2 (basis 0) (basis 1))
  let b := B (vec2 (basis 0) (basis 1))
  have ha : a ≠ 0 := by
    intro ha
    have hzero : A = 0 := alternating_two_tensor_ext basis A 0 hA
      (by intros; simp) ha
    exact hne ((normSq0S_eq_zero_iff g x 2 A).mpr hzero)
  have hBA : B = (b / a) • A := by
    apply alternating_two_tensor_ext basis B _ hB
    · intro v w
      simp only [Tensor0SSpace.smul_apply, smul_eq_mul]
      rw [hA]
      ring
    · change b = b / a * a
      rw [div_mul_cancel₀ _ ha]
  rw [hBA, inner0S_smul_left] at horth
  have hc : b / a = 0 := (mul_eq_zero.mp horth).resolve_right hne
  rw [hBA, hc, zero_smul]

private theorem nabla_alternating_two_tensor [T2Space M]
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (A : Tensor0SField (𝕜 := Real) (I := I) (M := M) (n := ∞) 2)
    (hA : ∀ x v w, A x (vec2 v w) = -A x (vec2 w v))
    (X : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M → Type _))
    (x : M) (v w : TangentSpace I x) :
    nabla0SFun 2 cov X A x (vec2 v w) = -nabla0SFun 2 cov X A x (vec2 w v) := by
  let swap : Fin 2 ≃ Fin 2 := Equiv.swap 0 1
  have hswap : Tensor0SField.domDomCongr (∞ : WithTop ℕ∞) swap A = (-1 : Real) • A := by
    refine DFunLike.ext _ _ fun y => ?_
    ext slots
    change A y (fun i => slots (swap i)) = (-1 : Real) * A y slots
    have hslots : slots = vec2 (slots 0) (slots 1) := by
      funext i
      fin_cases i <;> rfl
    have hperm : (fun i => slots (swap i)) = vec2 (slots 1) (slots 0) := by
      funext i
      fin_cases i <;> simp [swap, vec2]
    rw [hperm, hA, hslots]
    simp [vec2]
  have h := nabla0SFun_domDomCongr cov X swap A x (vec2 v w)
  rw [hswap, nabla0SFun_smul] at h
  have hperm : (vec2 v w ∘ swap) = vec2 w v := by
    funext i
    fin_cases i <;> simp [swap, vec2]
  rw [hperm] at h
  simp only [Tensor0SSpace.smul_apply, smul_eq_mul, neg_one_mul] at h
  linarith

/-- Every smooth alternating covariant two-tensor of constant norm on a surface is parallel. -/
theorem metricNabla0S_eq_zero_of_alternating_const_normSq [T2Space M]
    (hdim : Module.finrank Real E = 2)
    (g : SmoothRiemannianMetric I M)
    (A : Tensor0SField (𝕜 := Real) (I := I) (M := M) (n := ∞) 2)
    (hA : ∀ x v w, A x (vec2 v w) = -A x (vec2 w v))
    (k : Real) (hnorm : ∀ x, normSq0S g x 2 (A x) = k) : metricNabla0S g A = 0 := by
  by_cases hk : k = 0
  · have hzero : A = 0 := by
      refine DFunLike.ext _ _ fun x => ?_
      exact (normSq0S_eq_zero_iff g x 2 (A x)).mp ((hnorm x).trans hk)
    rw [hzero]
    simpa only [zero_smul] using metricNabla0S_smul g (0 : Real) A
  have hmc : DifferentialGeometry.Geometry.Connection.IsMetricCompatible
      (metricCov (I := I) g) g :=
    DifferentialGeometry.Geometry.Connection.leviCivitaConnectionOfMetric_isMetricCompatible g
  refine DFunLike.ext _ _ fun x => ?_
  ext slots
  obtain ⟨X, hX⟩ := ContMDiffSection.exists_eq_at
    (I := I) (F := E) (V := TangentSpace I) (n := (⊤ : ℕ∞)) x (slots 0)
  let B := nabla0SFun 2 (metricCov (I := I) g) X A x
  have hnormfun : (fun y => inner0S g y 2 (A y) (A y)) = fun _ : M => k :=
    funext hnorm
  have hdiff := inner0S_two_nabla (metricCov (I := I) g) g hmc A A X x
  rw [hnormfun, mvfderiv_const] at hdiff
  have horth : inner0S g x 2 B (A x) = 0 := by
    rw [inner0S_symm g x (A x)] at hdiff
    change 0 = inner0S g x 2 B (A x) + inner0S g x 2 B (A x) at hdiff
    linarith
  have hBzero : B = 0 := alternating_two_tensor_eq_zero_of_orthogonal hdim g x (A x) B
    (hA x) (nabla_alternating_two_tensor (metricCov (I := I) g) A hA X x)
    (by rw [hnorm]; exact hk) horth
  have h := canonicalDerivatives_first g A X x (Fin.tail slots)
  rw [hX, Fin.cons_self_tail] at h
  change metricNabla0S g A x slots = 0
  change metricNabla0S g A x slots = B (Fin.tail slots) at h
  rw [h, hBzero]
  rfl

/-- An alternating tensor realizing the metric area has squared tensor norm two. -/
theorem normSq0S_eq_two_of_unit_alternating
    (hdim : Module.finrank Real E = 2)
    (g : SmoothRiemannianMetric I M) (x : M)
    (A : Tensor0SSpace (𝕜 := Real) (I := I) 2 x)
    (hA : ∀ v w, A (vec2 v w) = -A (vec2 w v))
    (hunit : ∀ (basis : Module.Basis (Fin 2) Real (TangentSpace I x)),
      (∀ i j, g.inner x (basis i) (basis j) = if i = j then 1 else 0) →
        A (vec2 (basis 0) (basis 1)) ^ 2 = 1) : normSq0S g x 2 A = 2 := by
  classical
  obtain ⟨basis, hbasis⟩ := exists_orthonormal_basis g x
  let B := basis.reindex (finCongr hdim)
  have hON (i j : Fin 2) : g.inner x (B i) (B j) = if i = j then 1 else 0 := by
    have hij : (finCongr hdim).symm i = (finCongr hdim).symm j ↔ i = j :=
      (finCongr hdim).symm.injective.eq_iff
    dsimp only [B]
    rw [Module.Basis.reindex_apply, Module.Basis.reindex_apply]
    exact (hbasis _ _).trans (if_congr hij rfl rfl)
  have h00 : A (vec2 (B 0) (B 0)) = 0 := by
    have h := hA (B 0) (B 0)
    linarith
  have h11 : A (vec2 (B 1) (B 1)) = 0 := by
    have h := hA (B 1) (B 1)
    linarith
  have h10 := hA (B 1) (B 0)
  have ha := hunit B hON
  rw [normSq0S, inner0S_two_eq_coord g x B identityInvMetric
    (metricInverseInBasis_identity_of_orthonormal g B hON)]
  simp only [Fin.sum_univ_two, identityInvMetric, diagonalInvMetric, ite_true,
    zero_ne_one, one_ne_zero, ite_false, one_mul, zero_mul, zero_add, add_zero]
  change A (vec2 (B 0) (B 0)) * A (vec2 (B 0) (B 0)) +
      A (vec2 (B 0) (B 1)) * A (vec2 (B 0) (B 1)) +
      (A (vec2 (B 1) (B 0)) * A (vec2 (B 1) (B 0)) +
        A (vec2 (B 1) (B 1)) * A (vec2 (B 1) (B 1))) = 2
  rw [h00, h11, h10]
  nlinarith

end RicciFlowSharpEstimate.Geometry
