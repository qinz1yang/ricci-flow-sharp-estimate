/-
Copyright (c) 2026 Ziyang Qin. All rights reserved.
No license is granted by this file.
Authors: Ziyang Qin
-/
import RicciFlowSharpEstimate.Geometry.AlternatingSurfaceTensors
import RicciFlowSharpEstimate.Geometry.SurfaceTensorDecomposition
import RicciFlowSharpEstimate.Geometry.TensorOrthonormalContractions
import DifferentialGeometry.Geometry.Connection.MetricTrace.CovariantTwoTensor

/-!
# Covariant derivative decomposition of surface two-tensors

The actual covariant derivative splits into the derivative of the existing Ahlfors
projection and the differentials of the metric trace and oriented curl. The unit
alternating tensor is proved parallel from its ordinary pointwise hypotheses.

The differential calculations adapt Ziyang Qin's historical
`SurfaceHodgeDifferentials.lean`. The private finite-coordinate calculations also
use the methods of `TraceFreeTensorWeitzenbock.lean` and the accepted
`SurfaceTensorDecomposition.lean`.
-/

noncomputable section

namespace RicciFlowSharpEstimate.Geometry

open Bundle DifferentialGeometry DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Geometry.Operator DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Connection DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.Tensor.RSTensor DifferentialGeometry.Tensor.Coordinates
open DifferentialGeometry.Tensor.RicciIdentity
open scoped Manifold ContDiff BigOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
variable [IsManifold I ∞ M] [T2Space M]

private theorem nabla_eq_curry {s : ℕ} (g : SmoothRiemannianMetric I M)
    (T : Tensor0SField (𝕜 := Real) (I := I) (M := M) (n := ∞) s)
    (X : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M → Type _))
    (x : M) :
    nabla0SFun s (metricCov g) X T x =
      tensor0SCurry (I := I) (𝕜 := Real) s x (metricNabla0S g T x) (X x) := by
  ext slots
  rw [tensor0S_curry_apply_cons]
  exact (canonicalDerivatives_first g T X x slots).symm

/-- The differential of the tensor trace is the last-two-slot trace of the actual derivative. -/
theorem differential1FormFun_metricTrace_apply (g : SmoothRiemannianMetric I M)
    (T : Tensor0SField (𝕜 := Real) (I := I) (M := M) (n := ∞) 2)
    (x : M) (X : TangentSpace I x) :
    differential1FormFun (I := I) (fun y => metricTracePair0SAt g (T y)) x
        (fun _ : Fin 1 => X) =
      metricTracePair0SAt g (tensor0SCurry (I := I) (𝕜 := Real) 2 x
        (metricNabla0S g T x) X) := by
  obtain ⟨Xs, hXs⟩ := ContMDiffSection.exists_eq_at
    (I := I) (F := E) (V := TangentSpace I) (n := (⊤ : ℕ∞)) x X
  have h := differential_metricTrace_eq_metricTrace_nabla (metricCov g) g
    (leviCivitaConnectionOfMetric_isMetricCompatible g) T Xs x
  dsimp only at h
  rw [nabla_eq_curry, hXs] at h
  exact h

/-- The differential of the native rank-two pairing follows the metric product rule. -/
theorem differential1FormFun_inner0S_two_apply (g : SmoothRiemannianMetric I M)
    (S T : Tensor0SField (𝕜 := Real) (I := I) (M := M) (n := ∞) 2)
    (x : M) (X : TangentSpace I x) :
    differential1FormFun (I := I) (fun y => inner0S g y 2 (S y) (T y)) x
        (fun _ : Fin 1 => X) =
      inner0S g x 2 (tensor0SCurry (I := I) (𝕜 := Real) 2 x
        (metricNabla0S g S x) X) (T x) +
      inner0S g x 2 (S x) (tensor0SCurry (I := I) (𝕜 := Real) 2 x
        (metricNabla0S g T x) X) := by
  obtain ⟨Xs, hXs⟩ := ContMDiffSection.exists_eq_at
    (I := I) (F := E) (V := TangentSpace I) (n := (⊤ : ℕ∞)) x X
  have h := inner0S_two_nabla (metricCov g) g
    (leviCivitaConnectionOfMetric_isMetricCompatible g) S T Xs x
  rw [nabla_eq_curry, nabla_eq_curry, hXs] at h
  rw [differential1FormFun_apply_eq_mvfderiv]
  exact h

omit [T2Space M] in
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

private theorem sum_finThree_functions
    (f : (Fin 3 → Fin 2) → Real) :
    (∑ φ : Fin 3 → Fin 2, f φ) =
      ∑ i : Fin 2, ∑ j : Fin 2, ∑ k : Fin 2, f ![i, j, k] := by
  classical
  let e : (Fin 3 → Fin 2) ≃ Fin 2 × (Fin 2 × Fin 2) :=
    (Fin.consEquiv (fun _ : Fin 3 => Fin 2)).symm.trans
      (Equiv.prodCongr (Equiv.refl (Fin 2))
        (finTwoArrowEquiv (Fin 2)))
  calc
    (∑ φ : Fin 3 → Fin 2, f φ) =
        ∑ p : Fin 2 × (Fin 2 × Fin 2), f (e.symm p) := by
      refine Fintype.sum_equiv e _ _ ?_
      intro φ
      rw [e.symm_apply_apply]
    _ = ∑ i : Fin 2, ∑ jk : Fin 2 × Fin 2,
        f (e.symm (i, jk)) := by
      rw [Fintype.sum_prod_type]
    _ = ∑ i : Fin 2, ∑ j : Fin 2, ∑ k : Fin 2,
        f ![i, j, k] := by
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [Fintype.sum_prod_type]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      refine Finset.sum_congr rfl (fun k _ => ?_)
      congr 1

private theorem sum_finOne_functions
    (f : (Fin 1 → Fin 2) → Real) :
    (∑ φ : Fin 1 → Fin 2, f φ) =
      ∑ i : Fin 2, f ![i] := by
  classical
  let e : (Fin 1 → Fin 2) ≃ Fin 2 :=
    { toFun := fun φ => φ 0
      invFun := fun i => ![i]
      left_inv := by
        intro φ
        funext q
        have hq : q = 0 := Subsingleton.elim _ _
        subst q
        rfl
      right_inv := by
        intro i
        rfl }
  refine Fintype.sum_equiv e _ _ ?_
  intro φ
  congr 1
  change φ = ![φ 0]
  funext q
  have hq : q = 0 := Subsingleton.elim _ _
  subst q
  rfl

omit [T2Space M] in
private theorem norm_one (g : SmoothRiemannianMetric I M) {x : M}
    (B : Module.Basis (Fin 2) Real (TangentSpace I x))
    (hON : ∀ i j, g.inner x (B i) (B j) = if i = j then 1 else 0)
    (T : Tensor0SSpace (𝕜 := Real) (I := I) 1 x) :
    normSq0S g x 1 T = ∑ i : Fin 2, T (fun _ => B i) ^ 2 := by
  rw [normSq0S_eq_sum_sq_orthonormal g x 1 B hON, sum_finOne_functions]
  refine Finset.sum_congr rfl fun i _ => ?_
  congr 2
  funext q
  fin_cases q
  rfl

omit [T2Space M] in
private theorem norm_three (g : SmoothRiemannianMetric I M) {x : M}
    (B : Module.Basis (Fin 2) Real (TangentSpace I x))
    (hON : ∀ i j, g.inner x (B i) (B j) = if i = j then 1 else 0)
    (T : Tensor0SSpace (𝕜 := Real) (I := I) 3 x) :
    normSq0S g x 3 T = ∑ i : Fin 2,
      (T ![B i, B 0, B 0] ^ 2 + T ![B i, B 0, B 1] ^ 2 +
        T ![B i, B 1, B 0] ^ 2 + T ![B i, B 1, B 1] ^ 2) := by
  rw [normSq0S_eq_sum_sq_orthonormal g x 3 B hON, sum_finThree_functions]
  have hslots (i j k : Fin 2) :
      (fun q => B (![i, j, k] q)) = ![B i, B j, B k] := by
    funext q
    fin_cases q <;> rfl
  simp only [hslots]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Fin.sum_univ_two]
  ring

private theorem sum_finTwo_functions (f : (Fin 2 → Fin 2) → Real) :
    (∑ v : Fin 2 → Fin 2, f v) = ∑ i : Fin 2, ∑ j : Fin 2, f ![i, j] := by
  rw [Fintype.sum_equiv (finTwoArrowEquiv (Fin 2)) f
    (fun ij : Fin 2 × Fin 2 => f ![ij.1, ij.2])]
  · rw [Fintype.sum_prod_type]
  · intro v
    congr 1
    funext q
    fin_cases q <;> rfl

omit [T2Space M] in
private theorem norm_two (g : SmoothRiemannianMetric I M) {x : M}
    (B : Module.Basis (Fin 2) Real (TangentSpace I x))
    (hON : ∀ i j, g.inner x (B i) (B j) = if i = j then 1 else 0)
    (T : Tensor0SSpace (𝕜 := Real) (I := I) 2 x) :
    normSq0S g x 2 T =
      T (vec2 (B 0) (B 0)) ^ 2 + T (vec2 (B 0) (B 1)) ^ 2 +
        T (vec2 (B 1) (B 0)) ^ 2 + T (vec2 (B 1) (B 1)) ^ 2 := by
  rw [normSq0S_eq_sum_sq_orthonormal g x 2 B hON, sum_finTwo_functions]
  have hslots (i j : Fin 2) : (fun q => B (![i, j] q)) = vec2 (B i) (B j) := by
    funext q
    fin_cases q <;> rfl
  simp only [hslots, Fin.sum_univ_two]
  ring

omit [T2Space M] in
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

omit [T2Space M] in
private theorem norm_split_of_coefficients (g : SmoothRiemannianMetric I M) {x : M}
    (B : Module.Basis (Fin 2) Real (TangentSpace I x))
    (hON : ∀ i j, g.inner x (B i) (B j) = if i = j then 1 else 0)
    (T A : Tensor0SSpace (𝕜 := Real) (I := I) 3 x)
    (τ κ : Tensor0SSpace (𝕜 := Real) (I := I) 1 x)
    (c : Real) (hc : c ^ 2 = 1)
    (hA : ∀ i j k : Fin 2, A ![B i, B j, B k] =
      (T ![B i, B j, B k] + T ![B i, B k, B j]) / 2 -
        τ (fun _ => B i) / 2 * (if j = k then 1 else 0))
    (hτ : ∀ i : Fin 2, τ (fun _ => B i) = T ![B i, B 0, B 0] + T ![B i, B 1, B 1])
    (hκ : ∀ i : Fin 2, κ (fun _ => B i) =
      c * (T ![B i, B 0, B 1] - T ![B i, B 1, B 0])) :
    normSq0S g x 3 T = normSq0S g x 3 A +
      (normSq0S g x 1 τ + normSq0S g x 1 κ) / 2 := by
  have hi (i : Fin 2) :
      T ![B i, B 0, B 0] ^ 2 + T ![B i, B 0, B 1] ^ 2 +
          T ![B i, B 1, B 0] ^ 2 + T ![B i, B 1, B 1] ^ 2 =
        A ![B i, B 0, B 0] ^ 2 + A ![B i, B 0, B 1] ^ 2 +
          A ![B i, B 1, B 0] ^ 2 + A ![B i, B 1, B 1] ^ 2 +
            (τ (fun _ => B i) ^ 2 + κ (fun _ => B i) ^ 2) / 2 := by
    rw [hA i 0 0, hA i 0 1, hA i 1 0, hA i 1 1, hτ, hκ, mul_pow, hc]
    norm_num
    ring
  rw [norm_three g B hON, norm_three g B hON, norm_one g B hON, norm_one g B hON]
  simp only [Fin.sum_univ_two]
  linarith [hi 0, hi 1]

omit [T2Space M] in
private theorem curl_curry (g : SmoothRiemannianMetric I M) {x : M}
    (B : Module.Basis (Fin 2) Real (TangentSpace I x))
    (hON : ∀ i j, g.inner x (B i) (B j) = if i = j then 1 else 0)
    (Ω : Tensor0SSpace (𝕜 := Real) (I := I) 2 x)
    (hAlt : ∀ v w, Ω (vec2 v w) = -Ω (vec2 w v))
    (T : Tensor0SSpace (𝕜 := Real) (I := I) 3 x) (X : TangentSpace I x) :
    inner0S g x 2 Ω (tensor0SCurry (I := I) (𝕜 := Real) 2 x T X) =
      Ω (vec2 (B 0) (B 1)) * (T ![X, B 0, B 1] - T ![X, B 1, B 0]) := by
  rw [inner0S_eq_sum_orthonormal g x 2 B hON, sum_finTwo_functions]
  have hslots (i j : Fin 2) : (fun q => B (![i, j] q)) = vec2 (B i) (B j) := by
    funext q
    fin_cases q <;> rfl
  simp only [hslots, Fin.sum_univ_two, tensor0S_curry_apply_cons]
  have h00 : Ω (vec2 (B 0) (B 0)) = 0 := by have h := hAlt (B 0) (B 0); linarith
  have h11 : Ω (vec2 (B 1) (B 1)) = 0 := by have h := hAlt (B 1) (B 1); linarith
  rw [h00, h11, hAlt (B 1) (B 0)]
  have hcons (Y Z : TangentSpace I x) : Fin.cons X (vec2 Y Z) = ![X, Y, Z] := by
    funext q
    fin_cases q <;> rfl
  simp only [hcons]
  ring

/-- The actual derivative of the Ahlfors part projects the last two tensor slots. -/
theorem metricNabla0S_ahlforsPart_apply
    (hdim : Module.finrank Real E = 2) (g : SmoothRiemannianMetric I M)
    (T : Tensor0SField (𝕜 := Real) (I := I) (M := M) (n := ∞) 2)
    (x : M) (X Y Z : TangentSpace I x) :
    metricNabla0S g (ahlforsPart g T) x (Fin.cons X (vec2 Y Z)) =
      (metricNabla0S g T x (Fin.cons X (vec2 Y Z)) +
        metricNabla0S g T x (Fin.cons X (vec2 Z Y))) / 2 -
      differential1FormFun (I := I) (fun y => metricTracePair0SAt g (T y)) x
        (fun _ : Fin 1 => X) / 2 * g.inner x Y Z := by
  let tr : M → Real := fun y => metricTracePair0SAt g (T y)
  have htr : ContMDiff I 𝓘(Real, Real) ∞ tr := trace02_smooth g T
  let P := tensor0SFieldSmulByFun (∞ : WithTop ℕ∞) tr htr (metricTensorField g)
  let swap : Fin 2 ≃ Fin 2 := Equiv.swap 0 1
  let S := Tensor0SField.domDomCongr (∞ : WithTop ℕ∞) swap T
  have hA : ahlforsPart g T = (2 : Real)⁻¹ • (T + S + (-1 : Real) • P) := by
    refine DFunLike.ext _ _ fun y => ?_
    ext slots
    rw [ahlforsPart_apply_of_finrank_eq_two hdim]
    change (2 : Real)⁻¹ * (T y slots + (T y).domDomCongr swap slots) -
        metricTracePair0SAt g (T y) / 2 * g.inner y (slots 0) (slots 1) =
      (2 : Real)⁻¹ * (T y slots + (T y).domDomCongr swap slots +
        -1 * (metricTracePair0SAt g (T y) * g.inner y (slots 0) (slots 1)))
    ring
  obtain ⟨Xs, hXs⟩ := ContMDiffSection.exists_eq_at
    (I := I) (F := E) (V := TangentSpace I) (n := (⊤ : ℕ∞)) x X
  have hP : nabla0SFun 2 (metricCov g) Xs P x (vec2 Y Z) =
      differential1FormFun (I := I) tr x (fun _ : Fin 1 => X) * g.inner x Y Z := by
    have hp := nabla_smul_metric (metricCov g) g
      (leviCivitaConnectionOfMetric_isMetricCompatible g) tr htr (duSec tr htr)
      (fun y v => differential1FormFun_apply_eq_mvfderiv tr y v) Xs x (vec2 Y Z)
    calc
      _ = (MultilinearSection.product (𝕜 := Real) (F := E) (IB := I)
          (E := TangentSpace I) (∞ : WithTop ℕ∞) (duSec tr htr)
          (metricTensorField g)) x (Fin.cons (Xs x) (vec2 Y Z)) := hp.symm
      _ = _ := by
        change (Bundle.continuousMultilinearMap.productFun
          (tensor0SSpaceFiberContinuousLinearEquiv (I := I) 1 x (duSec tr htr x))
          (tensor0SSpaceFiberContinuousLinearEquiv (I := I) 2 x (metricTensorField g x)))
            (Fin.cons (Xs x) (vec2 Y Z)) = _
        rw [Bundle.continuousMultilinearMap.product_fun_apply]
        have hleft : (Fin.cons (Xs x) (vec2 Y Z)) ∘ Fin.castAdd 2 =
            fun _ : Fin 1 => Xs x := by
          funext q
          fin_cases q
          rfl
        have hright : (Fin.cons (Xs x) (vec2 Y Z)) ∘ Fin.natAdd 1 = vec2 Y Z := by
          funext q
          fin_cases q <;> rfl
        rw [hleft, hright, tensor0SSpaceFiberContinuousLinearEquiv_apply_apply,
          tensor0SSpaceFiberContinuousLinearEquiv_apply_apply, duSec_apply,
          metricTensorField_apply, hXs]
        rfl
  have hS : nabla0SFun 2 (metricCov g) Xs S x (vec2 Y Z) =
      nabla0SFun 2 (metricCov g) Xs T x (vec2 Z Y) := by
    rw [nabla0SFun_domDomCongr]
    congr 1
    funext q
    fin_cases q <;> simp [swap, vec2]
  have hT := canonicalDerivatives_first g T Xs x (vec2 Y Z)
  have hT' := canonicalDerivatives_first g T Xs x (vec2 Z Y)
  rw [hXs] at hT hT'
  calc
    _ = nabla0SFun 2 (metricCov g) Xs (ahlforsPart g T) x (vec2 Y Z) := by
      simpa only [hXs] using canonicalDerivatives_first g (ahlforsPart g T) Xs x (vec2 Y Z)
    _ = _ := by
      rw [hA, nabla0SFun_smul, nabla0SFun_add, nabla0SFun_add, nabla0SFun_smul]
      simp only [Tensor0SSpace.smul_apply, Tensor0SSpace.add_apply, smul_eq_mul]
      rw [hS, hP, ← hT, ← hT']
      change _ = _ - differential1FormFun (I := I) tr x (fun _ : Fin 1 => X) / 2 * _
      ring

omit [T2Space M] in
private theorem trace_two (g : SmoothRiemannianMetric I M) {x : M}
    (B : Module.Basis (Fin 2) Real (TangentSpace I x))
    (hON : ∀ i j, g.inner x (B i) (B j) = if i = j then 1 else 0)
    (T : Tensor0SSpace (𝕜 := Real) (I := I) 2 x) :
    metricTracePair0SAt g T = T (vec2 (B 0) (B 0)) + T (vec2 (B 1) (B 1)) := by
  rw [metricTracePair0SAt_eq_sum_basis g B identityInvMetric
    (metricInverseInBasis_identity_of_orthonormal g B hON)]
  simp [Fin.sum_univ_two, identityInvMetric, diagonalInvMetric]

/-- The genuine gradient norm splits into Ahlfors, trace, and curl derivative energies. -/
theorem normSq0S_metricNabla0S_twoTensor_split
    (hdim : Module.finrank Real E = 2) (g : SmoothRiemannianMetric I M)
    (T Ω : TwoTensorSection (I := I) (M := M))
    (hAlt : ∀ x v w, Ω x (vec2 v w) = -Ω x (vec2 w v))
    (hUnit : ∀ x, normSq0S g x 2 (Ω x) = 2) (x : M) :
    normSq0S g x 3 (metricNabla0S g T x) =
      normSq0S g x 3 (metricNabla0S g (ahlforsPart g T) x) +
        (normSq0S g x 1
            (differential1FormFun (I := I) (fun y => metricTracePair0SAt g (T y)) x) +
          normSq0S g x 1
            (differential1FormFun (I := I) (fun y => inner0S g y 2 (Ω y) (T y)) x)) / 2 := by
  obtain ⟨B, hON⟩ := exists_basis_two hdim g x
  have hParallel := metricNabla0S_eq_zero_of_alternating_const_normSq
    hdim g Ω hAlt 2 hUnit
  have hcons (U V W : TangentSpace I x) : Fin.cons U (vec2 V W) = ![U, V, W] := by
    funext q
    fin_cases q <;> rfl
  refine norm_split_of_coefficients g B hON (metricNabla0S g T x)
    (metricNabla0S g (ahlforsPart g T) x)
    (differential1FormFun (I := I) (fun y => metricTracePair0SAt g (T y)) x)
    (differential1FormFun (I := I) (fun y => inner0S g y 2 (Ω y) (T y)) x)
    (Ω x (vec2 (B 0) (B 1)))
    (area_coefficient_sq g B hON (Ω x) (hAlt x) (hUnit x)) ?_ ?_ ?_
  · intro i j k
    have h := metricNabla0S_ahlforsPart_apply hdim g T x (B i) (B j) (B k)
    simpa only [hcons, hON] using h
  · intro i
    rw [differential1FormFun_metricTrace_apply, trace_two g B hON,
      tensor0S_curry_apply_cons, tensor0S_curry_apply_cons, hcons, hcons]
  · intro i
    have hP : tensor0SCurry (I := I) (𝕜 := Real) 2 x
        (metricNabla0S g Ω x) (B i) = 0 := by
      rw [hParallel]
      ext slots
      rw [tensor0S_curry_apply_cons]
      rfl
    have hzero : inner0S g x 2 (0 : Tensor0SSpace (𝕜 := Real) (I := I) 2 x) (T x) = 0 := by
      simpa only [zero_smul, zero_mul] using inner0S_smul_left g x 2 0 (T x) (T x)
    rw [differential1FormFun_inner0S_two_apply, hP, hzero, zero_add]
    exact curl_curry g B hON (Ω x) (hAlt x) (metricNabla0S g T x) (B i)

end RicciFlowSharpEstimate.Geometry
