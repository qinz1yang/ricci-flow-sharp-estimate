/-
Copyright (c) 2026 Ziyang Qin. All rights reserved.
No license is granted by this file.
Authors: Ziyang Qin
-/
import RicciFlowSharpEstimate.Geometry.SurfaceCovariantCommutator
import RicciFlowSharpEstimate.Geometry.TensorOrthonormalContractions

/-!
# The skew pairing of the actual second derivative of a one-form

On a surface, curvature determines the part of the second covariant derivative
antisymmetric in the first two slots.  Its pairing defect is exactly the squared
Gauss curvature times the squared norm of the original one-form.

The finite-index sum conversions adapt Ziyang Qin's historical
`TraceFreeTensorWeitzenbock.lean`.
-/

noncomputable section

namespace RicciFlowSharpEstimate.Geometry

open Bundle DifferentialGeometry DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Geometry.Operator DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Connection DifferentialGeometry.PDE.RicciFlow
open scoped Manifold ContDiff BigOperators

private theorem sum_finThree_functions (f : (Fin 3 → Fin 2) → Real) :
    (∑ v : Fin 3 → Fin 2, f v) =
      ∑ i : Fin 2, ∑ j : Fin 2, ∑ k : Fin 2, f ![i, j, k] := by
  classical
  let e : (Fin 3 → Fin 2) ≃ Fin 2 × (Fin 2 × Fin 2) :=
    (Fin.consEquiv (fun _ : Fin 3 => Fin 2)).symm.trans
      (Equiv.prodCongr (Equiv.refl (Fin 2)) (finTwoArrowEquiv (Fin 2)))
  calc
    (∑ v : Fin 3 → Fin 2, f v) =
        ∑ p : Fin 2 × (Fin 2 × Fin 2), f (e.symm p) := by
      refine Fintype.sum_equiv e _ _ fun v => ?_
      rw [e.symm_apply_apply]
    _ = ∑ i : Fin 2, ∑ jk : Fin 2 × Fin 2, f (e.symm (i, jk)) := by
      rw [Fintype.sum_prod_type]
    _ = ∑ i : Fin 2, ∑ j : Fin 2, ∑ k : Fin 2, f ![i, j, k] := by
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Fintype.sum_prod_type]
      refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
      congr 1

private theorem sum_finOne_functions (f : (Fin 1 → Fin 2) → Real) :
    (∑ v : Fin 1 → Fin 2, f v) = ∑ i : Fin 2, f ![i] := by
  classical
  let e : (Fin 1 → Fin 2) ≃ Fin 2 :=
    { toFun := fun v => v 0
      invFun := fun i => ![i]
      left_inv := by
        intro v
        funext q
        fin_cases q
        rfl
      right_inv := fun _ => rfl }
  refine Fintype.sum_equiv e _ _ fun v => ?_
  congr 1
  change v = ![v 0]
  funext q
  fin_cases q
  rfl

private theorem skew_pairing_finTwo (C : Fin 2 → Fin 2 → Fin 2 → Real) :
    (∑ i, ∑ j, ∑ k, C i j k ^ 2) -
        (∑ i, ∑ j, ∑ k, C j i k * C i j k) =
      (C 0 1 0 - C 1 0 0) ^ 2 + (C 0 1 1 - C 1 0 1) ^ 2 := by
  simp only [Fin.sum_univ_two]
  ring

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

private theorem skew_pairing_components (g : SmoothRiemannianMetric I M) (x : M)
    (B : Module.Basis (Fin 2) Real (TangentSpace I x))
    (hB : ∀ i j, g.inner x (B i) (B j) = if i = j then 1 else 0)
    (T : Tensor0SSpace (𝕜 := Real) (I := I) 3 x) :
    normSq0S g x 3 T -
        inner0S g x 3 (T.domDomCongr (Equiv.swap (0 : Fin 3) 1)) T =
      (T ![B 0, B 1, B 0] - T ![B 1, B 0, B 0]) ^ 2 +
        (T ![B 0, B 1, B 1] - T ![B 1, B 0, B 1]) ^ 2 := by
  classical
  have hvec (i j k : Fin 2) :
      (fun q : Fin 3 => B ((![i, j, k] : Fin 3 → Fin 2) q)) = ![B i, B j, B k] := by
    funext q
    fin_cases q <;> rfl
  have hswap (i j k : Fin 2) :
      T.domDomCongr (Equiv.swap (0 : Fin 3) 1) ![B i, B j, B k] =
        T ![B j, B i, B k] := by
    change T (fun q => (![B i, B j, B k] : Fin 3 → TangentSpace I x)
      ((Equiv.swap (0 : Fin 3) 1).symm q)) = _
    rw [Equiv.symm_swap]
    congr 1
    funext q
    fin_cases q <;> norm_num [Equiv.swap_apply_def]
  rw [normSq0S_eq_sum_sq_orthonormal g x 3 B hB,
    inner0S_eq_sum_orthonormal g x 3 B hB,
    sum_finThree_functions, sum_finThree_functions]
  simp_rw [hvec, hswap]
  exact skew_pairing_finTwo fun i j k => T ![B i, B j, B k]

private theorem one_form_norm_components (g : SmoothRiemannianMetric I M) (x : M)
    (B : Module.Basis (Fin 2) Real (TangentSpace I x))
    (hB : ∀ i j, g.inner x (B i) (B j) = if i = j then 1 else 0)
    (α : Tensor0SSpace (𝕜 := Real) (I := I) 1 x) :
    normSq0S g x 1 α = α (fun _ => B 0) ^ 2 + α (fun _ => B 1) ^ 2 := by
  have hvec (i : Fin 2) :
      (fun q : Fin 1 => B ((![i] : Fin 1 → Fin 2) q)) = fun _ => B i := by
    funext q
    fin_cases q
    rfl
  rw [normSq0S_eq_sum_sq_orthonormal g x 1 B hB, sum_finOne_functions]
  simp only [hvec, Fin.sum_univ_two]

variable [T2Space M] [I.Boundaryless]

private theorem second_derivative_skew_components
    (hdim : Module.finrank Real E = 2) (g : SmoothRiemannianMetric I M)
    (h : Tensor0SField (𝕜 := Real) (I := I) (M := M) (n := ∞) 1) (x : M)
    (B : Module.Basis (Fin 2) Real (TangentSpace I x))
    (hB : ∀ i j, g.inner x (B i) (B j) = if i = j then 1 else 0) :
    (metricNabla0S g (metricNabla0S g h) x ![B 0, B 1, B 0] -
      metricNabla0S g (metricNabla0S g h) x ![B 1, B 0, B 0] =
        metricScalarAt g x / 2 * h x (fun _ => B 1)) ∧
    (metricNabla0S g (metricNabla0S g h) x ![B 0, B 1, B 1] -
      metricNabla0S g (metricNabla0S g h) x ![B 1, B 0, B 1] =
        -(metricScalarAt g x / 2 * h x (fun _ => B 0))) := by
  classical
  have hslots (a b c : TangentSpace I x) :
      Fin.cons a (Fin.cons b (fun _ : Fin 1 => c)) = ![a, b, c] := by
    funext q
    fin_cases q <;> rfl
  have hu (a b : TangentSpace I x) :
      Function.update (fun _ : Fin 1 => a) 0 b = fun _ => b := by
    funext q
    fin_cases q
    simp
  have hsmul (c : Real) (a : TangentSpace I x) :
      h x (fun _ => c • a) = c * h x (fun _ => a) := by
    simpa only [hu, smul_eq_mul] using
      (h x).map_update_smul (fun _ : Fin 1 => a) 0 c a
  have hneg (a : TangentSpace I x) : h x (fun _ => -a) = -h x (fun _ => a) := by
    simpa only [neg_one_smul, neg_one_mul] using hsmul (-1) a
  have hcomm (k : Fin 2) := metricNabla0S_commutator g h x (B 0) (B 1) (fun _ => B k)
  simp only [hslots, Fin.sum_univ_one, hu,
    riemannOp_eq_scalar_div_two_of_finrank_eq_two g hdim] at hcomm
  constructor
  · simpa [hB, hsmul, hneg] using hcomm 0
  · simpa [hB, hsmul] using hcomm 1

/-- The skew pairing of the genuine second derivative of a surface one-form is
Gauss curvature squared times the squared norm of that same one-form. -/
theorem oneForm_secondDerivative_skew_pairing
    (hdim : Module.finrank Real E = 2) (g : SmoothRiemannianMetric I M)
    (h : Tensor0SField (𝕜 := Real) (I := I) (M := M) (n := ∞) 1) (x : M) :
    normSq0S g x 3 (metricNabla0S g (metricNabla0S g h) x) -
        inner0S g x 3
          ((metricNabla0S g (metricNabla0S g h) x).domDomCongr
            (Equiv.swap (0 : Fin 3) 1))
          (metricNabla0S g (metricNabla0S g h) x) =
      (metricScalarAt g x / 2) ^ 2 * normSq0S g x 1 (h x) := by
  obtain ⟨B, hB⟩ := exists_basis_two hdim g x
  obtain ⟨h0, h1⟩ := second_derivative_skew_components hdim g h x B hB
  rw [skew_pairing_components g x B hB, h0, h1, one_form_norm_components g x B hB]
  ring

end RicciFlowSharpEstimate.Geometry
