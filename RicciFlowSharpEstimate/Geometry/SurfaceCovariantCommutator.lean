/-
Copyright (c) 2026 Ziyang Qin. All rights reserved.
No license is granted by this file.
Authors: Ziyang Qin
-/
import RicciFlowSharpEstimate.Geometry.CanonicalDerivatives
import RicciFlowSharpEstimate.Geometry.TraceFreeSymmetric
import DifferentialGeometry.Geometry.Connection.RicciIdentity.Tensor0S.Formula
import DifferentialGeometry.Geometry.Curvature.DimensionTwo.RicciScalar

/-!
# The covariant derivative commutator on surfaces

The slot and contraction mechanics adapt Ziyang Qin's historical
`TraceFreeTensorWeitzenbock.lean`.  The curvature term here is computed for an
arbitrary covariant two-tensor directly from the native Ricci identity and
the native two-dimensional Riemann operator formula.
-/

noncomputable section

namespace RicciFlowSharpEstimate.Geometry

open Bundle DifferentialGeometry DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Geometry.Operator DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Tensor.RSTensor DifferentialGeometry.Tensor.RicciIdentity
open DifferentialGeometry.Tensor.Coordinates DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.Geometry.Connection
open scoped Manifold ContDiff BigOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
variable [IsManifold I ∞ M] [T2Space M]

private theorem actual_second_realizes {s : ℕ}
    (g : SmoothRiemannianMetric I M)
    (S : Tensor0SField (𝕜 := Real) (I := I) (M := M) (n := ∞) s) (x : M) :
    Nabla20SRealizesAt s (metricCov g) S (metricNabla0S g S) x
      (metricNabla0S g (metricNabla0S g S) x) := by
  constructor
  · intro y X slots
    exact canonicalDerivatives_first g S X y slots
  · intro X slots
    exact canonicalDerivatives_second g S X x slots

set_option maxHeartbeats 800000 in
-- Normalizing the native Ricci and curvature-section realizations needs a larger local budget.
/-- The native second metric derivative obeys the Ricci identity in every covariant rank. -/
theorem metricNabla0S_commutator [I.Boundaryless] {s : ℕ}
    (g : SmoothRiemannianMetric I M)
    (S : Tensor0SField (𝕜 := Real) (I := I) (M := M) (n := ∞) s)
    (x : M) (X Y : TangentSpace I x) (slots : Fin s → TangentSpace I x) :
    metricNabla0S g (metricNabla0S g S) x (Fin.cons X (Fin.cons Y slots)) -
        metricNabla0S g (metricNabla0S g S) x (Fin.cons Y (Fin.cons X slots)) =
      -∑ q : Fin s, S x (Function.update slots q
        (riemannOp (LeviCivita g) x X Y (slots q))) := by
  classical
  have hri := tensor0S_ricciIdentity_of_torsionFree (metricCov g)
    (leviCivitaConnectionOfMetric_contMDiffCovariantDerivativeLocally_one g)
    (metricRm13 g) S (metricNabla0S g S) (S x) (metricNabla0S g S x)
    (metricNabla0S g (metricNabla0S g S) x)
    (metricCurvatureSections g).rm13Realizes rfl rfl (actual_second_realizes g S x)
    (leviCivitaConnectionOfMetric_isTorsionFree g x)
  obtain ⟨Xs, hXs⟩ := ContMDiffSection.exists_eq_at
    (I := I) (F := E) (V := TangentSpace I) (n := (⊤ : ℕ∞)) x X
  obtain ⟨Ys, hYs⟩ := ContMDiffSection.exists_eq_at
    (I := I) (F := E) (V := TangentSpace I) (n := (⊤ : ℕ∞)) x Y
  choose V hV using fun q : Fin s => ContMDiffSection.exists_eq_at
    (I := I) (F := E) (V := TangentSpace I) (n := (⊤ : ℕ∞)) x (slots q)
  have hcurv := curvatureAction0SAt_eq_neg_sum_connectionRiemannCurvature
    (cov := metricCov g) (Rm13 := metricRm13 g) (S x) Xs Ys V
    (metricCurvatureSections g).rm13Realizes
  have hop (q : Fin s) :
      connectionRiemannCurvatureField (metricCov g) Xs Ys (V q) x =
        riemannOp (LeviCivita g) x (Xs x) (Ys x) (V q x) := by
    exact (riemannOp_apply_smooth (LeviCivita g)
      Xs.contMDiff Ys.contMDiff (V q).contMDiff).symm
  change curvatureAction0SAt (metricRm13 g) (S x) (Xs x) (Ys x)
    (fun q => V q x) = -∑ q : Fin s, S x
      (Function.update (fun q => V q x) q
        (connectionRiemannCurvatureField (metricCov g) Xs Ys (V q) x)) at hcurv
  simp only [hop, hXs, hYs, hV] at hcurv
  exact (hri X Y slots).trans hcurv

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

omit [T2Space M] in
private theorem trace_two (g : SmoothRiemannianMetric I M) {x : M}
    (B : Module.Basis (Fin 2) Real (TangentSpace I x))
    (hON : ∀ i j, g.inner x (B i) (B j) = if i = j then 1 else 0)
    (T : Tensor0SSpace (𝕜 := Real) (I := I) 2 x) :
    metricTracePair0SAt g T = T ![B 0, B 0] + T ![B 1, B 1] := by
  rw [metricTracePair0SAt_eq_sum_basis g B identityInvMetric
    (metricInverseInBasis_identity_of_orthonormal g B hON)]
  simp only [Fin.sum_univ_two, identityInvMetric, diagonalInvMetric, ite_true,
    zero_ne_one, one_ne_zero, ite_false, one_mul, zero_mul, zero_add, add_zero]
  congr 2 <;> funext q <;> fin_cases q <;> rfl

omit [T2Space M] in
private theorem trace_first_two {s : ℕ} (g : SmoothRiemannianMetric I M) {x : M}
    (B : Module.Basis (Fin 2) Real (TangentSpace I x))
    (hON : ∀ i j, g.inner x (B i) (B j) = if i = j then 1 else 0)
    (T : Tensor0SField (𝕜 := Real) (I := I) (M := M) (n := ∞) (s + 2))
    (v : Fin s → TangentSpace I x) :
    metricTraceFirstTwoField g T x v =
      ∑ i : Fin 2, T x (Fin.cons (B i) (Fin.cons (B i) v)) := by
  rw [metricTraceFirstTwoField_apply, metricTraceFirstTwo0STensor_apply,
    metricTraceFirstTwo0SAt_eq_sum_basis g B identityInvMetric
      (metricInverseInBasis_identity_of_orthonormal g B hON)]
  simp only [metricTrace0S2InBasis, identityInvMetric, diagonalInvMetric,
    Fin.sum_univ_two, ite_true, zero_ne_one, one_ne_zero, ite_false,
    one_mul, zero_mul, zero_add, add_zero]
  rfl

private theorem nabla_domDomCongr {s s' : ℕ}
    (g : SmoothRiemannianMetric I M) (e : Fin s ≃ Fin s')
    (S : Tensor0SField (𝕜 := Real) (I := I) (M := M) (n := ∞) s) :
    metricNabla0S g (Tensor0SField.domDomCongr ∞ e S) =
      Tensor0SField.domDomCongr ∞ (frontExtendEquiv e) (metricNabla0S g S) := by
  exact (canonicalDerivatives_first g _).unique
    (totalNabla0SRealizes_domDomCongr (metricCov g) e S _
      (canonicalDerivatives_first g S))

private theorem nabla_trace {s : ℕ} (g : SmoothRiemannianMetric I M)
    (S : Tensor0SField (𝕜 := Real) (I := I) (M := M) (n := ∞) (s + 2)) :
    metricNabla0S g (metricTraceFirstTwoField g S) =
      metricTraceFirstTwoField g
        (Tensor0SField.domDomCongr ∞ (traceNablaShuffle s) (metricNabla0S g S)) := by
  exact (canonicalDerivatives_first g _).unique
    (nablaRealizes_metricTraceFirstTwo (metricCov g) g
      (leviCivitaConnectionOfMetric_isMetricCompatible g) S _
      (canonicalDerivatives_first g S))

private theorem nabla_div_component (g : SmoothRiemannianMetric I M)
    (S : Tensor0SField (𝕜 := Real) (I := I) (M := M) (n := ∞) 2)
    (x : M) (B : Module.Basis (Fin 2) Real (TangentSpace I x))
    (hON : ∀ i j, g.inner x (B i) (B j) = if i = j then 1 else 0)
    (j k : Fin 2) :
    metricNabla0S g (covDiv0SField g S) x ![B j, B k] =
      ∑ i : Fin 2, metricNabla0S g (metricNabla0S g S) x ![B j, B i, B i, B k] := by
  unfold covDiv0SField
  rw [nabla_trace, trace_first_two g B hON]
  refine Finset.sum_congr rfl fun i _ => ?_
  change (metricNabla0S g (metricNabla0S g S) x).domDomCongr
    (traceNablaShuffle 1) ![B i, B i, B j, B k] = _
  rw [Tensor0SSpace.domDomCongr_apply]
  congr 1
  funext q
  fin_cases q <;> rfl

private theorem nabla_swap_component (g : SmoothRiemannianMetric I M)
    (T : Tensor0SField (𝕜 := Real) (I := I) (M := M) (n := ∞) 3)
    (x : M) (a b c d : TangentSpace I x) :
    metricNabla0S g (Tensor0SField.domDomCongr ∞ (Equiv.swap (0 : Fin 3) 1) T) x
        ![a, b, c, d] =
      metricNabla0S g T x ![a, c, b, d] := by
  rw [nabla_domDomCongr]
  change (metricNabla0S g T x).domDomCongr
    (frontExtendEquiv (Equiv.swap (0 : Fin 3) 1)) ![a, b, c, d] = _
  rw [Tensor0SSpace.domDomCongr_apply]
  congr 1
  funext q
  fin_cases q <;> rfl

private theorem div_swap_component (g : SmoothRiemannianMetric I M)
    (S : Tensor0SField (𝕜 := Real) (I := I) (M := M) (n := ∞) 2)
    (x : M) (B : Module.Basis (Fin 2) Real (TangentSpace I x))
    (hON : ∀ i j, g.inner x (B i) (B j) = if i = j then 1 else 0)
    (j k : Fin 2) :
    covDiv0SField g (Tensor0SField.domDomCongr ∞ (Equiv.swap (0 : Fin 3) 1)
        (metricNabla0S g S)) x ![B j, B k] =
      ∑ i : Fin 2, metricNabla0S g (metricNabla0S g S) x ![B i, B j, B i, B k] := by
  change metricTraceFirstTwoField g _ x ![B j, B k] = _
  rw [trace_first_two g B hON]
  refine Finset.sum_congr rfl fun i _ => ?_
  exact nabla_swap_component g _ x _ _ _ _

private theorem curvature_contraction [I.Boundaryless]
    (hdim : Module.finrank Real E = 2) (g : SmoothRiemannianMetric I M)
    (S : Tensor0SField (𝕜 := Real) (I := I) (M := M) (n := ∞) 2)
    (x : M) (B : Module.Basis (Fin 2) Real (TangentSpace I x))
    (hON : ∀ i j, g.inner x (B i) (B j) = if i = j then 1 else 0)
    (j k : Fin 2) :
    (∑ i : Fin 2, -(∑ q : Fin 2,
      S x (Function.update ![B i, B k] q
        (riemannOp (LeviCivita g) x (B i) (B j) (![B i, B k] q))))) =
      metricScalarAt g x * ahlforsPart g S x ![B j, B k] := by
  classical
  have hu0 (a b c : TangentSpace I x) :
      Function.update ![a, b] (0 : Fin 2) c = ![c, b] := by
    funext q
    fin_cases q <;> simp
  have hu1 (a b c : TangentSpace I x) :
      Function.update ![a, b] (1 : Fin 2) c = ![a, c] := by
    funext q
    fin_cases q <;> simp
  have hz0 (a : TangentSpace I x) : S x ![0, a] = 0 :=
    (S x).map_coord_zero 0 rfl
  have hz1 (a : TangentSpace I x) : S x ![a, 0] = 0 :=
    (S x).map_coord_zero 1 rfl
  have hn0 (a b : TangentSpace I x) : S x ![-a, b] = -S x ![a, b] := by
    have h := (S x).map_update_smul ![a, b] 0 (-1 : Real) a
    simpa only [neg_one_smul, smul_eq_mul, neg_one_mul, hu0] using h
  have hn1 (a b : TangentSpace I x) : S x ![a, -b] = -S x ![a, b] := by
    have h := (S x).map_update_smul ![a, b] 1 (-1 : Real) b
    simpa only [neg_one_smul, smul_eq_mul, neg_one_mul, hu1] using h
  have hswap (a b : TangentSpace I x) :
      (fun q => (![a, b] : Fin 2 → TangentSpace I x) (Equiv.swap 0 1 q)) =
        ![b, a] := by
    funext q
    fin_cases q <;> simp
  rw [ahlforsPart_apply_of_finrank_eq_two hdim, trace_two g B hON]
  simp only [Tensor0SSpace.sub_apply, Tensor0SSpace.smul_apply,
    Tensor0SSpace.add_apply, smul_eq_mul, metricTensor0S_apply]
  simp_rw [riemannOp_eq_scalar_div_two_of_finrank_eq_two g hdim]
  fin_cases j <;> fin_cases k <;>
    simp [Fin.sum_univ_two, hON, (S x).map_update_smul, hu0, hu1,
      hz0, hz1, hn0, hn1, hswap] <;> ring

/-- On a surface, the contracted gradient-slot commutator is scalar curvature
 times the Ahlfors part of the original arbitrary covariant two-tensor. -/
theorem covDiv0SField_gradSlotSwap_commutator_of_finrank_eq_two [I.Boundaryless]
    (hdim : Module.finrank Real E = 2) (g : SmoothRiemannianMetric I M)
    (S : Tensor0SField (𝕜 := Real) (I := I) (M := M) (n := ∞) 2) :
    covDiv0SField g
        (MultilinearSection.domDomCongr (𝕜 := Real) (F := E) (IB := I)
          (E := TangentSpace I) ∞ (Equiv.swap (0 : Fin 3) 1) (metricNabla0S g S)) =
      metricNabla0S g (covDiv0SField g S) +
        tensor0SFieldSmulByFun ∞ (metricScalarAt g) (metricScalar_smooth g)
          (ahlforsPart g S) := by
  classical
  refine DFunLike.ext _ _ fun x => ?_
  obtain ⟨B, hON⟩ := exists_basis_two hdim g x
  apply ext0S_basis (I := I) B
  intro idx
  simp only [component0S_apply]
  have hv : (fun q : Fin 2 => B (idx q)) = ![B (idx 0), B (idx 1)] := by
    funext q
    fin_cases q <;> rfl
  rw [hv]
  change covDiv0SField g (Tensor0SField.domDomCongr ∞ (Equiv.swap (0 : Fin 3) 1)
      (metricNabla0S g S)) x ![B (idx 0), B (idx 1)] =
    metricNabla0S g (covDiv0SField g S) x ![B (idx 0), B (idx 1)] +
      metricScalarAt g x * ahlforsPart g S x ![B (idx 0), B (idx 1)]
  rw [div_swap_component g S x B hON, nabla_div_component g S x B hON,
    ← curvature_contraction hdim g S x B hON]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  have h := metricNabla0S_commutator g S x (B i) (B (idx 0)) ![B i, B (idx 1)]
  have hslots (a b c d : TangentSpace I x) :
      Fin.cons a (Fin.cons b ![c, d]) = ![a, b, c, d] := by
    funext q
    fin_cases q <;> rfl
  rw [hslots, hslots] at h
  linarith only [h]

end RicciFlowSharpEstimate.Geometry
