/-
Copyright (c) 2026 Ziyang Qin. All rights reserved.
No license is granted by this file.
Authors: Ziyang Qin
-/
import DifferentialGeometry.Geometry.Curvature.Coordinates.MetricJet.ChartBridge
import DifferentialGeometry.Geometry.Curvature.DimensionTwo.RicciScalar
import Mathlib.Algebra.Group.Pi.Units

/-!
# Intrinsic curvature from radial diagonal metric jets

A genuine chart two-jet of a two-dimensional metric determines its scalar
curvature. The proof contracts the universal Ricci polynomial, applies the
released local chart bridge, and identifies Ricci with half the actual scalar
curvature times the metric. Chart regularity is derived locally from smoothness.

Adapted from Ziyang Qin's historical `RotationalDiagonalCurvatureJet.lean`.
-/

noncomputable section

namespace RicciFlowSharpEstimate.Geometry

open Bundle Manifold Set
open DifferentialGeometry DifferentialGeometry.Analysis
open DifferentialGeometry.Geometry DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Tensor.Coordinates
open scoped Manifold Topology ContDiff Matrix

private theorem jetRicci_zero_zero_of_radialDiagonal
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (basis : Fin 2 → V)
    (p : MatJet V 2)
    (E G E₁ G₁ E₂ G₂ : ℝ)
    (hinv :
      ∀ i j : Fin 2,
        (Matrix.of p.1)⁻¹ i j =
          if i = 0 ∧ j = 0 then 1 / E
          else if i = 1 ∧ j = 1 then 1 / G else 0)
    (hd1 :
      ∀ m i j : Fin 2,
        (p.2.1 (basis m)) i j =
          if m = 0 then
            if i = 0 ∧ j = 0 then E₁
            else if i = 1 ∧ j = 1 then G₁ else 0
          else 0)
    (hd2 :
      ∀ m n i j : Fin 2,
        (p.2.2 (basis m) (basis n)) i j =
          if m = 0 ∧ n = 0 then
            if i = 0 ∧ j = 0 then E₂
            else if i = 1 ∧ j = 1 then G₂ else 0
          else 0) :
    jetRicci basis p 0 0 =
      -G₂ / (2 * G) + G₁ ^ 2 / (4 * G ^ 2) +
        E₁ * G₁ / (4 * E * G) := by
  simp only [jetRicci, jetRiemann, jetChristoffelDeriv,
    jetChristoffel, Fin.sum_univ_two]
  simp [hinv, hd1, hd2]
  ring

private theorem inverse_of_radialDiagonal
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (p : MatJet V 2)
    (E G : ℝ) (hE : E ≠ 0) (hG : G ≠ 0)
    (hval :
      ∀ i j : Fin 2,
        p.1 i j =
          if i = 0 ∧ j = 0 then E
          else if i = 1 ∧ j = 1 then G else 0) :
    ∀ i j : Fin 2,
      (Matrix.of p.1)⁻¹ i j =
        if i = 0 ∧ j = 0 then 1 / E
        else if i = 1 ∧ j = 1 then 1 / G else 0 := by
  let d : Fin 2 → ℝ := fun i => if i = 0 then E else G
  have hp : Matrix.of p.1 = Matrix.diagonal d := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [hval, d]
  have hdUnit : IsUnit d := by
    rw [Pi.isUnit_iff]
    intro i
    fin_cases i <;>
      simp [d, hE, hG]
  rw [hp, Matrix.inv_diagonal]
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp only [Matrix.diagonal_apply]
  · rw [← hdUnit.unit_spec, Ring.inverse_unit,
      IsUnit.val_inv_apply]
    simp [d, one_div]
  · simp
  · simp
  · rw [← hdUnit.unit_spec, Ring.inverse_unit,
      IsUnit.val_inv_apply]
    simp [d, one_div]

/-- `00` Ricci formula with the inverse matrix discharged from the diagonal
metric value. -/
private theorem jetRicci_zero_zero_of_radialDiagonal'
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (basis : Fin 2 → V)
    (p : MatJet V 2)
    (E G E₁ G₁ E₂ G₂ : ℝ)
    (hE : E ≠ 0) (hG : G ≠ 0)
    (hval :
      ∀ i j : Fin 2,
        p.1 i j =
          if i = 0 ∧ j = 0 then E
          else if i = 1 ∧ j = 1 then G else 0)
    (hd1 :
      ∀ m i j : Fin 2,
        (p.2.1 (basis m)) i j =
          if m = 0 then
            if i = 0 ∧ j = 0 then E₁
            else if i = 1 ∧ j = 1 then G₁ else 0
          else 0)
    (hd2 :
      ∀ m n i j : Fin 2,
        (p.2.2 (basis m) (basis n)) i j =
          if m = 0 ∧ n = 0 then
            if i = 0 ∧ j = 0 then E₂
            else if i = 1 ∧ j = 1 then G₂ else 0
          else 0) :
    jetRicci basis p 0 0 =
      -G₂ / (2 * G) + G₁ ^ 2 / (4 * G ^ 2) +
        E₁ * G₁ / (4 * E * G) := by
  exact jetRicci_zero_zero_of_radialDiagonal basis p
    E G E₁ G₁ E₂ G₂
    (inverse_of_radialDiagonal p E G hE hG hval) hd1 hd2

/-- A dimension-indexed wrapper for
`jetRicci_zero_zero_of_radialDiagonal'`.  It is useful when the matrix
size is written as the finrank of a model space and is propositionally,
rather than definitionally, equal to two. -/
private theorem jetRicci_zero_zero_of_radialDiagonal_of_eq_two
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {n : ℕ} [NeZero n]
    (hn : n = 2)
    (basis : Fin n → V)
    (p : MatJet V n)
    (E G E₁ G₁ E₂ G₂ : ℝ)
    (hE : E ≠ 0) (hG : G ≠ 0)
    (hval :
      ∀ i j : Fin n,
        p.1 i j =
          if i = 0 ∧ j = 0 then E
          else if i = 1 ∧ j = 1 then G else 0)
    (hd1 :
      ∀ m i j : Fin n,
        (p.2.1 (basis m)) i j =
          if m = 0 then
            if i = 0 ∧ j = 0 then E₁
            else if i = 1 ∧ j = 1 then G₁ else 0
          else 0)
    (hd2 :
      ∀ m k i j : Fin n,
        (p.2.2 (basis m) (basis k)) i j =
          if m = 0 ∧ k = 0 then
            if i = 0 ∧ j = 0 then E₂
            else if i = 1 ∧ j = 1 then G₂ else 0
          else 0) :
    jetRicci basis p 0 0 =
      -G₂ / (2 * G) + G₁ ^ 2 / (4 * G ^ 2) +
        E₁ * G₁ / (4 * E * G) := by
  subst n
  exact jetRicci_zero_zero_of_radialDiagonal'
    basis p E G E₁ G₁ E₂ G₂ hE hG hval hd1 hd2

private local instance : NeZero (Module.finrank ℝ (EuclideanSpace ℝ (Fin 2))) :=
  ⟨by simp⟩

/-- An actual radial diagonal chart two-jet computes scalar curvature.
The value component supplies the metric coefficient used to recover scalar
curvature from the `00` Ricci component. Only local chart interior data is needed. -/
theorem metricScalarAt_eq_radialDiagonalJet
    {H : Type*} [TopologicalSpace H]
    {I : ModelWithCorners ℝ (EuclideanSpace ℝ (Fin 2)) H}
    [I.Boundaryless]
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M] [T2Space M]
    (g : SmoothRiemannianMetric I M) (α x : M)
    (hx : x ∈ chartLeviCivitaGoodSet (I := I) α)
    (E G E₁ G₁ E₂ G₂ : ℝ)
    (hval :
      ∀ i j :
          Fin (Module.finrank ℝ
            (EuclideanSpace ℝ (Fin 2))),
        (jet2 (chartGramPi (I := I) g α)
            (extChartAt I α x)).1 i j =
          if i = 0 ∧ j = 0 then E
          else if i = 1 ∧ j = 1 then G else 0)
    (hd1 :
      ∀ m i j :
          Fin (Module.finrank ℝ
            (EuclideanSpace ℝ (Fin 2))),
        (jet2 (chartGramPi (I := I) g α)
            (extChartAt I α x)).2.1
            (chartModelBasis
              (EuclideanSpace ℝ (Fin 2)) m) i j =
          if m = 0 then
            if i = 0 ∧ j = 0 then E₁
            else if i = 1 ∧ j = 1 then G₁ else 0
          else 0)
    (hd2 :
      ∀ m n i j :
          Fin (Module.finrank ℝ
            (EuclideanSpace ℝ (Fin 2))),
        (jet2 (chartGramPi (I := I) g α)
            (extChartAt I α x)).2.2
            (chartModelBasis
              (EuclideanSpace ℝ (Fin 2)) m)
            (chartModelBasis
              (EuclideanSpace ℝ (Fin 2)) n) i j =
          if m = 0 ∧ n = 0 then
            if i = 0 ∧ j = 0 then E₂
            else if i = 1 ∧ j = 1 then G₂ else 0
          else 0)
    : metricScalarAt (I := I) g x =
      2 * ((-G₂ / (2 * G) + G₁ ^ 2 / (4 * G ^ 2) +
        E₁ * G₁ / (4 * E * G)) / E) := by
  have hy : extChartAt I α x ∈ interior (extChartAt I α).target :=
    chartLeviCivitaGoodSet_extChartAt_mem_interior (I := I) hx
  have hxsrc : x ∈ (extChartAt I α).source :=
    chartLeviCivitaGoodSet_mem_extChartAt_source (I := I) hx
  have hxbase : x ∈
      (trivializationAt (EuclideanSpace ℝ (Fin 2)) (TangentSpace I) α).baseSet :=
    chartLeviCivitaGoodSet_mem_baseSet (I := I) hx
  let bas := chartBasisFamily (I := I) α hxbase
  have hmetric (i j : Fin (Module.finrank ℝ (EuclideanSpace ℝ (Fin 2)))) :
      g.inner x (bas i) (bas j) =
        if i = 0 ∧ j = 0 then E else if i = 1 ∧ j = 1 then G else 0 := by
    have hvalue := hval i j
    simp only [jet2] at hvalue
    rw [chartGramPi_apply, chartGramOnE_def,
      (extChartAt I α).left_inv hxsrc] at hvalue
    simpa only [bas, chartBasisFamily_apply, chartGramMatrix_apply] using hvalue
  have hEpos : 0 < E := by
    simpa [hmetric] using g.pos x (bas 0) (bas.ne_zero 0)
  have hGpos : 0 < G := by
    simpa [hmetric] using g.pos x (bas 1) (bas.ne_zero 1)
  have hE : E ≠ 0 := hEpos.ne'
  have hGne : G ≠ 0 := hGpos.ne'
  have hGramSmooth {y : EuclideanSpace ℝ (Fin 2)}
      (hy' : y ∈ interior (extChartAt I α).target) :
      ContDiffAt ℝ ∞ (chartGramPi (I := I) g α) y := by
    refine contDiffAt_pi.mpr (fun i => contDiffAt_pi.mpr (fun j => ?_))
    exact ((chartGramOnE_contDiffOn (I := I) g α i j).mono
      interior_subset).contDiffAt (isOpen_interior.mem_nhds hy')
  have hGramDiff := (hGramSmooth hy).differentiableAt (by simp)
  have hGramDiffNear : ∀ᶠ y in 𝓝 (extChartAt I α x),
      DifferentiableAt ℝ (chartGramPi (I := I) g α) y := by
    filter_upwards [isOpen_interior.mem_nhds hy] with y hy'
    exact (hGramSmooth hy').differentiableAt (by simp)
  have hGramFDerivDiff : DifferentiableAt ℝ
      (fun y => fderiv ℝ (chartGramPi (I := I) g α) y) (extChartAt I α x) :=
    ((hGramSmooth hy).fderiv_right (m := (∞ : WithTop ℕ∞))
      (by simp)).differentiableAt (by simp)
  let p :=
    jet2 (chartGramPi (I := I) g α)
      (extChartAt I α x)
  have hdim :
      Module.finrank ℝ
          (EuclideanSpace ℝ (Fin 2)) = 2 := by
    simp
  have hjet :
      jetRicci
          (chartModelBasis
            (EuclideanSpace ℝ (Fin 2))) p 0 0 =
        -G₂ / (2 * G) + G₁ ^ 2 / (4 * G ^ 2) +
          E₁ * G₁ / (4 * E * G) := by
    exact
      jetRicci_zero_zero_of_radialDiagonal_of_eq_two
        hdim
        (chartModelBasis
          (EuclideanSpace ℝ (Fin 2))) p
        E G E₁ G₁ E₂ G₂ hE hGne hval hd1 hd2
  have hchart :
      chartRicciTensor (I := I) g α 0 0
          (extChartAt I α x) =
        -G₂ / (2 * G) + G₁ ^ 2 / (4 * G ^ 2) +
          E₁ * G₁ / (4 * E * G) := by
    calc
      chartRicciTensor (I := I) g α 0 0
          (extChartAt I α x) =
          jetRicci
            (chartModelBasis
              (EuclideanSpace ℝ (Fin 2))) p 0 0 :=
        chartRicci_eq_jet g α hy hGramDiff
          hGramDiffNear hGramFDerivDiff 0 0
      _ = _ := hjet
  let V := chartBasisVecFiber (I := I) α 0 x
  have hinner : g.inner x V V = E := by
    have hxsrc : x ∈ (extChartAt I α).source :=
      chartLeviCivitaGoodSet_mem_extChartAt_source
        (I := I) hx
    have hvalue := hval 0 0
    simp only [jet2] at hvalue
    rw [chartGramPi_apply, chartGramOnE_def,
      (extChartAt I α).left_inv hxsrc] at hvalue
    simpa [chartGramMatrix_apply] using hvalue
  have hRicci :
      ricciTensor (I := I) g x V V =
        -G₂ / (2 * G) + G₁ ^ 2 / (4 * G ^ 2) +
          E₁ * G₁ / (4 * E * G) := by
    rw [ricciTensor_chartBasisVec_alpha_eq
      g α 0 0 hx]
    exact hchart
  have hRicciScalar :=
    ricciTensor_eq_half_metricScalarAt_mul_inner_of_finrank_eq_two
      (I := I) g hdim x V V
  rw [hRicci, hinner] at hRicciScalar
  have hhalf : metricScalarAt (I := I) g x / 2 =
      (-G₂ / (2 * G) + G₁ ^ 2 / (4 * G ^ 2) +
        E₁ * G₁ / (4 * E * G)) / E :=
    (eq_div_iff hE).2 hRicciScalar.symm
  calc
    metricScalarAt (I := I) g x = 2 * (metricScalarAt (I := I) g x / 2) := by ring
    _ = _ := by rw [hhalf]

end RicciFlowSharpEstimate.Geometry
