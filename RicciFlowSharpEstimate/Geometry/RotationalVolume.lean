/-
Copyright (c) 2026 Ziyang Qin. All rights reserved.
No license is granted by this file.
Authors: Ziyang Qin
-/
import RicciFlowSharpEstimate.Geometry.BalancedSphereMetric
import RicciFlowSharpEstimate.Geometry.SphereHeightIntegral
import RicciFlowSharpEstimate.LinearAlgebra.RankOneDeterminant
import DifferentialGeometry.Analysis.Integration.Measure.Chart.Density
import DifferentialGeometry.Analysis.Integration.Measure.Riemannian.Invariance
import DifferentialGeometry.Analysis.Integration.Measure.Riemannian.Basic
import DifferentialGeometry.Geometry.Operator.Gradient.Basic
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
# Volume density of the genuine rotational sphere metric

The actual Riemannian volume of the reconstructed metric is round volume weighted
by its original profile at the actual sphere height. The determinant calculation
uses the ambient tangent projection of the height gradient.

Adapted from Ziyang Qin's historical `RotationalSphereVolumeDensity.lean`.
-/

noncomputable section

namespace RicciFlowSharpEstimate.Geometry

open Bundle DifferentialGeometry DifferentialGeometry.Geometry
open DifferentialGeometry.Geometry.Operator DifferentialGeometry.Tensor.Coordinates
open DifferentialGeometry.Integral.Measure DifferentialGeometry.Integral.DivergenceTheorem
open MeasureTheory Metric
open scoped ENNReal Manifold RealInnerProductSpace

local instance : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 2 + 1) :=
  ⟨finrank_euclideanSpace_fin⟩

private local instance : MeasurableSpace RotationalSphere := borel RotationalSphere
private local instance : BorelSpace RotationalSphere := ⟨rfl⟩

/-- The actual round gradient of height has squared length `1 - height²`,
including at the poles. -/
theorem round_grad_sphereHeight_inner_self (x : RotationalSphere) :
    HeightMetricCoefficients.round.inner x
      (gradFun HeightMetricCoefficients.round sphereHeight x)
      (gradFun HeightMetricCoefficients.round sphereHeight x) = 1 - sphereHeight x ^ 2 := by
  let e : EuclideanSpace ℝ (Fin 3) := EuclideanSpace.single (2 : Fin 3) (1 : ℝ)
  let P : EuclideanSpace ℝ (Fin 3) := e - sphereHeight x • (x : EuclideanSpace ℝ (Fin 3))
  have hex : ⟪e, (x : EuclideanSpace ℝ (Fin 3))⟫ = sphereHeight x := rfl
  have hxe : ⟪(x : EuclideanSpace ℝ (Fin 3)), e⟫ = sphereHeight x := by
    rw [real_inner_comm, hex]
  have hee : ⟪e, e⟫ = 1 := by simp [e]
  have hxx : ⟪(x : EuclideanSpace ℝ (Fin 3)), (x : EuclideanSpace ℝ (Fin 3))⟫ = 1 := by
    rw [real_inner_self_eq_norm_sq, norm_eq_of_mem_sphere x]
    norm_num
  have hP : P ∈ (ℝ ∙ (x : EuclideanSpace ℝ (Fin 3)))ᗮ := by
    apply Submodule.mem_orthogonal_singleton_iff_inner_right.mpr
    simp only [P, inner_sub_right, real_inner_smul_right, hxe, hxx, mul_one, sub_self]
  let Z : TangentSpace (𝓡 2) x := (dInclEquiv (n := 2) x).symm ⟨P, hP⟩
  have hZ : dIncl (n := 2) x Z = P := by
    rw [← dInclEquiv_coe (n := 2) x]
    exact congrArg Subtype.val ((dInclEquiv (n := 2) x).apply_symm_apply ⟨P, hP⟩)
  have hGrad : Z = gradFun HeightMetricCoefficients.round sphereHeight x := by
    apply metricFlatLinear_injective HeightMetricCoefficients.round x
    ext v
    change HeightMetricCoefficients.round.inner x Z v =
      HeightMetricCoefficients.round.inner x
        (gradFun HeightMetricCoefficients.round sphereHeight x) v
    rw [inner_gradFun, roundMetric_inner, hZ]
    have hv : ⟪(x : EuclideanSpace ℝ (Fin 3)), dIncl (n := 2) x v⟫ = 0 := by
      apply Submodule.mem_orthogonal_singleton_iff_inner_right.mp
      rw [← range_mvfderiv_subtypeVal (n := 2) x]
      exact ⟨v, rfl⟩
    rw [show sphereHeight = ⇑(innerCoordFun (n := 2) e) from rfl,
      mfderiv_innerCoordFun]
    simp only [P, inner_sub_left, real_inner_smul_left, hv, mul_zero, sub_zero]
  rw [← hGrad, roundMetric_inner, hZ]
  simp only [P, inner_sub_left, inner_sub_right, real_inner_smul_left,
    real_inner_smul_right, hee, hex, hxe, hxx]
  ring

namespace RotationalProfile.PoleData

private def chartIndexEquiv :
    Fin (Module.finrank ℝ (EuclideanSpace ℝ (Fin 2))) ≃ Fin 2 :=
  finCongr finrank_euclideanSpace_fin

/-- The exact Gram determinant ratio of the reconstructed metric and round metric. -/
theorem det_chartGramMatrix_metric (D : PoleData) (α x : RotationalSphere)
    (hx : x ∈ (trivializationAt (EuclideanSpace ℝ (Fin 2))
      (TangentSpace (𝓡 2)) α).baseSet) :
    (chartGramMatrix D.metric α x).det = D.a (sphereHeight x) ^ 2 *
      (chartGramMatrix HeightMetricCoefficients.round α x).det := by
  let B := (chartBasisFamily (I := 𝓡 2) α hx).reindex chartIndexEquiv
  let Z := gradFun HeightMetricCoefficients.round sphereHeight x
  let G := metricFlatLinear HeightMetricCoefficients.round x
  have hB (i : Fin 2) : B i = chartBasisVecFiber (I := 𝓡 2) α (chartIndexEquiv.symm i) x := by
    simp only [B, Module.Basis.reindex_apply, chartBasisFamily_apply]
  have hu (i : Fin 2) : G Z (B i) = heightOneForm x (fun _ : Fin 1 => B i) := by
    change HeightMetricCoefficients.round.inner x Z (B i) = _
    rw [inner_gradFun, heightOneForm_apply, mvfderiv_real_eq_mfderiv]
    rfl
  have hZZ : G Z Z = 1 - sphereHeight x ^ 2 := round_grad_sphereHeight_inner_self x
  have hdet := LinearMap.det_smul_add_rankOne_gram_fin_two G
    (HeightMetricCoefficients.round.symm x) B Z
    (D.b (sphereHeight x)) (D.c (sphereHeight x) / D.b (sphereHeight x))
  have hmetric : (Matrix.of fun i j =>
      D.b (sphereHeight x) * G (B i) (B j) + D.c (sphereHeight x) / D.b (sphereHeight x) *
        (G Z (B i) * G Z (B j))) =
      (chartGramMatrix D.metric α x).submatrix chartIndexEquiv.symm chartIndexEquiv.symm := by
    ext i j
    rw [Matrix.of_apply, hu i, hu j, hB i, hB j]
    exact (D.metric_inner x _ _).symm
  have hround : (Matrix.of fun i j => G (B i) (B j)) =
      (chartGramMatrix HeightMetricCoefficients.round α x).submatrix
        chartIndexEquiv.symm chartIndexEquiv.symm := by
    ext i j
    rw [Matrix.of_apply, hB i, hB j]
    rfl
  rw [hmetric, hround, Matrix.det_submatrix_equiv_self,
    Matrix.det_submatrix_equiv_self, hZZ,
    D.radial_identity _ (sphereHeight_mem_Icc x)] at hdet
  rw [hdet]
  field_simp [(D.b_pos _ (sphereHeight_mem_Icc x)).ne']

/-- The local volume density is the original profile times the round density. -/
theorem chartDensity_metric (D : PoleData) (α x : RotationalSphere)
    (hx : x ∈ (trivializationAt (EuclideanSpace ℝ (Fin 2))
      (TangentSpace (𝓡 2)) α).baseSet) :
    chartDensity D.metric α x = D.a (sphereHeight x) *
      chartDensity HeightMetricCoefficients.round α x := by
  unfold chartDensity
  rw [det_chartGramMatrix_metric D α x hx,
    Real.sqrt_mul (sq_nonneg (D.a (sphereHeight x))),
    Real.sqrt_sq (D.a_pos _ (sphereHeight_mem_Icc x)).le]

private theorem measurable_profileDensity (D : PoleData) :
    Measurable (fun x : RotationalSphere => ENNReal.ofReal (D.a (sphereHeight x))) :=
  ENNReal.measurable_ofReal.comp
    (D.a_contDiff.comp_contMDiff sphereHeight_contMDiff).continuous.measurable

/-- Measure-level form of the balanced volume identity, for an arbitrary
smooth partition of unity used in the construction of the Riemannian
measure. -/
private theorem riemannianMeasure_metric_eq_withDensity
    (D : PoleData)
    (ρ : SmoothPartitionOfUnity
      RotationalSphere (𝓡 2) RotationalSphere Set.univ) :
    riemannianMeasure D.metric ρ =
      (riemannianMeasure
          HeightMetricCoefficients.round ρ).withDensity
        (fun x : RotationalSphere =>
          ENNReal.ofReal (D.a (sphereHeight x))) := by
  set A : RotationalSphere → ℝ≥0∞ :=
    fun x => ENNReal.ofReal (D.a (sphereHeight x)) with hAdef
  have hA : Measurable A := measurable_profileDensity D
  have key :
      ∀ (F : RotationalSphere → ℝ≥0∞), Measurable F →
        ∫⁻ x, F x ∂(riemannianMeasure D.metric ρ) =
          ∫⁻ x, F x ∂((riemannianMeasure
            HeightMetricCoefficients.round ρ).withDensity A) := by
    intro F hF
    rw [lintegral_withDensity_eq_lintegral_mul
      (riemannianMeasure
        HeightMetricCoefficients.round ρ) hA hF]
    simp only [Pi.mul_apply]
    rw [riemannianMeasure_lintegral_eq D.metric ρ hF,
      riemannianMeasure_lintegral_eq
        HeightMetricCoefficients.round ρ (f := fun x => A x * F x) (hA.mul hF)]
    refine tsum_congr (fun α => ?_)
    have hρα :
        Measurable
          (fun x : RotationalSphere => ENNReal.ofReal (ρ α x)) :=
      measurable_ofReal_pou_weight ρ α
    rw [chartLocalMeasure_lintegral
        D.metric α (F := fun x => ENNReal.ofReal (ρ α x) * F x) (hρα.mul hF),
      chartLocalMeasure_lintegral
        HeightMetricCoefficients.round α
          (F := fun x => ENNReal.ofReal (ρ α x) * (A x * F x)) (hρα.mul (hA.mul hF))]
    refine MeasureTheory.setLIntegral_congr_fun
      (measurableSet_extChartAt_target
        (I := 𝓡 2) α) (fun y hyTarget => ?_)
    have hy :
        (extChartAt (𝓡 2) α).symm y ∈
          (trivializationAt
            (EuclideanSpace ℝ (Fin 2))
            (TangentSpace (𝓡 2)) α).baseSet := by
      have hsource :
          (extChartAt (𝓡 2) α).symm y ∈
            (extChartAt (𝓡 2) α).source :=
        (extChartAt (𝓡 2) α).map_target hyTarget
      rw [extChartAt_source_eq_chartAt_source
        (I := 𝓡 2)] at hsource
      rw [trivializationAt_baseSet_eq_chartAt_source]
      exact hsource
    rw [chartDensity_metric
      D α ((extChartAt (𝓡 2) α).symm y) hy,
      ENNReal.ofReal_mul
        (D.a_pos _ (sphereHeight_mem_Icc ((extChartAt (𝓡 2) α).symm y))).le]
    simp only [hAdef]
    ring
  refine Measure.ext fun s hs => ?_
  rw [← lintegral_indicator_one hs,
    ← lintegral_indicator_one hs]
  exact key (s.indicator 1)
    (measurable_const.indicator hs)

/-- The Riemannian volume of the balanced rotational metric is the round
volume with density `a(height)`. -/
theorem volume_metric_eq_withDensity (D : PoleData) :
    riemannianVolumeMeasure
        (I := 𝓡 2) (M := RotationalSphere) D.metric =
      (riemannianVolumeMeasure
          (I := 𝓡 2) (M := RotationalSphere)
          HeightMetricCoefficients.round).withDensity
        (fun x : RotationalSphere =>
          ENNReal.ofReal (D.a (sphereHeight x))) := by
  rw [riemannianVolumeMeasure_def,
    riemannianVolumeMeasure_def]
  exact
    riemannianMeasure_metric_eq_withDensity
      D (chartAtlasPOU (𝓡 2) RotationalSphere)

/-- Integral form of the volume identity.  It is stated without a
separate integrability hypothesis because the Bochner integral has the
same convention on both sides. -/
theorem integral_volume_metric
    (D : PoleData) (F : RotationalSphere → ℝ) :
    ∫ x, F x ∂(riemannianVolumeMeasure
        (I := 𝓡 2) (M := RotationalSphere) D.metric) =
      ∫ x, D.a (sphereHeight x) * F x
        ∂(riemannianVolumeMeasure
          (I := 𝓡 2) (M := RotationalSphere)
          HeightMetricCoefficients.round) := by
  rw [volume_metric_eq_withDensity D]
  rw [integral_withDensity_eq_integral_toReal_smul
    (measurable_profileDensity D)
    (Filter.Eventually.of_forall
      (fun x : RotationalSphere =>
        ENNReal.ofReal_lt_top))]
  apply integral_congr_ae
  filter_upwards [] with x
  rw [ENNReal.toReal_ofReal (D.a_pos _ (sphereHeight_mem_Icc x)).le]
  rfl

/-- Exact height disintegration for the original balanced profile and its metric. -/
theorem integral_height_metric (D : PoleData) {F : ℝ → ℝ}
    (hF : ContinuousOn F (Set.Icc (-1 : ℝ) 1)) :
    (∫ x : RotationalSphere, F (sphereHeight x)
      ∂(riemannianVolumeMeasure (I := 𝓡 2) (M := RotationalSphere) D.metric)) =
      2 * Real.pi * ∫ v in (-1 : ℝ)..1, D.a v * F v := by
  rw [D.integral_volume_metric]
  exact integral_round_height (D.a_contDiff.continuous.continuousOn.mul hF)

end RotationalProfile.PoleData

end RicciFlowSharpEstimate.Geometry
