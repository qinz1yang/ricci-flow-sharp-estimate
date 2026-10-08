/-
Copyright (c) 2026 Ziyang Qin. All rights reserved.
No license is granted by this file.
Authors: Ziyang Qin
-/
import RicciFlowSharpEstimate.Geometry.RotationalSphereMetric
import DifferentialGeometry.Geometry.Metric.Sphere.Round.TotalArea

/-!
# Height disintegration of round sphere area

The hemisphere graph area formula gives the actual pushforward measure. Radial
integration then proves the height identity with its exact normalization.
-/

open Bundle Manifold Metric Set Module MeasureTheory
open DifferentialGeometry.Geometry
open DifferentialGeometry.Integral.Measure
open scoped Manifold ContDiff RealInnerProductSpace ENNReal Topology Matrix

noncomputable section

namespace RicciFlowSharpEstimate.Geometry

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "E2" => EuclideanSpace ℝ (Fin 2)
local notation "μround" => riemannianVolumeMeasure (I := 𝓡 2)
  (M := RotationalSphere) HeightMetricCoefficients.round

private instance : Fact (Module.finrank ℝ E3 = 2 + 1) := ⟨by simp⟩
private local instance : MeasurableSpace E2 := borel E2
private local instance : BorelSpace E2 := ⟨rfl⟩
private local instance : MeasurableSpace RotationalSphere := borel RotationalSphere
private local instance : BorelSpace RotationalSphere := ⟨rfl⟩

private def graphDensity (y : E2) : ℝ := Real.sqrt ((1 - ‖y‖ ^ 2)⁻¹)

private theorem graphDensity_measurable : Measurable graphDensity := by
  unfold graphDensity
  fun_prop

private theorem measurable_graph {v : E3} (hv : ‖v‖ = 1)
    (R : E2 ≃ₗᵢ[ℝ] (ℝ ∙ v)ᗮ) : Measurable (sphereGraphParametrization hv R) := by
  classical
  apply (isClosed_sphere.isClosedEmbedding_subtypeVal.measurableEmbedding.measurable_comp_iff).mp
  change Measurable (fun y => (sphereGraphParametrization hv R y : E3))
  have heq : (fun y => (sphereGraphParametrization hv R y : E3)) =
      fun y => if y ∈ ball (0 : E2) 1 then sphereGraphMap R y else v := by
    funext y
    simp only [sphereGraphParametrization]
    split_ifs <;> rfl
  rw [heq]
  apply Measurable.ite measurableSet_ball
  · unfold sphereGraphMap
    fun_prop
  · exact measurable_const

private theorem volume_eq_graph_smul_modelHaar :
    (volume : Measure E2) =
      ENNReal.ofReal (Real.sqrt sphereGraphGram.det) • modelHaar (E := E2) := by
  let e : Fin (Module.finrank ℝ E2) ≃ Fin 2 :=
    finCongr (finrank_euclideanSpace_fin (𝕜 := ℝ) (n := 2))
  have hgram : sphereGraphGram = Matrix.reindex e e
      (Matrix.of fun i j =>
        ⟪(DifferentialGeometry.Tensor.Coordinates.chartModelBasis E2 i : E2),
          (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E2 j : E2)⟫) := by
    ext i j
    simp [sphereGraphGram, chartModelBasisTwo, Matrix.reindex, e, Basis.reindex_apply]
  have hdet : (Matrix.det (Matrix.of fun i j =>
      ⟪(DifferentialGeometry.Tensor.Coordinates.chartModelBasis E2 i : E2),
        (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E2 j : E2)⟫)) =
      sphereGraphGram.det := by
    rw [hgram, Matrix.det_reindex_self]
  have h := addHaar_withDensity_sqrt_det_gramMatrix_eq_volume
    (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E2)
  rw [← h, modelHaar, withDensity_const, hdet]

private theorem map_graphDensity {v : E3} (hv : ‖v‖ = 1)
    (R : E2 ≃ₗᵢ[ℝ] (ℝ ∙ v)ᗮ) :
    Measure.map (sphereGraphParametrization hv R)
        ((volume.restrict (ball (0 : E2) 1)).withDensity
          (fun y => ENNReal.ofReal (graphDensity y))) =
      (μround).restrict {p : RotationalSphere | 0 < ⟪(p : E3), v⟫} := by
  ext s hs
  let Ψ := sphereGraphParametrization hv R
  have hΨ : Measurable Ψ := measurable_graph hv R
  have hK : MeasurableSet (Ψ ⁻¹' s ∩ ball (0 : E2) 1) :=
    (hΨ hs).inter measurableSet_ball
  have himg : Ψ '' (Ψ ⁻¹' s ∩ ball (0 : E2) 1) =
      s ∩ {p : RotationalSphere | 0 < ⟪(p : E3), v⟫} := by
    rw [image_preimage_inter, sphereGraphParametrization_image_eq_openHemisphere hv R]
  rw [Measure.map_apply hΨ hs, withDensity_apply _ (hΨ hs), Measure.restrict_restrict
    (hΨ hs), Measure.restrict_apply hs, ← himg]
  rw [riemannianVolumeMeasure_image_eq HeightMetricCoefficients.round isOpen_ball hK
    inter_subset_right (contMDiffOn_sphereGraphParametrization hv R)
    ((sphereGraphParametrization_injOn hv R).mono inter_subset_right)]
  rw [volume_eq_graph_smul_modelHaar, Measure.restrict_smul,
    lintegral_smul_measure, smul_eq_mul]
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine setLIntegral_congr_fun hK fun y hy => ?_
  rw [paramDensity_roundMetric_sphereGraphParametrization hv R
    (mem_ball_zero_iff.mp hy.2), ENNReal.ofReal_mul (Real.sqrt_nonneg _)]
  rfl

private theorem integral_radial_graph (F : ℝ → ℝ) :
    (∫ r in (0 : ℝ)..1, r * Real.sqrt ((1 - r ^ 2)⁻¹) *
      F (Real.sqrt (1 - r ^ 2))) = ∫ z in (0 : ℝ)..1, F z := by
  let f : ℝ → ℝ := fun r => Real.sqrt (1 - r ^ 2)
  let f' : ℝ → ℝ := fun r => -(r * Real.sqrt ((1 - r ^ 2)⁻¹))
  have hf : Continuous f := by dsimp [f]; fun_prop
  have hderiv : ∀ r ∈ Ioo (min (0 : ℝ) 1) (max (0 : ℝ) 1), HasDerivAt f (f' r) r := by
    intro r hr
    simp only [min_eq_left zero_le_one, max_eq_right zero_le_one, mem_Ioo] at hr
    have hpos : 0 < 1 - r ^ 2 := by nlinarith [hr.1, hr.2]
    have h := ((hasDerivAt_id r).pow 2).const_sub (1 : ℝ)
    have h' := h.sqrt hpos.ne'
    convert h' using 1 <;>
      simp only [f, f', id_eq, Pi.pow_apply, Nat.cast_ofNat, Nat.reduceSub, pow_one,
        mul_one, Real.sqrt_inv]
    ring
  have hnonpos : ∀ r ∈ Ioo (min (0 : ℝ) 1) (max (0 : ℝ) 1), f' r ≤ 0 := by
    intro r hr
    dsimp [f']
    apply neg_nonpos.mpr
    exact mul_nonneg (le_of_lt (by simpa using hr.1)) (Real.sqrt_nonneg _)
  have h := intervalIntegral.integral_comp_mul_deriv_of_deriv_nonpos
    (g := F) hf.continuousOn hderiv hnonpos
  have hfun : (fun r => (F ∘ f) r * f' r) =
      fun r => -(r * Real.sqrt ((1 - r ^ 2)⁻¹) * F (Real.sqrt (1 - r ^ 2))) := by
    funext r
    dsimp [f, f']
    ring
  rw [hfun, intervalIntegral.integral_neg] at h
  simp only [f, zero_pow (by decide : 2 ≠ 0), sub_zero, Real.sqrt_one, one_pow,
    sub_self, Real.sqrt_zero] at h
  rw [intervalIntegral.integral_symm (f := F)] at h
  exact neg_injective h

private theorem volumeReal_disk : (volume : Measure E2).real (ball (0 : E2) 1) = Real.pi := by
  have hG : Real.Gamma (2 : ℝ) = 1 := by
    have h2 : (2 : ℝ) = ((1 : ℕ) : ℝ) + 1 := by norm_num
    rw [h2, Real.Gamma_nat_eq_factorial]
    norm_num
  have harg : (↑(2 : ℕ) : ℝ) / 2 + 1 = 2 := by norm_num
  rw [Measure.real_def, InnerProductSpace.volume_ball (0 : E2) (1 : ℝ),
    finrank_euclideanSpace_fin, ENNReal.ofReal_one, one_pow, one_mul,
    Real.sq_sqrt Real.pi_pos.le, harg, hG, div_one,
    ENNReal.toReal_ofReal Real.pi_pos.le]

private theorem integral_graphDensity_height (F : ℝ → ℝ) :
    (∫ y in ball (0 : E2) 1, graphDensity y * F (Real.sqrt (1 - ‖y‖ ^ 2))) =
      2 * Real.pi * ∫ z in (0 : ℝ)..1, F z := by
  let P : ℝ → ℝ := fun r => Real.sqrt ((1 - r ^ 2)⁻¹) * F (Real.sqrt (1 - r ^ 2))
  have hzero : ∀ r : ℝ, 1 ≤ r → P r = 0 := by
    intro r hr
    dsimp [P]
    have hnonpos : 1 - r ^ 2 ≤ 0 := by nlinarith
    rw [Real.sqrt_eq_zero_of_nonpos (inv_nonpos.mpr hnonpos), zero_mul]
  have hind : (ball (0 : E2) 1).indicator (fun y => P ‖y‖) = fun y => P ‖y‖ := by
    funext y
    by_cases hy : y ∈ ball (0 : E2) 1
    · exact indicator_of_mem hy _
    · rw [indicator_of_notMem hy, hzero _ (by simpa using hy)]
  change (∫ y in ball (0 : E2) 1, P ‖y‖) = _
  rw [← integral_indicator measurableSet_ball, hind, integral_fun_norm_addHaar,
    volumeReal_disk, finrank_euclideanSpace_fin]
  have hradial : (∫ r in Ioi (0 : ℝ), r ^ (2 - 1) • P r) = ∫ r in (0 : ℝ)..1, r * P r := by
    simp only [Nat.reduceSub, pow_one, smul_eq_mul]
    rw [intervalIntegral.integral_of_le zero_le_one,
      ← integral_indicator measurableSet_Ioi, ← integral_indicator measurableSet_Ioc]
    apply integral_congr_ae
    filter_upwards with r
    by_cases hr : r ∈ Ioi (0 : ℝ)
    · rw [indicator_of_mem hr]
      by_cases hr1 : r ∈ Ioc (0 : ℝ) 1
      · rw [indicator_of_mem hr1]
      · rw [indicator_of_notMem hr1, hzero _ (by
          by_contra h
          exact hr1 ⟨hr, (lt_of_not_ge h).le⟩), mul_zero]
    · rw [indicator_of_notMem hr, indicator_of_notMem (fun h => hr h.1)]
  rw [hradial]
  have hP : (fun r => r * P r) =
      fun r => r * Real.sqrt ((1 - r ^ 2)⁻¹) * F (Real.sqrt (1 - r ^ 2)) := by
    funext r
    dsimp [P]
    ring
  rw [hP, integral_radial_graph]
  simp only [nsmul_eq_mul, smul_eq_mul, Nat.cast_ofNat]
  ring

private theorem integral_openHemisphere {v : E3} (hv : ‖v‖ = 1)
    (R : E2 ≃ₗᵢ[ℝ] (ℝ ∙ v)ᗮ) {H : RotationalSphere → ℝ} (hH : Continuous H)
    (F : ℝ → ℝ)
    (hcomp : ∀ y ∈ ball (0 : E2) 1,
      H (sphereGraphParametrization hv R y) = F (Real.sqrt (1 - ‖y‖ ^ 2))) :
    (∫ p in {p : RotationalSphere | 0 < ⟪(p : E3), v⟫}, H p ∂μround) =
      2 * Real.pi * ∫ z in (0 : ℝ)..1, F z := by
  rw [← map_graphDensity hv R,
    integral_map (measurable_graph hv R).aemeasurable hH.aestronglyMeasurable,
    integral_withDensity_eq_integral_toReal_smul
      graphDensity_measurable.ennreal_ofReal (Filter.Eventually.of_forall fun _ =>
        ENNReal.ofReal_lt_top)]
  simp only [smul_eq_mul]
  calc
    _ = ∫ y in ball (0 : E2) 1,
        graphDensity y * F (Real.sqrt (1 - ‖y‖ ^ 2)) := by
      refine setIntegral_congr_fun measurableSet_ball fun y hy => ?_
      rw [hcomp y hy, ENNReal.toReal_ofReal (show 0 ≤ graphDensity y from Real.sqrt_nonneg _)]
    _ = _ := integral_graphDensity_height F

private def sphereFrame (v : E3) (hv : v ≠ 0) : E2 ≃ₗᵢ[ℝ] (ℝ ∙ v)ᗮ :=
  ((stdOrthonormalBasis ℝ ((ℝ ∙ v)ᗮ)).reindex
    (finCongr (by rw [finrank_normal hv, finrank_euclideanSpace_fin]))).repr.symm

/-- Integrating a continuous function of height against the genuine round area measure. -/
theorem integral_round_height {F : ℝ → ℝ} (hF : ContinuousOn F (Icc (-1 : ℝ) 1)) :
    (∫ p : RotationalSphere, F (sphereHeight p) ∂μround) =
      2 * Real.pi * ∫ z in (-1 : ℝ)..1, F z := by
  let e : E3 := EuclideanSpace.single (2 : Fin 3) (1 : ℝ)
  have he : ‖e‖ = 1 := by simp [e]
  have hne : e ≠ 0 := by intro h; simp [h] at he
  have hneg : ‖(-e : E3)‖ = 1 := by simpa using he
  let R := sphereFrame e hne
  let R' := sphereFrame (-e) (neg_ne_zero.mpr hne)
  have hheight : ∀ p : RotationalSphere, sphereHeight p = ⟪(p : E3), e⟫ := by
    intro p
    change ⟪e, (p : E3)⟫ = _
    exact real_inner_comm _ _
  have hH : Continuous (fun p : RotationalSphere => F (sphereHeight p)) :=
    hF.comp_continuous sphereHeight_contMDiff.continuous sphereHeight_mem_Icc
  have hupper := integral_openHemisphere he R hH F (by
    intro y hy
    rw [hheight, coe_sphereGraphParametrization he R hy, sphereGraphMap_inner_base he R])
  have hlower := integral_openHemisphere hneg R' hH (fun z => F (-z)) (by
    intro y hy
    rw [hheight, coe_sphereGraphParametrization hneg R' hy]
    have h := sphereGraphMap_inner_base hneg R' y
    rw [inner_neg_right] at h
    congr 1
    linarith)
  have hnull : (μround) {p : RotationalSphere | sphereHeight p = 0} = 0 := by
    simpa only [hheight] using riemannianVolumeMeasure_roundMetric_equator_eq_zero
      ⟨e, mem_sphere_zero_iff_norm.mpr he⟩ R
  have hae : ∀ᵐ p ∂μround, sphereHeight p ≠ 0 := by
    rw [ae_iff]
    simpa only [not_not] using hnull
  have hsets : {p : RotationalSphere | 0 < ⟪(p : E3), e⟫}ᶜ =ᵐ[μround]
      {p : RotationalSphere | 0 < ⟪(p : E3), -e⟫} := by
    filter_upwards [hae] with p hp
    simp only [mem_compl_iff, mem_ofPred_eq, inner_neg_right, ← hheight]
    apply propext
    constructor
    · intro h
      exact neg_pos.mpr (lt_of_le_of_ne (le_of_not_gt h) hp)
    · intro h
      exact not_lt.mpr (neg_pos.mp h).le
  have : CompactSpace RotationalSphere := Metric.sphere.compactSpace _ _
  have : Nonempty RotationalSphere := ⟨⟨e, mem_sphere_zero_iff_norm.mpr he⟩⟩
  have : IsFiniteMeasure (μround) :=
    riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace _
  have hint : Integrable (fun p : RotationalSphere => F (sphereHeight p)) (μround) :=
    hH.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hmeas : MeasurableSet {p : RotationalSphere | 0 < ⟪(p : E3), e⟫} :=
    (isOpen_lt continuous_const (continuous_subtype_val.inner continuous_const)).measurableSet
  have hFI : IntervalIntegrable F volume (-1) 1 :=
    (show ContinuousOn F (uIcc (-1 : ℝ) 1) by simpa using hF).intervalIntegrable
  rw [← integral_add_compl hmeas hint, setIntegral_congr_set hsets, hupper, hlower,
    intervalIntegral.integral_comp_neg]
  simp only [neg_zero]
  rw [← mul_add, add_comm (∫ z in (0 : ℝ)..1, F z),
    intervalIntegral.integral_add_adjacent_intervals]
  · exact hFI.mono_set (by
      simpa using Icc_subset_Icc (le_refl (-1 : ℝ)) (zero_le_one : (0 : ℝ) ≤ 1))
  · exact hFI.mono_set (by
      simpa using Icc_subset_Icc (by norm_num : (-1 : ℝ) ≤ 0) (le_refl (1 : ℝ)))

end RicciFlowSharpEstimate.Geometry
