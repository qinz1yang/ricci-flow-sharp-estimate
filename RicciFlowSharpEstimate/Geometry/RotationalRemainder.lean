/-
Copyright (c) 2026 Ziyang Qin. All rights reserved.
No license is granted by this file.
Authors: Ziyang Qin
-/
import RicciFlowSharpEstimate.Geometry.RotationalRemainderBounds
import RicciFlowSharpEstimate.Geometry.WeightedIntegralRigidity
import RicciFlowSharpEstimate.Geometry.OneFormDerivativeRigidity
import RicciFlowSharpEstimate.Geometry.RotationalInvariantClassification

/-!
# Strict positivity of the original Haar remainder

The positive scalar gap forces every zero-action Haar remainder to vanish.
The proof uses the actual full-support Riemannian volume, canonical derivatives
and original four-term action. The exact Haar and zonal consumers retain the
original form and the same globally smooth probes.
-/

noncomputable section

namespace RicciFlowSharpEstimate.Geometry

open MeasureTheory DifferentialGeometry DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Tensor.RicciIdentity DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.Integral.Measure
open scoped Manifold ContDiff

local instance : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 2 + 1) :=
  ⟨finrank_euclideanSpace_fin⟩
local instance : CompactSpace RotationalSphere := Metric.sphere.compactSpace _ _
private local instance : MeasurableSpace RotationalSphere := borel RotationalSphere
private local instance : BorelSpace RotationalSphere := ⟨rfl⟩

namespace RotationalProfile.PoleData

/-- Zero original action of the actual Haar remainder is equivalent to zero remainder. -/
theorem oneFormDissipation_remainder_eq_zero_iff (D : PoleData)
    (h : OneFormSection (I := 𝓡 2) (M := RotationalSphere)) :
    oneFormDissipation D.metric (h - rotationalAverage h) = 0 ↔
      h - rotationalAverage h = 0 := by
  constructor
  · intro hQ
    let k := h - rotationalAverage h
    let μ := riemannianVolumeMeasure (I := 𝓡 2) (M := RotationalSphere) D.metric
    let A := ahlforsPart D.metric (metricNabla0S D.metric k)
    let tau := oneFormTrace D.metric k
    let curlScalar := oneFormCurl D.metric D.areaForm k
    let wa : RotationalSphere → ℝ := fun x => 1 / D.a (sphereHeight x)
    let wb : RotationalSphere → ℝ := fun x => 1 / D.b (sphereHeight x)
    have hwa : Continuous wa := continuous_const.div
      (D.a_contDiff.continuous.comp sphereHeight_contMDiff.continuous)
      (fun x => (D.a_pos _ (sphereHeight_mem_Icc x)).ne')
    have hwb : Continuous wb := continuous_const.div
      (D.b_contDiff.continuous.comp sphereHeight_contMDiff.continuous)
      (fun x => (D.b_pos _ (sphereHeight_mem_Icc x)).ne')
    have hwaPos (x : RotationalSphere) : 0 < wa x :=
      one_div_pos.mpr (D.a_pos _ (sphereHeight_mem_Icc x))
    have hwbPos (x : RotationalSphere) : 0 < wb x :=
      one_div_pos.mpr (D.b_pos _ (sphereHeight_mem_Icc x))
    let IA := ∫ x, wa x * normSq0S D.metric x 2 (A x) ∂μ
    let IT := ∫ x, tau x ^ 2 / D.b (sphereHeight x) ∂μ
    let IC := ∫ x, curlScalar x ^ 2 / D.b (sphereHeight x) ∂μ
    have hApos : 0 ≤ IA :=
      integral_nonneg (fun x => mul_nonneg (hwaPos x).le (normSq0S_nonneg D.metric x 2 _))
    have hTpos : 0 ≤ IT :=
      integral_nonneg (fun x => div_nonneg (sq_nonneg _) (D.b_pos _ (sphereHeight_mem_Icc x)).le)
    have hCpos : 0 ≤ IC :=
      integral_nonneg (fun x => div_nonneg (sq_nonneg _) (D.b_pos _ (sphereHeight_mem_Icc x)).le)
    have hbound := D.oneFormDissipation_remainder_lower_bound h
    change 3 * IA + (1 / 2 : ℝ) * (IT + IC) ≤ oneFormDissipation D.metric k at hbound
    change oneFormDissipation D.metric k = 0 at hQ
    have hIA : IA = 0 := by linarith
    have hIT : IT = 0 := by linarith
    have hIC : IC = 0 := by linarith
    have hA : A = 0 :=
      (integral_weight_mul_normSq_eq_zero_iff D.metric A wa hwa hwaPos).mp hIA
    have hTau : tau = 0 :=
      (integral_weight_mul_sq_eq_zero_iff D.metric tau
        (oneFormTrace_contMDiff D.metric k).continuous wb hwb hwbPos).mp (by
        simpa only [IT, wb, one_div, div_eq_mul_inv, one_mul, mul_comm] using hIT)
    have hCurl : curlScalar = 0 :=
      (integral_weight_mul_sq_eq_zero_iff D.metric curlScalar
        (oneFormCurl_contMDiff D.metric D.areaForm k).continuous wb hwb hwbPos).mp (by
        simpa only [IC, wb, one_div, div_eq_mul_inv, one_mul, mul_comm] using hIC)
    have hfirst : metricNabla0S D.metric k = 0 :=
      metricNabla0S_eq_zero_of_ahlfors_trace_curl_eq_zero (by simp) D.metric D.areaForm k
        D.areaForm_alternating D.areaForm_normSq hA hTau hCurl
    have hpar := oneFormDissipation_eq_curvature_energy_of_metricNabla0S_eq_zero
      D.metric k hfirst
    have hK (x : RotationalSphere) : metricScalarAt D.metric x / 2 = wa x := by
      rw [D.metricScalarAt_metric]
      dsimp only [wa]
      ring
    have henergy : (∫ x, wa x ^ 2 * normSq0S D.metric x 1 (k x) ∂μ) = 0 := by
      simpa only [hK] using hpar.symm.trans hQ
    exact (integral_weight_mul_normSq_eq_zero_iff D.metric k (fun x => wa x ^ 2)
      (hwa.pow 2) (fun x => pow_pos (hwaPos x) 2)).mp henergy
  · intro hk
    rw [hk, oneFormDissipation_zero]

/-- Every nonzero genuine Haar remainder has strictly positive original action. -/
theorem oneFormDissipation_remainder_pos_iff (D : PoleData)
    (h : OneFormSection (I := 𝓡 2) (M := RotationalSphere)) :
    0 < oneFormDissipation D.metric (h - rotationalAverage h) ↔
      h - rotationalAverage h ≠ 0 := by
  have hn := D.oneFormDissipation_remainder_nonneg h
  rw [lt_iff_le_and_ne]
  constructor
  · rintro ⟨_, hne⟩ hz
    exact hne ((D.oneFormDissipation_remainder_eq_zero_iff h).mpr hz).symm
  · intro hk
    refine ⟨hn, ?_⟩
    intro heq
    exact hk ((D.oneFormDissipation_remainder_eq_zero_iff h).mp heq.symm)

/-- Haar averaging never increases the original complete action. -/
theorem oneFormDissipation_rotationalAverage_le (D : PoleData)
    (h : OneFormSection (I := 𝓡 2) (M := RotationalSphere)) :
    oneFormDissipation D.metric (rotationalAverage h) ≤ oneFormDissipation D.metric h := by
  rw [D.oneFormDissipation_haar_split h]
  exact le_add_of_nonneg_right (D.oneFormDissipation_remainder_nonneg h)

/-- Equality in the Haar action comparison characterizes the original fixed form. -/
theorem oneFormDissipation_eq_rotationalAverage_iff (D : PoleData)
    (h : OneFormSection (I := 𝓡 2) (M := RotationalSphere)) :
    oneFormDissipation D.metric h = oneFormDissipation D.metric (rotationalAverage h) ↔
      h = rotationalAverage h := by
  constructor
  · intro hQ
    have hsplit := D.oneFormDissipation_haar_split h
    have hz : oneFormDissipation D.metric (h - rotationalAverage h) = 0 := by linarith
    exact sub_eq_zero.mp ((D.oneFormDissipation_remainder_eq_zero_iff h).mp hz)
  · intro hh
    exact congrArg (oneFormDissipation D.metric) hh

/-- Equality in Haar comparison is exactly invariance under the actual native circle action. -/
theorem oneFormDissipation_eq_rotationalAverage_iff_invariant (D : PoleData)
    (h : OneFormSection (I := 𝓡 2) (M := RotationalSphere)) :
    oneFormDissipation D.metric h = oneFormDissipation D.metric (rotationalAverage h) ↔
      ∀ z : Circle, diffeomorphTensorPullback (circleSphereDiffeo z) h = h := by
  rw [D.oneFormDissipation_eq_rotationalAverage_iff]
  exact eq_comm.trans (rotationalAverage_eq_self_iff h)

/-- The same globally smooth probes representing the actual Haar average give
the exact zonal lower bound, with equality precisely at that zonal form. -/
theorem exists_haar_zonal_lower_bound (D : PoleData)
    (h : OneFormSection (I := 𝓡 2) (M := RotationalSphere)) :
    ∃ r s : ℝ → ℝ, ∃ hr : ContDiff ℝ ∞ r, ∃ hs : ContDiff ℝ ∞ s,
      rotationalAverage h = D.meridionalOneForm r hr + D.azimuthalOneForm s hs ∧
      2 * Real.pi * (D.meridionalAction r + D.meridionalAction s) ≤
        oneFormDissipation D.metric h ∧
      (oneFormDissipation D.metric h =
          2 * Real.pi * (D.meridionalAction r + D.meridionalAction s) ↔
        h = D.meridionalOneForm r hr + D.azimuthalOneForm s hs) := by
  obtain ⟨r, s, hr, hs, hrepr⟩ := D.exists_smooth_zonal_decomposition_rotationalAverage h
  have hvalue : oneFormDissipation D.metric (rotationalAverage h) =
      2 * Real.pi * (D.meridionalAction r + D.meridionalAction s) := by
    rw [hrepr, D.oneFormDissipation_zonal]
  refine ⟨r, s, hr, hs, hrepr, ?_, ?_⟩
  · rw [← hvalue]
    exact D.oneFormDissipation_rotationalAverage_le h
  · rw [← hvalue, D.oneFormDissipation_eq_rotationalAverage_iff, hrepr]

end RotationalProfile.PoleData
end RicciFlowSharpEstimate.Geometry
