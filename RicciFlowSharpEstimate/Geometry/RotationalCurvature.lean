/-
Copyright (c) 2026 Ziyang Qin. All rights reserved.
No license is granted by this file.
Authors: Ziyang Qin
-/
import RicciFlowSharpEstimate.Geometry.RotationalCoordinates
import RicciFlowSharpEstimate.Geometry.RotationalCoordinateRange
import RicciFlowSharpEstimate.Geometry.RotationalDiagonalCurvature
import RicciFlowSharpEstimate.Geometry.RotationalCurvatureProfile
import DifferentialGeometry.Topology.Manifold.InverseFunction
import DifferentialGeometry.Geometry.Curvature.Naturality.Pullback.LocalCross
import DifferentialGeometry.Geometry.Curvature.DimensionTwo.SectionalCurvature

/-!
# Curvature of the genuine rotational sphere metric

The cylinder map is a local diffeomorphism. Its actual pullback metric is
computed in a chart-basis-aligned open domain, and its true metric two-jet is
inserted into the intrinsic scalar-curvature formula. Continuity and the dense
cylinder image extend the identity across both poles of the same sphere metric.

The basis alignment adapts Ziyang Qin's historical
`RotationalSpherePolarJetPatch.lean` and `RotationalSpherePolarMetricJet.lean`.
-/

noncomputable section

namespace RicciFlowSharpEstimate.Geometry

open Bundle Manifold Set TopologicalSpace Filter
open DifferentialGeometry DifferentialGeometry.Analysis DifferentialGeometry.Geometry
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Tensor.Coordinates
open scoped Manifold ContDiff Topology

private abbrev Plane := EuclideanSpace ℝ (Fin 2)
private local instance : NeZero (Module.finrank ℝ Plane) := ⟨by simp [Plane]⟩
local instance : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 2 + 1) :=
  ⟨finrank_euclideanSpace_fin⟩

private theorem cylinderLocalDiffeomorph :
    IsLocalDiffeomorph (𝓘(ℝ, Plane)) (𝓡 2) ∞ cylinderMap := by
  intro q
  let L : Plane →L[ℝ] Plane := mfderiv (𝓘(ℝ, Plane)) (𝓡 2) cylinderMap q
  have hL : Function.Bijective L := ⟨cylinderMap_mfderiv_injective q,
    (LinearMap.injective_iff_surjective).mp (cylinderMap_mfderiv_injective q)⟩
  let A := ContinuousLinearEquiv.ofBijective L
    (LinearMap.ker_eq_bot.mpr hL.1) (LinearMap.range_eq_top.mpr hL.2)
  exact DifferentialGeometry.Topology.Manifold.isLocalDiffeomorphAt_of_hasMFDerivAt_equiv
    cylinderMap cylinderMap_contMDiff q A
    (cylinderMap_contMDiff.mdifferentiableAt (by simp)).hasMFDerivAt

private def modelReindex : EuclideanSpace ℝ (Fin (Module.finrank ℝ Plane)) ≃ₗᵢ[ℝ] Plane :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (finCongr finrank_euclideanSpace_fin)

private def align : Plane ≃L[ℝ] Plane :=
  (toEuclidean (E := Plane)).trans modelReindex.toContinuousLinearEquiv

private theorem align_basis (i : Fin (Module.finrank ℝ Plane)) :
    align (chartModelBasis Plane i) = modelReindex (EuclideanSpace.single i (1 : ℝ)) := by
  simp only [align, ContinuousLinearEquiv.trans_apply, chartModelBasis_apply,
    ContinuousLinearEquiv.apply_symm_apply, LinearIsometryEquiv.coe_toContinuousLinearEquiv]

private theorem index_cases (i : Fin (Module.finrank ℝ Plane)) : i = 0 ∨ i = 1 := by
  have hi : i.val = 0 ∨ i.val = 1 := by have := i.isLt; simp [Plane] at this; omega
  rcases hi with hi | hi
  · exact Or.inl (Fin.ext hi)
  · exact Or.inr (Fin.ext (by simpa using hi))

private theorem align_basis_coord (i : Fin (Module.finrank ℝ Plane)) (j : Fin 2) :
    align (chartModelBasis Plane i) j = if i.val = j.val then 1 else 0 := by
  have hidx : finCongr finrank_euclideanSpace_fin
      (1 : Fin (Module.finrank ℝ Plane)) = (1 : Fin 2) := by
    apply Fin.ext
    simp [finCongr]
  rw [align_basis]
  rcases index_cases i with rfl | rfl <;> fin_cases j <;> simp [modelReindex, hidx]

private def alignedDomain : Opens Plane where
  carrier := align ⁻¹' (cylinderDomain : Set Plane)
  is_open' := cylinderDomain.2.preimage align.continuous

private def alignedToCylinder (p : alignedDomain) : cylinderDomain := ⟨align p.val, p.property⟩

private theorem alignedToCylinder_smooth :
    ContMDiff (𝓘(ℝ, Plane)) (𝓘(ℝ, Plane)) ∞ alignedToCylinder := by
  intro p
  exact codRestr_contMDiffAt (f := fun y : alignedDomain => align y.val)
    (fun y : alignedDomain => y.property)
    (align.toContinuousLinearMap.contMDiff.contMDiffAt.comp p
      contMDiff_subtype_val.contMDiffAt)

private theorem alignedToCylinder_deriv (p : alignedDomain) (v : Plane) :
    mfderiv (𝓘(ℝ, Plane)) (𝓘(ℝ, Plane)) alignedToCylinder p v = align v := by
  have h := mfderiv_comp_apply p
    ((contMDiff_subtype_val (U := cylinderDomain) (n := ∞)).mdifferentiableAt (by simp))
    (alignedToCylinder_smooth.mdifferentiableAt (by simp)) v
  rw [mfderiv_subtype_val_apply] at h
  rw [← h]
  change mfderiv (𝓘(ℝ, Plane)) (𝓘(ℝ, Plane)) (align ∘ Subtype.val) p v = _
  erw [mfderiv_comp_apply p
    align.toContinuousLinearMap.hasFDerivAt.differentiableAt.mdifferentiableAt
    ((contMDiff_subtype_val (n := ∞)).mdifferentiableAt (by simp)),
    mfderiv_subtype_val_apply, mfderiv_eq_fderiv,
    align.toContinuousLinearMap.hasFDerivAt.fderiv]
  rfl

private theorem alignedLocalDiffeomorph :
    IsLocalDiffeomorph (𝓘(ℝ, Plane)) (𝓘(ℝ, Plane)) ∞ alignedToCylinder := by
  intro p
  apply DifferentialGeometry.Topology.Manifold.isLocalDiffeomorphAt_of_hasMFDerivAt_equiv
    alignedToCylinder alignedToCylinder_smooth p align
  have hderiv : mfderiv (𝓘(ℝ, Plane)) (𝓘(ℝ, Plane)) alignedToCylinder p =
      align.toContinuousLinearMap := by
    ext v
    exact alignedToCylinder_deriv p v
  rw [← hderiv]
  exact (alignedToCylinder_smooth.mdifferentiableAt (x := p) (by simp)).hasMFDerivAt

private def alignedMap (p : alignedDomain) : RotationalSphere := cylinderMap (alignedToCylinder p)

private theorem alignedMap_localDiffeomorph :
    IsLocalDiffeomorph (𝓘(ℝ, Plane)) (𝓡 2) ∞ alignedMap :=
  fun p => IsLocalDiffeomorphAt.comp (I := 𝓘(ℝ, Plane)) (J := 𝓘(ℝ, Plane))
    (K := 𝓡 2) (M := alignedDomain) (N := cylinderDomain) (P := RotationalSphere)
    (alignedLocalDiffeomorph p) (cylinderLocalDiffeomorph (alignedToCylinder p))

private def pullMetric (D : RotationalProfile.PoleData) :
    SmoothRiemannianMetric (𝓘(ℝ, Plane)) alignedDomain :=
  localPullMetric D.metric alignedMap alignedMap_localDiffeomorph

private theorem pullMetric_inner (D : RotationalProfile.PoleData) (p : alignedDomain)
    (v w : Plane) :
    (pullMetric D).inner p v w = D.radialCoefficient ((align p.val) 0) *
      (align v) 0 * (align w) 0 + RotationalProfile.warp D.a ((align p.val) 0) *
        (align v) 1 * (align w) 1 := by
  change TangentSpace (𝓘(ℝ, Plane)) p at v w
  rw [pullMetric, localPullMetric_inner]
  change D.metric.inner (cylinderMap (alignedToCylinder p))
    (mfderiv (𝓘(ℝ, Plane)) (𝓡 2) (cylinderMap ∘ alignedToCylinder) p v)
    (mfderiv (𝓘(ℝ, Plane)) (𝓡 2) (cylinderMap ∘ alignedToCylinder) p w) = _
  rw [mfderiv_comp_apply p (cylinderMap_contMDiff.mdifferentiableAt (by simp))
      (alignedToCylinder_smooth.mdifferentiableAt (by simp)),
    mfderiv_comp_apply p (cylinderMap_contMDiff.mdifferentiableAt (by simp))
      (alignedToCylinder_smooth.mdifferentiableAt (by simp)),
    ]
  erw [alignedToCylinder_deriv, alignedToCylinder_deriv, D.cylinderMap_metric_inner]
  rfl

private def radial : Plane →L[ℝ] ℝ :=
  (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 2 => ℝ) 0).comp align.toContinuousLinearMap

private theorem radial_apply (w : Plane) : radial w = (align w) 0 := rfl

private theorem radial_basis (i : Fin (Module.finrank ℝ Plane)) :
    radial (chartModelBasis Plane i) = if i = 0 then 1 else 0 := by
  by_cases hi : i = 0
  · subst i
    simpa [radial_apply] using align_basis_coord 0 0
  · have hi0 : i.val ≠ 0 := fun h => hi (Fin.ext h)
    simpa [radial_apply, hi, hi0] using align_basis_coord i 0

private def diagonal (e f : ℝ → ℝ) (w : Plane)
    (i j : Fin (Module.finrank ℝ Plane)) : ℝ :=
  if i = 0 ∧ j = 0 then e (radial w) else if i = 1 ∧ j = 1 then f (radial w) else 0

private theorem inverseChart (p : alignedDomain) (w : Plane) (hw : w ∈ alignedDomain) :
    (extChartAt (𝓘(ℝ, Plane)) p).symm w = (⟨w, hw⟩ : alignedDomain) := by
  have hsrc : (⟨w, hw⟩ : alignedDomain) ∈ (extChartAt (𝓘(ℝ, Plane)) p).source := by
    simp [extChartAt, TopologicalSpace.Opens.chartAt_eq]
  exact (extChartAt (𝓘(ℝ, Plane)) p).left_inv hsrc

private theorem chartBasis_open (p q : alignedDomain)
    (i : Fin (Module.finrank ℝ Plane)) :
    chartBasisVecFiber (I := 𝓘(ℝ, Plane)) p i q = chartModelBasis Plane i := by
  calc
    chartBasisVecFiber (I := 𝓘(ℝ, Plane)) p i q =
      chartBasisVecFiber (I := 𝓘(ℝ, Plane)) q i q :=
        chartBasisVecFiber_eq_of_chartAt_eq (I := 𝓘(ℝ, Plane))
          (show chartAt Plane p = chartAt Plane q by rfl) i q
    _ = _ := by
      simpa only [centeredChartTangentBasis_apply, centeredChartTangentEquiv_symm_apply] using
        chartBasisVecFiber_self (I := 𝓘(ℝ, Plane)) q i

private theorem gram_eq (D : RotationalProfile.PoleData) (p : alignedDomain)
    (w : Plane) (hw : w ∈ alignedDomain) (i j : Fin (Module.finrank ℝ Plane)) :
    chartGramPi (I := 𝓘(ℝ, Plane)) (pullMetric D) p w i j =
      diagonal D.radialCoefficient (RotationalProfile.warp D.a) w i j := by
  rw [chartGramPi_apply, chartGramOnE_def, inverseChart p w hw, chartGramMatrix_apply,
    chartBasis_open, chartBasis_open]
  erw [pullMetric_inner]
  simp only [align_basis_coord]
  rcases index_cases i with rfl | rfl <;> rcases index_cases j with rfl | rfl <;>
    simp [diagonal, radial_apply]

private theorem gram_eventuallyEq (D : RotationalProfile.PoleData) (p : alignedDomain) :
    chartGramPi (I := 𝓘(ℝ, Plane)) (pullMetric D) p =ᶠ[𝓝 p.val]
      diagonal D.radialCoefficient (RotationalProfile.warp D.a) := by
  filter_upwards [alignedDomain.2.mem_nhds p.property] with w hw
  funext i j
  exact gram_eq D p w hw i j

private theorem scalar_smooth (e : ℝ → ℝ) (he : ContDiffOn ℝ ∞ e (Ioo (-1 : ℝ) 1))
    (p : alignedDomain) : ContDiffAt ℝ ∞ e (radial p.val) :=
  (he _ p.property).contDiffAt (isOpen_Ioo.mem_nhds p.property)

private theorem diagonal_smooth (e f : ℝ → ℝ)
    (he : ContDiffOn ℝ ∞ e (Ioo (-1 : ℝ) 1))
    (hf : ContDiffOn ℝ ∞ f (Ioo (-1 : ℝ) 1)) (p : alignedDomain) :
    ContDiffAt ℝ ∞ (diagonal e f) p.val := by
  refine contDiffAt_pi.mpr (fun i => contDiffAt_pi.mpr (fun j => ?_))
  dsimp only [diagonal]
  split_ifs
  · exact (scalar_smooth e he p).comp p.val radial.contDiff.contDiffAt
  · exact (scalar_smooth f hf p).comp p.val radial.contDiff.contDiffAt
  · exact contDiffAt_const

private theorem radialLift_fderiv (e : ℝ → ℝ) (w v : Plane)
    (he : DifferentiableAt ℝ e (radial w)) :
    fderiv ℝ (fun z => e (radial z)) w v = deriv e (radial w) * radial v := by
  have h := he.hasDerivAt.comp_hasFDerivAt w radial.hasFDerivAt
  exact congrArg (fun L : Plane →L[ℝ] ℝ => L v) h.fderiv

private theorem diagonal_d1 (e f : ℝ → ℝ)
    (he : ContDiffOn ℝ ∞ e (Ioo (-1 : ℝ) 1))
    (hf : ContDiffOn ℝ ∞ f (Ioo (-1 : ℝ) 1)) (p : alignedDomain) (v : Plane)
    (i j : Fin (Module.finrank ℝ Plane)) :
    (fderiv ℝ (diagonal e f) p.val) v i j =
      if i = 0 ∧ j = 0 then deriv e (radial p.val) * radial v
      else if i = 1 ∧ j = 1 then deriv f (radial p.val) * radial v else 0 := by
  rw [fderiv_matEntry ((diagonal_smooth e f he hf p).differentiableAt (by simp))]
  by_cases h00 : i = 0 ∧ j = 0
  · simpa [diagonal, h00] using
      radialLift_fderiv e p.val v ((scalar_smooth e he p).differentiableAt (by simp))
  · by_cases h11 : i = 1 ∧ j = 1
    · simpa [diagonal, h11] using
        radialLift_fderiv f p.val v ((scalar_smooth f hf p).differentiableAt (by simp))
    · simp [diagonal, h00, h11]

private theorem diagonal_d2 (e f : ℝ → ℝ)
    (he : ContDiffOn ℝ ∞ e (Ioo (-1 : ℝ) 1))
    (hf : ContDiffOn ℝ ∞ f (Ioo (-1 : ℝ) 1)) (p : alignedDomain) (u v : Plane)
    (i j : Fin (Module.finrank ℝ Plane)) :
    ((fderiv ℝ (fun z => fderiv ℝ (diagonal e f) z) p.val) u) v i j =
      if i = 0 ∧ j = 0 then deriv (deriv e) (radial p.val) * radial u * radial v
      else if i = 1 ∧ j = 1 then deriv (deriv f) (radial p.val) * radial u * radial v
      else 0 := by
  have hs := diagonal_smooth e f he hf p
  have hs2 := (hs.fderiv_right (m := (∞ : WithTop ℕ∞)) (by simp)).differentiableAt (by simp)
  rw [fderiv2_matEntry hs2]
  have heq : (fun z => (fderiv ℝ (diagonal e f) z) v i j) =ᶠ[𝓝 p.val]
      (fun z => if i = 0 ∧ j = 0 then deriv e (radial z) * radial v
        else if i = 1 ∧ j = 1 then deriv f (radial z) * radial v else 0) := by
    filter_upwards [alignedDomain.2.mem_nhds p.property] with z hz
    exact diagonal_d1 e f he hf ⟨z, hz⟩ v i j
  rw [heq.fderiv_eq]
  by_cases h00 : i = 0 ∧ j = 0
  · simp [h00]
    have h := (((scalar_smooth e he p).derivWithin (m := (∞ : WithTop ℕ∞))
      (by simp)).differentiableAt (by simp)).hasDerivAt.comp_hasFDerivAt p.val radial.hasFDerivAt
    have hv := congrArg (fun L : Plane →L[ℝ] ℝ => L u) (h.mul_const (radial v)).fderiv
    simpa [mul_comm, mul_left_comm, mul_assoc] using hv
  · by_cases h11 : i = 1 ∧ j = 1
    · simp [h11]
      have h := (((scalar_smooth f hf p).derivWithin (m := (∞ : WithTop ℕ∞))
        (by simp)).differentiableAt (by simp)).hasDerivAt.comp_hasFDerivAt p.val radial.hasFDerivAt
      have hv := congrArg (fun L : Plane →L[ℝ] ℝ => L u) (h.mul_const (radial v)).fderiv
      simpa [mul_comm, mul_left_comm, mul_assoc] using hv
    · simp [h00, h11]

private theorem scalar_pullMetric (D : RotationalProfile.PoleData) (p : alignedDomain) :
    metricScalarAt (pullMetric D) p = 2 / D.a (radial p.val) := by
  let e := D.radialCoefficient
  let f := RotationalProfile.warp D.a
  have he : ContDiffOn ℝ ∞ e (Ioo (-1 : ℝ) 1) := D.radialCoefficient_contDiffOn
  have hf : ContDiffOn ℝ ∞ f (Ioo (-1 : ℝ) 1) :=
    (RotationalProfile.warp_contDiff D.a D.a_contDiff).contDiffOn
  have heq := gram_eventuallyEq D p
  have hval (i j : Fin (Module.finrank ℝ Plane)) :
      (jet2 (chartGramPi (I := 𝓘(ℝ, Plane)) (pullMetric D) p)
        (extChartAt (𝓘(ℝ, Plane)) p p)).1 i j =
      if i = 0 ∧ j = 0 then e (radial p.val)
      else if i = 1 ∧ j = 1 then f (radial p.val) else 0 := by
    change chartGramPi (I := 𝓘(ℝ, Plane)) (pullMetric D) p p.val i j = _
    exact gram_eq D p p.val p.property i j
  have hd1 (m i j : Fin (Module.finrank ℝ Plane)) :
      (jet2 (chartGramPi (I := 𝓘(ℝ, Plane)) (pullMetric D) p)
        (extChartAt (𝓘(ℝ, Plane)) p p)).2.1 (chartModelBasis Plane m) i j =
      if m = 0 then
        if i = 0 ∧ j = 0 then deriv e (radial p.val)
        else if i = 1 ∧ j = 1 then deriv f (radial p.val) else 0
      else 0 := by
    change (fderiv ℝ (chartGramPi (I := 𝓘(ℝ, Plane)) (pullMetric D) p) p.val)
      (chartModelBasis Plane m) i j = _
    rw [heq.fderiv_eq, diagonal_d1 e f he hf p, radial_basis]
    by_cases hm : m = 0 <;> by_cases h00 : i = 0 ∧ j = 0 <;>
      by_cases h11 : i = 1 ∧ j = 1 <;> simp [hm, h00, h11]
  have hd2 (m n i j : Fin (Module.finrank ℝ Plane)) :
      (jet2 (chartGramPi (I := 𝓘(ℝ, Plane)) (pullMetric D) p)
        (extChartAt (𝓘(ℝ, Plane)) p p)).2.2
          (chartModelBasis Plane m) (chartModelBasis Plane n) i j =
      if m = 0 ∧ n = 0 then
        if i = 0 ∧ j = 0 then deriv (deriv e) (radial p.val)
        else if i = 1 ∧ j = 1 then deriv (deriv f) (radial p.val) else 0
      else 0 := by
    change ((fderiv ℝ (fun z => fderiv ℝ
      (chartGramPi (I := 𝓘(ℝ, Plane)) (pullMetric D) p) z) p.val)
        (chartModelBasis Plane m)) (chartModelBasis Plane n) i j = _
    rw [heq.fderiv.fderiv_eq, diagonal_d2 e f he hf p, radial_basis, radial_basis]
    by_cases hm : m = 0 <;> by_cases hn : n = 0 <;>
      by_cases h00 : i = 0 ∧ j = 0 <;> by_cases h11 : i = 1 ∧ j = 1 <;>
      simp [hm, hn, h00, h11]
  rw [metricScalarAt_eq_radialDiagonalJet (I := 𝓘(ℝ, Plane)) (pullMetric D) p p
    (self_mem_chartLeviCivitaGoodSet (I := 𝓘(ℝ, Plane)) (α := p))
    (e (radial p.val)) (f (radial p.val)) (deriv e (radial p.val))
    (deriv f (radial p.val)) (deriv (deriv e) (radial p.val))
    (deriv (deriv f) (radial p.val)) hval hd1 hd2]
  exact D.radial_curvature_identity (radial p.val) p.property

/-- The actual scalar curvature of the accepted sphere metric on the entire
height cylinder is twice the reciprocal of its original profile. -/
theorem RotationalProfile.PoleData.metricScalarAt_cylinderMap
    (D : RotationalProfile.PoleData) (q : cylinderDomain) :
    metricScalarAt D.metric (cylinderMap q) = 2 / D.a (q.val 0) := by
  let p : alignedDomain := ⟨align.symm q.val, by
    change align (align.symm q.val) ∈ cylinderDomain
    simpa only [align.apply_symm_apply] using q.property⟩
  have hq : alignedToCylinder p = q := by
    apply Subtype.ext
    exact align.apply_symm_apply q.val
  have hr : radial p.val = q.val 0 := by
    rw [radial_apply]
    exact congrArg (fun z : Plane => z 0) (align.apply_symm_apply q.val)
  have hm : alignedMap p = cylinderMap q := congrArg cylinderMap hq
  have hcurv := scalar_pullMetric D p
  rw [pullMetric, metricScalarAt_localPull, hm, hr] at hcurv
  exact hcurv

/-- The actual scalar curvature of the original metric is twice the reciprocal
profile everywhere on the sphere, including both poles. -/
theorem RotationalProfile.PoleData.metricScalarAt_metric
    (D : RotationalProfile.PoleData) (p : RotationalSphere) :
    metricScalarAt D.metric p = 2 / D.a (sphereHeight p) := by
  have hright : Continuous (fun x : RotationalSphere => 2 / D.a (sphereHeight x)) :=
    continuous_const.div (D.a_contDiff.continuous.comp sphereHeight_contMDiff.continuous)
      (fun x => (D.a_pos _ (sphereHeight_mem_Icc x)).ne')
  have heq := denseRange_cylinderMap.equalizer (metricScalar_smooth D.metric).continuous
    hright (by
      funext q
      simpa using D.metricScalarAt_cylinderMap q)
  exact congrFun heq p

/-- Every actual tangent two-plane has Gauss curvature equal to the reciprocal
of the same profile at the actual height. -/
theorem RotationalProfile.PoleData.sectionalCurvature_metric
    (D : RotationalProfile.PoleData) (p : RotationalSphere)
    (v w : TangentSpace (𝓡 2) p) (hvw : LinearIndependent ℝ ![v, w]) :
    Riemannian.sectionalCurvature D.metric p v w = 1 / D.a (sphereHeight p) := by
  rw [Riemannian.sectionalCurvature_eq_scalar_div_two_of_finrank_eq_two
    D.metric (by simp) p v w hvw, D.metricScalarAt_metric]
  ring

end RicciFlowSharpEstimate.Geometry
