/-
Copyright (c) 2026 Ziyang Qin. All rights reserved.
No license is granted by this file.
Authors: Ziyang Qin
-/
import RicciFlowSharpEstimate.Geometry.RotationalOneForms
import RicciFlowSharpEstimate.Geometry.CanonicalDerivatives
import RicciFlowSharpEstimate.Geometry.RotationalCurvature
import DifferentialGeometry.Geometry.Operator.Pullback
import DifferentialGeometry.Geometry.Connection.ChartBridge.Scalar.HessianNorm

/-!
# The genuine covariant derivative of meridional one-forms

The actual meridional section is the differential of its global height potential.
Its first covariant derivative is computed through the metric's Levi-Civita Hessian.
-/

noncomputable section

namespace RicciFlowSharpEstimate.Geometry

open Bundle Manifold Set TopologicalSpace Filter
open DifferentialGeometry DifferentialGeometry.Analysis DifferentialGeometry.Geometry
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Operator DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Tensor.Coordinates DifferentialGeometry.Tensor.RicciIdentity
open DifferentialGeometry.Integral.Connection DifferentialGeometry.PDE.RicciFlow
open scoped Manifold ContDiff Topology

local instance : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 2 + 1) :=
  ⟨finrank_euclideanSpace_fin⟩

namespace RotationalProfile.PoleData

/-- The normalized primitive of the actual meridional coefficient. -/
def meridionalPrimitive (D : PoleData) (r : ℝ → ℝ) : ℝ → ℝ :=
  momentCoordinate (fun z => D.a z * r z)

/-- The primitive is smooth for every globally smooth probe. -/
theorem meridionalPrimitive_contDiff (D : PoleData) (r : ℝ → ℝ)
    (hr : ContDiff ℝ ∞ r) : ContDiff ℝ ∞ (D.meridionalPrimitive r) :=
  momentCoordinate_contDiff _ (D.a_contDiff.mul hr)

/-- The exact derivative of the normalized primitive. -/
theorem meridionalPrimitive_hasDerivAt (D : PoleData) (r : ℝ → ℝ)
    (hr : ContDiff ℝ ∞ r) (z : ℝ) :
    HasDerivAt (D.meridionalPrimitive r) (D.a z * r z) z :=
  momentCoordinate_hasDerivAt _ (D.a_contDiff.continuous.mul hr.continuous) z

/-- The global height potential producing the accepted meridional one-form. -/
def meridionalPotential (D : PoleData) (r : ℝ → ℝ) : RotationalSphere → ℝ :=
  fun x => D.meridionalPrimitive r (sphereHeight x)

/-- The genuine meridional potential is smooth across both poles. -/
theorem meridionalPotential_contMDiff (D : PoleData) (r : ℝ → ℝ)
    (hr : ContDiff ℝ ∞ r) : ContMDiff (𝓡 2) 𝓘(ℝ) ∞ (D.meridionalPotential r) :=
  (D.meridionalPrimitive_contDiff r hr).comp_contMDiff sphereHeight_contMDiff

/-- Its genuine differential is exactly the accepted meridional section. -/
theorem duSec_meridionalPotential (D : PoleData) (r : ℝ → ℝ)
    (hr : ContDiff ℝ ∞ r) :
    duSec (I := 𝓡 2) (D.meridionalPotential r)
      (D.meridionalPotential_contMDiff r hr) = D.meridionalOneForm r hr := by
  apply DFunLike.ext
  intro x
  apply ContinuousMultilinearMap.ext
  intro slots
  have hslots : slots = fun _ : Fin 1 => slots 0 := by
    funext i
    fin_cases i
    rfl
  rw [hslots]
  change duSec (I := 𝓡 2) _ _ x (fun _ : Fin 1 => slots 0) =
    D.meridionalOneForm r hr x (fun _ : Fin 1 => slots 0)
  rw [meridionalOneForm_apply, duSec_apply,
    differential1FormFun_apply_eq_mvfderiv]
  change mvfderiv (𝓡 2) (D.meridionalPrimitive r ∘ sphereHeight) x (slots 0) = _
  rw [mvfderiv_comp_apply x
    ((D.meridionalPrimitive_hasDerivAt r hr (sphereHeight x)).differentiableAt.mdifferentiableAt)
    (sphereHeight_contMDiff.mdifferentiableAt (by simp)), mvfderiv_real_model_eq_fderiv,
    (D.meridionalPrimitive_hasDerivAt r hr (sphereHeight x)).hasFDerivAt.fderiv]
  rw [heightOneForm, duSec_apply, differential1FormFun_apply_eq_mvfderiv,
    mvfderiv_real_eq_mfderiv]
  simp only [ContinuousLinearMap.toSpanSingleton_apply, smul_eq_mul]
  ring

/-- The native first derivative of the meridional form is its potential Hessian. -/
theorem metricNabla0S_meridionalOneForm_eq_leviHessSec (D : PoleData) (r : ℝ → ℝ)
    (hr : ContDiff ℝ ∞ r) :
    metricNabla0S D.metric (D.meridionalOneForm r hr) =
      leviHessSec D.metric (D.meridionalPotential r)
        (D.meridionalPotential_contMDiff r hr) := by
  rw [← D.duSec_meridionalPotential r hr]
  rfl

end RotationalProfile.PoleData

private abbrev Plane := EuclideanSpace ℝ (Fin 2)
private local instance : NeZero (Module.finrank ℝ Plane) := ⟨by simp [Plane]⟩

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


private theorem scalarOnE_radial (f : ℝ → ℝ) (p : alignedDomain) :
    scalarOnE (I := 𝓘(ℝ, Plane)) p (fun q : alignedDomain => f (radial q.val)) =ᶠ[𝓝 p.val]
      (fun w => f (radial w)) := by
  filter_upwards [alignedDomain.2.mem_nhds p.property] with w hw
  simp only [scalarOnE_def, inverseChart p w hw]

private theorem scalar_partial (f : ℝ → ℝ) (hf : ContDiff ℝ ∞ f)
    (p : alignedDomain) (i : Fin (Module.finrank ℝ Plane)) :
    partialDeriv (E := Plane) i
        (scalarOnE (I := 𝓘(ℝ, Plane)) p (fun q : alignedDomain => f (radial q.val))) p.val =
      deriv f (radial p.val) * radial (chartModelBasis Plane i) := by
  rw [partialDeriv, (scalarOnE_radial f p).fderiv_eq]
  exact radialLift_fderiv f p.val _ (hf.differentiable (by simp) _)

private theorem scalar_iteratedPartial (f : ℝ → ℝ) (hf : ContDiff ℝ ∞ f)
    (p : alignedDomain) (i j : Fin (Module.finrank ℝ Plane)) :
    chartIteratedPartialDeriv (I := 𝓘(ℝ, Plane)) p
        (fun q : alignedDomain => f (radial q.val)) i j p.val =
      deriv (deriv f) (radial p.val) * radial (chartModelBasis Plane i) *
        radial (chartModelBasis Plane j) := by
  have hderiv := (scalarOnE_radial f p).fderiv (𝕜 := ℝ)
  have hpartial : partialDeriv (E := Plane) j
      (scalarOnE (I := 𝓘(ℝ, Plane)) p (fun q : alignedDomain => f (radial q.val)))
      =ᶠ[𝓝 p.val] (fun w => deriv f (radial w) * radial (chartModelBasis Plane j)) := by
    filter_upwards [hderiv] with w hw
    rw [partialDeriv, hw, radialLift_fderiv f w _ (hf.differentiable (by simp) _)]
  have hd : ContDiff ℝ ∞ (deriv f) := (contDiff_infty_iff_deriv.mp hf).2
  change fderiv ℝ (partialDeriv (E := Plane) j
    (scalarOnE (I := 𝓘(ℝ, Plane)) p (fun q : alignedDomain => f (radial q.val)))) p.val
      (chartModelBasis Plane i) = _
  rw [hpartial.fderiv_eq]
  have h := (((hd.differentiable (by simp) (radial p.val)).hasDerivAt.comp_hasFDerivAt
    p.val radial.hasFDerivAt).mul_const (radial (chartModelBasis Plane j))).fderiv
  simp only [Function.comp_apply] at h
  rw [h]
  simp only [smul_apply, smul_eq_mul]
  ring

private theorem inverse_of_radialDiagonal
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (p : MatJet V 2) (e f : ℝ) (he : e ≠ 0) (hf : f ≠ 0)
    (hval : ∀ i j : Fin 2, p.1 i j =
      if i = 0 ∧ j = 0 then e else if i = 1 ∧ j = 1 then f else 0) :
    ∀ i j : Fin 2, (Matrix.of p.1)⁻¹ i j =
      if i = 0 ∧ j = 0 then 1 / e else if i = 1 ∧ j = 1 then 1 / f else 0 := by
  let d : Fin 2 → ℝ := fun i => if i = 0 then e else f
  have hp : Matrix.of p.1 = Matrix.diagonal d := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [hval, d]
  have hdUnit : IsUnit d := by
    rw [Pi.isUnit_iff]
    intro i
    fin_cases i <;> simp [d, he, hf]
  rw [hp, Matrix.inv_diagonal]
  intro i j
  fin_cases i <;> fin_cases j <;> simp only [Matrix.diagonal_apply]
  · rw [← hdUnit.unit_spec, Ring.inverse_unit, IsUnit.val_inv_apply]
    simp [d, one_div]
  · simp
  · simp
  · rw [← hdUnit.unit_spec, Ring.inverse_unit, IsUnit.val_inv_apply]
    simp [d, one_div]

private theorem christoffel_radialDiagonal
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {n : ℕ} [NeZero n] (hn : n = 2) (basis : Fin n → V)
    (p : MatJet V n) (e f e₁ f₁ : ℝ) (he : e ≠ 0) (hf : f ≠ 0)
    (hval : ∀ i j : Fin n, p.1 i j =
      if i = 0 ∧ j = 0 then e else if i = 1 ∧ j = 1 then f else 0)
    (hd1 : ∀ m i j : Fin n, p.2.1 (basis m) i j =
      if m = 0 then
        if i = 0 ∧ j = 0 then e₁ else if i = 1 ∧ j = 1 then f₁ else 0
      else 0)
    (i j : Fin n) :
    jetChristoffel basis p i j 0 =
      if i = 0 ∧ j = 0 then e₁ / (2 * e)
      else if i = 1 ∧ j = 1 then -f₁ / (2 * e) else 0 := by
  subst n
  have hinv := inverse_of_radialDiagonal p e f he hf hval
  fin_cases i <;> fin_cases j <;>
    simp [jetChristoffel, hinv, hd1] <;> ring

private theorem pullMetric_christoffel (D : RotationalProfile.PoleData) (p : alignedDomain)
    (i j : Fin (Module.finrank ℝ Plane)) :
    chartChristoffel (I := 𝓘(ℝ, Plane)) (pullMetric D) p i j 0 p.val =
      if i = 0 ∧ j = 0 then deriv D.radialCoefficient (radial p.val) /
        (2 * D.radialCoefficient (radial p.val))
      else if i = 1 ∧ j = 1 then -deriv (RotationalProfile.warp D.a) (radial p.val) /
        (2 * D.radialCoefficient (radial p.val)) else 0 := by
  let e := D.radialCoefficient
  let f := RotationalProfile.warp D.a
  have he : ContDiffOn ℝ ∞ e (Ioo (-1 : ℝ) 1) := D.radialCoefficient_contDiffOn
  have hf : ContDiffOn ℝ ∞ f (Ioo (-1 : ℝ) 1) :=
    (RotationalProfile.warp_contDiff D.a D.a_contDiff).contDiffOn
  have heq := gram_eventuallyEq D p
  have hval (i j : Fin (Module.finrank ℝ Plane)) :
      (jet2 (chartGramPi (I := 𝓘(ℝ, Plane)) (pullMetric D) p) p.val).1 i j =
      if i = 0 ∧ j = 0 then e (radial p.val)
      else if i = 1 ∧ j = 1 then f (radial p.val) else 0 :=
    gram_eq D p p.val p.property i j
  have hd1 (m i j : Fin (Module.finrank ℝ Plane)) :
      (jet2 (chartGramPi (I := 𝓘(ℝ, Plane)) (pullMetric D) p) p.val).2.1
        (chartModelBasis Plane m) i j =
      if m = 0 then
        if i = 0 ∧ j = 0 then deriv e (radial p.val)
        else if i = 1 ∧ j = 1 then deriv f (radial p.val) else 0
      else 0 := by
    change (fderiv ℝ (chartGramPi (I := 𝓘(ℝ, Plane)) (pullMetric D) p) p.val)
      (chartModelBasis Plane m) i j = _
    rw [heq.fderiv_eq, diagonal_d1 e f he hf p, radial_basis]
    by_cases hm : m = 0 <;> by_cases h00 : i = 0 ∧ j = 0 <;>
      by_cases h11 : i = 1 ∧ j = 1 <;> simp [hm, h00, h11]
  have ha := (D.a_pos (radial p.val) ⟨p.property.1.le, p.property.2.le⟩).ne'
  have hw := (D.cylinderMap_warp_pos (alignedToCylinder p)).ne'
  have he0 : e (radial p.val) ≠ 0 := div_ne_zero (pow_ne_zero 2 ha) hw
  rw [chartChristoffel_eq_jet (pullMetric D) p
    (((diagonal_smooth e f he hf p).differentiableAt (by simp)).congr_of_eventuallyEq
      heq)]
  exact christoffel_radialDiagonal finrank_euclideanSpace_fin (chartModelBasis Plane) _
    (e (radial p.val)) (f (radial p.val)) (deriv e (radial p.val))
    (deriv f (radial p.val)) he0 hw hval hd1 i j

private theorem sum_two {n : ℕ} [NeZero n] (hn : n = 2) (f : Fin n → ℝ) :
    ∑ i, f i = f 0 + f 1 := by
  subst n
  exact Fin.sum_univ_two f

private theorem primitive_second (D : RotationalProfile.PoleData) (r : ℝ → ℝ)
    (hr : ContDiff ℝ ∞ r) (z : ℝ) :
    deriv (deriv (D.meridionalPrimitive r)) z = deriv D.a z * r z + D.a z * deriv r z := by
  have hd : deriv (D.meridionalPrimitive r) = fun z => D.a z * r z :=
    funext (fun z => (D.meridionalPrimitive_hasDerivAt r hr z).deriv)
  rw [hd]
  exact ((D.a_contDiff.differentiable (by simp) z).hasDerivAt.mul
    (hr.differentiable (by simp) z).hasDerivAt).deriv

private theorem hessian_component (D : RotationalProfile.PoleData) (r : ℝ → ℝ)
    (hr : ContDiff ℝ ∞ r) (p : alignedDomain) (i j : Fin (Module.finrank ℝ Plane)) :
    chartHessianTensor (I := 𝓘(ℝ, Plane)) (pullMetric D) p
        (fun q : alignedDomain => D.meridionalPrimitive r (radial q.val)) i j p =
      if i = 0 ∧ j = 0 then D.a (radial p.val) * deriv r (radial p.val) -
        radial p.val * r (radial p.val) * D.radialCoefficient (radial p.val)
      else if i = 1 ∧ j = 1 then -radial p.val * r (radial p.val) *
        RotationalProfile.warp D.a (radial p.val) else 0 := by
  rw [chartHessianTensor_def]
  change chartIteratedPartialDeriv (I := 𝓘(ℝ, Plane)) p
      (fun q : alignedDomain => D.meridionalPrimitive r (radial q.val)) i j p.val - _ = _
  rw [scalar_iteratedPartial _ (D.meridionalPrimitive_contDiff r hr),
    sum_two finrank_euclideanSpace_fin]
  have hchart : extChartAt (𝓘(ℝ, Plane)) p p = p.val := rfl
  rw [hchart]
  rw [scalar_partial _ (D.meridionalPrimitive_contDiff r hr),
    scalar_partial _ (D.meridionalPrimitive_contDiff r hr), radial_basis,
    radial_basis, radial_basis, radial_basis, primitive_second D r hr,
    (D.meridionalPrimitive_hasDerivAt r hr (radial p.val)).deriv]
  have h01 : (0 : Fin (Module.finrank ℝ Plane)) ≠ 1 := by
    intro h
    have hh := congrArg Fin.val h
    norm_num [Plane] at hh
  have h10 := h01.symm
  simp only [ite_true, h10, ite_false, mul_zero, mul_one, add_zero]
  rw [pullMetric_christoffel]
  have ha := (D.a_pos (radial p.val) ⟨p.property.1.le, p.property.2.le⟩).ne'
  have hw := (D.cylinderMap_warp_pos (alignedToCylinder p)).ne'
  change RotationalProfile.warp D.a (radial p.val) ≠ 0 at hw
  rw [(D.radialCoefficient_hasDerivAt (radial p.val) p.property).deriv,
    RotationalProfile.deriv_warp_eq D.a D.a_contDiff.continuous,
    RotationalProfile.PoleData.radialCoefficient]
  rcases index_cases i with rfl | rfl <;> rcases index_cases j with rfl | rfl <;>
    simp [h01, h10] <;> field_simp [ha, hw]
  all_goals ring

private theorem model_repr_coord (v : Plane) (j : Fin 2) :
    (chartModelBasis Plane).repr v (finCongr finrank_euclideanSpace_fin.symm j) =
      (align v) j := by
  have h := congrArg (fun w : Plane => (align w) j) ((chartModelBasis Plane).sum_repr v)
  simp only [map_sum, map_smul, WithLp.ofLp_sum, Finset.sum_apply, PiLp.smul_apply, smul_eq_mul,
    align_basis_coord] at h
  rw [sum_two finrank_euclideanSpace_fin] at h
  fin_cases j
  · simpa using h
  · have hi : finCongr finrank_euclideanSpace_fin.symm (1 : Fin 2) =
        (1 : Fin (Module.finrank ℝ Plane)) := by apply Fin.ext; simp [finCongr]
    change (chartModelBasis Plane).repr v (finCongr finrank_euclideanSpace_fin.symm (1 : Fin 2)) =
      (align v) 1
    rw [hi]
    simpa using h

private theorem centered_repr (p : alignedDomain) (v : Plane)
    (i : Fin (Module.finrank ℝ Plane)) :
    (centeredChartTangentBasis (I := 𝓘(ℝ, Plane)) p).repr v i =
      (chartModelBasis Plane).repr v i := by
  have hb : centeredChartTangentBasis (I := 𝓘(ℝ, Plane)) p = chartModelBasis Plane := by
    apply DFunLike.ext
    intro j
    simp only [centeredChartTangentBasis_apply, centeredChartTangentEquiv_symm_apply]
    rfl
  rw [hb]
  rfl

private theorem hessian_pullMetric (D : RotationalProfile.PoleData) (r : ℝ → ℝ)
    (hr : ContDiff ℝ ∞ r) (p : alignedDomain) (v w : Plane) :
    hessFun (pullMetric D)
        (fun q : alignedDomain => D.meridionalPrimitive r (radial q.val)) p v w =
      D.a (radial p.val) * deriv r (radial p.val) * (align v) 0 * (align w) 0 -
        radial p.val * r (radial p.val) * (pullMetric D).inner p v w := by
  erw [hessFun_apply]
  simp_rw [centered_repr, hessian_component D r hr p]
  rw [sum_two finrank_euclideanSpace_fin, sum_two finrank_euclideanSpace_fin,
    sum_two finrank_euclideanSpace_fin]
  have hv0 := model_repr_coord v 0
  have hv1 := model_repr_coord v 1
  have hw0 := model_repr_coord w 0
  have hw1 := model_repr_coord w 1
  have hi0 : finCongr finrank_euclideanSpace_fin.symm (0 : Fin 2) =
      (0 : Fin (Module.finrank ℝ Plane)) := by apply Fin.ext; simp [finCongr]
  have hi1 : finCongr finrank_euclideanSpace_fin.symm (1 : Fin 2) =
      (1 : Fin (Module.finrank ℝ Plane)) := by apply Fin.ext; simp [finCongr]
  rw [hi0] at hv0 hw0
  rw [hi1] at hv1 hw1
  rw [hv0, hv1, hw0, hw1, pullMetric_inner]
  have h01 : (0 : Fin (Module.finrank ℝ Plane)) ≠ 1 := by
    intro h
    have hh := congrArg Fin.val h
    norm_num [Plane] at hh
  simp only [ite_true, h01, h01.symm, and_self, and_false, and_true, ite_false,
    mul_zero, add_zero, zero_add]
  rw [radial_apply]
  ring

private theorem sphere_hessSec_abs
    (g : SmoothRiemannianMetric (𝓡 2) RotationalSphere)
    {f : RotationalSphere -> Real} (hf : ContMDiff (𝓡 2) 𝓘(Real, Real) ∞ f)
    (x : RotationalSphere) (v w : TangentSpace (𝓡 2) x) :
    leviHessSec (I := 𝓡 2) g f hf x (vec2 (I := 𝓡 2) v w) =
      abstractHessian (I := 𝓡 2) g f x v w := by
  classical
  change hessianSec (I := 𝓡 2)
      (leviCivitaConnectionOfMetric (I := 𝓡 2) g)
      (leviCivitaConnectionOfMetric_contMDiffCovariantDerivativeLocally
        (I := 𝓡 2) (M := RotationalSphere) g)
      f hf x (vec2 (I := 𝓡 2) v w) = _
  let cov := leviCivitaConnectionOfMetric (I := 𝓡 2) g
  let hcov :=
    leviCivitaConnectionOfMetric_contMDiffCovariantDerivativeLocally
      (I := 𝓡 2) (M := RotationalSphere) g
  obtain ⟨X, hX⟩ :=
    ContMDiffSection.exists_eq_at
      (I := 𝓡 2) (F := EuclideanSpace ℝ (Fin 2)) (V := TangentSpace (𝓡 2)) (n := (⊤ : ℕ∞)) x v
  obtain ⟨Y, hY⟩ :=
    ContMDiffSection.exists_eq_at
      (I := 𝓡 2) (F := EuclideanSpace ℝ (Fin 2)) (V := TangentSpace (𝓡 2)) (n := (⊤ : ℕ∞)) x w
  have hsec := (hessianSec_nabla (I := 𝓡 2) cov hcov f hf) x X (Y x)
  have heval := nabla0SFun_one_eval_smooth_slots
    (I := 𝓡 2) cov X Y (duSec (I := 𝓡 2) f hf) x
  have htheta : MDiffAtCotangent (mvfderiv (I := 𝓡 2) f) x :=
    ((cotangentCov_mvfderiv_smooth (I := 𝓡 2) hf) x).mdifferentiableAt (by simp)
  have hYmd := Y.mdifferentiableAt (x := x)
  have hpair := cotangentCov_dualPairing cov htheta hYmd (X x)
  have hdufun :
      (fun p : RotationalSphere => duSec (I := 𝓡 2) f hf p (fun _ : Fin 1 => Y p)) =
        fun p : RotationalSphere => mvfderiv (I := 𝓡 2) f p (Y p) := by
    funext p
    rw [duSec_apply]
    exact differential1FormFun_apply_eq_mvfderiv (I := 𝓡 2) f p (Y p)
  rw [← hX, ← hY]
  rw [hsec]
  change
    (nabla0SFun (𝕜 := Real) (E := EuclideanSpace ℝ (Fin 2))
      (H := EuclideanSpace ℝ (Fin 2)) (I := 𝓡 2) (M := RotationalSphere)
      1 cov X (duSec (I := 𝓡 2) f hf) x) (fun _ : Fin 1 => Y x) = _
  rw [heval, hdufun, duSec_apply,
    differential1FormFun_apply_eq_mvfderiv]
  change
    mvfderiv (I := 𝓡 2) (fun p : RotationalSphere => mvfderiv (I := 𝓡 2) f p (Y p)) x (X x) -
        mvfderiv (I := 𝓡 2) f x ((cov (fun p : RotationalSphere => Y p) x) (X x)) =
      ((cotangentCov cov).toFun (mvfderiv (I := 𝓡 2) f) x (X x)) (Y x)
  linarith


private theorem alignedMap_deriv (p : alignedDomain) (v : Plane) :
    mfderiv (𝓘(ℝ, Plane)) (𝓡 2) alignedMap p v =
      mfderiv (𝓘(ℝ, Plane)) (𝓡 2) cylinderMap (alignedToCylinder p) (align v) := by
  change mfderiv (𝓘(ℝ, Plane)) (𝓡 2) (cylinderMap ∘ alignedToCylinder) p v = _
  erw [mfderiv_comp_apply p (cylinderMap_contMDiff.mdifferentiableAt (by simp))
    (alignedToCylinder_smooth.mdifferentiableAt (by simp))]
  erw [alignedToCylinder_deriv]

private theorem alignedMap_height (p : alignedDomain) :
    sphereHeight (alignedMap p) = radial p.val := sphereHeight_cylinderMap _

private theorem alignedMap_heightOneForm (p : alignedDomain) (v : Plane) :
    heightOneForm (alignedMap p) (fun _ : Fin 1 =>
      mfderiv (𝓘(ℝ, Plane)) (𝓡 2) alignedMap p v) = (align v) 0 := by
  erw [alignedMap_deriv, heightOneForm_apply_dIncl]
  change (dIncl (n := 2) (cylinderMap (alignedToCylinder p))
    (mfderiv (𝓘(ℝ, Plane)) (𝓡 2) cylinderMap (alignedToCylinder p) (align v))) 2 = _
  rw [cylinderMap_dIncl_mfderiv]
  rfl

private theorem meridional_nabla_aligned (D : RotationalProfile.PoleData) (r : ℝ → ℝ)
    (hr : ContDiff ℝ ∞ r) (p : alignedDomain) (v w : Plane) :
    metricNabla0S D.metric (D.meridionalOneForm r hr) (alignedMap p)
        (vec2 (I := 𝓡 2) (mfderiv (𝓘(ℝ, Plane)) (𝓡 2) alignedMap p v)
          (mfderiv (𝓘(ℝ, Plane)) (𝓡 2) alignedMap p w)) =
      D.a (radial p.val) * deriv r (radial p.val) * (align v) 0 * (align w) 0 -
        radial p.val * r (radial p.val) * D.metric.inner (alignedMap p)
          (mfderiv (𝓘(ℝ, Plane)) (𝓡 2) alignedMap p v)
          (mfderiv (𝓘(ℝ, Plane)) (𝓡 2) alignedMap p w) := by
  rw [D.metricNabla0S_meridionalOneForm_eq_leviHessSec, sphere_hessSec_abs,
    ← hessFun_eq_abstract D.metric (D.meridionalPotential_contMDiff r hr)]
  let F : C^∞⟮𝓡 2, RotationalSphere; ℝ⟯ :=
    ⟨D.meridionalPotential r, D.meridionalPotential_contMDiff r hr⟩
  have hf : (F ∘ alignedMap) =
      (fun q : alignedDomain => D.meridionalPrimitive r (radial q.val)) := by
    funext q
    exact congrArg (D.meridionalPrimitive r) (alignedMap_height q)
  let : SigmaCompactSpace alignedDomain :=
    isSigmaCompact_iff_sigmaCompactSpace.mp
      (DifferentialGeometry.Geometry.isSigmaCompact_of_isOpen (𝓘(ℝ, Plane)) alignedDomain.isOpen)
  have hpull := hessFun_localPull D.metric alignedMap alignedMap_localDiffeomorph F p v w
  rw [hf] at hpull
  erw [← hpull, hessian_pullMetric D r hr]
  rfl

/-- The exact first metric derivative on the image of the genuine cylinder map. -/
theorem RotationalProfile.PoleData.metricNabla0S_meridionalOneForm_cylinderMap
    (D : RotationalProfile.PoleData) (r : ℝ → ℝ) (hr : ContDiff ℝ ∞ r)
    (q : cylinderDomain) (v w : TangentSpace (𝓡 2) (cylinderMap q)) :
    metricNabla0S D.metric (D.meridionalOneForm r hr) (cylinderMap q) (vec2 (I := 𝓡 2) v w) =
      D.a (sphereHeight (cylinderMap q)) * deriv r (sphereHeight (cylinderMap q)) *
        heightOneForm (cylinderMap q) (fun _ : Fin 1 => v) *
        heightOneForm (cylinderMap q) (fun _ : Fin 1 => w) -
      sphereHeight (cylinderMap q) * r (sphereHeight (cylinderMap q)) *
        D.metric.inner (cylinderMap q) v w := by
  have halign (p : alignedDomain) (v w : TangentSpace (𝓡 2) (alignedMap p)) :
      metricNabla0S D.metric (D.meridionalOneForm r hr) (alignedMap p) (vec2 (I := 𝓡 2) v w) =
        D.a (sphereHeight (alignedMap p)) * deriv r (sphereHeight (alignedMap p)) *
          heightOneForm (alignedMap p) (fun _ : Fin 1 => v) *
          heightOneForm (alignedMap p) (fun _ : Fin 1 => w) -
        sphereHeight (alignedMap p) * r (sphereHeight (alignedMap p)) *
          D.metric.inner (alignedMap p) v w := by
    have hinj : Function.Injective (mfderiv (𝓘(ℝ, Plane)) (𝓡 2) alignedMap p) := by
      intro u z h
      erw [alignedMap_deriv, alignedMap_deriv] at h
      exact align.injective (cylinderMap_mfderiv_injective (alignedToCylinder p) h)
    have hsurj := (LinearMap.injective_iff_surjective).mp hinj
    obtain ⟨v₀, rfl⟩ := hsurj v
    obtain ⟨w₀, rfl⟩ := hsurj w
    erw [alignedMap_height, alignedMap_heightOneForm, alignedMap_heightOneForm]
    exact meridional_nabla_aligned D r hr p v₀ w₀
  let p : alignedDomain := ⟨align.symm q.val, by
    change align (align.symm q.val) ∈ cylinderDomain
    simp⟩
  have hp : alignedToCylinder p = q := by
    apply Subtype.ext
    exact align.apply_symm_apply q.val
  have hmap : alignedMap p = cylinderMap q := congrArg cylinderMap hp
  have hh := halign p
  rw [hmap] at hh
  exact hh v w

/-- The actual global first metric covariant derivative of every smooth meridional probe. -/
theorem RotationalProfile.PoleData.metricNabla0S_meridionalOneForm
    (D : RotationalProfile.PoleData) (r : ℝ → ℝ) (hr : ContDiff ℝ ∞ r)
    (x : RotationalSphere) (slots : Fin 2 → TangentSpace (𝓡 2) x) :
    metricNabla0S D.metric (D.meridionalOneForm r hr) x slots =
      D.a (sphereHeight x) * deriv r (sphereHeight x) *
        heightOneForm x (fun _ : Fin 1 => slots 0) *
        heightOneForm x (fun _ : Fin 1 => slots 1) -
      sphereHeight x * r (sphereHeight x) * D.metric.inner x (slots 0) (slots 1) := by
  obtain ⟨X, hX⟩ := ContMDiffSection.exists_eq_at
    (I := 𝓡 2) (F := EuclideanSpace ℝ (Fin 2)) (V := TangentSpace (𝓡 2))
    (n := (⊤ : ℕ∞)) x (slots 0)
  obtain ⟨Y, hY⟩ := ContMDiffSection.exists_eq_at
    (I := 𝓡 2) (F := EuclideanSpace ℝ (Fin 2)) (V := TangentSpace (𝓡 2))
    (n := (⊤ : ℕ∞)) x (slots 1)
  let fields : Fin 2 → ContMDiffSection (𝓡 2) (EuclideanSpace ℝ (Fin 2)) ∞
      (TangentSpace (𝓡 2) : RotationalSphere → Type) := fun i => if i = 0 then X else Y
  have hfields (p : RotationalSphere) : (fun i : Fin 2 => fields i p) =
      vec2 (I := 𝓡 2) (X p) (Y p) := by
    funext i
    fin_cases i <;> rfl
  have hleft := TensorMultilinear.contMDiff_tensor0SField_apply
    (metricNabla0S D.metric (D.meridionalOneForm r hr)) fields
  simp only [hfields] at hleft
  have hheightX := TensorMultilinear.contMDiff_tensor0SField_apply heightOneForm
    (fun _ : Fin 1 => X)
  have hheightY := TensorMultilinear.contMDiff_tensor0SField_apply heightOneForm
    (fun _ : Fin 1 => Y)
  have hmetric : ContMDiff (𝓡 2) 𝓘(ℝ) ∞
      (fun p => D.metric.inner p (X p) (Y p)) := by
    intro p
    exact Curvature.CovariantDerivative.metric_inner_contMDiffAt D.metric
      X.contMDiff.contMDiffAt Y.contMDiff.contMDiffAt le_rfl
  have ha := D.a_contDiff.continuous.comp sphereHeight_contMDiff.continuous
  have hdr := ((contDiff_infty_iff_deriv.mp hr).2.continuous).comp
    sphereHeight_contMDiff.continuous
  have hright := (((ha.mul hdr).mul hheightX.continuous).mul hheightY.continuous).sub
    ((sphereHeight_contMDiff.continuous.mul
      (hr.continuous.comp sphereHeight_contMDiff.continuous)).mul hmetric.continuous)
  have heq := denseRange_cylinderMap.equalizer hleft.continuous hright (by
    funext q
    exact D.metricNabla0S_meridionalOneForm_cylinderMap r hr q (X (cylinderMap q))
      (Y (cylinderMap q)))
  have hx := congrFun heq x
  have hs : vec2 (I := 𝓡 2) (X x) (Y x) = slots := by
    funext i
    fin_cases i
    · exact hX
    · exact hY
  simp only [Pi.sub_apply, Pi.mul_apply, Function.comp_apply] at hx
  rw [hs] at hx
  simpa only [hX, hY] using hx

end RicciFlowSharpEstimate.Geometry
