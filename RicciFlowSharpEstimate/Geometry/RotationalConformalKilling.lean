/-
Copyright (c) 2026 Ziyang Qin. All rights reserved.
No license is granted by this file.
Authors: Ziyang Qin
-/
import RicciFlowSharpEstimate.Geometry.ConformalKillingOneForms
import RicciFlowSharpEstimate.Geometry.RotationalInvariantClassification

/-!
# Conformal Killing one-forms on rotational spheres

Invariant conformal Killing forms are constant combinations of the actual
meridional and azimuthal generators. Haar averaging preserves the equation of
the original smooth form. Probe constancy is proved only on the closed physical
height interval, using the genuine Ahlfors norm and meridian reflection.

The argument adapts Ziyang Qin's historical `RotationalConformalKilling.lean`.
-/

noncomputable section

namespace RicciFlowSharpEstimate.Geometry

open Bundle DifferentialGeometry DifferentialGeometry.Geometry
open DifferentialGeometry.Tensor0SBundle DifferentialGeometry.Tensor.RicciIdentity
open DifferentialGeometry.PDE.RicciFlow
open Set
open scoped Manifold ContDiff

local instance : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 2 + 1) :=
  ⟨finrank_euclideanSpace_fin⟩

namespace RotationalProfile.PoleData

/-- The genuine meridional constant probes satisfy the conformal Killing equation
globally, including both poles. -/
theorem isConformalKillingOneForm_meridional_const (D : PoleData) (c : ℝ) :
    IsConformalKillingOneForm D.metric
      (D.meridionalOneForm (fun _ => c) contDiff_const) := by
  rw [isConformalKillingOneForm_iff_normSq_eq_zero]
  intro x
  rw [D.meridionalOneForm_ahlfors_normSq]
  simp

/-- Hodge rotation identifies the actual azimuthal Ahlfors norm with the same
weighted derivative square as in the meridional sector. -/
theorem azimuthalOneForm_ahlfors_normSq (D : PoleData) (r : ℝ → ℝ)
    (hr : ContDiff ℝ ∞ r) (x : RotationalSphere) :
    normSq0S D.metric x 2
      (ahlforsPart D.metric (metricNabla0S D.metric (D.azimuthalOneForm r hr)) x) =
        (D.meridionalWeight (sphereHeight x) * deriv r (sphereHeight x)) ^ 2 / 2 := by
  have hrot := normSq0S_ahlforsPart_eq_of_rotation finrank_euclideanSpace_fin
    D.metric x (D.areaForm x) (D.areaForm_alternating x) (D.areaForm_normSq x)
    (metricNabla0S D.metric (D.meridionalOneForm r hr))
    (metricNabla0S D.metric (D.hodgeRotation (D.meridionalOneForm r hr)))
    (metricNabla0S_oneFormAreaContraction finrank_euclideanSpace_fin D.metric D.areaForm
      D.areaForm_alternating D.areaForm_normSq (D.meridionalOneForm r hr) x)
  rw [D.hodgeRotation_meridionalOneForm, metricNabla0S_smul, ahlforsPart_smul] at hrot
  change normSq0S D.metric x 2
    ((-1 : ℝ) • ahlforsPart D.metric (metricNabla0S D.metric (D.azimuthalOneForm r hr)) x) =
      _ at hrot
  rw [normSq0S_smul] at hrot
  norm_num only [neg_sq, one_pow, one_mul] at hrot
  exact hrot.trans (D.meridionalOneForm_ahlfors_normSq r hr x)

/-- The genuine azimuthal constant probes are globally conformal Killing. -/
theorem isConformalKillingOneForm_azimuthal_const (D : PoleData) (c : ℝ) :
    IsConformalKillingOneForm D.metric
      (D.azimuthalOneForm (fun _ => c) contDiff_const) := by
  rw [isConformalKillingOneForm_iff_normSq_eq_zero]
  intro x
  rw [D.azimuthalOneForm_ahlfors_normSq]
  simp

/-- Constant combinations of both actual geometric generators are conformal Killing. -/
theorem isConformalKillingOneForm_constant_zonal_sum (D : PoleData) (c d : ℝ) :
    IsConformalKillingOneForm D.metric
      (D.meridionalOneForm (fun _ => c) contDiff_const +
        D.azimuthalOneForm (fun _ => d) contDiff_const) :=
  (D.isConformalKillingOneForm_meridional_const c).add
    (D.isConformalKillingOneForm_azimuthal_const d)

private theorem probe_eq_const_on_Icc (D : PoleData) (r : ℝ → ℝ)
    (hr : ContDiff ℝ ∞ r)
    (hzero : ∀ x : RotationalSphere,
      (D.meridionalWeight (sphereHeight x) * deriv r (sphereHeight x)) ^ 2 / 2 = 0) :
    ∀ v ∈ Icc (-1 : ℝ) 1, r v = r 0 := by
  have hd : ∀ v ∈ Ioo (-1 : ℝ) 1, deriv r v = 0 := by
    intro v hv
    let q : cylinderDomain := ⟨WithLp.toLp 2 ![v, 0], hv⟩
    let x := cylinderMap q
    have hx : sphereHeight x = v := by
      exact sphereHeight_cylinderMap q
    have hz := hzero x
    rw [hx] at hz
    have hp : 0 < D.meridionalWeight v :=
      div_pos (warp_pos_of_balance D.a D.a_contDiff.continuous D.a_pos D.balance_eq v hv)
        (D.a_pos v ⟨hv.1.le, hv.2.le⟩)
    have hprod : D.meridionalWeight v * deriv r v = 0 := by nlinarith
    exact (mul_eq_zero.mp hprod).resolve_left hp.ne'
  have hopen : ∀ v ∈ Ioo (-1 : ℝ) 1, r v = r 0 := by
    intro v hv
    apply isOpen_Ioo.is_const_of_deriv_eq_zero (convex_Ioo (-1 : ℝ) 1).isPreconnected
      (hr.differentiable (by simp)).differentiableOn
    · exact hd
    · exact hv
    · constructor <;> norm_num
  have hclosed : IsClosed {v : ℝ | r v = r 0} :=
    isClosed_eq hr.continuous continuous_const
  intro v hv
  apply closure_minimal (fun u hu => hopen u hu) hclosed
  rw [closure_Ioo (by norm_num : (-1 : ℝ) ≠ 1)]
  exact hv

/-- A meridional conformal Killing probe is constant on the full physical height
interval, with no assertion about its arbitrary extension outside the sphere. -/
theorem meridional_probe_eq_const_of_isConformalKillingOneForm (D : PoleData)
    (r : ℝ → ℝ) (hr : ContDiff ℝ ∞ r)
    (hCK : IsConformalKillingOneForm D.metric (D.meridionalOneForm r hr)) :
    ∀ v ∈ Icc (-1 : ℝ) 1, r v = r 0 := by
  apply probe_eq_const_on_Icc D r hr
  intro x
  rw [← D.meridionalOneForm_ahlfors_normSq r hr x]
  exact (isConformalKillingOneForm_iff_normSq_eq_zero _ _).mp hCK x

/-- The azimuthal probe has the same physical-interval constancy property. -/
theorem azimuthal_probe_eq_const_of_isConformalKillingOneForm (D : PoleData)
    (r : ℝ → ℝ) (hr : ContDiff ℝ ∞ r)
    (hCK : IsConformalKillingOneForm D.metric (D.azimuthalOneForm r hr)) :
    ∀ v ∈ Icc (-1 : ℝ) 1, r v = r 0 := by
  apply probe_eq_const_on_Icc D r hr
  intro x
  rw [← D.azimuthalOneForm_ahlfors_normSq r hr x]
  exact (isConformalKillingOneForm_iff_normSq_eq_zero _ _).mp hCK x

private theorem meridional_ck_of_sum (D : PoleData) (r s : ℝ → ℝ)
    (hr : ContDiff ℝ ∞ r) (hs : ContDiff ℝ ∞ s)
    (hCK : IsConformalKillingOneForm D.metric
      (D.meridionalOneForm r hr + D.azimuthalOneForm s hs)) :
    IsConformalKillingOneForm D.metric (D.meridionalOneForm r hr) := by
  have href := hCK.diffeomorphTensorPullback_of_isometry meridianReflectionSphereDiffeo
    D.pullbackMetric_meridianReflectionSphereDiffeo
  rw [diffeomorphTensorPullback_add, D.diffeomorphTensorPullback_meridional_reflection,
    D.diffeomorphTensorPullback_azimuthal_reflection] at href
  have h := (hCK.add href).smul (1 / 2)
  have heq : (1 / 2 : ℝ) • ((D.meridionalOneForm r hr + D.azimuthalOneForm s hs) +
      (D.meridionalOneForm r hr + (-1 : ℝ) • D.azimuthalOneForm s hs)) =
      D.meridionalOneForm r hr := by module
  rwa [heq] at h

/-- Every invariant conformal Killing form is literally a constant combination
of the two accepted geometric generators of its original metric. -/
theorem exists_constant_zonal_decomposition_of_rotationInvariant_of_isConformalKillingOneForm
    (D : PoleData) (h : OneFormSection (I := 𝓡 2) (M := RotationalSphere))
    (hinv : ∀ z : Circle, diffeomorphTensorPullback (circleSphereDiffeo z) h = h)
    (hCK : IsConformalKillingOneForm D.metric h) :
    ∃ c d : ℝ, h = D.meridionalOneForm (fun _ => c) contDiff_const +
      D.azimuthalOneForm (fun _ => d) contDiff_const := by
  obtain ⟨r, s, hr, hs, heq⟩ := D.exists_smooth_zonal_decomposition_of_rotationInvariant h hinv
  have hsum := hCK
  rw [heq] at hsum
  have hmer := meridional_ck_of_sum D r s hr hs hsum
  have hazi : IsConformalKillingOneForm D.metric (D.azimuthalOneForm s hs) := by
    simpa only [add_sub_cancel_left] using hsum.sub hmer
  refine ⟨r 0, s 0, ?_⟩
  rw [heq]
  ext x slots
  have hslots : slots = fun _ : Fin 1 => slots 0 := by
    funext i
    exact congrArg slots (Fin.eq_zero i)
  rw [hslots]
  change D.meridionalOneForm r hr x (fun _ : Fin 1 => slots 0) +
      D.azimuthalOneForm s hs x (fun _ : Fin 1 => slots 0) = _
  simp only [ContMDiffSection.coe_add, Pi.add_apply, Tensor0SSpace.add_apply,
    meridionalOneForm_apply, azimuthalOneForm_apply,
    D.meridional_probe_eq_const_of_isConformalKillingOneForm r hr hmer
      _ (sphereHeight_mem_Icc x),
    D.azimuthal_probe_eq_const_of_isConformalKillingOneForm s hs hazi
      _ (sphereHeight_mem_Icc x)]

/-- The conformal Killing equation is exactly the constant-generator condition
among the actual rotation-invariant smooth forms. -/
theorem rotationInvariant_isConformalKillingOneForm_iff_exists_constant_zonal_decomposition
    (D : PoleData) (h : OneFormSection (I := 𝓡 2) (M := RotationalSphere))
    (hinv : ∀ z : Circle, diffeomorphTensorPullback (circleSphereDiffeo z) h = h) :
    IsConformalKillingOneForm D.metric h ↔
      ∃ c d : ℝ, h = D.meridionalOneForm (fun _ => c) contDiff_const +
        D.azimuthalOneForm (fun _ => d) contDiff_const := by
  constructor
  · exact D.exists_constant_zonal_decomposition_of_rotationInvariant_of_isConformalKillingOneForm
      h hinv
  · rintro ⟨c, d, rfl⟩
    exact D.isConformalKillingOneForm_constant_zonal_sum c d

/-- Haar averaging preserves the conformal Killing equation of the original smooth form. -/
theorem isConformalKillingOneForm_rotationalAverage (D : PoleData)
    (h : OneFormSection (I := 𝓡 2) (M := RotationalSphere))
    (hCK : IsConformalKillingOneForm D.metric h) :
    IsConformalKillingOneForm D.metric (rotationalAverage h) := by
  unfold IsConformalKillingOneForm at *
  rw [D.ahlforsPart_metricNabla0S_rotationalAverage, hCK, rotationalAverage_zero]

/-- The actual Haar average of every original smooth conformal Killing form is
literally a constant combination of the meridional and azimuthal generators. -/
theorem exists_constant_zonal_decomposition_rotationalAverage_of_isConformalKillingOneForm
    (D : PoleData) (h : OneFormSection (I := 𝓡 2) (M := RotationalSphere))
    (hCK : IsConformalKillingOneForm D.metric h) :
    ∃ c d : ℝ, rotationalAverage h =
      D.meridionalOneForm (fun _ => c) contDiff_const +
        D.azimuthalOneForm (fun _ => d) contDiff_const :=
  D.exists_constant_zonal_decomposition_of_rotationInvariant_of_isConformalKillingOneForm
    (rotationalAverage h) (fun z => diffeomorphTensorPullback_circle_rotationalAverage z h)
    (D.isConformalKillingOneForm_rotationalAverage h hCK)

/-- The unit meridional generator is a genuine nonzero global conformal Killing form. -/
theorem meridional_one_nonzero_conformalKilling (D : PoleData) :
    D.meridionalOneForm (fun _ => 1) contDiff_const ≠ 0 ∧
      IsConformalKillingOneForm D.metric
        (D.meridionalOneForm (fun _ => 1) contDiff_const) :=
  ⟨D.meridionalOneForm_one_ne_zero, D.isConformalKillingOneForm_meridional_const 1⟩

end RotationalProfile.PoleData
end RicciFlowSharpEstimate.Geometry
