/-
Copyright (c) 2026 Ziyang Qin. All rights reserved.
No license is granted by this file.
Authors: Ziyang Qin
-/
import RicciFlowSharpEstimate.Analysis.SecondPrimitive
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun

/-!
# Flux reconstruction from a second-order weak Euler identity

An Euler identity against every globally smooth test reconstructs the leading
L¹ coefficient as an actual absolutely continuous integral primitive. The
primitive flux and its primitive both have zero traces at the endpoints.
The derivative conclusions use genuine almost-everywhere `HasDerivAt` facts.
-/

noncomputable section

namespace RicciFlowSharpEstimate.Analysis

open Filter Function MeasureTheory Set
open scoped ContDiff Topology

private theorem primitive_ae_hasDerivAt
    (a b : ℝ) (hab : a ≤ b) (f : ℝ → ℝ)
    (hf : IntervalIntegrable f volume a b) :
    ∀ᵐ x ∂volume.restrict (Ioo a b),
      HasDerivAt (fun y ↦ ∫ t in a..y, f t) (f x) x := by
  apply (ae_restrict_iff' measurableSet_Ioo).2
  filter_upwards [hf.ae_hasDerivAt_integral] with x hx
  intro hxIoo
  have hxIcc : x ∈ uIcc a b := by
    rw [uIcc_of_le hab]
    exact ⟨hxIoo.1.le, hxIoo.2.le⟩
  exact hx hxIcc a (by simp)

private theorem primitive_integration_by_parts
    (a b : ℝ) (f : ℝ → ℝ) (hf : IntervalIntegrable f volume a b)
    (hfzero : (∫ t in a..b, f t) = 0)
    (φ : ℝ → ℝ) (hφ : ContDiff ℝ ∞ φ) :
    (∫ x in a..b, f x * φ x) =
      -(∫ x in a..b, (∫ t in a..x, f t) * deriv φ x) := by
  let Q : ℝ → ℝ := fun x ↦ ∫ t in a..x, f t
  have hQ : AbsolutelyContinuousOnInterval Q a b :=
    hf.absolutelyContinuousOnInterval_intervalIntegral (by simp)
  have hφAC : AbsolutelyContinuousOnInterval φ a b :=
    ((hφ.of_le (by simp) : ContDiff ℝ 1 φ).contDiffOn).absolutelyContinuousOnInterval
  have hQa : Q a = 0 := by simp [Q]
  have hQb : Q b = 0 := hfzero
  have hDerivativeIntegral :
      (∫ x in a..b, deriv Q x * φ x) = ∫ x in a..b, f x * φ x := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards [hf.ae_hasDerivAt_integral] with x hx hxI
    have hDeriv : deriv Q x = f x :=
      (hx (uIoc_subset_uIcc hxI) a (by simp)).deriv
    rw [hDeriv]
  have hParts := hQ.integral_mul_deriv_eq_deriv_mul hφAC
  rw [hQa, hQb, hDerivativeIntegral] at hParts
  dsimp only [Q] at hParts
  linarith

private theorem first_order_weak_euler_primitive
    (a b : ℝ) (hab : a ≤ b) (u v : ℝ → ℝ)
    (hu : IntervalIntegrable u volume a b)
    (hv : IntervalIntegrable v volume a b)
    (hEuler : ∀ φ : ℝ → ℝ, ContDiff ℝ ∞ φ →
      (∫ x in a..b, u x * deriv φ x + v x * φ x) = 0) :
    u =ᵐ[volume.restrict (Ioo a b)] (fun x ↦ ∫ t in a..x, v t) ∧
      (∫ t in a..b, v t) = 0 := by
  have hvzero : (∫ t in a..b, v t) = 0 := by
    simpa using hEuler (fun _ ↦ 1) contDiff_const
  let Q : ℝ → ℝ := fun x ↦ ∫ t in a..x, v t
  have hQAC : AbsolutelyContinuousOnInterval Q a b :=
    hv.absolutelyContinuousOnInterval_intervalIntegral (by simp)
  have hQI : IntervalIntegrable Q volume a b := hQAC.continuousOn.intervalIntegrable
  have hTest : ∀ η : ℝ → ℝ, ContDiff ℝ ∞ η →
      (∫ x in a..b, (u x - Q x) * η x) = 0 := by
    intro η hη
    let φ : ℝ → ℝ := fun x ↦ ∫ t in a..x, η t
    have hφ : ContDiff ℝ ∞ φ := SecondPrimitive.integral_contDiff η hη a
    have hφDeriv : deriv φ = η := by
      funext x
      exact (hη.continuous.integral_hasStrictDerivAt a x).hasDerivAt.deriv
    have huη : IntervalIntegrable (fun x ↦ u x * η x) volume a b :=
      hu.mul_continuousOn hη.continuous.continuousOn
    have hvφ : IntervalIntegrable (fun x ↦ v x * φ x) volume a b :=
      hv.mul_continuousOn hφ.continuous.continuousOn
    have hQη : IntervalIntegrable (fun x ↦ Q x * η x) volume a b :=
      hQI.mul_continuousOn hη.continuous.continuousOn
    have hIdentity := hEuler φ hφ
    simp only [hφDeriv] at hIdentity
    rw [intervalIntegral.integral_add huη hvφ] at hIdentity
    have hParts := primitive_integration_by_parts a b v hv hvzero φ hφ
    rw [hφDeriv] at hParts
    change (∫ x in a..b, v x * φ x) = -(∫ x in a..b, Q x * η x) at hParts
    simp_rw [sub_mul]
    rw [intervalIntegral.integral_sub huη hQη]
    linarith
  have huIoo : IntegrableOn u (Ioo a b) volume :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le hab).1 hu
  have hQIoo : IntegrableOn Q (Ioo a b) volume :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le hab).1 hQI
  have hz : ∀ᵐ x ∂volume, x ∈ Ioo a b → (u - Q) x = 0 := by
    apply isOpen_Ioo.ae_eq_zero_of_integral_contDiff_smul_eq_zero
      (huIoo.sub hQIoo).locallyIntegrableOn
    intro η hη _hηc hηIoo
    have hSupport : support (fun x ↦ η x * (u - Q) x) ⊆ Ioc a b := by
      intro x hx
      have hηx : η x ≠ 0 := (mul_ne_zero_iff.mp hx).1
      have hxIoo : x ∈ Ioo a b := hηIoo (subset_tsupport η hηx)
      exact ⟨hxIoo.1, hxIoo.2.le⟩
    have hBridge := intervalIntegral.integral_eq_integral_of_support_subset
      (μ := volume) hSupport
    have hZero : (∫ x in a..b, η x * (u - Q) x) = 0 := by
      simpa only [Pi.sub_apply, mul_comm] using hTest η hη
    simpa only [smul_eq_mul] using hBridge.symm.trans hZero
  refine ⟨?_, hvzero⟩
  apply (ae_restrict_iff' measurableSet_Ioo).2
  filter_upwards [hz] with x hx
  intro hxIoo
  exact sub_eq_zero.mp (hx hxIoo)

/-- An unrestricted smooth-test Euler identity for three L¹ coefficients
reconstructs the leading coefficient as the actual primitive of the lower-order
flux, with absolute continuity, zero endpoint traces, and genuine derivatives
almost everywhere on the original open interval. -/
theorem second_order_weak_euler_flux
    (a b : ℝ) (hab : a ≤ b) (U V H : ℝ → ℝ)
    (hU : IntegrableOn U (Ioo a b) volume)
    (hV : IntegrableOn V (Ioo a b) volume)
    (hH : IntegrableOn H (Ioo a b) volume)
    (hEuler : ∀ φ : ℝ → ℝ, ContDiff ℝ ∞ φ →
      (∫ x in a..b, U x * deriv (deriv φ) x + V x * deriv φ x + H x * φ x) = 0) :
    let P := fun x ↦ -(∫ t in a..x, H t)
    let A := fun x ↦ ∫ t in a..x, V t + P t
    U =ᵐ[volume.restrict (Ioo a b)] A ∧
      AbsolutelyContinuousOnInterval P a b ∧
      AbsolutelyContinuousOnInterval A a b ∧
      P a = 0 ∧ P b = 0 ∧ A a = 0 ∧ A b = 0 ∧
      (∀ᵐ x ∂volume.restrict (Ioo a b), HasDerivAt P (-H x) x) ∧
      (∀ᵐ x ∂volume.restrict (Ioo a b), HasDerivAt A (V x + P x) x) := by
  let P : ℝ → ℝ := fun x ↦ -(∫ t in a..x, H t)
  let A : ℝ → ℝ := fun x ↦ ∫ t in a..x, V t + P t
  change U =ᵐ[volume.restrict (Ioo a b)] A ∧
    AbsolutelyContinuousOnInterval P a b ∧
    AbsolutelyContinuousOnInterval A a b ∧
    P a = 0 ∧ P b = 0 ∧ A a = 0 ∧ A b = 0 ∧
    (∀ᵐ x ∂volume.restrict (Ioo a b), HasDerivAt P (-H x) x) ∧
    (∀ᵐ x ∂volume.restrict (Ioo a b), HasDerivAt A (V x + P x) x)
  have hUI : IntervalIntegrable U volume a b :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le hab).2 hU
  have hVI : IntervalIntegrable V volume a b :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le hab).2 hV
  have hHI : IntervalIntegrable H volume a b :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le hab).2 hH
  have hHzero : (∫ t in a..b, H t) = 0 := by
    simpa using hEuler (fun _ ↦ 1) contDiff_const
  have hPAC : AbsolutelyContinuousOnInterval P a b :=
    (hHI.absolutelyContinuousOnInterval_intervalIntegral (c := a) (by simp)).neg
  have hPI : IntervalIntegrable P volume a b := hPAC.continuousOn.intervalIntegrable
  have hVPI : IntervalIntegrable (fun x ↦ V x + P x) volume a b := hVI.add hPI
  have hPParts (φ : ℝ → ℝ) (hφ : ContDiff ℝ ∞ φ) :
      (∫ x in a..b, H x * φ x) = ∫ x in a..b, P x * deriv φ x := by
    simpa only [P, neg_mul, intervalIntegral.integral_neg] using
      primitive_integration_by_parts a b H hHI hHzero φ hφ
  have hFirst : ∀ η : ℝ → ℝ, ContDiff ℝ ∞ η →
      (∫ x in a..b, U x * deriv η x + (V x + P x) * η x) = 0 := by
    intro η hη
    let φ : ℝ → ℝ := fun x ↦ ∫ t in a..x, η t
    have hφ : ContDiff ℝ ∞ φ := SecondPrimitive.integral_contDiff η hη a
    have hφDeriv : deriv φ = η := by
      funext x
      exact (hη.continuous.integral_hasStrictDerivAt a x).hasDerivAt.deriv
    have hUη : IntervalIntegrable (fun x ↦ U x * deriv η x) volume a b :=
      hUI.mul_continuousOn (hη.continuous_deriv (by simp)).continuousOn
    have hVη : IntervalIntegrable (fun x ↦ V x * η x) volume a b :=
      hVI.mul_continuousOn hη.continuous.continuousOn
    have hHφ : IntervalIntegrable (fun x ↦ H x * φ x) volume a b :=
      hHI.mul_continuousOn hφ.continuous.continuousOn
    have hPη : IntervalIntegrable (fun x ↦ P x * η x) volume a b :=
      hPI.mul_continuousOn hη.continuous.continuousOn
    have hVPη : IntervalIntegrable (fun x ↦ (V x + P x) * η x) volume a b :=
      hVPI.mul_continuousOn hη.continuous.continuousOn
    have hIdentity := hEuler φ hφ
    simp only [hφDeriv] at hIdentity
    rw [intervalIntegral.integral_add (hUη.add hVη) hHφ,
      intervalIntegral.integral_add hUη hVη] at hIdentity
    have hParts := hPParts φ hφ
    rw [hφDeriv] at hParts
    have hSplit : (∫ x in a..b, (V x + P x) * η x) =
        (∫ x in a..b, V x * η x) + ∫ x in a..b, P x * η x := by
      simp_rw [add_mul]
      exact intervalIntegral.integral_add hVη hPη
    rw [intervalIntegral.integral_add hUη hVPη, hSplit]
    linarith
  obtain ⟨hUA, hAzero⟩ :=
    first_order_weak_euler_primitive a b hab U (fun x ↦ V x + P x) hUI hVPI hFirst
  have hAAC : AbsolutelyContinuousOnInterval A a b :=
    hVPI.absolutelyContinuousOnInterval_intervalIntegral (by simp)
  have hPa : P a = 0 := by simp [P]
  have hPb : P b = 0 := by simp [P, hHzero]
  have hAa : A a = 0 := by simp [A]
  have hAb : A b = 0 := hAzero
  have hPDeriv : ∀ᵐ x ∂volume.restrict (Ioo a b), HasDerivAt P (-H x) x := by
    filter_upwards [primitive_ae_hasDerivAt a b hab H hHI] with x hx
    exact hx.neg
  have hADeriv : ∀ᵐ x ∂volume.restrict (Ioo a b), HasDerivAt A (V x + P x) x :=
    primitive_ae_hasDerivAt a b hab (fun x ↦ V x + P x) hVPI
  exact ⟨hUA, hPAC, hAAC, hPa, hPb, hAa, hAb, hPDeriv, hADeriv⟩

end RicciFlowSharpEstimate.Analysis
