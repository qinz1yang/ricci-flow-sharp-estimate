/-
Copyright (c) 2026 Ziyang Qin. All rights reserved.
No license is granted by this file.
Authors: Ziyang Qin
-/
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
# Real weak derivatives on open domains

`HasWeakDerivOn U r p` states the distributional derivative identity against
every smooth function compactly supported in `U`. Both representatives are
locally integrable on `U`; the supporting integrability laws ensure that the
full Lebesgue integrals in this identity are integrals of integrable functions.

Weak derivatives are unique almost everywhere on open domains. A function
that is `C¹` on an open domain has its actual derivative as a weak derivative,
without any boundary condition on that function.
-/

noncomputable section

namespace RicciFlowSharpEstimate.Analysis

open Filter Function MeasureTheory Set
open scoped ContDiff Topology

/-- A continuous factor compactly supported inside a domain turns a locally
integrable function on that domain into an integrable function on the line. -/
theorem integrable_mul_of_locallyIntegrableOn
    {U : Set ℝ} {f φ : ℝ → ℝ} (hf : LocallyIntegrableOn f U volume)
    (hφ : Continuous φ) (hφc : HasCompactSupport φ) (hφU : tsupport φ ⊆ U) :
    Integrable (fun x ↦ φ x * f x) volume := by
  have hi : IntegrableOn (fun x ↦ φ x * f x) (tsupport φ) volume :=
    (hf.integrableOn_compact_subset hφU hφc).continuousOn_mul hφ.continuousOn hφc
  exact hi.integrable_of_forall_notMem_eq_zero fun x hx ↦ by
    simp [image_eq_zero_of_notMem_tsupport hx]

/-- A real weak derivative on a domain, defined by compactly supported smooth
tests and local integrability of both the function and its weak derivative. -/
def HasWeakDerivOn (U : Set ℝ) (r p : ℝ → ℝ) : Prop :=
  LocallyIntegrableOn r U volume ∧ LocallyIntegrableOn p U volume ∧
    ∀ φ : ℝ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ U →
      (∫ x, deriv φ x * r x) = -(∫ x, φ x * p x)

/-- A function with a weak derivative is locally integrable on its domain. -/
theorem HasWeakDerivOn.locallyIntegrable {U : Set ℝ} {r p : ℝ → ℝ}
    (h : HasWeakDerivOn U r p) : LocallyIntegrableOn r U volume := h.1

/-- The weak derivative is locally integrable on the same domain. -/
theorem HasWeakDerivOn.locallyIntegrable_deriv {U : Set ℝ} {r p : ℝ → ℝ}
    (h : HasWeakDerivOn U r p) : LocallyIntegrableOn p U volume := h.2.1

/-- The actual compact-test integration identity of a weak derivative. -/
theorem HasWeakDerivOn.integral_deriv_mul {U : Set ℝ} {r p : ℝ → ℝ}
    (h : HasWeakDerivOn U r p) (φ : ℝ → ℝ) (hφ : ContDiff ℝ ∞ φ)
    (hφc : HasCompactSupport φ) (hφU : tsupport φ ⊆ U) :
    (∫ x, deriv φ x * r x) = -(∫ x, φ x * p x) := h.2.2 φ hφ hφc hφU

/-- The left integrand in the weak derivative identity is integrable. -/
theorem HasWeakDerivOn.integrable_deriv_test_mul
    {U : Set ℝ} {r p φ : ℝ → ℝ} (h : HasWeakDerivOn U r p)
    (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ) (hφU : tsupport φ ⊆ U) :
    Integrable (fun x ↦ deriv φ x * r x) volume :=
  integrable_mul_of_locallyIntegrableOn h.locallyIntegrable
    (hφ.continuous_deriv (by simp)) hφc.deriv (tsupport_deriv_subset.trans hφU)

/-- The right integrand in the weak derivative identity is integrable. -/
theorem HasWeakDerivOn.integrable_test_mul_weakDeriv
    {U : Set ℝ} {r p φ : ℝ → ℝ} (h : HasWeakDerivOn U r p)
    (hφ : Continuous φ) (hφc : HasCompactSupport φ) (hφU : tsupport φ ⊆ U) :
    Integrable (fun x ↦ φ x * p x) volume :=
  integrable_mul_of_locallyIntegrableOn h.locallyIntegrable_deriv hφ hφc hφU

/-- Weak derivatives of the same function agree almost everywhere on an open
domain. -/
theorem HasWeakDerivOn.ae_unique
    {U : Set ℝ} {r p q : ℝ → ℝ} (hp : HasWeakDerivOn U r p)
    (hq : HasWeakDerivOn U r q) (hU : IsOpen U) :
    p =ᵐ[volume.restrict U] q := by
  have hz : ∀ᵐ x ∂volume, x ∈ U → (p - q) x = 0 := by
    apply hU.ae_eq_zero_of_integral_contDiff_smul_eq_zero
      (hp.locallyIntegrable_deriv.sub hq.locallyIntegrable_deriv)
    intro φ hφ hφc hφU
    simp only [Pi.sub_apply, smul_eq_mul, mul_sub]
    rw [integral_sub
      (hp.integrable_test_mul_weakDeriv hφ.continuous hφc hφU)
      (hq.integrable_test_mul_weakDeriv hφ.continuous hφc hφU)]
    apply sub_eq_zero.mpr
    exact neg_injective ((hp.integral_deriv_mul φ hφ hφc hφU).symm.trans
      (hq.integral_deriv_mul φ hφ hφc hφU))
  apply (ae_restrict_iff' hU.measurableSet).2
  filter_upwards [hz] with x hx
  intro hxU
  exact sub_eq_zero.mp (hx hxU)

/-- A function that is `C¹` on an open domain has its actual derivative as its
weak derivative there. Compact support of the test, rather than a boundary
condition on the function, supplies integration by parts. -/
theorem hasWeakDerivOn_of_contDiffOn
    {U : Set ℝ} {r : ℝ → ℝ} (hU : IsOpen U) (hr : ContDiffOn ℝ 1 r U) :
    HasWeakDerivOn U r (deriv r) := by
  have hrL : LocallyIntegrableOn r U volume :=
    hr.continuousOn.locallyIntegrableOn hU.measurableSet
  have hdL : LocallyIntegrableOn (deriv r) U volume :=
    (hr.continuousOn_deriv_of_isOpen hU le_rfl).locallyIntegrableOn hU.measurableSet
  refine ⟨hrL, hdL, ?_⟩
  intro φ hφ hφc hφU
  have hi₀ : Integrable (fun x ↦ φ x * r x) volume :=
    integrable_mul_of_locallyIntegrableOn hrL hφ.continuous hφc hφU
  have hi₁ : Integrable (fun x ↦ deriv φ x * r x) volume :=
    integrable_mul_of_locallyIntegrableOn hrL (hφ.continuous_deriv (by simp))
      hφc.deriv (tsupport_deriv_subset.trans hφU)
  have hi₂ : Integrable (fun x ↦ φ x * deriv r x) volume :=
    integrable_mul_of_locallyIntegrableOn hdL hφ.continuous hφc hφU
  have hdr : ∀ x ∈ tsupport φ, HasDerivAt r (deriv r x) x := by
    intro x hx
    exact (hr.differentiableOn_one.differentiableAt
      (hU.mem_nhds (hφU hx))).hasDerivAt
  have hdφ : ∀ x ∈ tsupport r, HasDerivAt φ (deriv φ x) x := by
    intro x _
    exact (hφ.differentiable (by simp) x).hasDerivAt
  simpa only [mul_comm] using
    (integral_mul_deriv_eq_deriv_mul_of_integrable
      (u := r) (v := φ) (u' := deriv r) (v' := deriv φ) hdr hdφ
      (by change Integrable (fun x => r x * deriv φ x) volume
          simpa only [mul_comm] using hi₁)
      (by change Integrable (fun x => deriv r x * φ x) volume
          simpa only [mul_comm] using hi₂)
      (by change Integrable (fun x => r x * φ x) volume
          simpa only [mul_comm] using hi₀))

/-- A globally `C¹` function has its actual derivative as a weak derivative
on every open domain. -/
theorem hasWeakDerivOn_of_contDiff
    {U : Set ℝ} {r : ℝ → ℝ} (hU : IsOpen U) (hr : ContDiff ℝ 1 r) :
    HasWeakDerivOn U r (deriv r) :=
  hasWeakDerivOn_of_contDiffOn hU hr.contDiffOn

private theorem weakDeriv_test_mul_congr_ae
    {U : Set ℝ} {f g φ : ℝ → ℝ} (hfg : f =ᵐ[volume.restrict U] g)
    (hφU : tsupport φ ⊆ U) :
    (fun x ↦ φ x * f x) =ᵐ[volume] (fun x ↦ φ x * g x) := by
  filter_upwards [ae_imp_of_ae_restrict hfg] with x hx
  by_cases hxφ : x ∈ tsupport φ
  · rw [hx (hφU hxφ)]
  · simp [image_eq_zero_of_notMem_tsupport hxφ]

/-- Changing either representative on a null subset of the domain preserves
the weak derivative identity. -/
theorem HasWeakDerivOn.congr_ae
    {U : Set ℝ} {r s p q : ℝ → ℝ} (h : HasWeakDerivOn U r p)
    (hrs : r =ᵐ[volume.restrict U] s) (hpq : p =ᵐ[volume.restrict U] q) :
    HasWeakDerivOn U s q := by
  refine ⟨(locallyIntegrableOn_congr hrs).1 h.locallyIntegrable,
    (locallyIntegrableOn_congr hpq).1 h.locallyIntegrable_deriv, ?_⟩
  intro φ hφ hφc hφU
  calc
    (∫ x, deriv φ x * s x) = ∫ x, deriv φ x * r x :=
      integral_congr_ae (weakDeriv_test_mul_congr_ae hrs
        (tsupport_deriv_subset.trans hφU)).symm
    _ = -(∫ x, φ x * p x) := h.integral_deriv_mul φ hφ hφc hφU
    _ = -(∫ x, φ x * q x) :=
      congrArg (fun z : ℝ ↦ -z)
        (integral_congr_ae (weakDeriv_test_mul_congr_ae hpq hφU))

end RicciFlowSharpEstimate.Analysis
