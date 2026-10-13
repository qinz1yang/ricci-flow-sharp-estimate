/-
Copyright (c) 2026 Ziyang Qin. All rights reserved.
No license is granted by this file.
Authors: Ziyang Qin
-/
import RicciFlowSharpEstimate.Analysis.WeakDerivative
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Topology.UniformSpace.LocallyUniformConvergence

/-!
# Limits of real weak derivative identities

Locally uniform convergence on an open domain implies convergence of the
full Lebesgue integrals against continuous compactly supported tests in that
domain. The products in these integrals are genuinely integrable.

Weak derivative identities pass to limits whenever the two corresponding
test pairings converge and both limit representatives are locally integrable.
In particular, they pass to locally uniform limits of continuous functions
and continuous weak derivatives.
-/

noncomputable section

namespace RicciFlowSharpEstimate.Analysis

open Filter Function MeasureTheory Set
open scoped ContDiff Topology

/-- Locally uniform convergence on an open real domain implies convergence
of full-space integrals against a continuous test compactly supported in the
domain. Each test product is integrable by local integrability and support. -/
theorem test_mul_integral_tendsto_of_locallyUniformlyOn
    {U : Set ℝ} {F : ℕ → ℝ → ℝ} {f φ : ℝ → ℝ}
    (hU : IsOpen U) (hF : ∀ n, ContinuousOn (F n) U) (hf : ContinuousOn f U)
    (hlim : TendstoLocallyUniformlyOn F f atTop U)
    (hφ : Continuous φ) (hφc : HasCompactSupport φ) (hφU : tsupport φ ⊆ U) :
    Tendsto (fun n ↦ ∫ x, φ x * F n x) atTop (𝓝 (∫ x, φ x * f x)) := by
  have hFI : ∀ n, Integrable (fun x ↦ φ x * F n x) volume := fun n ↦
    integrable_mul_of_locallyIntegrableOn
      ((hF n).locallyIntegrableOn hU.measurableSet) hφ hφc hφU
  have hfI : Integrable (fun x ↦ φ x * f x) volume :=
    integrable_mul_of_locallyIntegrableOn
      (hf.locallyIntegrableOn hU.measurableSet) hφ hφc hφU
  have hφI : Integrable φ volume := hφ.integrable_of_hasCompactSupport hφc
  have hcompact : TendstoUniformlyOn F f atTop (tsupport φ) :=
    (tendstoLocallyUniformlyOn_iff_tendstoUniformlyOn_of_compact hφc).1
      (hlim.mono hφU)
  have hnear : ∀ᶠ n : ℕ in atTop, ∀ x ∈ tsupport φ, ‖F n x - f x‖ ≤ 1 := by
    filter_upwards [(Metric.tendstoUniformlyOn_iff.mp hcompact) 1 (by norm_num)]
      with n hn
    intro x hx
    have hd : dist (f x) (F n x) ≤ 1 := (hn x hx).le
    rw [dist_comm] at hd
    simpa only [dist_eq_norm] using hd
  apply tendsto_integral_filter_of_dominated_convergence
    (fun x ↦ ‖φ x * f x‖ + ‖φ x‖)
  · exact Eventually.of_forall fun n ↦ (hFI n).aestronglyMeasurable
  · filter_upwards [hnear] with n hn
    exact Eventually.of_forall fun x ↦ by
      by_cases hx : x ∈ tsupport φ
      · have hnorm : ‖F n x‖ ≤ 1 + ‖f x‖ := by
          calc
            ‖F n x‖ = ‖(F n x - f x) + f x‖ := by rw [sub_add_cancel]
            _ ≤ ‖F n x - f x‖ + ‖f x‖ := norm_add_le _ _
            _ ≤ 1 + ‖f x‖ := add_le_add (hn x hx) le_rfl
        calc
          ‖φ x * F n x‖ = ‖φ x‖ * ‖F n x‖ := norm_mul _ _
          _ ≤ ‖φ x‖ * (1 + ‖f x‖) :=
            mul_le_mul_of_nonneg_left hnorm (norm_nonneg _)
          _ = ‖φ x * f x‖ + ‖φ x‖ := by rw [norm_mul]; ring
      · simp [image_eq_zero_of_notMem_tsupport hx]
  · exact hfI.norm.add hφI.norm
  · exact Eventually.of_forall fun x ↦ by
      by_cases hx : x ∈ tsupport φ
      · exact tendsto_const_nhds.mul (hlim.tendsto_at (hφU hx))
      · simpa only [image_eq_zero_of_notMem_tsupport hx, zero_mul] using
          (tendsto_const_nhds :
            Tendsto (fun _ : ℕ ↦ (0 : ℝ)) atTop (𝓝 (0 : ℝ)))

/-- Weak derivative identities pass to a limit under convergence of both
compact smooth test pairings. The limit representatives are required to be
locally integrable; no derivative of either representative is substituted
for the weak derivative predicate. -/
theorem HasWeakDerivOn.of_tendsto_test_pairings
    {U : Set ℝ} {R P : ℕ → ℝ → ℝ} {r p : ℝ → ℝ}
    (hseq : ∀ n, HasWeakDerivOn U (R n) (P n))
    (hr : LocallyIntegrableOn r U volume) (hp : LocallyIntegrableOn p U volume)
    (hR : ∀ φ : ℝ → ℝ,
      ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ U →
        Tendsto (fun n ↦ ∫ x, deriv φ x * R n x) atTop
          (𝓝 (∫ x, deriv φ x * r x)))
    (hP : ∀ φ : ℝ → ℝ,
      ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ U →
        Tendsto (fun n ↦ ∫ x, φ x * P n x) atTop (𝓝 (∫ x, φ x * p x))) :
    HasWeakDerivOn U r p := by
  refine ⟨hr, hp, ?_⟩
  intro φ hφ hφc hφU
  have heq : (fun n ↦ ∫ x, deriv φ x * R n x) =
      (fun n ↦ -(∫ x, φ x * P n x)) := by
    funext n
    exact (hseq n).integral_deriv_mul φ hφ hφc hφU
  have hneg : Tendsto (fun n ↦ -(∫ x, φ x * P n x)) atTop
      (𝓝 (-(∫ x, φ x * p x))) :=
    (hP φ hφ hφc hφU).neg
  rw [← heq] at hneg
  exact tendsto_nhds_unique (hR φ hφ hφc hφU) hneg

/-- Weak derivative identities pass to locally uniform limits when both the
functions and their weak derivatives are continuous on the open domain. -/
theorem hasWeakDerivOn_of_locallyUniformlyOn
    {U : Set ℝ} {R P : ℕ → ℝ → ℝ} {r p : ℝ → ℝ}
    (hU : IsOpen U) (hseq : ∀ n, HasWeakDerivOn U (R n) (P n))
    (hR : ∀ n, ContinuousOn (R n) U) (hP : ∀ n, ContinuousOn (P n) U)
    (hr : ContinuousOn r U) (hp : ContinuousOn p U)
    (hRlim : TendstoLocallyUniformlyOn R r atTop U)
    (hPlim : TendstoLocallyUniformlyOn P p atTop U) :
    HasWeakDerivOn U r p := by
  apply HasWeakDerivOn.of_tendsto_test_pairings hseq
    (hr.locallyIntegrableOn hU.measurableSet)
    (hp.locallyIntegrableOn hU.measurableSet)
  · intro φ hφ hφc hφU
    exact test_mul_integral_tendsto_of_locallyUniformlyOn hU hR hr hRlim
      (hφ.continuous_deriv (by simp)) hφc.deriv (tsupport_deriv_subset.trans hφU)
  · intro φ hφ hφc hφU
    exact test_mul_integral_tendsto_of_locallyUniformlyOn hU hP hp hPlim
      hφ.continuous hφc hφU

end RicciFlowSharpEstimate.Analysis
