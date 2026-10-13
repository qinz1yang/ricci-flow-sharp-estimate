/-
Copyright (c) 2026 Ziyang Qin. All rights reserved.
No license is granted by this file.
Authors: Ziyang Qin
-/
import RicciFlowSharpEstimate.Analysis.WeakDerivativeLimits
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSeminorm.Monotonicity

/-!
# Identifying weak derivatives from weighted weak `L²` limits

Let a continuous weight be nonzero on `(0, 1)`. If globally `C¹` functions
converge locally uniformly and their weighted derivatives converge in all
`L²` pairings to `Z`, then the limit has the genuine weak derivative `Z / a`.

Division by the weight preserves local integrability and local `L²`
regularity. Compact test functions divided by the weight are legitimate
`L²` tests even when the weight vanishes at an endpoint.
-/

noncomputable section

namespace RicciFlowSharpEstimate.Analysis

open Filter Function MeasureTheory Set
open scoped ContDiff Topology

/-- Dividing an `L²` function by a continuous weight nonzero on `(0, 1)`
gives a locally integrable function on that open interval. -/
theorem locallyIntegrableOn_Ioo_div_weight
    {a Z : ℝ → ℝ} (ha : Continuous a) (ha0 : ∀ x ∈ Ioo 0 1, a x ≠ 0)
    (hZ : MemLp Z 2 (volume.restrict (Ioo (0 : ℝ) 1))) :
    LocallyIntegrableOn (fun x ↦ Z x / a x) (Ioo 0 1) volume := by
  have hZI : IntegrableOn Z (Ioo (0 : ℝ) 1) volume :=
    MemLp.integrable (by norm_num) hZ
  have hinv : ContinuousOn (fun x ↦ (a x)⁻¹) (Ioo 0 1) :=
    ha.continuousOn.inv₀ ha0
  simpa only [div_eq_mul_inv] using
    hZI.locallyIntegrableOn.mul_continuousOn hinv isOpen_Ioo.isLocallyClosed

/-- Dividing by a continuous nonzero weight preserves `L²` regularity on
each compact subset of the open interval. -/
theorem memLp_two_Ioo_div_weight_on_compact
    {a Z : ℝ → ℝ} (ha : Continuous a) (ha0 : ∀ x ∈ Ioo 0 1, a x ≠ 0)
    (hZ : MemLp Z 2 (volume.restrict (Ioo (0 : ℝ) 1)))
    {K : Set ℝ} (hK : IsCompact K) (hKI : K ⊆ Ioo 0 1) :
    MemLp (fun x ↦ Z x / a x) 2 (volume.restrict K) := by
  have hinv : ContinuousOn (fun x ↦ (a x)⁻¹) K :=
    ha.continuousOn.inv₀ fun x hx ↦ ha0 x (hKI hx)
  obtain ⟨C, hC⟩ : ∃ C : ℝ, ∀ x ∈ K, ‖(a x)⁻¹‖ ≤ C :=
    hK.exists_bound_of_continuousOn hinv
  have hZK : MemLp Z 2 (volume.restrict K) :=
    hZ.mono_measure (Measure.restrict_mono_set volume hKI)
  have hloc := locallyIntegrableOn_Ioo_div_weight ha ha0 hZ
  apply hZK.of_le_mul (c := C) (hloc.mono_set hKI).aestronglyMeasurable
  filter_upwards [ae_restrict_mem hK.measurableSet] with x hx
  calc
    ‖Z x / a x‖ = ‖(a x)⁻¹‖ * ‖Z x‖ := by
      rw [div_eq_mul_inv, norm_mul, mul_comm]
    _ ≤ C * ‖Z x‖ := mul_le_mul_of_nonneg_right (hC x hx) (norm_nonneg _)

/-- A continuous compact test supported inside the nonzero-weight domain
can be divided by the weight and still defines an `L²` test. -/
theorem memLp_two_Ioo_div_test
    {a φ : ℝ → ℝ} (ha : Continuous a) (ha0 : ∀ x ∈ Ioo 0 1, a x ≠ 0)
    (hφ : Continuous φ) (hφc : HasCompactSupport φ)
    (hφI : tsupport φ ⊆ Ioo 0 1) :
    MemLp (fun x ↦ φ x / a x) 2 (volume.restrict (Ioo (0 : ℝ) 1)) := by
  have hcont : ContinuousOn (fun x ↦ φ x / a x) (tsupport φ) :=
    hφ.continuousOn.div₀ ha.continuousOn fun x hx ↦ ha0 x (hφI hx)
  have hsqK : IntegrableOn (fun x ↦ (φ x / a x) ^ 2) (tsupport φ) volume :=
    (hcont.pow 2).integrableOn_compact hφc
  have hsq : Integrable (fun x ↦ (φ x / a x) ^ 2) volume :=
    hsqK.integrable_of_forall_notMem_eq_zero fun x hx ↦ by
      simp [image_eq_zero_of_notMem_tsupport hx]
  have hmeas : AEStronglyMeasurable (fun x ↦ φ x / a x)
      (volume.restrict (Ioo (0 : ℝ) 1)) :=
    (hφ.measurable.div ha.measurable).aestronglyMeasurable
  exact (memLp_two_iff_integrable_sq hmeas).2 hsq.integrableOn

/-- Multiplication by a nonzero weight recovers the original representative
almost everywhere on the open interval. -/
theorem ae_weight_mul_div_Ioo
    {a Z : ℝ → ℝ} (ha0 : ∀ x ∈ Ioo 0 1, a x ≠ 0) :
    (fun x ↦ a x * (Z x / a x)) =ᵐ[volume.restrict (Ioo (0 : ℝ) 1)] Z := by
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
  field_simp [ha0 x hx]

/-- The reconstructed derivative has precisely the weighted `L²`
membership of the given weighted limit. -/
theorem memLp_two_Ioo_weight_mul_div
    {a Z : ℝ → ℝ} (ha0 : ∀ x ∈ Ioo 0 1, a x ≠ 0)
    (hZ : MemLp Z 2 (volume.restrict (Ioo (0 : ℝ) 1))) :
    MemLp (fun x ↦ a x * (Z x / a x)) 2 (volume.restrict (Ioo (0 : ℝ) 1)) :=
  (memLp_congr_ae (ae_weight_mul_div_Ioo ha0)).2 hZ

/-- A continuous weight times the actual derivative of a globally `C¹`
function belongs to `L²` on the bounded interval. -/
theorem memLp_two_Ioo_weighted_deriv
    {a F : ℝ → ℝ} (ha : Continuous a) (hF : ContDiff ℝ 1 F) :
    MemLp (fun x ↦ a x * deriv F x) 2 (volume.restrict (Ioo (0 : ℝ) 1)) := by
  have hc : Continuous (fun x ↦ a x * deriv F x) := ha.mul hF.continuous_deriv_one
  apply (memLp_two_iff_integrable_sq hc.aestronglyMeasurable).2
  have hsq : IntegrableOn (fun x ↦ (a x * deriv F x) ^ 2) (Icc (0 : ℝ) 1) volume :=
    (hc.pow 2).continuousOn.integrableOn_compact isCompact_Icc
  exact hsq.mono_set Ioo_subset_Icc_self

/-- A weighted weak `L²` limit of actual derivatives identifies the genuine
weak derivative of a locally uniform limit. The representative is `Z / a`;
no classical derivative of the limit is assumed. -/
theorem hasWeakDerivOn_Ioo_of_weighted_weak_L2_limit
    {a Z f : ℝ → ℝ} {F : ℕ → ℝ → ℝ}
    (ha : Continuous a) (ha0 : ∀ x ∈ Ioo 0 1, a x ≠ 0)
    (hF : ∀ n, ContDiff ℝ 1 (F n)) (hf : ContinuousOn f (Ioo 0 1))
    (hFlim : TendstoLocallyUniformlyOn F f atTop (Ioo 0 1))
    (hZ : MemLp Z 2 (volume.restrict (Ioo (0 : ℝ) 1)))
    (hweak : ∀ v : Lp ℝ 2 (volume.restrict (Ioo (0 : ℝ) 1)),
      Tendsto
        (fun n ↦ ∫ x, (a x * deriv (F n) x) * v x
          ∂(volume.restrict (Ioo (0 : ℝ) 1))) atTop
        (𝓝 (∫ x, Z x * v x ∂(volume.restrict (Ioo (0 : ℝ) 1))))) :
    HasWeakDerivOn (Ioo 0 1) f (fun x ↦ Z x / a x) := by
  apply HasWeakDerivOn.of_tendsto_test_pairings
    (R := F) (P := fun n ↦ deriv (F n))
    (fun n ↦ hasWeakDerivOn_of_contDiff isOpen_Ioo (hF n))
    (hf.locallyIntegrableOn measurableSet_Ioo)
    (locallyIntegrableOn_Ioo_div_weight ha ha0 hZ)
  · intro φ hφ hφc hφI
    exact test_mul_integral_tendsto_of_locallyUniformlyOn isOpen_Ioo
      (fun n ↦ (hF n).continuous.continuousOn) hf hFlim
      (hφ.continuous_deriv (by simp)) hφc.deriv (tsupport_deriv_subset.trans hφI)
  · intro φ hφ hφc hφI
    have htest := memLp_two_Ioo_div_test ha ha0 hφ.continuous hφc hφI
    let v : Lp ℝ 2 (volume.restrict (Ioo (0 : ℝ) 1)) :=
      htest.toLp (fun x ↦ φ x / a x)
    have hv : (fun x ↦ v x) =ᵐ[volume.restrict (Ioo (0 : ℝ) 1)]
        (fun x ↦ φ x / a x) :=
      htest.coeFn_toLp
    have hφzero : ∀ x, x ∉ Ioo (0 : ℝ) 1 → φ x = 0 := by
      intro x hx
      exact image_eq_zero_of_notMem_tsupport fun hxφ ↦ hx (hφI hxφ)
    have hsource : ∀ n,
        (∫ x, (a x * deriv (F n) x) * v x
          ∂(volume.restrict (Ioo (0 : ℝ) 1))) = ∫ x, φ x * deriv (F n) x := by
      intro n
      calc
        (∫ x, (a x * deriv (F n) x) * v x
            ∂(volume.restrict (Ioo (0 : ℝ) 1))) =
            ∫ x in Ioo (0 : ℝ) 1, φ x * deriv (F n) x := by
          apply integral_congr_ae
          filter_upwards [hv, ae_restrict_mem measurableSet_Ioo] with x hx hxI
          rw [hx]
          field_simp [ha0 x hxI]
        _ = ∫ x, φ x * deriv (F n) x :=
          setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx ↦ by
            simp [hφzero x hx]
    have htarget : (∫ x, Z x * v x ∂(volume.restrict (Ioo (0 : ℝ) 1))) =
        ∫ x, φ x * (Z x / a x) := by
      calc
        (∫ x, Z x * v x ∂(volume.restrict (Ioo (0 : ℝ) 1))) =
            ∫ x in Ioo (0 : ℝ) 1, φ x * (Z x / a x) := by
          apply integral_congr_ae
          filter_upwards [hv] with x hx
          rw [hx]
          simp only [div_eq_mul_inv]
          ring
        _ = ∫ x, φ x * (Z x / a x) :=
          setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx ↦ by
            simp [hφzero x hx]
    simpa only [hsource, htarget] using hweak v

end RicciFlowSharpEstimate.Analysis
