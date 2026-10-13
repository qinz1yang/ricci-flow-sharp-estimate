/-
Copyright (c) 2026 Ziyang Qin. All rights reserved.
No license is granted by this file.
Authors: Ziyang Qin
-/
import RicciFlowSharpEstimate.Analysis.WeakDerivative
import Mathlib.Analysis.Real.Sqrt
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSeminorm.Monotonicity

/-!
# The parabolic weighted weak derivative graph

On `(0, 1)`, write `w(x) = x * (1 - x)`. The graph
`HasParabolicWeakDerivatives r p z` requires that `p` and `z` are the first
and second weak derivatives of `r`, and that `r`, `√w * p`, and `w * √w * z`
belong to `L²`. It imposes no endpoint conditions.

Every globally `C²` function belongs to this graph with its actual first and
second derivatives. These derivatives are unique almost everywhere. The
weighted assumptions imply unweighted `L²` regularity of both derivatives
on every compact subset of the open interval.
-/

noncomputable section

namespace RicciFlowSharpEstimate.Analysis

open Filter MeasureTheory Set
open scoped ContDiff Topology

/-- The weighted graph of the first two real weak derivatives on `(0, 1)`.
The square energies have respective weights `1`, `x * (1 - x)`, and
`(x * (1 - x)) ^ 3`. No endpoint trace is prescribed. -/
def HasParabolicWeakDerivatives (r p z : ℝ → ℝ) : Prop :=
  HasWeakDerivOn (Ioo 0 1) r p ∧ HasWeakDerivOn (Ioo 0 1) p z ∧
    MemLp r 2 (volume.restrict (Ioo (0 : ℝ) 1)) ∧
    MemLp (fun x ↦ Real.sqrt (x * (1 - x)) * p x) 2
      (volume.restrict (Ioo (0 : ℝ) 1)) ∧
    MemLp (fun x ↦ x * (1 - x) * Real.sqrt (x * (1 - x)) * z x) 2
      (volume.restrict (Ioo (0 : ℝ) 1))

/-- The first entry is the genuine weak derivative of the probe. -/
theorem HasParabolicWeakDerivatives.weakDeriv {r p z : ℝ → ℝ}
    (h : HasParabolicWeakDerivatives r p z) : HasWeakDerivOn (Ioo 0 1) r p := h.1

/-- The second entry is the genuine weak derivative of the first. -/
theorem HasParabolicWeakDerivatives.weakDeriv_deriv {r p z : ℝ → ℝ}
    (h : HasParabolicWeakDerivatives r p z) : HasWeakDerivOn (Ioo 0 1) p z := h.2.1

/-- The unweighted probe belongs to L² on the physical interval. -/
theorem HasParabolicWeakDerivatives.memLp {r p z : ℝ → ℝ}
    (h : HasParabolicWeakDerivatives r p z) :
    MemLp r 2 (volume.restrict (Ioo (0 : ℝ) 1)) := h.2.2.1

/-- The first derivative has the parabolic L² weight. -/
theorem HasParabolicWeakDerivatives.memLp_weighted_deriv {r p z : ℝ → ℝ}
    (h : HasParabolicWeakDerivatives r p z) :
    MemLp (fun x ↦ Real.sqrt (x * (1 - x)) * p x) 2
      (volume.restrict (Ioo (0 : ℝ) 1)) := h.2.2.2.1

/-- The second derivative has the cubic parabolic L² weight. -/
theorem HasParabolicWeakDerivatives.memLp_weighted_secondDeriv {r p z : ℝ → ℝ}
    (h : HasParabolicWeakDerivatives r p z) :
    MemLp (fun x ↦ x * (1 - x) * Real.sqrt (x * (1 - x)) * z x) 2
      (volume.restrict (Ioo (0 : ℝ) 1)) := h.2.2.2.2

/-- The ordinary square-energy density in the weighted graph is integrable. -/
theorem HasParabolicWeakDerivatives.integrable_sq
    {r p z : ℝ → ℝ} (h : HasParabolicWeakDerivatives r p z) :
    Integrable (fun x ↦ r x ^ 2) (volume.restrict (Ioo (0 : ℝ) 1)) :=
  h.memLp.integrable_sq

/-- The first weighted derivative square-energy density is integrable. -/
theorem HasParabolicWeakDerivatives.integrable_weighted_deriv_sq
    {r p z : ℝ → ℝ} (h : HasParabolicWeakDerivatives r p z) :
    Integrable (fun x ↦ x * (1 - x) * p x ^ 2)
      (volume.restrict (Ioo (0 : ℝ) 1)) := by
  apply h.memLp_weighted_deriv.integrable_sq.congr
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
  rw [mul_pow, Real.sq_sqrt (mul_nonneg hx.1.le (sub_nonneg.mpr hx.2.le))]

/-- The second weighted derivative square-energy density is integrable. -/
theorem HasParabolicWeakDerivatives.integrable_weighted_secondDeriv_sq
    {r p z : ℝ → ℝ} (h : HasParabolicWeakDerivatives r p z) :
    Integrable (fun x ↦ (x * (1 - x)) ^ 3 * z x ^ 2)
      (volume.restrict (Ioo (0 : ℝ) 1)) := by
  apply h.memLp_weighted_secondDeriv.integrable_sq.congr
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
  rw [mul_pow, mul_pow,
    Real.sq_sqrt (mul_nonneg hx.1.le (sub_nonneg.mpr hx.2.le))]
  ring

private theorem memLp_two_Ioo_of_continuous
    {f : ℝ → ℝ} (hf : Continuous f) :
    MemLp f 2 (volume.restrict (Ioo (0 : ℝ) 1)) := by
  apply (memLp_two_iff_integrable_sq hf.aestronglyMeasurable).2
  have hi : IntegrableOn (fun x ↦ f x ^ 2) (Icc (0 : ℝ) 1) volume :=
    (hf.pow 2).continuousOn.integrableOn_compact isCompact_Icc
  exact hi.mono_set Ioo_subset_Icc_self

/-- A globally `C²` function lies in the weighted weak derivative graph with
its actual first and second derivatives, without endpoint conditions. -/
theorem hasParabolicWeakDerivatives_of_contDiff
    {r : ℝ → ℝ} (hr : ContDiff ℝ 2 r) :
    HasParabolicWeakDerivatives r (deriv r) (deriv (deriv r)) := by
  have hrD : ContDiff ℝ 1 (deriv r) := hr.deriv'
  have hw : Continuous (fun x : ℝ ↦ x * (1 - x)) := by fun_prop
  refine ⟨hasWeakDerivOn_of_contDiff isOpen_Ioo (hr.of_le (by norm_num)),
    hasWeakDerivOn_of_contDiff isOpen_Ioo hrD,
    memLp_two_Ioo_of_continuous hr.continuous, ?_, ?_⟩
  · exact memLp_two_Ioo_of_continuous (hw.sqrt.mul hrD.continuous)
  · exact memLp_two_Ioo_of_continuous
      ((hw.mul hw.sqrt).mul hrD.continuous_deriv_one)

/-- The two weak derivatives in the graph are uniquely determined almost
everywhere by the function. -/
theorem HasParabolicWeakDerivatives.ae_unique
    {r p z p' z' : ℝ → ℝ}
    (h : HasParabolicWeakDerivatives r p z)
    (h' : HasParabolicWeakDerivatives r p' z') :
    (p =ᵐ[volume.restrict (Ioo (0 : ℝ) 1)] p') ∧
      (z =ᵐ[volume.restrict (Ioo (0 : ℝ) 1)] z') := by
  have hp := h.weakDeriv.ae_unique h'.weakDeriv isOpen_Ioo
  have hz : HasWeakDerivOn (Ioo 0 1) p' z :=
    h.weakDeriv_deriv.congr_ae hp ae_eq_rfl
  exact ⟨hp, hz.ae_unique h'.weakDeriv_deriv isOpen_Ioo⟩

private theorem memLp_two_of_weighted_on_compact
    {U K : Set ℝ} {a f : ℝ → ℝ}
    (hK : IsCompact K) (hKU : K ⊆ U)
    (ha : ContinuousOn a K) (ha0 : ∀ x ∈ K, a x ≠ 0)
    (hf : LocallyIntegrableOn f U volume)
    (haf : MemLp (fun x ↦ a x * f x) 2 (volume.restrict U)) :
    MemLp f 2 (volume.restrict K) := by
  have hinv : ContinuousOn (fun x ↦ (a x)⁻¹) K := ha.inv₀ ha0
  obtain ⟨C, hC⟩ : ∃ C : ℝ, ∀ x ∈ K, ‖(a x)⁻¹‖ ≤ C :=
    hK.exists_bound_of_continuousOn hinv
  have hafK : MemLp (fun x ↦ a x * f x) 2 (volume.restrict K) :=
    haf.mono_measure (Measure.restrict_mono_set volume hKU)
  apply hafK.of_le_mul (c := C) (hf.mono_set hKU).aestronglyMeasurable
  filter_upwards [ae_restrict_mem hK.measurableSet] with x hx
  calc
    ‖f x‖ = ‖(a x)⁻¹ * (a x * f x)‖ := by
      rw [← mul_assoc, inv_mul_cancel₀ (ha0 x hx), one_mul]
    _ = ‖(a x)⁻¹‖ * ‖a x * f x‖ := norm_mul _ _
    _ ≤ C * ‖a x * f x‖ :=
      mul_le_mul_of_nonneg_right (hC x hx) (norm_nonneg _)

/-- On every compact subset of the open interval, the first derivative in
the weighted graph belongs to ordinary `L²`. -/
theorem HasParabolicWeakDerivatives.memLp_deriv_compact
    {r p z : ℝ → ℝ} (h : HasParabolicWeakDerivatives r p z)
    {K : Set ℝ} (hK : IsCompact K) (hKI : K ⊆ Ioo 0 1) :
    MemLp p 2 (volume.restrict K) := by
  have hw : Continuous (fun x : ℝ ↦ x * (1 - x)) := by fun_prop
  refine memLp_two_of_weighted_on_compact hK hKI hw.sqrt.continuousOn
    ?_ h.weakDeriv.locallyIntegrable_deriv h.memLp_weighted_deriv
  intro x hx
  exact (Real.sqrt_pos.2 (mul_pos (hKI hx).1 (sub_pos.mpr (hKI hx).2))).ne'

/-- On every compact subset of the open interval, the second derivative in
the weighted graph belongs to ordinary `L²`. -/
theorem HasParabolicWeakDerivatives.memLp_secondDeriv_compact
    {r p z : ℝ → ℝ} (h : HasParabolicWeakDerivatives r p z)
    {K : Set ℝ} (hK : IsCompact K) (hKI : K ⊆ Ioo 0 1) :
    MemLp z 2 (volume.restrict K) := by
  have hw : Continuous (fun x : ℝ ↦ x * (1 - x)) := by fun_prop
  refine memLp_two_of_weighted_on_compact hK hKI (hw.mul hw.sqrt).continuousOn
    ?_ h.weakDeriv_deriv.locallyIntegrable_deriv
    h.memLp_weighted_secondDeriv
  intro x hx
  have hpos : 0 < x * (1 - x) := mul_pos (hKI hx).1 (sub_pos.mpr (hKI hx).2)
  exact (mul_pos hpos (Real.sqrt_pos.2 hpos)).ne'

end RicciFlowSharpEstimate.Analysis
