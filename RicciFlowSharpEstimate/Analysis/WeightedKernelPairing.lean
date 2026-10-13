/-
Copyright (c) 2026 Ziyang Qin. All rights reserved.
No license is granted by this file.
Authors: Ziyang Qin
-/
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Kernel pairings with an integrable weighted coefficient

A kernel dominated by a weight can be paired with a coefficient whose
weighted product is integrable. The coefficient itself need not be
integrable. Fubini gives integrability of the adjoint and transfers a
bounded measurable test function from the primal integral to the adjoint.
-/

noncomputable section

namespace RicciFlowSharpEstimate.Analysis

open Filter MeasureTheory

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
  {μ : Measure α} {ν : Measure β} {g : α → β → ℝ} {w a : α → ℝ}

private theorem integrable_kernel_coefficient_prod [IsFiniteMeasure ν]
    (hg : AEStronglyMeasurable (Function.uncurry g) (μ.prod ν))
    (ha : AEStronglyMeasurable a μ)
    (hwa : Integrable (fun x => w x * a x) μ)
    (hbound : ∀ᵐ v ∂μ.prod ν, |g v.1 v.2| ≤ |w v.1|) :
    Integrable (fun v : α × β => g v.1 v.2 * a v.1) (μ.prod ν) := by
  refine (hwa.comp_fst ν).mono (hg.mul ha.comp_fst) ?_
  filter_upwards [hbound] with v hv
  simpa only [Real.norm_eq_abs, abs_mul] using
    mul_le_mul_of_nonneg_right hv (abs_nonneg (a v.1))

/-- A kernel dominated by a weight has an integrable adjoint whenever
the weight times its measurable coefficient is integrable. -/
theorem integrable_kernel_adjoint_of_weighted_integrable [SFinite μ] [IsFiniteMeasure ν]
    (hg : AEStronglyMeasurable (Function.uncurry g) (μ.prod ν))
    (ha : AEStronglyMeasurable a μ)
    (hwa : Integrable (fun x => w x * a x) μ)
    (hbound : ∀ᵐ v ∂μ.prod ν, |g v.1 v.2| ≤ |w v.1|) :
    Integrable (fun y => ∫ x, g x y * a x ∂μ) ν :=
  (integrable_kernel_coefficient_prod hg ha hwa hbound).integral_prod_right

/-- An integrable weighted coefficient and a bounded measurable test
function give integrable primal and adjoint pairings, with equal integrals.
No integrability assumption on the unweighted coefficient is required. -/
theorem integral_kernel_pairing_of_weighted_integrable [SFinite μ] [IsFiniteMeasure ν]
    {ξ : β → ℝ} {D : ℝ}
    (hg : AEStronglyMeasurable (Function.uncurry g) (μ.prod ν))
    (ha : AEStronglyMeasurable a μ)
    (hwa : Integrable (fun x => w x * a x) μ)
    (hbound : ∀ᵐ v ∂μ.prod ν, |g v.1 v.2| ≤ |w v.1|)
    (hξ : AEStronglyMeasurable ξ ν)
    (hD : ∀ᵐ y ∂ν, |ξ y| ≤ D) :
    Integrable (fun x => a x * (∫ y, g x y * ξ y ∂ν)) μ ∧
      Integrable (fun y => (∫ x, g x y * a x ∂μ) * ξ y) ν ∧
      (∫ x, a x * (∫ y, g x y * ξ y ∂ν) ∂μ) =
        ∫ y, (∫ x, g x y * a x ∂μ) * ξ y ∂ν := by
  have hDprod : ∀ᵐ v ∂μ.prod ν, ‖ξ v.2‖ ≤ D := by
    simpa only [Real.norm_eq_abs] using
      (Measure.quasiMeasurePreserving_snd (μ := μ) (ν := ν)).ae hD
  have hprod :
      Integrable (fun v : α × β => (g v.1 v.2 * a v.1) * ξ v.2) (μ.prod ν) :=
    (integrable_kernel_coefficient_prod hg ha hwa hbound).mul_bdd hξ.comp_snd hDprod
  have hleft (x : α) :
      (∫ y, (g x y * a x) * ξ y ∂ν) =
        a x * (∫ y, g x y * ξ y ∂ν) := by
    calc
      _ = ∫ y, a x * (g x y * ξ y) ∂ν := by
        apply integral_congr_ae
        filter_upwards with y
        rw [mul_comm (g x y) (a x), mul_assoc]
      _ = _ := integral_const_mul (a x) (fun y => g x y * ξ y)
  have hright (y : β) :
      (∫ x, (g x y * a x) * ξ y ∂μ) =
        (∫ x, g x y * a x ∂μ) * ξ y :=
    integral_mul_const (ξ y) (fun x => g x y * a x)
  refine ⟨hprod.integral_prod_left.congr (Eventually.of_forall hleft),
    hprod.integral_prod_right.congr (Eventually.of_forall hright), ?_⟩
  calc
    _ = ∫ x, ∫ y, (g x y * a x) * ξ y ∂ν ∂μ :=
      integral_congr_ae (Eventually.of_forall fun x => (hleft x).symm)
    _ = ∫ y, ∫ x, (g x y * a x) * ξ y ∂μ ∂ν :=
      integral_integral_swap (f := fun x y => (g x y * a x) * ξ y) hprod
    _ = _ := integral_congr_ae (Eventually.of_forall hright)

end RicciFlowSharpEstimate.Analysis
