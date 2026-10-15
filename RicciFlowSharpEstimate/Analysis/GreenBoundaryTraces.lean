/-
Copyright (c) 2026 Ziyang Qin. All rights reserved.
No license is granted by this file.
Authors: Ziyang Qin
-/
import RicciFlowSharpEstimate.Analysis.UnitIntervalGreen

/-!
# Boundary traces of weighted Dirichlet adjoints

The Dirichlet adjoint is continuous on the closed unit interval and vanishes
at both endpoints when the source multiplied by the parabolic weight is
integrable. The evaluation variable is the second argument of the kernel.
-/

noncomputable section

namespace RicciFlowSharpEstimate.Analysis

open Filter MeasureTheory Set

local notation "areaμ" => volume.restrict (Ioo (0 : ℝ) 1)

/-- The actual weighted Dirichlet adjoint extends continuously to both physical
endpoints with value zero. Only weighted source integrability is required;
source measurability on the open interval is derived internally. -/
theorem weighted_dirichlet_adjoint_boundary_traces (A : ℝ → ℝ)
    (hA : Integrable (fun s => s * (1 - s) * A s) areaμ) :
    let G := fun x => ∫ s, unitDirichletKernel s x * A s ∂areaμ
    ContinuousOn G (Icc (0 : ℝ) 1) ∧ G 0 = 0 ∧ G 1 = 0 := by
  have hweight : AEStronglyMeasurable (fun s : ℝ => s * (1 - s)) areaμ :=
    (continuous_id.mul (continuous_const.sub continuous_id)).aestronglyMeasurable
  have hAm : AEStronglyMeasurable A areaμ := by
    apply (hA.aestronglyMeasurable.div₀ hweight).congr
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
    change (s * (1 - s) * A s) / (s * (1 - s)) = A s
    exact mul_div_cancel_left₀ (A s) (mul_pos hs.1 (sub_pos.mpr hs.2)).ne'
  have hmeas (x : ℝ) :
      AEStronglyMeasurable (fun s => unitDirichletKernel s x * A s) areaμ := by
    have hk : Continuous (fun s => unitDirichletKernel s x) :=
      continuous_unitDirichletKernel.comp (continuous_id.prodMk continuous_const)
    exact hk.aestronglyMeasurable.mul hAm
  have hbound (x : ℝ) (hx : x ∈ Icc (0 : ℝ) 1) :
      ∀ᵐ s ∂areaμ, ‖unitDirichletKernel s x * A s‖ ≤ ‖s * (1 - s) * A s‖ := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
    simp only [Real.norm_eq_abs, abs_mul, abs_of_pos hs.1, abs_of_pos (sub_pos.mpr hs.2)]
    exact mul_le_mul_of_nonneg_right
      (abs_unitDirichletKernel_le s x (Ioo_subset_Icc_self hs) hx) (abs_nonneg (A s))
  have hcont : ContinuousOn (fun x => ∫ s, unitDirichletKernel s x * A s ∂areaμ)
      (Icc (0 : ℝ) 1) := by
    apply continuousOn_of_dominated (fun x _ => hmeas x) hbound hA.norm
    exact Eventually.of_forall fun s =>
      ((continuous_unitDirichletKernel.comp (continuous_const.prodMk continuous_id)).mul
        continuous_const).continuousOn
  refine ⟨hcont, ?_, ?_⟩
  · change (∫ s, unitDirichletKernel s 0 * A s ∂areaμ) = 0
    apply integral_eq_zero_of_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
    simp only [unitDirichletKernel, min_eq_right hs.1.le, mul_zero, sub_self, zero_mul,
      Pi.zero_apply]
  · change (∫ s, unitDirichletKernel s 1 * A s ∂areaμ) = 0
    apply integral_eq_zero_of_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
    simp only [unitDirichletKernel, min_eq_left hs.2.le, mul_one, sub_self, zero_mul,
      Pi.zero_apply]

end RicciFlowSharpEstimate.Analysis
