/-
Copyright (c) 2026 Ziyang Qin. All rights reserved.
No license is granted by this file.
Authors: Ziyang Qin
-/
import RicciFlowSharpEstimate.Analysis.ParabolicSobolev
import RicciFlowSharpEstimate.Analysis.WeakDerivativePrimitives
import Mathlib.Analysis.Calculus.Deriv.Abs

/-!
# Interior C¹ regularity and the corner obstruction in the parabolic graph

The first weak derivative has a continuous representative because it too has a
locally integrable weak derivative. Consequently a continuous probe in the
parabolic second-order graph is C¹ in the interior. In particular, taking the
absolute value of a smooth probe with a simple interior zero need not preserve
the graph: even the absolute value of a translated linear probe is excluded.
-/

noncomputable section
namespace RicciFlowSharpEstimate.Analysis
open Set MeasureTheory
open scoped ContDiff

/-- A continuous representative in the parabolic second-order weak graph is
C¹ on the physical interior, independently of the chosen derivative representatives. -/
theorem HasParabolicWeakDerivatives.contDiffOn_one_of_continuousOn
    {r p z : ℝ → ℝ} (h : HasParabolicWeakDerivatives r p z)
    (hr : ContinuousOn r (Ioo (0 : ℝ) 1)) :
    ContDiffOn ℝ 1 r (Ioo (0 : ℝ) 1) := by
  obtain ⟨P, hPc, hpP, _⟩ := h.weakDeriv_deriv.exists_continuous_representative_Ioo
    (show (1 / 2 : ℝ) ∈ Ioo 0 1 by norm_num)
  have hRP := h.weakDeriv.congr_ae Filter.EventuallyEq.rfl hpP
  exact hRP.contDiffOn_one_of_continuousOn hr hPc

/-- The absolute value of a translated linear probe with an interior zero has
no parabolic second-order weak graph. A sign-changing smooth probe therefore
cannot be made nonnegative by absolute value without a separate domain proof. -/
theorem not_exists_parabolicWeakDerivatives_abs_sub
    (c : ℝ) (hc : c ∈ Ioo (0 : ℝ) 1) :
    ¬ ∃ p z : ℝ → ℝ, HasParabolicWeakDerivatives (fun x => |x - c|) p z := by
  rintro ⟨p, z, h⟩
  have hr : ContinuousOn (fun x : ℝ => |x - c|) (Ioo (0 : ℝ) 1) :=
    (continuous_id.sub continuous_const).abs.continuousOn
  have hd : DifferentiableAt ℝ (fun x : ℝ => |x - c|) c :=
    (h.contDiffOn_one_of_continuousOn hr).differentiableOn_one.differentiableAt
      (isOpen_Ioo.mem_nhds hc)
  have htranslate : DifferentiableAt ℝ (fun x : ℝ => x + c) 0 := by fun_prop
  have hd' : DifferentiableAt ℝ (fun x : ℝ => |x - c|) (0 + c) := by
    simpa only [zero_add] using hd
  have hcomp := hd'.comp 0 htranslate
  apply not_differentiableAt_abs_zero
  simpa only [Function.comp_def, add_sub_cancel_right] using hcomp

end RicciFlowSharpEstimate.Analysis
