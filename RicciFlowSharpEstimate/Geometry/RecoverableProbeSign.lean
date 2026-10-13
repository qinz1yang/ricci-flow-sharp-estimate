/-
Copyright (c) 2026 Ziyang Qin. All rights reserved.
No license is granted by this file.
Authors: Ziyang Qin
-/
import RicciFlowSharpEstimate.Geometry.RecoverableAreaCompetitor
import RicciFlowSharpEstimate.Geometry.WeakAreaPolarization
import RicciFlowSharpEstimate.Analysis.ParabolicGraphConvergence

/-!
# Global sign symmetry of actual recoverable probes

Negation acts on the probe and both genuine weak derivatives together. The
curvature and original constraints stay fixed; mass and complete action are
unchanged, while the actual operator changes sign. The proof negates the same
smooth recovering probes and retains all graph limits. This symmetry does not
assert that either orientation has a one-sided operator.
-/

noncomputable section
namespace RicciFlowSharpEstimate.Geometry.AreaProfile
open Set MeasureTheory Filter Topology
open scoped ContDiff
local notation "areaμ" => volume.restrict (Ioo (0 : ℝ) 1)

/-- A global sign change preserves the physical probe mass. -/
@[simp] theorem probeMass_neg (K r : ℝ → ℝ) : probeMass K (-r) = probeMass K r := by
  simp only [probeMass, Pi.neg_apply, neg_sq]

/-- A global sign change of all weak jet entries negates the actual operator. -/
@[simp] theorem weakMeridionalOperator_neg (K r p z : ℝ → ℝ) :
    weakMeridionalOperator K (-r) (-p) (-z) = -weakMeridionalOperator K r p z := by
  funext x
  simp only [weakMeridionalOperator, Pi.neg_apply]
  ring

/-- Simultaneous negation preserves the complete action, including signed lower
order terms; no field or derivative is changed independently. -/
@[simp] theorem weakMeridionalAction_neg (K r p z : ℝ → ℝ) :
    weakMeridionalAction K (-r) (-p) (-z) = weakMeridionalAction K r p z := by
  simpa only [neg_one_mul, neg_one_sq, one_mul, Pi.neg_def] using
    weakMeridionalAction_const_mul K r p z (-1)

/-- Negating an actual recoverable probe negates both its tied derivatives.
The proof uses the same curvature sequence and the negated smooth probe sequence
with all three weighted graph limits, without an absolute-value operation. -/
theorem IsRecoverableAreaCompetitor.neg_probe {C : ℝ} {K r p z : ℝ → ℝ}
    (h : IsRecoverableAreaCompetitor C K r p z) :
    IsRecoverableAreaCompetitor C K (-r) (-p) (-z) := by
  obtain ⟨hK, hg, hbox, hzero, hone, hm, Ks, rs, hS, hKS, hRS, hPS, hZS⟩ := h
  have hgraph : Analysis.HasParabolicWeakDerivatives (-r) (-p) (-z) := by
    simpa only [neg_one_mul, Pi.neg_def] using hg.const_mul (-1)
  have hconv := Analysis.parabolicGraph_tendsto_const_mul
    (fun n => (hS n).2.1.of_le (by simp)) hg
    (a := fun _ => (-1 : ℝ)) (a0 := -1) tendsto_const_nhds hRS hPS hZS
  refine ⟨hK, hgraph, hbox, hzero, hone, by simpa only [probeMass_neg] using hm,
    Ks, fun n => -rs n, ?_, hKS, ?_, ?_, ?_⟩
  · intro n
    obtain ⟨hnK, hnr, hnbox, hnzero, hnone, hnm⟩ := hS n
    exact ⟨hnK, hnr.neg, hnbox, hnzero, hnone, by simpa only [probeMass_neg] using hnm⟩
  · simpa only [neg_one_mul, Pi.neg_def] using hconv.1
  · simpa only [neg_one_mul, Pi.neg_def] using hconv.2.1
  · simpa only [neg_one_mul, Pi.neg_def] using hconv.2.2

end RicciFlowSharpEstimate.Geometry.AreaProfile
