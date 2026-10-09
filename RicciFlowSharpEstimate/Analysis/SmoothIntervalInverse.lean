/-
Copyright (c) 2026 Ziyang Qin. All rights reserved.
No license is granted by this file.
Authors: Ziyang Qin
-/
import RicciFlowSharpEstimate.Analysis.SmoothIntervalExtension
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Topology.Homeomorph.Lemmas

/-!
# Smooth inverses on closed real intervals

A smooth real function with positive derivative on a nondegenerate closed
interval has a globally smooth extension of its physical inverse. Smoothness
at the target endpoints follows by comparison with local smooth inverses.

Adapted from Ziyang Qin's historical closed-interval moment-coordinate
inverse construction, with arbitrary interval endpoints and no coordinate
wrapper.
-/

noncomputable section

namespace RicciFlowSharpEstimate.Analysis

open Filter Set
open scoped ContDiff Topology

private theorem strictMonoOn_Icc_of_deriv_pos (V : ℝ → ℝ) (a b : ℝ)
    (hV : ContDiff ℝ ∞ V) (hpos : ∀ x ∈ Icc a b, 0 < deriv V x) :
    StrictMonoOn V (Icc a b) := by
  apply strictMonoOn_of_deriv_pos (convex_Icc a b)
  · exact hV.continuous.continuousOn
  · intro x hx
    rw [interior_Icc] at hx
    exact hpos x ⟨hx.1.le, hx.2.le⟩

private theorem bijOn_Icc_of_deriv_pos (V : ℝ → ℝ) (a b : ℝ) (hab : a ≤ b)
    (hV : ContDiff ℝ ∞ V) (hpos : ∀ x ∈ Icc a b, 0 < deriv V x) :
    BijOn V (Icc a b) (Icc (V a) (V b)) := by
  have hmono := strictMonoOn_Icc_of_deriv_pos V a b hV hpos
  refine ⟨?_, hmono.injOn, ?_⟩
  · intro x hx
    exact ⟨hmono.monotoneOn ⟨le_rfl, hab⟩ hx hx.1,
      hmono.monotoneOn hx ⟨hab, le_rfl⟩ hx.2⟩
  · exact intermediate_value_Icc hab hV.continuous.continuousOn

private def intervalHomeomorph (V : ℝ → ℝ) (a b : ℝ) (hab : a ≤ b)
    (hV : ContDiff ℝ ∞ V) (hpos : ∀ x ∈ Icc a b, 0 < deriv V x) :
    {x : ℝ // x ∈ Icc a b} ≃ₜ {v : ℝ // v ∈ Icc (V a) (V b)} := by
  apply Continuous.homeoOfEquivCompactToT2
    (f := (bijOn_Icc_of_deriv_pos V a b hab hV hpos).equiv)
  apply Continuous.subtype_mk
  exact hV.continuous.comp continuous_subtype_val

private theorem exists_contDiffOn_intervalInverse
    (V : ℝ → ℝ) (a b : ℝ) (hab : a < b)
    (hV : ContDiff ℝ ∞ V) (hpos : ∀ x ∈ Icc a b, 0 < deriv V x) :
    ∃ inv : ℝ → ℝ,
      ContDiffOn ℝ ∞ inv (Icc (V a) (V b)) ∧
      MapsTo inv (Icc (V a) (V b)) (Icc a b) ∧
      (∀ x ∈ Icc a b, inv (V x) = x) ∧
      ∀ v ∈ Icc (V a) (V b), V (inv v) = v := by
  have hbij := bijOn_Icc_of_deriv_pos V a b hab.le hV hpos
  have hVab : V a < V b :=
    strictMonoOn_Icc_of_deriv_pos V a b hV hpos
      ⟨le_rfl, hab.le⟩ ⟨hab.le, le_rfl⟩ hab
  let H := intervalHomeomorph V a b hab.le hV hpos
  let inv : ℝ → ℝ := fun v => (H.symm (projIcc (V a) (V b) hVab.le v) : ℝ)
  have hinvMap : MapsTo inv (Icc (V a) (V b)) (Icc a b) := by
    intro v _
    exact (H.symm (projIcc (V a) (V b) hVab.le v)).property
  have hinvV : ∀ x ∈ Icc a b, inv (V x) = x := by
    intro x hx
    change (H.symm (projIcc (V a) (V b) hVab.le (V x)) : ℝ) = x
    rw [projIcc_of_mem hVab.le (hbij.mapsTo hx)]
    change (H.symm (H ⟨x, hx⟩) : ℝ) = x
    rw [H.symm_apply_apply]
  have hVinv : ∀ v ∈ Icc (V a) (V b), V (inv v) = v := by
    intro v hv
    change V (H.symm (projIcc (V a) (V b) hVab.le v)) = v
    rw [projIcc_of_mem hVab.le hv]
    exact congrArg Subtype.val (H.apply_symm_apply ⟨v, hv⟩)
  have hinvContinuous : Continuous inv :=
    continuous_subtype_val.comp (H.symm.continuous.comp continuous_projIcc)
  refine ⟨inv, ?_, hinvMap, hinvV, hVinv⟩
  intro W hW
  let x : ℝ := inv W
  have hx : x ∈ Icc a b := hinvMap hW
  have hVW : V x = W := hVinv W hW
  let d : ℝ := deriv V x
  have hdPos : 0 < d := hpos x hx
  have hVHas : HasDerivAt V d x :=
    (hV.differentiable (by simp) x).hasDerivAt
  let e : ℝ ≃L[ℝ] ℝ :=
    (ContinuousLinearEquiv.unitsEquivAut ℝ) (Units.mk0 d hdPos.ne')
  have hVF : HasFDerivAt V (e : ℝ →L[ℝ] ℝ) x :=
    hVHas.hasFDerivAt_equiv hdPos.ne'
  let P : OpenPartialHomeomorph ℝ ℝ :=
    hV.contDiffAt.toOpenPartialHomeomorph V hVF (by simp)
  have hxSource : x ∈ P.source :=
    ContDiffAt.mem_toOpenPartialHomeomorph_source hV.contDiffAt hVF (by simp)
  have hPsymmW : P.symm W = x := by
    rw [← hVW]
    exact P.left_inv hxSource
  have hWTarget : W ∈ P.target := by
    rw [← hVW]
    exact ContDiffAt.image_mem_toOpenPartialHomeomorph_target
      hV.contDiffAt hVF (by simp)
  have hPsymmSmooth : ContDiffAt ℝ ∞ (P.symm : ℝ → ℝ) W := by
    apply P.contDiffAt_symm_deriv hdPos.ne' hWTarget
    · change HasDerivAt V d (P.symm W)
      rw [hPsymmW]
      exact hVHas
    · change ContDiffAt ℝ ∞ V (P.symm W)
      rw [hPsymmW]
      exact hV.contDiffAt
  have hinvSource : ∀ᶠ y in 𝓝 W, inv y ∈ P.source :=
    hinvContinuous.continuousAt.preimage_mem_nhds (P.open_source.mem_nhds hxSource)
  have hinvEq : inv =ᶠ[𝓝[Icc (V a) (V b)] W] (P.symm : ℝ → ℝ) := by
    have hinvSourceWithin : ∀ᶠ y in 𝓝[Icc (V a) (V b)] W, inv y ∈ P.source :=
      hinvSource.filter_mono inf_le_left
    filter_upwards [hinvSourceWithin, self_mem_nhdsWithin] with y hySource hy
    have hleft := P.left_inv hySource
    change P.symm (V (inv y)) = inv y at hleft
    rw [hVinv y hy] at hleft
    exact hleft.symm
  exact hPsymmSmooth.contDiffWithinAt.congr_of_eventuallyEq_of_mem hinvEq hW

/-- The physical inverse of a smooth increasing map on a nondegenerate closed
interval has a globally smooth extension. Its two inverse laws, endpoint
values and reciprocal derivative identity hold on the entire closed
intervals, including both endpoints. -/
theorem exists_contDiff_inverse_on_Icc
    (V : ℝ → ℝ) (a b : ℝ) (hab : a < b)
    (hV : ContDiff ℝ ∞ V) (hpos : ∀ x ∈ Icc a b, 0 < deriv V x) :
    ∃ X : ℝ → ℝ,
      ContDiff ℝ ∞ X ∧
      MapsTo X (Icc (V a) (V b)) (Icc a b) ∧
      (∀ x ∈ Icc a b, X (V x) = x) ∧
      (∀ v ∈ Icc (V a) (V b), V (X v) = v) ∧
      X (V a) = a ∧ X (V b) = b ∧
      ∀ v ∈ Icc (V a) (V b), deriv X v * deriv V (X v) = 1 := by
  have hVab : V a < V b :=
    strictMonoOn_Icc_of_deriv_pos V a b hV hpos
      ⟨le_rfl, hab.le⟩ ⟨hab.le, le_rfl⟩ hab
  obtain ⟨inv, hinv, hinvMap, hinvV, hVinv⟩ :=
    exists_contDiffOn_intervalInverse V a b hab hV hpos
  obtain ⟨X, hX, hEq⟩ := exists_contDiff_extension_Icc inv (V a) (V b) hVab hinv
  have hXMap : MapsTo X (Icc (V a) (V b)) (Icc a b) := by
    intro v hv
    rw [hEq hv]
    exact hinvMap hv
  have hXV : ∀ x ∈ Icc a b, X (V x) = x := by
    intro x hx
    rw [hEq ((bijOn_Icc_of_deriv_pos V a b hab.le hV hpos).mapsTo hx)]
    exact hinvV x hx
  have hVX : ∀ v ∈ Icc (V a) (V b), V (X v) = v := by
    intro v hv
    rw [hEq hv]
    exact hVinv v hv
  refine ⟨X, hX, hXMap, hXV, hVX,
    hXV a ⟨le_rfl, hab.le⟩, hXV b ⟨hab.le, le_rfl⟩, ?_⟩
  intro v hv
  have hComp : HasDerivAt (fun y => V (X y)) (deriv V (X v) * deriv X v) v :=
    ((hV.differentiable (by simp) (X v)).hasDerivAt).comp v
      ((hX.differentiable (by simp) v).hasDerivAt)
  have hCompEq : (fun y => V (X y)) =ᶠ[𝓝[Icc (V a) (V b)] v] (fun y : ℝ => y) := by
    filter_upwards [self_mem_nhdsWithin] with y hy
    exact hVX y hy
  have hCompId : HasDerivWithinAt (fun y : ℝ => y)
      (deriv V (X v) * deriv X v) (Icc (V a) (V b)) v :=
    hComp.hasDerivWithinAt.congr_of_eventuallyEq hCompEq.symm (hVX v hv).symm
  have hId : HasDerivWithinAt (fun y : ℝ => y) 1 (Icc (V a) (V b)) v :=
    (hasDerivAt_id v).hasDerivWithinAt
  have hUnique := (uniqueDiffOn_Icc hVab v hv).eq_deriv (Icc (V a) (V b)) hId hCompId
  nlinarith

end RicciFlowSharpEstimate.Analysis
