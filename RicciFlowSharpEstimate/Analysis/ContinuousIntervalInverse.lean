/-
Copyright (c) 2026 Ziyang Qin. All rights reserved.
No license is granted by this file.
Authors: Ziyang Qin
-/
import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Order.ProjIcc
import Mathlib.Topology.Instances.Real.Lemmas

/-!
# Continuous clamped inverses on closed real intervals

A continuous strictly increasing function on a closed interval has a physical
inverse extended continuously by clamping the target. The definition depends
only on the function and endpoints, independently of its hypotheses.

Adapted from Ziyang Qin's historical physical meridian coordinate construction.
-/

noncomputable section

namespace RicciFlowSharpEstimate.Analysis

open Set

/-- The physical interval inverse, extended by clamping the target to its endpoint values. -/
def clampedIntervalInverse (f : ℝ → ℝ) (a b x : ℝ) : ℝ :=
  Function.invFunOn f (Icc a b) (max (f a) (min (f b) x))

private theorem interval_bijOn (f : ℝ → ℝ) (a b : ℝ) (hab : a ≤ b)
    (hf : ContinuousOn f (Icc a b)) (hm : StrictMonoOn f (Icc a b)) :
    BijOn f (Icc a b) (Icc (f a) (f b)) := by
  refine ⟨?_, hm.injOn, intermediate_value_Icc hab hf⟩
  intro x hx
  exact ⟨hm.monotoneOn ⟨le_rfl, hab⟩ hx hx.1,
    hm.monotoneOn hx ⟨hab, le_rfl⟩ hx.2⟩

/-- The clamped inverse always belongs to the original physical interval. -/
theorem clampedIntervalInverse_mem (f : ℝ → ℝ) (a b : ℝ) (hab : a ≤ b)
    (hf : ContinuousOn f (Icc a b)) (hm : StrictMonoOn f (Icc a b)) (x : ℝ) :
    clampedIntervalInverse f a b x ∈ Icc a b := by
  have hfab := hm.monotoneOn ⟨le_rfl, hab⟩ ⟨hab, le_rfl⟩ hab
  exact (interval_bijOn f a b hab hf hm).surjOn.mapsTo_invFunOn
    (projIcc (f a) (f b) hfab x).property

/-- The clamped inverse is a left inverse on the full original interval. -/
theorem clampedIntervalInverse_apply (f : ℝ → ℝ) (a b : ℝ) (hab : a ≤ b)
    (hm : StrictMonoOn f (Icc a b)) (x : ℝ) (hx : x ∈ Icc a b) :
    clampedIntervalInverse f a b (f x) = x := by
  have hlow := hm.monotoneOn ⟨le_rfl, hab⟩ hx hx.1
  have hhigh := hm.monotoneOn hx ⟨hab, le_rfl⟩ hx.2
  simp only [clampedIntervalInverse, min_eq_right hhigh, max_eq_right hlow]
  exact hm.injOn.leftInvOn_invFunOn hx

/-- On the target interval the original function is a right inverse. -/
theorem apply_clampedIntervalInverse (f : ℝ → ℝ) (a b : ℝ) (hab : a ≤ b)
    (hf : ContinuousOn f (Icc a b)) (x : ℝ) (hx : x ∈ Icc (f a) (f b)) :
    f (clampedIntervalInverse f a b x) = x := by
  simp only [clampedIntervalInverse, min_eq_right hx.2, max_eq_right hx.1]
  exact Function.invFunOn_eq (intermediate_value_Icc hab hf hx)

/-- The same proof-independent inverse is continuous on the whole real line. -/
theorem clampedIntervalInverse_continuous (f : ℝ → ℝ) (a b : ℝ) (hab : a ≤ b)
    (hf : ContinuousOn f (Icc a b)) (hm : StrictMonoOn f (Icc a b)) :
    Continuous (clampedIntervalInverse f a b) := by
  have hbij := interval_bijOn f a b hab hf hm
  have hfab := hm.monotoneOn ⟨le_rfl, hab⟩ ⟨hab, le_rfl⟩ hab
  let H : Icc a b ≃ₜ Icc (f a) (f b) :=
    Continuous.homeoOfEquivCompactToT2 (f := hbij.equiv)
      (Continuous.subtype_mk (hf.comp_continuous continuous_subtype_val
        (fun x => x.property)) _)
  have heq : clampedIntervalInverse f a b =
      fun x => (H.symm (projIcc (f a) (f b) hfab x) : ℝ) := by
    funext x
    apply hm.injOn (clampedIntervalInverse_mem f a b hab hf hm x)
      (H.symm (projIcc (f a) (f b) hfab x)).property
    have hleft : f (clampedIntervalInverse f a b x) =
        (projIcc (f a) (f b) hfab x : ℝ) :=
      hbij.surjOn.rightInvOn_invFunOn (projIcc (f a) (f b) hfab x).property
    have hright := congrArg Subtype.val
      (H.apply_symm_apply (projIcc (f a) (f b) hfab x))
    exact hleft.trans hright.symm
  rw [heq]
  exact continuous_subtype_val.comp (H.symm.continuous.comp continuous_projIcc)

end RicciFlowSharpEstimate.Analysis
