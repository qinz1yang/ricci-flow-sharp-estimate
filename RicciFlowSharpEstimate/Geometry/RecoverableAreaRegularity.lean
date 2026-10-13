/-
Copyright (c) 2026 Ziyang Qin. All rights reserved.
No license is granted by this file.
Authors: Ziyang Qin
-/
import RicciFlowSharpEstimate.Geometry.RecoverableAreaGeometry
import RicciFlowSharpEstimate.Analysis.WeakDerivativePrimitives

/-!
# Actual local regularity of recoverable area primitives

The existing smooth recovery supplies the genuine weak derivatives of the same
curvature primitives. The local weak fundamental theorem converts their
continuous representatives into the classical first warp derivative and the
local absolutely continuous slope, without curvature differentiability.
-/

noncomputable section
namespace RicciFlowSharpEstimate.Geometry.AreaProfile
open Set MeasureTheory Filter Topology
local notation "areaμ" => volume.restrict (Ioo (0 : ℝ) 1)

/-- Recoverable curvature primitives have their actual tied weak derivatives.
No derivative of the limiting curvature is used. -/
theorem IsRecoverableAreaCompetitor.primitive_weak_derivatives
    {C : ℝ} {K r p z : ℝ → ℝ} (hC : 1 ≤ C)
    (h : IsRecoverableAreaCompetitor C K r p z) :
    Analysis.HasWeakDerivOn (Ioo (0 : ℝ) 1) (warp K) (warpSlope K) ∧
      Analysis.HasWeakDerivOn (Ioo (0 : ℝ) 1) (warpSlope K) (fun x => -2 * K x) := by
  have hK : MemLp K 2 areaμ := h.1
  obtain ⟨Ks, rs, hS, hKS, _, _, _, _⟩ := h.strong_curvature_subsequence
  have hCpos : 0 < C := zero_lt_one.trans_le hC
  have hlo : 0 < 2 / C := by positivity
  have hcont (n : ℕ) : Continuous (Ks n) := (hS n).1.continuous
  have hbox (n : ℕ) :
      ∀ x ∈ Icc (0 : ℝ) 1, 2 / C ≤ Ks n x ∧ Ks n x ≤ 2 * C :=
    (hS n).common_bounds
  have hzero (n : ℕ) : (∫ x in (0 : ℝ)..1, Ks n x) = 2 :=
    (hS n).2.2.2.1
  have hweak : ∀ v : Lp ℝ 2 areaμ,
      Tendsto (fun n => ∫ x, Ks n x * v x ∂areaμ) atTop
        (𝓝 (∫ x, K x * v x ∂areaμ)) := by
    intro v
    have hvstrong : Tendsto
        (fun (_ : ℕ) => eLpNorm ((v : ℝ → ℝ) - (v : ℝ → ℝ)) 2 areaμ)
        atTop (𝓝 0) := by
      simp only [sub_self, eLpNorm_zero]
      exact tendsto_const_nhds
    exact (Analysis.tendsto_integral_mul_of_tendsto_eLpNorm_two
      (u := Ks) (u0 := K) (v := fun _ => (v : ℝ → ℝ)) (v0 := (v : ℝ → ℝ))
      (fun n => (hS n).memLp_curvature) hK
      (fun _ => Lp.memLp v) (Lp.memLp v) hKS hvstrong).2.2
  exact ⟨hasWeakDerivOn_warp_of_weak_L2
    Ks K hcont (2 / C) (2 * C) hlo hbox hK hweak hzero,
    hasWeakDerivOn_warpSlope_of_weak_L2 Ks K hcont (2 / C) (2 * C) hlo hbox hK hweak⟩

/-- The actual warp is C¹ in the physical interior. Its slope is locally
absolutely continuous with genuine a.e. derivative minus twice the curvature. -/
theorem IsRecoverableAreaCompetitor.primitive_local_regularity
    {C : ℝ} {K r p z : ℝ → ℝ} (hC : 1 ≤ C)
    (h : IsRecoverableAreaCompetitor C K r p z) :
    (∀ x ∈ Ioo (0 : ℝ) 1, HasDerivAt (warp K) (warpSlope K x) x) ∧
      (∀ a ∈ Ioo (0 : ℝ) 1, ∀ b ∈ Ioo (0 : ℝ) 1,
        AbsolutelyContinuousOnInterval (warpSlope K) a b) ∧
      (∀ᵐ x ∂areaμ, HasDerivAt (warpSlope K) (-2 * K x) x) := by
  have hw := h.primitive_weak_derivatives hC
  have hg := h.geometry_bounds hC
  have hf := hg.1.mono Ioo_subset_Icc_self
  have hb := hg.2.1.mono Ioo_subset_Icc_self
  refine ⟨?_, ?_, hw.2.ae_hasDerivAt_of_continuousOn hb⟩
  · intro x hx
    exact hw.1.hasDerivAt_of_continuousOn hf hb hx
  · intro a ha b hb'
    exact hw.2.absolutelyContinuousOnInterval hb ha hb'

end RicciFlowSharpEstimate.Geometry.AreaProfile
