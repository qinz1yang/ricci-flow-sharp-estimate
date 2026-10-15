/-
Copyright (c) 2026 Ziyang Qin. All rights reserved.
No license is granted by this file.
Authors: Ziyang Qin
-/
import RicciFlowSharpEstimate.Analysis.WeakSystemZeroIsolation
import RicciFlowSharpEstimate.Geometry.WeakProbeContinuation
import Mathlib.Topology.DiscreteSubset

/-! # Interior nodal sets of the actual signed minimum -/

noncomputable section
namespace RicciFlowSharpEstimate.Geometry.AreaProfile
open Set MeasureTheory Filter Topology
local notation "areaμ" => volume.restrict (Ioo (0 : ℝ) 1)

/-- Every interior zero of the actual continuous minimizing probe is isolated.
The conclusion uses the signed operator and canonical flux; no orientation,
curvature derivative or nodal hypothesis is supplied. -/
theorem IsRecoverableAreaCompetitor.isolated_zero_of_minimum
    {C : ℝ} {K r p z : ℝ → ℝ} (hC : 1 ≤ C)
    (h : IsRecoverableAreaCompetitor C K r p z)
    (hr : ContinuousOn r (Ioo (0 : ℝ) 1))
    (hp : ContinuousOn p (Ioo (0 : ℝ) 1))
    (hmin : ∀ K' r' p' z' : ℝ → ℝ, IsRecoverableAreaCompetitor C K' r' p' z' →
      weakMeridionalAction K r p z ≤ weakMeridionalAction K' r' p' z')
    {x₀ : ℝ} (hx₀ : x₀ ∈ Ioo (0 : ℝ) 1) (hr0 : r x₀ = 0) :
    ∀ᶠ x in 𝓝[≠] x₀, r x ≠ 0 := by
  let lam := weakMeridionalAction K r p z
  let P := weakProbeEulerFlux K r p z lam
  let q := fun x => weakProbeEulerMomentum K r p z lam x / warp K x ^ 2
  obtain ⟨hrD, _, _, _, hAC, hD⟩ := h.probe_first_order_system_of_minimum hC hr hp hmin
  have hP := (h.probe_euler_flux_of_minimum hC hmin).2.1
  have hg := h.geometry_bounds hC
  have hCpos : 0 < C := zero_lt_one.trans_le hC
  have hfpos (x : ℝ) (hx : x ∈ Ioo (0 : ℝ) 1) : 0 < warp K x := by
    exact (mul_pos (mul_pos (by positivity : (0 : ℝ) < 2 / C) hx.1)
      (sub_pos.mpr hx.2)).trans_le (hg.2.2.1 x ⟨hx.1.le, hx.2.le⟩).1
  let a := x₀ / 2
  let b := (x₀ + 1) / 2
  have ha : 0 < a := by dsimp [a]; linarith [hx₀.1]
  have hb : b < 1 := by dsimp [b]; linarith [hx₀.2]
  have hax : a < x₀ := by dsimp [a]; linarith [hx₀.1]
  have hxb : x₀ < b := by dsimp [b]; linarith [hx₀.2]
  have haI : a ∈ Ioo (0 : ℝ) 1 := ⟨ha, hax.trans hx₀.2⟩
  have hbI : b ∈ Ioo (0 : ℝ) 1 := ⟨hx₀.1.trans hxb, hb⟩
  have hsub : uIcc a b ⊆ Ioo (0 : ℝ) 1 := by
    rw [uIcc_of_le (hax.trans hxb).le]
    intro x hx
    exact ⟨ha.trans_le hx.1, hx.2.trans_lt hb⟩
  have hsubO : Ioo a b ⊆ Ioo (0 : ℝ) 1 :=
    fun x hx => ⟨ha.trans hx.1, hx.2.trans hb⟩
  have hfC : ContinuousAt (warp K) x₀ :=
    hg.1.continuousAt (Icc_mem_nhds hx₀.1 hx₀.2)
  have hfinv : ContinuousOn (fun x => (warp K x)⁻¹) (uIcc a b) :=
    (hg.1.mono (hsub.trans Ioo_subset_Icc_self)).inv₀
      (fun x hx => (hfpos x (hsub hx)).ne')
  obtain ⟨M, hM⟩ := isCompact_uIcc.exists_bound_of_continuousOn hfinv
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM a left_mem_uIcc)
  have hnonzero : p x₀ ≠ 0 ∨ q x₀ ≠ 0 ∨ P x₀ ≠ 0 := by
    have hn := h.probe_state_ne_zero_of_minimum hC hr hp hmin x₀ hx₀
    exact hn.resolve_left (not_not.mpr hr0)
  have hPc : ContinuousAt P x₀ := hP.continuousOn.continuousAt (by
    simpa only [uIcc_of_le zero_le_one] using Icc_mem_nhds hx₀.1 hx₀.2)
  apply Analysis.isolated_zero_of_weak_triangular_system
    (a₁ := fun x => (warp K x)⁻¹) (a₂ := fun x => (warp K x ^ 2)⁻¹)
    (b₁ := fun x => -2 * warpSlope K x / warp K x)
    (c₁ := fun x => K x / warp K x)
    (b₂ := fun _ => 0) (c₂ := fun _ => 0)
    (d₂ := fun x => -(K x * warpSlope K x) / (2 * warp K x))
    hax hxb (fun x hx => hrD x (hsubO hx)) (hAC a haI b hbI).1 (hAC a haI b hbI).2
    hPc
    (hfC.inv₀ (hfpos x₀ hx₀).ne') ((hfC.pow 2).inv₀ (pow_ne_zero 2 (hfpos x₀ hx₀).ne'))
    (inv_ne_zero (hfpos x₀ hx₀).ne') (inv_ne_zero (pow_ne_zero 2 (hfpos x₀ hx₀).ne'))
    ?_ ?_ hr0 hnonzero
  · refine ⟨4 * M + 2 * C * M, ?_⟩
    have hkae := (ae_restrict_iff' measurableSet_Ioo).mp hg.2.2.2.2
    filter_upwards [hkae] with x hxK hx
    have hxI := hsubO hx
    have hxi : x ∈ uIcc a b := by
      simpa only [uIcc_of_le (hax.trans hxb).le] using Ioo_subset_Icc_self hx
    have hi : |(warp K x)⁻¹| ≤ M := by simpa only [Real.norm_eq_abs] using hM x hxi
    have hbnd := (hg.2.2.1 x ⟨hxI.1.le, hxI.2.le⟩).2.2
    have hK0 : 0 ≤ K x := (by positivity : (0 : ℝ) ≤ 2 / C).trans (hxK hxI).1
    have hKb : |K x| ≤ 2 * C := by simpa only [abs_of_nonneg hK0] using (hxK hxI).2
    have h1 : |-2 * warpSlope K x / warp K x| ≤ 4 * M := by
      calc
        _ = 2 * |warpSlope K x| * |(warp K x)⁻¹| := by
          rw [div_eq_mul_inv, abs_mul, abs_mul]; norm_num
        _ ≤ 2 * 2 * M := by gcongr
        _ = _ := by ring
    have h2 : |K x / warp K x| ≤ 2 * C * M := by
      rw [div_eq_mul_inv, abs_mul]
      gcongr
    have h3 : |-(K x * warpSlope K x) / (2 * warp K x)| ≤ 2 * C * M := by
      calc
        _ = |K x| * |warpSlope K x| * |(warp K x)⁻¹| / 2 := by
          rw [div_eq_mul_inv, mul_inv, abs_mul, abs_neg, abs_mul, abs_mul]
          norm_num
          ring
        _ ≤ (2 * C) * 2 * M / 2 := by gcongr
        _ = _ := by ring
    have h4 : 0 ≤ 4 * M := by positivity
    have h5 : 0 ≤ 2 * C * M := by positivity
    refine ⟨by linarith, by linarith, ?_, ?_, by linarith⟩ <;> simp only [abs_zero] <;> positivity
  · have hdae := (ae_restrict_iff' measurableSet_Ioo).mp hD
    filter_upwards [hdae] with x hx hxI
    have hfx := (hfpos x (hsubO hxI)).ne'
    refine ⟨(hx (hsubO hxI)).1.congr_deriv ?_, (hx (hsubO hxI)).2.1.congr_deriv ?_⟩ <;>
      field_simp [hfx] <;> ring

/-- The zero set of the same signed minimizing probe is finite on every
compact subset of the physical interior. This makes no assertion about the
number of zeros accumulating at a physical pole. -/
theorem IsRecoverableAreaCompetitor.finite_zero_set_on_compact_of_minimum
    {C : ℝ} {K r p z : ℝ → ℝ} (hC : 1 ≤ C)
    (h : IsRecoverableAreaCompetitor C K r p z)
    (hr : ContinuousOn r (Ioo (0 : ℝ) 1))
    (hp : ContinuousOn p (Ioo (0 : ℝ) 1))
    (hmin : ∀ K' r' p' z' : ℝ → ℝ, IsRecoverableAreaCompetitor C K' r' p' z' →
      weakMeridionalAction K r p z ≤ weakMeridionalAction K' r' p' z')
    {s : Set ℝ} (hs : IsCompact s) (hsub : s ⊆ Ioo (0 : ℝ) 1) :
    (s ∩ {x | r x = 0}).Finite := by
  have hclosed : IsClosed (s ∩ {x | r x = 0}) := by
    simpa only [Set.preimage, Set.mem_singleton_iff] using
      (hr.mono hsub).preimage_isClosed_of_isClosed hs.isClosed (isClosed_singleton (x := 0))
  have hcompact : IsCompact (s ∩ {x | r x = 0}) :=
    hs.of_isClosed_subset hclosed inter_subset_left
  apply hcompact.finite
  apply isDiscrete_iff_nhdsNE.mpr
  intro x hx
  apply Filter.eventually_false_iff_eq_bot.mp
  have hzero : ∀ᶠ y in 𝓟 (s ∩ {x | r x = 0}), r y = 0 :=
    eventually_principal.mpr (fun _ hy => hy.2)
  filter_upwards [(h.isolated_zero_of_minimum hC hr hp hmin (hsub hx.1) hx.2).filter_mono
    inf_le_left, hzero.filter_mono inf_le_right] with y hne hy
  exact hne hy

end RicciFlowSharpEstimate.Geometry.AreaProfile
