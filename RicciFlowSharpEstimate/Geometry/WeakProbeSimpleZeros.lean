/-
Copyright (c) 2026 Ziyang Qin. All rights reserved.
No license is granted by this file.
Authors: Ziyang Qin
-/
import RicciFlowSharpEstimate.Analysis.ParabolicCutRecovery
import RicciFlowSharpEstimate.Geometry.AreaRawGraphRecovery
import RicciFlowSharpEstimate.Geometry.WeakProbeNodalSet
import RicciFlowSharpEstimate.Geometry.SmoothAreaSafety
import RicciFlowSharpEstimate.Geometry.WeakAreaPolarization

/-! # Simple interior zeros of a zero-action joint minimum -/

noncomputable section
namespace RicciFlowSharpEstimate.Geometry.AreaProfile
open Set MeasureTheory Filter Topology
open scoped ContDiff
local notation "areaμ" => volume.restrict (Ioo (0 : ℝ) 1)

private theorem continuous_left_cut {r : ℝ → ℝ} {c : ℝ}
    (hr : ContinuousOn r (Ioo (0 : ℝ) 1)) (hc : c ∈ Ioo (0 : ℝ) 1) (hz : r c = 0) :
    ContinuousOn (fun x => if x < c then r x else 0) (Ioo (0 : ℝ) 1) := by
  intro x hx
  rcases lt_trichotomy x c with hxc | hxc | hcx
  · have heq : (fun y => if y < c then r y else 0) =ᶠ[𝓝 x] r := by
      filter_upwards [Iio_mem_nhds hxc] with y hy
      exact ite_eq_left hy
    exact ((hr.continuousAt (isOpen_Ioo.mem_nhds hx)).congr heq.symm).continuousWithinAt
  · subst x
    have hr0 : Tendsto (fun x => ‖r x‖) (𝓝 c) (𝓝 0) := by
      simpa only [hz, norm_zero] using
        (hr.continuousAt (isOpen_Ioo.mem_nhds hc)).tendsto.norm
    have hcut : Tendsto (fun x => if x < c then r x else 0) (𝓝 c) (𝓝 0) := by
      apply squeeze_zero_norm' ?_ hr0
      exact Eventually.of_forall fun y => by split_ifs <;> simp
    have hcutC : ContinuousAt (fun x => if x < c then r x else 0) c := by
      simpa only [ContinuousAt, lt_self_iff_false, ite_false] using hcut
    exact hcutC.continuousWithinAt
  · have heq : (fun y => if y < c then r y else 0) =ᶠ[𝓝 x] (fun _ => 0) := by
      filter_upwards [Ioi_mem_nhds hcx] with y hy
      exact ite_eq_right (not_lt.mpr hy.le)
    exact (continuousAt_const.congr heq.symm).continuousWithinAt

private theorem minimum_not_zero_on_interval
    {C : ℝ} {K r p z : ℝ → ℝ} (hC : 1 ≤ C)
    (h : IsRecoverableAreaCompetitor C K r p z)
    (hr : ContinuousOn r (Ioo (0 : ℝ) 1))
    (hp : ContinuousOn p (Ioo (0 : ℝ) 1))
    (hmin : ∀ K' r' p' z' : ℝ → ℝ, IsRecoverableAreaCompetitor C K' r' p' z' →
      weakMeridionalAction K r p z ≤ weakMeridionalAction K' r' p' z')
    {a b : ℝ} (hab : a < b) (hsub : Ioo a b ⊆ Ioo (0 : ℝ) 1)
    (hz : ∀ x ∈ Ioo a b, r x = 0) : False := by
  let d := (a + b) / 2
  have hd : d ∈ Ioo a b := by dsimp [d]; constructor <;> linarith
  have hiso := h.isolated_zero_of_minimum hC hr hp hmin (hsub hd) (hz d hd)
  have hI : ∀ᶠ x in 𝓝 d, x ∈ Ioo a b := isOpen_Ioo.mem_nhds hd
  have hfalse : ∀ᶠ x in 𝓝[≠] d, False := by
    filter_upwards [hiso, hI.filter_mono nhdsWithin_le_nhds] with x hx hxI
    exact hx (hz x hxI)
  exact hfalse.exists.elim (fun _ h => h)

/-- Every interior zero of a zero-action global joint minimum is simple.
The proof uses genuine same-cap smooth recovery of the two double-trace cuts;
no operator orientation or physical probe pole value is assumed. -/
theorem IsRecoverableAreaCompetitor.simple_zero_of_zero_action_minimum
    {C : ℝ} {K r p z : ℝ → ℝ} (hC : 1 ≤ C)
    (h : IsRecoverableAreaCompetitor C K r p z)
    (hr : ContinuousOn r (Ioo (0 : ℝ) 1))
    (hp : ContinuousOn p (Ioo (0 : ℝ) 1))
    (hzero : weakMeridionalAction K r p z = 0)
    (hmin : ∀ K' r' p' z' : ℝ → ℝ, IsRecoverableAreaCompetitor C K' r' p' z' →
      weakMeridionalAction K r p z ≤ weakMeridionalAction K' r' p' z')
    {c : ℝ} (hc : c ∈ Ioo (0 : ℝ) 1) (hrc : r c = 0) :
    HasDerivAt r (p c) c ∧ p c ≠ 0 := by
  refine ⟨h.2.1.weakDeriv.hasDerivAt_of_continuousOn hr hp hc, ?_⟩
  intro hpc
  let rL := fun x => if x < c then r x else 0
  let pL := fun x => if x < c then p x else 0
  let zL := fun x => if x < c then z x else 0
  have hinf : 0 ≤ smoothAreaInfimum C := by
    apply le_csInf (smoothAreaActionValues_nonempty C hC)
    rintro v ⟨J, s, hs, rfl⟩
    simpa only [hzero, weakMeridionalAction_deriv] using
      hmin J s (deriv s) (deriv (deriv s)) hs.recoverable
  have hsafe : C ∈ rotationalSafeCaps :=
    (smoothAreaInfimum_nonneg_iff_rotationalSafeCap C hC).mp hinf
  obtain ⟨Ks, rs, hS, hKS, hRS, hPS, hZS, hKae⟩ := h.strong_curvature_subsequence
  obtain ⟨hL, hR, m, us, vs, _hm, hmtop, _hus, _hvs, huC, hvC,
      hLu, hLp, hLz, hRu, hRp, hRz⟩ :=
    Analysis.exists_smooth_cut_parabolicGraph_recovery
      (fun n => (hS n).2.1) h.2.1 hr hp hc hrc hpc hRS hPS hZS
  have hKs (n : ℕ) : IsSmoothAreaCurvature C (Ks (m n)) :=
    ⟨(hS (m n)).1, (hS (m n)).2.2.1,
      (hS (m n)).2.2.2.1, (hS (m n)).2.2.2.2.1⟩
  have hKLS := hKS.comp hmtop
  have hKA : ∀ᵐ x ∂areaμ, Tendsto (fun n => Ks (m n) x) atTop (𝓝 (K x)) :=
    hKae.mono (fun _ hx => hx.comp hmtop)
  have hleft := h.curvature_bounded.raw_graph_recovery hC hL
    (fun n => Ks (m n)) us hKs huC hKLS hKA hLu hLp hLz
  have hright := h.curvature_bounded.raw_graph_recovery hC hR
    (fun n => Ks (m n)) vs hKs hvC hKLS hKA hRu hRp hRz
  have hsmoothNonneg (s : ℕ → ℝ → ℝ) (hs : ∀ n, ContDiff ℝ ∞ (s n)) (n : ℕ) :
      0 ≤ meridionalAction (Ks (m n)) (s n) := by
    obtain ⟨κ, Λ, hκ, hbox, hratio⟩ := (hS (m n)).2.2.1
    exact areaAction_nonneg_of_rotationalSafeCap C hsafe (Ks (m n)) (s n)
      (hS (m n)).1 (hs n) (fun x hx => hκ.trans_le (hbox x hx).1)
      (hS (m n)).2.2.2.1 (hS (m n)).2.2.2.2.1 κ Λ hκ hbox hratio
  have hAL : 0 ≤ weakMeridionalAction K rL pL zL :=
    ge_of_tendsto' hleft.2.2.1 (hsmoothNonneg us huC)
  have hAR : 0 ≤ weakMeridionalAction K (r - rL) (p - pL) (z - zL) :=
    ge_of_tendsto' hright.2.2.1 (hsmoothNonneg vs hvC)
  have hAadd : weakMeridionalAction K r p z = weakMeridionalAction K rL pL zL +
      weakMeridionalAction K (r - rL) (p - pL) (z - zL) := by
    unfold weakMeridionalAction
    rw [← intervalIntegral.integral_add
      ((intervalIntegrable_iff_integrableOn_Ioo_of_le zero_le_one).mpr hleft.1)
      ((intervalIntegrable_iff_integrableOn_Ioo_of_le zero_le_one).mpr hright.1)]
    apply intervalIntegral.integral_congr
    intro x _
    by_cases hx : x < c <;> simp [hx, meridionalActionDensity]
  have hAL0 : weakMeridionalAction K rL pL zL = 0 := by linarith
  have hAR0 : weakMeridionalAction K (r - rL) (p - pL) (z - zL) = 0 := by linarith
  have hMadd : probeMass K r = probeMass K rL + probeMass K (r - rL) := by
    unfold probeMass
    rw [← intervalIntegral.integral_add
      ((intervalIntegrable_iff_integrableOn_Ioo_of_le zero_le_one).mpr hleft.2.1)
      ((intervalIntegrable_iff_integrableOn_Ioo_of_le zero_le_one).mpr hright.2.1)]
    apply intervalIntegral.integral_congr
    intro x _
    by_cases hx : x < c <;> simp [hx]
  have hMchoice : 0 < probeMass K rL ∨ 0 < probeMass K (r - rL) := by
    have hmass : probeMass K r = 1 := h.2.2.2.2.2.1
    by_contra hn
    push Not at hn
    linarith
  have hrL : ContinuousOn rL (Ioo (0 : ℝ) 1) := continuous_left_cut hr hc hrc
  have hpL : ContinuousOn pL (Ioo (0 : ℝ) 1) := continuous_left_cut hp hc hpc
  have hcontradiction (u v w : ℝ → ℝ)
      (hu : ContinuousOn u (Ioo (0 : ℝ) 1))
      (hv : ContinuousOn v (Ioo (0 : ℝ) 1))
      (huA : weakMeridionalAction K u v w = 0)
      (hn : IsRecoverableAreaCompetitor C K (normalizedProbe K u)
        (fun x => (1 / Real.sqrt (probeMass K u)) * v x)
        (fun x => (1 / Real.sqrt (probeMass K u)) * w x))
      (a b : ℝ) (hab : a < b) (hsub : Ioo a b ⊆ Ioo (0 : ℝ) 1)
      (hz : ∀ x ∈ Ioo a b, u x = 0) : False := by
    let β := 1 / Real.sqrt (probeMass K u)
    have hNA : weakMeridionalAction K (normalizedProbe K u)
        (fun x => β * v x) (fun x => β * w x) = 0 := by
      change weakMeridionalAction K (fun x => β * u x)
        (fun x => β * v x) (fun x => β * w x) = 0
      simpa only [huA, mul_zero] using
        weakMeridionalAction_const_mul K u v w β
    have hNmin : ∀ K' r' p' z', IsRecoverableAreaCompetitor C K' r' p' z' →
        weakMeridionalAction K (normalizedProbe K u)
          (fun x => β * v x) (fun x => β * w x) ≤ weakMeridionalAction K' r' p' z' := by
      intro K' r' p' z' h'
      rw [hNA]
      simpa only [hzero] using hmin K' r' p' z' h'
    apply minimum_not_zero_on_interval hC hn
      (continuousOn_const.mul hu) (continuousOn_const.mul hv) hNmin hab hsub
    intro x hx
    simp only [normalizedProbe, hz x hx, mul_zero]
  rcases hMchoice with hm | hm
  · apply hcontradiction rL pL zL hrL hpL hAL0 (hleft.2.2.2.2 hm) c 1
      hc.2 (fun x hx => ⟨hc.1.trans hx.1, hx.2⟩)
    intro x hx
    simp only [rL, ite_eq_right (not_lt.mpr hx.1.le)]
  · apply hcontradiction (r - rL) (p - pL) (z - zL)
      (hr.sub hrL) (hp.sub hpL) hAR0 (hright.2.2.2.2 hm) 0 c hc.1
      (fun x hx => ⟨hx.1, hx.2.trans hc.2⟩)
    intro x hx
    simp only [rL, Pi.sub_apply, ite_eq_left hx.2, sub_self]

end RicciFlowSharpEstimate.Geometry.AreaProfile
