/-
Copyright (c) 2026 Ziyang Qin. All rights reserved.
No license is granted by this file.
Authors: Ziyang Qin
-/
import RicciFlowSharpEstimate.Analysis.WeightedGreenRegularity
import RicciFlowSharpEstimate.Geometry.WeakProbeFirstOrderSystem

/-!
# A regular curvature representative at the actual weak minimum

The complete curvature adjoint and genuine box complementarity express the
curvature as a clipped continuous control wherever the actual probe is nonzero.
The weighted control remains absolutely continuous across every probe zero.
The representative equals the original curvature almost everywhere; no curvature
derivative, zero-set regularity, zero action, or operator sign is assumed.
-/

noncomputable section
namespace RicciFlowSharpEstimate.Geometry.AreaProfile
open Set MeasureTheory Filter Topology
open scoped ContDiff
local notation "areaμ" => volume.restrict (Ioo (0 : ℝ) 1)

private theorem control_interval_subset {a b : ℝ}
    (ha : a ∈ Ioo (0 : ℝ) 1) (hb : b ∈ Ioo (0 : ℝ) 1) :
    uIcc a b ⊆ Ioo (0 : ℝ) 1 := by
  intro x hx
  rcases mem_uIcc.mp hx with hx | hx
  · exact ⟨ha.1.trans_le hx.1, hx.2.trans_lt hb.2⟩
  · exact ⟨hb.1.trans_le hx.1, hx.2.trans_lt ha.2⟩

private theorem control_ac_const (v a b : ℝ) :
    AbsolutelyContinuousOnInterval (fun _ : ℝ => v) a b :=
  (contDiff_const : ContDiff ℝ 1 (fun _ : ℝ => v)).contDiffOn.absolutelyContinuousOnInterval

private theorem control_ac_abs {f : ℝ → ℝ} {a b : ℝ}
    (hf : AbsolutelyContinuousOnInterval f a b) :
    AbsolutelyContinuousOnInterval (fun x => |f x|) a b := by
  have hLip : LipschitzWith 1 (fun x : ℝ => |x|) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    simp only [Real.dist_eq, NNReal.coe_one, one_mul]
    have hx := abs_add_le (x - y) y
    have hy := abs_add_le (y - x) x
    simp only [sub_add_cancel] at hx hy
    rw [abs_sub_comm y x] at hy
    apply abs_le.mpr
    constructor <;> linarith
  simpa only [Function.comp_def] using hLip.comp_absolutelyContinuousOnInterval hf

private theorem control_ac_max {f g : ℝ → ℝ} {a b : ℝ}
    (hf : AbsolutelyContinuousOnInterval f a b)
    (hg : AbsolutelyContinuousOnInterval g a b) :
    AbsolutelyContinuousOnInterval (fun x => max (f x) (g x)) a b := by
  have hh := ((hf.fun_add hg).fun_add (control_ac_abs (hf.fun_sub hg))).const_mul
    (1 / 2 : ℝ)
  apply hh.congr
  intro x _
  change (1 / 2 : ℝ) * (f x + g x + |f x - g x|) = max (f x) (g x)
  by_cases hx : f x ≤ g x
  · rw [max_eq_right hx, abs_of_nonpos (sub_nonpos.mpr hx)]
    ring
  · have hx' := (lt_of_not_ge hx).le
    rw [max_eq_left hx', abs_of_nonneg (sub_nonneg.mpr hx')]
    ring

private theorem control_ac_min {f g : ℝ → ℝ} {a b : ℝ}
    (hf : AbsolutelyContinuousOnInterval f a b)
    (hg : AbsolutelyContinuousOnInterval g a b) :
    AbsolutelyContinuousOnInterval (fun x => min (f x) (g x)) a b := by
  have hh := ((hf.fun_add hg).fun_sub (control_ac_abs (hf.fun_sub hg))).const_mul
    (1 / 2 : ℝ)
  apply hh.congr
  intro x _
  change (1 / 2 : ℝ) * (f x + g x - |f x - g x|) = min (f x) (g x)
  by_cases hx : f x ≤ g x
  · rw [min_eq_left hx, abs_of_nonpos (sub_nonpos.mpr hx)]
    ring
  · have hx' := (lt_of_not_ge hx).le
    rw [min_eq_right hx', abs_of_nonneg (sub_nonneg.mpr hx')]
    ring

private theorem control_continuousOn_of_local_ac (F : ℝ → ℝ)
    (hF : ∀ a ∈ Ioo (0 : ℝ) 1, ∀ b ∈ Ioo (0 : ℝ) 1,
      AbsolutelyContinuousOnInterval F a b) :
    ContinuousOn F (Ioo (0 : ℝ) 1) := by
  intro x hx
  let a := x / 2
  let b := (x + 1) / 2
  have ha : a ∈ Ioo (0 : ℝ) 1 := by
    dsimp [a]
    constructor <;> linarith [hx.1, hx.2]
  have hb : b ∈ Ioo (0 : ℝ) 1 := by
    dsimp [b]
    constructor <;> linarith [hx.1, hx.2]
  have hax : a < x := by dsimp [a]; linarith only [hx.1]
  have hxb : x < b := by dsimp [b]; linarith only [hx.2]
  have hn : uIcc a b ∈ 𝓝 x := by
    rw [uIcc_of_le (hax.trans hxb).le]
    exact Icc_mem_nhds hax hxb
  exact ((hF a ha b hb).continuousOn.continuousAt hn).continuousWithinAt

private theorem control_clamp_of_sign (lo hi k c H : ℝ)
    (hlohi : lo < hi) (hc : 0 < c) (hbox : lo ≤ k ∧ k ≤ hi)
    (hsign : (lo < k → c * k + H ≤ 0) ∧ (k < hi → 0 ≤ c * k + H)) :
    max lo (min hi (-H / c)) = k := by
  by_cases hklo : k = lo
  · subst k
    have hz := hsign.2 hlohi
    have hu : -H / c ≤ lo := (div_le_iff₀ hc).mpr (by nlinarith only [hz])
    exact max_eq_left ((min_le_right _ _).trans hu)
  by_cases hkhi : k = hi
  · subst k
    have hz := hsign.1 hlohi
    have hu : hi ≤ -H / c := (le_div_iff₀ hc).mpr (by nlinarith only [hz])
    rw [min_eq_left hu, max_eq_right hlohi.le]
  have hlo : lo < k := lt_of_le_of_ne hbox.1 (Ne.symm hklo)
  have hhi : k < hi := lt_of_le_of_ne hbox.2 hkhi
  have hz : c * k + H = 0 := le_antisymm (hsign.1 hlo) (hsign.2 hhi)
  have hu : -H / c = k := (div_eq_iff hc.ne').mpr (by nlinarith only [hz])
  rw [hu, min_eq_right hbox.2, max_eq_right hbox.1]

/-- The actual weak minimum has an a.e. equal, everywhere boxed curvature
representative, continuous and locally absolutely continuous where its same
probe is nonzero. The actual weighted product Kc*f*r² is locally absolutely
continuous throughout the physical interior, including every probe zero. -/
theorem IsRecoverableAreaCompetitor.exists_regular_curvature_representative
    {C : ℝ} {K r p z : ℝ → ℝ} (hC : 1 < C)
    (h : IsRecoverableAreaCompetitor C K r p z)
    (hr : ContinuousOn r (Ioo (0 : ℝ) 1))
    (hp : ContinuousOn p (Ioo (0 : ℝ) 1))
    (hmin : ∀ K' r' p' z' : ℝ → ℝ, IsRecoverableAreaCompetitor C K' r' p' z' →
      weakMeridionalAction K r p z ≤ weakMeridionalAction K' r' p' z') :
    ∃ (κ Λ : ℝ) (Kc : ℝ → ℝ), 0 < κ ∧ κ < 2 ∧ 2 < Λ ∧ Λ / κ ≤ C ∧
      Kc =ᵐ[areaμ] K ∧
      (∀ x ∈ Ioo (0 : ℝ) 1, κ ≤ Kc x ∧ Kc x ≤ Λ) ∧
      ContinuousOn Kc {x | x ∈ Ioo (0 : ℝ) 1 ∧ r x ≠ 0} ∧
      (∀ a b : ℝ, uIcc a b ⊆ {x | x ∈ Ioo (0 : ℝ) 1 ∧ r x ≠ 0} →
        AbsolutelyContinuousOnInterval Kc a b) ∧
      (∀ a ∈ Ioo (0 : ℝ) 1, ∀ b ∈ Ioo (0 : ℝ) 1,
        AbsolutelyContinuousOnInterval (fun x => Kc x * warp K x * r x ^ 2) a b) := by
  classical
  let lam := weakMeridionalAction K r p z
  let q : ℝ → ℝ := fun x => weakProbeEulerMomentum K r p z lam x / warp K x ^ 2
  obtain ⟨_hrD, hrCD, _hqC, hqeq, hpqAC, _hsystem⟩ :=
    h.probe_first_order_system_of_minimum hC.le hr hp hmin
  change weakMeridionalOperator K r p z =ᵐ[areaμ] q at hqeq
  have hqAC (a : ℝ) (ha : a ∈ Ioo (0 : ℝ) 1)
      (b : ℝ) (hb : b ∈ Ioo (0 : ℝ) 1) :
      AbsolutelyContinuousOnInterval q a b := (hpqAC a ha b hb).2
  obtain ⟨κ, Λ, a0, a1, hκ, hκ2, h2Λ, hbox, hratio, hsign⟩ :=
    h.exists_curvature_moment_multipliers hC hmin
  have hκΛ : κ < Λ := hκ2.trans h2Λ
  have hg := h.geometry_bounds hC.le
  have hw := h.primitive_weak_derivatives hC.le
  have hfC := hg.1.mono Ioo_subset_Icc_self
  have hbC := hg.2.1.mono Ioo_subset_Icc_self
  have hfCD : ContDiffOn ℝ 1 (warp K) (Ioo (0 : ℝ) 1) :=
    hw.1.contDiffOn_one_of_continuousOn hfC hbC
  have hfpos (x : ℝ) (hx : x ∈ Ioo (0 : ℝ) 1) : 0 < warp K x := by
    have hCpos : 0 < C := zero_lt_one.trans hC
    exact (mul_pos (mul_pos (by positivity : (0 : ℝ) < 2 / C) hx.1)
      (sub_pos.mpr hx.2)).trans_le (hg.2.2.1 x ⟨hx.1.le, hx.2.le⟩).1
  let A : ℝ → ℝ := fun x => weakCurvatureWarpCoefficient K r p z x - lam * r x ^ 2
  let B : ℝ → ℝ := weakCurvatureSlopeCoefficient K r p z
  obtain ⟨hAm0, hAw0, hBi, _hDi⟩ := h.curvature_coefficients_integrable hC.le
  have hAm : AEStronglyMeasurable A areaμ :=
    hAm0.sub ((h.2.1.memLp.aestronglyMeasurable.pow 2).const_mul lam)
  have hweightm : AEStronglyMeasurable (fun x : ℝ => x * (1 - x)) areaμ :=
    (continuous_id.mul (continuous_const.sub continuous_id)).aestronglyMeasurable
  have hweightb : ∀ᵐ x ∂areaμ, ‖x * (1 - x)‖ ≤ (1 : ℝ) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hx.1.le (sub_nonneg.mpr hx.2.le))]
    nlinarith only [sq_nonneg (x - (1 / 2 : ℝ))]
  have hAw : Integrable (fun x => x * (1 - x) * A x) areaμ := by
    apply (hAw0.sub ((h.2.1.integrable_sq.bdd_mul hweightm hweightb).const_mul lam)).congr
    filter_upwards [] with x
    change x * (1 - x) * weakCurvatureWarpCoefficient K r p z x -
      lam * (x * (1 - x) * r x ^ 2) = x * (1 - x) * A x
    dsimp only [A]
    ring
  let G : ℝ → ℝ := fun x => ∫ s, Analysis.unitDirichletKernel s x * A s ∂areaμ
  let T : ℝ → ℝ := fun x => ∫ s, Analysis.unitDirichletSlopeKernel s x * B s ∂areaμ
  obtain ⟨_hGformula, _hGCD, _hJC, _hGD, hGAC, _hJD⟩ :=
    Analysis.weighted_dirichlet_adjoint_local_regularity A hAm hAw
  obtain ⟨_hTformula, hTAC, _hT0, _hT1, _hTD⟩ :=
    Analysis.slope_kernel_adjoint_absolutelyContinuous B hBi
  let c : ℝ → ℝ := fun x => 2 * warp K x * r x ^ 2
  let D0 : ℝ → ℝ := fun x =>
    -2 * warp K x * q x * r x - warpSlope K x * warp K x * r x * p x -
      (1 / 2 : ℝ) * warpSlope K x ^ 2 * r x ^ 2
  let H : ℝ → ℝ := fun x => D0 x + 2 * G x + 2 * T x - a0 - a1 * x
  have hcCD : ContDiffOn ℝ 1 c (Ioo (0 : ℝ) 1) :=
    (contDiffOn_const.mul hfCD).mul (hrCD.pow 2)
  have hcpos (x : ℝ) (hx : x ∈ Ioo (0 : ℝ) 1) (hrx : r x ≠ 0) : 0 < c x :=
    mul_pos (mul_pos (by norm_num) (hfpos x hx)) (sq_pos_of_ne_zero hrx)
  have hHAC (a : ℝ) (ha : a ∈ Ioo (0 : ℝ) 1)
      (b : ℝ) (hb : b ∈ Ioo (0 : ℝ) 1) :
      AbsolutelyContinuousOnInterval H a b := by
    have hsub := control_interval_subset ha hb
    have hfA := hw.1.absolutelyContinuousOnInterval hfC ha hb
    have hbA := hw.2.absolutelyContinuousOnInterval hbC ha hb
    have hrA := h.2.1.weakDeriv.absolutelyContinuousOnInterval hr ha hb
    have hpA := (hpqAC a ha b hb).1
    have hqA := hqAC a ha b hb
    have hr2A : AbsolutelyContinuousOnInterval (fun x => r x ^ 2) a b := by
      simpa only [pow_two] using hrA.fun_mul hrA
    have hb2A : AbsolutelyContinuousOnInterval (fun x => warpSlope K x ^ 2) a b := by
      simpa only [pow_two] using hbA.fun_mul hbA
    have hD0A : AbsolutelyContinuousOnInterval D0 a b :=
      ((((hfA.const_mul (-2)).fun_mul hqA).fun_mul hrA).fun_sub
        (((hbA.fun_mul hfA).fun_mul hrA).fun_mul hpA)).fun_sub
          ((hb2A.const_mul (1 / 2 : ℝ)).fun_mul hr2A)
    have hGA : AbsolutelyContinuousOnInterval G a b := (hGAC a ha b hb).1
    have hTA : AbsolutelyContinuousOnInterval T a b := hTAC.mono (by
      simpa only [uIcc_of_le zero_le_one] using hsub.trans Ioo_subset_Icc_self)
    have hId : AbsolutelyContinuousOnInterval (fun x : ℝ => x) a b :=
      (contDiff_id : ContDiff ℝ 1 (fun x : ℝ => x)).contDiffOn.absolutelyContinuousOnInterval
    exact (((hD0A.fun_add (hGA.const_mul 2)).fun_add (hTA.const_mul 2)).fun_sub
      (control_ac_const a0 a b)).fun_sub (hId.const_mul a1)
  have hHC : ContinuousOn H (Ioo (0 : ℝ) 1) :=
    control_continuousOn_of_local_ac H hHAC
  have hresidual : ∀ᵐ x ∂areaμ,
      weakCurvatureAdjoint K r p z lam x - a0 - a1 * x = c x * K x + H x := by
    filter_upwards [hqeq] with x hx
    dsimp only [weakCurvatureAdjoint, weakCurvatureCoefficient, c, H, D0, G, T, A, B]
    rw [hx]
    ring
  have hcontrol : ∀ᵐ x ∂areaμ,
      (κ < K x → c x * K x + H x ≤ 0) ∧
      (K x < Λ → 0 ≤ c x * K x + H x) := by
    filter_upwards [hsign, hresidual] with x hs hx
    rw [hx] at hs
    exact hs
  let Ω : Set ℝ := {x | x ∈ Ioo (0 : ℝ) 1 ∧ r x ≠ 0}
  let Kc : ℝ → ℝ := fun x =>
    if r x = 0 then max κ (min Λ (K x)) else max κ (min Λ (-H x / c x))
  have hclipbox (v : ℝ) : κ ≤ max κ (min Λ v) ∧ max κ (min Λ v) ≤ Λ :=
    ⟨le_max_left _ _, max_le hκΛ.le (min_le_left _ _)⟩
  have hKcbox (x : ℝ) : κ ≤ Kc x ∧ Kc x ≤ Λ := by
    by_cases hx : r x = 0
    · simpa only [Kc, ite_eq_left hx] using hclipbox (K x)
    · simpa only [Kc, ite_eq_right hx] using hclipbox (-H x / c x)
  have hKceq : Kc =ᵐ[areaμ] K := by
    filter_upwards [hbox, hcontrol, ae_restrict_mem measurableSet_Ioo] with x hx hs hxI
    by_cases hrx : r x = 0
    · simp only [Kc, ite_eq_left hrx]
      rw [min_eq_right hx.2, max_eq_right hx.1]
    · simp only [Kc, ite_eq_right hrx]
      exact control_clamp_of_sign κ Λ (K x) (c x) (H x)
        hκΛ (hcpos x hxI hrx) hx hs
  have hΩsub : Ω ⊆ Ioo (0 : ℝ) 1 := fun _ hx => hx.1
  have hquotC : ContinuousOn (fun x => -H x / c x) Ω :=
    (hHC.mono hΩsub).neg.div (hcCD.continuousOn.mono hΩsub)
      (fun x hx => (hcpos x hx.1 hx.2).ne')
  have hKcC : ContinuousOn Kc Ω := by
    have hclipC : ContinuousOn (fun x => max κ (min Λ (-H x / c x))) Ω :=
      continuousOn_const.sup (continuousOn_const.inf hquotC)
    apply hclipC.congr
    intro x hx
    simp only [Kc, ite_eq_right hx.2]
  have hKcAC (a b : ℝ) (hab : uIcc a b ⊆ Ω) :
      AbsolutelyContinuousOnInterval Kc a b := by
    have ha := hab (left_mem_uIcc : a ∈ uIcc a b)
    have hb := hab (right_mem_uIcc : b ∈ uIcc a b)
    have hiCD : ContDiffOn ℝ 1 (fun x => (c x)⁻¹) (uIcc a b) :=
      (hcCD.mono (hab.trans hΩsub)).inv (fun x hx => (hcpos x (hab hx).1 (hab hx).2).ne')
    have hquotA : AbsolutelyContinuousOnInterval (fun x => -H x / c x) a b := by
      simpa only [div_eq_mul_inv, Pi.neg_apply] using
        (hHAC a ha.1 b hb.1).neg.fun_mul hiCD.absolutelyContinuousOnInterval
    have hclipA := control_ac_max (control_ac_const κ a b)
      (control_ac_min (control_ac_const Λ a b) hquotA)
    apply hclipA.congr
    intro x hx
    simp only [Kc, ite_eq_right (hab hx).2]
  have hweighted (x : ℝ) (hx : x ∈ Ioo (0 : ℝ) 1) :
      c x * Kc x = max (c x * κ) (min (c x * Λ) (-H x)) := by
    by_cases hrx : r x = 0
    · have hc0 : c x = 0 := by dsimp only [c]; rw [hrx]; ring
      simp only [hc0, zero_mul]
      rw [max_eq_left (min_le_left (0 : ℝ) (-H x))]
    · have hcp := hcpos x hx hrx
      simp only [Kc, ite_eq_right hrx]
      rw [mul_max_of_nonneg _ _ hcp.le, mul_min_of_nonneg _ _ hcp.le]
      have hcancel : c x * (-H x / c x) = -H x := by field_simp [hcp.ne']
      rw [hcancel]
  refine ⟨κ, Λ, Kc, hκ, hκ2, h2Λ, hratio, hKceq, fun x _ => hKcbox x,
    hKcC, hKcAC, ?_⟩
  intro a ha b hb
  have hab := control_interval_subset ha hb
  have hcA := (hcCD.mono hab).absolutelyContinuousOnInterval
  have hclipA := control_ac_max (hcA.fun_mul (control_ac_const κ a b))
    (control_ac_min (hcA.fun_mul (control_ac_const Λ a b)) (hHAC a ha b hb).neg)
  apply (hclipA.const_mul (1 / 2 : ℝ)).congr
  intro x hx
  change (1 / 2 : ℝ) * max (c x * κ) (min (c x * Λ) (-H x)) =
    Kc x * warp K x * r x ^ 2
  rw [← hweighted x (hab hx)]
  dsimp only [c]
  ring

end RicciFlowSharpEstimate.Geometry.AreaProfile
