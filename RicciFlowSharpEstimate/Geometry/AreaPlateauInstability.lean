/-
Copyright (c) 2026 Ziyang Qin. All rights reserved.
No license is granted by this file.
Authors: Ziyang Qin
-/
import RicciFlowSharpEstimate.Analysis.PositiveSmoothBump
import RicciFlowSharpEstimate.Geometry.AreaAction

/-!
# Instability on a positive constant-curvature plateau

The complete area density has an exact quadratic expansion at the unit probe.
Its linear coefficient is a positive weighted pairing plus the derivative of
an explicit flux, whose boundary values vanish for an interior smooth bump.

Adapted from Ziyang Qin's historical constant-curvature plateau argument,
using the actual normalized warp, slope and probe derivatives throughout.
-/

noncomputable section

namespace RicciFlowSharpEstimate.Geometry.AreaProfile

open MeasureTheory Set
open scoped ContDiff Topology

/-- The coefficient of the linear variation of the complete density at the unit probe. -/
def constantProbeVariationDensity (f f1 K χ χ1 χ2 : ℝ) : ℝ :=
  -2 * K * f ^ 2 * χ2 - 5 * K * f * f1 * χ1 +
    (4 * K ^ 2 * f - K * f1 ^ 2) * χ

/-- The complete density is exactly quadratic along the affine probe variation. -/
theorem meridionalActionDensity_one_sub_mul (f f1 K χ χ1 χ2 ε : ℝ) :
    meridionalActionDensity f f1 K (1 - ε * χ) (-ε * χ1) (-ε * χ2) =
      meridionalActionDensity f f1 K 1 0 0 -
        ε * constantProbeVariationDensity f f1 K χ χ1 χ2 +
        ε ^ 2 * meridionalActionDensity f f1 K χ χ1 χ2 := by
  unfold meridionalActionDensity constantProbeVariationDensity
  ring

/-- The explicit flux built from the actual curvature primitives and bump derivative. -/
def plateauFlux (K : ℝ → ℝ) (κ : ℝ) (χ : ℝ → ℝ) (x : ℝ) : ℝ :=
  -2 * κ * warp K x ^ 2 * deriv χ x - κ * warp K x * warpSlope K x * χ x

private theorem jet_eq_zero_of_notMem_tsupport (χ : ℝ → ℝ) {x : ℝ}
    (hx : x ∉ tsupport χ) :
    χ x = 0 ∧ deriv χ x = 0 ∧ deriv (deriv χ) x = 0 := by
  refine ⟨(notMem_tsupport_iff_eventuallyEq.mp hx).eq_of_nhds,
    deriv_of_notMem_tsupport hx, ?_⟩
  exact deriv_of_notMem_tsupport (fun h => hx (tsupport_deriv_subset h))

/-- On a supported plateau variation, the actual flux derivative removes precisely
all terms except the positive curvature-squared pairing. -/
theorem plateauFlux_hasDerivAt (K χ : ℝ → ℝ) (hK : Continuous K)
    (hχ : ContDiff ℝ ∞ χ) (κ l u : ℝ)
    (hSupp : tsupport χ ⊆ Ioo l u) (hPlateau : ∀ x ∈ Ioo l u, K x = κ)
    (x : ℝ) :
    HasDerivAt (plateauFlux K κ χ)
      (constantProbeVariationDensity (warp K x) (warpSlope K x) (K x)
        (χ x) (deriv χ x) (deriv (deriv χ) x) - 2 * κ ^ 2 * warp K x * χ x) x := by
  have hχ1 : ContDiff ℝ ∞ (deriv χ) := (contDiff_infty_iff_deriv.mp hχ).2
  have hdχ := (hχ.differentiable (by simp) x).hasDerivAt
  have hdχ1 := (hχ1.differentiable (by simp) x).hasDerivAt
  have hf := warp_hasDerivAt K hK x
  have hf1 := warpSlope_hasDerivAt K hK x
  have hF := (((hf.pow 2).mul hdχ1).const_mul (-2 * κ)).sub
    (((hf.mul hf1).mul hdχ).const_mul κ)
  convert hF using 1
  · ext y
    simp only [plateauFlux, Pi.mul_apply, Pi.pow_apply, Pi.sub_apply]
    ring
  · simp only [Pi.mul_apply, Pi.pow_apply]
    by_cases hx : x ∈ tsupport χ
    · rw [hPlateau x (hSupp hx)]
      unfold constantProbeVariationDensity
      ring
    · obtain ⟨h0, h1, h2⟩ := jet_eq_zero_of_notMem_tsupport χ hx
      simp [constantProbeVariationDensity, h0, h1, h2]

/-- The supported plateau flux vanishes at both physical endpoints. -/
theorem plateauFlux_endpoints (K χ : ℝ → ℝ) (κ l u : ℝ)
    (hl : 0 < l) (hu : u < 1) (hSupp : tsupport χ ⊆ Ioo l u) :
    plateauFlux K κ χ 0 = 0 ∧ plateauFlux K κ χ 1 = 0 := by
  have hn0 : (0 : ℝ) ∉ tsupport χ := fun h => (not_lt_of_ge hl.le) (hSupp h).1
  have hn1 : (1 : ℝ) ∉ tsupport χ := fun h => (not_lt_of_ge hu.le) (hSupp h).2
  obtain ⟨h00, h01, _⟩ := jet_eq_zero_of_notMem_tsupport χ hn0
  obtain ⟨h10, h11, _⟩ := jet_eq_zero_of_notMem_tsupport χ hn1
  simp [plateauFlux, h00, h01, h10, h11]

/-- The complete first variation at the unit probe equals the weighted plateau pairing. -/
theorem constantProbeVariation_integral_eq_plateau_pairing
    (K χ : ℝ → ℝ) (hK : Continuous K) (hχ : ContDiff ℝ ∞ χ)
    (κ l u : ℝ) (hl : 0 < l) (hu : u < 1)
    (hSupp : tsupport χ ⊆ Ioo l u) (hPlateau : ∀ x ∈ Ioo l u, K x = κ) :
    (∫ x in (0 : ℝ)..1, constantProbeVariationDensity (warp K x) (warpSlope K x)
      (K x) (χ x) (deriv χ x) (deriv (deriv χ) x)) =
      2 * κ ^ 2 * ∫ x in (0 : ℝ)..1, warp K x * χ x := by
  have hf := warp_continuous K hK
  have hf1 := warpSlope_continuous K hK
  have hχ1 := hχ.continuous_deriv (by simp)
  have hχ2 := (contDiff_infty_iff_deriv.mp hχ).2.continuous_deriv (by simp)
  have hV : Continuous (fun x => constantProbeVariationDensity (warp K x) (warpSlope K x)
      (K x) (χ x) (deriv χ x) (deriv (deriv χ) x)) := by
    unfold constantProbeVariationDensity
    fun_prop
  have hq : Continuous (fun x => 2 * κ ^ 2 * warp K x * χ x) := by fun_prop
  have hInt := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun x _ => plateauFlux_hasDerivAt K χ hK hχ κ l u hSupp hPlateau x)
    ((hV.sub hq).intervalIntegrable 0 1)
  rw [intervalIntegral.integral_sub (hV.intervalIntegrable 0 1)
    (hq.intervalIntegrable 0 1)] at hInt
  obtain ⟨h0, h1⟩ := plateauFlux_endpoints K χ κ l u hl hu hSupp
  rw [h0, h1] at hInt
  have hMul : (∫ x in (0 : ℝ)..1, 2 * κ ^ 2 * warp K x * χ x) =
      2 * κ ^ 2 * ∫ x in (0 : ℝ)..1, warp K x * χ x := by
    calc
      _ = ∫ x in (0 : ℝ)..1, (2 * κ ^ 2) * (warp K x * χ x) := by
        apply intervalIntegral.integral_congr
        intro x _
        ring
      _ = _ := intervalIntegral.integral_const_mul _ _
  rw [hMul] at hInt
  linarith

/-- The actual probe derivatives and full action satisfy an exact plateau variation law. -/
theorem meridionalAction_one_sub_mul_of_plateau
    (K χ : ℝ → ℝ) (hK : Continuous K) (hχ : ContDiff ℝ ∞ χ)
    (κ l u ε : ℝ) (hl : 0 < l) (hu : u < 1)
    (hSupp : tsupport χ ⊆ Ioo l u) (hPlateau : ∀ x ∈ Ioo l u, K x = κ) :
    deriv (fun x => 1 - ε * χ x) = (fun x => -ε * deriv χ x) ∧
    deriv (deriv (fun x => 1 - ε * χ x)) = (fun x => -ε * deriv (deriv χ) x) ∧
    meridionalAction K (fun x => 1 - ε * χ x) = meridionalAction K (fun _ => 1) -
      2 * ε * (κ ^ 2 * ∫ x in (0 : ℝ)..1, warp K x * χ x) +
      ε ^ 2 * meridionalAction K χ := by
  have hχ1 : ContDiff ℝ ∞ (deriv χ) := (contDiff_infty_iff_deriv.mp hχ).2
  have hr1 : deriv (fun x => 1 - ε * χ x) = fun x => -ε * deriv χ x := by
    funext x
    rw [deriv_const_sub, deriv_const_mul ε (hχ.differentiable (by simp) x)]
    ring
  have hr2 : deriv (deriv (fun x => 1 - ε * χ x)) =
      fun x => -ε * deriv (deriv χ) x := by
    rw [hr1]
    funext x
    exact deriv_const_mul (-ε) (hχ1.differentiable (by simp) x)
  refine ⟨hr1, hr2, ?_⟩
  have hf := warp_continuous K hK
  have hf1 := warpSlope_continuous K hK
  have hχ2 := (contDiff_infty_iff_deriv.mp hχ1).2.continuous
  have hc0 := meridionalAction_integrand_continuous K (fun _ => 1) hK contDiff_const
  simp only [deriv_const', deriv_const] at hc0
  have hcB := meridionalAction_integrand_continuous K χ hK hχ
  have hcV : Continuous (fun x => constantProbeVariationDensity (warp K x) (warpSlope K x)
      (K x) (χ x) (deriv χ x) (deriv (deriv χ) x)) := by
    unfold constantProbeVariationDensity
    fun_prop
  unfold meridionalAction
  rw [hr2, hr1]
  simp only [deriv_const', deriv_const]
  simp_rw [meridionalActionDensity_one_sub_mul]
  rw [intervalIntegral.integral_add
    ((hc0.intervalIntegrable 0 1).sub ((hcV.intervalIntegrable 0 1).const_mul ε))
    ((hcB.intervalIntegrable 0 1).const_mul (ε ^ 2)),
    intervalIntegral.integral_sub (hc0.intervalIntegrable 0 1)
      ((hcV.intervalIntegrable 0 1).const_mul ε),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    constantProbeVariation_integral_eq_plateau_pairing K χ hK hχ κ l u hl hu hSupp hPlateau]
  ring

private theorem explicit_quadratic_neg (A B : ℝ) (hA : 0 < A) :
    -2 * (A / (|B| + 1)) * A + (A / (|B| + 1)) ^ 2 * B < 0 := by
  let ε := A / (|B| + 1)
  have hden : 0 < |B| + 1 := by positivity
  have heps : 0 < ε := div_pos hA hden
  have hB : B ≤ |B| := le_abs_self B
  have hfrac : ε * |B| < A := by
    calc
      ε * |B| = A * |B| / (|B| + 1) := by dsimp [ε]; ring
      _ < A := (div_lt_iff₀ hden).mpr (by nlinarith)
  change -2 * ε * A + ε ^ 2 * B < 0
  nlinarith [sq_nonneg ε]

/-- A smooth bump on the plateau produces one fixed negative complete-action probe.
The coefficient, quadratic remainder, step size and actual probe jets are retained. -/
theorem exists_smooth_plateau_probe
    (K : ℝ → ℝ) (hK : Continuous K) (κ l u : ℝ)
    (hκ : 0 < κ) (hl : 0 < l) (hlu : l < u) (hu : u < 1)
    (hPlateau : ∀ x ∈ Ioo l u, K x = κ)
    (hfpos : ∀ x ∈ Ioo l u, 0 < warp K x)
    (hZero : meridionalAction K (fun _ => 1) = 0) :
    ∃ χ : ℝ → ℝ,
      ContDiff ℝ ∞ χ ∧ HasCompactSupport χ ∧ tsupport χ ⊆ Ioo l u ∧
      (∀ x, χ x ∈ Icc (0 : ℝ) 1) ∧
      0 < ∫ x in (0 : ℝ)..1, warp K x * χ x ∧
      let A := κ ^ 2 * ∫ x in (0 : ℝ)..1, warp K x * χ x
      let B := meridionalAction K χ
      let ε := A / (|B| + 1)
      let r := fun x => 1 - ε * χ x
      0 < A ∧ 0 < ε ∧ ContDiff ℝ ∞ r ∧
      deriv r = (fun x => -ε * deriv χ x) ∧
      deriv (deriv r) = (fun x => -ε * deriv (deriv χ) x) ∧
      r 0 = 1 ∧ deriv r 0 = 0 ∧
      r =ᶠ[𝓝 0] (fun _ => 1) ∧ r =ᶠ[𝓝 1] (fun _ => 1) ∧
      (∃ x ∈ Ioo (0 : ℝ) 1, r x ≠ 1) ∧
      meridionalAction K r = -2 * ε * A + ε ^ 2 * B ∧ meridionalAction K r < 0 := by
  obtain ⟨χ, hχ, hCompact, hSupp, hBox, hPair⟩ :=
    Analysis.exists_contDiff_nonneg_tsupport_subset_integral_mul_pos
      (warp K) 0 1 l u (warp_continuous K hK).continuousOn hl.le hlu hu.le hfpos
  refine ⟨χ, hχ, hCompact, hSupp, hBox, hPair, ?_⟩
  let A := κ ^ 2 * ∫ x in (0 : ℝ)..1, warp K x * χ x
  let B := meridionalAction K χ
  let ε := A / (|B| + 1)
  let r := fun x => 1 - ε * χ x
  have hA : 0 < A := mul_pos (sq_pos_of_pos hκ) hPair
  have heps : 0 < ε := div_pos hA (by positivity)
  have hr : ContDiff ℝ ∞ r := contDiff_const.sub (contDiff_const.mul hχ)
  obtain ⟨hr1, hr2, hAction⟩ :=
    meridionalAction_one_sub_mul_of_plateau K χ hK hχ κ l u ε hl hu hSupp hPlateau
  have hn0 : (0 : ℝ) ∉ tsupport χ := fun h => (not_lt_of_ge hl.le) (hSupp h).1
  have hn1 : (1 : ℝ) ∉ tsupport χ := fun h => (not_lt_of_ge hu.le) (hSupp h).2
  obtain ⟨hχ0, hχd0, _⟩ := jet_eq_zero_of_notMem_tsupport χ hn0
  have hr0 : r =ᶠ[𝓝 0] (fun _ => 1) := by
    filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hn0] with x hx
    simp [r, hx]
  have hrone : r =ᶠ[𝓝 1] (fun _ => 1) := by
    filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hn1] with x hx
    simp [r, hx]
  have hχnz : ∃ x, χ x ≠ 0 := by
    by_contra h
    push Not at h
    have hz : χ = 0 := funext h
    simp [hz] at hPair
  have hrnz : ∃ x ∈ Ioo (0 : ℝ) 1, r x ≠ 1 := by
    obtain ⟨x, hx⟩ := hχnz
    have hxs := hSupp (subset_tsupport χ (Function.mem_support.mpr hx))
    refine ⟨x, ⟨hl.trans hxs.1, hxs.2.trans hu⟩, ?_⟩
    dsimp [r]
    intro heq
    have : ε * χ x = 0 := by linarith
    rcases mul_eq_zero.mp this with hε | hχx
    · exact (ne_of_gt heps) hε
    · exact hx hχx
  have hAction' : meridionalAction K r = -2 * ε * A + ε ^ 2 * B := by
    rw [hZero, zero_sub] at hAction
    simpa only [A, B, r, neg_mul] using hAction
  refine ⟨hA, heps, hr, hr1, hr2, ?_, ?_, hr0, hrone, hrnz, hAction', ?_⟩
  · simp [hχ0]
  · simpa only [hχd0, mul_zero] using congrFun hr1 0
  · rw [hAction']
    exact explicit_quadratic_neg A B hA

/-- A zero-action unit probe is unstable on every positive constant-curvature
interior plateau. The same smooth probe equals one near both physical endpoints. -/
theorem exists_smooth_probe_action_neg_of_constant_curvature_plateau
    (K : ℝ → ℝ) (hK : Continuous K) (κ l u : ℝ)
    (hκ : 0 < κ) (hl : 0 < l) (hlu : l < u) (hu : u < 1)
    (hPlateau : ∀ x ∈ Ioo l u, K x = κ)
    (hfpos : ∀ x ∈ Ioo l u, 0 < warp K x)
    (hZero : meridionalAction K (fun _ => 1) = 0) :
    ∃ r : ℝ → ℝ, ContDiff ℝ ∞ r ∧ r 0 = 1 ∧ deriv r 0 = 0 ∧
      r =ᶠ[𝓝 0] (fun _ => 1) ∧ r =ᶠ[𝓝 1] (fun _ => 1) ∧
      (∃ x ∈ Ioo (0 : ℝ) 1, r x ≠ 1) ∧ meridionalAction K r < 0 := by
  obtain ⟨χ, _, _, _, _, _, _, _, hr, _, _, hr0, hrd0, hn0, hn1, hnz, _, hneg⟩ :=
    exists_smooth_plateau_probe K hK κ l u hκ hl hlu hu hPlateau hfpos hZero
  exact ⟨_, hr, hr0, hrd0, hn0, hn1, hnz, hneg⟩

end RicciFlowSharpEstimate.Geometry.AreaProfile
