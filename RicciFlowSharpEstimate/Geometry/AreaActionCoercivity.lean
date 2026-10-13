/-
Copyright (c) 2026 Ziyang Qin. All rights reserved.
No license is granted by this file.
Authors: Ziyang Qin
-/
import RicciFlowSharpEstimate.Geometry.AreaProbeEnergy
import RicciFlowSharpEstimate.Geometry.AreaWarpBounds
import RicciFlowSharpEstimate.Geometry.AreaPolarMass

/-!
# Coercivity of the complete normalized area action

All lower-order terms are estimated in the original density. The correction
constant depends only on a positive curvature box, not on curvature derivatives.
-/

noncomputable section
namespace RicciFlowSharpEstimate.Geometry.AreaProfile
open Set MeasureTheory
open scoped ContDiff

private theorem actionDensity_lower_bound (f b k r p z hi : ℝ)
    (hf : 0 ≤ f) (hk : 0 ≤ k) (hki : k ≤ hi) (hb : b ^ 2 ≤ 4) :
    f * (f * z + 2 * b * p - k * r) ^ 2 - hi * f ^ 2 * p ^ 2 - 3 * hi * r ^ 2 ≤
      meridionalActionDensity f b k r p z := by
  have hcoef : 0 ≤ 3 * hi - 3 * k * b ^ 2 / 4 := by
    nlinarith [mul_le_mul_of_nonneg_left hb hk]
  have hsq := mul_nonneg (div_nonneg hk (by norm_num : (0 : ℝ) ≤ 4))
    (sq_nonneg (b * r - 2 * f * p))
  have hg := mul_nonneg (mul_nonneg (sub_nonneg.mpr hki) (sq_nonneg f)) (sq_nonneg p)
  have hu := mul_nonneg hcoef (sq_nonneg r)
  have ht := mul_nonneg (mul_nonneg (sq_nonneg k) hf) (sq_nonneg r)
  unfold meridionalActionDensity
  nlinarith [hsq, hg, hu, ht]

/-- Direct control of the negative and mixed terms in the COMPLETE action. -/
theorem probeOperatorEnergy_sub_le_action (K r : ℝ → ℝ)
    (hK : Continuous K) (hr : ContDiff ℝ 2 r) (hi : ℝ)
    (hbox : ∀ x ∈ Icc (0 : ℝ) 1, 0 ≤ K x ∧ K x ≤ hi)
    (hzero : (∫ x in (0 : ℝ)..1, K x) = 2)
    (hone : (∫ x in (0 : ℝ)..1, x * K x) = 1) :
    probeOperatorEnergy K r - hi * probeGradientEnergy K r -
      3 * hi * (∫ x in (0 : ℝ)..1, r x ^ 2) ≤ meridionalAction K r := by
  have hf := warp_continuous K hK
  have hb := warpSlope_continuous K hK
  have hr0 := hr.continuous
  have hr1 := hr.continuous_deriv (by norm_num)
  have hr2 := hr.deriv'.continuous_deriv_one
  have hL := meridionalOperator_continuous_of_contDiff_two K r hK hr
  have hE : Continuous (fun x => warp K x * meridionalOperator K r x ^ 2) := by fun_prop
  have hG : Continuous (fun x => warp K x ^ 2 * deriv r x ^ 2) := by fun_prop
  have hU := hr0.pow 2
  have hEG : IntervalIntegrable (fun x => warp K x * meridionalOperator K r x ^ 2 -
      hi * (warp K x ^ 2 * deriv r x ^ 2)) volume 0 1 :=
    (hE.sub (hG.const_mul hi)).intervalIntegrable 0 1
  have hD : Continuous (fun x => meridionalActionDensity (warp K x) (warpSlope K x)
      (K x) (r x) (deriv r x) (deriv (deriv r) x)) := by
    unfold meridionalActionDensity
    fun_prop
  have h := intervalIntegral.integral_mono_on zero_le_one
    (hEG.sub ((hU.intervalIntegrable 0 1).const_mul (3 * hi)))
    (hD.intervalIntegrable 0 1) (fun x hx => ?_)
  · rw [intervalIntegral.integral_sub hEG ((hU.intervalIntegrable 0 1).const_mul (3 * hi)),
      intervalIntegral.integral_sub (hE.intervalIntegrable 0 1)
        ((hG.intervalIntegrable 0 1).const_mul hi),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul] at h
    exact h
  · have hn := fun y hy => (hbox y hy).1
    have hwarp := (warp_nonneg_le_two_mul_min K hK hn hzero hone x hx).1
    have habs := abs_warpSlope_le_two K hK hn hzero x hx
    have hb2 : warpSlope K x ^ 2 ≤ 4 := by
      have hs := abs_le.mp habs
      nlinarith [sq_nonneg (warpSlope K x)]
    have hbound := actionDensity_lower_bound (warp K x) (warpSlope K x) (K x)
      (r x) (deriv r x) (deriv (deriv r) x) hi hwarp (hbox x hx).1 (hbox x hx).2 hb2
    simpa only [meridionalOperator, Pi.mul_apply, Pi.sub_apply, Pi.pow_apply, mul_assoc]
      using hbound

/-- The explicit mass correction obtained from the Hardy and Young absorptions. -/
def actionMassCorrection (lo hi : ℝ) : ℝ :=
  (hi * (1 + 12 / lo ^ 2)) ^ 2 / 2 + 36 * hi / lo + 3 / lo + 1 / lo ^ 4

/-- The correction is nonnegative on a positive curvature box. -/
theorem actionMassCorrection_nonneg (lo hi : ℝ) (hlo : 0 < lo) (hhi : 0 ≤ hi) :
    0 ≤ actionMassCorrection lo hi := by
  unfold actionMassCorrection
  positivity

/-- The complete action uniformly controls the operator square and unweighted
probe mass, after the explicit box-dependent mass correction. -/
theorem meridionalAction_coercive (K r : ℝ → ℝ)
    (hK : Continuous K) (hr : ContDiff ℝ 2 r) (lo hi : ℝ) (hlo : 0 < lo)
    (hbox : ∀ x ∈ Icc (0 : ℝ) 1, lo ≤ K x ∧ K x ≤ hi)
    (hzero : (∫ x in (0 : ℝ)..1, K x) = 2)
    (hone : (∫ x in (0 : ℝ)..1, x * K x) = 1) :
    (probeOperatorEnergy K r + (∫ x in (0 : ℝ)..1, r x ^ 2)) / 4 ≤
      meridionalAction K r + actionMassCorrection lo hi * probeMass K r := by
  have hhi : 0 < hi := hlo.trans_le ((hbox 0 (by norm_num)).1.trans (hbox 0 (by norm_num)).2)
  have hn : ∀ x ∈ Icc (0 : ℝ) 1, 0 ≤ K x := fun x hx => hlo.le.trans (hbox x hx).1
  have hA := probeOperatorEnergy_sub_le_action K r hK hr hi
    (fun x hx => ⟨hn x hx, (hbox x hx).2⟩) hzero hone
  have hHardy := integral_sq_le_probeMass_gradient K r hK (hr.of_le (by norm_num))
    lo hlo.le (fun x hx => (hbox x hx).1) hzero hone
  let d := hi * (1 + 12 / lo ^ 2)
  have hd : 0 < d := by dsimp [d]; positivity
  have hU : (∫ x in (0 : ℝ)..1, r x ^ 2) ≤
      (12 * lo * probeMass K r + 4 * probeGradientEnergy K r) / lo ^ 2 := by
    apply (le_div_iff₀ (sq_pos_of_pos hlo)).mpr
    nlinarith only [hHardy]
  have hUscaled := mul_le_mul_of_nonneg_left hU (by positivity : 0 ≤ 3 * hi)
  have hid : 3 * hi * ((12 * lo * probeMass K r + 4 * probeGradientEnergy K r) / lo ^ 2) =
      (d - hi) * probeGradientEnergy K r + (36 * hi / lo) * probeMass K r := by
    dsimp [d]
    field_simp [hlo.ne']
    ring
  rw [hid] at hUscaled
  have hlower : probeOperatorEnergy K r - d * probeGradientEnergy K r ≤
      meridionalAction K r + (36 * hi / lo) * probeMass K r := by
    linarith only [hA, hUscaled]
  have hG := probeGradientEnergy_interpolation K r hK hr hn hzero hone
    (1 / (2 * d)) (by positivity)
  have hGscaled := mul_le_mul_of_nonneg_left hG (sq_nonneg d)
  have hleft : d ^ 2 * (4 * (1 / (2 * d)) * probeGradientEnergy K r) =
      2 * d * probeGradientEnergy K r := by
    field_simp [hd.ne']
    ring
  have hright : d ^ 2 * (4 * (1 / (2 * d)) ^ 2 * probeOperatorEnergy K r + probeMass K r) =
      probeOperatorEnergy K r + d ^ 2 * probeMass K r := by
    field_simp [hd.ne']
    ring
  rw [hleft, hright] at hGscaled
  have hE : probeOperatorEnergy K r / 2 ≤ meridionalAction K r +
      (d ^ 2 / 2 + 36 * hi / lo) * probeMass K r := by
    nlinarith only [hlower, hGscaled]
  have hGrad := probeGradientEnergy_interpolation K r hK hr hn hzero hone
    (lo ^ 2 / 4) (by positivity)
  have hHardyScaled := mul_le_mul_of_nonneg_left hHardy (sq_nonneg lo)
  have hUraw : lo ^ 4 * (∫ x in (0 : ℝ)..1, r x ^ 2) ≤
      lo ^ 4 * probeOperatorEnergy K r + (12 * lo ^ 3 + 4) * probeMass K r := by
    nlinarith only [hGrad, hHardyScaled]
  have hUfinal : (∫ x in (0 : ℝ)..1, r x ^ 2) ≤
      probeOperatorEnergy K r + (12 / lo + 4 / lo ^ 4) * probeMass K r := by
    have hdiv : (∫ x in (0 : ℝ)..1, r x ^ 2) ≤
        (lo ^ 4 * probeOperatorEnergy K r + (12 * lo ^ 3 + 4) * probeMass K r) / lo ^ 4 := by
      apply (le_div_iff₀ (pow_pos hlo 4)).mpr
      nlinarith only [hUraw]
    have heq : (lo ^ 4 * probeOperatorEnergy K r + (12 * lo ^ 3 + 4) * probeMass K r) /
        lo ^ 4 = probeOperatorEnergy K r + (12 / lo + 4 / lo ^ 4) * probeMass K r := by
      field_simp [hlo.ne']
    rwa [heq] at hdiv
  unfold actionMassCorrection
  dsimp [d] at hE
  simp only [div_eq_mul_inv] at hE hUfinal ⊢
  nlinarith only [hE, hUfinal]

/-- Coercivity constants are chosen before every geometry and probe in the box. -/
theorem exists_uniform_action_coercivity (lo hi : ℝ) (hlo : 0 < lo) (hhi : 0 ≤ hi) :
    ∃ c > (0 : ℝ), ∃ C ≥ (0 : ℝ), ∀ K r : ℝ → ℝ,
      Continuous K → ContDiff ℝ 2 r →
      (∀ x ∈ Icc (0 : ℝ) 1, lo ≤ K x ∧ K x ≤ hi) →
      (∫ x in (0 : ℝ)..1, K x) = 2 → (∫ x in (0 : ℝ)..1, x * K x) = 1 →
      c * (probeOperatorEnergy K r + (∫ x in (0 : ℝ)..1, r x ^ 2)) ≤
        meridionalAction K r + C * probeMass K r := by
  refine ⟨1 / 4, by norm_num, actionMassCorrection lo hi,
    actionMassCorrection_nonneg lo hi hlo hhi, ?_⟩
  intro K r hK hr hbox hzero hone
  simpa only [div_eq_mul_inv, one_mul, mul_comm] using
    meridionalAction_coercive K r hK hr lo hi hlo hbox hzero hone

/-- Uniform control of both positive energies at unit physical probe mass,
allowing a negative complete action and retaining the required mass correction. -/
theorem probe_energies_le_of_unit_mass_action_le (K r : ℝ → ℝ)
    (hK : Continuous K) (hr : ContDiff ℝ 2 r) (lo hi : ℝ) (hlo : 0 < lo)
    (hbox : ∀ x ∈ Icc (0 : ℝ) 1, lo ≤ K x ∧ K x ≤ hi)
    (hzero : (∫ x in (0 : ℝ)..1, K x) = 2)
    (hone : (∫ x in (0 : ℝ)..1, x * K x) = 1)
    (hmass : probeMass K r = 1) (B : ℝ) (hA : meridionalAction K r ≤ B) :
    probeOperatorEnergy K r ≤ 4 * (B + actionMassCorrection lo hi) ∧
      (∫ x in (0 : ℝ)..1, r x ^ 2) ≤ 4 * (B + actionMassCorrection lo hi) := by
  have h := meridionalAction_coercive K r hK hr lo hi hlo hbox hzero hone
  rw [hmass, mul_one] at h
  have hE := probeOperatorEnergy_nonneg K r hK
    (fun x hx => hlo.le.trans (hbox x hx).1) hzero hone
  have hU : 0 ≤ ∫ x in (0 : ℝ)..1, r x ^ 2 :=
    intervalIntegral.integral_nonneg zero_le_one (fun x _ => sq_nonneg (r x))
  constructor <;> linarith

/-- A complete-action bound gives one explicit linear modulus for both polar
weighted masses of every unit-mass probe in the curvature box. -/
theorem polarProbeMass_le_of_unit_mass_action_le (K r : ℝ → ℝ)
    (hK : Continuous K) (hr : ContDiff ℝ 2 r) (lo hi : ℝ) (hlo : 0 < lo)
    (hbox : ∀ x ∈ Icc (0 : ℝ) 1, lo ≤ K x ∧ K x ≤ hi)
    (hzero : (∫ x in (0 : ℝ)..1, K x) = 2)
    (hone : (∫ x in (0 : ℝ)..1, x * K x) = 1)
    (hmass : probeMass K r = 1) (B : ℝ) (hA : meridionalAction K r ≤ B)
    (δ : ℝ) (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1) :
    polarProbeMass K r δ ≤ 16 * δ * (B + actionMassCorrection lo hi) := by
  have hU := (probe_energies_le_of_unit_mass_action_le K r hK hr lo hi hlo hbox
    hzero hone hmass B hA).2
  calc
    polarProbeMass K r δ ≤ 4 * δ * (∫ x in (0 : ℝ)..1, r x ^ 2) :=
      polarProbeMass_le_four_mul_radius K r hK hr.continuous
        (fun x hx => hlo.le.trans (hbox x hx).1) hzero hone δ hδ0 hδ1
    _ ≤ 4 * δ * (4 * (B + actionMassCorrection lo hi)) :=
      mul_le_mul_of_nonneg_left hU (mul_nonneg (by norm_num) hδ0)
    _ = 16 * δ * (B + actionMassCorrection lo hi) := by ring

/-- One polar radius works uniformly for all geometries and probes with the
same box, unit mass and bounded complete action. In particular it works for
both tails of every member of any such varying sequence. -/
theorem exists_uniform_polar_mass_radius (lo hi : ℝ) (hlo : 0 < lo) (hhi : 0 ≤ hi)
    (B : ℝ) (ε : ℝ) (hε : 0 < ε) :
    ∃ δ > (0 : ℝ), δ ≤ 1 ∧ ∀ K r : ℝ → ℝ,
      Continuous K → ContDiff ℝ 2 r →
      (∀ x ∈ Icc (0 : ℝ) 1, lo ≤ K x ∧ K x ≤ hi) →
      (∫ x in (0 : ℝ)..1, K x) = 2 → (∫ x in (0 : ℝ)..1, x * K x) = 1 →
      probeMass K r = 1 → meridionalAction K r ≤ B →
      ∀ t ∈ Icc (0 : ℝ) δ, polarProbeMass K r t ≤ ε := by
  let q := 16 * (max B 0 + actionMassCorrection lo hi)
  have hq : 0 ≤ q := by
    dsimp [q]
    exact mul_nonneg (by norm_num) (add_nonneg (le_max_right B 0)
      (actionMassCorrection_nonneg lo hi hlo hhi))
  have hden : 0 < q + 1 := by linarith
  refine ⟨min 1 (ε / (q + 1)), lt_min zero_lt_one (div_pos hε hden), min_le_left _ _, ?_⟩
  intro K r hK hr hbox hzero hone hmass hA t ht
  have htdiv : t ≤ ε / (q + 1) := ht.2.trans (min_le_right _ _)
  have hteps := (le_div_iff₀ hden).mp htdiv
  have hsmall : t * q ≤ ε := by nlinarith only [hteps, ht.1]
  calc
    polarProbeMass K r t ≤ 16 * t * (max B 0 + actionMassCorrection lo hi) :=
      polarProbeMass_le_of_unit_mass_action_le K r hK hr lo hi hlo hbox hzero hone
        hmass (max B 0) (hA.trans (le_max_left _ _)) t ht.1 (ht.2.trans (min_le_left _ _))
    _ = t * q := by dsimp [q]; ring
    _ ≤ ε := hsmall

/-- Uniform coercivity for the ORIGINAL curvature-ratio restriction. The same
normalized moments give the auxiliary common box without replacing that restriction. -/
theorem meridionalAction_coercive_of_curvature_ratio (K r : ℝ → ℝ)
    (hK : Continuous K) (hr : ContDiff ℝ 2 r) (kappa Lambda C : ℝ)
    (hkappa : 0 < kappa) (hC : 1 ≤ C)
    (hbox : ∀ x ∈ Icc (0 : ℝ) 1, kappa ≤ K x ∧ K x ≤ Lambda)
    (hratio : Lambda / kappa ≤ C)
    (hzero : (∫ x in (0 : ℝ)..1, K x) = 2)
    (hone : (∫ x in (0 : ℝ)..1, x * K x) = 1) :
    (probeOperatorEnergy K r + (∫ x in (0 : ℝ)..1, r x ^ 2)) / 4 ≤
      meridionalAction K r + actionMassCorrection (2 / C) (2 * C) * probeMass K r := by
  have hCpos : 0 < C := lt_of_lt_of_le zero_lt_one hC
  exact meridionalAction_coercive K r hK hr (2 / C) (2 * C) (by positivity)
    (curvature_bounds_of_ratio K hK kappa Lambda C hkappa hbox hratio hzero) hzero hone

/-- A single two-pole mass modulus for the entire original normalized ratio class,
including varying curvature boxes and probes. -/
theorem exists_uniform_polar_mass_radius_of_ratio (C : ℝ) (hC : 1 ≤ C)
    (B : ℝ) (ε : ℝ) (hε : 0 < ε) :
    ∃ δ > (0 : ℝ), δ ≤ 1 ∧ ∀ K r : ℝ → ℝ,
      Continuous K → ContDiff ℝ 2 r → ∀ kappa Lambda : ℝ, 0 < kappa →
      (∀ x ∈ Icc (0 : ℝ) 1, kappa ≤ K x ∧ K x ≤ Lambda) → Lambda / kappa ≤ C →
      (∫ x in (0 : ℝ)..1, K x) = 2 → (∫ x in (0 : ℝ)..1, x * K x) = 1 →
      probeMass K r = 1 → meridionalAction K r ≤ B →
      ∀ t ∈ Icc (0 : ℝ) δ, polarProbeMass K r t ≤ ε := by
  have hCpos : 0 < C := lt_of_lt_of_le zero_lt_one hC
  obtain ⟨δ, hδ, hδ1, hδall⟩ := exists_uniform_polar_mass_radius (2 / C) (2 * C)
    (by positivity) (by positivity) B ε hε
  refine ⟨δ, hδ, hδ1, ?_⟩
  intro K r hK hr kappa Lambda hkappa hbox hratio hzero hone hmass hA
  exact hδall K r hK hr
    (curvature_bounds_of_ratio K hK kappa Lambda C hkappa hbox hratio hzero)
    hzero hone hmass hA

end RicciFlowSharpEstimate.Geometry.AreaProfile
