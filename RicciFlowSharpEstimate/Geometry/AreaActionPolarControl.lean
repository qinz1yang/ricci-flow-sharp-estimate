/-
Copyright (c) 2026 Ziyang Qin. All rights reserved.
No license is granted by this file.
Authors: Ziyang Qin
-/
import RicciFlowSharpEstimate.Geometry.AreaActionCoercivity
import RicciFlowSharpEstimate.Geometry.AreaProbeRegularity
import RicciFlowSharpEstimate.Analysis.ParabolicPolarControl

/-!
# Direct polar control of the complete action remainder

Weighted derivative bounds and a tent-flux inequality control unweighted probe
mass at both poles. A parameterized square bound then controls the absolute
value of every term left after subtracting the positive operator square.
-/

noncomputable section

namespace RicciFlowSharpEstimate.Geometry.AreaProfile

open Set MeasureTheory
open scoped ContDiff

/-- The exact full density minus its nonnegative operator-square term. -/
def meridionalActionRemainder (K r : ℝ → ℝ) (x : ℝ) : ℝ :=
  meridionalActionDensity (warp K x) (warpSlope K x) (K x)
    (r x) (deriv r x) (deriv (deriv r) x) -
      warp K x * meridionalOperator K r x ^ 2

private theorem remainder_eq (K r : ℝ → ℝ) (x : ℝ) :
    meridionalActionRemainder K r x =
      -(K x * warpSlope K x * warp K x * r x * deriv r x) -
        K x * warpSlope K x ^ 2 * r x ^ 2 / 2 + K x ^ 2 * warp K x * r x ^ 2 := by
  unfold meridionalActionRemainder meridionalActionDensity meridionalOperator
  ring

/-- The remainder is continuous already for C¹ probes. -/
theorem meridionalActionRemainder_continuous (K r : ℝ → ℝ)
    (hK : Continuous K) (hr : ContDiff ℝ 1 r) : Continuous (meridionalActionRemainder K r) := by
  have hf := warp_continuous K hK
  have hb := warpSlope_continuous K hK
  have hr0 := hr.continuous
  have hr1 := hr.continuous_deriv_one
  simp_rw [show meridionalActionRemainder K r = fun x =>
      -(K x * warpSlope K x * warp K x * r x * deriv r x) -
        K x * warpSlope K x ^ 2 * r x ^ 2 / 2 + K x ^ 2 * warp K x * r x ^ 2 by
    funext x; exact remainder_eq K r x]
  fun_prop

/-- The sum of the absolute complete-action remainders near the two poles. -/
def polarActionRemainder (K r : ℝ → ℝ) (δ : ℝ) : ℝ :=
  (∫ x in (0 : ℝ)..δ, |meridionalActionRemainder K r x|) +
    ∫ x in (1 - δ)..1, |meridionalActionRemainder K r x|

private theorem remainder_bound (f b k u v hi a : ℝ)
    (hf0 : 0 ≤ f) (hf1 : f ≤ 1) (hk0 : 0 ≤ k) (hkhi : k ≤ hi)
    (hb : |b| ≤ 2) (ha : 0 < a) :
    |-(k * b * f * u * v) - k * b ^ 2 * u ^ 2 / 2 + k ^ 2 * f * u ^ 2| ≤
      (hi / a + 2 * hi + hi ^ 2) * u ^ 2 + hi * a * f ^ 2 * v ^ 2 := by
  have hhi : 0 ≤ hi := hk0.trans hkhi
  have hb2 : b ^ 2 ≤ 4 := by rcases abs_le.mp hb with ⟨hl, hu⟩; nlinarith
  have hsq : k ^ 2 ≤ hi ^ 2 := by nlinarith [mul_nonneg (sub_nonneg.mpr hkhi) (add_nonneg hhi hk0)]
  have hpot : k ^ 2 * f * u ^ 2 ≤ hi ^ 2 * u ^ 2 := by
    have h := mul_le_mul_of_nonneg_left hf1 (sq_nonneg k)
    simp only [mul_one] at h
    have h' := mul_le_mul_of_nonneg_right (h.trans hsq) (sq_nonneg u)
    simpa only [mul_one] using h'
  have hpot0 : 0 ≤ k ^ 2 * f * u ^ 2 := by positivity
  have hbad : k * b ^ 2 * u ^ 2 / 2 ≤ 2 * hi * u ^ 2 := by
    have h := mul_le_mul_of_nonneg_left hb2 hk0
    have h' := mul_le_mul_of_nonneg_right h (sq_nonneg u)
    have h'' := mul_le_mul_of_nonneg_right hkhi (sq_nonneg u)
    nlinarith only [h', h'']
  have hbad0 : 0 ≤ k * b ^ 2 * u ^ 2 / 2 := by positivity
  have hcross : |k * b * f * u * v| ≤ hi / a * u ^ 2 + hi * a * f ^ 2 * v ^ 2 := by
    have hy : 2 * |f * u * v| ≤ u ^ 2 / a + a * f ^ 2 * v ^ 2 := by
      apply (mul_le_mul_iff_right₀ ha).mp
      have hs := sq_nonneg (|u| - a * |f * v|)
      simp only [sub_sq, sq_abs, mul_pow] at hs
      have hid : |f * u * v| = |u| * |f * v| := by rw [← abs_mul]; congr 1; ring
      rw [hid]
      field_simp
      nlinarith only [hs]
    have hbound : |k * b * f * u * v| ≤ hi * (2 * |f * u * v|) := by
      have hid : |k * b * f * u * v| = k * |b| * |f * u * v| := by
        rw [show k * b * f * u * v = k * b * (f * u * v) by ring]
        rw [abs_mul, abs_mul, abs_of_nonneg hk0]
      rw [hid]
      have hkb : k * |b| ≤ hi * 2 := mul_le_mul hkhi hb (abs_nonneg b) hhi
      nlinarith only [mul_le_mul_of_nonneg_right hkb (abs_nonneg (f * u * v))]
    calc
      |k * b * f * u * v| ≤ hi * (2 * |f * u * v|) := hbound
      _ ≤ hi * (u ^ 2 / a + a * f ^ 2 * v ^ 2) := mul_le_mul_of_nonneg_left hy hhi
      _ = hi / a * u ^ 2 + hi * a * f ^ 2 * v ^ 2 := by ring
  rcases abs_le.mp hcross with ⟨hcl, hcu⟩
  apply abs_le.mpr
  constructor <;> nlinarith only [hcl, hcu, hbad, hbad0, hpot, hpot0,
    mul_nonneg hhi (sq_nonneg u), mul_nonneg (sq_nonneg hi) (sq_nonneg u)]

/-- A parameterized estimate for every absolute lower-order density term near
both poles. The operator square is excluded explicitly, not silently dropped. -/
theorem polarActionRemainder_le (K r : ℝ → ℝ)
    (hK : Continuous K) (hr : ContDiff ℝ 1 r) (hi : ℝ)
    (hbox : ∀ x ∈ Icc (0 : ℝ) 1, 0 ≤ K x ∧ K x ≤ hi)
    (hzero : (∫ x in (0 : ℝ)..1, K x) = 2)
    (hone : (∫ x in (0 : ℝ)..1, x * K x) = 1)
    (a : ℝ) (ha : 0 < a) (δ : ℝ) (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1) :
    polarActionRemainder K r δ ≤
      (hi / a + 2 * hi + hi ^ 2) *
        ((∫ x in (0 : ℝ)..δ, r x ^ 2) + ∫ x in (1 - δ)..1, r x ^ 2) +
          2 * hi * a * probeGradientEnergy K r := by
  have hhi : 0 ≤ hi := (hbox 0 (by norm_num)).1.trans (hbox 0 (by norm_num)).2
  have hf := warp_continuous K hK
  have hr1 := hr.continuous_deriv_one
  have hR := (meridionalActionRemainder_continuous K r hK hr).abs
  have hG : Continuous (fun x => warp K x ^ 2 * deriv r x ^ 2) := by fun_prop
  have htail (u v : ℝ) (hu : 0 ≤ u) (huv : u ≤ v) (hv : v ≤ 1) :
      (∫ x in u..v, |meridionalActionRemainder K r x|) ≤
        (hi / a + 2 * hi + hi ^ 2) * (∫ x in u..v, r x ^ 2) +
          hi * a * probeGradientEnergy K r := by
    have hUi : IntervalIntegrable (fun x => (hi / a + 2 * hi + hi ^ 2) * r x ^ 2)
        volume u v := ((hr.continuous.pow 2).const_mul _).intervalIntegrable u v
    have hGi : IntervalIntegrable (fun x => (hi * a) * (warp K x ^ 2 * deriv r x ^ 2))
        volume u v := (hG.const_mul _).intervalIntegrable u v
    have hbound : (∫ x in u..v, |meridionalActionRemainder K r x|) ≤
        ∫ x in u..v, (hi / a + 2 * hi + hi ^ 2) * r x ^ 2 +
          (hi * a) * (warp K x ^ 2 * deriv r x ^ 2) := by
      apply intervalIntegral.integral_mono_on huv (hR.intervalIntegrable u v)
        ((((hr.continuous.pow 2).const_mul _).add (hG.const_mul _)).intervalIntegrable u v)
      intro x hx
      have hx01 : x ∈ Icc (0 : ℝ) 1 := ⟨hu.trans hx.1, hx.2.trans hv⟩
      have hw := warp_nonneg_le_two_mul_min K hK (fun y hy => (hbox y hy).1)
        hzero hone x hx01
      have hf1 : warp K x ≤ 1 := by
        have hl := min_le_left x (1 - x)
        have hr' := min_le_right x (1 - x)
        linarith only [hw.2, hl, hr']
      rw [remainder_eq]
      have h := remainder_bound (warp K x) (warpSlope K x) (K x) (r x) (deriv r x)
        hi a hw.1 hf1 (hbox x hx01).1 (hbox x hx01).2
        (abs_warpSlope_le_two K hK (fun y hy => (hbox y hy).1) hzero x hx01) ha
      simpa only [Pi.add_apply, Pi.mul_apply, Pi.pow_apply, mul_assoc] using h
    rw [intervalIntegral.integral_add hUi hGi,
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul] at hbound
    have hmono : (∫ x in u..v, warp K x ^ 2 * deriv r x ^ 2) ≤ probeGradientEnergy K r :=
      intervalIntegral.integral_mono_interval hu huv hv
        (Filter.Eventually.of_forall fun x => mul_nonneg (sq_nonneg _) (sq_nonneg _))
        (hG.intervalIntegrable 0 1)
    have hscaled := mul_le_mul_of_nonneg_left hmono (mul_nonneg hhi ha.le)
    linarith only [hbound, hscaled]
  have hl := htail 0 δ le_rfl hδ0 hδ1
  have hr' := htail (1 - δ) 1 (sub_nonneg.mpr hδ1) (sub_le_self 1 hδ0) le_rfl
  unfold polarActionRemainder
  nlinarith only [hl, hr']


/-- One bound controls the operator energy, unweighted square integral and both
weighted first-derivative energies for the entire normalized action sublevel. -/
theorem exists_uniform_probe_regularity_bound (lo hi : ℝ) (hlo : 0 < lo) (hhi : 0 ≤ hi)
    (B : ℝ) : ∃ M > (0 : ℝ), ∀ K r : ℝ → ℝ,
      Continuous K → ContDiff ℝ 2 r →
      (∀ x ∈ Icc (0 : ℝ) 1, lo ≤ K x ∧ K x ≤ hi) →
      (∫ x in (0 : ℝ)..1, K x) = 2 → (∫ x in (0 : ℝ)..1, x * K x) = 1 →
      probeMass K r = 1 → meridionalAction K r ≤ B →
      probeOperatorEnergy K r ≤ M ∧ (∫ x in (0 : ℝ)..1, r x ^ 2) ≤ M ∧
        probeGradientEnergy K r ≤ M ∧
          (∫ x in (0 : ℝ)..1, x * (1 - x) * deriv r x ^ 2) ≤ M := by
  let D := max B 0 + actionMassCorrection lo hi
  have hD : 0 ≤ D := add_nonneg (le_max_right B 0) (actionMassCorrection_nonneg lo hi hlo hhi)
  let H := ((10 * lo + 2) * (4 * D) + (5 * lo / 2 + 2 * hi ^ 2)) / lo ^ 3
  have hH : 0 ≤ H := by dsimp [H]; positivity
  refine ⟨1 + 4 * D + H, by positivity, ?_⟩
  intro K r hK hr hbox hzero hone hmass hA
  have henergies := probe_energies_le_of_unit_mass_action_le K r hK hr lo hi hlo
    hbox hzero hone hmass (max B 0) (hA.trans (le_max_left B 0))
  change probeOperatorEnergy K r ≤ 4 * D ∧ (∫ x in (0 : ℝ)..1, r x ^ 2) ≤ 4 * D at henergies
  have hgrad := probeGradientEnergy_interpolation K r hK hr
    (fun x hx => hlo.le.trans (hbox x hx).1) hzero hone 1 zero_le_one
  rw [hmass] at hgrad
  have hfirst := integral_parabolic_deriv_sq_le K r hK hr lo hi hlo hbox hzero hone
  rw [hmass, mul_one] at hfirst
  have hfirstBound : (∫ x in (0 : ℝ)..1, x * (1 - x) * deriv r x ^ 2) ≤ H := by
    apply (le_div_iff₀ (pow_pos hlo 3)).mpr
    have hscaled := mul_le_mul_of_nonneg_left henergies.1 (by positivity : 0 ≤ 10 * lo + 2)
    nlinarith only [hfirst, hscaled]
  exact ⟨by linarith [henergies.1], by linarith [henergies.2],
    by nlinarith [henergies.1], by linarith⟩

/-- One radius controls both unweighted polar probe mass and the absolute
complete-action remainder uniformly over the whole normalized sublevel. -/
theorem exists_uniform_polar_action_radius (lo hi : ℝ) (hlo : 0 < lo) (hhi : 0 ≤ hi)
    (B ε : ℝ) (hε : 0 < ε) :
    ∃ δ > (0 : ℝ), δ ≤ 1 ∧ ∀ K r : ℝ → ℝ,
      Continuous K → ContDiff ℝ 2 r →
      (∀ x ∈ Icc (0 : ℝ) 1, lo ≤ K x ∧ K x ≤ hi) →
      (∫ x in (0 : ℝ)..1, K x) = 2 → (∫ x in (0 : ℝ)..1, x * K x) = 1 →
      probeMass K r = 1 → meridionalAction K r ≤ B → ∀ s ∈ Icc (0 : ℝ) δ,
      ((∫ x in (0 : ℝ)..s, r x ^ 2) + ∫ x in (1 - s)..1, r x ^ 2) ≤ ε ∧
        polarActionRemainder K r s ≤ ε := by
  obtain ⟨M, hM, hbound⟩ := exists_uniform_probe_regularity_bound lo hi hlo hhi B
  let Q := (6 + 20 * hi + 6 * hi ^ 2) * M
  have hQ : 0 ≤ Q := by dsimp [Q]; positivity
  let t := min 1 (ε / (Q + 1))
  have ht : 0 < t := lt_min zero_lt_one (div_pos hε (by positivity))
  have ht1 : t ≤ 1 := min_le_left _ _
  have htQ : t * Q ≤ ε := by
    have hdiv : t ≤ ε / (Q + 1) := min_le_right _ _
    have h := (le_div_iff₀ (by positivity : 0 < Q + 1)).mp hdiv
    nlinarith only [h, ht.le]
  have ht2 : t ^ 2 ≤ 1 := by nlinarith only [ht.le, ht1, sq_nonneg (t - 1)]
  have ht4 : t ^ 4 ≤ t ^ 2 := by
    nlinarith only [mul_nonneg (sq_nonneg t) (sub_nonneg.mpr ht2)]
  refine ⟨t ^ 4, pow_pos ht 4, ht4.trans ht2, ?_⟩
  intro K r hK hr hbox hzero hone hmass hA s hs
  obtain ⟨hE, hU, hG, hH⟩ := hbound K r hK hr hbox hzero hone hmass hA
  have hs1 : s ≤ 1 := hs.2.trans (ht4.trans ht2)
  have hs2 : s ≤ t ^ 2 := hs.2.trans ht4
  have htail := Analysis.integral_polar_sq_le_parabolic_energy r (hr.of_le (by norm_num))
    hs.1 hs1 (sq_pos_of_pos ht) (by nlinarith only [hs.2] : s ≤ (t ^ 2) ^ 2)
  have htailBound : ((∫ x in (0 : ℝ)..s, r x ^ 2) + ∫ x in (1 - s)..1, r x ^ 2) ≤
      6 * t ^ 2 * M := by
    have hUscaled := mul_le_mul_of_nonneg_left hU
      (show 0 ≤ 2 * s from mul_nonneg (by norm_num) hs.1)
    have hUHscaled := mul_le_mul_of_nonneg_left (add_le_add hU hH) (by positivity : 0 ≤ 2 * t ^ 2)
    have hsM := mul_le_mul_of_nonneg_right hs2 hM.le
    nlinarith only [htail, hUscaled, hUHscaled, hsM]
  have htailSmall : ((∫ x in (0 : ℝ)..s, r x ^ 2) + ∫ x in (1 - s)..1, r x ^ 2) ≤ t * Q := by
    have htt : t ^ 2 ≤ t := by nlinarith only [mul_nonneg ht.le (sub_nonneg.mpr ht1)]
    have hscale := mul_le_mul_of_nonneg_right htt (by positivity : 0 ≤ 6 * M)
    have hcoeff : 6 * M ≤ Q := by
      dsimp [Q]
      nlinarith only [mul_nonneg hhi hM.le, mul_nonneg (sq_nonneg hi) hM.le]
    have hscale' := mul_le_mul_of_nonneg_left hcoeff ht.le
    nlinarith only [htailBound, hscale, hscale']
  have hrem := polarActionRemainder_le K r hK (hr.of_le (by norm_num)) hi
    (fun x hx => ⟨hlo.le.trans (hbox x hx).1, (hbox x hx).2⟩) hzero hone t ht s hs.1 hs1
  have hc : 0 ≤ hi / t + 2 * hi + hi ^ 2 := by positivity
  have hremBound : polarActionRemainder K r s ≤
      (hi / t + 2 * hi + hi ^ 2) * (6 * t ^ 2 * M) + 2 * hi * t * M := by
    have hscaled := mul_le_mul_of_nonneg_left htailBound hc
    have hscaled' := mul_le_mul_of_nonneg_left hG (by positivity : 0 ≤ 2 * hi * t)
    linarith only [hrem, hscaled, hscaled']
  have hid : (hi / t + 2 * hi + hi ^ 2) * (6 * t ^ 2 * M) + 2 * hi * t * M =
      t * M * (8 * hi + (12 * hi + 6 * hi ^ 2) * t) := by
    field_simp [ht.ne']
    ring
  rw [hid] at hremBound
  have hcoeff : 8 * hi + (12 * hi + 6 * hi ^ 2) * t ≤ 6 + 20 * hi + 6 * hi ^ 2 := by
    have h := mul_le_mul_of_nonneg_left ht1 (by positivity : 0 ≤ 12 * hi + 6 * hi ^ 2)
    nlinarith only [h]
  have hremSmall : polarActionRemainder K r s ≤ t * Q := by
    have hscaled := mul_le_mul_of_nonneg_left hcoeff (mul_nonneg ht.le hM.le)
    dsimp [Q]
    nlinarith only [hremBound, hscaled]
  exact ⟨htailSmall.trans htQ, hremSmall.trans htQ⟩

/-- The same direct polar control retains the original varying curvature boxes
and their actual ratio restriction; the radius precedes all competitors. -/
theorem exists_uniform_polar_action_radius_of_ratio (C : ℝ) (hC : 1 ≤ C)
    (B ε : ℝ) (hε : 0 < ε) :
    ∃ δ > (0 : ℝ), δ ≤ 1 ∧ ∀ K r : ℝ → ℝ,
      Continuous K → ContDiff ℝ 2 r → ∀ kappa Lambda : ℝ, 0 < kappa →
      (∀ x ∈ Icc (0 : ℝ) 1, kappa ≤ K x ∧ K x ≤ Lambda) → Lambda / kappa ≤ C →
      (∫ x in (0 : ℝ)..1, K x) = 2 → (∫ x in (0 : ℝ)..1, x * K x) = 1 →
      probeMass K r = 1 → meridionalAction K r ≤ B → ∀ s ∈ Icc (0 : ℝ) δ,
      ((∫ x in (0 : ℝ)..s, r x ^ 2) + ∫ x in (1 - s)..1, r x ^ 2) ≤ ε ∧
        polarActionRemainder K r s ≤ ε := by
  have hCpos : 0 < C := lt_of_lt_of_le zero_lt_one hC
  obtain ⟨δ, hδ, hδ1, hδall⟩ := exists_uniform_polar_action_radius (2 / C) (2 * C)
    (by positivity) (by positivity) B ε hε
  refine ⟨δ, hδ, hδ1, ?_⟩
  intro K r hK hr kappa Lambda hkappa hbox hratio hzero hone hmass hA
  exact hδall K r hK hr
    (curvature_bounds_of_ratio K hK kappa Lambda C hkappa hbox hratio hzero)
    hzero hone hmass hA

end RicciFlowSharpEstimate.Geometry.AreaProfile
