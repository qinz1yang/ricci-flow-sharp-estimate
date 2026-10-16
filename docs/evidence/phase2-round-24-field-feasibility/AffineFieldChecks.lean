import RicciFlowSharpEstimate.Geometry.AreaWarpCalibration
import RicciFlowSharpEstimate.Geometry.SmoothAreaInfimum

noncomputable section
namespace RicciFlowSharpEstimate.Geometry.AreaProfile
open Set MeasureTheory
open scoped ContDiff

private def trialA (κ α f : ℝ) : ℝ := κ + α * κ ^ 2 * f
private def trialBeta (κ C c f : ℝ) : ℝ := C * κ - c * κ ^ 2 * f
private def trialDensity (K r : ℝ → ℝ) (κ C α c x : ℝ) : ℝ :=
  let f := warp K x
  let b := warpSlope K x
  let a := trialA κ α f
  let β := trialBeta κ C c f
  f * (meridionalOperator K r x + a * r x) ^ 2 +
    2 * a * f ^ 2 * deriv r x ^ 2 +
    f * ((β - K x) * b + 2 * f * (α * κ ^ 2 * b)) * r x * deriv r x +
    (f * (K x ^ 2 + (2 * a - β) * K x - a ^ 2) +
      (β - K x) * b ^ 2 / 2 + f * b / 2 * (-c * κ ^ 2 * b)) * r x ^ 2

private def trialFlux (K r : ℝ → ℝ) (κ C α c x : ℝ) : ℝ :=
  2 * trialA κ α (warp K x) * warp K x ^ 2 * r x * deriv r x +
    trialBeta κ C c (warp K x) / 2 * warp K x * warpSlope K x * r x ^ 2

private theorem trial_flux_hasDerivAt (K r : ℝ → ℝ)
    (hK : Continuous K) (hr : ContDiff ℝ 2 r) (κ C α c x : ℝ) :
    HasDerivAt (trialFlux K r κ C α c)
      (trialDensity K r κ C α c x -
        meridionalActionDensity (warp K x) (warpSlope K x) (K x)
          (r x) (deriv r x) (deriv (deriv r) x)) x := by
  have hf := warp_hasDerivAt K hK x
  have hb := warpSlope_hasDerivAt K hK x
  have hrd := (hr.differentiable (by norm_num) x).hasDerivAt
  have hrD : ContDiff ℝ 1 (deriv r) := hr.deriv'
  have hrdd := (hrD.differentiable (by norm_num) x).hasDerivAt
  have ha := (hf.const_mul (α * κ ^ 2)).const_add κ
  have hβ := (hasDerivAt_const x (C * κ)).sub (hf.const_mul (c * κ ^ 2))
  have h := (((((ha.const_mul 2).mul (hf.pow 2)).mul hrd).mul hrdd)).add
    (((((hβ.div_const 2).mul hf).mul hb).mul (hrd.pow 2)))
  convert h using 1
  · rfl
  · simp only [Pi.mul_apply, Pi.pow_apply, Pi.sub_apply]
    unfold trialDensity trialA trialBeta meridionalActionDensity meridionalOperator
    ring

private def coefficientJ (C u t k α c : ℝ) : ℝ :=
  u * (k ^ 2 + (2 * (1 + α * u) - (C - c * u)) * k - (1 + α * u) ^ 2) +
    (C - c * u - k) * t / 2 - c * u * t / 2

private theorem upper_branch_identity (C u : ℝ) :
    8 * (1 + u / 8) * coefficientJ C u (4 - 4 * C * u) C (1 / 8) ((2 * C - 1) / 4) -
      ((C - ((2 * C - 1) / 4) * u - C + 2 * (1 / 8) * u) ^ 2 *
        (4 - 4 * C * u)) =
      u ^ 2 * (19 * C ^ 2 - 6 * C - 3 +
        (C ^ 3 + C ^ 2 / 2 - 3 / 8) * u - u ^ 2 / 64) := by
  unfold coefficientJ
  ring

private def testK (x : ℝ) : ℝ := 50 / 17 - (480 / 17) * x ^ 2 * (1 - x) ^ 2
private def testR (x : ℝ) : ℝ := 1 - (25 / 289) * (x - 1 / 2) ^ 2
private def intK (x : ℝ) : ℝ :=
  (50 / 17) * x - (160 / 17) * x ^ 3 + (240 / 17) * x ^ 4 - (96 / 17) * x ^ 5
private def intXK (x : ℝ) : ℝ :=
  (25 / 17) * x ^ 2 - (120 / 17) * x ^ 4 + (192 / 17) * x ^ 5 - (80 / 17) * x ^ 6

private theorem testK_smooth : ContDiff ℝ ∞ testK := by unfold testK; fun_prop
private theorem testR_smooth : ContDiff ℝ ∞ testR := by unfold testR; fun_prop

private theorem intK_deriv (x : ℝ) : HasDerivAt intK (testK x) x := by
  have h := ((((hasDerivAt_id x).const_mul (50 / 17)).sub
    (((hasDerivAt_id x).pow 3).const_mul (160 / 17))).add
    (((hasDerivAt_id x).pow 4).const_mul (240 / 17))).sub
    (((hasDerivAt_id x).pow 5).const_mul (96 / 17))
  convert h using 1
  · rfl
  · simp only [id_eq]
    unfold testK
    ring

private theorem intXK_deriv (x : ℝ) : HasDerivAt intXK (x * testK x) x := by
  have h := (((((hasDerivAt_id x).pow 2).const_mul (25 / 17)).sub
    (((hasDerivAt_id x).pow 4).const_mul (120 / 17))).add
    (((hasDerivAt_id x).pow 5).const_mul (192 / 17))).sub
    (((hasDerivAt_id x).pow 6).const_mul (80 / 17))
  convert h using 1
  · rfl
  · simp only [id_eq]
    unfold testK
    ring

private theorem integralK (x : ℝ) : (∫ y in (0 : ℝ)..x, testK y) = intK x := by
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun y _ => intK_deriv y) (testK_smooth.continuous.intervalIntegrable 0 x)
  simpa [intK] using h

private theorem integralXK (x : ℝ) : (∫ y in (0 : ℝ)..x, y * testK y) = intXK x := by
  have hc : Continuous (fun y => y * testK y) := continuous_id.mul testK_smooth.continuous
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun y _ => intXK_deriv y) (hc.intervalIntegrable 0 x)
  simpa [intXK] using h

private theorem test_moments : (∫ x in (0 : ℝ)..1, testK x) = 2 ∧
    (∫ x in (0 : ℝ)..1, x * testK x) = 1 := by
  rw [integralK, integralXK]
  norm_num [intK, intXK]

private theorem test_box (x : ℝ) (hx : x ∈ Icc (0 : ℝ) 1) :
    (20 / 17 : ℝ) ≤ testK x ∧ testK x ≤ 50 / 17 := by
  have hs0 : 0 ≤ x * (1 - x) := mul_nonneg hx.1 (sub_nonneg.mpr hx.2)
  have hs1 : x * (1 - x) ≤ (1 / 4 : ℝ) := by nlinarith [sq_nonneg (x - 1 / 2)]
  have hs2 : (x * (1 - x)) ^ 2 ≤ (1 / 16 : ℝ) := by
    nlinarith [mul_nonneg hs0 (sub_nonneg.mpr hs1)]
  unfold testK
  constructor <;> nlinarith [sq_nonneg (x * (1 - x))]

private theorem test_slope : warpSlope testK (1 / 2) = 0 := by
  rw [warpSlope, integralK]
  norm_num [intK]

private theorem test_warp : warp testK (1 / 2) = 7 / 17 := by
  rw [warp, Analysis.SecondPrimitive.integral_kernel_eq testK testK_smooth.continuous 0 (1 / 2),
    integralK, integralXK]
  norm_num [intK, intXK]

private theorem testR_deriv (x : ℝ) : HasDerivAt testR (-(50 / 289) * (x - 1 / 2)) x := by
  have h := (hasDerivAt_const x (1 : ℝ)).sub
    ((((hasDerivAt_id x).sub_const (1 / 2)).pow 2).const_mul (25 / 289))
  convert h using 1
  · rfl
  · simp only [id_eq]
    ring

private theorem deriv_testR : deriv testR = fun x => -(50 / 289) * (x - 1 / 2) :=
  funext fun x => (testR_deriv x).deriv

private theorem deriv_deriv_testR (x : ℝ) : deriv (deriv testR) x = -(50 / 289) := by
  rw [deriv_testR]
  simpa only [id_eq, mul_one] using
    (((hasDerivAt_id x).sub_const (1 / 2)).const_mul (-(50 / 289 : ℝ))).deriv

private theorem negative_actual_density :
    trialDensity testK testR (20 / 17) (5 / 2) (1 / 8) 1 (1 / 2) =
      -(4498900 / 410338673 : ℝ) := by
  unfold trialDensity
  rw [test_warp, test_slope]
  unfold trialA trialBeta meridionalOperator
  rw [test_warp, test_slope, deriv_deriv_testR, deriv_testR]
  norm_num [testK, testR]

private theorem trial_density_scale (K r : ℝ → ℝ) (hr : ContDiff ℝ 2 r)
    (κ C α c d x : ℝ) :
    trialDensity K (fun y => d * r y) κ C α c x = d ^ 2 * trialDensity K r κ C α c x := by
  have hd : deriv (fun y => d * r y) = fun y => d * deriv r y :=
    funext fun y => ((hr.differentiable (by norm_num) y).hasDerivAt.const_mul d).deriv
  have hdd : deriv (deriv (fun y => d * r y)) x = d * deriv (deriv r) x := by
    rw [hd]
    have hrD : ContDiff ℝ 1 (deriv r) := hr.deriv'
    exact ((hrD.differentiable (by norm_num) x).hasDerivAt.const_mul d).deriv
  unfold trialDensity meridionalOperator
  rw [hdd, hd]
  ring

-- This is a failure of the candidate pointwise certificate, NOT negative action.
example : ∃ s : ℝ → ℝ, IsSmoothAreaCompetitor (5 / 2) testK s ∧
    trialDensity testK s (20 / 17) (5 / 2) (1 / 8) 1 (1 / 2) < 0 := by
  have hpos (x : ℝ) (hx : x ∈ Icc (0 : ℝ) 1) : 0 < testK x :=
    (by norm_num : (0 : ℝ) < 20 / 17).trans_le (test_box x hx).1
  obtain ⟨d, hd, hm, _⟩ := exists_normalized_area_probe testK testR testK_smooth testR_smooth
    hpos test_moments.1 test_moments.2 ⟨1 / 2, by norm_num, by norm_num [testR]⟩
  refine ⟨fun y => d * testR y, ?_, ?_⟩
  · refine ⟨testK_smooth, contDiff_const.mul testR_smooth,
      ⟨20 / 17, 50 / 17, by norm_num, test_box, by norm_num⟩,
      test_moments.1, test_moments.2, hm⟩
  · rw [trial_density_scale testK testR (testR_smooth.of_le (by simp)), negative_actual_density]
    exact mul_neg_of_pos_of_neg (sq_pos_of_pos hd) (by norm_num)

private def historyA (κ γ f b : ℝ) : ℝ :=
  κ + κ ^ 2 * f / 8 + κ * γ * (b ^ 2 + 10 * κ * f - 4)
private def historyBeta (κ η f b : ℝ) : ℝ :=
  5 * κ / 2 - κ ^ 2 * f + κ * η * (b ^ 2 + 10 * κ * f - 4)
private def historyDensity (K r : ℝ → ℝ) (κ γ η x : ℝ) : ℝ :=
  let f := warp K x
  let b := warpSlope K x
  let a := historyA κ γ f b
  let β := historyBeta κ η f b
  let da := κ ^ 2 * b / 8 + 4 * κ * γ * b * (5 * κ / 2 - K x)
  let db := -κ ^ 2 * b + 4 * κ * η * b * (5 * κ / 2 - K x)
  f * (meridionalOperator K r x + a * r x) ^ 2 + 2 * a * f ^ 2 * deriv r x ^ 2 +
    f * ((β - K x) * b + 2 * f * da) * r x * deriv r x +
    (f * (K x ^ 2 + (2 * a - β) * K x - a ^ 2) +
      (β - K x) * b ^ 2 / 2 + f * b / 2 * db) * r x ^ 2
private def historyFlux (K r : ℝ → ℝ) (κ γ η x : ℝ) : ℝ :=
  2 * historyA κ γ (warp K x) (warpSlope K x) * warp K x ^ 2 * r x * deriv r x +
    historyBeta κ η (warp K x) (warpSlope K x) / 2 * warp K x * warpSlope K x * r x ^ 2

private theorem history_flux_hasDerivAt (K r : ℝ → ℝ) (hK : Continuous K)
    (hr : ContDiff ℝ 2 r) (κ γ η x : ℝ) :
    HasDerivAt (historyFlux K r κ γ η)
      (historyDensity K r κ γ η x -
        meridionalActionDensity (warp K x) (warpSlope K x) (K x)
          (r x) (deriv r x) (deriv (deriv r) x)) x := by
  have hf := warp_hasDerivAt K hK x
  have hb := warpSlope_hasDerivAt K hK x
  have hrd := (hr.differentiable (by norm_num) x).hasDerivAt
  have hrD : ContDiff ℝ 1 (deriv r) := hr.deriv'
  have hrdd := (hrD.differentiable (by norm_num) x).hasDerivAt
  have hΦ := ((hb.pow 2).add (hf.const_mul (10 * κ))).sub_const 4
  have ha := ((hf.const_mul (κ ^ 2 / 8)).const_add κ).add (hΦ.const_mul (κ * γ))
  have hβ := ((hasDerivAt_const x (5 * κ / 2)).sub
    (hf.const_mul (κ ^ 2))).add (hΦ.const_mul (κ * η))
  have h := (((((ha.const_mul 2).mul (hf.pow 2)).mul hrd).mul hrdd)).add
    (((((hβ.div_const 2).mul hf).mul hb).mul (hrd.pow 2)))
  convert h using 1
  · funext y
    unfold historyFlux historyA historyBeta
    simp only [Pi.mul_apply, Pi.pow_apply, Pi.sub_apply, Pi.add_apply]
    ring
  · simp only [Pi.mul_apply, Pi.pow_apply, Pi.sub_apply, Pi.add_apply]
    unfold historyDensity historyA historyBeta meridionalActionDensity meridionalOperator
    ring

private def historyDet (γ η u t k : ℝ) : ℝ :=
  let g := t + 10 * u - 4
  let a := 1 + u / 8 + γ * g
  let β := 5 / 2 - u + η * g
  let da := 1 / 8 + 4 * γ * (5 / 2 - k)
  let db := -1 + 4 * η * (5 / 2 - k)
  8 * a * (u * (k ^ 2 + (2 * a - β) * k - a ^ 2) +
    (β - k) * t / 2 + u * t * db / 2) - (β - k + 2 * u * da) ^ 2 * t

private def historyCornerQuotient (γ η u : ℝ) : ℝ :=
  let a1 := 1 / 8 + 6 * γ
  8 * (1 + a1 * u) * (12 * η + u * (55 / 8 + 18 * γ - 27 * η) - a1 ^ 2 * u ^ 2) -
    4 * (-3 / 4 + 6 * η) ^ 2 * u * (1 - u)

private theorem history_corner_factor (γ η u : ℝ) :
    historyDet γ η u (4 - 4 * u) (5 / 2) = u * historyCornerQuotient γ η u := by
  unfold historyDet historyCornerQuotient
  ring

private theorem history_corner_eta_nonneg (γ η : ℝ)
    (hN : ∀ u ∈ Ioo (0 : ℝ) (2 / 5), 0 ≤ historyDet γ η u (4 - 4 * u) (5 / 2)) :
    0 ≤ η := by
  have hc : Continuous (historyCornerQuotient γ η) := by
    unfold historyCornerQuotient
    fun_prop
  have hupper : ∀ᶠ u in nhdsWithin (0 : ℝ) (Ioi 0), u < (2 / 5 : ℝ) :=
    (eventually_lt_nhds (by norm_num : (0 : ℝ) < 2 / 5)).filter_mono nhdsWithin_le_nhds
  have hpos : ∀ᶠ u in nhdsWithin (0 : ℝ) (Ioi 0), 0 < u := self_mem_nhdsWithin
  have hge : ∀ᶠ u in nhdsWithin (0 : ℝ) (Ioi 0), 0 ≤ historyCornerQuotient γ η u := by
    filter_upwards [hupper, hpos] with u hu hp
    have hh := hN u ⟨hp, hu⟩
    rw [history_corner_factor] at hh
    exact nonneg_of_mul_nonneg_right hh hp
  have hlim := (hc.tendsto 0).mono_left
    (show nhdsWithin (0 : ℝ) (Ioi 0) ≤ nhds 0 from nhdsWithin_le_nhds)
  have hh : 0 ≤ historyCornerQuotient γ η 0 := ge_of_tendsto hlim hge
  norm_num [historyCornerQuotient] at hh
  linarith

private theorem history_midpoint_eta_neg (γ η : ℝ)
    (hD : 0 ≤ (140 / 289 : ℝ) *
      (2 - (5 / 2 - 140 / 289 + η * (244 / 289)) -
        ((140 / 289 : ℝ) / 8 + γ * (244 / 289)) ^ 2)) : η ≤ -9 / 488 := by
  nlinarith only [hD, sq_nonneg ((140 / 289 : ℝ) / 8 + γ * (244 / 289))]

-- This rejects the stated ENCLOSURE certificate at cap5/2. It does not
-- assert that every enclosed corner is attained by an original geometry.
private theorem no_constant_history_enclosure (γ η : ℝ)
    (hN : ∀ u ∈ Ioo (0 : ℝ) (2 / 5), 0 ≤ historyDet γ η u (4 - 4 * u) (5 / 2))
    (hD : 0 ≤ (140 / 289 : ℝ) *
      (2 - (5 / 2 - 140 / 289 + η * (244 / 289)) -
        ((140 / 289 : ℝ) / 8 + γ * (244 / 289)) ^ 2)) : False := by
  have hp := history_corner_eta_nonneg γ η hN
  have hn := history_midpoint_eta_neg γ η hD
  linarith

end RicciFlowSharpEstimate.Geometry.AreaProfile
