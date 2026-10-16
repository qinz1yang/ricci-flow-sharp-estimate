/-
Copyright (c) 2026 Ziyang Qin. All rights reserved.
No license is granted by this file.
Authors: Ziyang Qin
-/
import RicciFlowSharpEstimate.Geometry.AreaProbeEnergy
import RicciFlowSharpEstimate.Geometry.AreaWarpStateBounds

/-! # Complete-action comparison from a warp-dependent flux -/

noncomputable section
namespace RicciFlowSharpEstimate.Geometry.AreaProfile
open Set MeasureTheory
open scoped ContDiff

private def row (a b c x : ℝ) : ℝ :=
  a * (1 - x) ^ 2 + b * (2 * x * (1 - x)) + c * x ^ 2

private theorem row_nonneg {a b c x : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hc : 0 ≤ c) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) : 0 ≤ row a b c x := by
  unfold row
  have : 0 ≤ 1 - x := sub_nonneg.mpr hx1
  positivity

private theorem row_ge {a b c d x : ℝ} (ha : d ≤ a) (hb : d ≤ b)
    (hc : d ≤ c) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) : d ≤ row a b c x := by
  have h := row_nonneg (sub_nonneg.mpr ha) (sub_nonneg.mpr hb)
    (sub_nonneg.mpr hc) hx0 hx1
  unfold row at *
  nlinarith only [h]

private def block0 (C y z : ℝ) : ℝ :=
  row (row 0 (5 - 2 * C) (4 - C) z)
    (row (-11 / 2 + 5 / 2 * C) (-1 / 8 + C / 2) 3 z)
    (row (5 / 2 - C) (3 / 4 * C) (-1 + 5 / 2 * C) z) y

private def block1 (C y z : ℝ) : ℝ :=
  row (row (-7 / 6 + 2 / 3 * C) (25 / 6 - 5 / 3 * C) (21 / 4 - 2 * C) z)
    (row (-29 / 12 + 7 / 6 * C) (7 / 6 - 7 / 24 * C) (3 - 3 / 4 * C) z)
    (row (-7 / 24 + C / 6) (-29 / 24 + 5 / 6 * C) (-11 / 8 + 3 / 2 * C) z) y

private def block2 (C y z : ℝ) : ℝ :=
  row (row (-4 / 3 + C) (35 / 12 - C) (14 / 3 - 2 * C) z)
    (row (-5 / 3 + 13 / 12 * C) (17 / 24 - C / 24) (11 / 6 - 2 / 3 * C) z)
    (row (-2 + 7 / 6 * C) (-3 / 2 + 11 / 12 * C) (-1 + 2 / 3 * C) z) y

private def block3 (C y z : ℝ) : ℝ :=
  row (row (-11 / 4 + 2 * C) (-1 + C) 0 z)
    (row (-11 / 4 + 2 * C) (-1 + C) 0 z)
    (row (-11 / 4 + 2 * C) (-1 + C) 0 z) y

private def remainder (C u t k : ℝ) : ℝ :=
  u * (k ^ 2 + (2 - C) * k - 1 + u * k / 2 - t / 2) +
    (C - k) * t / 2 - (C - k - u / 2) ^ 2 * t / 8

private theorem remainder_bernstein (C v y z : ℝ) (hC : C ^ 2 = 2 * C + 1 / 2) :
    remainder C ((1 - v) * ((2 * C - 4) + (5 - 2 * C) * y)) (4 * v)
        (1 + (C - 1) * z) =
      block0 C y z * (1 - v) ^ 3 +
        3 * block1 C y z * v * (1 - v) ^ 2 +
        3 * block2 C y z * v ^ 2 * (1 - v) + block3 C y z * v ^ 3 := by
  have hC3 : C ^ 3 = 9 / 2 * C + 1 := by
    have h := congrArg (fun t : ℝ => t * C) hC
    nlinarith
  unfold remainder block0 block1 block2 block3 row
  ring_nf
  simp only [hC, hC3]
  ring

private theorem remainder_nonneg_of_coordinates (C v y z : ℝ)
    (hC : C ^ 2 = 2 * C + 1 / 2) (hlo : 11 / 5 ≤ C) (hhi : C ≤ 9 / 4)
    (hv0 : 0 ≤ v) (hv1 : v ≤ 1) (hy0 : 0 ≤ y) (hy1 : y ≤ 1)
    (hz0 : 0 ≤ z) (hz1 : z ≤ 1) :
    0 ≤ remainder C ((1 - v) * ((2 * C - 4) + (5 - 2 * C) * y)) (4 * v)
      (1 + (C - 1) * z) := by
  have h0 : 0 ≤ block0 C y z := by
    unfold block0
    apply row_nonneg _ _ _ hy0 hy1 <;>
      apply row_nonneg <;> first | exact hz0 | exact hz1 | linarith
  have h1 : 0 ≤ block1 C y z := by
    unfold block1
    apply row_nonneg _ _ _ hy0 hy1 <;>
      apply row_nonneg <;> first | exact hz0 | exact hz1 | linarith
  have h2 : 0 ≤ block2 C y z := by
    unfold block2
    apply row_nonneg _ _ _ hy0 hy1 <;>
      apply row_nonneg <;> first | exact hz0 | exact hz1 | linarith
  have h3 : 0 ≤ block3 C y z := by
    unfold block3
    apply row_nonneg _ _ _ hy0 hy1 <;>
      apply row_nonneg <;> first | exact hz0 | exact hz1 | linarith
  rw [remainder_bernstein C v y z hC]
  have : 0 ≤ 1 - v := sub_nonneg.mpr hv1
  positivity

private theorem remainder_ge_of_coordinates (C v y z : ℝ)
    (hC : C ^ 2 = 2 * C + 1 / 2) (hlo : 11 / 5 ≤ C) (hhi : C ≤ 9 / 4)
    (hv0 : 0 ≤ v) (hv1 : v ≤ 1) (hy0 : 0 ≤ y) (hy1 : y ≤ 1)
    (hz0 : 0 ≤ z) (hz1 : z ≤ 1) :
    3 / 16 * v * (1 - v) ≤
      remainder C ((1 - v) * ((2 * C - 4) + (5 - 2 * C) * y)) (4 * v)
        (1 + (C - 1) * z) := by
  have h0 : 0 ≤ block0 C y z := by
    unfold block0
    apply row_nonneg _ _ _ hy0 hy1 <;>
      apply row_nonneg <;> first | exact hz0 | exact hz1 | linarith
  have h1 : 1 / 16 ≤ block1 C y z := by
    unfold block1
    apply row_ge _ _ _ hy0 hy1 <;>
      apply row_ge <;> first | exact hz0 | exact hz1 | linarith
  have h2 : 1 / 16 ≤ block2 C y z := by
    unfold block2
    apply row_ge _ _ _ hy0 hy1 <;>
      apply row_ge <;> first | exact hz0 | exact hz1 | linarith
  have h3 : 0 ≤ block3 C y z := by
    unfold block3
    apply row_nonneg _ _ _ hy0 hy1 <;>
      apply row_nonneg <;> first | exact hz0 | exact hz1 | linarith
  have hv : 0 ≤ 1 - v := sub_nonneg.mpr hv1
  rw [remainder_bernstein C v y z hC]
  calc
    3 / 16 * v * (1 - v) =
        0 * (1 - v) ^ 3 + 3 * (1 / 16) * v * (1 - v) ^ 2 +
          3 * (1 / 16) * v ^ 2 * (1 - v) + 0 * v ^ 3 := by ring
    _ ≤ _ := by gcongr

private theorem reachable_remainder_ge (C u v k : ℝ)
    (hC : C ^ 2 = 2 * C + 1 / 2) (hlo : 11 / 5 ≤ C) (hhi : C ≤ 9 / 4)
    (hv0 : 0 ≤ v) (hv1 : v ≤ 1) (hu0 : 0 ≤ u)
    (huL : 1 - v ≤ C * u) (huU : u ≤ 1 - v) (hk0 : 1 ≤ k) (hk1 : k ≤ C) :
    3 / 16 * u * v ≤ remainder C u (4 * v) k := by
  rcases lt_or_eq_of_le hv1 with hv | hv
  · have hB : 0 < 5 - 2 * C := by linarith
    have hA : 0 ≤ 2 * C - 4 := by linarith
    have hD : 0 < C - 1 := by linarith
    have hV : 0 < 1 - v := sub_pos.mpr hv
    have hCA : C * (2 * C - 4) = 1 := by nlinarith [hC]
    have huA : (1 - v) * (2 * C - 4) ≤ u := by
      calc
        _ ≤ C * u * (2 * C - 4) := mul_le_mul_of_nonneg_right huL hA
        _ = (C * (2 * C - 4)) * u := by ring
        _ = u := by rw [hCA, one_mul]
    let y := (u / (1 - v) - (2 * C - 4)) / (5 - 2 * C)
    let z := (k - 1) / (C - 1)
    have hy0 : 0 ≤ y := div_nonneg
      (sub_nonneg.mpr ((le_div_iff₀ hV).mpr (by simpa only [mul_comm] using huA))) hB.le
    have hy1 : y ≤ 1 := by
      apply (div_le_iff₀ hB).mpr
      have := (div_le_one hV).mpr huU
      linarith
    have hz0 : 0 ≤ z := div_nonneg (sub_nonneg.mpr hk0) hD.le
    have hz1 : z ≤ 1 := (div_le_one hD).mpr (by linarith)
    have hu : (1 - v) * ((2 * C - 4) + (5 - 2 * C) * y) = u := by
      dsimp [y]
      field_simp
      ring
    have hk : 1 + (C - 1) * z = k := by
      dsimp [z]
      field_simp
      ring
    have hG := remainder_ge_of_coordinates C v y z hC hlo hhi hv0 hv.le hy0 hy1 hz0 hz1
    rw [hu, hk] at hG
    exact (by nlinarith [mul_nonneg (sub_nonneg.mpr huU) hv0] :
      3 / 16 * u * v ≤ 3 / 16 * v * (1 - v)).trans hG
  · have hu : u = 0 := by rw [hv] at huU; linarith
    rw [hu, hv]
    unfold remainder
    nlinarith [mul_nonneg (sub_nonneg.mpr hk1) (show 0 ≤ 4 - (C - k) by linarith)]

private theorem reachable_remainder_nonneg_of_lt (C u v k : ℝ)
    (hC : C ^ 2 = 2 * C + 1 / 2) (hlo : 11 / 5 ≤ C) (hhi : C ≤ 9 / 4)
    (hv0 : 0 ≤ v) (hv1 : v < 1) (hu0 : 1 - v ≤ C * u) (hu1 : u ≤ 1 - v)
    (hk0 : 1 ≤ k) (hk1 : k ≤ C) : 0 ≤ remainder C u (4 * v) k := by
  have hB : 0 < 5 - 2 * C := by linarith
  have hA : 0 ≤ 2 * C - 4 := by linarith
  have hD : 0 < C - 1 := by linarith
  have hv : 0 < 1 - v := sub_pos.mpr hv1
  have hCA : C * (2 * C - 4) = 1 := by nlinarith [hC]
  have huA : (1 - v) * (2 * C - 4) ≤ u := by
    calc
      (1 - v) * (2 * C - 4) ≤ C * u * (2 * C - 4) :=
        mul_le_mul_of_nonneg_right hu0 hA
      _ = (C * (2 * C - 4)) * u := by ring
      _ = u := by rw [hCA, one_mul]
  let y := (u / (1 - v) - (2 * C - 4)) / (5 - 2 * C)
  let z := (k - 1) / (C - 1)
  have hy0 : 0 ≤ y := div_nonneg
    (sub_nonneg.mpr ((le_div_iff₀ hv).mpr (by simpa only [mul_comm] using huA))) hB.le
  have hy1 : y ≤ 1 := by
    apply (div_le_iff₀ hB).mpr
    have := (div_le_one hv).mpr hu1
    linarith
  have hz0 : 0 ≤ z := div_nonneg (sub_nonneg.mpr hk0) hD.le
  have hz1 : z ≤ 1 := (div_le_one hD).mpr (by linarith)
  have hu : (1 - v) * ((2 * C - 4) + (5 - 2 * C) * y) = u := by
    dsimp [y]
    field_simp
    ring
  have hk : 1 + (C - 1) * z = k := by
    dsimp [z]
    field_simp
    ring
  simpa only [hu, hk] using
    remainder_nonneg_of_coordinates C v y z hC hlo hhi hv0 hv1.le hy0 hy1 hz0 hz1

private theorem reachable_remainder_nonneg (C u v k : ℝ)
    (hC : C ^ 2 = 2 * C + 1 / 2) (hlo : 11 / 5 ≤ C) (hhi : C ≤ 9 / 4)
    (hv0 : 0 ≤ v) (hv1 : v ≤ 1) (hu0 : 0 ≤ u)
    (huL : 1 - v ≤ C * u) (huU : u ≤ 1 - v) (hk0 : 1 ≤ k) (hk1 : k ≤ C) :
    0 ≤ remainder C u (4 * v) k := by
  rcases lt_or_eq_of_le hv1 with hv | hv
  · exact reachable_remainder_nonneg_of_lt C u v k hC hlo hhi hv0 hv huL huU hk0 hk1
  · have hu : u = 0 := by rw [hv] at huU; linarith
    rw [hu, hv]
    unfold remainder
    nlinarith [mul_nonneg (sub_nonneg.mpr hk1) (show 0 ≤ 4 - (C - k) by linarith)]

private def warpCalibrationDensity (K r : ℝ → ℝ) (κ Λ x : ℝ) : ℝ :=
  let f := warp K x
  let b := warpSlope K x
  f * (meridionalOperator K r x + κ * r x) ^ 2 +
    2 * κ * f ^ 2 * deriv r x ^ 2 +
    f * (Λ - K x - κ ^ 2 * f / 2) * b * r x * deriv r x +
    (f * (K x ^ 2 + (2 * κ - Λ) * K x - κ ^ 2) +
      κ ^ 2 * f ^ 2 * K x / 2 + (Λ - K x) * b ^ 2 / 2 -
      κ ^ 2 * f * b ^ 2 / 2) * r x ^ 2

private def warpCalibrationFlux (K r : ℝ → ℝ) (κ Λ x : ℝ) : ℝ :=
  (-2 * κ) * ((warp K x ^ 2 * r x) * deriv r x) -
    (Λ / 2) * ((warp K x * warpSlope K x) * r x ^ 2) +
    (κ ^ 2 / 4) * ((warp K x ^ 2 * warpSlope K x) * r x ^ 2)

private theorem warp_calibration_flux_hasDerivAt (K r : ℝ → ℝ)
    (hK : Continuous K) (hr : ContDiff ℝ 2 r) (κ Λ x : ℝ) :
    HasDerivAt (warpCalibrationFlux K r κ Λ)
      (meridionalActionDensity (warp K x) (warpSlope K x) (K x)
          (r x) (deriv r x) (deriv (deriv r) x) -
        warpCalibrationDensity K r κ Λ x) x := by
  have hf := warp_hasDerivAt K hK x
  have hb := warpSlope_hasDerivAt K hK x
  have hrd := (hr.differentiable (by norm_num) x).hasDerivAt
  have hrD : ContDiff ℝ 1 (deriv r) := hr.deriv'
  have hrdd := (hrD.differentiable (by norm_num) x).hasDerivAt
  have h := (((((hf.pow 2).mul hrd).mul hrdd).const_mul (-2 * κ)).sub
    (((hf.mul hb).mul (hrd.pow 2)).const_mul (Λ / 2))).add
    ((((hf.pow 2).mul hb).mul (hrd.pow 2)).const_mul (κ ^ 2 / 4))
  convert h using 1
  · rfl
  · simp only [Pi.mul_apply, Pi.pow_apply]
    unfold meridionalActionDensity warpCalibrationDensity meridionalOperator
    ring

private theorem warp_calibration_density_continuous (K r : ℝ → ℝ)
    (hK : Continuous K) (hr : ContDiff ℝ 2 r) (κ Λ : ℝ) :
    Continuous (warpCalibrationDensity K r κ Λ) := by
  have hf := warp_continuous K hK
  have hb := warpSlope_continuous K hK
  have hr0 := hr.continuous
  have hr1 := hr.continuous_deriv (by norm_num)
  have hq := meridionalOperator_continuous_of_contDiff_two K r hK hr
  unfold warpCalibrationDensity
  fun_prop

private theorem action_eq_warp_calibration (K r : ℝ → ℝ)
    (hK : Continuous K) (hr : ContDiff ℝ 2 r)
    (hzero : (∫ x in (0 : ℝ)..1, K x) = 2)
    (hone : (∫ x in (0 : ℝ)..1, x * K x) = 1) (κ Λ : ℝ) :
    meridionalAction K r = ∫ x in (0 : ℝ)..1, warpCalibrationDensity K r κ Λ x := by
  have hf := warp_continuous K hK
  have hb := warpSlope_continuous K hK
  have hr0 := hr.continuous
  have hr1 := hr.continuous_deriv (by norm_num)
  have hr2 := hr.deriv'.continuous_deriv_one
  have hD : Continuous (fun x => meridionalActionDensity (warp K x)
      (warpSlope K x) (K x) (r x) (deriv r x) (deriv (deriv r) x)) := by
    unfold meridionalActionDensity
    fun_prop
  have hCal := warp_calibration_density_continuous K r hK hr κ Λ
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun x _ => warp_calibration_flux_hasDerivAt K r hK hr κ Λ x)
    ((hD.sub hCal).intervalIntegrable 0 1)
  rw [intervalIntegral.integral_sub (hD.intervalIntegrable 0 1)
    (hCal.intervalIntegrable 0 1)] at h
  have hF0 : warpCalibrationFlux K r κ Λ 0 = 0 := by
    simp [warpCalibrationFlux, warp_zero]
  have hF1 : warpCalibrationFlux K r κ Λ 1 = 0 := by
    simp [warpCalibrationFlux, warp_one K hK hzero hone]
  rw [hF0, hF1, sub_self] at h
  exact sub_eq_zero.mp h

private theorem warp_calibration_density_nonneg (K r : ℝ → ℝ) (κ C x : ℝ)
    (hκ : 0 < κ) (hC : C ^ 2 = 2 * C + 1 / 2)
    (hlo : 11 / 5 ≤ C) (hhi : C ≤ 9 / 4)
    (hbox : κ ≤ K x ∧ K x ≤ C * κ) (hf : 0 ≤ warp K x)
    (hstate : (warpSlope K x) ^ 2 + 4 * κ * warp K x ≤ 4 ∧
      4 ≤ (warpSlope K x) ^ 2 + 4 * (C * κ) * warp K x) :
    0 ≤ warpCalibrationDensity K r κ (C * κ) x := by
  let f := warp K x
  let b := warpSlope K x
  have hv0 : 0 ≤ b ^ 2 / 4 := div_nonneg (sq_nonneg b) (by norm_num)
  have hu0 : 0 ≤ κ * f := mul_nonneg hκ.le hf
  have hv1 : b ^ 2 / 4 ≤ 1 := by dsimp [b] at *; nlinarith [hstate.1]
  have huL : 1 - b ^ 2 / 4 ≤ C * (κ * f) := by
    dsimp [f, b] at *
    nlinarith [hstate.2]
  have huU : κ * f ≤ 1 - b ^ 2 / 4 := by
    dsimp [f, b] at *
    nlinarith [hstate.1]
  have hkL : 1 ≤ K x / κ := (le_div_iff₀ hκ).mpr (by simpa using hbox.1)
  have hkU : K x / κ ≤ C := (div_le_iff₀ hκ).mpr hbox.2
  have hG := reachable_remainder_nonneg C (κ * f) (b ^ 2 / 4) (K x / κ)
    hC hlo hhi hv0 hv1 hu0 huL huU hkL hkU
  have hfour : 4 * (b ^ 2 / 4) = b ^ 2 := by ring
  rw [hfour] at hG
  have hid : warpCalibrationDensity K r κ (C * κ) x =
      f * (meridionalOperator K r x + κ * r x) ^ 2 +
        2 * κ * (f * deriv r x + (C - K x / κ - κ * f / 2) * b / 4 * r x) ^ 2 +
        κ * remainder C (κ * f) (b ^ 2) (K x / κ) * r x ^ 2 := by
    dsimp [warpCalibrationDensity, remainder, f, b]
    field_simp
    ring
  rw [hid]
  positivity

/-- A warp-dependent boundary-null flux proves complete-action safety for
the original positive curvature boxes satisfying the displayed quadratic
pinching condition. Curvature is continuous and the probe has its actual
first and second derivatives, with arbitrary pole values. -/
theorem meridionalAction_nonneg_of_quadratic_pinching (K r : ℝ → ℝ)
    (hK : Continuous K) (hr : ContDiff ℝ 2 r)
    (hzero : (∫ x in (0 : ℝ)..1, K x) = 2)
    (hone : (∫ x in (0 : ℝ)..1, x * K x) = 1)
    (κ Λ : ℝ) (hκ : 0 < κ)
    (hbox : ∀ x ∈ Icc (0 : ℝ) 1, κ ≤ K x ∧ K x ≤ Λ)
    (hpinch : Λ ^ 2 ≤ 2 * κ * Λ + κ ^ 2 / 2) :
    0 ≤ meridionalAction K r := by
  let C : ℝ := 1 + Real.sqrt (3 / 2)
  have hs : (Real.sqrt (3 / 2 : ℝ)) ^ 2 = 3 / 2 := Real.sq_sqrt (by norm_num)
  have hs0 : 0 ≤ Real.sqrt (3 / 2 : ℝ) := Real.sqrt_nonneg _
  have hC : C ^ 2 = 2 * C + 1 / 2 := by dsimp [C]; nlinarith
  have hlo : 11 / 5 ≤ C := by dsimp [C]; nlinarith
  have hhi : C ≤ 9 / 4 := by dsimp [C]; nlinarith
  have hscale : Λ ≤ C * κ := by
    have hκΛ : κ ≤ Λ := (hbox 0 (by norm_num)).1.trans (hbox 0 (by norm_num)).2
    have hCsq : (C * κ - κ) ^ 2 = 3 / 2 * κ ^ 2 := by
      have := congrArg (fun y : ℝ => y * κ ^ 2) hC
      nlinarith
    have hCκ : 0 ≤ C * κ - κ := by nlinarith [mul_nonneg hκ.le (by linarith : 0 ≤ C - 1)]
    have hsq : (Λ - κ) ^ 2 ≤ (C * κ - κ) ^ 2 := by nlinarith [hpinch, hCsq]
    have := (sq_le_sq₀ (sub_nonneg.mpr hκΛ) hCκ).mp hsq
    linarith
  have hrootbox (x : ℝ) (hx : x ∈ Icc (0 : ℝ) 1) : κ ≤ K x ∧ K x ≤ C * κ :=
    ⟨(hbox x hx).1, (hbox x hx).2.trans hscale⟩
  rw [action_eq_warp_calibration K r hK hr hzero hone κ (C * κ)]
  apply intervalIntegral.integral_nonneg zero_le_one
  intro x hx
  have hf := (warp_nonneg_le_two_mul_min K hK
    (fun y hy => hκ.le.trans (hbox y hy).1) hzero hone x hx).1
  exact warp_calibration_density_nonneg K r κ C x hκ hC hlo hhi (hrootbox x hx) hf
    (warpSlope_sq_add_four_mul_warp_bounds K hK κ (C * κ) hκ.le hrootbox hzero hone x hx)

private theorem warp_calibration_density_ge_slope (K r : ℝ → ℝ) (κ C x : ℝ)
    (hκ : 0 < κ) (hC : C ^ 2 = 2 * C + 1 / 2)
    (hlo : 11 / 5 ≤ C) (hhi : C ≤ 9 / 4)
    (hbox : κ ≤ K x ∧ K x ≤ C * κ) (hf : 0 ≤ warp K x)
    (hstate : (warpSlope K x) ^ 2 + 4 * κ * warp K x ≤ 4 ∧
      4 ≤ (warpSlope K x) ^ 2 + 4 * (C * κ) * warp K x) :
    3 * κ ^ 2 / 64 * (warp K x * warpSlope K x ^ 2 * r x ^ 2) ≤
      warpCalibrationDensity K r κ (C * κ) x := by
  let f := warp K x
  let b := warpSlope K x
  have hv0 : 0 ≤ b ^ 2 / 4 := div_nonneg (sq_nonneg b) (by norm_num)
  have hu0 : 0 ≤ κ * f := mul_nonneg hκ.le hf
  have hv1 : b ^ 2 / 4 ≤ 1 := by dsimp [b] at *; nlinarith [hstate.1]
  have huL : 1 - b ^ 2 / 4 ≤ C * (κ * f) := by dsimp [f, b] at *; nlinarith [hstate.2]
  have huU : κ * f ≤ 1 - b ^ 2 / 4 := by dsimp [f, b] at *; nlinarith [hstate.1]
  have hkL : 1 ≤ K x / κ := (le_div_iff₀ hκ).mpr (by simpa using hbox.1)
  have hkU : K x / κ ≤ C := (div_le_iff₀ hκ).mpr hbox.2
  have hG := reachable_remainder_ge C (κ * f) (b ^ 2 / 4) (K x / κ)
    hC hlo hhi hv0 hv1 hu0 huL huU hkL hkU
  have hfour : 4 * (b ^ 2 / 4) = b ^ 2 := by ring
  rw [hfour] at hG
  have hid : warpCalibrationDensity K r κ (C * κ) x =
      f * (meridionalOperator K r x + κ * r x) ^ 2 +
        2 * κ * (f * deriv r x + (C - K x / κ - κ * f / 2) * b / 4 * r x) ^ 2 +
        κ * remainder C (κ * f) (b ^ 2) (K x / κ) * r x ^ 2 := by
    dsimp [warpCalibrationDensity, remainder, f, b]
    field_simp
    ring
  rw [hid]
  have hs0 : 0 ≤ f * (meridionalOperator K r x + κ * r x) ^ 2 :=
    mul_nonneg hf (sq_nonneg _)
  have hs1 : 0 ≤ 2 * κ *
      (f * deriv r x + (C - K x / κ - κ * f / 2) * b / 4 * r x) ^ 2 := by positivity
  have hmul := mul_le_mul_of_nonneg_right hG (mul_nonneg hκ.le (sq_nonneg (r x)))
  dsimp only [f, b] at *
  nlinarith only [hs0, hs1, hmul]

/-- The complete quadratic-pinching calibration retains a positive multiple
of the physical slope-weighted probe mass, with arbitrary smooth pole values. -/
theorem meridionalAction_ge_slope_mass_of_quadratic_pinching (K r : ℝ → ℝ)
    (hK : Continuous K) (hr : ContDiff ℝ 2 r)
    (hzero : (∫ x in (0 : ℝ)..1, K x) = 2)
    (hone : (∫ x in (0 : ℝ)..1, x * K x) = 1)
    (κ Λ : ℝ) (hκ : 0 < κ)
    (hbox : ∀ x ∈ Icc (0 : ℝ) 1, κ ≤ K x ∧ K x ≤ Λ)
    (hpinch : Λ ^ 2 ≤ 2 * κ * Λ + κ ^ 2 / 2) :
    3 * κ ^ 2 / 64 * (∫ x in (0 : ℝ)..1,
      warp K x * warpSlope K x ^ 2 * r x ^ 2) ≤ meridionalAction K r := by
  let C : ℝ := 1 + Real.sqrt (3 / 2)
  have hs : (Real.sqrt (3 / 2 : ℝ)) ^ 2 = 3 / 2 := Real.sq_sqrt (by norm_num)
  have hs0 : 0 ≤ Real.sqrt (3 / 2 : ℝ) := Real.sqrt_nonneg _
  have hC : C ^ 2 = 2 * C + 1 / 2 := by dsimp [C]; nlinarith
  have hlo : 11 / 5 ≤ C := by dsimp [C]; nlinarith
  have hhi : C ≤ 9 / 4 := by dsimp [C]; nlinarith
  have hscale : Λ ≤ C * κ := by
    have hκΛ : κ ≤ Λ := (hbox 0 (by norm_num)).1.trans (hbox 0 (by norm_num)).2
    have hCsq : (C * κ - κ) ^ 2 = 3 / 2 * κ ^ 2 := by
      have := congrArg (fun y : ℝ => y * κ ^ 2) hC
      nlinarith
    have hCκ : 0 ≤ C * κ - κ := by
      nlinarith [mul_nonneg hκ.le (by linarith : 0 ≤ C - 1)]
    have hsq : (Λ - κ) ^ 2 ≤ (C * κ - κ) ^ 2 := by nlinarith [hpinch, hCsq]
    have := (sq_le_sq₀ (sub_nonneg.mpr hκΛ) hCκ).mp hsq
    linarith
  have hrootbox (x : ℝ) (hx : x ∈ Icc (0 : ℝ) 1) : κ ≤ K x ∧ K x ≤ C * κ :=
    ⟨(hbox x hx).1, (hbox x hx).2.trans hscale⟩
  have hi : IntervalIntegrable
      (fun x => warp K x * warpSlope K x ^ 2 * r x ^ 2) volume 0 1 := by
    have hf := warp_continuous K hK
    have hb := warpSlope_continuous K hK
    exact (show Continuous (fun x => warp K x * warpSlope K x ^ 2 * r x ^ 2) by
      fun_prop).intervalIntegrable 0 1
  rw [action_eq_warp_calibration K r hK hr hzero hone κ (C * κ),
    ← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_mono_on zero_le_one (hi.const_mul _)
    ((warp_calibration_density_continuous K r hK hr κ (C * κ)).intervalIntegrable 0 1)
  intro x hx
  have hf := (warp_nonneg_le_two_mul_min K hK
    (fun y hy => hκ.le.trans (hbox y hy).1) hzero hone x hx).1
  exact warp_calibration_density_ge_slope K r κ C x hκ hC hlo hhi (hrootbox x hx) hf
    (warpSlope_sq_add_four_mul_warp_bounds K hK κ (C * κ) hκ.le hrootbox hzero hone x hx)

end RicciFlowSharpEstimate.Geometry.AreaProfile
