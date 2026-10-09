/-
Copyright (c) 2026 Ziyang Qin. All rights reserved.
No license is granted by this file.
Authors: Ziyang Qin
-/
import RicciFlowSharpEstimate.Geometry.AreaAction
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Continuity of the complete area action

Curvature convergence controls the actual normalized primitives. For one fixed
smooth probe, bounded curvature and almost-everywhere convergence dominate all
terms of the complete action. The polynomial density estimate is adapted from
Ziyang Qin's historical `ConnectionMeridianActionContinuity` development.
-/

noncomputable section

namespace RicciFlowSharpEstimate.Geometry.AreaProfile

open Filter MeasureTheory Set Topology
open scoped ContDiff

private theorem abs_integral_weight_le (u w : ℝ → ℝ)
    (hu : Continuous u) (hw : Continuous w) (x : ℝ) (hx : x ∈ Icc (0 : ℝ) 1)
    (hwbound : ∀ s ∈ Icc (0 : ℝ) x, |w s| ≤ 1) :
    |∫ s in (0 : ℝ)..x, w s * u s| ≤ ∫ s in (0 : ℝ)..1, |u s| := by
  calc
    |∫ s in (0 : ℝ)..x, w s * u s| ≤ ∫ s in (0 : ℝ)..x, |w s * u s| :=
      intervalIntegral.abs_integral_le_integral_abs hx.1
    _ ≤ ∫ s in (0 : ℝ)..x, |u s| := by
      apply intervalIntegral.integral_mono_on hx.1
        ((hw.mul hu).abs.intervalIntegrable 0 x) (hu.abs.intervalIntegrable 0 x)
      intro s hs
      change |w s * u s| ≤ |u s|
      rw [abs_mul]
      exact mul_le_of_le_one_left (abs_nonneg _) (hwbound s hs)
    _ ≤ ∫ s in (0 : ℝ)..1, |u s| :=
      intervalIntegral.integral_mono_interval le_rfl hx.1 hx.2
        (Filter.Eventually.of_forall fun _ => abs_nonneg _) (hu.abs.intervalIntegrable 0 1)

/-- The physical warp changes by at most twice the curvature `L¹` distance. -/
theorem abs_warp_sub_le_integral_abs (K L : ℝ → ℝ)
    (hK : Continuous K) (hL : Continuous L) (x : ℝ) (hx : x ∈ Icc (0 : ℝ) 1) :
    |warp K x - warp L x| ≤ 2 * ∫ s in (0 : ℝ)..1, |K s - L s| := by
  have hiK : IntervalIntegrable (fun s : ℝ => (x - s) * K s) volume 0 x :=
    ((continuous_const.sub continuous_id).mul hK).intervalIntegrable 0 x
  have hiL : IntervalIntegrable (fun s : ℝ => (x - s) * L s) volume 0 x :=
    ((continuous_const.sub continuous_id).mul hL).intervalIntegrable 0 x
  have heq : warp K x - warp L x =
      -2 * ∫ s in (0 : ℝ)..x, (x - s) * (K s - L s) := by
    simp only [mul_sub, intervalIntegral.integral_sub hiK hiL, warp]
    ring
  rw [heq, abs_mul]
  norm_num only [abs_neg, abs_of_nonneg (show (0 : ℝ) ≤ 2 by norm_num)]
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  apply abs_integral_weight_le _ _ (hK.sub hL) (continuous_const.sub continuous_id) x hx
  intro s hs
  change |x - s| ≤ 1
  rw [abs_of_nonneg (sub_nonneg.mpr hs.2)]
  linarith [hs.1, hx.2]

/-- The physical warp slope has the same curvature `L¹` bound. -/
theorem abs_warpSlope_sub_le_integral_abs (K L : ℝ → ℝ)
    (hK : Continuous K) (hL : Continuous L) (x : ℝ) (hx : x ∈ Icc (0 : ℝ) 1) :
    |warpSlope K x - warpSlope L x| ≤ 2 * ∫ s in (0 : ℝ)..1, |K s - L s| := by
  have heq : warpSlope K x - warpSlope L x =
      -2 * ∫ s in (0 : ℝ)..x, (1 : ℝ) * (K s - L s) := by
    simp only [one_mul, intervalIntegral.integral_sub
      (hK.intervalIntegrable 0 x) (hL.intervalIntegrable 0 x), warpSlope]
    ring
  rw [heq, abs_mul]
  norm_num only [abs_neg, abs_of_nonneg (show (0 : ℝ) ≤ 2 by norm_num)]
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  exact abs_integral_weight_le _ _ (hK.sub hL) continuous_const x hx
    (by intro s hs; norm_num)

/-- `L¹` convergence of curvature gives convergence of the actual warp at every physical point. -/
theorem tendsto_warp_of_l1 (Kn : ℕ → ℝ → ℝ) (K : ℝ → ℝ)
    (hn : ∀ n, Continuous (Kn n)) (hK : Continuous K)
    (hL1 : Tendsto (fun n => ∫ x in (0 : ℝ)..1, |Kn n x - K x|) atTop (𝓝 0))
    (x : ℝ) (hx : x ∈ Icc (0 : ℝ) 1) :
    Tendsto (fun n => warp (Kn n) x) atTop (𝓝 (warp K x)) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  apply squeeze_zero (fun n => norm_nonneg _)
    (fun n => by simpa only [Real.norm_eq_abs] using
      abs_warp_sub_le_integral_abs (Kn n) K (hn n) hK x hx)
  simpa using hL1.const_mul 2

/-- `L¹` convergence also controls the actual warp slope at every physical point. -/
theorem tendsto_warpSlope_of_l1 (Kn : ℕ → ℝ → ℝ) (K : ℝ → ℝ)
    (hn : ∀ n, Continuous (Kn n)) (hK : Continuous K)
    (hL1 : Tendsto (fun n => ∫ x in (0 : ℝ)..1, |Kn n x - K x|) atTop (𝓝 0))
    (x : ℝ) (hx : x ∈ Icc (0 : ℝ) 1) :
    Tendsto (fun n => warpSlope (Kn n) x) atTop (𝓝 (warpSlope K x)) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  apply squeeze_zero (fun n => norm_nonneg _)
    (fun n => by simpa only [Real.norm_eq_abs] using
      abs_warpSlope_sub_le_integral_abs (Kn n) K (hn n) hK x hx)
  simpa using hL1.const_mul 2

/-- Curvature `L¹` convergence gives uniform convergence of the actual warp on the
whole physical interval, with the same error bound at every point. -/
theorem tendstoUniformlyOn_warp_of_l1 (Kn : ℕ → ℝ → ℝ) (K : ℝ → ℝ)
    (hn : ∀ n, Continuous (Kn n)) (hK : Continuous K)
    (hL1 : Tendsto (fun n => ∫ x in (0 : ℝ)..1, |Kn n x - K x|) atTop (𝓝 0)) :
    TendstoUniformlyOn (fun n => warp (Kn n)) (warp K) atTop (Icc (0 : ℝ) 1) := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  have hsmall : ∀ᶠ n in atTop, 2 * (∫ x in (0 : ℝ)..1, |Kn n x - K x|) < ε := by
    have hlimit := hL1.const_mul 2
    simp only [mul_zero] at hlimit
    exact hlimit.eventually (gt_mem_nhds hε)
  filter_upwards [hsmall] with n hnε x hx
  rw [Real.dist_eq, abs_sub_comm]
  exact (abs_warp_sub_le_integral_abs (Kn n) K (hn n) hK x hx).trans_lt hnε

/-- Curvature `L¹` convergence gives uniform convergence of the actual warp slope
on the whole physical interval. -/
theorem tendstoUniformlyOn_warpSlope_of_l1 (Kn : ℕ → ℝ → ℝ) (K : ℝ → ℝ)
    (hn : ∀ n, Continuous (Kn n)) (hK : Continuous K)
    (hL1 : Tendsto (fun n => ∫ x in (0 : ℝ)..1, |Kn n x - K x|) atTop (𝓝 0)) :
    TendstoUniformlyOn (fun n => warpSlope (Kn n)) (warpSlope K) atTop (Icc (0 : ℝ) 1) := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  have hsmall : ∀ᶠ n in atTop, 2 * (∫ x in (0 : ℝ)..1, |Kn n x - K x|) < ε := by
    have hlimit := hL1.const_mul 2
    simp only [mul_zero] at hlimit
    exact hlimit.eventually (gt_mem_nhds hε)
  filter_upwards [hsmall] with n hnε x hx
  rw [Real.dist_eq, abs_sub_comm]
  exact (abs_warpSlope_sub_le_integral_abs (Kn n) K (hn n) hK x hx).trans_lt hnε

private theorem abs_density_le
    (B f f1 K r r1 r2 : ℝ)
    (hB : 0 ≤ B)
    (hf : |f| ≤ B) (hf1 : |f1| ≤ B) (hK : |K| ≤ B)
    (hr : |r| ≤ B) (hr1 : |r1| ≤ B) (hr2 : |r2| ≤ B) :
    |meridionalActionDensity f f1 K r r1 r2| ≤
      B * (B ^ 2 + 2 * B ^ 2 + B ^ 2) ^ 2 +
        B ^ 3 * (B ^ 2 + B ^ 2 / 2) + B ^ 2 * B * B ^ 2 := by
  have hB0 : 0 ≤ B := hB
  have hfr2 : |f * r2| ≤ B ^ 2 := by
    rw [abs_mul]
    calc
      |f| * |r2| ≤ B * B :=
        mul_le_mul hf hr2 (abs_nonneg r2) hB0
      _ = B ^ 2 := by ring
  have hf1r1 : |f1 * r1| ≤ B ^ 2 := by
    rw [abs_mul]
    calc
      |f1| * |r1| ≤ B * B :=
        mul_le_mul hf1 hr1 (abs_nonneg r1) hB0
      _ = B ^ 2 := by ring
  have hKr : |K * r| ≤ B ^ 2 := by
    rw [abs_mul]
    calc
      |K| * |r| ≤ B * B :=
        mul_le_mul hK hr (abs_nonneg r) hB0
      _ = B ^ 2 := by ring
  have htwof1r1 : |2 * f1 * r1| ≤ 2 * B ^ 2 := by
    calc
      |2 * f1 * r1| = 2 * |f1 * r1| := by
        rw [mul_assoc, abs_mul]
        norm_num
      _ ≤ 2 * B ^ 2 :=
        mul_le_mul_of_nonneg_left hf1r1 (by norm_num)
  have hfactor :
      |(f * r2 + 2 * f1 * r1 - K * r)| ≤
        B ^ 2 + 2 * B ^ 2 + B ^ 2 := by
    calc
      |(f * r2 + 2 * f1 * r1 - K * r)| =
          |f * r2 + 2 * f1 * r1 - K * r| := rfl
      _ ≤ |f * r2 + 2 * f1 * r1| + |K * r| := abs_sub _ _
      _ ≤ (|f * r2| + |2 * f1 * r1|) + |K * r| := by
        gcongr
        exact abs_add_le _ _
      _ ≤ (B ^ 2 + 2 * B ^ 2) + B ^ 2 := by gcongr
  have hfactorSq :
      |(f * r2 + 2 * f1 * r1 - K * r)| ^ 2 ≤
        (B ^ 2 + 2 * B ^ 2 + B ^ 2) ^ 2 :=
    pow_le_pow_left₀ (abs_nonneg _) hfactor 2
  have htermOne :
      |f * (f * r2 + 2 * f1 * r1 - K * r) ^ 2| ≤
        B * (B ^ 2 + 2 * B ^ 2 + B ^ 2) ^ 2 := by
    rw [abs_mul, abs_pow]
    exact mul_le_mul hf hfactorSq (sq_nonneg _) hB0
  have hfr1 : |f * r1| ≤ B ^ 2 := by
    rw [abs_mul]
    calc
      |f| * |r1| ≤ B * B :=
        mul_le_mul hf hr1 (abs_nonneg r1) hB0
      _ = B ^ 2 := by ring
  have hf1r : |f1 * r| ≤ B ^ 2 := by
    rw [abs_mul]
    calc
      |f1| * |r| ≤ B * B :=
        mul_le_mul hf1 hr (abs_nonneg r) hB0
      _ = B ^ 2 := by ring
  have hf1rHalf : |f1 * r / 2| ≤ B ^ 2 / 2 := by
    calc
      |f1 * r / 2| = |f1 * r| / 2 := by
        rw [abs_div]
        norm_num
      _ ≤ B ^ 2 / 2 := by
        exact div_le_div_of_nonneg_right hf1r (by norm_num)
  have hinner : |f * r1 + f1 * r / 2| ≤ B ^ 2 + B ^ 2 / 2 := by
    calc
      |f * r1 + f1 * r / 2| ≤ |f * r1| + |f1 * r / 2| :=
        abs_add_le _ _
      _ ≤ B ^ 2 + B ^ 2 / 2 := add_le_add hfr1 hf1rHalf
  have hKf1 : |K * f1| ≤ B ^ 2 := by
    rw [abs_mul]
    calc
      |K| * |f1| ≤ B * B :=
        mul_le_mul hK hf1 (abs_nonneg f1) hB0
      _ = B ^ 2 := by ring
  have hKf1r : |K * f1 * r| ≤ B ^ 3 := by
    rw [abs_mul]
    calc
      |K * f1| * |r| ≤ B ^ 2 * B :=
        mul_le_mul hKf1 hr (abs_nonneg r) (by positivity)
      _ = B ^ 3 := by ring
  have htermTwo :
      |K * f1 * r * (f * r1 + f1 * r / 2)| ≤
        B ^ 3 * (B ^ 2 + B ^ 2 / 2) := by
    rw [abs_mul]
    exact mul_le_mul hKf1r hinner (abs_nonneg _) (by positivity)
  have hKsq : |K| ^ 2 ≤ B ^ 2 :=
    pow_le_pow_left₀ (abs_nonneg K) hK 2
  have hrsq : |r| ^ 2 ≤ B ^ 2 :=
    pow_le_pow_left₀ (abs_nonneg r) hr 2
  have htermThree : |K ^ 2 * f * r ^ 2| ≤ B ^ 2 * B * B ^ 2 := by
    rw [abs_mul, abs_mul, abs_pow, abs_pow]
    gcongr
  rw [meridionalActionDensity, sub_eq_add_neg]
  calc
    |f * (f * r2 + 2 * f1 * r1 - K * r) ^ 2 +
          -(K * f1 * r * (f * r1 + f1 * r / 2)) + K ^ 2 * f * r ^ 2| ≤
        |f * (f * r2 + 2 * f1 * r1 - K * r) ^ 2| +
          |-(K * f1 * r * (f * r1 + f1 * r / 2))| + |K ^ 2 * f * r ^ 2| :=
      abs_add_three _ _ _
    _ ≤ B * (B ^ 2 + 2 * B ^ 2 + B ^ 2) ^ 2 +
          B ^ 3 * (B ^ 2 + B ^ 2 / 2) + B ^ 2 * B * B ^ 2 := by
      simpa only [abs_neg] using add_le_add (add_le_add htermOne htermTwo) htermThree

private theorem primitive_bounds (K : ℝ → ℝ) (hK : Continuous K) (B : ℝ)
    (hbound : ∀ x ∈ Icc (0 : ℝ) 1, |K x| ≤ B) (x : ℝ) (hx : x ∈ Icc (0 : ℝ) 1) :
    |warp K x| ≤ 2 + 2 * B ∧ |warpSlope K x| ≤ 2 + 2 * B := by
  have hi : (∫ s in (0 : ℝ)..1, |K s|) ≤ B := by
    calc
      (∫ s in (0 : ℝ)..1, |K s|) ≤ ∫ _s in (0 : ℝ)..1, B :=
        intervalIntegral.integral_mono_on (by norm_num)
          (hK.abs.intervalIntegrable 0 1) intervalIntegrable_const hbound
      _ = B := by simp
  have hf := abs_integral_weight_le K (fun s => x - s) hK
    (continuous_const.sub continuous_id) x hx (by
      intro s hs
      rw [abs_of_nonneg (sub_nonneg.mpr hs.2)]
      linarith [hs.1, hx.2])
  have hf1 := abs_integral_weight_le K (fun _ => 1) hK continuous_const x hx
    (by intro s hs; norm_num)
  simp only [one_mul] at hf1
  constructor
  · calc
      |warp K x| ≤ |2 * x| + |2 * ∫ s in (0 : ℝ)..x, (x - s) * K s| :=
        abs_sub _ _
      _ ≤ 2 + 2 * B := by
        rw [abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2),
          abs_of_nonneg hx.1]
        linarith [hx.2]
  · calc
      |warpSlope K x| ≤ |(2 : ℝ)| + |2 * ∫ s in (0 : ℝ)..x, K s| := abs_sub _ _
      _ ≤ 2 + 2 * B := by
        rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
        linarith

private theorem tendsto_density {ι : Type*} {l : Filter ι}
    {fn f1n Kn : ι → ℝ} {f f1 K r r1 r2 : ℝ}
    (hf : Tendsto fn l (𝓝 f)) (hf1 : Tendsto f1n l (𝓝 f1))
    (hK : Tendsto Kn l (𝓝 K)) :
    Tendsto (fun n => meridionalActionDensity (fn n) (f1n n) (Kn n) r r1 r2)
      l (𝓝 (meridionalActionDensity f f1 K r r1 r2)) := by
  unfold meridionalActionDensity
  exact ((hf.mul (((hf.mul_const r2).add ((hf1.const_mul 2).mul_const r1)).sub
    (hK.mul_const r) |>.pow 2)).sub
      (((hK.mul hf1).mul_const r).mul
        ((hf.mul_const r1).add ((hf1.mul_const r).div_const 2)))) |>.add
          (((hK.pow 2).mul hf).mul_const (r ^ 2))

/-- Curvature `L¹` and almost-everywhere convergence preserve the complete action
of the same fixed smooth probe under one common physical curvature bound. -/
theorem tendsto_meridionalAction_of_l1_of_ae (Kn : ℕ → ℝ → ℝ) (K r : ℝ → ℝ)
    (hn : ∀ n, Continuous (Kn n)) (hK : Continuous K) (hr : ContDiff ℝ ∞ r)
    (B : ℝ) (hbound : ∀ n x, x ∈ Icc (0 : ℝ) 1 → |Kn n x| ≤ B)
    (hL1 : Tendsto (fun n => ∫ x in (0 : ℝ)..1, |Kn n x - K x|) atTop (𝓝 0))
    (hae : ∀ᵐ x ∂volume.restrict (Icc (0 : ℝ) 1),
      Tendsto (fun n => Kn n x) atTop (𝓝 (K x))) :
    Tendsto (fun n => meridionalAction (Kn n) r) atTop (𝓝 (meridionalAction K r)) := by
  have hr1 := hr.continuous_deriv (by simp)
  have hr2 := (contDiff_infty_iff_deriv.mp hr).2.continuous_deriv (by simp)
  obtain ⟨R, hR⟩ := isCompact_Icc.bddAbove_image
    ((hr.continuous.abs.add hr1.abs).add hr2.abs).continuousOn
  let C := max (max 0 B) (max (2 + 2 * B) R)
  have hC : 0 ≤ C := (le_max_left 0 B).trans (le_max_left _ _)
  have hBC : B ≤ C := (le_max_right 0 B).trans (le_max_left _ _)
  have hfC : 2 + 2 * B ≤ C := (le_max_left _ _).trans (le_max_right _ _)
  have hRC : R ≤ C := (le_max_right _ _).trans (le_max_right _ _)
  have hjets (x : ℝ) (hx : x ∈ Icc (0 : ℝ) 1) :
      |r x| ≤ C ∧ |deriv r x| ≤ C ∧ |deriv (deriv r) x| ≤ C := by
    have ht : |r x| + |deriv r x| + |deriv (deriv r) x| ≤ R :=
      hR (mem_image_of_mem _ hx)
    exact ⟨by linarith [abs_nonneg (deriv r x), abs_nonneg (deriv (deriv r) x)],
      by linarith [abs_nonneg (r x), abs_nonneg (deriv (deriv r) x)],
      by linarith [abs_nonneg (r x), abs_nonneg (deriv r x)]⟩
  simp only [meridionalAction, intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1),
    ← integral_Icc_eq_integral_Ioc]
  apply tendsto_integral_of_dominated_convergence (fun _ =>
    C * (C ^ 2 + 2 * C ^ 2 + C ^ 2) ^ 2 +
      C ^ 3 * (C ^ 2 + C ^ 2 / 2) + C ^ 2 * C * C ^ 2)
  · intro n
    exact (meridionalAction_integrand_continuous (Kn n) r (hn n) hr).aestronglyMeasurable
  · exact integrable_const _
  · intro n
    filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
    have hp := primitive_bounds (Kn n) (hn n) B (hbound n) x hx
    have hj := hjets x hx
    rw [Real.norm_eq_abs]
    exact abs_density_le C _ _ _ _ _ _ hC (hp.1.trans hfC) (hp.2.trans hfC)
      ((hbound n x hx).trans hBC) hj.1 hj.2.1 hj.2.2
  · filter_upwards [ae_restrict_mem measurableSet_Icc, hae] with x hx hax
    exact tendsto_density (tendsto_warp_of_l1 Kn K hn hK hL1 x hx)
      (tendsto_warpSlope_of_l1 Kn K hn hK hL1 x hx) hax

/-- The actual normalized warp is affine along contraction toward curvature two. -/
theorem warp_affine_two (K : ℝ → ℝ) (hK : Continuous K) (t x : ℝ) :
    warp (fun s => (1 - t) * K s + 2 * t) x =
      (1 - t) * warp K x + t * warp (fun _ => 2) x := by
  have hiK : IntervalIntegrable (fun s : ℝ => (x - s) * K s) volume 0 x :=
    ((continuous_const.sub continuous_id).mul hK).intervalIntegrable 0 x
  have hi2 : IntervalIntegrable (fun s : ℝ => (x - s) * 2) volume 0 x :=
    ((continuous_const.sub continuous_id).mul continuous_const).intervalIntegrable 0 x
  have hi : (∫ s in (0 : ℝ)..x, (x - s) * ((1 - t) * K s + 2 * t)) =
      (1 - t) * (∫ s in (0 : ℝ)..x, (x - s) * K s) +
        t * (∫ s in (0 : ℝ)..x, (x - s) * 2) := by
    calc
      _ = ∫ s in (0 : ℝ)..x, (1 - t) * ((x - s) * K s) + t * ((x - s) * 2) := by
        apply intervalIntegral.integral_congr
        intro s hs
        ring
      _ = _ := by
        rw [intervalIntegral.integral_add (hiK.const_mul _) (hi2.const_mul _),
          intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
  simp only [warp, hi]
  ring

/-- The actual warp slope is affine along the same contraction. -/
theorem warpSlope_affine_two (K : ℝ → ℝ) (hK : Continuous K) (t x : ℝ) :
    warpSlope (fun s => (1 - t) * K s + 2 * t) x =
      (1 - t) * warpSlope K x + t * warpSlope (fun _ => 2) x := by
  have hi : (∫ s in (0 : ℝ)..x, (1 - t) * K s + 2 * t) =
      (1 - t) * (∫ s in (0 : ℝ)..x, K s) + t * (∫ _s in (0 : ℝ)..x, (2 : ℝ)) := by
    rw [intervalIntegral.integral_add ((hK.intervalIntegrable 0 x).const_mul _)
      intervalIntegrable_const, intervalIntegral.integral_const_mul]
    simp only [intervalIntegral.integral_const, sub_zero, smul_eq_mul]
    ring
  simp only [warpSlope, hi]
  ring

/-- For one fixed smooth probe, its complete action is continuous throughout
an affine curvature family, including at the original curvature at parameter zero. -/
theorem continuous_meridionalAction_affine (K r : ℝ → ℝ)
    (hK : Continuous K) (hr : ContDiff ℝ ∞ r) :
    Continuous (fun t : ℝ => meridionalAction (fun x => (1 - t) * K x + 2 * t) r) := by
  have hf := warp_continuous K hK
  have hf1 := warpSlope_continuous K hK
  have hr0 := hr.continuous
  have hr1 := hr.continuous_deriv (by simp)
  have hr2 := (contDiff_infty_iff_deriv.mp hr).2.continuous_deriv (by simp)
  simp only [meridionalAction, warp_affine_two K hK, warpSlope_affine_two K hK,
    warp_two, warpSlope_two,
    intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1),
    ← integral_Icc_eq_integral_Ioc]
  apply continuous_parametric_integral_of_continuous _ isCompact_Icc
  unfold Function.uncurry meridionalActionDensity
  fun_prop

end RicciFlowSharpEstimate.Geometry.AreaProfile
