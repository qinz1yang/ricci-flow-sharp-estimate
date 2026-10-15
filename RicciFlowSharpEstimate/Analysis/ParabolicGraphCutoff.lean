/-
Copyright (c) 2026 Ziyang Qin. All rights reserved.
No license is granted by this file.
Authors: Ziyang Qin
-/
import RicciFlowSharpEstimate.Analysis.WeakDerivativeEnergy
import RicciFlowSharpEstimate.Analysis.SmoothLeftCutoff
import RicciFlowSharpEstimate.Analysis.ParabolicGraphMultiplication
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Cutting a parabolic weak graph at a double zero

The literal left cut is approached by globally smooth multipliers. The first
two product jets remain the genuine weak product derivatives. The only new
errors lie on shrinking compact interior intervals and are controlled by the
local square integral of the actual second weak derivative.
-/

noncomputable section

namespace RicciFlowSharpEstimate.Analysis

open Set MeasureTheory Filter
open scoped ContDiff Topology ENNReal

local notation "areaμ" => volume.restrict (Ioo (0 : ℝ) 1)

private theorem cutoff_integral_sq_bound
    {f : ℝ → ℝ} {a b B : ℝ} (hab : a < b)
    (hf : ContinuousOn f (Icc a b))
    (hzero : ∀ x, x ∉ Icc a b → f x = 0)
    (hbound : ∀ x ∈ Icc a b, f x ^ 2 ≤ B / (b - a)) :
    MemLp f 2 volume ∧ (∫ x, f x ^ 2) ≤ B := by
  have hfi : IntegrableOn f (Icc a b) volume :=
    hf.integrableOn_compact isCompact_Icc
  have hfi2 : IntegrableOn (fun x ↦ f x ^ 2) (Icc a b) volume :=
    (hf.pow 2).integrableOn_compact isCompact_Icc
  have hzero2 : ∀ x, x ∉ Icc a b → f x ^ 2 = 0 := by
    intro x hx
    simp only [hzero x hx, zero_pow (by decide : 2 ≠ 0)]
  have hi := hfi.integrable_of_forall_notMem_eq_zero hzero
  have hi2 := hfi2.integrable_of_forall_notMem_eq_zero hzero2
  refine ⟨(memLp_two_iff_integrable_sq hi.aestronglyMeasurable).mpr hi2, ?_⟩
  calc
    _ = ∫ x in Icc a b, f x ^ 2 :=
      (setIntegral_eq_integral_of_forall_compl_eq_zero hzero2).symm
    _ = ∫ x in a..b, f x ^ 2 := by
      rw [intervalIntegral.integral_of_le hab.le, integral_Icc_eq_integral_Ioc]
    _ ≤ ∫ _x in a..b, B / (b - a) :=
      intervalIntegral.integral_mono_on hab.le
        ((intervalIntegrable_iff_integrableOn_Icc_of_le hab.le).mpr hfi2)
        intervalIntegrable_const hbound
    _ = B := by
      rw [intervalIntegral.integral_const]
      simp only [smul_eq_mul]
      field_simp [(sub_pos.mpr hab).ne']

private theorem cutoff_eLpNorm_tendsto_of_integral_bound
    {f : ℕ → ℝ → ℝ} {B : ℕ → ℝ}
    (hf : ∀ n, MemLp (f n) 2 volume)
    (hB : ∀ n, (∫ x, f n x ^ 2) ≤ B n)
    (hlim : Tendsto B atTop (𝓝 0)) :
    Tendsto (fun n ↦ eLpNorm (f n) 2 volume) atTop (𝓝 0) := by
  have hmajor : Tendsto (fun n ↦ ENNReal.ofReal (Real.sqrt (B n))) atTop (𝓝 0) := by
    simpa only [Real.sqrt_zero, ENNReal.ofReal_zero] using ENNReal.tendsto_ofReal hlim.sqrt
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hmajor
    (fun _ ↦ zero_le) ?_
  intro n
  change eLpNorm (f n) 2 volume ≤ ENNReal.ofReal (Real.sqrt (B n))
  rw [MemLp.eLpNorm_eq_integral_rpow_norm two_ne_zero ENNReal.ofNat_ne_top (hf n)]
  simpa only [ENNReal.toReal_ofNat, Real.rpow_two, Real.norm_eq_abs, sq_abs,
    ← one_div, ← Real.sqrt_eq_rpow] using
    ENNReal.ofReal_le_ofReal (Real.sqrt_le_sqrt (hB n))

private theorem cutoff_energy_tendsto
    {r p z : ℝ → ℝ} {c : ℝ} {ε : ℕ → ℝ}
    (h : HasParabolicWeakDerivatives r p z) (hc : c ∈ Ioo (0 : ℝ) 1)
    (hε : ∀ n, 0 < ε n) (hwidth : ∀ n, ε n ≤ c / 2)
    (hlim : Tendsto ε atTop (𝓝 0)) :
    Tendsto (fun n ↦ ∫ t in (c - ε n)..c, z t ^ 2) atTop (𝓝 0) := by
  have hhalf : c / 2 ≤ c := by linarith [hc.1]
  have hJ : Icc (c / 2) c ⊆ Ioo (0 : ℝ) 1 := by
    intro x hx
    exact ⟨(by linarith [hc.1, hx.1]), hx.2.trans_lt hc.2⟩
  have hz := (h.memLp_secondDeriv_compact isCompact_Icc hJ).integrable_sq
  have hz' : IntegrableOn (fun t ↦ z t ^ 2) (uIcc (c / 2) c) volume := by
    rw [uIcc_of_le hhalf]
    exact hz
  have hcont : ContinuousOn (fun x ↦ ∫ t in x..c, z t ^ 2) (Icc (c / 2) c) := by
    simpa only [uIcc_of_le hhalf] using intervalIntegral.continuousOn_primitive_interval_left hz'
  have hclim : Tendsto (fun n ↦ c - ε n) atTop (𝓝 c) := by
    simpa only [sub_zero] using tendsto_const_nhds.sub hlim
  have hwithin : Tendsto (fun n ↦ c - ε n) atTop (𝓝[Icc (c / 2) c] c) :=
    tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ hclim
      (Eventually.of_forall fun n ↦ ⟨by linarith [hwidth n], by linarith [hε n]⟩)
  simpa only [Function.comp_def, intervalIntegral.integral_same] using
    (hcont c ⟨hhalf, le_rfl⟩).tendsto.comp hwithin

private theorem cutoff_first_error_bound {e A E f d : ℝ}
    (he : 0 < e) (hA : 0 ≤ A) (hE : 0 ≤ E)
    (hd : |d| ≤ A / e) (hf : f ^ 2 ≤ e * E) :
    (f * d) ^ 2 ≤ A ^ 2 * E / e := by
  have hd2 : d ^ 2 ≤ (A / e) ^ 2 := by
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg d) (div_nonneg hA he.le)).mpr hd
  calc
    _ = f ^ 2 * d ^ 2 := mul_pow _ _ _
    _ ≤ (e * E) * (A / e) ^ 2 :=
      mul_le_mul hf hd2 (sq_nonneg d) (mul_nonneg he.le hE)
    _ = _ := by field_simp [he.ne']

private theorem cutoff_second_error_bound {e B E f d : ℝ}
    (he : 0 < e) (hB : 0 ≤ B) (hE : 0 ≤ E)
    (hd : |d| ≤ B / e ^ 2) (hf : f ^ 2 ≤ e ^ 3 * E) :
    (f * d) ^ 2 ≤ B ^ 2 * E / e := by
  have hd2 : d ^ 2 ≤ (B / e ^ 2) ^ 2 := by
    simpa only [sq_abs] using
      (sq_le_sq₀ (abs_nonneg d) (div_nonneg hB (sq_nonneg e))).mpr hd
  calc
    _ = f ^ 2 * d ^ 2 := mul_pow _ _ _
    _ ≤ (e ^ 3 * E) * (B / e ^ 2) ^ 2 :=
      mul_le_mul hf hd2 (sq_nonneg d) (mul_nonneg (by positivity) hE)
    _ = _ := by field_simp [he.ne']

private theorem cutoff_error_limits
    {r p z : ℝ → ℝ} {c : ℝ} {ε : ℕ → ℝ}
    (h : HasParabolicWeakDerivatives r p z)
    (hr : ContinuousOn r (Ioo (0 : ℝ) 1))
    (hp : ContinuousOn p (Ioo (0 : ℝ) 1))
    (hc : c ∈ Ioo (0 : ℝ) 1) (hrc : r c = 0) (hpc : p c = 0)
    (hε : ∀ n, 0 < ε n) (hwidth : ∀ n, ε n ≤ c / 2)
    (hlim : Tendsto ε atTop (𝓝 0)) :
    (∀ n, MemLp (fun x ↦ r x * deriv (smoothLeftCutoff c (ε n)) x) 2 volume) ∧
    (∀ n, MemLp (fun x ↦ p x * deriv (smoothLeftCutoff c (ε n)) x) 2 volume) ∧
    (∀ n, MemLp (fun x ↦ r x * deriv (deriv (smoothLeftCutoff c (ε n))) x) 2 volume) ∧
    Tendsto (fun n ↦ eLpNorm (fun x ↦ r x * deriv (smoothLeftCutoff c (ε n)) x)
      2 volume) atTop (𝓝 0) ∧
    Tendsto (fun n ↦ eLpNorm (fun x ↦ p x * deriv (smoothLeftCutoff c (ε n)) x)
      2 volume) atTop (𝓝 0) ∧
    Tendsto (fun n ↦ eLpNorm (fun x ↦ r x * deriv (deriv (smoothLeftCutoff c (ε n))) x)
      2 volume) atTop (𝓝 0) := by
  obtain ⟨A, B, hA, hB, hderiv⟩ := exists_smoothLeftCutoff_derivative_bounds
  let E : ℕ → ℝ := fun n ↦ ∫ t in (c - ε n)..c, z t ^ 2
  have hElim : Tendsto E atTop (𝓝 0) := cutoff_energy_tendsto h hc hε hwidth hlim
  have hE (n : ℕ) : 0 ≤ E n :=
    intervalIntegral.integral_nonneg_of_forall (by linarith [hε n]) (fun t ↦ sq_nonneg _)
  have hleft (n : ℕ) : c - ε n ∈ Ioo (0 : ℝ) 1 := by
    constructor <;> linarith [hc.1, hc.2, hwidth n, hε n]
  have hJ (n : ℕ) : Icc (c - ε n) c ⊆ Ioo (0 : ℝ) 1 := by
    intro x hx
    exact ⟨(hleft n).1.trans_le hx.1, hx.2.trans_lt hc.2⟩
  have hdecay (n : ℕ) (x : ℝ) (hx : x ∈ Icc (c - ε n) c) :
      p x ^ 2 ≤ ε n * E n ∧ r x ^ 2 ≤ ε n ^ 3 * E n ∧ r x ^ 2 ≤ ε n * E n := by
    have he := h.sq_le_energy_of_double_zero_left hr hp (hleft n) hc hx hrc hpc
    have hdist : 0 ≤ c - x ∧ c - x ≤ ε n := by constructor <;> linarith [hx.1, hx.2]
    have he1 : ε n ≤ 1 := by linarith [hwidth n, hc.2]
    have hcub : (c - x) ^ 3 ≤ ε n ^ 3 := pow_le_pow_left₀ hdist.1 hdist.2 3
    have hsmall : ε n ^ 3 ≤ ε n := by
      nlinarith only [mul_nonneg (hε n).le (sub_nonneg.mpr he1),
        mul_nonneg (sq_nonneg (ε n)) (sub_nonneg.mpr he1)]
    have hr3 : r x ^ 2 ≤ ε n ^ 3 * E n :=
      he.2.trans (mul_le_mul_of_nonneg_right hcub (hE n))
    exact ⟨he.1.trans (mul_le_mul_of_nonneg_right hdist.2 (hE n)), hr3,
      hr3.trans (mul_le_mul_of_nonneg_right hsmall (hE n))⟩
  have hRD (n : ℕ) :
      MemLp (fun x ↦ r x * deriv (smoothLeftCutoff c (ε n)) x) 2 volume ∧
      (∫ x, (r x * deriv (smoothLeftCutoff c (ε n)) x) ^ 2) ≤ A ^ 2 * E n := by
    apply cutoff_integral_sq_bound (a := c - ε n) (b := c) (B := A ^ 2 * E n)
      (by linarith [hε n])
    · exact (hr.mono (hJ n)).mul
        ((contDiff_smoothLeftCutoff c (ε n)).continuous_deriv (by simp)).continuousOn
    · intro x hx
      simp only [(smoothLeftCutoff_derivatives_eq_zero (hε n) hx).1, mul_zero]
    · intro x hx
      have he := cutoff_first_error_bound (hε n) hA.le (hE n)
        (hderiv c (ε n) (hε n) x hx).1 (hdecay n x hx).2.2
      simpa only [sub_sub_cancel] using he
  have hPD (n : ℕ) :
      MemLp (fun x ↦ p x * deriv (smoothLeftCutoff c (ε n)) x) 2 volume ∧
      (∫ x, (p x * deriv (smoothLeftCutoff c (ε n)) x) ^ 2) ≤ A ^ 2 * E n := by
    apply cutoff_integral_sq_bound (a := c - ε n) (b := c) (B := A ^ 2 * E n)
      (by linarith [hε n])
    · exact (hp.mono (hJ n)).mul
        ((contDiff_smoothLeftCutoff c (ε n)).continuous_deriv (by simp)).continuousOn
    · intro x hx
      simp only [(smoothLeftCutoff_derivatives_eq_zero (hε n) hx).1, mul_zero]
    · intro x hx
      have he := cutoff_first_error_bound (hε n) hA.le (hE n)
        (hderiv c (ε n) (hε n) x hx).1 (hdecay n x hx).1
      simpa only [sub_sub_cancel] using he
  have hRDD (n : ℕ) :
      MemLp (fun x ↦ r x * deriv (deriv (smoothLeftCutoff c (ε n))) x) 2 volume ∧
      (∫ x, (r x * deriv (deriv (smoothLeftCutoff c (ε n))) x) ^ 2) ≤ B ^ 2 * E n := by
    apply cutoff_integral_sq_bound (a := c - ε n) (b := c) (B := B ^ 2 * E n)
      (by linarith [hε n])
    · have hd : ContDiff ℝ ∞ (deriv (smoothLeftCutoff c (ε n))) :=
        (contDiff_infty_iff_deriv.mp (contDiff_smoothLeftCutoff c (ε n))).2
      exact (hr.mono (hJ n)).mul (hd.continuous_deriv (by simp)).continuousOn
    · intro x hx
      simp only [(smoothLeftCutoff_derivatives_eq_zero (hε n) hx).2, mul_zero]
    · intro x hx
      have he := cutoff_second_error_bound (hε n) hB.le (hE n)
        (hderiv c (ε n) (hε n) x hx).2 (hdecay n x hx).2.1
      simpa only [sub_sub_cancel] using he
  have hAE : Tendsto (fun n ↦ A ^ 2 * E n) atTop (𝓝 0) := by
    simpa only [mul_zero] using hElim.const_mul (A ^ 2)
  have hBE : Tendsto (fun n ↦ B ^ 2 * E n) atTop (𝓝 0) := by
    simpa only [mul_zero] using hElim.const_mul (B ^ 2)
  exact ⟨fun n ↦ (hRD n).1, fun n ↦ (hPD n).1, fun n ↦ (hRDD n).1,
    cutoff_eLpNorm_tendsto_of_integral_bound (fun n ↦ (hRD n).1) (fun n ↦ (hRD n).2) hAE,
    cutoff_eLpNorm_tendsto_of_integral_bound (fun n ↦ (hPD n).1) (fun n ↦ (hPD n).2) hAE,
    cutoff_eLpNorm_tendsto_of_integral_bound (fun n ↦ (hRDD n).1) (fun n ↦ (hRDD n).2) hBE⟩

private theorem cutoff_strong_zero_add
    {f g : ℕ → ℝ → ℝ}
    (hf : Tendsto (fun n ↦ eLpNorm (f n) 2 areaμ) atTop (𝓝 0))
    (hg : Tendsto (fun n ↦ eLpNorm (g n) 2 areaμ) atTop (𝓝 0)) :
    Tendsto (fun n ↦ eLpNorm (fun x ↦ f n x + g n x) 2 areaμ) atTop (𝓝 0) := by
  have hmajor : Tendsto
      (fun n ↦ eLpNorm (f n) 2 areaμ + eLpNorm (g n) 2 areaμ) atTop (𝓝 0) := by
    simpa only [zero_add] using hf.add hg
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hmajor
    (fun _ ↦ zero_le) (fun _ ↦ eLpNorm_add_le (by norm_num))

private theorem cutoff_weighted_error_tendsto
    {f : ℕ → ℝ → ℝ} {a : ℝ → ℝ}
    (hf : ∀ n, MemLp (f n) 2 volume)
    (hlim : Tendsto (fun n ↦ eLpNorm (f n) 2 volume) atTop (𝓝 0))
    (ha : Continuous a) (hbound : ∀ x ∈ Ioo (0 : ℝ) 1, |a x| ≤ 1) :
    Tendsto (fun n ↦ eLpNorm (fun x ↦ a x * f n x) 2 areaμ) atTop (𝓝 0) := by
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim
    (fun _ ↦ zero_le) ?_
  intro n
  have hfn : MemLp (f n) 2 areaμ := (hf n).mono_measure Measure.restrict_le_self
  calc
    _ ≤ eLpNorm (f n) 2 areaμ := by
      apply eLpNorm_mono_ae (ha.aestronglyMeasurable.mul hfn.aestronglyMeasurable)
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
      change ‖a x * f n x‖ ≤ ‖f n x‖
      rw [norm_mul, Real.norm_eq_abs (a x)]
      simpa only [one_mul] using
        mul_le_mul_of_nonneg_right (hbound x hx) (norm_nonneg (f n x))
    _ ≤ eLpNorm (f n) 2 volume := eLpNorm_mono_measure _ Measure.restrict_le_self

private theorem cutoff_base_tendsto
    {f : ℝ → ℝ} {c : ℝ} {ε : ℕ → ℝ}
    (hf : MemLp f 2 areaμ) (hε : ∀ n, 0 < ε n)
    (hlim : Tendsto ε atTop (𝓝 0)) :
    Tendsto (fun n ↦ eLpNorm
      (fun x ↦ smoothLeftCutoff c (ε n) x * f x - (if x < c then f x else 0))
      2 areaμ) atTop (𝓝 0) := by
  have hfixed : Tendsto (fun _ : ℕ ↦ eLpNorm (f - f) 2 areaμ) atTop (𝓝 0) := by
    simp only [sub_self, eLpNorm_zero]
    exact tendsto_const_nhds
  have hstep : AEStronglyMeasurable (fun x : ℝ ↦ if x < c then (1 : ℝ) else 0) areaμ := by
    exact (measurable_const.piecewise measurableSet_Iio measurable_const).aestronglyMeasurable
  have hh := strong_L2_mul_of_ae_tendsto_of_ae_abs_le
    (u := fun _ ↦ f) (u0 := f) (a := fun n ↦ smoothLeftCutoff c (ε n))
    (a0 := fun x ↦ if x < c then (1 : ℝ) else 0) (D := 1)
    (fun _ ↦ hf) hf hfixed
    (fun n ↦ (contDiff_smoothLeftCutoff c (ε n)).continuous.aestronglyMeasurable)
    hstep
    (fun n ↦ Eventually.of_forall fun x ↦ by
      rw [abs_of_nonneg (smoothLeftCutoff_mem_Icc c (ε n) x).1]
      exact (smoothLeftCutoff_mem_Icc c (ε n) x).2)
    (Eventually.of_forall fun x ↦ by split_ifs <;> norm_num)
    (Eventually.of_forall fun x ↦ smoothLeftCutoff_tendsto hε hlim x)
  apply hh.2.2.congr' (Eventually.of_forall ?_)
  intro n
  apply eLpNorm_congr_ae
  filter_upwards [] with x
  split_ifs <;> simp

/-- At an interior double zero, shrinking smooth left cutoffs converge in all
three parabolic graph coordinates to the literal left cut. The displayed
derivative fields are the genuine product jets furnished by
`HasParabolicWeakDerivatives.mul_contDiff`; no independent jets or recovery
assumptions occur. -/
private theorem parabolicGraph_tendsto_smoothLeftCutoff_of_width_le
    {r p z : ℝ → ℝ} {c : ℝ} {ε : ℕ → ℝ}
    (h : HasParabolicWeakDerivatives r p z)
    (hr : ContinuousOn r (Ioo (0 : ℝ) 1))
    (hp : ContinuousOn p (Ioo (0 : ℝ) 1))
    (hc : c ∈ Ioo (0 : ℝ) 1) (hrc : r c = 0) (hpc : p c = 0)
    (hε : ∀ n, 0 < ε n) (hwidth : ∀ n, ε n ≤ c / 2)
    (hlim : Tendsto ε atTop (𝓝 0)) :
    Tendsto (fun n ↦ eLpNorm
      ((fun x ↦ r x * smoothLeftCutoff c (ε n) x) -
        (fun x ↦ if x < c then r x else 0)) 2 areaμ) atTop (𝓝 0) ∧
    Tendsto (fun n ↦ eLpNorm
      ((fun x ↦ Real.sqrt (x * (1 - x)) *
        (p x * smoothLeftCutoff c (ε n) x + r x * deriv (smoothLeftCutoff c (ε n)) x)) -
        (fun x ↦ Real.sqrt (x * (1 - x)) * (if x < c then p x else 0)))
      2 areaμ) atTop (𝓝 0) ∧
    Tendsto (fun n ↦ eLpNorm
      ((fun x ↦ x * (1 - x) * Real.sqrt (x * (1 - x)) *
        (z x * smoothLeftCutoff c (ε n) x + 2 * p x * deriv (smoothLeftCutoff c (ε n)) x +
          r x * deriv (deriv (smoothLeftCutoff c (ε n))) x)) -
        (fun x ↦ x * (1 - x) * Real.sqrt (x * (1 - x)) * (if x < c then z x else 0)))
      2 areaμ) atTop (𝓝 0) := by
  let a : ℝ → ℝ := fun x ↦ Real.sqrt (x * (1 - x))
  let b : ℝ → ℝ := fun x ↦ x * (1 - x) * Real.sqrt (x * (1 - x))
  have ha : Continuous a := by dsimp only [a]; fun_prop
  have hb : Continuous b := by dsimp only [b]; fun_prop
  have hw (x : ℝ) (hx : x ∈ Ioo (0 : ℝ) 1) :
      0 ≤ x * (1 - x) ∧ x * (1 - x) ≤ 1 := by
    exact ⟨mul_nonneg hx.1.le (sub_nonneg.mpr hx.2.le), by nlinarith [sq_nonneg x]⟩
  have habound (x : ℝ) (hx : x ∈ Ioo (0 : ℝ) 1) : |a x| ≤ 1 := by
    dsimp only [a]
    rw [abs_of_nonneg (Real.sqrt_nonneg _)]
    simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt (hw x hx).2
  have hbbound (x : ℝ) (hx : x ∈ Ioo (0 : ℝ) 1) : |b x| ≤ 1 := by
    have hsa : 0 ≤ a x := Real.sqrt_nonneg _
    have hsa1 : a x ≤ 1 := (le_abs_self (a x)).trans (habound x hx)
    change |(x * (1 - x)) * a x| ≤ 1
    rw [abs_of_nonneg (mul_nonneg (hw x hx).1 hsa)]
    nlinarith only [(hw x hx).1, (hw x hx).2, hsa, hsa1,
      mul_nonneg (sub_nonneg.mpr (hw x hx).2) hsa]
  obtain ⟨hRD, hPD, hRDD, hRDL, hPDL, hRDDL⟩ :=
    cutoff_error_limits h hr hp hc hrc hpc hε hwidth hlim
  have hRa := cutoff_weighted_error_tendsto hRD hRDL ha habound
  have hPb := cutoff_weighted_error_tendsto hPD hPDL hb hbbound
  have hRb := cutoff_weighted_error_tendsto hRDD hRDDL hb hbbound
  have hRbase := cutoff_base_tendsto (c := c) h.memLp hε hlim
  have hPbase := cutoff_base_tendsto (c := c) h.memLp_weighted_deriv hε hlim
  have hZbase := cutoff_base_tendsto (c := c) h.memLp_weighted_secondDeriv hε hlim
  have hPsum := cutoff_strong_zero_add hPbase hRa
  have hZsum := cutoff_strong_zero_add
    (cutoff_strong_zero_add hZbase (cutoff_strong_zero_add hPb hPb)) hRb
  refine ⟨?_, ?_, ?_⟩
  · apply hRbase.congr' (Eventually.of_forall ?_)
    intro n
    apply eLpNorm_congr_ae
    filter_upwards [] with x
    simp only [Pi.sub_apply]
    ring
  · apply hPsum.congr' (Eventually.of_forall ?_)
    intro n
    apply eLpNorm_congr_ae
    filter_upwards [] with x
    dsimp only [a]
    simp only [Pi.sub_apply]
    split_ifs <;> ring
  · apply hZsum.congr' (Eventually.of_forall ?_)
    intro n
    apply eLpNorm_congr_ae
    filter_upwards [] with x
    dsimp only [b]
    simp only [Pi.sub_apply]
    split_ifs <;> ring

/-- At an interior double zero, any positive widths tending to zero give
convergence of the genuine smooth-multiplier product jets to the literal left
cut in all three parabolic graph coordinates. No uniform width restriction is
needed: the transition eventually lies in a compact interior interval. -/
theorem parabolicGraph_tendsto_smoothLeftCutoff
    {r p z : ℝ → ℝ} {c : ℝ} {ε : ℕ → ℝ}
    (h : HasParabolicWeakDerivatives r p z)
    (hr : ContinuousOn r (Ioo (0 : ℝ) 1))
    (hp : ContinuousOn p (Ioo (0 : ℝ) 1))
    (hc : c ∈ Ioo (0 : ℝ) 1) (hrc : r c = 0) (hpc : p c = 0)
    (hε : ∀ n, 0 < ε n) (hlim : Tendsto ε atTop (𝓝 0)) :
    Tendsto (fun n ↦ eLpNorm
      ((fun x ↦ r x * smoothLeftCutoff c (ε n) x) -
        (fun x ↦ if x < c then r x else 0)) 2 areaμ) atTop (𝓝 0) ∧
    Tendsto (fun n ↦ eLpNorm
      ((fun x ↦ Real.sqrt (x * (1 - x)) *
        (p x * smoothLeftCutoff c (ε n) x + r x * deriv (smoothLeftCutoff c (ε n)) x)) -
        (fun x ↦ Real.sqrt (x * (1 - x)) * (if x < c then p x else 0)))
      2 areaμ) atTop (𝓝 0) ∧
    Tendsto (fun n ↦ eLpNorm
      ((fun x ↦ x * (1 - x) * Real.sqrt (x * (1 - x)) *
        (z x * smoothLeftCutoff c (ε n) x + 2 * p x * deriv (smoothLeftCutoff c (ε n)) x +
          r x * deriv (deriv (smoothLeftCutoff c (ε n))) x)) -
        (fun x ↦ x * (1 - x) * Real.sqrt (x * (1 - x)) * (if x < c then z x else 0)))
      2 areaμ) atTop (𝓝 0) := by
  have hhalf : 0 < c / 2 := div_pos hc.1 (by norm_num)
  have hsmall : ∀ᶠ n in atTop, ε n ≤ c / 2 :=
    (hlim.eventually (gt_mem_nhds hhalf)).mono fun _ hn ↦ hn.le
  obtain ⟨N, hN⟩ := eventually_atTop.1 hsmall
  have htail := parabolicGraph_tendsto_smoothLeftCutoff_of_width_le
    (ε := fun n ↦ ε (n + N)) h hr hp hc hrc hpc
    (fun n ↦ hε (n + N))
    (fun n ↦ hN (n + N) (Nat.le_add_left N n))
    (hlim.comp (tendsto_add_atTop_nat N))
  exact ⟨(tendsto_add_atTop_iff_nat N).mp htail.1,
    (tendsto_add_atTop_iff_nat N).mp htail.2.1,
    (tendsto_add_atTop_iff_nat N).mp htail.2.2⟩

end RicciFlowSharpEstimate.Analysis
