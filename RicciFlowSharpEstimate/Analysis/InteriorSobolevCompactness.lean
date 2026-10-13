/-
Copyright (c) 2026 Ziyang Qin. All rights reserved.
No license is granted by this file.
Authors: Ziyang Qin
-/
import RicciFlowSharpEstimate.Analysis.IntervalDerivativeEnergy
import RicciFlowSharpEstimate.Analysis.LocallyUniformSubsequence
import Mathlib.Topology.MetricSpace.Equicontinuity
import Mathlib.Topology.Instances.Real.Lemmas

/-!
# Interior compactness from first derivative energy

Uniform square-integral bounds for a sequence and its actual first derivatives
on every interior interval give a locally uniformly convergent subsequence.
-/

noncomputable section

namespace RicciFlowSharpEstimate.Analysis

open Set MeasureTheory Filter Topology

/-- Local first derivative energy bounds produce an actual continuous interior
limit and a strictly increasing locally uniformly convergent subsequence. -/
theorem exists_subseq_locallyUniform_of_local_derivative_energy
    (r : ℕ → ℝ → ℝ) (hr : ∀ n, ContDiff ℝ 1 (r n))
    (hlocal : ∀ a b : ℝ, 0 < a → a < b → b < 1 → ∃ M : ℝ, ∀ n,
      (∫ x in a..b, r n x ^ 2) ≤ M ∧ (∫ x in a..b, deriv (r n) x ^ 2) ≤ M) :
    ∃ g : C(Ioo (0 : ℝ) 1, ℝ), ∃ φ : ℕ → ℕ, StrictMono φ ∧
      TendstoLocallyUniformly (fun n (x : Ioo (0 : ℝ) 1) => r (φ n) x) g atTop := by
  let : LocallyCompactSpace (Ioo (0 : ℝ) 1) :=
    isOpen_Ioo.isOpenEmbedding_subtypeVal.locallyCompactSpace
  let u : ℕ → C(Ioo (0 : ℝ) 1, ℝ) := fun n =>
    ⟨fun x => r n x, (hr n).continuous.comp continuous_subtype_val⟩
  have hnear (x : Ioo (0 : ℝ) 1) : ∃ a b M : ℝ,
      a < x.val ∧ x.val < b ∧ 0 < M ∧ ∀ n,
        (∫ y in a..b, r n y ^ 2) ≤ M ∧ (∫ y in a..b, deriv (r n) y ^ 2) ≤ M := by
    let a := x.val / 2
    let b := (x.val + 1) / 2
    have ha : 0 < a := by dsimp [a]; linarith [x.property.1]
    have hb : b < 1 := by dsimp [b]; linarith [x.property.2]
    have hax : a < x.val := by dsimp [a]; linarith [x.property.1]
    have hxb : x.val < b := by dsimp [b]; linarith [x.property.2]
    obtain ⟨M, hM⟩ := hlocal a b ha (hax.trans hxb) hb
    refine ⟨a, b, max M 0 + 1, hax, hxb, by positivity, ?_⟩
    intro n
    exact ⟨(hM n).1.trans (by linarith [le_max_left M 0]),
      (hM n).2.trans (by linarith [le_max_left M 0])⟩
  have heq : Equicontinuous (fun n => (u n : Ioo (0 : ℝ) 1 → ℝ)) := by
    intro x
    obtain ⟨a, b, M, hax, hxb, hM, hbounds⟩ := hnear x
    apply Metric.equicontinuousAt_iff.mpr
    intro ε hε
    refine ⟨min (min (x.val - a) (b - x.val)) (ε ^ 2 / M),
      lt_min (lt_min (sub_pos.mpr hax) (sub_pos.mpr hxb)) (div_pos (sq_pos_of_pos hε) hM), ?_⟩
    intro y hy n
    have hdist : |y.val - x.val| < min (min (x.val - a) (b - x.val)) (ε ^ 2 / M) := hy
    have hya : a < y.val := by
      have h := (abs_lt.mp (hdist.trans_le ((min_le_left _ _).trans (min_le_left _ _)))).1
      linarith only [h]
    have hyb : y.val < b := by
      have h := (abs_lt.mp (hdist.trans_le ((min_le_left _ _).trans (min_le_right _ _)))).2
      linarith only [h]
    have hxy := sq_sub_le_abs_mul_integral_deriv_sq (r n) (hr n) a b x.val y.val
      ⟨hax.le, hxb.le⟩ ⟨hya.le, hyb.le⟩
    have hscale := mul_le_mul_of_nonneg_left (hbounds n).2 (abs_nonneg (x.val - y.val))
    have hsmall : |x.val - y.val| * M < ε ^ 2 := by
      apply (lt_div_iff₀ hM).mp
      rw [abs_sub_comm]
      exact hdist.trans_le (min_le_right _ _)
    change |r n x.val - r n y.val| < ε
    have hs : (r n x.val - r n y.val) ^ 2 < ε ^ 2 := hxy.trans_lt (hscale.trans_lt hsmall)
    nlinarith only [hs, sq_abs (r n x.val - r n y.val), abs_nonneg (r n x.val - r n y.val), hε]
  have hb : ∀ x : Ioo (0 : ℝ) 1, ∃ B : ℝ, ∀ n, ‖u n x‖ ≤ B := by
    intro x
    obtain ⟨a, b, M, hax, hxb, hM, hbounds⟩ := hnear x
    have hab : a < b := hax.trans hxb
    let N := (2 * M + 2 * (b - a) ^ 2 * M) / (b - a)
    have hN : 0 ≤ N := by dsimp [N]; positivity
    refine ⟨N + 1, ?_⟩
    intro n
    have hpoint := length_mul_sq_le_integral_sq_add_integral_deriv_sq (r n) (hr n)
      a b x.val hab ⟨hax.le, hxb.le⟩
    have hU := mul_le_mul_of_nonneg_left (hbounds n).1 (by norm_num : (0 : ℝ) ≤ 2)
    have hD := mul_le_mul_of_nonneg_left (hbounds n).2 (by positivity : 0 ≤ 2 * (b - a) ^ 2)
    have hs : r n x.val ^ 2 ≤ N := by
      apply (le_div_iff₀ (sub_pos.mpr hab)).mpr
      nlinarith only [hpoint, hU, hD]
    change |r n x.val| ≤ N + 1
    nlinarith only [hs, sq_abs (r n x.val), sq_nonneg (|r n x.val| - 1)]
  exact exists_subseq_tendstoLocallyUniformly_of_equicontinuous u heq hb


/-- A positive interior lower bound for the parabolic weight controls the
ordinary square integral on the smaller interval. -/
theorem mul_integral_sq_le_parabolic_energy (v : ℝ → ℝ) (hv : Continuous v)
    (a b : ℝ) (ha : 0 < a) (hab : a < b) (hb : b < 1) (k : ℕ) :
    (a * (1 - b)) ^ k * (∫ x in a..b, v x ^ 2) ≤
      ∫ x in (0 : ℝ)..1, (x * (1 - x)) ^ k * v x ^ 2 := by
  have hw : Continuous (fun x : ℝ => (x * (1 - x)) ^ k * v x ^ 2) := by fun_prop
  have hlocal : (a * (1 - b)) ^ k * (∫ x in a..b, v x ^ 2) ≤
      ∫ x in a..b, (x * (1 - x)) ^ k * v x ^ 2 := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_mono_on hab.le
      (((hv.pow 2).const_mul _).intervalIntegrable a b) (hw.intervalIntegrable a b)
    intro x hx
    have hprod : a * (1 - b) ≤ x * (1 - x) :=
      mul_le_mul hx.1 (sub_le_sub_left hx.2 1) (sub_nonneg.mpr hb.le) (ha.le.trans hx.1)
    have hpow := pow_le_pow_left₀ (mul_nonneg ha.le (sub_nonneg.mpr hb.le)) hprod k
    exact mul_le_mul_of_nonneg_right hpow (sq_nonneg _)
  have hmono : (∫ x in a..b, (x * (1 - x)) ^ k * v x ^ 2) ≤
      ∫ x in (0 : ℝ)..1, (x * (1 - x)) ^ k * v x ^ 2 := by
    apply intervalIntegral.integral_mono_interval ha.le hab.le hb.le _ (hw.intervalIntegrable 0 1)
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
    exact mul_nonneg (pow_nonneg (mul_nonneg hx.1.le (sub_nonneg.mpr hx.2)) k) (sq_nonneg _)
  exact hlocal.trans hmono

/-- Bounded parabolic H² graph energies of smooth probes give one subsequence
on which both the probes and their actual first derivatives converge locally
uniformly in the physical interior. No endpoint value is prescribed. -/
theorem exists_subseq_locallyUniform_probe_deriv_of_weighted_energy
    (r : ℕ → ℝ → ℝ) (hr : ∀ n, ContDiff ℝ 2 (r n)) (M : ℝ)
    (hbound : ∀ n,
      (∫ x in (0 : ℝ)..1, r n x ^ 2) ≤ M ∧
      (∫ x in (0 : ℝ)..1, x * (1 - x) * deriv (r n) x ^ 2) ≤ M ∧
      (∫ x in (0 : ℝ)..1, (x * (1 - x)) ^ 3 * deriv (deriv (r n)) x ^ 2) ≤ M) :
    ∃ g p : C(Ioo (0 : ℝ) 1, ℝ), ∃ φ : ℕ → ℕ, StrictMono φ ∧
      TendstoLocallyUniformly (fun n (x : Ioo (0 : ℝ) 1) => r (φ n) x) g atTop ∧
      TendstoLocallyUniformly (fun n (x : Ioo (0 : ℝ) 1) => deriv (r (φ n)) x) p atTop := by
  have hM : 0 ≤ M := (intervalIntegral.integral_nonneg zero_le_one
    (fun x _ => sq_nonneg (r 0 x))).trans (hbound 0).1
  have hlocal (a b : ℝ) (ha : 0 < a) (hab : a < b) (hb : b < 1) :
      ∃ N : ℝ, ∀ n, (∫ x in a..b, r n x ^ 2) ≤ N ∧
        (∫ x in a..b, deriv (r n) x ^ 2) ≤ N ∧
        (∫ x in a..b, deriv (deriv (r n)) x ^ 2) ≤ N := by
    let c := a * (1 - b)
    have hc : 0 < c := mul_pos ha (sub_pos.mpr hb)
    refine ⟨M + M / c + M / c ^ 3, ?_⟩
    intro n
    have h0 : (∫ x in a..b, r n x ^ 2) ≤ M :=
      (intervalIntegral.integral_mono_interval ha.le hab.le hb.le
        (Filter.Eventually.of_forall fun x => sq_nonneg (r n x))
        (((hr n).continuous.pow 2).intervalIntegrable 0 1)).trans (hbound n).1
    have h1 : (∫ x in a..b, deriv (r n) x ^ 2) ≤ M / c := by
      apply (le_div_iff₀ hc).mpr
      have h := mul_integral_sq_le_parabolic_energy (deriv (r n))
        ((hr n).continuous_deriv (by norm_num)) a b ha hab hb 1
      simp only [pow_one] at h
      change c * (∫ x in a..b, deriv (r n) x ^ 2) ≤ _ at h
      nlinarith only [h, (hbound n).2.1]
    have h2 : (∫ x in a..b, deriv (deriv (r n)) x ^ 2) ≤ M / c ^ 3 := by
      apply (le_div_iff₀ (pow_pos hc 3)).mpr
      have h := mul_integral_sq_le_parabolic_energy (deriv (deriv (r n)))
        (hr n).deriv'.continuous_deriv_one a b ha hab hb 3
      change c ^ 3 * (∫ x in a..b, deriv (deriv (r n)) x ^ 2) ≤ _ at h
      nlinarith only [h, (hbound n).2.2]
    have hq : 0 ≤ M / c := div_nonneg hM hc.le
    have hq3 : 0 ≤ M / c ^ 3 := div_nonneg hM (pow_nonneg hc.le 3)
    exact ⟨by linarith, by linarith, by linarith⟩
  obtain ⟨g, φ, hφ, hg⟩ := exists_subseq_locallyUniform_of_local_derivative_energy r
    (fun n => (hr n).of_le (by norm_num)) (fun a b ha hab hb => by
      obtain ⟨N, hN⟩ := hlocal a b ha hab hb
      exact ⟨N, fun n => ⟨(hN n).1, (hN n).2.1⟩⟩)
  obtain ⟨p, ψ, hψ, hp⟩ := exists_subseq_locallyUniform_of_local_derivative_energy
    (fun n => deriv (r (φ n))) (fun n => (hr (φ n)).deriv') (fun a b ha hab hb => by
      obtain ⟨N, hN⟩ := hlocal a b ha hab hb
      exact ⟨N, fun n => (hN (φ n)).2⟩)
  refine ⟨g, p, φ ∘ ψ, hφ.comp hψ, ?_, hp⟩
  intro V hV x
  obtain ⟨s, hs, hevent⟩ := hg V hV x
  exact ⟨s, hs, hψ.tendsto_atTop.eventually hevent⟩

end RicciFlowSharpEstimate.Analysis
