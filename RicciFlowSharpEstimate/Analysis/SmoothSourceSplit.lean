/-
Copyright (c) 2026 Ziyang Qin. All rights reserved.
No license is granted by this file.
Authors: Ziyang Qin
-/
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.Function.LpOrder
import Mathlib.MeasureTheory.Function.LpSeminorm.SMul
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# Smooth nonnegative source splitting with weighted strong convergence

Square-root regularization splits each original smooth source exactly, with
the same index, into two globally nonnegative smooth sources. Strong limits
are retained for the original weighted positive and negative parts even when
the continuous nonnegative weight vanishes.
-/

noncomputable section

namespace RicciFlowSharpEstimate.Analysis

open Set MeasureTheory Filter
open scoped ContDiff ENNReal Topology

local notation "sourceμ" => volume.restrict (Ioo (0 : ℝ) 1)

private def sourceEpsilon (n : ℕ) : ℝ := 1 / ((n : ℝ) + 1)

private theorem sourceEpsilon_pos (n : ℕ) : 0 < sourceEpsilon n := by
  unfold sourceEpsilon
  positivity

private def sourceRegularizer (ε t : ℝ) : ℝ := (Real.sqrt (t ^ 2 + ε ^ 2) + t) / 2

private theorem sourceRegularizer_nonneg (ε t : ℝ) : 0 ≤ sourceRegularizer ε t := by
  have hs : |t| ≤ Real.sqrt (t ^ 2 + ε ^ 2) := Real.abs_le_sqrt (by nlinarith [sq_nonneg ε])
  unfold sourceRegularizer
  linarith [neg_le_abs t]

private theorem sourceRegularizer_sub_neg (ε t : ℝ) :
    sourceRegularizer ε t - sourceRegularizer ε (-t) = t := by
  simp only [sourceRegularizer, neg_sq]
  ring

private theorem sourceRegularizer_contDiff (ε : ℝ) (hε : 0 < ε) (q : ℝ → ℝ)
    (hq : ContDiff ℝ ∞ q) : ContDiff ℝ ∞ (fun x => sourceRegularizer ε (q x)) := by
  have hpos (x : ℝ) : 0 < q x ^ 2 + ε ^ 2 :=
    add_pos_of_nonneg_of_pos (sq_nonneg _) (sq_pos_of_pos hε)
  change ContDiff ℝ ∞ (fun x => (Real.sqrt (q x ^ 2 + ε ^ 2) + q x) / 2)
  exact ((((hq.pow 2).add contDiff_const).sqrt (fun x => (hpos x).ne')).add hq).div_const 2

private theorem sourceRegularizer_error_bound (ε t : ℝ) (hε : 0 ≤ ε) :
    |sourceRegularizer ε t - max t 0| ≤ ε / 2 := by
  have hlo : |t| ≤ Real.sqrt (t ^ 2 + ε ^ 2) :=
    Real.abs_le_sqrt (by nlinarith [sq_nonneg ε])
  have hhi : Real.sqrt (t ^ 2 + ε ^ 2) ≤ |t| + ε := by
    apply Real.sqrt_le_iff.mpr
    refine ⟨add_nonneg (abs_nonneg _) hε, ?_⟩
    nlinarith [sq_abs t, mul_nonneg (abs_nonneg t) hε]
  have hm : max t 0 = (|t| + t) / 2 := by
    rcases le_total 0 t with ht | ht
    · rw [max_eq_left ht, abs_of_nonneg ht]
      ring
    · rw [max_eq_right ht, abs_of_nonpos ht]
      ring
  rw [hm]
  unfold sourceRegularizer
  apply abs_le.mpr
  constructor <;> linarith

private theorem sourceRegularizer_weighted_error_bound (ε w t s : ℝ) (hε : 0 ≤ ε) :
    |w * sourceRegularizer ε t - w * max s 0| ≤
      ε / 2 * |w| + |w * t - w * s| := by
  calc
    _ ≤ |w * sourceRegularizer ε t - w * max t 0| + |w * max t 0 - w * max s 0| :=
      abs_sub_le _ _ _
    _ = |w| * |sourceRegularizer ε t - max t 0| + |w| * |max t 0 - max s 0| := by
      rw [← mul_sub, ← mul_sub, abs_mul, abs_mul]
    _ ≤ |w| * (ε / 2) + |w| * |t - s| :=
      add_le_add
        (mul_le_mul_of_nonneg_left (sourceRegularizer_error_bound ε t hε) (abs_nonneg _))
        (mul_le_mul_of_nonneg_left (abs_max_sub_max_le_abs t s 0) (abs_nonneg _))
    _ = _ := by
      rw [← abs_mul, mul_sub]
      ring

private theorem source_weighted_max (w t : ℝ) (hw : 0 ≤ w) :
    w * max t 0 = max (w * t) 0 := by
  rcases le_total 0 t with ht | ht
  · rw [max_eq_left ht, max_eq_left (mul_nonneg hw ht)]
  · rw [max_eq_right ht, max_eq_right (mul_nonpos_of_nonneg_of_nonpos hw ht), mul_zero]

private theorem source_continuous_memLp (f : ℝ → ℝ) (hf : Continuous f) : MemLp f 2 sourceμ := by
  obtain ⟨x, hx, hmax⟩ := isCompact_Icc.exists_isMaxOn
    (show (Icc (0 : ℝ) 1).Nonempty from ⟨0, by norm_num⟩) hf.norm.continuousOn
  apply MemLp.of_bound hf.aestronglyMeasurable ‖f x‖
  filter_upwards [self_mem_ae_restrict measurableSet_Ioo] with y hy
  exact hmax ⟨hy.1.le, hy.2.le⟩

private theorem source_weighted_max_memLp (a q : ℝ → ℝ)
    (ha : ∀ x ∈ Icc (0 : ℝ) 1, 0 ≤ a x) (hq : MemLp (fun x => a x * q x) 2 sourceμ) :
    MemLp (fun x => a x * max (q x) 0) 2 sourceμ := by
  have hm : MemLp (fun x => max (a x * q x) 0) 2 sourceμ := by
    change MemLp ((fun x => a x * q x) ⊔ (fun _ : ℝ => (0 : ℝ))) 2 sourceμ
    exact hq.sup (memLp_const (0 : ℝ))
  have heq : (fun x => a x * max (q x) 0) =ᵐ[sourceμ]
      (fun x => max (a x * q x) 0) := by
    filter_upwards [self_mem_ae_restrict measurableSet_Ioo] with x hx
    exact source_weighted_max (a x) (q x) (ha x ⟨hx.1.le, hx.2.le⟩)
  exact (memLp_congr_ae heq).mpr hm

private theorem source_positive_strong (q : ℕ → ℝ → ℝ) (q0 a : ℝ → ℝ)
    (hq : ∀ n, ContDiff ℝ ∞ (q n)) (ha : Continuous a)
    (hapos : ∀ x ∈ Icc (0 : ℝ) 1, 0 ≤ a x)
    (hq0 : MemLp (fun x => a x * q0 x) 2 sourceμ)
    (hstrong : Tendsto
      (fun n => eLpNorm (fun x => a x * q n x - a x * q0 x) 2 sourceμ) atTop (𝓝 0)) :
    Tendsto (fun n => eLpNorm
      (fun x => a x * sourceRegularizer (sourceEpsilon n) (q n x) - a x * max (q0 x) 0)
      2 sourceμ) atTop (𝓝 0) := by
  have haLp := source_continuous_memLp a ha
  have hqLp (n : ℕ) := source_continuous_memLp
    (fun x => a x * q n x) (ha.mul (hq n).continuous)
  have hp0 := source_weighted_max_memLp a q0 hapos hq0
  have hpLp (n : ℕ) := source_continuous_memLp
    (fun x => a x * sourceRegularizer (sourceEpsilon n) (q n x))
    (ha.mul (sourceRegularizer_contDiff (sourceEpsilon n)
      (sourceEpsilon_pos n) (q n) (hq n)).continuous)
  have hbound (n : ℕ) : eLpNorm
      (fun x => a x * sourceRegularizer (sourceEpsilon n) (q n x) - a x * max (q0 x) 0)
      2 sourceμ ≤
      ‖sourceEpsilon n / 2‖ₑ * eLpNorm a 2 sourceμ +
        eLpNorm (fun x => a x * q n x - a x * q0 x) 2 sourceμ := by
    have hmeas : AEStronglyMeasurable
        (fun x => a x * sourceRegularizer (sourceEpsilon n) (q n x) -
          a x * max (q0 x) 0) sourceμ := ((hpLp n).sub hp0).aestronglyMeasurable
    have hemeas : AEStronglyMeasurable
        (fun x => a x * q n x - a x * q0 x) sourceμ :=
      ((hqLp n).sub hq0).aestronglyMeasurable
    calc
      _ ≤ eLpNorm (fun x => sourceEpsilon n / 2 * ‖a x‖ +
          ‖a x * q n x - a x * q0 x‖) 2 sourceμ := by
        apply eLpNorm_mono_ae_real hmeas
        exact Eventually.of_forall fun x => by
          simpa only [Real.norm_eq_abs] using
            sourceRegularizer_weighted_error_bound (sourceEpsilon n) (a x) (q n x) (q0 x)
              (sourceEpsilon_pos n).le
      _ ≤ eLpNorm (fun x => sourceEpsilon n / 2 * ‖a x‖) 2 sourceμ +
          eLpNorm (fun x => ‖a x * q n x - a x * q0 x‖) 2 sourceμ :=
        eLpNorm_add_le (by norm_num)
      _ = _ := by
        change eLpNorm ((sourceEpsilon n / 2) • (fun x => ‖a x‖)) 2 sourceμ +
          eLpNorm (fun x => ‖a x * q n x - a x * q0 x‖) 2 sourceμ = _
        rw [eLpNorm_const_smul, eLpNorm_norm a ha.aestronglyMeasurable,
          eLpNorm_norm (fun x => a x * q n x - a x * q0 x) hemeas]
  have hε : Tendsto (fun n => sourceEpsilon n / 2) atTop (𝓝 (0 : ℝ)) := by
    have h := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).div_const 2
    simpa only [sourceEpsilon, zero_div] using h
  have hεnorm : Tendsto (fun n => ‖sourceEpsilon n / 2‖ₑ) atTop (𝓝 (0 : ℝ≥0∞)) := by
    simpa only [enorm_zero] using hε.enorm
  have hsmallRaw := ENNReal.Tendsto.mul_const
    (b := eLpNorm a 2 sourceμ) hεnorm (Or.inr haLp.eLpNorm_ne_top)
  have hsmall : Tendsto (fun n => ‖sourceEpsilon n / 2‖ₑ * eLpNorm a 2 sourceμ)
      atTop (𝓝 0) := by
    simpa only [zero_mul] using hsmallRaw
  have hsumRaw := hsmall.add hstrong
  have hsum : Tendsto (fun n => ‖sourceEpsilon n / 2‖ₑ * eLpNorm a 2 sourceμ +
      eLpNorm (fun x => a x * q n x - a x * q0 x) 2 sourceμ) atTop (𝓝 0) := by
    simpa only [zero_add] using hsumRaw
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsum
    (fun _ => zero_le) hbound

/-- Smooth sources admit exact globally nonnegative smooth splits with the
same index and strong weighted limits to the original positive and negative
parts. The weight may vanish; no unweighted regularity or integrability of
the raw limit is assumed. -/
theorem exists_smooth_nonnegative_source_split (q : ℕ → ℝ → ℝ) (q0 a : ℝ → ℝ)
    (hq : ∀ n, ContDiff ℝ ∞ (q n)) (ha : Continuous a)
    (hapos : ∀ x ∈ Icc (0 : ℝ) 1, 0 ≤ a x)
    (hq0 : MemLp (fun x => a x * q0 x) 2 sourceμ)
    (hstrong : Tendsto
      (fun n => eLpNorm (fun x => a x * q n x - a x * q0 x) 2 sourceμ) atTop (𝓝 0)) :
    ∃ gp gm : ℕ → ℝ → ℝ,
      (∀ n, ContDiff ℝ ∞ (gp n) ∧ ContDiff ℝ ∞ (gm n)) ∧
      (∀ n x, 0 ≤ gp n x ∧ 0 ≤ gm n x) ∧
      (∀ n x, gp n x - gm n x = q n x) ∧
      (∀ n, MemLp (fun x => a x * gp n x) 2 sourceμ ∧
        MemLp (fun x => a x * gm n x) 2 sourceμ) ∧
      MemLp (fun x => a x * max (q0 x) 0) 2 sourceμ ∧
      MemLp (fun x => a x * max (-q0 x) 0) 2 sourceμ ∧
      Tendsto (fun n => eLpNorm (fun x => a x * gp n x - a x * max (q0 x) 0)
        2 sourceμ) atTop (𝓝 0) ∧
      Tendsto (fun n => eLpNorm (fun x => a x * gm n x - a x * max (-q0 x) 0)
        2 sourceμ) atTop (𝓝 0) := by
  let gp : ℕ → ℝ → ℝ := fun n x => sourceRegularizer (sourceEpsilon n) (q n x)
  let gm : ℕ → ℝ → ℝ := fun n x => sourceRegularizer (sourceEpsilon n) (-q n x)
  have hgp (n : ℕ) : ContDiff ℝ ∞ (gp n) :=
    sourceRegularizer_contDiff _ (sourceEpsilon_pos n) _ (hq n)
  have hgm (n : ℕ) : ContDiff ℝ ∞ (gm n) :=
    sourceRegularizer_contDiff _ (sourceEpsilon_pos n) _ (hq n).neg
  have hneg0 : MemLp (fun x => a x * (-q0 x)) 2 sourceμ := by
    simpa only [Pi.neg_def, mul_neg] using hq0.neg
  have hnegNorm (n : ℕ) :
      eLpNorm (fun x => a x * (-q n x) - a x * (-q0 x)) 2 sourceμ =
        eLpNorm (fun x => a x * q n x - a x * q0 x) 2 sourceμ := by
    have heq : (fun x => a x * (-q n x) - a x * (-q0 x)) =
        -(fun x => a x * q n x - a x * q0 x) := by
      funext x
      simp only [Pi.neg_apply]
      ring
    rw [heq, eLpNorm_neg]
  have hnegStrong : Tendsto
      (fun n => eLpNorm (fun x => a x * (-q n x) - a x * (-q0 x)) 2 sourceμ)
      atTop (𝓝 0) := by
    simpa only [hnegNorm] using hstrong
  refine ⟨gp, gm, fun n => ⟨hgp n, hgm n⟩,
    fun n x => ⟨sourceRegularizer_nonneg _ _, sourceRegularizer_nonneg _ _⟩,
    fun n x => sourceRegularizer_sub_neg _ _, ?_,
    source_weighted_max_memLp a q0 hapos hq0, ?_, ?_, ?_⟩
  · intro n
    exact ⟨source_continuous_memLp _ (ha.mul (hgp n).continuous),
      source_continuous_memLp _ (ha.mul (hgm n).continuous)⟩
  · exact source_weighted_max_memLp a (fun x => -q0 x) hapos hneg0
  · exact source_positive_strong q q0 a hq ha hapos hq0 hstrong
  · exact source_positive_strong (fun n x => -q n x) (fun x => -q0 x) a
      (fun n => (hq n).neg) ha hapos hneg0 hnegStrong

end RicciFlowSharpEstimate.Analysis
