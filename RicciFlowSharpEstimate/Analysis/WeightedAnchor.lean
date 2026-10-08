/-
Copyright (c) 2026 Ziyang Qin. All rights reserved.
No license is granted by this file.
Authors: Ziyang Qin
-/
import Mathlib.Algebra.QuadraticDiscriminant
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Coercivity from a variance estimate and a normalized nonnegative anchor

The anchor controls the constant mode left undetermined by the variance.
All product integrability follows from continuity on the compact unit interval.
-/

open MeasureTheory

namespace RicciFlowSharpEstimate.Analysis

private lemma integral_mul_sq_sub_const {f w : ℝ → ℝ}
    (hf : ContinuousOn f (Set.Icc 0 1)) (hw : ContinuousOn w (Set.Icc 0 1))
    (c : ℝ) :
    (∫ x in (0 : ℝ)..1, w x * (f x - c) ^ 2) =
      (∫ x in (0 : ℝ)..1, w x * (f x) ^ 2) -
        2 * c * (∫ x in (0 : ℝ)..1, w x * f x) +
        c ^ 2 * (∫ x in (0 : ℝ)..1, w x) := by
  have hiw := ContinuousOn.intervalIntegrable_of_Icc (μ := volume) (by norm_num : (0 : ℝ) ≤ 1) hw
  have hiwf : IntervalIntegrable (fun x => w x * f x) volume 0 1 :=
    ContinuousOn.intervalIntegrable_of_Icc (μ := volume)
    (by norm_num : (0 : ℝ) ≤ 1) (hw.mul hf)
  have hiwf2 : IntervalIntegrable (fun x => w x * (f x) ^ 2) volume 0 1 :=
    ContinuousOn.intervalIntegrable_of_Icc (μ := volume)
    (by norm_num : (0 : ℝ) ≤ 1) (hw.mul (hf.pow 2))
  calc
    _ = ∫ x in (0 : ℝ)..1,
        (w x * (f x) ^ 2 - (2 * c) * (w x * f x)) + c ^ 2 * w x := by
      apply intervalIntegral.integral_congr
      intro x _
      ring
    _ = _ := by
      rw [intervalIntegral.integral_add (hiwf2.sub (hiwf.const_mul (2 * c)))
        (hiw.const_mul (c ^ 2)),
        intervalIntegral.integral_sub hiwf2 (hiwf.const_mul (2 * c)),
        intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]

private lemma integral_sq_sub_const {f : ℝ → ℝ}
    (hf : ContinuousOn f (Set.Icc 0 1)) (c : ℝ) :
    (∫ x in (0 : ℝ)..1, (f x - c) ^ 2) =
      (∫ x in (0 : ℝ)..1, (f x) ^ 2) -
        2 * c * (∫ x in (0 : ℝ)..1, f x) + c ^ 2 := by
  simpa using integral_mul_sq_sub_const hf (w := fun _ => 1) continuousOn_const c

private lemma integral_mul_sq_le {f g : ℝ → ℝ}
    (hf : ContinuousOn f (Set.Icc 0 1)) (hg : ContinuousOn g (Set.Icc 0 1)) :
    (∫ x in (0 : ℝ)..1, f x * g x) ^ 2 ≤
      (∫ x in (0 : ℝ)..1, (f x) ^ 2) * (∫ x in (0 : ℝ)..1, (g x) ^ 2) := by
  have hif2 : IntervalIntegrable (fun x => (f x) ^ 2) volume 0 1 :=
    ContinuousOn.intervalIntegrable_of_Icc (μ := volume)
    (by norm_num : (0 : ℝ) ≤ 1) (hf.pow 2)
  have hig2 : IntervalIntegrable (fun x => (g x) ^ 2) volume 0 1 :=
    ContinuousOn.intervalIntegrable_of_Icc (μ := volume)
    (by norm_num : (0 : ℝ) ≤ 1) (hg.pow 2)
  have hifg : IntervalIntegrable (fun x => f x * g x) volume 0 1 :=
    ContinuousOn.intervalIntegrable_of_Icc (μ := volume)
    (by norm_num : (0 : ℝ) ≤ 1) (hf.mul hg)
  have hpoly (t : ℝ) :
      0 ≤ (∫ x in (0 : ℝ)..1, (f x) ^ 2) * (t * t) +
        (2 * (∫ x in (0 : ℝ)..1, f x * g x)) * t +
        (∫ x in (0 : ℝ)..1, (g x) ^ 2) := by
    have hnonneg := intervalIntegral.integral_nonneg_of_forall (μ := volume)
      (by norm_num : (0 : ℝ) ≤ 1) (fun x => sq_nonneg (t * f x + g x))
    have heq : (∫ x in (0 : ℝ)..1, (t * f x + g x) ^ 2) =
        (∫ x in (0 : ℝ)..1, (f x) ^ 2) * (t * t) +
          (2 * (∫ x in (0 : ℝ)..1, f x * g x)) * t +
          (∫ x in (0 : ℝ)..1, (g x) ^ 2) := by
      calc
        _ = ∫ x in (0 : ℝ)..1,
            (t ^ 2 * (f x) ^ 2 + (2 * t) * (f x * g x)) + (g x) ^ 2 := by
          apply intervalIntegral.integral_congr
          intro x _
          ring
        _ = _ := by
          rw [intervalIntegral.integral_add
            ((hif2.const_mul (t ^ 2)).add (hifg.const_mul (2 * t))) hig2,
            intervalIntegral.integral_add
              (hif2.const_mul (t ^ 2)) (hifg.const_mul (2 * t)),
            intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
          ring
    rwa [heq] at hnonneg
  have hdisc := discrim_le_zero hpoly
  dsimp [discrim] at hdisc
  nlinarith only [hdisc]

private lemma sq_sub_le_budget {u t a b P r V : ℝ}
    (ha : 0 < a) (hb : 0 ≤ b) (hP : 0 ≤ P) (hr : 0 ≤ r) (hV : 0 ≤ V)
    (hu : u ^ 2 ≤ b * P) (ht : t ^ 2 ≤ r * V) :
    (u - t) ^ 2 ≤ (b + r / a) * (P + a * V) := by
  have hprod := mul_le_mul_of_nonneg_left
    (mul_le_mul hu ht (sq_nonneg t) (mul_nonneg hb hP)) (sq_nonneg a)
  have hz : (a * u * t) ^ 2 ≤ (a ^ 2 * b * V) * (r * P) := by
    nlinarith only [hprod]
  have hX : 0 ≤ a ^ 2 * b * V := mul_nonneg (mul_nonneg (sq_nonneg a) hb) hV
  have hY : 0 ≤ r * P := mul_nonneg hr hP
  have hcross : -2 * (a * u * t) ≤ a ^ 2 * b * V + r * P := by
    by_contra h
    have hlt : a ^ 2 * b * V + r * P < -2 * (a * u * t) := lt_of_not_ge h
    have hpos₁ : 0 < -2 * (a * u * t) - (a ^ 2 * b * V + r * P) := by
      linarith only [hlt]
    have hpos₂ : 0 < -2 * (a * u * t) + (a ^ 2 * b * V + r * P) := by
      linarith only [hlt, hX, hY]
    have hpos := mul_pos hpos₁ hpos₂
    nlinarith only [hz, hpos, sq_nonneg (a ^ 2 * b * V - r * P)]
  have hu' := mul_le_mul_of_nonneg_left hu ha.le
  have ht' := mul_le_mul_of_nonneg_left ht ha.le
  have hbudget : a * (u - t) ^ 2 ≤ (a * b + r) * (P + a * V) := by
    nlinarith only [hu', ht', hcross]
  have heq : (b + r / a) * (P + a * V) = ((a * b + r) * (P + a * V)) / a := by
    field_simp
  rw [heq]
  exact (le_div_iff₀ ha).2 (by nlinarith only [hbudget])

/-- A nonnegative normalized weight anchors the constant mode of a variance estimate.

The ordinary interval mean is the integral because the interval has length one. -/
theorem integral_sq_le_of_variance_anchor {f w : ℝ → ℝ} {P a b D : ℝ}
    (hf : ContinuousOn f (Set.Icc 0 1)) (hw : ContinuousOn w (Set.Icc 0 1))
    (hw_nonneg : ∀ x ∈ Set.Icc (0 : ℝ) 1, 0 ≤ w x)
    (hw_integral : (∫ x in (0 : ℝ)..1, w x) = 1)
    (hP : 0 ≤ P) (ha : 0 < a) (hb : 0 ≤ b)
    (hbudget : P + a * (∫ x in (0 : ℝ)..1,
      (f x - (∫ v in (0 : ℝ)..1, f v)) ^ 2) ≤ D)
    (hanchor : (∫ x in (0 : ℝ)..1, w x * (f x) ^ 2) ≤ b * P) :
    (∫ x in (0 : ℝ)..1, (f x) ^ 2) ≤
      ((∫ x in (0 : ℝ)..1, (w x) ^ 2) / a + b) * D := by
  let m := ∫ x in (0 : ℝ)..1, f x
  let u := ∫ x in (0 : ℝ)..1, w x * f x
  let V := ∫ x in (0 : ℝ)..1, (f x - m) ^ 2
  let r := ∫ x in (0 : ℝ)..1, (w x - 1) ^ 2
  have hV : 0 ≤ V := intervalIntegral.integral_nonneg_of_forall (μ := volume)
    (by norm_num : (0 : ℝ) ≤ 1) (fun x => sq_nonneg (f x - m))
  have hr : 0 ≤ r := intervalIntegral.integral_nonneg_of_forall (μ := volume)
    (by norm_num : (0 : ℝ) ≤ 1) (fun x => sq_nonneg (w x - 1))
  have hmean : (∫ x in (0 : ℝ)..1, (f x) ^ 2) = V + m ^ 2 := by
    have h := integral_sq_sub_const hf m
    change V = (∫ x in (0 : ℝ)..1, (f x) ^ 2) - 2 * m * m + m ^ 2 at h
    nlinarith only [h]
  have hweight : (∫ x in (0 : ℝ)..1, (w x) ^ 2) = r + 1 := by
    have h := integral_sq_sub_const hw 1
    rw [hw_integral] at h
    change r = (∫ x in (0 : ℝ)..1, (w x) ^ 2) - 2 * 1 * 1 + 1 ^ 2 at h
    linarith only [h]
  have hu : u ^ 2 ≤ b * P := by
    have hnonneg := intervalIntegral.integral_nonneg (μ := volume)
      (by norm_num : (0 : ℝ) ≤ 1)
      (fun x hx => mul_nonneg (hw_nonneg x hx) (sq_nonneg (f x - u)))
    rw [integral_mul_sq_sub_const hf hw u, hw_integral] at hnonneg
    change 0 ≤ (∫ x in (0 : ℝ)..1, w x * (f x) ^ 2) - 2 * u * u + u ^ 2 * 1
      at hnonneg
    nlinarith only [hnonneg, hanchor]
  have hif := ContinuousOn.intervalIntegrable_of_Icc (μ := volume) (by norm_num : (0 : ℝ) ≤ 1) hf
  have hiw := ContinuousOn.intervalIntegrable_of_Icc (μ := volume) (by norm_num : (0 : ℝ) ≤ 1) hw
  have hiwf : IntervalIntegrable (fun x => w x * f x) volume 0 1 :=
    ContinuousOn.intervalIntegrable_of_Icc (μ := volume)
    (by norm_num : (0 : ℝ) ≤ 1) (hw.mul hf)
  have hcross : (∫ x in (0 : ℝ)..1, (w x - 1) * (f x - m)) = u - m := by
    calc
      _ = ∫ x in (0 : ℝ)..1, (w x * f x - m * w x) - f x + m := by
        apply intervalIntegral.integral_congr
        intro x _
        ring
      _ = u - m := by
        rw [intervalIntegral.integral_add ((hiwf.sub (hiw.const_mul m)).sub hif)
          intervalIntegrable_const,
          intervalIntegral.integral_sub (hiwf.sub (hiw.const_mul m)) hif,
          intervalIntegral.integral_sub hiwf (hiw.const_mul m),
          intervalIntegral.integral_const_mul, hw_integral]
        simp [m, u]
  have ht : (u - m) ^ 2 ≤ r * V := by
    have h := integral_mul_sq_le (hw.sub continuousOn_const) (hf.sub continuousOn_const)
      (g := fun x => f x - m) (f := fun x => w x - 1)
    rw [hcross] at h
    exact h
  have hm : m ^ 2 ≤ (b + r / a) * D := by
    have h := sq_sub_le_budget ha hb hP hr hV hu ht
    have hnonneg : 0 ≤ b + r / a := add_nonneg hb (div_nonneg hr ha.le)
    have hbudget' : P + a * V ≤ D := hbudget
    calc
      m ^ 2 = (u - (u - m)) ^ 2 := by ring
      _ ≤ (b + r / a) * (P + a * V) := h
      _ ≤ (b + r / a) * D := mul_le_mul_of_nonneg_left hbudget' hnonneg
  have hVD : V ≤ D / a := by
    apply (le_div_iff₀ ha).2
    change P + a * V ≤ D at hbudget
    nlinarith only [hbudget, hP]
  rw [hmean, hweight]
  calc
    V + m ^ 2 ≤ D / a + (b + r / a) * D := add_le_add hVD hm
    _ = ((r + 1) / a + b) * D := by ring

end RicciFlowSharpEstimate.Analysis
