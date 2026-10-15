/-
Copyright (c) 2026 Ziyang Qin. All rights reserved.
No license is granted by this file.
Authors: Ziyang Qin
-/
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.GCongr

/-! # Local uniqueness for a bounded singular Volterra system -/

noncomputable section
namespace RicciFlowSharpEstimate.Analysis
open Set MeasureTheory

private theorem integral_le_const_mul {u : ℝ → ℝ} {x B : ℝ} (hx : 0 < x)
    (hu : ∀ t ∈ Ioc (0 : ℝ) x, ‖u t‖ ≤ B) :
    (∫ t in (0 : ℝ)..x, u t) ≤ B * x := by
  have hh := intervalIntegral.norm_integral_le_of_norm_le_const_ae
    (f := u) (a := 0) (b := x) (C := B) (by
      filter_upwards [] with t ht
      exact hu t (by simpa only [uIoc_of_le hx.le] using ht))
  exact (le_abs_self _).trans (by
    simpa only [Real.norm_eq_abs, sub_zero, abs_of_pos hx] using hh)

/-- A bounded solution of the homogeneous singular Volterra inequalities
vanishes on a nonempty endpoint interval. All integrals are the literal
coupled functions; the shrinking envelope is constructed in the proof. -/
theorem exists_eq_zero_of_singular_volterra_bounds
    {r p q P : ℝ → ℝ} {b A B : ℝ}
    (hb : 0 < b) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hbound : ∃ N : ℝ, ∀ x ∈ Ioo (0 : ℝ) b, |q x| + |p x| + |r x| / x ≤ N)
    (hr : ∀ x ∈ Ioo (0 : ℝ) b, |r x| ≤ ∫ t in (0 : ℝ)..x, |p t|)
    (hP : ∀ x ∈ Ioo (0 : ℝ) b,
      |P x| ≤ A * ∫ t in (0 : ℝ)..x, t * (|q t| + |p t| + |r t| / t))
    (hq : ∀ x ∈ Ioo (0 : ℝ) b,
      |q x| ≤ B * ∫ t in (0 : ℝ)..x, (|P t| / t ^ 2 + |r t| / t))
    (hp : ∀ x ∈ Ioo (0 : ℝ) b,
      |p x| ≤ B / x ^ 2 * ∫ t in (0 : ℝ)..x, t * (|q t| + |r t|)) :
    ∃ δ : ℝ, 0 < δ ∧ δ < b ∧
      ∀ x ∈ Ioo (0 : ℝ) δ, r x = 0 ∧ p x = 0 ∧ q x = 0 ∧ P x = 0 := by
  let E := fun x => |q x| + |p x| + |r x| / x
  let T := B * (A + 1)
  let U := B * (T + 1)
  let C := T + 2 * U
  have hT : 0 ≤ T := by dsimp only [T]; positivity
  have hU : 0 ≤ U := by dsimp only [U]; positivity
  have hC : 0 ≤ C := by dsimp only [C]; positivity
  let δ := min (b / 2) (1 / (2 * (C + 1)))
  have hδ : 0 < δ := by dsimp only [δ]; positivity
  have hδb : δ < b := (min_le_left _ _).trans_lt (by linarith)
  have hδC : C * δ < 1 := by
    have hh : δ * (2 * (C + 1)) ≤ 1 :=
      (le_div_iff₀ (by positivity : (0 : ℝ) < 2 * (C + 1))).mp (min_le_right _ _)
    nlinarith only [hh, hδ]
  obtain ⟨N, hN⟩ := hbound
  let S : Set ℝ := {y | ∃ x, x ∈ Ioo (0 : ℝ) δ ∧ y = E x}
  have hSb : BddAbove S := by
    refine ⟨N, ?_⟩
    rintro y ⟨x, hx, rfl⟩
    exact hN x ⟨hx.1, hx.2.trans hδb⟩
  have hSn : S.Nonempty :=
    ⟨E (δ / 2), δ / 2, by constructor <;> linarith, rfl⟩
  let M := sSup S
  have hEM (x : ℝ) (hx : x ∈ Ioo (0 : ℝ) δ) : E x ≤ M :=
    le_csSup hSb ⟨x, hx, rfl⟩
  have hE0 (x : ℝ) (hx : 0 < x) : 0 ≤ E x := by dsimp only [E]; positivity
  have hM0 : 0 ≤ M :=
    (hE0 (δ / 2) (by linarith)).trans (hEM (δ / 2) (by constructor <;> linarith))
  have hparts (x : ℝ) (hx : x ∈ Ioo (0 : ℝ) δ) :
      |q x| ≤ M ∧ |p x| ≤ M ∧ |r x| / x ≤ M := by
    have hh := hEM x hx
    have hrd : 0 ≤ |r x| / x := div_nonneg (abs_nonneg _) hx.1.le
    dsimp only [E] at hh
    exact ⟨by linarith [abs_nonneg (p x)],
      by linarith [abs_nonneg (q x)], by linarith [abs_nonneg (q x), abs_nonneg (p x)]⟩
  have hrb (x : ℝ) (hx : x ∈ Ioo (0 : ℝ) δ) : |r x| ≤ x * M := by
    have hh := (div_le_iff₀ hx.1).mp (hparts x hx).2.2
    simpa only [mul_comm] using hh
  have hPb (x : ℝ) (hx : x ∈ Ioo (0 : ℝ) δ) : |P x| ≤ A * x ^ 2 * M := by
    have hi : (∫ t in (0 : ℝ)..x, t * E t) ≤ (x * M) * x := by
      apply integral_le_const_mul hx.1
      intro t ht
      have htδ : t ∈ Ioo (0 : ℝ) δ := ⟨ht.1, ht.2.trans_lt hx.2⟩
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg ht.1.le (hE0 t ht.1))]
      exact (mul_le_mul_of_nonneg_left (hEM t htδ) ht.1.le).trans
        (mul_le_mul_of_nonneg_right ht.2 hM0)
    calc
      |P x| ≤ A * (∫ t in (0 : ℝ)..x, t * E t) := hP x ⟨hx.1, hx.2.trans hδb⟩
      _ ≤ A * ((x * M) * x) := mul_le_mul_of_nonneg_left hi hA
      _ = A * x ^ 2 * M := by ring
  have hqb (x : ℝ) (hx : x ∈ Ioo (0 : ℝ) δ) : |q x| ≤ T * x * M := by
    have hi : (∫ t in (0 : ℝ)..x, (|P t| / t ^ 2 + |r t| / t)) ≤
        ((A + 1) * M) * x := by
      apply integral_le_const_mul hx.1
      intro t ht
      have htδ : t ∈ Ioo (0 : ℝ) δ := ⟨ht.1, ht.2.trans_lt hx.2⟩
      have hpt : |P t| / t ^ 2 ≤ A * M :=
        (div_le_iff₀ (sq_pos_of_pos ht.1)).mpr (by
          simpa only [mul_assoc, mul_left_comm, mul_comm] using hPb t htδ)
      rw [Real.norm_eq_abs, abs_of_nonneg (add_nonneg
        (div_nonneg (abs_nonneg _) (sq_nonneg _)) (div_nonneg (abs_nonneg _) ht.1.le))]
      nlinarith only [hpt, (hparts t htδ).2.2]
    calc
      |q x| ≤ B * (∫ t in (0 : ℝ)..x, (|P t| / t ^ 2 + |r t| / t)) :=
        hq x ⟨hx.1, hx.2.trans hδb⟩
      _ ≤ B * (((A + 1) * M) * x) := mul_le_mul_of_nonneg_left hi hB
      _ = T * x * M := by dsimp only [T]; ring
  have hpb (x : ℝ) (hx : x ∈ Ioo (0 : ℝ) δ) : |p x| ≤ U * x * M := by
    have hi : (∫ t in (0 : ℝ)..x, t * (|q t| + |r t|)) ≤
        ((T + 1) * x ^ 2 * M) * x := by
      apply integral_le_const_mul hx.1
      intro t ht
      have htδ : t ∈ Ioo (0 : ℝ) δ := ⟨ht.1, ht.2.trans_lt hx.2⟩
      rw [Real.norm_eq_abs, abs_of_nonneg
        (mul_nonneg ht.1.le (add_nonneg (abs_nonneg _) (abs_nonneg _)))]
      calc
        t * (|q t| + |r t|) ≤ t * (T * t * M + t * M) :=
          mul_le_mul_of_nonneg_left (add_le_add (hqb t htδ) (hrb t htδ)) ht.1.le
        _ = (T + 1) * t ^ 2 * M := by ring
        _ ≤ (T + 1) * x ^ 2 * M := by
          gcongr
          · exact ht.1.le
          · exact ht.2
    calc
      |p x| ≤ B / x ^ 2 * (∫ t in (0 : ℝ)..x, t * (|q t| + |r t|)) :=
        hp x ⟨hx.1, hx.2.trans hδb⟩
      _ ≤ B / x ^ 2 * (((T + 1) * x ^ 2 * M) * x) :=
        mul_le_mul_of_nonneg_left hi (div_nonneg hB (sq_nonneg _))
      _ = U * x * M := by
        dsimp only [U]
        field_simp [hx.1.ne']
  have hrsmall (x : ℝ) (hx : x ∈ Ioo (0 : ℝ) δ) : |r x| / x ≤ U * x * M := by
    have hi : (∫ t in (0 : ℝ)..x, |p t|) ≤ (U * x * M) * x := by
      apply integral_le_const_mul hx.1
      intro t ht
      have htδ : t ∈ Ioo (0 : ℝ) δ := ⟨ht.1, ht.2.trans_lt hx.2⟩
      rw [Real.norm_eq_abs, abs_abs]
      exact (hpb t htδ).trans (by gcongr; exact ht.2)
    apply (div_le_iff₀ hx.1).mpr
    exact (hr x ⟨hx.1, hx.2.trans hδb⟩).trans hi
  have hES (x : ℝ) (hx : x ∈ Ioo (0 : ℝ) δ) : E x ≤ C * δ * M := by
    have hh : E x ≤ C * x * M := by
      dsimp only [E, C]
      nlinarith only [hqb x hx, hpb x hx, hrsmall x hx]
    exact hh.trans (by gcongr; exact hx.2.le)
  have hMsup : M ≤ C * δ * M := by
    apply csSup_le hSn
    rintro y ⟨x, hx, rfl⟩
    exact hES x hx
  have hMzero : M = 0 := by
    have hMle : M ≤ 0 := by
      by_contra hn
      have hMp : 0 < M := lt_of_not_ge hn
      have hh := mul_lt_mul_of_pos_right hδC hMp
      nlinarith only [hh, hMsup]
    exact le_antisymm hMle hM0
  refine ⟨δ, hδ, hδb, ?_⟩
  intro x hx
  have hparts0 := hparts x hx
  have hP0 := hPb x hx
  rw [hMzero] at hparts0 hP0
  have hq0 : q x = 0 := abs_eq_zero.mp (le_antisymm hparts0.1 (abs_nonneg _))
  have hp0 : p x = 0 := abs_eq_zero.mp (le_antisymm hparts0.2.1 (abs_nonneg _))
  have hr0 : r x = 0 := by
    have hh := (div_le_iff₀ hx.1).mp hparts0.2.2
    simp only [zero_mul] at hh
    exact abs_eq_zero.mp (le_antisymm hh (abs_nonneg _))
  have hPz : P x = 0 := by
    simp only [mul_zero] at hP0
    exact abs_eq_zero.mp (le_antisymm hP0 (abs_nonneg _))
  exact ⟨hr0, hp0, hq0, hPz⟩

end RicciFlowSharpEstimate.Analysis
