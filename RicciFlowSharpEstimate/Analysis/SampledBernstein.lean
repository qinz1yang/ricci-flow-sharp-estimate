/-
Copyright (c) 2026 Ziyang Qin. All rights reserved.
No license is granted by this file.
Authors: Ziyang Qin
-/
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Polynomial

/-!
# Sampled Bernstein polynomials

Bernstein polynomials preserve boxes and monotonicity, and approximate bounded functions at
points of relative continuity. The derivative argument is adapted from Ziyang Qin's historical
`BalancedBoxBernstein` development; the convergence argument uses Mathlib's exact variance law.
-/

noncomputable section

open Filter Set Polynomial
open scoped unitInterval Topology

namespace RicciFlowSharpEstimate.Analysis

/-- The polynomial represented by a Bernstein control coefficient vector. -/
def bernsteinPolynomialOfCoefficients
    (n : ℕ) (coeff : Fin (n + 1) → ℝ) : ℝ[X] :=
  ∑ j : Fin (n + 1),
    C (coeff j) * bernsteinPolynomial ℝ n j

theorem eval_bernsteinPolynomialOfCoefficients
    (n : ℕ) (coeff : Fin (n + 1) → ℝ) (x : ℝ) :
    (bernsteinPolynomialOfCoefficients n coeff).eval x =
      ∑ j : Fin (n + 1),
        (n.choose (j : ℕ) : ℝ) * x ^ (j : ℕ) *
          (1 - x) ^ (n - (j : ℕ)) * coeff j := by
  simp only [bernsteinPolynomialOfCoefficients, Polynomial.eval_finsetSum]
  apply Finset.sum_congr rfl
  intro j hj
  simp [bernsteinPolynomial]
  ring

theorem eval_bernsteinPolynomialOfCoefficients_unitInterval
    (n : ℕ) (coeff : Fin (n + 1) → ℝ) (x : I) :
    (bernsteinPolynomialOfCoefficients n coeff).eval (x : ℝ) =
      ∑ j : Fin (n + 1), bernstein n j x * coeff j := by
  simp [eval_bernsteinPolynomialOfCoefficients, bernstein_apply, mul_comm]

/-- Linearity of the coefficient-to-polynomial map. -/
private theorem bernsteinPolynomialOfCoefficients_linearCombination
    (n : ℕ) (left right : Fin (n + 1) → ℝ)
    (α β : ℝ) :
    bernsteinPolynomialOfCoefficients n (fun j => α * left j + β * right j) =
      C α * bernsteinPolynomialOfCoefficients n left +
        C β * bernsteinPolynomialOfCoefficients n right := by
  unfold bernsteinPolynomialOfCoefficients
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j hj
  simp only [map_add, map_mul]
  ring

/-- Reindexing identity used in differentiating a Bernstein control
polygon.  The apparent last shifted basis element is zero. -/
private theorem bernsteinPolynomialOfCoefficients_castSucc_eq_zero_add_shift
    (n : ℕ) (coeff : Fin (n + 2) → ℝ) :
    bernsteinPolynomialOfCoefficients n (fun k => coeff k.castSucc) =
      C (coeff 0) * bernsteinPolynomial ℝ n 0 +
        ∑ k : Fin (n + 1),
          C (coeff k.succ) *
            bernsteinPolynomial ℝ n ((k : ℕ) + 1) := by
  unfold bernsteinPolynomialOfCoefficients
  rw [Fin.sum_univ_succ]
  congr 1
  rw [Fin.sum_univ_castSucc]
  have hlast :
      bernsteinPolynomial ℝ n
        (((Fin.last n : Fin (n + 1)) : ℕ) + 1) = 0 := by
    apply bernsteinPolynomial.eq_zero_of_lt
    simp
  rw [hlast, mul_zero, add_zero]
  apply Finset.sum_congr rfl
  intro k hk
  congr 2

/-- Exact derivative formula for a Bernstein control polygon:
the derivative has the adjacent coefficient differences as its degree-`n`
Bernstein coefficients. -/
theorem derivative_bernsteinPolynomialOfCoefficients_succ
    (n : ℕ) (coeff : Fin (n + 2) → ℝ) :
    derivative (bernsteinPolynomialOfCoefficients (n + 1) coeff) =
      C (n + 1 : ℝ) *
        bernsteinPolynomialOfCoefficients n
          (fun k => coeff k.succ - coeff k.castSucc) := by
  have hsucc :
      (∑ k : Fin (n + 1),
          C (coeff k.succ) *
            bernsteinPolynomial ℝ n k) =
        bernsteinPolynomialOfCoefficients n (fun k => coeff k.succ) := by
    rfl
  have hshift :
      C (coeff 0) * bernsteinPolynomial ℝ n 0 +
          ∑ k : Fin (n + 1),
            C (coeff k.succ) *
              bernsteinPolynomial ℝ n ((k : ℕ) + 1) =
        bernsteinPolynomialOfCoefficients n (fun k => coeff k.castSucc) :=
    (bernsteinPolynomialOfCoefficients_castSucc_eq_zero_add_shift n coeff).symm
  have hdiff :=
    bernsteinPolynomialOfCoefficients_linearCombination n
      (fun k => coeff k.succ)
      (fun k => coeff k.castSucc) 1 (-1)
  change
    derivative
        (∑ j : Fin (n + 2),
          C (coeff j) *
            bernsteinPolynomial ℝ (n + 1) j) =
      C (n + 1 : ℝ) *
        bernsteinPolynomialOfCoefficients n
          (fun k => coeff k.succ - coeff k.castSucc)
  rw [derivative_sum, Fin.sum_univ_succ]
  simp only [Fin.val_zero, Fin.val_succ, derivative_mul,
    derivative_C, zero_mul, zero_add,
    bernsteinPolynomial.derivative_zero,
    bernsteinPolynomial.derivative_succ]
  rw [show n + 1 - 1 = n by omega]
  simp only [Nat.cast_add, Nat.cast_one]
  rw [show
      (∑ k : Fin (n + 1),
        C (coeff k.succ) *
          ((↑n + 1) *
            (bernsteinPolynomial ℝ n ↑k -
              bernsteinPolynomial ℝ n (↑k + 1)))) =
        C (n + 1 : ℝ) *
          ((∑ k : Fin (n + 1),
              C (coeff k.succ) *
                bernsteinPolynomial ℝ n k) -
            ∑ k : Fin (n + 1),
              C (coeff k.succ) *
                bernsteinPolynomial ℝ n ((k : ℕ) + 1)) by
      rw [mul_sub, Finset.mul_sum, Finset.mul_sum,
        ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro k hk
      simp
      ring]
  rw [hsucc]
  have hzeroTerm :
      C (coeff 0) *
          (-(↑n + 1) *
            bernsteinPolynomial ℝ n 0) =
        C (n + 1 : ℝ) *
          (-(C (coeff 0) *
            bernsteinPolynomial ℝ n 0)) := by
    simp
    ring
  rw [hzeroTerm]
  rw [← mul_add]
  rw [show
      -(C (coeff 0) * bernsteinPolynomial ℝ n 0) +
          (bernsteinPolynomialOfCoefficients n (fun k => coeff k.succ) -
            ∑ k : Fin (n + 1),
              C (coeff k.succ) *
                bernsteinPolynomial ℝ n (↑k + 1)) =
        bernsteinPolynomialOfCoefficients n (fun k => coeff k.succ) -
          (C (coeff 0) * bernsteinPolynomial ℝ n 0 +
            ∑ k : Fin (n + 1),
              C (coeff k.succ) *
                bernsteinPolynomial ℝ n (↑k + 1)) by ring,
    hshift]
  have hdiff' :
      bernsteinPolynomialOfCoefficients n
          (fun k => coeff k.succ - coeff k.castSucc) =
        bernsteinPolynomialOfCoefficients n (fun k => coeff k.succ) -
          bernsteinPolynomialOfCoefficients n (fun k => coeff k.castSucc) := by
    simpa only [one_mul, neg_mul, C_1, C_neg, C_1, one_mul,
      neg_one_mul, sub_eq_add_neg] using hdiff
  rw [← hdiff']

/-- The Bernstein polynomial with coefficients sampled at the equally spaced nodes. -/
def sampledBernsteinPolynomial (n : ℕ) (f : ℝ → ℝ) : ℝ[X] :=
  bernsteinPolynomialOfCoefficients n (fun j => f ((j : ℕ) / (n : ℝ)))

theorem eval_sampledBernsteinPolynomial (n : ℕ) (f : ℝ → ℝ) (x : I) :
    (sampledBernsteinPolynomial n f).eval (x : ℝ) =
      ∑ j : Fin (n + 1), bernstein n j x * f (bernstein.z j) := by
  simp [sampledBernsteinPolynomial, eval_bernsteinPolynomialOfCoefficients_unitInterval,
    bernstein.z]

/-- Bernstein convex combinations preserve every closed coefficient interval. -/
theorem bernsteinPolynomialOfCoefficients_mem_Icc (n : ℕ)
    (coeff : Fin (n + 1) → ℝ) {lo hi : ℝ}
    (hcoeff : ∀ j, coeff j ∈ Icc lo hi) {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
    (bernsteinPolynomialOfCoefficients n coeff).eval x ∈ Icc lo hi := by
  let t : I := ⟨x, hx⟩
  change (bernsteinPolynomialOfCoefficients n coeff).eval (t : ℝ) ∈ Icc lo hi
  rw [eval_bernsteinPolynomialOfCoefficients_unitInterval]
  constructor
  · calc
      lo = ∑ j : Fin (n + 1), bernstein n j t * lo := by
        rw [← Finset.sum_mul, bernstein.probability, one_mul]
      _ ≤ ∑ j : Fin (n + 1), bernstein n j t * coeff j :=
        Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (hcoeff j).1 bernstein_nonneg
  · calc
      (∑ j : Fin (n + 1), bernstein n j t * coeff j) ≤
          ∑ j : Fin (n + 1), bernstein n j t * hi :=
        Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (hcoeff j).2 bernstein_nonneg
      _ = hi := by rw [← Finset.sum_mul, bernstein.probability, one_mul]

/-- Sampling a monotone function gives a monotone Bernstein polynomial on the unit interval.
No continuity of the sampled function is needed. -/
theorem monotoneOn_sampledBernsteinPolynomial (f : ℝ → ℝ)
    (hf : MonotoneOn f (Icc (0 : ℝ) 1)) (n : ℕ) :
    MonotoneOn (fun x => (sampledBernsteinPolynomial (n + 1) f).eval x)
      (Icc (0 : ℝ) 1) := by
  let p := sampledBernsteinPolynomial (n + 1) f
  apply monotoneOn_of_deriv_nonneg (convex_Icc (𝕜 := ℝ) (0 : ℝ) 1)
    p.continuous.continuousOn p.differentiable.differentiableOn
  intro x hx
  rw [p.deriv]
  dsimp only [p, sampledBernsteinPolynomial]
  rw [derivative_bernsteinPolynomialOfCoefficients_succ, Polynomial.eval_mul,
    Polynomial.eval_C]
  apply mul_nonneg (by positivity)
  have hxIcc : x ∈ Icc (0 : ℝ) 1 := interior_subset hx
  let t : I := ⟨x, hxIcc⟩
  rw [show x = (t : ℝ) by rfl, eval_bernsteinPolynomialOfCoefficients_unitInterval]
  apply Finset.sum_nonneg
  intro k _
  apply mul_nonneg bernstein_nonneg
  apply sub_nonneg.mpr
  apply hf
  · constructor
    · positivity
    · apply (div_le_one (by positivity : (0 : ℝ) < (n + 1 : ℕ))).2
      exact_mod_cast (show (k.castSucc : Fin (n + 2)).val ≤ n + 1 by omega)
  · constructor
    · positivity
    · apply (div_le_one (by positivity : (0 : ℝ) < (n + 1 : ℕ))).2
      exact_mod_cast (show (k.succ : Fin (n + 2)).val ≤ n + 1 by omega)
  · apply (div_le_div_iff_of_pos_right (by positivity : (0 : ℝ) < (n + 1 : ℕ))).2
    exact_mod_cast (show (k.castSucc : Fin (n + 2)).val ≤ k.succ.val by simp)

/-- Bernstein approximation converges at every continuity point of bounded
unit-interval data.  This is the pointwise form of the classical
probability/variance proof of Bernstein approximation. -/
private theorem tendsto_bernstein_sum_of_continuousAt
    (f : I → ℝ) (x : I) (D : ℝ) (hD : 0 ≤ D)
    (hBound : ∀ y : I, |f y - f x| ≤ D)
    (hContinuous : ContinuousAt f x) :
    Tendsto (fun n : ℕ => (∑ k : Fin (n + 1), bernstein n k x * f (bernstein.z k)))
      atTop (𝓝 (f x)) := by
  rw [Metric.tendsto_atTop]
  intro epsilon hEpsilon
  obtain ⟨delta, hDelta, hClose⟩ :=
    Metric.continuousAt_iff.mp hContinuous (epsilon / 2)
      (half_pos hEpsilon)
  have hFarTendsto :=
    tendsto_const_div_atTop_nhds_zero_nat (D / delta ^ 2)
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp hFarTendsto
    (epsilon / 2) (half_pos hEpsilon)
  refine ⟨max N 1, ?_⟩
  intro n hn
  have hnN : N ≤ n := (le_max_left N 1).trans hn
  have hnPos : 0 < n := (le_max_right N 1).trans hn
  have hnNe : n ≠ 0 := Nat.ne_of_gt hnPos
  have hFarSmall : D / delta ^ 2 / n < epsilon / 2 := by
    have hNonneg : 0 ≤ D / delta ^ 2 / (n : ℝ) := by positivity
    have h := hN n hnN
    rw [Real.dist_eq, sub_zero, abs_of_nonneg hNonneg] at h
    exact h
  let S : Finset (Fin (n + 1)) :=
    {k : Fin (n + 1) | dist (bernstein.z k) x < delta}
  have hRewrite :
      (∑ k : Fin (n + 1), bernstein n k x * f (bernstein.z k)) - f x =
        ∑ k : Fin (n + 1),
          bernstein n k x * (f (bernstein.z k) - f x) := by
    calc
      (∑ k : Fin (n + 1), bernstein n k x * f (bernstein.z k)) - f x =
          (∑ k : Fin (n + 1), bernstein n k x * f (bernstein.z k)) -
            (∑ k : Fin (n + 1), bernstein n k x) * f x := by
              rw [bernstein.probability, one_mul]
      _ = ∑ k : Fin (n + 1),
          bernstein n k x * (f (bernstein.z k) - f x) := by
            rw [Finset.sum_mul, ← Finset.sum_sub_distrib]
            apply Finset.sum_congr rfl
            intro k _hk
            ring
  rw [Real.dist_eq, hRewrite]
  calc
    |∑ k : Fin (n + 1),
          bernstein n k x * (f (bernstein.z k) - f x)| ≤
        ∑ k : Fin (n + 1),
          |bernstein n k x * (f (bernstein.z k) - f x)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ = ∑ k : Fin (n + 1),
          bernstein n k x * |f (bernstein.z k) - f x| := by
      apply Finset.sum_congr rfl
      intro k _hk
      rw [abs_mul, abs_of_nonneg bernstein_nonneg]
    _ = (∑ k ∈ S,
          bernstein n k x * |f (bernstein.z k) - f x|) +
        ∑ k ∈ Sᶜ,
          bernstein n k x * |f (bernstein.z k) - f x| :=
      (S.sum_add_sum_compl _).symm
    _ < epsilon / 2 + epsilon / 2 := add_lt_add_of_le_of_lt ?_ ?_
    _ = epsilon := by ring
  · calc
      ∑ k ∈ S, bernstein n k x * |f (bernstein.z k) - f x| ≤
          ∑ k ∈ S, bernstein n k x * (epsilon / 2) := by
        gcongr with k hk
        have hkDist : dist (bernstein.z k) x < delta := by
          simpa [S] using hk
        have hkClose := hClose hkDist
        rw [Real.dist_eq] at hkClose
        exact hkClose.le
      _ = epsilon / 2 * ∑ k ∈ S, bernstein n k x := by
        rw [mul_comm, Finset.sum_mul]
      _ ≤ epsilon / 2 * ∑ k : Fin (n + 1), bernstein n k x := by
        gcongr
        exact S.subset_univ
      _ = epsilon / 2 := by rw [bernstein.probability, mul_one]
  · calc
      ∑ k ∈ Sᶜ, bernstein n k x * |f (bernstein.z k) - f x| ≤
          ∑ k ∈ Sᶜ, D * bernstein n k x := by
        simp only [mul_comm (bernstein n _ x)]
        gcongr with k _hk
        exact hBound _
      _ = D * ∑ k ∈ Sᶜ, bernstein n k x := by rw [Finset.mul_sum]
      _ ≤ D * ∑ k ∈ Sᶜ,
          ((x : ℝ) - bernstein.z k) ^ 2 / delta ^ 2 *
            bernstein n k x := by
        gcongr with k hk
        conv_lhs => rw [← one_mul (bernstein _ _ _)]
        gcongr
        simpa [one_le_div₀, hDelta, sq_le_sq, S, abs_of_pos,
          ← Real.dist_eq, dist_comm (x : ℝ), Subtype.dist_eq] using hk
      _ ≤ D * ∑ k : Fin (n + 1),
          ((x : ℝ) - bernstein.z k) ^ 2 / delta ^ 2 *
            bernstein n k x := by
        gcongr
        exact Sᶜ.subset_univ
      _ = D * (∑ k : Fin (n + 1),
          ((x : ℝ) - bernstein.z k) ^ 2 * bernstein n k x) /
            delta ^ 2 := by
        simp only [← mul_div_right_comm, ← mul_div_assoc, ← Finset.sum_div]
      _ = D / delta ^ 2 * x * (1 - x) / n := by
        rw [bernstein.variance hnNe]
        ring
      _ ≤ D / delta ^ 2 * 1 * 1 / n := by
        gcongr <;> unit_interval
      _ < epsilon / 2 := by simpa only [mul_one] using hFarSmall

/-- Bounded sampled Bernstein polynomials converge at every relative continuity point,
including the endpoints of the unit interval. -/
theorem tendsto_sampledBernsteinPolynomial (f : ℝ → ℝ) {M : ℝ}
    (hbound : ∀ y ∈ Icc (0 : ℝ) 1, |f y| ≤ M) {x : ℝ}
    (hx : x ∈ Icc (0 : ℝ) 1) (hcont : ContinuousWithinAt f (Icc (0 : ℝ) 1) x) :
    Tendsto (fun n => (sampledBernsteinPolynomial (n + 1) f).eval x)
      atTop (𝓝 (f x)) := by
  let t : I := ⟨x, hx⟩
  have hM : 0 ≤ M := (abs_nonneg (f x)).trans (hbound x hx)
  have hcontinuous : ContinuousAt (fun y : I => f y) t := by
    exact (continuousWithinAt_iff_continuousAt_domRestrict f hx).mp hcont
  have hlim := tendsto_bernstein_sum_of_continuousAt (fun y : I => f y) t (2 * M)
    (by positivity) (fun y => (abs_sub (f y) (f x)).trans
      (by simpa only [two_mul] using add_le_add (hbound y y.2) (hbound x hx))) hcontinuous
  simpa only [← eval_sampledBernsteinPolynomial, Function.comp_def, t] using
    hlim.comp (tendsto_add_atTop_nat 1)

end RicciFlowSharpEstimate.Analysis
