/-
Copyright (c) 2026 Ziyang Qin. All rights reserved.
No license is granted by this file.
Authors: Ziyang Qin
-/
import RicciFlowSharpEstimate.Analysis.SampledBernstein
import Mathlib.Analysis.Calculus.ContDiff.Polynomial

/-!
# Symmetric monotone Bernstein approximation

Sampling the radial profile at squared distance from the midpoint gives genuine polynomials,
symmetric about the midpoint, with both hemisphere order laws and the original physical box.
The construction is adapted from Ziyang Qin's historical symmetric monotone density development.
-/

noncomputable section

open Filter Set Polynomial
open scoped unitInterval Topology ContDiff

namespace RicciFlowSharpEstimate.Analysis

/-- Squared midpoint radius on the unit interval, defined on the entire real line. -/
def squaredMidpointRadius (x : ℝ) : ℝ := (2 * x - 1) ^ 2

theorem squaredMidpointRadius_mem_Icc {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
    squaredMidpointRadius x ∈ Icc (0 : ℝ) 1 := by
  unfold squaredMidpointRadius
  constructor
  · positivity
  · nlinarith [sq_nonneg (2 * x - 1), mul_nonneg hx.1 (sub_nonneg.mpr hx.2)]

/-- Radial reconstruction from the right hemisphere. -/
def upperRadialProfile (K : ℝ → ℝ) (t : ℝ) : ℝ := K ((1 + Real.sqrt t) / 2)

theorem upperRadialArgument_mem_Icc {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    (1 + Real.sqrt t) / 2 ∈ Icc (1 / 2 : ℝ) 1 := by
  constructor
  · nlinarith [Real.sqrt_nonneg t]
  · have hsqrt : Real.sqrt t ≤ 1 := Real.sqrt_le_one.2 ht.2
    linarith

theorem monotoneOn_upperRadialProfile (K : ℝ → ℝ)
    (hK : MonotoneOn K (Icc (1 / 2 : ℝ) 1)) :
    MonotoneOn (upperRadialProfile K) (Icc (0 : ℝ) 1) := by
  intro s hs t ht hst
  apply hK (upperRadialArgument_mem_Icc hs) (upperRadialArgument_mem_Icc ht)
  nlinarith [Real.sqrt_le_sqrt hst]

/-- The literal degree-`n + 1` sampled Bernstein polynomial evaluated at squared midpoint radius.
The definition depends on values of `K` alone, without regularity or symmetry witnesses. -/
def symmetricBernsteinApproximation (n : ℕ) (K : ℝ → ℝ) (x : ℝ) : ℝ :=
  (sampledBernsteinPolynomial (n + 1) (upperRadialProfile K)).eval (squaredMidpointRadius x)

/-- The real polynomial underlying the symmetric approximation. -/
def symmetricBernsteinPolynomial (n : ℕ) (K : ℝ → ℝ) : ℝ[X] :=
  (sampledBernsteinPolynomial (n + 1) (upperRadialProfile K)).comp ((C 2 * X - 1) ^ 2)

theorem eval_symmetricBernsteinPolynomial (n : ℕ) (K : ℝ → ℝ) (x : ℝ) :
    (symmetricBernsteinPolynomial n K).eval x = symmetricBernsteinApproximation n K x := by
  simp [symmetricBernsteinPolynomial, symmetricBernsteinApproximation, squaredMidpointRadius]

theorem contDiff_symmetricBernsteinApproximation (n : ℕ) (K : ℝ → ℝ) :
    ContDiff ℝ ∞ (symmetricBernsteinApproximation n K) := by
  have hp : ContDiff ℝ ∞ (fun x : ℝ => (symmetricBernsteinPolynomial n K).eval x) := by
    simpa [Polynomial.aeval_def] using
      (symmetricBernsteinPolynomial n K).contDiff_aeval (𝕜 := ℝ) ∞
  simpa only [eval_symmetricBernsteinPolynomial] using hp

/-- Reflection symmetry holds globally, irrespective of the original function's symmetry. -/
theorem symmetric_symmetricBernsteinApproximation (n : ℕ) (K : ℝ → ℝ) (x : ℝ) :
    symmetricBernsteinApproximation n K (1 - x) = symmetricBernsteinApproximation n K x := by
  unfold symmetricBernsteinApproximation squaredMidpointRadius
  congr 1
  ring

theorem monotoneOn_symmetricBernsteinApproximation (n : ℕ) (K : ℝ → ℝ)
    (hK : MonotoneOn K (Icc (1 / 2 : ℝ) 1)) :
    MonotoneOn (symmetricBernsteinApproximation n K) (Icc (1 / 2 : ℝ) 1) := by
  intro x hx y hy hxy
  apply monotoneOn_sampledBernsteinPolynomial (upperRadialProfile K)
    (monotoneOn_upperRadialProfile K hK) n
  · exact squaredMidpointRadius_mem_Icc ⟨by linarith [hx.1], hx.2⟩
  · exact squaredMidpointRadius_mem_Icc ⟨by linarith [hy.1], hy.2⟩
  · unfold squaredMidpointRadius
    nlinarith [hx.1, hy.1, sq_nonneg (2 * y - 1)]

theorem antitoneOn_symmetricBernsteinApproximation (n : ℕ) (K : ℝ → ℝ)
    (hK : MonotoneOn K (Icc (1 / 2 : ℝ) 1)) :
    AntitoneOn (symmetricBernsteinApproximation n K) (Icc (0 : ℝ) (1 / 2)) := by
  intro x hx y hy hxy
  rw [← symmetric_symmetricBernsteinApproximation n K y,
    ← symmetric_symmetricBernsteinApproximation n K x]
  apply monotoneOn_symmetricBernsteinApproximation n K hK
  · constructor <;> linarith [hy.1, hy.2]
  · constructor <;> linarith [hx.1, hx.2]
  · linarith

theorem symmetricBernsteinApproximation_mem_Icc (n : ℕ) (K : ℝ → ℝ) (lo hi : ℝ)
    (hbox : ∀ x ∈ Icc (0 : ℝ) 1, K x ∈ Icc lo hi) {x : ℝ}
    (hx : x ∈ Icc (0 : ℝ) 1) : symmetricBernsteinApproximation n K x ∈ Icc lo hi := by
  apply bernsteinPolynomialOfCoefficients_mem_Icc
  · intro j
    apply hbox
    have hj : ((j : ℕ) / (n + 1 : ℕ) : ℝ) ∈ Icc (0 : ℝ) 1 := by
      constructor
      · positivity
      · apply (div_le_one (by positivity : (0 : ℝ) < (n + 1 : ℕ))).2
        exact_mod_cast (show (j : ℕ) ≤ n + 1 by omega)
    have harg := upperRadialArgument_mem_Icc hj
    exact ⟨by linarith [harg.1], harg.2⟩
  · exact squaredMidpointRadius_mem_Icc hx

/-- Physical reflection symmetry reconstructs the original function from its radial profile. -/
theorem upperRadialProfile_squaredMidpointRadius_eq (K : ℝ → ℝ)
    (hsymm : ∀ x ∈ Icc (0 : ℝ) 1, K (1 - x) = K x) {x : ℝ}
    (hx : x ∈ Icc (0 : ℝ) 1) : upperRadialProfile K (squaredMidpointRadius x) = K x := by
  rcases le_total x (1 / 2 : ℝ) with hhalf | hhalf
  · rw [show upperRadialProfile K (squaredMidpointRadius x) = K (1 - x) by
      unfold upperRadialProfile squaredMidpointRadius
      rw [Real.sqrt_sq_eq_abs, abs_of_nonpos (by linarith : 2 * x - 1 ≤ 0)]
      congr 1
      ring]
    exact hsymm x hx
  · unfold upperRadialProfile squaredMidpointRadius
    rw [Real.sqrt_sq_eq_abs, abs_of_nonneg (by linarith : 0 ≤ 2 * x - 1)]
    congr 1
    ring

end RicciFlowSharpEstimate.Analysis
