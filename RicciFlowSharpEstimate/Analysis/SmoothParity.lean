/-
Copyright (c) 2026 Ziyang Qin. All rights reserved.
No license is granted by this file.
Authors: Ziyang Qin
-/
import DifferentialGeometry.Analysis.Calculus.SmoothExtension.BorelHalfLine.Parametric
import DifferentialGeometry.Analysis.Calculus.SmoothExtension.BoundaryDerivLimit
import DifferentialGeometry.Analysis.Calculus.Taylor
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# Smooth parity factorization

These elementary one-dimensional lemmas are the analytic input for the
classification of smooth rotation-invariant covectors at a fixed point.
No analyticity is assumed. The square descent is smooth at zero by iterating
the odd Hadamard quotient, and the parametric Borel extension supplies a global
smooth function on the real line.

Adapted from Ziyang Qin's pinned `SmoothParityFactorization.lean`.
-/

noncomputable section

namespace RicciFlowSharpEstimate.Analysis

open DifferentialGeometry.Analysis.Calculus
open DifferentialGeometry.Analysis.Calculus.SmoothExtension
open Filter Topology
open Set
open scoped ContDiff


/-- Hadamard's integral quotient has no exceptional value at zero. -/
private def smoothOddQuotient (p : ℝ → ℝ) : ℝ → ℝ :=
  hadamardFactor p 0

private theorem smoothOddQuotient_contDiff (p : ℝ → ℝ)
    (hp : ContDiff ℝ (⊤ : ℕ∞) p) :
    ContDiff ℝ (⊤ : ℕ∞) (smoothOddQuotient p) :=
  hadamardFactor_contDiff p hp 0

private theorem eq_mul_smoothOddQuotient (p : ℝ → ℝ)
    (hp : ContDiff ℝ (⊤ : ℕ∞) p) (hodd : Function.Odd p) (x : ℝ) :
    p x = x * smoothOddQuotient p x := by
  have hp0 : p 0 = 0 := by
    have h := hodd 0
    simp only [neg_zero] at h
    linarith
  simpa only [hp0, sub_zero, smul_eq_mul, smoothOddQuotient] using
    hadamard_factorization p hp 0 x

private theorem smoothOddQuotient_even (p : ℝ → ℝ)
    (hp : ContDiff ℝ (⊤ : ℕ∞) p) (hodd : Function.Odd p) :
    Function.Even (smoothOddQuotient p) := by
  intro x
  by_cases hx : x = 0
  · simp [hx]
  · have h := eq_mul_smoothOddQuotient p hp hodd (-x)
    rw [hodd x, eq_mul_smoothOddQuotient p hp hodd x] at h
    exact mul_left_cancel₀ hx (by nlinarith only [h])

/-- The derivative of a smooth even function is odd. -/
private theorem deriv_odd_of_even
    (e : ℝ → ℝ)
    (he : ContDiff ℝ (⊤ : ℕ∞) e)
    (heven : Function.Even e) :
    Function.Odd (deriv e) := by
  intro x
  have hfun :
      (fun t : ℝ => e (-t)) = fun t : ℝ => e t := by
    funext t
    exact heven t
  have hderivFun := congrArg deriv hfun
  have heDiff : Differentiable ℝ e :=
    he.differentiable (by simp)
  have hleft :
      deriv (fun t : ℝ => e (-t)) x =
        -(deriv e (-x)) := by
    have heAt :
        HasDerivAt e (deriv e (-x)) (-x) :=
      heDiff.differentiableAt.hasDerivAt
    have hneg :
        HasDerivAt (fun t : ℝ => -t) (-1) x :=
      (hasDerivAt_id x).neg
    simpa only [Function.comp_def, mul_neg, mul_one] using
      (heAt.comp x hneg).deriv
  have hAt := congrFun hderivFun x
  rw [hleft] at hAt
  linarith

/-- The radial derivative operator corresponding to differentiation
after the substitution `s = x²`. -/
private def evenSquareStep (e : ℝ → ℝ) (x : ℝ) : ℝ :=
  (2 : ℝ)⁻¹ * smoothOddQuotient (deriv e) x

private theorem evenSquareStep_contDiff
    (e : ℝ → ℝ)
    (he : ContDiff ℝ (⊤ : ℕ∞) e) :
    ContDiff ℝ (⊤ : ℕ∞) (evenSquareStep e) := by
  have he' : ContDiff ℝ (⊤ : ℕ∞) (deriv e) := (contDiff_infty_iff_deriv.mp he).2
  exact contDiff_const.mul
    (smoothOddQuotient_contDiff (deriv e) he')

private theorem evenSquareStep_even
    (e : ℝ → ℝ)
    (he : ContDiff ℝ (⊤ : ℕ∞) e)
    (heven : Function.Even e) :
    Function.Even (evenSquareStep e) := by
  have he' : ContDiff ℝ (⊤ : ℕ∞) (deriv e) := (contDiff_infty_iff_deriv.mp he).2
  have hq := smoothOddQuotient_even
    (deriv e) he' (deriv_odd_of_even e he heven)
  intro x
  unfold evenSquareStep
  rw [hq x]

private theorem deriv_eq_two_mul_mul_evenSquareStep
    (e : ℝ → ℝ)
    (he : ContDiff ℝ (⊤ : ℕ∞) e)
    (heven : Function.Even e)
    (x : ℝ) :
    deriv e x = 2 * x * evenSquareStep e x := by
  have he' : ContDiff ℝ (⊤ : ℕ∞) (deriv e) := (contDiff_infty_iff_deriv.mp he).2
  rw [eq_mul_smoothOddQuotient
    (deriv e) he' (deriv_odd_of_even e he heven) x]
  unfold evenSquareStep
  ring

/-- The right-half-line function obtained by descending an even
function through the square map. -/
private def evenSquareDesc (e : ℝ → ℝ) (s : ℝ) : ℝ :=
  e (Real.sqrt s)

private theorem evenSquareDesc_hasDerivAt_of_pos
    (e : ℝ → ℝ)
    (he : ContDiff ℝ (⊤ : ℕ∞) e)
    (heven : Function.Even e)
    {s : ℝ} (hs : 0 < s) :
    HasDerivAt (evenSquareDesc e)
      (evenSquareDesc (evenSquareStep e) s) s := by
  have heAt :
      HasDerivAt e (deriv e (Real.sqrt s))
        (Real.sqrt s) :=
    (he.differentiable (by simp)).differentiableAt.hasDerivAt
  have hcomp :=
    heAt.comp s (Real.hasDerivAt_sqrt hs.ne')
  have hsqrt : Real.sqrt s ≠ 0 :=
    (Real.sqrt_pos.2 hs).ne'
  have hcoef :
      deriv e (Real.sqrt s) * (1 / (2 * Real.sqrt s)) =
        evenSquareStep e (Real.sqrt s) := by
    rw [deriv_eq_two_mul_mul_evenSquareStep e he heven]
    field_simp
  unfold evenSquareDesc
  convert hcomp using 1
  · rfl
  · exact hcoef.symm

private theorem evenSquareDesc_hasDerivWithinAt_zero
    (e : ℝ → ℝ)
    (he : ContDiff ℝ (⊤ : ℕ∞) e)
    (heven : Function.Even e) :
    HasDerivWithinAt (evenSquareDesc e)
      (evenSquareDesc (evenSquareStep e) 0)
      (Set.Ici (0 : ℝ)) 0 := by
  have hcont :
      ContinuousOn (evenSquareDesc e)
        (Set.Icc (0 : ℝ) 1) :=
    (he.continuous.comp Real.continuous_sqrt).continuousOn
  have hderiv :
      ∀ s ∈ Set.Ioo (0 : ℝ) 1,
        HasDerivAt (evenSquareDesc e)
          (evenSquareDesc (evenSquareStep e) s) s := by
    intro s hs
    exact evenSquareDesc_hasDerivAt_of_pos e he heven hs.1
  have hstepCont :
      Continuous (evenSquareStep e) :=
    (evenSquareStep_contDiff e he).continuous
  have hlim :
      Filter.Tendsto
        (evenSquareDesc (evenSquareStep e))
        (𝓝[>] (0 : ℝ))
        (𝓝 (evenSquareDesc (evenSquareStep e) 0)) := by
    have hfull :
        Filter.Tendsto
          (evenSquareDesc (evenSquareStep e))
          (𝓝 (0 : ℝ))
          (𝓝 (evenSquareDesc (evenSquareStep e) 0)) := by
      exact (hstepCont.comp Real.continuous_sqrt).continuousAt
    exact hfull.mono_left nhdsWithin_le_nhds
  exact hasDerivWithinAt_Ici_of_tendsto_nhdsGT
    (show (0 : ℝ) < 1 by norm_num)
    hcont hderiv hlim

private theorem evenSquareDesc_derivWithin_eq
    (e : ℝ → ℝ)
    (he : ContDiff ℝ (⊤ : ℕ∞) e)
    (heven : Function.Even e)
    {s : ℝ} (hs : s ∈ Set.Ici (0 : ℝ)) :
    derivWithin (evenSquareDesc e) (Set.Ici (0 : ℝ)) s =
      evenSquareDesc (evenSquareStep e) s := by
  rcases eq_or_lt_of_le (Set.mem_Ici.mp hs) with rfl | hspos
  · exact
      (evenSquareDesc_hasDerivWithinAt_zero e he heven).derivWithin
        (uniqueDiffOn_Ici (0 : ℝ) 0 (Set.mem_Ici.mpr le_rfl))
  · exact
      (evenSquareDesc_hasDerivAt_of_pos e he heven hspos).hasDerivWithinAt.derivWithin
        (uniqueDiffOn_Ici (0 : ℝ) s hs)

private theorem evenSquareDesc_differentiableOn
    (e : ℝ → ℝ)
    (he : ContDiff ℝ (⊤ : ℕ∞) e)
    (heven : Function.Even e) :
    DifferentiableOn ℝ (evenSquareDesc e) (Set.Ici (0 : ℝ)) := by
  intro s hs
  rcases eq_or_lt_of_le (Set.mem_Ici.mp hs) with rfl | hspos
  · exact
      (evenSquareDesc_hasDerivWithinAt_zero e he heven).differentiableWithinAt
  · exact
      (evenSquareDesc_hasDerivAt_of_pos e he heven hspos).differentiableAt
        |>.differentiableWithinAt

/-- Finite-order smoothness of the square-descended function on the
closed right half-line. -/
private theorem evenSquareDesc_contDiffOn_nat
    (n : ℕ)
    (e : ℝ → ℝ)
    (he : ContDiff ℝ (⊤ : ℕ∞) e)
    (heven : Function.Even e) :
    ContDiffOn ℝ (n : ℕ) (evenSquareDesc e)
      (Set.Ici (0 : ℝ)) := by
  induction n generalizing e with
  | zero =>
      rw [Nat.cast_zero, contDiffOn_zero]
      exact
        (he.continuous.comp Real.continuous_sqrt).continuousOn
  | succ n ih =>
      rw [Nat.cast_succ,
        contDiffOn_succ_iff_derivWithin
          (uniqueDiffOn_Ici (0 : ℝ))]
      refine ⟨evenSquareDesc_differentiableOn e he heven, ?_, ?_⟩
      · intro hcontra
        exact absurd hcontra (by simp)
      · have hstepSmooth := evenSquareStep_contDiff e he
        have hstepEven := evenSquareStep_even e he heven
        have hIH :=
          ih (evenSquareStep e) hstepSmooth hstepEven
        exact hIH.congr
          (fun s hs =>
            (evenSquareDesc_derivWithin_eq
              e he heven hs))

/-- An even smooth function descends smoothly through the square map on
the entire closed right half-line. -/
private theorem evenSquareDesc_contDiffOn
    (e : ℝ → ℝ)
    (he : ContDiff ℝ (⊤ : ℕ∞) e)
    (heven : Function.Even e) :
    ContDiffOn ℝ (⊤ : ℕ∞) (evenSquareDesc e)
      (Set.Ici (0 : ℝ)) := by
  rw [contDiffOn_infty]
  intro n
  exact evenSquareDesc_contDiffOn_nat n e he heven

/-- A smooth even real function is a smooth function of the square.
The factor is global; only its values on the nonnegative half-line are
canonical. -/
theorem exists_contDiff_comp_sq_of_even
    (e : ℝ → ℝ)
    (he : ContDiff ℝ (⊤ : ℕ∞) e)
    (heven : Function.Even e) :
    ∃ E : ℝ → ℝ,
      ContDiff ℝ (⊤ : ℕ∞) E ∧
      ∀ x : ℝ, e x = E (x ^ 2) := by
  let g : ℝ → ℝ → ℝ :=
    fun s _ => evenSquareDesc e s
  have hg :
      ContDiffOn ℝ (⊤ : ℕ∞)
        (Function.uncurry g)
        (Set.Ici (0 : ℝ) ×ˢ (Set.univ : Set ℝ)) := by
    have hdesc := evenSquareDesc_contDiffOn e he heven
    have hfst :
        ContDiffOn ℝ (⊤ : ℕ∞)
          (fun q : ℝ × ℝ => q.1)
          (Set.Ici (0 : ℝ) ×ˢ (Set.univ : Set ℝ)) :=
      contDiff_fst.contDiffOn
    exact hdesc.comp hfst
      (fun q hq => hq.1)
  obtain ⟨gext, V, hV, hgext, hext⟩ :=
    DifferentialGeometry.Analysis.borel_halfLine_extend_param
      g (Set.univ : Set ℝ) 0 (by simp) hg
  have h0V : (0 : ℝ) ∈ V :=
    mem_of_mem_nhds hV
  let E : ℝ → ℝ := fun s => gext s 0
  have hE : ContDiff ℝ (⊤ : ℕ∞) E := by
    have hpair :
        ContDiff ℝ (⊤ : ℕ∞)
          (fun s : ℝ => (s, (0 : ℝ))) :=
      contDiff_id.prodMk contDiff_const
    have hcomp :
        ContDiffOn ℝ (⊤ : ℕ∞)
          (fun s : ℝ => Function.uncurry gext (s, 0))
          (Set.univ : Set ℝ) :=
      hgext.comp hpair.contDiffOn
        (fun s _ => ⟨Set.mem_univ s, h0V⟩)
    exact contDiffOn_univ.mp hcomp
  refine ⟨E, hE, ?_⟩
  intro x
  have hxnonneg : 0 ≤ x ^ 2 := sq_nonneg x
  have heq :
      E (x ^ 2) = evenSquareDesc e (x ^ 2) := by
    exact hext (x ^ 2) hxnonneg 0 h0V
  rw [heq, evenSquareDesc, Real.sqrt_sq_eq_abs]
  by_cases hx : 0 ≤ x
  · rw [abs_of_nonneg hx]
  · rw [abs_of_neg (lt_of_not_ge hx)]
    exact (heven x).symm

/-- A smooth odd real function is the coordinate times a global smooth
function of the square. -/
theorem exists_contDiff_mul_comp_sq_of_odd
    (p : ℝ → ℝ)
    (hp : ContDiff ℝ (⊤ : ℕ∞) p)
    (hodd : Function.Odd p) :
    ∃ P : ℝ → ℝ,
      ContDiff ℝ (⊤ : ℕ∞) P ∧
      ∀ x : ℝ, p x = x * P (x ^ 2) := by
  have hqSmooth := smoothOddQuotient_contDiff p hp
  have hqEven := smoothOddQuotient_even p hp hodd
  obtain ⟨P, hP, hfactor⟩ :=
    exists_contDiff_comp_sq_of_even
      (smoothOddQuotient p) hqSmooth hqEven
  refine ⟨P, hP, ?_⟩
  intro x
  rw [eq_mul_smoothOddQuotient p hp hodd x,
    hfactor x]

end RicciFlowSharpEstimate.Analysis
