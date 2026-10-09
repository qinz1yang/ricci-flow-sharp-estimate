/-
Copyright (c) 2026 Ziyang Qin. All rights reserved.
No license is granted by this file.
Authors: Ziyang Qin
-/
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Fourier.AddCircle

/-!
# Sharp periodic Wirtinger inequality

A real continuously differentiable function with matching endpoints and zero mean on `[0, 2π]`
satisfies the sharp inequality between the integrals of its square and its derivative squared.
The proof uses Parseval's identity and the derivative multiplier on Fourier coefficients.
The Fourier calculation adapts Ziyang Qin's historical `CircleWirtinger.lean`;
the natural C¹ statement derives its analytic integrability hypotheses internally.
-/

namespace RicciFlowSharpEstimate.Analysis

open MeasureTheory
open scoped Interval

/-- Fourier coefficients of a periodic function and its derivative on
an interval of length `2π` satisfy the exact multiplier identity. -/
private theorem fourierCoeffOn_deriv_eq_mul
    (f f' : ℝ → ℂ)
    (hfDeriv : ∀ x : ℝ, HasDerivAt f (f' x) x)
    (hfPeriod : f (2 * Real.pi) = f 0)
    (hf'Int : IntervalIntegrable f' volume 0 (2 * Real.pi))
    (n : ℤ) (hn : n ≠ 0) :
    fourierCoeffOn (by positivity : (0 : ℝ) < 2 * Real.pi) f' n =
      Complex.I * (n : ℂ) *
        fourierCoeffOn (by positivity : (0 : ℝ) < 2 * Real.pi) f n := by
  let hperiod : (0 : ℝ) < 2 * Real.pi := by positivity
  have h :=
    fourierCoeffOn_of_hasDerivAt hperiod hn
      (fun x _ => hfDeriv x) hf'Int
  rw [hfPeriod, sub_self, mul_zero, zero_sub] at h
  norm_num at h
  have hnComplex : (n : ℂ) ≠ 0 := by exact_mod_cast hn
  have hpiComplex : (Real.pi : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  field_simp [hnComplex, hpiComplex] at h
  calc
    fourierCoeffOn hperiod f' n =
        Complex.I *
          (-(Complex.I * fourierCoeffOn hperiod f' n)) := by
            rw [mul_neg, ← mul_assoc, Complex.I_mul_I]
            ring
    _ = Complex.I *
          (fourierCoeffOn hperiod f n * (n : ℂ)) := by
            rw [h]
    _ = Complex.I * (n : ℂ) *
          fourierCoeffOn hperiod f n := by ring

/-- A zero angular mean removes precisely the zero Fourier
coefficient. -/
private theorem fourierCoeffOn_zero_eq_zero_of_integral_eq_zero
    (f : ℝ → ℂ)
    (hmean : (∫ x : ℝ in 0..2 * Real.pi, f x) = 0) :
    fourierCoeffOn (by positivity : (0 : ℝ) < 2 * Real.pi) f 0 = 0 := by
  rw [fourierCoeffOn_eq_integral]
  simp [hmean]

/-- Pointwise domination of all Fourier coefficient squares by those
of the derivative. -/
private theorem norm_fourierCoeffOn_sq_le_deriv
    (f f' : ℝ → ℂ)
    (hfDeriv : ∀ x : ℝ, HasDerivAt f (f' x) x)
    (hfPeriod : f (2 * Real.pi) = f 0)
    (hmean : (∫ x : ℝ in 0..2 * Real.pi, f x) = 0)
    (hf'Int : IntervalIntegrable f' volume 0 (2 * Real.pi))
    (n : ℤ) :
    ‖fourierCoeffOn (by positivity : (0 : ℝ) < 2 * Real.pi) f n‖ ^ 2 ≤
      ‖fourierCoeffOn (by positivity : (0 : ℝ) < 2 * Real.pi) f' n‖ ^ 2 := by
  by_cases hn : n = 0
  · subst n
    rw [fourierCoeffOn_zero_eq_zero_of_integral_eq_zero f hmean]
    simp
  have hCoeff :=
    fourierCoeffOn_deriv_eq_mul f f' hfDeriv hfPeriod hf'Int n hn
  rw [hCoeff, norm_mul, norm_mul]
  have hnAbs : (1 : ℝ) ≤ |(n : ℝ)| := by
    exact_mod_cast (Int.one_le_abs hn)
  simp only [Complex.norm_I, one_mul, Complex.norm_intCast]
  have hnormNonneg :
      0 ≤ ‖fourierCoeffOn
        (by positivity : (0 : ℝ) < 2 * Real.pi) f n‖ := norm_nonneg _
  rw [sq_le_sq₀ hnormNonneg
    (mul_nonneg (abs_nonneg (n : ℝ)) hnormNonneg)]
  nlinarith

/-- Sharp periodic Wirtinger inequality on the circle of length `2π`,
in the complex-valued form convenient for Parseval. -/
private theorem intervalIntegral_norm_sq_le_deriv_of_mean_zero
    (f f' : ℝ → ℂ)
    (hfDeriv : ∀ x : ℝ, HasDerivAt f (f' x) x)
    (hfPeriod : f (2 * Real.pi) = f 0)
    (hmean : (∫ x : ℝ in 0..2 * Real.pi, f x) = 0)
    (hf : Continuous f) (hf' : Continuous f') :
    (∫ x : ℝ in 0..2 * Real.pi, ‖f x‖ ^ 2) ≤
      ∫ x : ℝ in 0..2 * Real.pi, ‖f' x‖ ^ 2 := by
  let hperiod : (0 : ℝ) < 2 * Real.pi := by positivity
  have hfMem : MemLp f 2 (volume.restrict (Set.Ioc 0 (2 * Real.pi))) :=
    (memLp_two_iff_integrable_sq_norm hf.aestronglyMeasurable).mpr
      ((intervalIntegrable_iff_integrableOn_Ioc_of_le hperiod.le).mp
        ((hf.norm.pow 2).intervalIntegrable _ _))
  have hf'Mem : MemLp f' 2 (volume.restrict (Set.Ioc 0 (2 * Real.pi))) :=
    (memLp_two_iff_integrable_sq_norm hf'.aestronglyMeasurable).mpr
      ((intervalIntegrable_iff_integrableOn_Ioc_of_le hperiod.le).mp
        ((hf'.norm.pow 2).intervalIntegrable _ _))
  have hf'Int : IntervalIntegrable f' volume 0 (2 * Real.pi) :=
    hf'.intervalIntegrable _ _
  have hParsevalF :=
    hasSum_sq_fourierCoeffOn hperiod hfMem
  have hParsevalF' :=
    hasSum_sq_fourierCoeffOn hperiod hf'Mem
  have hSum :
      (∑' n : ℤ,
        ‖fourierCoeffOn hperiod f n‖ ^ 2) ≤
      ∑' n : ℤ,
        ‖fourierCoeffOn hperiod f' n‖ ^ 2 := by
    exact hParsevalF.summable.tsum_le_tsum
      (fun n =>
        norm_fourierCoeffOn_sq_le_deriv
          f f' hfDeriv hfPeriod hmean hf'Int n)
      hParsevalF'.summable
  rw [hParsevalF.tsum_eq, hParsevalF'.tsum_eq] at hSum
  simp only [sub_zero, smul_eq_mul] at hSum
  have hTwoPiPos : 0 < 2 * Real.pi := by positivity
  nlinarith [inv_pos.mpr hTwoPiPos]

/-- The sharp periodic Wirtinger inequality for a real continuously differentiable function
with zero mean on the circle of length `2π`. -/
theorem integral_sq_le_deriv_sq_of_periodic_mean_zero
    (f : ℝ → ℝ) (hf : ContDiff ℝ 1 f)
    (hperiod : f (2 * Real.pi) = f 0)
    (hmean : (∫ x in 0..2 * Real.pi, f x) = 0) :
    (∫ x in 0..2 * Real.pi, f x ^ 2) ≤
      ∫ x in 0..2 * Real.pi, deriv f x ^ 2 := by
  have hd := (contDiff_one_iff_deriv.mp hf).1
  have hc := intervalIntegral_norm_sq_le_deriv_of_mean_zero
    (fun x : ℝ => (f x : ℂ)) (fun x : ℝ => ((deriv f x : ℝ) : ℂ))
    (fun x => (hd x).hasDerivAt.ofReal_comp)
    (by simpa only [Complex.ofReal_inj] using hperiod)
    (by rw [intervalIntegral.integral_ofReal]; simp only [hmean, Complex.ofReal_zero])
    (Complex.continuous_ofReal.comp hf.continuous)
    (Complex.continuous_ofReal.comp hf.continuous_deriv_one)
  simpa only [Complex.norm_real, Real.norm_eq_abs, sq_abs] using hc

end RicciFlowSharpEstimate.Analysis
