/-
Copyright (c) 2026 Ziyang Qin. All rights reserved.
No license is granted by this file.
Authors: Ziyang Qin
-/
import DifferentialGeometry.Analysis.Calculus.Taylor

/-!
# Smooth factorization at the two endpoints

Two applications of the released Hadamard factorization give a global smooth
factor of `1 - x^2` for a smooth function vanishing at both endpoints.
-/

namespace RicciFlowSharpEstimate.Analysis

open DifferentialGeometry.Analysis.Calculus

/-- A globally smooth function vanishing at `-1` and `1` has a globally smooth
factor of `1 - x^2`, with the factorization valid on the whole real line. -/
theorem exists_contDiff_one_sub_sq_factor_of_roots (p : ℝ → ℝ)
    (hp : ContDiff ℝ (⊤ : ℕ∞) p) (hneg : p (-1) = 0) (hpos : p 1 = 0) :
    ∃ b : ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) b ∧ ∀ x : ℝ, p x = (1 - x ^ 2) * b x := by
  obtain ⟨a, ha, hpa⟩ := exists_contDiff_hadamardFactor p hp (-1)
  simp only [hneg, sub_zero, smul_eq_mul] at hpa
  have ha1 : a 1 = 0 := by
    have h := hpa 1
    norm_num [hpos] at h
    linarith only [h]
  obtain ⟨b, hb, hab⟩ := exists_contDiff_hadamardFactor a ha 1
  simp only [ha1, sub_zero, smul_eq_mul] at hab
  refine ⟨fun x => -b x, hb.neg, ?_⟩
  intro x
  rw [hpa x, hab x]
  ring

end RicciFlowSharpEstimate.Analysis
