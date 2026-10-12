/-
Copyright (c) 2026 Ziyang Qin. All rights reserved.
No license is granted by this file.
Authors: Ziyang Qin
-/
import Mathlib.Analysis.Calculus.ContDiff.Deriv

/-!
# Actual derivatives of equal functions on a closed interval

On a nondegenerate closed interval, equality of twice continuously differentiable
functions determines both actual derivatives, including at the endpoints.
-/

namespace RicciFlowSharpEstimate.Analysis

open Set

/-- Equality of C² functions on a closed interval determines the same first and
second actual derivatives on that interval. -/
theorem eqOn_derivatives_Icc (a b : ℝ) (hab : a < b) (f g : ℝ → ℝ)
    (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g) (heq : EqOn f g (Icc a b)) :
    EqOn (deriv f) (deriv g) (Icc a b) ∧
      EqOn (deriv (deriv f)) (deriv (deriv g)) (Icc a b) := by
  have hi : EqOn f g (Ioo a b) := heq.mono Ioo_subset_Icc_self
  have hd := hi.deriv isOpen_Ioo
  have hdd := hd.deriv isOpen_Ioo
  have hf1 : ContDiff ℝ 1 (deriv f) := hf.deriv'
  have hg1 : ContDiff ℝ 1 (deriv g) := hg.deriv'
  constructor
  · have hc := hd.closure (hf.continuous_deriv (by norm_num)) (hg.continuous_deriv (by norm_num))
    simpa only [closure_Ioo hab.ne] using hc
  · have hc := hdd.closure hf1.continuous_deriv_one hg1.continuous_deriv_one
    simpa only [closure_Ioo hab.ne] using hc

end RicciFlowSharpEstimate.Analysis
