/-
Copyright (c) 2026 Ziyang Qin. All rights reserved.
No license is granted by this file.
Authors: Ziyang Qin
-/
import RicciFlowSharpEstimate.Analysis.ParabolicSobolev
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul

/-!
# Linear operations on the parabolic weak derivative graph

Weak derivatives on any domain are closed under addition and real scalar
multiplication. The compact-test identities and their local integrability
conditions are preserved by the same operations. Applying these identities
to both derivatives, together with weighted `L²` addition and scaling, gives
the corresponding algebra for the parabolic graph.

A fixed smooth perturbation preserves strong convergence in all three graph
coordinates, with the actual first and second derivatives of the perturbed
probes. No endpoint conditions are imposed.
-/

noncomputable section

namespace RicciFlowSharpEstimate.Analysis

open Filter MeasureTheory Set
open scoped ContDiff Topology

/-- The sum of two weak derivatives is the weak derivative of the sum on
the same domain. No openness assumption on the domain is needed. -/
theorem HasWeakDerivOn.add
    {U : Set ℝ} {r p s q : ℝ → ℝ}
    (hr : HasWeakDerivOn U r p) (hs : HasWeakDerivOn U s q) :
    HasWeakDerivOn U (fun x ↦ r x + s x) (fun x ↦ p x + q x) := by
  refine ⟨hr.locallyIntegrable.add hs.locallyIntegrable,
    hr.locallyIntegrable_deriv.add hs.locallyIntegrable_deriv, ?_⟩
  intro φ hφ hφc hφU
  simp only [mul_add]
  rw [integral_add
      (hr.integrable_deriv_test_mul hφ hφc hφU)
      (hs.integrable_deriv_test_mul hφ hφc hφU),
    integral_add
      (hr.integrable_test_mul_weakDeriv hφ.continuous hφc hφU)
      (hs.integrable_test_mul_weakDeriv hφ.continuous hφc hφU),
    hr.integral_deriv_mul φ hφ hφc hφU,
    hs.integral_deriv_mul φ hφ hφc hφU]
  ring

/-- Multiplication by a real constant preserves a weak derivative and
scales both representatives by that same constant. -/
theorem HasWeakDerivOn.const_mul
    {U : Set ℝ} {r p : ℝ → ℝ} (hr : HasWeakDerivOn U r p) (c : ℝ) :
    HasWeakDerivOn U (fun x ↦ c * r x) (fun x ↦ c * p x) := by
  refine ⟨?_, ?_, ?_⟩
  · exact hr.locallyIntegrable.smul c
  · exact hr.locallyIntegrable_deriv.smul c
  · intro φ hφ hφc hφU
    have hleft : (fun x ↦ deriv φ x * (c * r x)) =
        (fun x ↦ c * (deriv φ x * r x)) := by
      funext x
      ring
    have hright : (fun x ↦ φ x * (c * p x)) =
        (fun x ↦ c * (φ x * p x)) := by
      funext x
      ring
    rw [hleft, hright, integral_const_mul, integral_const_mul,
      hr.integral_deriv_mul φ hφ hφc hφU, mul_neg]

/-- Addition preserves both genuine weak derivatives and all three
weighted `L²` conditions in the parabolic graph. -/
theorem HasParabolicWeakDerivatives.add
    {r p z s q v : ℝ → ℝ}
    (hR : HasParabolicWeakDerivatives r p z)
    (hS : HasParabolicWeakDerivatives s q v) :
    HasParabolicWeakDerivatives
      (fun x ↦ r x + s x) (fun x ↦ p x + q x) (fun x ↦ z x + v x) := by
  refine ⟨hR.weakDeriv.add hS.weakDeriv,
    hR.weakDeriv_deriv.add hS.weakDeriv_deriv, hR.memLp.add hS.memLp, ?_, ?_⟩
  · refine (memLp_congr_ae ?_).1 (hR.memLp_weighted_deriv.add hS.memLp_weighted_deriv)
    filter_upwards [] with x
    simp only [Pi.add_apply]
    ring
  · refine (memLp_congr_ae ?_).1
      (hR.memLp_weighted_secondDeriv.add hS.memLp_weighted_secondDeriv)
    filter_upwards [] with x
    simp only [Pi.add_apply]
    ring

/-- A real constant scales the entire parabolic weak derivative graph,
including its two genuine derivatives and their weighted `L²` conditions. -/
theorem HasParabolicWeakDerivatives.const_mul
    {r p z : ℝ → ℝ} (hR : HasParabolicWeakDerivatives r p z) (c : ℝ) :
    HasParabolicWeakDerivatives
      (fun x ↦ c * r x) (fun x ↦ c * p x) (fun x ↦ c * z x) := by
  refine ⟨hR.weakDeriv.const_mul c, hR.weakDeriv_deriv.const_mul c,
    hR.memLp.const_mul c, ?_, ?_⟩
  · refine (memLp_congr_ae ?_).1 (hR.memLp_weighted_deriv.const_mul c)
    filter_upwards [] with x
    ring
  · refine (memLp_congr_ae ?_).1 (hR.memLp_weighted_secondDeriv.const_mul c)
    filter_upwards [] with x
    ring

local notation "areaμ" => volume.restrict (Ioo (0 : ℝ) 1)

/-- Adding a fixed `C²` perturbation preserves all three strong parabolic
graph convergences. The perturbed probes use their actual derivatives, and
each limit coordinate is perturbed by the corresponding actual derivative
of the fixed function. -/
theorem parabolicGraph_tendsto_add_fixed_smooth
    {rn : ℕ → ℝ → ℝ} {r p z : ℝ → ℝ}
    (hRnC2 : ∀ n, ContDiff ℝ 2 (rn n))
    (hStrong3 :
      Tendsto (fun n ↦ eLpNorm (rn n - r) 2 areaμ) atTop (𝓝 0) ∧
      Tendsto (fun n ↦ eLpNorm
        ((fun x ↦ Real.sqrt (x * (1 - x)) * deriv (rn n) x) -
          (fun x ↦ Real.sqrt (x * (1 - x)) * p x)) 2 areaμ) atTop (𝓝 0) ∧
      Tendsto (fun n ↦ eLpNorm
        ((fun x ↦ x * (1 - x) * Real.sqrt (x * (1 - x)) * deriv (deriv (rn n)) x) -
          (fun x ↦ x * (1 - x) * Real.sqrt (x * (1 - x)) * z x)) 2 areaμ)
        atTop (𝓝 0))
    (s : ℝ → ℝ) (hs : ContDiff ℝ 2 s) (t : ℝ) :
    Tendsto (fun n ↦ eLpNorm
      ((fun x ↦ rn n x + t * s x) - (fun x ↦ r x + t * s x)) 2 areaμ)
      atTop (𝓝 0) ∧
    Tendsto (fun n ↦ eLpNorm
      ((fun x ↦ Real.sqrt (x * (1 - x)) * deriv (fun y ↦ rn n y + t * s y) x) -
        (fun x ↦ Real.sqrt (x * (1 - x)) * (p x + t * deriv s x))) 2 areaμ)
      atTop (𝓝 0) ∧
    Tendsto (fun n ↦ eLpNorm
      ((fun x ↦ x * (1 - x) * Real.sqrt (x * (1 - x)) *
        deriv (deriv (fun y ↦ rn n y + t * s y)) x) -
        (fun x ↦ x * (1 - x) * Real.sqrt (x * (1 - x)) *
          (z x + t * deriv (deriv s) x))) 2 areaμ) atTop (𝓝 0) := by
  have hd (n : ℕ) : deriv (fun x ↦ rn n x + t * s x) =
      (fun x ↦ deriv (rn n) x + t * deriv s x) := by
    funext x
    rw [deriv_fun_add ((hRnC2 n).differentiable (by norm_num) x)
      ((hs.differentiable (by norm_num) x).const_mul t), deriv_const_mul_field]
  have hdd (n : ℕ) : deriv (deriv (fun x ↦ rn n x + t * s x)) =
      (fun x ↦ deriv (deriv (rn n)) x + t * deriv (deriv s) x) := by
    rw [hd n]
    funext x
    rw [deriv_fun_add ((hRnC2 n).differentiable_deriv_two x)
      ((hs.differentiable_deriv_two x).const_mul t), deriv_const_mul_field]
  refine ⟨?_, ?_, ?_⟩
  · apply hStrong3.1.congr' (Eventually.of_forall ?_)
    intro n
    apply eLpNorm_congr_ae
    filter_upwards [] with x
    simp only [Pi.sub_apply]
    ring
  · apply hStrong3.2.1.congr' (Eventually.of_forall ?_)
    intro n
    apply eLpNorm_congr_ae
    filter_upwards [] with x
    simp only [Pi.sub_apply, hd]
    ring
  · apply hStrong3.2.2.congr' (Eventually.of_forall ?_)
    intro n
    apply eLpNorm_congr_ae
    filter_upwards [] with x
    simp only [Pi.sub_apply, hdd]
    ring

end RicciFlowSharpEstimate.Analysis
