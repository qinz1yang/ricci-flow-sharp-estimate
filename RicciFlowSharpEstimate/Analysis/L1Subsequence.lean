/-
Copyright (c) 2026 Ziyang Qin. All rights reserved.
No license is granted by this file.
Authors: Ziyang Qin
-/
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Almost-everywhere subsequences from L1 convergence
-/

noncomputable section

open Filter MeasureTheory

namespace RicciFlowSharpEstimate.Analysis.L1Subsequence

/-- Integrable differences with `L1` error tending to zero yield a
pointwise almost-everywhere convergent subsequence. -/
theorem exists_strictMono_ae_tendsto_of_integral_norm_tendsto_zero
    {X : Type*} [MeasurableSpace X]
    (mu : Measure X) (f : ℕ → X → ℝ) (g : X → ℝ)
    (hIntegrable : ∀ n, Integrable (fun x ↦ f n x - g x) mu)
    (hL1 : Tendsto (fun n ↦ (∫ x, ‖f n x - g x‖ ∂mu))
      atTop (nhds 0)) :
    ∃ ns : ℕ → ℕ, StrictMono ns ∧
      ∀ᵐ x ∂mu, Tendsto (fun n ↦ f (ns n) x) atTop (nhds (g x)) := by
  have hLp : Tendsto
      (fun n ↦ eLpNorm (f n - g) 1 mu) atTop (nhds 0) := by
    have hEq : ∀ n, eLpNorm (f n - g) 1 mu =
        ENNReal.ofReal (∫ x, ‖f n x - g x‖ ∂mu) := by
      intro n
      calc
        eLpNorm (f n - g) 1 mu = ∫⁻ x, ‖(f n - g) x‖ₑ ∂mu :=
          eLpNorm_one_eq_lintegral_enorm (hIntegrable n).aestronglyMeasurable
        _ = ENNReal.ofReal (∫ x, ‖(f n - g) x‖ ∂mu) :=
          (ofReal_integral_norm_eq_lintegral_enorm (hIntegrable n)).symm
        _ = ENNReal.ofReal (∫ x, ‖f n x - g x‖ ∂mu) := by rfl
    simp_rw [hEq]
    simpa using ENNReal.tendsto_ofReal hL1
  exact (tendstoInMeasure_of_tendsto_eLpNorm
    (p := (1 : ENNReal)) one_ne_zero hLp).exists_seq_tendsto_ae

end RicciFlowSharpEstimate.Analysis.L1Subsequence

end
