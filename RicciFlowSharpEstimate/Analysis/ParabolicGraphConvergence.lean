/-
Copyright (c) 2026 Ziyang Qin. All rights reserved.
No license is granted by this file.
Authors: Ziyang Qin
-/
import RicciFlowSharpEstimate.Analysis.L2StrongMultipliers
import RicciFlowSharpEstimate.Analysis.ParabolicSobolev
import Mathlib.Analysis.Calculus.Deriv.Mul

/-!
# Scalar multiplication in the strong parabolic graph topology

A convergent family of real scalars preserves strong raw `L²` convergence
over an arbitrary measure. Applying this to the three coordinates of the
parabolic graph proves convergence for the actual first and second
derivatives of rescaled `C²` probes. No endpoint conditions are imposed.
-/

noncomputable section

namespace RicciFlowSharpEstimate.Analysis

open Filter MeasureTheory Set
open scoped ContDiff Topology

/-- Convergent real scalars preserve strong raw `L²` convergence over any
measure and along any filter. The proof uses continuous scalar multiplication
in `Lp`, so no uniform bound on the scalars is required as a hypothesis. -/
theorem strong_L2_const_mul_of_tendsto
    {Ω ι : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {l : Filter ι}
    {u : ι → Ω → ℝ} {u0 : Ω → ℝ} {a : ι → ℝ} {a0 : ℝ}
    (hu : ∀ n, MemLp (u n) 2 μ) (hu0 : MemLp u0 2 μ)
    (hstrong : Tendsto (fun n ↦ eLpNorm (u n - u0) 2 μ) l (𝓝 0))
    (ha : Tendsto a l (𝓝 a0)) :
    Tendsto (fun n ↦ eLpNorm (fun x ↦ a n * u n x - a0 * u0 x) 2 μ)
      l (𝓝 0) := by
  have hU := (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' u hu u0 hu0).mpr hstrong
  have hscaled := ha.smul hU
  have hscaledLp :
      Tendsto (fun n ↦ ((hu n).const_smul (a n)).toLp (a n • u n)) l
        (𝓝 ((hu0.const_smul a0).toLp (a0 • u0))) := by
    exact hscaled
  have hscaledNorm := (Lp.tendsto_Lp_iff_tendsto_eLpNorm''
    (fun n ↦ a n • u n) (fun n ↦ (hu n).const_smul (a n))
    (a0 • u0) (hu0.const_smul a0)).mp hscaledLp
  exact hscaledNorm

local notation "areaμ" => volume.restrict (Ioo (0 : ℝ) 1)

/-- Scalar multiplication by a convergent real sequence preserves all three
strong parabolic graph convergences for actual `C²` probes and their actual
derivatives. The limit is the scalar multiple of the supplied weak graph;
no boundary conditions or positivity assumptions on the scalars are needed. -/
theorem parabolicGraph_tendsto_const_mul
    {r : ℕ → ℝ → ℝ} {r0 p0 z0 : ℝ → ℝ} {a : ℕ → ℝ} {a0 : ℝ}
    (hr : ∀ n, ContDiff ℝ 2 (r n))
    (hgraph : HasParabolicWeakDerivatives r0 p0 z0)
    (ha : Tendsto a atTop (𝓝 a0))
    (hR : Tendsto (fun n ↦ eLpNorm (r n - r0) 2 areaμ) atTop (𝓝 0))
    (hP : Tendsto (fun n ↦ eLpNorm
      ((fun x ↦ Real.sqrt (x * (1 - x)) * deriv (r n) x) -
        (fun x ↦ Real.sqrt (x * (1 - x)) * p0 x)) 2 areaμ) atTop (𝓝 0))
    (hZ : Tendsto (fun n ↦ eLpNorm
      ((fun x ↦ x * (1 - x) * Real.sqrt (x * (1 - x)) * deriv (deriv (r n)) x) -
        (fun x ↦ x * (1 - x) * Real.sqrt (x * (1 - x)) * z0 x)) 2 areaμ)
      atTop (𝓝 0)) :
    Tendsto (fun n ↦ eLpNorm
      ((fun x ↦ a n * r n x) - (fun x ↦ a0 * r0 x)) 2 areaμ) atTop (𝓝 0) ∧
    Tendsto (fun n ↦ eLpNorm
      ((fun x ↦ Real.sqrt (x * (1 - x)) * deriv (fun y ↦ a n * r n y) x) -
        (fun x ↦ Real.sqrt (x * (1 - x)) * (a0 * p0 x))) 2 areaμ) atTop (𝓝 0) ∧
    Tendsto (fun n ↦ eLpNorm
      ((fun x ↦ x * (1 - x) * Real.sqrt (x * (1 - x)) *
        deriv (deriv (fun y ↦ a n * r n y)) x) -
        (fun x ↦ x * (1 - x) * Real.sqrt (x * (1 - x)) * (a0 * z0 x))) 2 areaμ)
      atTop (𝓝 0) := by
  have hgraphs (n : ℕ) := hasParabolicWeakDerivatives_of_contDiff (hr n)
  have hRscaled := strong_L2_const_mul_of_tendsto
    (fun n ↦ (hgraphs n).memLp) hgraph.memLp hR ha
  have hPscaled := strong_L2_const_mul_of_tendsto
    (fun n ↦ (hgraphs n).memLp_weighted_deriv) hgraph.memLp_weighted_deriv hP ha
  have hZscaled := strong_L2_const_mul_of_tendsto
    (fun n ↦ (hgraphs n).memLp_weighted_secondDeriv)
    hgraph.memLp_weighted_secondDeriv hZ ha
  refine ⟨hRscaled, ?_, ?_⟩
  · apply hPscaled.congr' (Eventually.of_forall ?_)
    intro n
    apply eLpNorm_congr_ae
    filter_upwards [] with x
    simp only [Pi.sub_apply, deriv_const_mul_field']
    ring
  · apply hZscaled.congr' (Eventually.of_forall ?_)
    intro n
    apply eLpNorm_congr_ae
    filter_upwards [] with x
    simp only [Pi.sub_apply, deriv_const_mul_field']
    ring

end RicciFlowSharpEstimate.Analysis
