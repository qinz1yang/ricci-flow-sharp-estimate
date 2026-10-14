/-
Copyright (c) 2026 Ziyang Qin. All rights reserved.
No license is granted by this file.
Authors: Ziyang Qin
-/
import RicciFlowSharpEstimate.Analysis.ParabolicGraphConvergence
import Mathlib.Analysis.Calculus.Deriv.Add

/-!
# Addition in the strong parabolic graph topology

Adding two actual C² probe sequences preserves their three strong graph
limits. The summed sequence uses its actual first and second derivatives.
The norm estimate needs no additional weak-graph or membership hypotheses.
-/

noncomputable section

namespace RicciFlowSharpEstimate.Analysis

open Set MeasureTheory Filter
open scoped ContDiff Topology

private theorem graph_add_strong_L2
    {Ω ι : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {l : Filter ι}
    {f g : ι → Ω → ℝ} {f0 g0 : Ω → ℝ}
    (hf : Tendsto (fun n => eLpNorm (f n - f0) 2 μ) l (𝓝 0))
    (hg : Tendsto (fun n => eLpNorm (g n - g0) 2 μ) l (𝓝 0)) :
    Tendsto (fun n => eLpNorm
      ((fun x => f n x + g n x) - (fun x => f0 x + g0 x)) 2 μ) l (𝓝 0) := by
  have hsumRaw := hf.add hg
  have hsum : Tendsto (fun n => eLpNorm (f n - f0) 2 μ + eLpNorm (g n - g0) 2 μ)
      l (𝓝 0) := by
    simpa only [zero_add] using hsumRaw
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsum
    (fun _ => zero_le)
  intro n
  have heq : ((fun x => f n x + g n x) - (fun x => f0 x + g0 x)) =
      (f n - f0) + (g n - g0) := by
    funext x
    simp only [Pi.sub_apply, Pi.add_apply]
    ring
  dsimp only
  rw [heq]
  exact eLpNorm_add_le (by norm_num)

local notation "areaμ" => volume.restrict (Ioo (0 : ℝ) 1)

/-- Two C² probe sequences converging in all three parabolic graph coordinates
have a literal sum converging to the sums of those same coordinates. No
endpoint, normalization, or additional weak-graph hypotheses are needed. -/
theorem parabolicGraph_tendsto_add
    {rs ss : ℕ → ℝ → ℝ} {r p z u v w : ℝ → ℝ}
    (hrs : ∀ n, ContDiff ℝ 2 (rs n)) (hss : ∀ n, ContDiff ℝ 2 (ss n))
    (hR : Tendsto (fun n => eLpNorm (rs n - r) 2 areaμ) atTop (𝓝 0))
    (hP : Tendsto (fun n => eLpNorm
      ((fun x => Real.sqrt (x * (1 - x)) * deriv (rs n) x) -
        (fun x => Real.sqrt (x * (1 - x)) * p x)) 2 areaμ) atTop (𝓝 0))
    (hZ : Tendsto (fun n => eLpNorm
      ((fun x => x * (1 - x) * Real.sqrt (x * (1 - x)) * deriv (deriv (rs n)) x) -
        (fun x => x * (1 - x) * Real.sqrt (x * (1 - x)) * z x)) 2 areaμ)
      atTop (𝓝 0))
    (hU : Tendsto (fun n => eLpNorm (ss n - u) 2 areaμ) atTop (𝓝 0))
    (hV : Tendsto (fun n => eLpNorm
      ((fun x => Real.sqrt (x * (1 - x)) * deriv (ss n) x) -
        (fun x => Real.sqrt (x * (1 - x)) * v x)) 2 areaμ) atTop (𝓝 0))
    (hW : Tendsto (fun n => eLpNorm
      ((fun x => x * (1 - x) * Real.sqrt (x * (1 - x)) * deriv (deriv (ss n)) x) -
        (fun x => x * (1 - x) * Real.sqrt (x * (1 - x)) * w x)) 2 areaμ)
      atTop (𝓝 0)) :
    Tendsto (fun n => eLpNorm
      ((fun x => rs n x + ss n x) - (fun x => r x + u x)) 2 areaμ) atTop (𝓝 0) ∧
    Tendsto (fun n => eLpNorm
      ((fun x => Real.sqrt (x * (1 - x)) * deriv (fun y => rs n y + ss n y) x) -
        (fun x => Real.sqrt (x * (1 - x)) * (p x + v x))) 2 areaμ) atTop (𝓝 0) ∧
    Tendsto (fun n => eLpNorm
      ((fun x => x * (1 - x) * Real.sqrt (x * (1 - x)) *
        deriv (deriv (fun y => rs n y + ss n y)) x) -
        (fun x => x * (1 - x) * Real.sqrt (x * (1 - x)) * (z x + w x))) 2 areaμ)
      atTop (𝓝 0) := by
  have hd (n : ℕ) : deriv (fun x => rs n x + ss n x) =
      fun x => deriv (rs n) x + deriv (ss n) x := by
    funext x
    exact (((hrs n).differentiable (by norm_num) x).hasDerivAt.add
      ((hss n).differentiable (by norm_num) x).hasDerivAt).deriv
  have hdd (n : ℕ) : deriv (deriv (fun x => rs n x + ss n x)) =
      fun x => deriv (deriv (rs n)) x + deriv (deriv (ss n)) x := by
    rw [hd n]
    funext x
    exact (((hrs n).differentiable_deriv_two x).hasDerivAt.add
      ((hss n).differentiable_deriv_two x).hasDerivAt).deriv
  have hRsum := graph_add_strong_L2 hR hU
  have hPsum := graph_add_strong_L2 hP hV
  have hZsum := graph_add_strong_L2 hZ hW
  refine ⟨hRsum, ?_, ?_⟩
  · apply hPsum.congr' (Eventually.of_forall ?_)
    intro n
    apply eLpNorm_congr_ae
    filter_upwards [] with x
    simp only [Pi.sub_apply, hd n]
    ring
  · apply hZsum.congr' (Eventually.of_forall ?_)
    intro n
    apply eLpNorm_congr_ae
    filter_upwards [] with x
    simp only [Pi.sub_apply, hdd n]
    ring

end RicciFlowSharpEstimate.Analysis
