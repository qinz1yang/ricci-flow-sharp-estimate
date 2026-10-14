/-
Copyright (c) 2026 Ziyang Qin. All rights reserved.
No license is granted by this file.
Authors: Ziyang Qin
-/
import RicciFlowSharpEstimate.Geometry.AreaSmoothInverse
import RicciFlowSharpEstimate.Geometry.AreaInverseGraphCauchy
import RicciFlowSharpEstimate.Geometry.AreaOperatorGraphContinuity
import Mathlib.MeasureTheory.Measure.OpenPos

/-!
# Nonnegative inverse recovery on a prescribed curvature sequence

The smooth inverse on each member of one original curvature recovery converges
in the full parabolic graph. The limit solves the literal weak equation and
has nonnegative continuous interior representatives. Sources with weighted L²
control, including zero, are allowed; raw components are not mass-normalized.
-/

noncomputable section
namespace RicciFlowSharpEstimate.Geometry.AreaProfile
open Set MeasureTheory Filter Topology
open scoped ContDiff ENNReal
local notation "areaμ" => volume.restrict (Ioo (0 : ℝ) 1)

private theorem nonneg_of_strong_limit
    {us : ℕ → ℝ → ℝ} {u : ℝ → ℝ}
    (hpos : ∀ n x, x ∈ Icc (0 : ℝ) 1 → 0 ≤ us n x)
    (hu : ContinuousOn u (Ioo (0 : ℝ) 1))
    (hL : Tendsto (fun n => eLpNorm (us n - u) 2 areaμ) atTop (𝓝 0)) :
    ∀ x ∈ Ioo (0 : ℝ) 1, 0 ≤ u x := by
  obtain ⟨ψ, _, hpoint⟩ :=
    (tendstoInMeasure_of_tendsto_eLpNorm
      (p := (2 : ENNReal)) (by norm_num) hL).exists_seq_tendsto_ae
  have hnonneg : ∀ᵐ x ∂areaμ, 0 ≤ u x := by
    filter_upwards [hpoint, ae_restrict_mem measurableSet_Ioo] with x hx hxI
    exact ge_of_tendsto' hx (fun n => hpos (ψ n) x ⟨hxI.1.le, hxI.2.le⟩)
  have heq : u =ᵐ[areaμ] (fun x => max (u x) 0) := by
    filter_upwards [hnonneg] with x hx
    exact (max_eq_left hx).symm
  have hsame := Measure.eqOn_open_of_ae_eq heq isOpen_Ioo hu (hu.sup continuousOn_const)
  intro x hx
  rw [hsame hx]
  exact le_max_right _ _

/-- Nonnegative smooth source approximations on one prescribed original
curvature recovery produce a nonnegative actual inverse in the full weak graph.
The very same curvature sequence and globally smooth inverse probes recover
all three displayed jets; no mass or nonzero hypothesis is required. -/
theorem exists_nonnegative_meridional_inverse_recovery
    (C : ℝ) (hC : 1 ≤ C) (K g : ℝ → ℝ) (Ks gs : ℕ → ℝ → ℝ)
    (hK : IsBoundedAreaCurvature C K)
    (hKs : ∀ n, IsSmoothAreaCurvature C (Ks n))
    (hgs : ∀ n, ContDiff ℝ ∞ (gs n))
    (hgpos : ∀ n x, x ∈ Icc (0 : ℝ) 1 → 0 ≤ gs n x)
    (hg : MemLp (fun x => Real.sqrt (x * (1 - x)) * g x) 2 areaμ)
    (hKL : Tendsto (fun n => eLpNorm (Ks n - K) 2 areaμ) atTop (𝓝 0))
    (hKae : ∀ᵐ x ∂areaμ, Tendsto (fun n => Ks n x) atTop (𝓝 (K x)))
    (hgL : Tendsto (fun n => eLpNorm
      ((fun x => Real.sqrt (x * (1 - x)) * gs n x) -
        (fun x => Real.sqrt (x * (1 - x)) * g x)) 2 areaμ) atTop (𝓝 0)) :
    ∃ (u p z : ℝ → ℝ) (us : ℕ → ℝ → ℝ),
      Analysis.HasParabolicWeakDerivatives u p z ∧
      ContinuousOn u (Ioo (0 : ℝ) 1) ∧ ContinuousOn p (Ioo (0 : ℝ) 1) ∧
      (∀ x ∈ Ioo (0 : ℝ) 1, 0 ≤ u x) ∧
      (∀ᵐ x ∂areaμ, -weakMeridionalOperator K u p z x = g x) ∧
      (∀ n, ContDiff ℝ ∞ (us n) ∧
        (∀ x ∈ Icc (0 : ℝ) 1, -meridionalOperator (Ks n) (us n) x = gs n x) ∧
        (∀ x ∈ Icc (0 : ℝ) 1, 0 ≤ us n x)) ∧
      Tendsto (fun n => eLpNorm (us n - u) 2 areaμ) atTop (𝓝 0) ∧
      Tendsto (fun n => eLpNorm
        ((fun x => Real.sqrt (x * (1 - x)) * deriv (us n) x) -
          (fun x => Real.sqrt (x * (1 - x)) * p x)) 2 areaμ) atTop (𝓝 0) ∧
      Tendsto (fun n => eLpNorm
        ((fun x => x * (1 - x) * Real.sqrt (x * (1 - x)) * deriv (deriv (us n)) x) -
          (fun x => x * (1 - x) * Real.sqrt (x * (1 - x)) * z x)) 2 areaμ)
        atTop (𝓝 0) := by
  have hCpos : 0 < C := zero_lt_one.trans_le hC
  have hex (n : ℕ) : ∃ u : ℝ → ℝ, ContDiff ℝ ∞ u ∧
      (∀ x ∈ Icc (0 : ℝ) 1, -meridionalOperator (Ks n) u x = gs n x) ∧
      (∀ x ∈ Icc (0 : ℝ) 1, 0 ≤ u x) := by
    obtain ⟨u, hu, heq, hpos, _⟩ := exists_smooth_meridional_inverse (Ks n) (gs n)
      (hKs n).1 (hgs n)
      (fun x hx => (by positivity : (0 : ℝ) < 2 / C).trans_le
        ((hKs n).common_bounds x hx).1)
      (hKs n).2.2.1 (hKs n).2.2.2
    exact ⟨u, hu, heq, hpos (hgpos n)⟩
  choose us hus heq hpos using hex
  have hu2 (n : ℕ) : ContDiff ℝ 2 (us n) := (hus n).of_le (by simp)
  have hc := cauchy_parabolic_graph_of_inverse_sources C hC Ks us gs K g
    hKs hu2 heq hK.memLp_curvature hg hKL hgL
  obtain ⟨u, p, z, hgraph, hu, hp, huL, hpL, hzL⟩ :=
    Analysis.exists_parabolic_graph_limit_of_cauchy us (fun n => deriv (us n))
      (fun n => deriv (deriv (us n)))
      (fun n => Analysis.hasParabolicWeakDerivatives_of_contDiff (hu2 n)) hc
  have hQ := weighted_meridionalOperator_tendsto_of_strong_graph C hC Ks us K u p z
    hKs hK hu2 hgraph hKL hKae huL hpL hzL
  have hneg : MemLp (fun x => -(Real.sqrt (x * (1 - x)) * g x)) 2 areaμ := hg.neg
  have hQL : Tendsto (fun n => eLpNorm
      ((fun x => Real.sqrt (x * (1 - x)) * meridionalOperator (Ks n) (us n) x) -
        (fun x => -(Real.sqrt (x * (1 - x)) * g x))) 2 areaμ) atTop (𝓝 0) := by
    apply hgL.congr' (Eventually.of_forall ?_)
    intro n
    have he : ((fun x => Real.sqrt (x * (1 - x)) * meridionalOperator (Ks n) (us n) x) -
        (fun x => -(Real.sqrt (x * (1 - x)) * g x))) =ᵐ[areaμ]
        -((fun x => Real.sqrt (x * (1 - x)) * gs n x) -
          (fun x => Real.sqrt (x * (1 - x)) * g x)) := by
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
      have hsolve := heq n x ⟨hx.1.le, hx.2.le⟩
      simp only [Pi.sub_apply, Pi.neg_apply]
      nlinarith only [congrArg (fun t => Real.sqrt (x * (1 - x)) * t) hsolve]
    exact ((eLpNorm_congr_ae he).trans (eLpNorm_neg _ _ _)).symm
  have hA := (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' _ hQ.1 _ hQ.2.1).mpr hQ.2.2
  have hB := (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' _ hQ.1 _ hneg).mpr hQL
  have hweighted := (MemLp.toLp_eq_toLp_iff hQ.2.1 hneg).mp (tendsto_nhds_unique hA hB)
  have hsolve : ∀ᵐ x ∂areaμ, -weakMeridionalOperator K u p z x = g x := by
    filter_upwards [hweighted, ae_restrict_mem measurableSet_Ioo] with x hx hxI
    have hs : 0 < Real.sqrt (x * (1 - x)) :=
      Real.sqrt_pos.mpr (mul_pos hxI.1 (sub_pos.mpr hxI.2))
    have he : Real.sqrt (x * (1 - x)) * (-weakMeridionalOperator K u p z x) =
        Real.sqrt (x * (1 - x)) * g x := by linarith only [hx]
    exact (mul_left_cancel₀ hs.ne') he
  exact ⟨u, p, z, us, hgraph, hu, hp, nonneg_of_strong_limit hpos hu huL,
    hsolve, fun n => ⟨hus n, heq n, hpos n⟩, huL, hpL, hzL⟩

end RicciFlowSharpEstimate.Geometry.AreaProfile
