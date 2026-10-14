/-
Copyright (c) 2026 Ziyang Qin. All rights reserved.
No license is granted by this file.
Authors: Ziyang Qin
-/
import RicciFlowSharpEstimate.Geometry.AreaInverseRecovery
import RicciFlowSharpEstimate.Geometry.AreaRawGraphRecovery
import RicciFlowSharpEstimate.Geometry.RecoverableAreaGeometry
import RicciFlowSharpEstimate.Analysis.SmoothSourceSplit
import RicciFlowSharpEstimate.Analysis.ParabolicGraphAddition

/-!
# Simultaneous recoverable inverse splitting of the actual operator

The positive and negative parts of the literal weak source have nonnegative
inverse components on the same curvature. Their difference is the original
probe in all three genuine graph coordinates. One common original curvature
sequence recovers every linear combination, with complete action and mass
limits and justified positive-mass normalization. No action sign is inferred
for the sum of the components.
-/

noncomputable section
namespace RicciFlowSharpEstimate.Geometry.AreaProfile
open Set MeasureTheory Filter Topology
open scoped ContDiff ENNReal
local notation "areaμ" => volume.restrict (Ioo (0 : ℝ) 1)

private theorem nonneg_continuous_limit
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

/-- Every recoverable probe with continuous interior representatives admits
the actual positive/negative-source inverse split. Raw zero components are
allowed. All linear combinations have one common same-cap recovery, genuine
value limits, and recoverable normalization whenever their physical mass is
positive. The sum has mass at least one, but its action is not asserted zero. -/
theorem IsRecoverableAreaCompetitor.exists_nonnegative_operator_split
    {C : ℝ} {K r p z : ℝ → ℝ} (hC : 1 ≤ C)
    (h : IsRecoverableAreaCompetitor C K r p z)
    (hr : ContinuousOn r (Ioo (0 : ℝ) 1))
    (hp : ContinuousOn p (Ioo (0 : ℝ) 1)) :
    ∃ (u pu zu v pv zv : ℝ → ℝ) (Ks us vs : ℕ → ℝ → ℝ),
      Analysis.HasParabolicWeakDerivatives u pu zu ∧
      Analysis.HasParabolicWeakDerivatives v pv zv ∧
      ContinuousOn u (Ioo (0 : ℝ) 1) ∧ ContinuousOn pu (Ioo (0 : ℝ) 1) ∧
      ContinuousOn v (Ioo (0 : ℝ) 1) ∧ ContinuousOn pv (Ioo (0 : ℝ) 1) ∧
      (∀ x ∈ Ioo (0 : ℝ) 1, 0 ≤ u x ∧ 0 ≤ v x) ∧
      r = (fun x => v x - u x) ∧ p = (fun x => pv x - pu x) ∧
      z = (fun x => zv x - zu x) ∧
      (∀ᵐ x ∂areaμ, -weakMeridionalOperator K u pu zu x =
        max (weakMeridionalOperator K r p z x) 0) ∧
      (∀ᵐ x ∂areaμ, -weakMeridionalOperator K v pv zv x =
        max (-weakMeridionalOperator K r p z x) 0) ∧
      (∀ n, IsSmoothAreaCurvature C (Ks n)) ∧
      (∀ n, ContDiff ℝ ∞ (us n) ∧ ContDiff ℝ ∞ (vs n) ∧
        (∀ x ∈ Icc (0 : ℝ) 1, 0 ≤ us n x ∧ 0 ≤ vs n x ∧
          meridionalOperator (Ks n) (us n) x ≤ 0 ∧
          meridionalOperator (Ks n) (vs n) x ≤ 0)) ∧
      Tendsto (fun n => eLpNorm (Ks n - K) 2 areaμ) atTop (𝓝 0) ∧
      (∀ᵐ x ∂areaμ, Tendsto (fun n => Ks n x) atTop (𝓝 (K x))) ∧
      1 ≤ probeMass K (fun x => u x + v x) ∧
      (∀ a b : ℝ,
        let R : ℝ → ℝ := fun x => a * u x + b * v x
        let P : ℝ → ℝ := fun x => a * pu x + b * pv x
        let Z : ℝ → ℝ := fun x => a * zu x + b * zv x
        let Rs : ℕ → ℝ → ℝ := fun n x => a * us n x + b * vs n x
        Analysis.HasParabolicWeakDerivatives R P Z ∧
        Tendsto (fun n => eLpNorm (Rs n - R) 2 areaμ) atTop (𝓝 0) ∧
        Tendsto (fun n => eLpNorm
          ((fun x => Real.sqrt (x * (1 - x)) * deriv (Rs n) x) -
            (fun x => Real.sqrt (x * (1 - x)) * P x)) 2 areaμ) atTop (𝓝 0) ∧
        Tendsto (fun n => eLpNorm
          ((fun x => x * (1 - x) * Real.sqrt (x * (1 - x)) * deriv (deriv (Rs n)) x) -
            (fun x => x * (1 - x) * Real.sqrt (x * (1 - x)) * Z x)) 2 areaμ)
          atTop (𝓝 0) ∧
        IntegrableOn (fun x => meridionalActionDensity (warp K x) (warpSlope K x)
          (K x) (R x) (P x) (Z x)) (Ioo (0 : ℝ) 1) ∧
        IntegrableOn (fun x => warp K x * R x ^ 2) (Ioo (0 : ℝ) 1) ∧
        Tendsto (fun n => meridionalAction (Ks n) (Rs n)) atTop
          (𝓝 (weakMeridionalAction K R P Z)) ∧
        Tendsto (fun n => probeMass (Ks n) (Rs n)) atTop (𝓝 (probeMass K R)) ∧
        (0 < probeMass K R → IsRecoverableAreaCompetitor C K (normalizedProbe K R)
          (fun x => (1 / Real.sqrt (probeMass K R)) * P x)
          (fun x => (1 / Real.sqrt (probeMass K R)) * Z x))) := by
  have hCpos : 0 < C := zero_lt_one.trans_le hC
  obtain ⟨Ks, rs, hS, hKL, hrL, hpL, hzL, hKae⟩ := h.strong_curvature_subsequence
  have hKs (n : ℕ) := (hS n).curvature_admissible
  have hrs (n : ℕ) := (hS n).2.1
  have hr2 (n : ℕ) : ContDiff ℝ 2 (rs n) := (hrs n).of_le (by simp)
  let q := weakMeridionalOperator K r p z
  let qs : ℕ → ℝ → ℝ := fun n => meridionalOperator (Ks n) (rs n)
  have hq := weighted_meridionalOperator_tendsto_of_strong_graph C hC Ks rs K r p z
    hKs h.curvature_bounded hr2 h.2.1 hKL hKae hrL hpL hzL
  have hqs (n : ℕ) : ContDiff ℝ ∞ (qs n) :=
    meridionalOperator_contDiff (Ks n) (rs n) (hKs n).1 (hrs n)
  obtain ⟨gp, gm, hgsm, hgspos, hgsdiff, _, hgp, _, hgpL, _⟩ :=
    Analysis.exists_smooth_nonnegative_source_split qs q
      (fun x => Real.sqrt (x * (1 - x))) hqs (by fun_prop)
      (fun x _ => Real.sqrt_nonneg _) hq.2.1 hq.2.2
  obtain ⟨u, pu, zu, us, hgu, huc, hpuc, hupos, huq, hus, huL, hpuL, hzuL⟩ :=
    exists_nonnegative_meridional_inverse_recovery C hC K (fun x => max (q x) 0)
      Ks gp h.curvature_bounded hKs (fun n => (hgsm n).1)
      (fun n x _ => (hgspos n x).1) hgp hKL hKae hgpL
  let v : ℝ → ℝ := fun x => r x + u x
  let pv : ℝ → ℝ := fun x => p x + pu x
  let zv : ℝ → ℝ := fun x => z x + zu x
  let vs : ℕ → ℝ → ℝ := fun n x => rs n x + us n x
  have hgv : Analysis.HasParabolicWeakDerivatives v pv zv := h.2.1.add hgu
  have hvc : ContinuousOn v (Ioo (0 : ℝ) 1) := hr.add huc
  have hpvc : ContinuousOn pv (Ioo (0 : ℝ) 1) := hp.add hpuc
  have hvs (n : ℕ) : ContDiff ℝ ∞ (vs n) := (hrs n).add (hus n).1
  have hvq (n : ℕ) (x : ℝ) (hx : x ∈ Icc (0 : ℝ) 1) :
      -meridionalOperator (Ks n) (vs n) x = gm n x := by
    have hlin := meridionalOperator_add_mul (Ks n) (rs n) (us n) (hrs n) (hus n).1 1 x
    simp only [one_mul] at hlin
    have hu := (hus n).2.1 x hx
    have hdiff := hgsdiff n x
    change gp n x - gm n x = meridionalOperator (Ks n) (rs n) x at hdiff
    change -(meridionalOperator (Ks n) (fun y => rs n y + us n y) x) = gm n x
    linarith only [hlin, hu, hdiff]
  have hvpos (n : ℕ) : ∀ x ∈ Icc (0 : ℝ) 1, 0 ≤ vs n x := by
    apply nonneg_of_meridionalOperator_nonpos (Ks n) (vs n) (hKs n).1.continuous
      (fun x hx => (by positivity : (0 : ℝ) < 2 / C).trans_le
        ((hKs n).common_bounds x hx).1)
      ((hvs n).of_le (by simp)) (hKs n).2.2.1 (hKs n).2.2.2
    intro x hx
    linarith only [hvq n x hx, (hgspos n x).2]
  have hvL := Analysis.parabolicGraph_tendsto_add hr2
    (fun n => (hus n).1.of_le (by simp)) hrL hpL hzL huL hpuL hzuL
  have hvnonneg : ∀ x ∈ Ioo (0 : ℝ) 1, 0 ≤ v x :=
    nonneg_continuous_limit hvpos hvc hvL.1
  have hvq0 : ∀ᵐ x ∂areaμ, -weakMeridionalOperator K v pv zv x = max (-q x) 0 := by
    filter_upwards [huq] with x hx
    have heq : weakMeridionalOperator K v pv zv x =
        q x + weakMeridionalOperator K u pu zu x := by
      dsimp only [weakMeridionalOperator, q, v, pv, zv]
      ring
    by_cases hqx : 0 ≤ q x
    · rw [max_eq_left hqx] at hx
      rw [max_eq_right (neg_nonpos.mpr hqx)]
      linarith only [heq, hx]
    · have hqn := (lt_of_not_ge hqx).le
      rw [max_eq_right hqn] at hx
      rw [max_eq_left (neg_nonneg.mpr hqn)]
      linarith only [heq, hx]
  have hlin (a b : ℝ) :
      let R : ℝ → ℝ := fun x => a * u x + b * v x
      let P : ℝ → ℝ := fun x => a * pu x + b * pv x
      let Z : ℝ → ℝ := fun x => a * zu x + b * zv x
      let Rs : ℕ → ℝ → ℝ := fun n x => a * us n x + b * vs n x
      Analysis.HasParabolicWeakDerivatives R P Z ∧
      Tendsto (fun n => eLpNorm (Rs n - R) 2 areaμ) atTop (𝓝 0) ∧
      Tendsto (fun n => eLpNorm
        ((fun x => Real.sqrt (x * (1 - x)) * deriv (Rs n) x) -
          (fun x => Real.sqrt (x * (1 - x)) * P x)) 2 areaμ) atTop (𝓝 0) ∧
      Tendsto (fun n => eLpNorm
        ((fun x => x * (1 - x) * Real.sqrt (x * (1 - x)) * deriv (deriv (Rs n)) x) -
          (fun x => x * (1 - x) * Real.sqrt (x * (1 - x)) * Z x)) 2 areaμ)
        atTop (𝓝 0) ∧
      IntegrableOn (fun x => meridionalActionDensity (warp K x) (warpSlope K x)
        (K x) (R x) (P x) (Z x)) (Ioo (0 : ℝ) 1) ∧
      IntegrableOn (fun x => warp K x * R x ^ 2) (Ioo (0 : ℝ) 1) ∧
      Tendsto (fun n => meridionalAction (Ks n) (Rs n)) atTop
        (𝓝 (weakMeridionalAction K R P Z)) ∧
      Tendsto (fun n => probeMass (Ks n) (Rs n)) atTop (𝓝 (probeMass K R)) ∧
      (0 < probeMass K R → IsRecoverableAreaCompetitor C K (normalizedProbe K R)
        (fun x => (1 / Real.sqrt (probeMass K R)) * P x)
        (fun x => (1 / Real.sqrt (probeMass K R)) * Z x)) := by
    dsimp only
    have hga := hgu.const_mul a
    have hgb := hgv.const_mul b
    have haL := Analysis.parabolicGraph_tendsto_const_mul
      (fun n => (hus n).1.of_le (by simp)) hgu
      (tendsto_const_nhds (x := a)) huL hpuL hzuL
    have hbL := Analysis.parabolicGraph_tendsto_const_mul
      (fun n => (hvs n).of_le (by simp)) hgv
      (tendsto_const_nhds (x := b)) hvL.1 hvL.2.1 hvL.2.2
    have habL := Analysis.parabolicGraph_tendsto_add
      (fun n => (contDiff_const.mul (hus n).1).of_le (by simp))
      (fun n => (contDiff_const.mul (hvs n)).of_le (by simp))
      haL.1 haL.2.1 haL.2.2 hbL.1 hbL.2.1 hbL.2.2
    have hpass := h.curvature_bounded.raw_graph_recovery hC (hga.add hgb) Ks
      (fun n x => a * us n x + b * vs n x) hKs
      (fun n => (contDiff_const.mul (hus n).1).add (contDiff_const.mul (hvs n)))
      hKL hKae habL.1 habL.2.1 habL.2.2
    exact ⟨hga.add hgb, habL.1, habL.2.1, habL.2.2, hpass⟩
  have hsum := hlin 1 1
  simp only [one_mul] at hsum
  have hmassR := (h.exists_action_recovery hC).2.1
  have hmassSum := hsum.2.2.2.2.2.1
  have hmass : 1 ≤ probeMass K (fun x => u x + v x) := by
    rw [← h.2.2.2.2.2.1]
    unfold probeMass
    simp only [intervalIntegral.integral_of_le zero_le_one, integral_Ioc_eq_integral_Ioo]
    apply integral_mono_ae hmassR hmassSum
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
    have hgeom := (h.geometry_bounds hC).2.2.1 x ⟨hx.1.le, hx.2.le⟩
    have hf : 0 ≤ warp K x :=
      (mul_nonneg (mul_nonneg (by positivity : (0 : ℝ) ≤ 2 / C) hx.1.le)
        (sub_nonneg.mpr hx.2.le)).trans hgeom.1
    have heq : r x = v x - u x := by dsimp only [v]; ring
    have hs : r x ^ 2 ≤ (u x + v x) ^ 2 := by
      rw [heq]
      nlinarith only [mul_nonneg (hupos x hx) (hvnonneg x hx)]
    exact mul_le_mul_of_nonneg_left hs hf
  refine ⟨u, pu, zu, v, pv, zv, Ks, us, vs, hgu, hgv, huc, hpuc, hvc, hpvc,
    (fun x hx => ⟨hupos x hx, hvnonneg x hx⟩), ?_, ?_, ?_, huq, hvq0,
    hKs, ?_, hKL, hKae, hmass, hlin⟩
  · funext x
    dsimp only [v]
    ring
  · funext x
    dsimp only [pv]
    ring
  · funext x
    dsimp only [zv]
    ring
  · intro n
    refine ⟨(hus n).1, hvs n, ?_⟩
    intro x hx
    refine ⟨(hus n).2.2 x hx, hvpos n x hx, ?_, ?_⟩
    · linarith only [(hus n).2.1 x hx, (hgspos n x).1]
    · linarith only [hvq n x hx, (hgspos n x).2]

end RicciFlowSharpEstimate.Geometry.AreaProfile
