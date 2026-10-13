/-
Copyright (c) 2026 Ziyang Qin. All rights reserved.
No license is granted by this file.
Authors: Ziyang Qin
-/
import RicciFlowSharpEstimate.Geometry.AreaActionPolarControl
import RicciFlowSharpEstimate.Analysis.InteriorSobolevCompactness
import RicciFlowSharpEstimate.Analysis.ParabolicSobolev
import RicciFlowSharpEstimate.Analysis.L2UniformIntegrability
import RicciFlowSharpEstimate.Analysis.WeakDerivativeLimits
import RicciFlowSharpEstimate.Analysis.WeightedWeakDerivativeLimit
import RicciFlowSharpEstimate.Analysis.HilbertWeakSubsequence
import Mathlib.MeasureTheory.Measure.SeparableMeasure

/-!
# Interior probe limits of normalized complete-action sublevels

The accepted complete-action estimates supply the weighted graph bounds used
in the actual subsequence theorem for probes and their first derivatives.
-/

noncomputable section

namespace RicciFlowSharpEstimate.Geometry.AreaProfile

open Set MeasureTheory Filter Topology
open scoped ContDiff

private theorem parabolic_second_deriv_bound (K r : ℝ → ℝ)
    (hK : Continuous K) (hr : ContDiff ℝ 2 r) (lo hi : ℝ) (hlo : 0 < lo)
    (hbox : ∀ x ∈ Icc (0 : ℝ) 1, lo ≤ K x ∧ K x ≤ hi)
    (hzero : (∫ x in (0 : ℝ)..1, K x) = 2)
    (hone : (∫ x in (0 : ℝ)..1, x * K x) = 1) :
    lo ^ 3 * (∫ x in (0 : ℝ)..1, (x * (1 - x)) ^ 3 * deriv (deriv r) x ^ 2) ≤
      2 * probeOperatorEnergy K r + 2 * hi ^ 2 * probeMass K r := by
  have hf := warp_continuous K hK
  have hr2 := hr.deriv'.continuous_deriv_one
  have hw : Continuous (fun x : ℝ => x * (1 - x)) := by fun_prop
  have hJ : lo ^ 3 * (∫ x in (0 : ℝ)..1, (x * (1 - x)) ^ 3 * deriv (deriv r) x ^ 2) ≤
      ∫ x in (0 : ℝ)..1, warp K x ^ 3 * deriv (deriv r) x ^ 2 := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_mono_on zero_le_one
      ((continuous_const.mul ((hw.pow 3).mul (hr2.pow 2))).intervalIntegrable 0 1)
      (((hf.pow 3).mul (hr2.pow 2)).intervalIntegrable 0 1)
    intro x hx
    have hbound := quadratic_le_warp_of_curvature_lower K hK lo
      (fun y hy => (hbox y hy).1) hzero hone x hx
    have hpos : 0 ≤ lo * x * (1 - x) :=
      mul_nonneg (mul_nonneg hlo.le hx.1) (sub_nonneg.mpr hx.2)
    have hs := pow_le_pow_left₀ hpos hbound 3
    have hm := mul_le_mul_of_nonneg_right hs (sq_nonneg (deriv (deriv r) x))
    simpa only [Pi.mul_apply, Pi.pow_apply, mul_pow, mul_assoc] using hm
  exact hJ.trans (integral_warp_cube_second_deriv_sq_le K r hK hr hi
    (fun x hx => ⟨hlo.le.trans (hbox x hx).1, (hbox x hx).2⟩) hzero hone)

/-- Normalized complete-action sublevels yield a single subsequence of probes
and actual first derivatives converging locally uniformly in the interior. -/
theorem exists_subseq_locallyUniform_probe_deriv_of_action_bound
    (K r : ℕ → ℝ → ℝ) (hK : ∀ n, Continuous (K n)) (hr : ∀ n, ContDiff ℝ 2 (r n))
    (lo hi : ℝ) (hlo : 0 < lo)
    (hbox : ∀ n x, x ∈ Icc (0 : ℝ) 1 → lo ≤ K n x ∧ K n x ≤ hi)
    (hzero : ∀ n, (∫ x in (0 : ℝ)..1, K n x) = 2)
    (hone : ∀ n, (∫ x in (0 : ℝ)..1, x * K n x) = 1)
    (hmass : ∀ n, probeMass (K n) (r n) = 1) (B : ℝ)
    (hA : ∀ n, meridionalAction (K n) (r n) ≤ B) :
    ∃ g p : C(Ioo (0 : ℝ) 1, ℝ), ∃ φ : ℕ → ℕ, StrictMono φ ∧
      TendstoLocallyUniformly (fun n (x : Ioo (0 : ℝ) 1) => r (φ n) x) g atTop ∧
      TendstoLocallyUniformly (fun n (x : Ioo (0 : ℝ) 1) => deriv (r (φ n)) x) p atTop := by
  have hhi : 0 ≤ hi := hlo.le.trans ((hbox 0 0 (by norm_num)).1.trans
    (hbox 0 0 (by norm_num)).2)
  obtain ⟨M, hM, hMb⟩ := exists_uniform_probe_regularity_bound lo hi hlo hhi B
  let J := (2 * M + 2 * hi ^ 2) / lo ^ 3
  have hJ : 0 ≤ J := by dsimp [J]; positivity
  apply Analysis.exists_subseq_locallyUniform_probe_deriv_of_weighted_energy r hr (M + J)
  intro n
  obtain ⟨hE, hU, _, hH⟩ := hMb (K n) (r n) (hK n) (hr n) (hbox n)
    (hzero n) (hone n) (hmass n) (hA n)
  have hsecond := parabolic_second_deriv_bound (K n) (r n) (hK n) (hr n)
    lo hi hlo (hbox n) (hzero n) (hone n)
  rw [hmass n, mul_one] at hsecond
  have hsecondBound :
      (∫ x in (0 : ℝ)..1, (x * (1 - x)) ^ 3 * deriv (deriv (r n)) x ^ 2) ≤ J := by
    apply (le_div_iff₀ (pow_pos hlo 3)).mpr
    nlinarith only [hsecond, hE]
  exact ⟨by linarith, by linarith, by linarith⟩


private theorem polar_square_complement (r : ℝ → ℝ) (hr : Continuous r)
    (δ : ℝ) (hδ : 0 ≤ δ) (hhalf : δ ≤ 1 / 2) :
    (∫ x in (Icc δ (1 - δ))ᶜ, r x ^ 2 ∂(volume.restrict (Ioo (0 : ℝ) 1))) =
      (∫ x in (0 : ℝ)..δ, r x ^ 2) + ∫ x in (1 - δ)..1, r x ^ 2 := by
  have hset : (Icc δ (1 - δ))ᶜ ∩ Ioo (0 : ℝ) 1 = Ioo 0 δ ∪ Ioo (1 - δ) 1 := by
    ext x
    simp only [mem_inter_iff, mem_compl_iff, mem_Icc, mem_Ioo, mem_union]
    constructor
    · rintro ⟨hx, hx0, hx1⟩
      by_cases hxd : x < δ
      · exact Or.inl ⟨hx0, hxd⟩
      · exact Or.inr ⟨lt_of_not_ge (fun h => hx ⟨le_of_not_gt hxd, h⟩), hx1⟩
    · rintro (⟨hx0, hxd⟩ | ⟨hxd, hx1⟩)
      · exact ⟨fun h => (not_lt_of_ge h.1) hxd, hx0, by linarith⟩
      · exact ⟨fun h => (not_lt_of_ge h.2) hxd, by linarith, hx1⟩
  have hdisj : Disjoint (Ioo (0 : ℝ) δ) (Ioo (1 - δ) 1) := by
    rw [disjoint_left]
    intro x hx hy
    linarith [hx.2, hy.1]
  have hleft : IntegrableOn (fun x => r x ^ 2) (Ioo 0 δ) volume :=
    ((hr.pow 2).continuousOn.integrableOn_compact isCompact_Icc).mono_set Ioo_subset_Icc_self
  have hright : IntegrableOn (fun x => r x ^ 2) (Ioo (1 - δ) 1) volume :=
    ((hr.pow 2).continuousOn.integrableOn_compact isCompact_Icc).mono_set Ioo_subset_Icc_self
  rw [Measure.restrict_restrict measurableSet_Icc.compl, hset,
    setIntegral_union hdisj measurableSet_Ioo hleft hright,
    intervalIntegral.integral_of_le hδ,
    intervalIntegral.integral_of_le (by linarith : 1 - δ ≤ 1),
    integral_Ioc_eq_integral_Ioo, integral_Ioc_eq_integral_Ioo]

private theorem probe_bound_on_interior (r : ℝ → ℝ) (hr : ContDiff ℝ 1 r)
    (M : ℝ)
    (hU : (∫ x in (0 : ℝ)..1, r x ^ 2) ≤ M)
    (hH : (∫ x in (0 : ℝ)..1, x * (1 - x) * deriv r x ^ 2) ≤ M)
    (δ : ℝ) (hδ : 0 < δ) (hhalf : δ < 1 / 2) :
    ∀ x ∈ Icc δ (1 - δ), |r x| ≤
      (2 * M + 2 * (1 - 2 * δ) ^ 2 * (M / δ ^ 2)) / (1 - 2 * δ) + 1 := by
  let d := 1 - 2 * δ
  have hd : 0 < d := by dsimp [d]; linarith
  have hUD : (∫ x in δ..(1 - δ), r x ^ 2) ≤ M :=
    (intervalIntegral.integral_mono_interval hδ.le (by linarith) (by linarith)
      (Filter.Eventually.of_forall fun x => sq_nonneg (r x))
      ((hr.continuous.pow 2).intervalIntegrable 0 1)).trans hU
  have hHD := Analysis.mul_integral_sq_le_parabolic_energy (deriv r)
    hr.continuous_deriv_one δ (1 - δ) hδ (by linarith) (by linarith) 1
  have hPD : (∫ x in δ..(1 - δ), deriv r x ^ 2) ≤ M / δ ^ 2 := by
    apply (le_div_iff₀ (sq_pos_of_pos hδ)).mpr
    simp only [pow_one] at hHD
    nlinarith only [hHD, hH]
  let N := (2 * M + 2 * d ^ 2 * (M / δ ^ 2)) / d
  intro x hx
  change |r x| ≤ N + 1
  have hp := Analysis.length_mul_sq_le_integral_sq_add_integral_deriv_sq r hr
    δ (1 - δ) x (by linarith) hx
  have hPDscaled := mul_le_mul_of_nonneg_left hPD (by positivity : 0 ≤ 2 * d ^ 2)
  have hsq : r x ^ 2 ≤ N := by
    apply (le_div_iff₀ hd).mpr
    dsimp [d] at hPDscaled ⊢
    nlinarith only [hp, hUD, hPDscaled]
  nlinarith only [hsq, sq_abs (r x), sq_nonneg (|r x| - 1)]

/-- Complete-action sublevels are uniformly L² integrable as unweighted
physical probes. This consumes the stronger two-pole estimate directly. -/
theorem uniformIntegrable_probes_of_action_bound
    (K r : ℕ → ℝ → ℝ) (hK : ∀ n, Continuous (K n)) (hr : ∀ n, ContDiff ℝ 2 (r n))
    (lo hi : ℝ) (hlo : 0 < lo)
    (hbox : ∀ n x, x ∈ Icc (0 : ℝ) 1 → lo ≤ K n x ∧ K n x ≤ hi)
    (hzero : ∀ n, (∫ x in (0 : ℝ)..1, K n x) = 2)
    (hone : ∀ n, (∫ x in (0 : ℝ)..1, x * K n x) = 1)
    (hmass : ∀ n, probeMass (K n) (r n) = 1) (B : ℝ)
    (hA : ∀ n, meridionalAction (K n) (r n) ≤ B) :
    UniformIntegrable r 2 (volume.restrict (Ioo (0 : ℝ) 1)) := by
  have hhi : 0 ≤ hi := hlo.le.trans ((hbox 0 0 (by norm_num)).1.trans
    (hbox 0 0 (by norm_num)).2)
  obtain ⟨M, hM, hMb⟩ := exists_uniform_probe_regularity_bound lo hi hlo hhi B
  have hbound (n : ℕ) := hMb (K n) (r n) (hK n) (hr n) (hbox n)
    (hzero n) (hone n) (hmass n) (hA n)
  apply Analysis.uniformIntegrable_two_of_sq_tails r
    (fun n => (Analysis.hasParabolicWeakDerivatives_of_contDiff (hr n)).memLp) M
  · intro n
    have h := (hbound n).2.1
    rwa [intervalIntegral.integral_of_le zero_le_one, integral_Ioc_eq_integral_Ioo] at h
  · intro ε hε
    obtain ⟨δ₀, hδ₀, _, hδall⟩ := exists_uniform_polar_action_radius lo hi hlo hhi B ε hε
    let δ := min δ₀ (1 / 4)
    have hδ : 0 < δ := lt_min hδ₀ (by norm_num)
    have hhalf : δ < 1 / 2 := (min_le_right _ _).trans_lt (by norm_num)
    have htail (n : ℕ) :
        ((∫ x in (0 : ℝ)..δ, r n x ^ 2) + ∫ x in (1 - δ)..1, r n x ^ 2) ≤ ε :=
      (hδall (K n) (r n) (hK n) (hr n) (hbox n) (hzero n) (hone n)
        (hmass n) (hA n) δ ⟨hδ.le, min_le_left _ _⟩).1
    let d := 1 - 2 * δ
    let N := (2 * M + 2 * d ^ 2 * (M / δ ^ 2)) / d
    have hd : 0 < d := by dsimp [d]; linarith
    have hN : 0 ≤ N := by dsimp [N]; positivity
    refine ⟨Icc δ (1 - δ), measurableSet_Icc, N + 1, by positivity, ?_⟩
    intro n
    refine ⟨?_, ?_⟩
    · exact Filter.Eventually.of_forall fun x hx =>
        probe_bound_on_interior (r n) ((hr n).of_le (by norm_num)) M
          (hbound n).2.1 (hbound n).2.2.2 δ hδ hhalf x hx
    · rw [polar_square_complement (r n) (hr n).continuous δ hδ.le hhalf.le]
      exact htail n


local notation "areaμ" => volume.restrict (Ioo (0 : ℝ) 1)

/-- A normalized complete-action sublevel has an actual nonzero global L²
probe limit, with its first weak derivative tied by the test-function identity.
The probes and their actual first derivatives also converge locally uniformly. -/
theorem exists_subseq_strong_probe_of_action_bound
    (K r : ℕ → ℝ → ℝ) (hK : ∀ n, Continuous (K n)) (hr : ∀ n, ContDiff ℝ 2 (r n))
    (lo hi : ℝ) (hlo : 0 < lo)
    (hbox : ∀ n x, x ∈ Icc (0 : ℝ) 1 → lo ≤ K n x ∧ K n x ≤ hi)
    (hzero : ∀ n, (∫ x in (0 : ℝ)..1, K n x) = 2)
    (hone : ∀ n, (∫ x in (0 : ℝ)..1, x * K n x) = 1)
    (hmass : ∀ n, probeMass (K n) (r n) = 1) (B : ℝ)
    (hA : ∀ n, meridionalAction (K n) (r n) ≤ B) :
    ∃ r0 p0 : ℝ → ℝ, ∃ φ : ℕ → ℕ, StrictMono φ ∧
      ContinuousOn r0 (Ioo 0 1) ∧ ContinuousOn p0 (Ioo 0 1) ∧
      Analysis.HasWeakDerivOn (Ioo 0 1) r0 p0 ∧ MemLp r0 2 areaμ ∧
      Tendsto (fun n => eLpNorm (r (φ n) - r0) 2 areaμ) atTop (𝓝 0) ∧
      TendstoLocallyUniformlyOn (fun n => r (φ n)) r0 atTop (Ioo 0 1) ∧
      TendstoLocallyUniformlyOn (fun n => deriv (r (φ n))) p0 atTop (Ioo 0 1) ∧
      1 ≤ (∫ x, r0 x ^ 2 ∂areaμ) ∧ ∃ x ∈ Ioo (0 : ℝ) 1, r0 x ≠ 0 := by
  classical
  obtain ⟨g, p, φ, hφ, hg, hp⟩ := exists_subseq_locallyUniform_probe_deriv_of_action_bound
    K r hK hr lo hi hlo hbox hzero hone hmass B hA
  let r0 : ℝ → ℝ := fun x => if hx : x ∈ Ioo (0 : ℝ) 1 then g ⟨x, hx⟩ else 0
  let p0 : ℝ → ℝ := fun x => if hx : x ∈ Ioo (0 : ℝ) 1 then p ⟨x, hx⟩ else 0
  have hr0eq : (fun x : Ioo (0 : ℝ) 1 => r0 x) = g := by
    funext x
    simp only [r0, dite_eq_left x.property]
  have hp0eq : (fun x : Ioo (0 : ℝ) 1 => p0 x) = p := by
    funext x
    simp only [p0, dite_eq_left x.property]
  have hr0c : ContinuousOn r0 (Ioo 0 1) := by
    rw [continuousOn_iff_continuous_domRestrict]
    change Continuous (fun x : Ioo (0 : ℝ) 1 => r0 x)
    rw [hr0eq]
    exact g.continuous
  have hp0c : ContinuousOn p0 (Ioo 0 1) := by
    rw [continuousOn_iff_continuous_domRestrict]
    change Continuous (fun x : Ioo (0 : ℝ) 1 => p0 x)
    rw [hp0eq]
    exact p.continuous
  have hr0conv : TendstoLocallyUniformlyOn (fun n => r (φ n)) r0 atTop (Ioo 0 1) := by
    rw [tendstoLocallyUniformlyOn_iff_tendstoLocallyUniformly_comp_coe]
    simpa only [Function.comp_def, hr0eq] using hg
  have hp0conv : TendstoLocallyUniformlyOn (fun n => deriv (r (φ n))) p0 atTop (Ioo 0 1) := by
    rw [tendstoLocallyUniformlyOn_iff_tendstoLocallyUniformly_comp_coe]
    simpa only [Function.comp_def, hp0eq] using hp
  have hweak : Analysis.HasWeakDerivOn (Ioo 0 1) r0 p0 :=
    Analysis.hasWeakDerivOn_of_locallyUniformlyOn isOpen_Ioo
      (fun n => Analysis.hasWeakDerivOn_of_contDiff isOpen_Ioo ((hr (φ n)).of_le (by norm_num)))
      (fun n => (hr (φ n)).continuous.continuousOn)
      (fun n => ((hr (φ n)).continuous_deriv (by norm_num)).continuousOn)
      hr0c hp0c hr0conv hp0conv
  have hUI := uniformIntegrable_probes_of_action_bound K r hK hr lo hi hlo
    hbox hzero hone hmass B hA
  have hUIseq : UniformIntegrable (fun n => r (φ n)) 2 areaμ := by
    obtain ⟨hui, M, hM⟩ := hUI
    exact ⟨hui.comp φ, M, fun n => hM (φ n)⟩
  have hae : ∀ᵐ x ∂areaμ, Tendsto (fun n => r (φ n) x) atTop (𝓝 (r0 x)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
    exact hr0conv.tendsto_at hx
  have hmem : MemLp r0 2 areaμ := hUIseq.memLp_of_ae_tendsto hae
  have hmemseq (n : ℕ) : MemLp (r (φ n)) 2 areaμ :=
    (Analysis.hasParabolicWeakDerivatives_of_contDiff (hr (φ n))).memLp
  have hstrong := tendsto_Lp_finite_of_tendsto_ae (by norm_num : (1 : ENNReal) ≤ 2)
    (by simp : (2 : ENNReal) ≠ ⊤) (fun n => (hmemseq n).aestronglyMeasurable)
    hmem hUIseq.unifIntegrable hae
  have hlp : Tendsto (fun n => (hmemseq n).toLp (r (φ n))) atTop (𝓝 (hmem.toLp r0)) := by
    apply tendsto_iff_edist_tendsto_0.mpr
    simpa only [Lp.edist_toLp_toLp] using hstrong
  have hsq (v : ℝ → ℝ) (hv : MemLp v 2 areaμ) :
      ‖hv.toLp v‖ ^ 2 = ∫ x, v x ^ 2 ∂areaμ := by
    calc
      ‖hv.toLp v‖ ^ 2 = inner ℝ (hv.toLp v) (hv.toLp v) := by
        rw [real_inner_self_eq_norm_mul_norm, pow_two]
      _ = _ := by
        rw [L2.inner_def]
        apply integral_congr_ae
        filter_upwards [hv.coeFn_toLp] with x hx
        simp only [Real.inner_apply, hx, pow_two]
  have hsqconv : Tendsto (fun n => ∫ x, r (φ n) x ^ 2 ∂areaμ) atTop
      (𝓝 (∫ x, r0 x ^ 2 ∂areaμ)) := by
    simpa only [hsq] using hlp.norm.pow 2
  have hU (n : ℕ) : 1 ≤ ∫ x, r (φ n) x ^ 2 ∂areaμ := by
    have hbound' : probeMass (K (φ n)) (r (φ n)) ≤
        ∫ x in (0 : ℝ)..1, r (φ n) x ^ 2 := by
      have hf := warp_continuous (K (φ n)) (hK (φ n))
      apply intervalIntegral.integral_mono_on zero_le_one
        ((hf.mul ((hr (φ n)).continuous.pow 2)).intervalIntegrable 0 1)
        (((hr (φ n)).continuous.pow 2).intervalIntegrable 0 1)
      intro x hx
      have hw := warp_nonneg_le_two_mul_min (K (φ n)) (hK (φ n))
        (fun y hy => hlo.le.trans (hbox (φ n) y hy).1) (hzero (φ n)) (hone (φ n)) x hx
      have hw1 : warp (K (φ n)) x ≤ 1 := by
        linarith only [hw.2, min_le_left x (1 - x), min_le_right x (1 - x)]
      simpa only [one_mul, Pi.mul_apply, Pi.pow_apply] using
        mul_le_mul_of_nonneg_right hw1 (sq_nonneg (r (φ n) x))
    rw [hmass (φ n), intervalIntegral.integral_of_le zero_le_one,
      integral_Ioc_eq_integral_Ioo] at hbound'
    exact hbound'
  have hnonzeroMass : 1 ≤ ∫ x, r0 x ^ 2 ∂areaμ := ge_of_tendsto' hsqconv hU
  refine ⟨r0, p0, φ, hφ, hr0c, hp0c, hweak, hmem, hstrong, hr0conv, hp0conv,
    hnonzeroMass, ?_⟩
  by_contra hnone
  have hz : ∀ x ∈ Ioo (0 : ℝ) 1, r0 x = 0 := by
    simpa only [not_exists, not_and, not_not] using hnone
  have hzeroSq : (∫ x, r0 x ^ 2 ∂areaμ) = 0 := by
    have heq : (fun x => r0 x ^ 2) =ᵐ[areaμ] fun _ => (0 : ℝ) := by
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
      simp only [hz x hx, zero_pow (by norm_num : (2 : ℕ) ≠ 0)]
    rw [integral_congr_ae heq, integral_zero]
  linarith


/-- Complete-action sublevels produce an actual nonzero limit in the weighted
weak derivative graph. The weighted second derivatives converge weakly on the
same subsequence as the strong L² and locally uniform probe limits. -/
theorem exists_subseq_weak_probe_of_action_bound
    (K r : ℕ → ℝ → ℝ) (hK : ∀ n, Continuous (K n)) (hr : ∀ n, ContDiff ℝ 2 (r n))
    (lo hi : ℝ) (hlo : 0 < lo)
    (hbox : ∀ n x, x ∈ Icc (0 : ℝ) 1 → lo ≤ K n x ∧ K n x ≤ hi)
    (hzero : ∀ n, (∫ x in (0 : ℝ)..1, K n x) = 2)
    (hone : ∀ n, (∫ x in (0 : ℝ)..1, x * K n x) = 1)
    (hmass : ∀ n, probeMass (K n) (r n) = 1) (B : ℝ)
    (hA : ∀ n, meridionalAction (K n) (r n) ≤ B) :
    ∃ r0 p0 z0 : ℝ → ℝ, ∃ φ : ℕ → ℕ, StrictMono φ ∧
      Analysis.HasParabolicWeakDerivatives r0 p0 z0 ∧
      ContinuousOn r0 (Ioo 0 1) ∧ ContinuousOn p0 (Ioo 0 1) ∧
      Tendsto (fun n => eLpNorm (r (φ n) - r0) 2 areaμ) atTop (𝓝 0) ∧
      TendstoLocallyUniformlyOn (fun n => r (φ n)) r0 atTop (Ioo 0 1) ∧
      TendstoLocallyUniformlyOn (fun n => deriv (r (φ n))) p0 atTop (Ioo 0 1) ∧
      (∀ v : Lp ℝ 2 areaμ,
        Tendsto (fun n => ∫ x, (x * (1 - x) * Real.sqrt (x * (1 - x)) *
          deriv (deriv (r (φ n))) x) * v x ∂areaμ) atTop
          (𝓝 (∫ x, (x * (1 - x) * Real.sqrt (x * (1 - x)) * z0 x) * v x ∂areaμ))) ∧
      1 ≤ (∫ x, r0 x ^ 2 ∂areaμ) ∧ ∃ x ∈ Ioo (0 : ℝ) 1, r0 x ≠ 0 := by
  let : Fact ((2 : ENNReal) ≠ ⊤) := ⟨by norm_num⟩
  obtain ⟨r0, p0, φ, hφ, hr0c, hp0c, hD, hr0mem, hstrong, hr0conv, hp0conv, hU0, hnz⟩ :=
    exists_subseq_strong_probe_of_action_bound K r hK hr lo hi hlo hbox hzero hone hmass B hA
  have hhi : 0 ≤ hi := hlo.le.trans ((hbox 0 0 (by norm_num)).1.trans
    (hbox 0 0 (by norm_num)).2)
  obtain ⟨M, hM, hMb⟩ := exists_uniform_probe_regularity_bound lo hi hlo hhi B
  have hbound (n : ℕ) := hMb (K n) (r n) (hK n) (hr n) (hbox n)
    (hzero n) (hone n) (hmass n) (hA n)
  have hw : Continuous (fun x : ℝ => x * (1 - x)) := by fun_prop
  let a : ℝ → ℝ := fun x => x * (1 - x) * Real.sqrt (x * (1 - x))
  have ha : Continuous a := hw.mul hw.sqrt
  have ha0 : ∀ x ∈ Ioo (0 : ℝ) 1, a x ≠ 0 := by
    intro x hx
    exact (mul_pos (mul_pos hx.1 (sub_pos.mpr hx.2))
      (Real.sqrt_pos.mpr (mul_pos hx.1 (sub_pos.mpr hx.2)))).ne'
  have hPmem (n : ℕ) : MemLp (fun x => Real.sqrt (x * (1 - x)) * deriv (r (φ n)) x) 2 areaμ :=
    (Analysis.hasParabolicWeakDerivatives_of_contDiff (hr (φ n))).memLp_weighted_deriv
  have hPbound (n : ℕ) :
      (∫ x, (Real.sqrt (x * (1 - x)) * deriv (r (φ n)) x) ^ 2 ∂areaμ) ≤ M := by
    have heq : (∫ x, (Real.sqrt (x * (1 - x)) * deriv (r (φ n)) x) ^ 2 ∂areaμ) =
        ∫ x in (0 : ℝ)..1, x * (1 - x) * deriv (r (φ n)) x ^ 2 := by
      rw [intervalIntegral.integral_of_le zero_le_one, integral_Ioc_eq_integral_Ioo]
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
      rw [mul_pow, Real.sq_sqrt (mul_nonneg hx.1.le (sub_nonneg.mpr hx.2.le))]
    rw [heq]
    exact (hbound (φ n)).2.2.2
  have hPpoint : ∀ᵐ x ∂areaμ,
      Tendsto (fun n => Real.sqrt (x * (1 - x)) * deriv (r (φ n)) x) atTop
        (𝓝 (Real.sqrt (x * (1 - x)) * p0 x)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
    exact (hp0conv.tendsto_at hx).const_mul _
  have hp0mem := Analysis.memLp_two_of_ae_tendsto_of_integral_sq_bound
    (fun n x => Real.sqrt (x * (1 - x)) * deriv (r (φ n)) x)
    (fun x => Real.sqrt (x * (1 - x)) * p0 x) hPmem M hPbound hPpoint
  have hZmem (n : ℕ) : MemLp (fun x => a x * deriv (deriv (r (φ n))) x) 2 areaμ :=
    Analysis.memLp_two_Ioo_weighted_deriv ha (hr (φ n)).deriv'
  let Z : ℕ → Lp ℝ 2 areaμ := fun n =>
    (hZmem n).toLp (fun x => a x * deriv (deriv (r (φ n))) x)
  let J := (2 * M + 2 * hi ^ 2) / lo ^ 3
  have hJ : 0 ≤ J := by dsimp [J]; positivity
  have hZbound (n : ℕ) : ‖Z n‖ ≤ J + 1 := by
    have hsecond := parabolic_second_deriv_bound (K (φ n)) (r (φ n)) (hK (φ n))
      (hr (φ n)) lo hi hlo (hbox (φ n)) (hzero (φ n)) (hone (φ n))
    rw [hmass (φ n), mul_one] at hsecond
    have hJB : (∫ x in (0 : ℝ)..1,
        (x * (1 - x)) ^ 3 * deriv (deriv (r (φ n))) x ^ 2) ≤ J := by
      apply (le_div_iff₀ (pow_pos hlo 3)).mpr
      nlinarith only [hsecond, (hbound (φ n)).1]
    have hZsq : ‖Z n‖ ^ 2 = (∫ x in (0 : ℝ)..1,
        (x * (1 - x)) ^ 3 * deriv (deriv (r (φ n))) x ^ 2) := by
      calc
        ‖Z n‖ ^ 2 = inner ℝ (Z n) (Z n) := by
          rw [real_inner_self_eq_norm_mul_norm, pow_two]
        _ = _ := by
          rw [L2.inner_def, intervalIntegral.integral_of_le zero_le_one,
            integral_Ioc_eq_integral_Ioo]
          apply integral_congr_ae
          filter_upwards [(hZmem n).coeFn_toLp, ae_restrict_mem measurableSet_Ioo] with x hx hxI
          change Z n x = a x * deriv (deriv (r (φ n))) x at hx
          rw [Real.inner_apply, hx]
          dsimp [a]
          have hs := Real.sq_sqrt (mul_nonneg hxI.1.le (sub_nonneg.mpr hxI.2.le))
          calc
            _ = (x * (1 - x)) ^ 2 * Real.sqrt (x * (1 - x)) ^ 2 *
                deriv (deriv (r (φ n))) x ^ 2 := by ring
            _ = _ := by rw [hs]; ring
    nlinarith only [hJB, hZsq, sq_nonneg (‖Z n‖ - 1)]
  obtain ⟨Z0, _, ψ, hψ, hZweak⟩ :=
    Analysis.HilbertWeakSubsequence.exists_subseq_tendsto_inner_of_norm_le Z (J + 1) hZbound
  have hsub {F : ℕ → ℝ → ℝ} {f : ℝ → ℝ}
      (h : TendstoLocallyUniformlyOn F f atTop (Ioo 0 1)) :
      TendstoLocallyUniformlyOn (fun n => F (ψ n)) f atTop (Ioo 0 1) := by
    intro V hV x hx
    obtain ⟨s, hs, he⟩ := h V hV x hx
    exact ⟨s, hs, hψ.tendsto_atTop.eventually he⟩
  have hPfinal := hsub hp0conv
  have hRfinal := hsub hr0conv
  have hraw : ∀ v : Lp ℝ 2 areaμ,
      Tendsto (fun n => ∫ x, (a x * deriv (deriv (r (φ (ψ n)))) x) * v x ∂areaμ)
        atTop (𝓝 (∫ x, Z0 x * v x ∂areaμ)) := by
    intro v
    have hpair (n : ℕ) : inner ℝ (Z (ψ n)) v =
        ∫ x, (a x * deriv (deriv (r (φ (ψ n)))) x) * v x ∂areaμ := by
      rw [L2.inner_def]
      apply integral_congr_ae
      filter_upwards [(hZmem (ψ n)).coeFn_toLp] with x hx
      change Z (ψ n) x = a x * deriv (deriv (r (φ (ψ n)))) x at hx
      simp only [Real.inner_apply, hx]
    simpa only [hpair, L2.inner_def, Real.inner_apply] using hZweak v
  let z0 : ℝ → ℝ := fun x => Z0 x / a x
  have hD2 : Analysis.HasWeakDerivOn (Ioo 0 1) p0 z0 :=
    Analysis.hasWeakDerivOn_Ioo_of_weighted_weak_L2_limit ha ha0
      (fun n => (hr (φ (ψ n))).deriv') hp0c hPfinal (Lp.memLp Z0) hraw
  have hzmem : MemLp (fun x => a x * z0 x) 2 areaμ :=
    Analysis.memLp_two_Ioo_weight_mul_div ha0 (Lp.memLp Z0)
  have hgraph : Analysis.HasParabolicWeakDerivatives r0 p0 z0 :=
    ⟨hD, hD2, hr0mem, hp0mem, hzmem⟩
  refine ⟨r0, p0, z0, φ ∘ ψ, hφ.comp hψ, hgraph, hr0c, hp0c,
    hstrong.comp hψ.tendsto_atTop, hRfinal, hPfinal, ?_, hU0, hnz⟩
  intro v
  have hid : (∫ x, (a x * z0 x) * v x ∂areaμ) = ∫ x, Z0 x * v x ∂areaμ := by
    apply integral_congr_ae
    filter_upwards [Analysis.ae_weight_mul_div_Ioo (Z := (Z0 : ℝ → ℝ)) ha0] with x hx
    change a x * z0 x = Z0 x at hx
    rw [hx]
  change Tendsto (fun n => ∫ x, (a x * deriv (deriv (r (φ (ψ n)))) x) * v x ∂areaμ)
    atTop (𝓝 (∫ x, (a x * z0 x) * v x ∂areaμ))
  rw [hid]
  exact hraw v

end RicciFlowSharpEstimate.Geometry.AreaProfile
