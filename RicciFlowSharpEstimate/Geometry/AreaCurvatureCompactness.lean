/-
Copyright (c) 2026 Ziyang Qin. All rights reserved.
No license is granted by this file.
Authors: Ziyang Qin
-/
import RicciFlowSharpEstimate.Analysis.HilbertWeakSubsequence
import RicciFlowSharpEstimate.Analysis.L2WeakOrder
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.SeparableMeasure
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.Topology.Sequences
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

/-!
# Weak compactness of normalized curvature coefficients

A positive a.e. curvature box, a fixed ratio bound, and the two normalized
moments give a weakly convergent subsequence on the unit area interval. Both
bounding scalars converge along the same subsequence. The limit retains its
actual box, its original ratio restriction, and both normalized moments.
-/

noncomputable section

namespace RicciFlowSharpEstimate.Geometry.AreaProfile

open Filter MeasureTheory Set
open scoped ENNReal

local notation "areaμ" => volume.restrict (Ioo (0 : ℝ) 1)

/-- A normalized sequence of measurable curvature coefficients with uniformly
bounded curvature ratio has a weak L2 subsequence. The positive lower and upper
bounding scalars converge along the same subsequence, and their limiting box,
ratio restriction, and both normalized moments are preserved. Membership in L2
is derived from the a.e. box and is not an additional assumption. -/
theorem exists_curvature_subsequence_of_ratio_bound
    (K : ℕ → ℝ → ℝ) (κ Λ : ℕ → ℝ) (C : ℝ)
    (hC : 1 ≤ C)
    (hmeas : ∀ n, AEStronglyMeasurable (K n) areaμ)
    (hκ : ∀ n, 0 < κ n)
    (hbox : ∀ n, ∀ᵐ x ∂areaμ, κ n ≤ K n x ∧ K n x ≤ Λ n)
    (hratio : ∀ n, Λ n / κ n ≤ C)
    (hmass : ∀ n, (∫ x, K n x ∂areaμ) = 2)
    (hmoment : ∀ n, (∫ x, x * K n x ∂areaμ) = 1) :
    ∃ (K0 : ℝ → ℝ) (κ0 Λ0 : ℝ) (φ : ℕ → ℕ),
      MemLp K0 2 areaμ ∧ StrictMono φ ∧
      Tendsto (fun n ↦ κ (φ n)) atTop (nhds κ0) ∧
      Tendsto (fun n ↦ Λ (φ n)) atTop (nhds Λ0) ∧
      (∀ v : Lp ℝ 2 areaμ,
        Tendsto (fun n ↦ ∫ x, K (φ n) x * v x ∂areaμ) atTop
          (nhds (∫ x, K0 x * v x ∂areaμ))) ∧
      (∫ x, K0 x ∂areaμ) = 2 ∧
      (∫ x, x * K0 x ∂areaμ) = 1 ∧
      κ0 ∈ Icc (2 / C) 2 ∧ Λ0 ∈ Icc 2 (2 * C) ∧
      0 < κ0 ∧ Λ0 / κ0 ≤ C ∧
      (∀ᵐ x ∂areaμ, κ0 ≤ K0 x ∧ K0 x ≤ Λ0) := by
  let : IsProbabilityMeasure areaμ := ⟨by simp [Real.volume_Ioo]⟩
  let : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by norm_num⟩
  have hCpos : 0 < C := lt_of_lt_of_le (by norm_num) hC
  have hmem : ∀ n, MemLp (K n) 2 areaμ := fun n ↦
    memLp_of_bounded (hbox n) (hmeas n) 2
  have hint : ∀ n, Integrable (K n) areaμ := fun n ↦
    (hmem n).integrable (by norm_num)
  have hscalar : ∀ n, κ n ∈ Icc (2 / C) 2 ∧ Λ n ∈ Icc 2 (2 * C) := by
    intro n
    have hk2 : κ n ≤ 2 := by
      have hi := integral_mono_ae (integrable_const (κ n)) (hint n)
        ((hbox n).mono fun _ hx ↦ hx.1)
      simpa only [integral_const, probReal_univ, one_smul, hmass n] using hi
    have h2L : 2 ≤ Λ n := by
      have hi := integral_mono_ae (hint n) (integrable_const (Λ n))
        ((hbox n).mono fun _ hx ↦ hx.2)
      simpa only [integral_const, probReal_univ, one_smul, hmass n] using hi
    have hLk : Λ n ≤ C * κ n := (div_le_iff₀ (hκ n)).mp (hratio n)
    have hklo : 2 / C ≤ κ n := by
      apply (div_le_iff₀ hCpos).mpr
      simpa only [mul_comm] using h2L.trans hLk
    have hLhi : Λ n ≤ 2 * C := by
      calc
        Λ n ≤ C * κ n := hLk
        _ ≤ C * 2 := mul_le_mul_of_nonneg_left hk2 hCpos.le
        _ = 2 * C := mul_comm _ _
    exact ⟨⟨hklo, hk2⟩, ⟨h2L, hLhi⟩⟩
  have hcompact : IsCompact (Icc (2 / C) (2 : ℝ) ×ˢ Icc (2 : ℝ) (2 * C)) :=
    isCompact_Icc.prod isCompact_Icc
  obtain ⟨z, hz, ψ, hψ, hzconv⟩ := hcompact.tendsto_subseq
    (x := fun n ↦ (κ n, Λ n)) (fun n ↦ hscalar n)
  have hkconv : Tendsto (fun n ↦ κ (ψ n)) atTop (nhds z.1) := by
    simpa only [Function.comp_def] using (continuous_fst.tendsto z).comp hzconv
  have hLconv : Tendsto (fun n ↦ Λ (ψ n)) atTop (nhds z.2) := by
    simpa only [Function.comp_def] using (continuous_snd.tendsto z).comp hzconv
  let u : ℕ → Lp ℝ 2 areaμ := fun n ↦ (hmem n).toLp (K n)
  have hu : ∀ n, ⇑(u n) =ᵐ[areaμ] K n := fun n ↦ (hmem n).coeFn_toLp
  have hnorm : ∀ n, ‖u n‖ ≤ 2 * C := by
    intro n
    have hbound : ∀ᵐ x ∂areaμ, ‖u n x‖ ≤ 2 * C := by
      filter_upwards [hu n, hbox n] with x hux hx
      rw [hux, Real.norm_eq_abs, abs_of_nonneg ((hκ n).le.trans hx.1)]
      exact hx.2.trans (hscalar n).2.2
    have hn := Lp.norm_le_of_ae_bound (f := u n)
      (show 0 ≤ 2 * C by positivity) hbound
    simpa [measureUnivNNReal] using hn
  obtain ⟨f, _hfNorm, χ, hχ, hweak⟩ :=
    Analysis.HilbertWeakSubsequence.exists_subseq_tendsto_inner_of_norm_le
      (fun n ↦ u (ψ n)) (2 * C) (fun n ↦ hnorm (ψ n))
  let φ : ℕ → ℕ := ψ ∘ χ
  have hφ : StrictMono φ := hψ.comp hχ
  have hkfinal : Tendsto (fun n ↦ κ (φ n)) atTop (nhds z.1) := by
    simpa only [φ, Function.comp_def] using hkconv.comp hχ.tendsto_atTop
  have hLfinal : Tendsto (fun n ↦ Λ (φ n)) atTop (nhds z.2) := by
    simpa only [φ, Function.comp_def] using hLconv.comp hχ.tendsto_atTop
  have hweakfinal : ∀ v : Lp ℝ 2 areaμ,
      Tendsto (fun n ↦ inner ℝ (u (φ n)) v) atTop (nhds (inner ℝ f v)) := by
    intro v
    simpa only [φ, Function.comp_def] using hweak v
  have hboxLp : ∀ n, ∀ᵐ x ∂areaμ, κ (φ n) ≤ u (φ n) x ∧ u (φ n) x ≤ Λ (φ n) := by
    intro n
    filter_upwards [hu (φ n), hbox (φ n)] with x hux hx
    simpa only [hux] using hx
  have hlimitBox : ∀ᵐ x ∂areaμ, z.1 ≤ f x ∧ f x ≤ z.2 :=
    Analysis.L2WeakOrder.ae_bounds_of_tendsto_inner
      (fun n ↦ u (φ n)) f (fun n ↦ κ (φ n)) (fun n ↦ Λ (φ n))
      z.1 z.2 hkfinal hLfinal hboxLp hweakfinal
  have hkpos : 0 < z.1 :=
    (div_pos (by norm_num) hCpos).trans_le hz.1.1
  have hratioLimit : z.2 / z.1 ≤ C :=
    le_of_tendsto' (hLfinal.div hkfinal (ne_of_gt hkpos)) (fun n ↦ hratio (φ n))
  have hpair : ∀ n (v : Lp ℝ 2 areaμ),
      inner ℝ (u (φ n)) v = ∫ x, K (φ n) x * v x ∂areaμ := by
    intro n v
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hu (φ n)] with x hx
    simp only [Real.inner_apply, hx]
  have hweakRaw : ∀ v : Lp ℝ 2 areaμ,
      Tendsto (fun n ↦ ∫ x, K (φ n) x * v x ∂areaμ) atTop
        (nhds (∫ x, f x * v x ∂areaμ)) := by
    intro v
    simpa only [hpair, L2.inner_def, Real.inner_apply] using hweakfinal v
  let c : Lp ℝ 2 areaμ :=
    (memLp_const (μ := areaμ) (p := 2) (1 : ℝ)).toLp (fun _ : ℝ ↦ 1)
  have hc : ⇑c =ᵐ[areaμ] fun _ : ℝ ↦ (1 : ℝ) :=
    (memLp_const (μ := areaμ) (p := 2) (1 : ℝ)).coeFn_toLp
  have htestOne : ∀ g : ℝ → ℝ,
      (∫ x, g x * c x ∂areaμ) = ∫ x, g x ∂areaμ := by
    intro g
    apply integral_congr_ae
    filter_upwards [hc] with x hx
    simp only [hx, mul_one]
  have hmassLimit : (∫ x, f x ∂areaμ) = 2 := by
    have ht : Tendsto (fun _ : ℕ ↦ (2 : ℝ)) atTop (nhds (∫ x, f x ∂areaμ)) := by
      simpa only [htestOne, hmass] using hweakRaw c
    exact tendsto_nhds_unique ht tendsto_const_nhds
  have hid : MemLp (fun x : ℝ ↦ x) 2 areaμ := by
    apply MemLp.of_bound continuous_id.aestronglyMeasurable 1
    filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Ioo] with x hx
    change |x| ≤ 1
    rw [abs_of_pos hx.1]
    exact hx.2.le
  let d : Lp ℝ 2 areaμ := hid.toLp (fun x : ℝ ↦ x)
  have hd : ⇑d =ᵐ[areaμ] fun x : ℝ ↦ x := hid.coeFn_toLp
  have htestId : ∀ g : ℝ → ℝ,
      (∫ x, g x * d x ∂areaμ) = ∫ x, x * g x ∂areaμ := by
    intro g
    apply integral_congr_ae
    filter_upwards [hd] with x hx
    rw [hx, mul_comm]
  have hmomentLimit : (∫ x, x * f x ∂areaμ) = 1 := by
    have ht : Tendsto (fun _ : ℕ ↦ (1 : ℝ)) atTop
        (nhds (∫ x, x * f x ∂areaμ)) := by
      simpa only [htestId, hmoment] using hweakRaw d
    exact tendsto_nhds_unique ht tendsto_const_nhds
  exact ⟨⇑f, z.1, z.2, φ, Lp.memLp f, hφ, hkfinal, hLfinal, hweakRaw,
    hmassLimit, hmomentLimit, hz.1, hz.2, hkpos, hratioLimit, hlimitBox⟩

end RicciFlowSharpEstimate.Geometry.AreaProfile
