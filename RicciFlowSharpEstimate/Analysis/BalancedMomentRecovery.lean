/-
Copyright (c) 2026 Ziyang Qin. All rights reserved.
No license is granted by this file.
Authors: Ziyang Qin
-/
import RicciFlowSharpEstimate.Analysis.InteriorMomentRecovery
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Smooth recovery with balanced moments in the original box

Contracting toward the mean creates room for interior moment correction.
When the mean lies on a box boundary, the original function is constant
almost everywhere. No symmetry or monotonicity is required.
-/

noncomputable section
namespace RicciFlowSharpEstimate.Analysis
open Set MeasureTheory Filter
open scoped ENNReal Topology ContDiff
local notation "areaμ" => volume.restrict (Ioo (0 : ℝ) 1)

private theorem first_moment_integrable {f : ℝ → ℝ} (hf : MemLp f 2 areaμ) :
    Integrable (fun x => x * f x) areaμ := by
  apply (hf.integrable (by norm_num : (1 : ENNReal) ≤ 2)).bdd_mul
    (continuous_id.aestronglyMeasurable : AEStronglyMeasurable (fun x : ℝ => x) areaμ)
    (c := 1)
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
  simpa only [id_eq, Real.norm_eq_abs, abs_of_pos hx.1] using hx.2.le

private theorem mean_mem_box {f : ℝ → ℝ} {lo hi c : ℝ}
    (hf : MemLp f 2 areaμ) (hb : ∀ᵐ x ∂areaμ, f x ∈ Icc lo hi)
    (hm : (∫ x in (0 : ℝ)..1, f x) = c) : c ∈ Icc lo hi := by
  have hfi := hf.integrable (by norm_num : (1 : ENNReal) ≤ 2)
  have hm' : (∫ x, f x ∂areaμ) = c := by
    simpa only [intervalIntegral.integral_of_le zero_le_one, integral_Ioc_eq_integral_Ioo]
      using hm
  have hlo := integral_mono_ae (integrable_const lo) hfi (hb.mono fun _ hx => hx.1)
  have hhi := integral_mono_ae hfi (integrable_const hi) (hb.mono fun _ hx => hx.2)
  simpa [hm'] using And.intro hlo hhi

private theorem constant_recovery {f : ℝ → ℝ} {lo hi c ε : ℝ}
    (hc : c ∈ Icc lo hi) (hfc : f =ᵐ[areaμ] fun _ => c) :
    ∃ g : ℝ → ℝ, ContDiff ℝ ∞ g ∧ (∀ x, g x ∈ Icc lo hi) ∧
      (∫ x in (0 : ℝ)..1, g x) = c ∧ (∫ x in (0 : ℝ)..1, x * g x) = c / 2 ∧
      eLpNorm (f - g) 2 areaμ ≤ ENNReal.ofReal ε := by
  refine ⟨fun _ => c, contDiff_const, fun _ => hc, by simp, ?_, ?_⟩
  · rw [intervalIntegral.integral_mul_const]
    norm_num [integral_id]
    ring
  · have heq : f - (fun _ => c) =ᵐ[areaμ] 0 := by
      filter_upwards [hfc] with x hx
      simp only [Pi.sub_apply, Pi.zero_apply, hx, sub_self]
    rw [eLpNorm_congr_ae heq, eLpNorm_zero]
    exact zero_le

/-- Every L2 function in a fixed closed box with mean `c` and first moment
`c / 2` admits smooth approximations in that same box with both moments exact.
This includes the degenerate box and either boundary value of the mean. -/
theorem exists_contDiff_Icc_exact_balanced_moments
    (f : ℝ → ℝ) (lo hi c ε : ℝ) (hf : MemLp f 2 areaμ)
    (hbox : ∀ᵐ x ∂areaμ, f x ∈ Icc lo hi)
    (hm0 : (∫ x in (0 : ℝ)..1, f x) = c)
    (hm1 : (∫ x in (0 : ℝ)..1, x * f x) = c / 2) (hε : 0 < ε) :
    ∃ g : ℝ → ℝ, ContDiff ℝ ∞ g ∧ (∀ x, g x ∈ Icc lo hi) ∧
      (∫ x in (0 : ℝ)..1, g x) = c ∧ (∫ x in (0 : ℝ)..1, x * g x) = c / 2 ∧
      eLpNorm (f - g) 2 areaμ ≤ ENNReal.ofReal ε := by
  have hc := mean_mem_box hf hbox hm0
  have hfi := hf.integrable (by norm_num : (1 : ENNReal) ≤ 2)
  have hm0' : (∫ x, f x ∂areaμ) = c := by
    simpa only [intervalIntegral.integral_of_le zero_le_one, integral_Ioc_eq_integral_Ioo]
      using hm0
  by_cases hlo : c = lo
  · apply constant_recovery hc
    have hle : (fun _ : ℝ => c) ≤ᵐ[areaμ] f := by
      filter_upwards [hbox] with x hx
      simpa only [hlo] using hx.1
    exact ((integral_eq_iff_of_ae_le (integrable_const c) hfi hle).mp
      (by simpa only [hm0'] using (show (∫ _x : ℝ, c ∂areaμ) = c by simp))).symm
  by_cases hhi : c = hi
  · apply constant_recovery hc
    have hle : f ≤ᵐ[areaμ] (fun _ : ℝ => c) := by
      filter_upwards [hbox] with x hx
      simpa only [hhi] using hx.2
    exact (integral_eq_iff_of_ae_le hfi (integrable_const c) hle).mp (by simp [hm0'])
  have hlc : lo < c := lt_of_le_of_ne hc.1 (Ne.symm hlo)
  have hch : c < hi := lt_of_le_of_ne hc.2 hhi
  let D := hi - lo
  have hD : 0 ≤ D := sub_nonneg.mpr (hc.1.trans hc.2)
  let t := min 1 (ε / (2 * (D + 1)))
  have ht : 0 < t := lt_min zero_lt_one (div_pos hε (by positivity))
  have ht1 : t ≤ 1 := min_le_left _ _
  have hterr : t * D ≤ ε / 2 := by
    have hh := (le_div_iff₀ (by positivity : 0 < 2 * (D + 1))).mp
      (min_le_right 1 (ε / (2 * (D + 1))))
    change t * (2 * (D + 1)) ≤ ε at hh
    nlinarith
  let ft : ℝ → ℝ := fun x => (1 - t) * f x + t * c
  have hft : MemLp ft 2 areaμ := (hf.const_mul (1 - t)).add (memLp_const (t * c))
  let δ := t * min (c - lo) (hi - c)
  have hδ : 0 < δ := mul_pos ht (lt_min (sub_pos.mpr hlc) (sub_pos.mpr hch))
  have hδl : δ ≤ t * (c - lo) := mul_le_mul_of_nonneg_left (min_le_left _ _) ht.le
  have hδu : δ ≤ t * (hi - c) := mul_le_mul_of_nonneg_left (min_le_right _ _) ht.le
  have hftbox : ∀ᵐ x ∂areaμ, ft x ∈ Icc (lo + δ) (hi - δ) := by
    filter_upwards [hbox] with x hx
    dsimp only [ft]
    have h1 := mul_nonneg (sub_nonneg.mpr ht1) (sub_nonneg.mpr hx.1)
    have h2 := mul_nonneg (sub_nonneg.mpr ht1) (sub_nonneg.mpr hx.2)
    constructor <;> nlinarith
  have hfI : IntervalIntegrable f volume (0 : ℝ) 1 :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le zero_le_one).mpr hfi
  have hxfI : IntervalIntegrable (fun x => x * f x) volume (0 : ℝ) 1 :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le zero_le_one).mpr (first_moment_integrable hf)
  have hmft0 : (∫ x in (0 : ℝ)..1, ft x) = c := by
    rw [show ft = (fun x => (1 - t) * f x + t * c) from rfl,
      intervalIntegral.integral_add (hfI.const_mul _) intervalIntegrable_const,
      intervalIntegral.integral_const_mul, hm0]
    simp only [intervalIntegral.integral_const, sub_zero, one_smul]
    ring
  have hmft1 : (∫ x in (0 : ℝ)..1, x * ft x) = c / 2 := by
    have heq : (fun x => x * ft x) =
        (fun x => (1 - t) * (x * f x) + (t * c) * x) := by
      funext x
      dsimp only [ft]
      ring
    have hxi : IntervalIntegrable (fun x : ℝ => (t * c) * x) volume 0 1 :=
      (continuous_const.mul continuous_id).intervalIntegrable 0 1
    rw [heq, intervalIntegral.integral_add (hxfI.const_mul (1 - t)) hxi,
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul, hm1]
    norm_num [integral_id]
    ring
  have hnorm : eLpNorm (f - ft) 2 areaμ ≤ ENNReal.ofReal (ε / 2) := by
    have hb : ∀ᵐ x ∂areaμ, ‖(f - ft) x‖ ≤ ε / 2 := by
      filter_upwards [hbox] with x hx
      have hd : |f x - c| ≤ D := abs_le.mpr ⟨by dsimp only [D]; linarith [hx.1, hx.2, hc.1, hc.2],
        by dsimp only [D]; linarith [hx.1, hx.2, hc.1, hc.2]⟩
      have heq : (f - ft) x = t * (f x - c) := by dsimp only [Pi.sub_apply, ft]; ring
      rw [heq, norm_mul, Real.norm_eq_abs, abs_of_pos ht, Real.norm_eq_abs]
      exact (mul_le_mul_of_nonneg_left hd ht.le).trans hterr
    simpa using eLpNorm_le_of_ae_bound (p := (2 : ENNReal))
      (hf.aestronglyMeasurable.sub hft.aestronglyMeasurable) hb
  obtain ⟨g, hg, hgb, hg0, hg1, herr⟩ :=
    exists_contDiff_exact_moments_of_memLp_of_interior_box ft lo hi δ (ε / 2)
      hft hδ hftbox (half_pos hε)
  refine ⟨g, hg, hgb, hg0.trans hmft0, hg1.trans hmft1, ?_⟩
  calc
    eLpNorm (f - g) 2 areaμ = eLpNorm ((f - ft) + (ft - g)) 2 areaμ := by
      congr 1
      funext x
      simp
    _ ≤ eLpNorm (f - ft) 2 areaμ + eLpNorm (ft - g) 2 areaμ :=
      eLpNorm_add_le (by norm_num)
    _ ≤ ENNReal.ofReal (ε / 2) + ENNReal.ofReal (ε / 2) := add_le_add hnorm herr
    _ = ENNReal.ofReal ε := by rw [← ENNReal.ofReal_add (by positivity) (by positivity), add_halves]

/-- A single smooth recovery sequence preserves the original box and both
balanced moments and converges strongly in L2. -/
theorem exists_contDiff_Icc_exact_balanced_moments_sequence
    (f : ℝ → ℝ) (lo hi c : ℝ) (hf : MemLp f 2 areaμ)
    (hbox : ∀ᵐ x ∂areaμ, f x ∈ Icc lo hi)
    (hm0 : (∫ x in (0 : ℝ)..1, f x) = c)
    (hm1 : (∫ x in (0 : ℝ)..1, x * f x) = c / 2) :
    ∃ g : ℕ → ℝ → ℝ,
      (∀ n, ContDiff ℝ ∞ (g n) ∧ (∀ x, g n x ∈ Icc lo hi) ∧
        (∫ x in (0 : ℝ)..1, g n x) = c ∧ (∫ x in (0 : ℝ)..1, x * g n x) = c / 2) ∧
      Tendsto (fun n => eLpNorm (g n - f) 2 areaμ) atTop (𝓝 0) := by
  classical
  have ha (n : ℕ) := exists_contDiff_Icc_exact_balanced_moments f lo hi c
    (1 / ((n : ℝ) + 1)) hf hbox hm0 hm1 (by positivity)
  choose g hg hb h0 h1 he using ha
  refine ⟨g, fun n => ⟨hg n, hb n, h0 n, h1 n⟩, ?_⟩
  have hlim : Tendsto (fun n : ℕ => ENNReal.ofReal (1 / ((n : ℝ) + 1)))
      atTop (𝓝 0) := by
    simpa only [ENNReal.ofReal_zero, Function.comp_def] using
      (ENNReal.continuous_ofReal.tendsto 0).comp
        (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim (fun _ => bot_le)
  intro n
  simpa only [eLpNorm_sub_comm] using he n

end RicciFlowSharpEstimate.Analysis
