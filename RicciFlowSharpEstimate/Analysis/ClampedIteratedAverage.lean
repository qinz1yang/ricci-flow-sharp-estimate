/-
Copyright (c) 2026 Ziyang Qin. All rights reserved.
No license is granted by this file.
Authors: Ziyang Qin
-/
import Mathlib.MeasureTheory.Integral.IntervalAverage
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Algebra.Order.Group.MinMax
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Clamped feedback through an iterated interval average

Interval averaging preserves a uniform bound on the distance from a constant.
The variable-endpoint average of a bounded integrable function is integrable,
so the same bound applies to its iterated average. A clamped feedback with
gain less than one therefore selects its explicit fixed point at the endpoint.
-/

noncomputable section

namespace RicciFlowSharpEstimate.Analysis

open Filter MeasureTheory Set Topology

/-- Averaging on a nonempty finite interval preserves an almost-everywhere
bound on the distance from a constant. Endpoint values do not affect the bound. -/
theorem abs_interval_average_sub_le_of_ae_bound
    {f : ℝ → ℝ} {a b c B : ℝ} (hab : a < b)
    (hf : IntegrableOn f (Ioo a b) volume)
    (hbound : ∀ᵐ t ∂volume.restrict (Ioo a b), |f t - c| ≤ B) :
    |(⨍ t in a..b, f t) - c| ≤ B := by
  have hfi : IntervalIntegrable f volume a b :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le hab.le).mpr hf
  have heq : (⨍ t in a..b, f t) - c = (∫ t in a..b, f t - c) / (b - a) := by
    rw [interval_average_eq_div,
      intervalIntegral.integral_sub hfi (continuous_const.intervalIntegrable a b),
      intervalIntegral.integral_const]
    simp only [smul_eq_mul]
    field_simp [(sub_pos.mpr hab).ne']
  have hnorm : ‖∫ t in a..b, f t - c‖ ≤ B * |b - a| := by
    apply intervalIntegral.norm_integral_le_of_norm_le_const_ae
    filter_upwards [ae_imp_of_ae_restrict hbound, volume.ae_ne b] with t ht htb htI
    have htI' : t ∈ Ioc a b := by simpa only [uIoc_of_le hab.le] using htI
    simpa only [Real.norm_eq_abs] using ht ⟨htI'.1, lt_of_le_of_ne htI'.2 htb⟩
  rw [heq, abs_div, abs_of_pos (sub_pos.mpr hab)]
  apply (div_le_iff₀ (sub_pos.mpr hab)).mpr
  simpa only [Real.norm_eq_abs, abs_of_pos (sub_pos.mpr hab)] using hnorm

/-- The variable-endpoint interval average of a bounded integrable real
function is integrable on the same positive interval. -/
theorem integrableOn_interval_average_of_ae_bound
    {f : ℝ → ℝ} {b B : ℝ}
    (hf : IntegrableOn f (Ioo 0 b) volume)
    (hbound : ∀ᵐ t ∂volume.restrict (Ioo 0 b), |f t| ≤ B) :
    IntegrableOn (fun x => ⨍ t in 0..x, f t) (Ioo 0 b) volume := by
  by_cases hb : 0 < b
  · have hfi : IntervalIntegrable f volume 0 b :=
      (intervalIntegrable_iff_integrableOn_Ioo_of_le hb.le).mpr hf
    have hPC : ContinuousOn (fun x => ∫ t in 0..x, f t) (Icc (0 : ℝ) b) := by
      simpa only [uIcc_of_le hb.le] using
        (intervalIntegral.continuousOn_primitive_interval' (a := 0) hfi left_mem_uIcc)
    have hPM : AEStronglyMeasurable (fun x => ∫ t in 0..x, f t)
        (volume.restrict (Ioo 0 b)) :=
      (hPC.integrableOn_Icc.mono_set Ioo_subset_Icc_self).aestronglyMeasurable
    have hAM : AEStronglyMeasurable (fun x => ⨍ t in 0..x, f t)
        (volume.restrict (Ioo 0 b)) := by
      apply (hPM.div₀ measurable_id.aestronglyMeasurable).congr
      exact Eventually.of_forall fun x => by
        change (∫ t in 0..x, f t) / x = (⨍ t in 0..x, f t)
        rw [interval_average_eq_div, sub_zero]
    apply (integrable_const B).mono' hAM
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
    have hsub : Ioo (0 : ℝ) x ⊆ Ioo (0 : ℝ) b := by
      intro t ht
      exact ⟨ht.1, ht.2.trans hx.2⟩
    have hbound' : ∀ᵐ t ∂volume.restrict (Ioo 0 x), |f t - 0| ≤ B := by
      simpa only [sub_zero] using ae_restrict_of_ae_restrict_of_subset hsub hbound
    simpa only [sub_zero, Real.norm_eq_abs] using
      abs_interval_average_sub_le_of_ae_bound hx.1 (hf.mono_set hsub) hbound'
  · simp only [Ioo_eq_empty_of_le (le_of_not_gt hb), integrableOn_empty]

/-- Iterating the interval average preserves an almost-everywhere bound on
the distance from a constant. Integrability of the inner average is derived. -/
theorem abs_iterated_interval_average_sub_le_of_ae_bound
    {f : ℝ → ℝ} {b c B : ℝ} (hb : 0 < b)
    (hf : IntegrableOn f (Ioo 0 b) volume)
    (hbound : ∀ᵐ t ∂volume.restrict (Ioo 0 b), |f t - c| ≤ B) :
    |(⨍ s in 0..b, ⨍ t in 0..s, f t) - c| ≤ B := by
  have habs : ∀ᵐ t ∂volume.restrict (Ioo 0 b), |f t| ≤ B + |c| := by
    filter_upwards [hbound] with t ht
    calc
      |f t| = |(f t - c) + c| := by rw [sub_add_cancel]
      _ ≤ |f t - c| + |c| := abs_add_le _ _
      _ ≤ B + |c| := add_le_add ht le_rfl
  have hinner : IntegrableOn (fun s => ⨍ t in 0..s, f t) (Ioo 0 b) volume :=
    integrableOn_interval_average_of_ae_bound hf habs
  apply abs_interval_average_sub_le_of_ae_bound hb hinner
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
  have hsub : Ioo (0 : ℝ) s ⊆ Ioo (0 : ℝ) b := by
    intro t ht
    exact ⟨ht.1, ht.2.trans hs.2⟩
  exact abs_interval_average_sub_le_of_ae_bound hs.1 (hf.mono_set hsub)
    (ae_restrict_of_ae_restrict_of_subset hsub hbound)

private theorem iterated_clamp_distance (lo hi u v : ℝ) :
    |max lo (min hi u) - max lo (min hi v)| ≤ |u - v| := by
  have hmax := abs_max_sub_max_le_max lo (min hi u) lo (min hi v)
  have hmin := abs_min_sub_min_le_max hi u hi v
  simp only [sub_self, abs_zero,
    max_eq_right (abs_nonneg (min hi u - min hi v))] at hmax
  simp only [sub_self, abs_zero, max_eq_right (abs_nonneg (u - v))] at hmin
  exact hmax.trans hmin

private theorem iterated_clamp_fixed (lo hi A ρ : ℝ)
    (hlohi : lo ≤ hi) (hρ : 0 ≤ ρ) :
    let k := max lo (min hi (A / (1 + ρ)))
    max lo (min hi (A - ρ * k)) = k := by
  let t := A / (1 + ρ)
  have hden : 0 < 1 + ρ := by linarith
  have hA : A = (1 + ρ) * t := by
    dsimp only [t]
    field_simp [hden.ne']
  by_cases htl : t ≤ lo
  · have hk : max lo (min hi t) = lo := max_eq_left ((min_le_right _ _).trans htl)
    change max lo (min hi (A - ρ * max lo (min hi t))) = max lo (min hi t)
    rw [hk]
    apply max_eq_left
    apply (min_le_right _ _).trans
    rw [hA]
    nlinarith [mul_le_mul_of_nonneg_left htl hden.le]
  by_cases hht : hi ≤ t
  · have hk : max lo (min hi t) = hi := by rw [min_eq_left hht, max_eq_right hlohi]
    change max lo (min hi (A - ρ * max lo (min hi t))) = max lo (min hi t)
    rw [hk]
    have hh : hi ≤ A - ρ * hi := by
      rw [hA]
      nlinarith [mul_le_mul_of_nonneg_left hht hden.le]
    rw [min_eq_left hh, max_eq_right hlohi]
  have hk : max lo (min hi t) = t := by
    rw [min_eq_right (le_of_not_ge hht), max_eq_right (le_of_not_ge htl)]
  change max lo (min hi (A - ρ * max lo (min hi t))) = max lo (min hi t)
  rw [hk]
  have heq : A - ρ * t = t := by rw [hA]; ring
  rw [heq]
  exact hk

/-- A bounded function with clamped feedback through its actual iterated
interval average converges to the explicit clipped fixed point when the
feedback gain is less than one and the additive error tends to zero. -/
theorem tendsto_of_clamped_iterated_average
    {K e : ℝ → ℝ} {b lo hi A ρ : ℝ}
    (hb : 0 < b) (hlohi : lo ≤ hi) (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1)
    (hK : IntegrableOn K (Ioo 0 b) volume)
    (hbox : ∀ x ∈ Ioo (0 : ℝ) b, lo ≤ K x ∧ K x ≤ hi)
    (he : Tendsto e (𝓝[>] (0 : ℝ)) (𝓝 0))
    (hclip : ∀ᶠ x in 𝓝[>] (0 : ℝ),
      K x = max lo (min hi (A - ρ * (⨍ s in 0..x, ⨍ t in 0..s, K t) + e x))) :
    Tendsto K (𝓝[>] (0 : ℝ)) (𝓝 (max lo (min hi (A / (1 + ρ))))) := by
  let k := max lo (min hi (A / (1 + ρ)))
  have hkfixed : max lo (min hi (A - ρ * k)) = k :=
    iterated_clamp_fixed lo hi A ρ hlohi hρ0
  change Tendsto K (𝓝[>] (0 : ℝ)) (𝓝 k)
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  let η := (1 - ρ) * ε / 2
  have hη : 0 < η := div_pos (mul_pos (sub_pos.mpr hρ1) hε) (by norm_num)
  have heabs : Tendsto (fun x => |e x|) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    simpa only [abs_zero] using he.abs
  have hnear : ∀ᶠ x in 𝓝[>] (0 : ℝ), |e x| ≤ η ∧
      K x = max lo (min hi (A - ρ * (⨍ s in 0..x, ⨍ t in 0..s, K t) + e x)) := by
    filter_upwards [heabs.eventually (gt_mem_nhds hη), hclip] with x hx hc
    exact ⟨hx.le, hc⟩
  have hnear' : ∀ᶠ x in 𝓝 (0 : ℝ), 0 < x → |e x| ≤ η ∧
      K x = max lo (min hi (A - ρ * (⨍ s in 0..x, ⨍ t in 0..s, K t) + e x)) := by
    simpa only [eventually_nhdsWithin_iff, mem_Ioi] using hnear
  have hI : ∀ᶠ x in 𝓝 (0 : ℝ), x < b := Iio_mem_nhds hb
  obtain ⟨δ, hδ, hlocal⟩ := Metric.eventually_nhds_iff.mp (hI.and hnear')
  have hlocal' (x : ℝ) (hx0 : 0 < x) (hxδ : x < δ) :
      x < b ∧ |e x| ≤ η ∧
        K x = max lo (min hi (A - ρ * (⨍ s in 0..x, ⨍ t in 0..s, K t) + e x)) := by
    have hloc := hlocal (y := x) (by
      simpa only [Real.dist_eq, sub_zero, abs_of_pos hx0] using hxδ)
    exact ⟨hloc.1, hloc.2 hx0⟩
  let S : Set ℝ := {y | ∃ x, 0 < x ∧ x < δ ∧ y = |K x - k|}
  have hSbdd : BddAbove S := by
    refine ⟨|lo| + |hi| + |k|, ?_⟩
    rintro y ⟨x, hx0, hxδ, rfl⟩
    have hbx := hbox x ⟨hx0, (hlocal' x hx0 hxδ).1⟩
    have hbK : |K x| ≤ |lo| + |hi| := by
      apply abs_le.mpr
      constructor <;> linarith [neg_abs_le lo, le_abs_self hi, abs_nonneg lo, abs_nonneg hi]
    exact (abs_sub _ _).trans (add_le_add hbK le_rfl)
  have hSnonempty : S.Nonempty := by
    refine ⟨|K (δ / 2) - k|, δ / 2, ?_, ?_, rfl⟩ <;> linarith
  let M := sSup S
  have hM (x : ℝ) (hx0 : 0 < x) (hxδ : x < δ) : |K x - k| ≤ M :=
    le_csSup hSbdd ⟨x, hx0, hxδ, rfl⟩
  have himproved (x : ℝ) (hx0 : 0 < x) (hxδ : x < δ) :
      |K x - k| ≤ ρ * M + η := by
    have hloc := hlocal' x hx0 hxδ
    have hsub : Ioo (0 : ℝ) x ⊆ Ioo (0 : ℝ) b := by
      intro t ht
      exact ⟨ht.1, ht.2.trans hloc.1⟩
    have hbound : ∀ᵐ t ∂volume.restrict (Ioo 0 x), |K t - k| ≤ M := by
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
      exact hM t ht.1 (ht.2.trans hxδ)
    have havg := abs_iterated_interval_average_sub_le_of_ae_bound hx0
      (hK.mono_set hsub) hbound
    have hClip := iterated_clamp_distance lo hi
      (A - ρ * (⨍ s in 0..x, ⨍ t in 0..s, K t) + e x) (A - ρ * k)
    rw [← hloc.2.2, hkfixed] at hClip
    have hid : (A - ρ * (⨍ s in 0..x, ⨍ t in 0..s, K t) + e x) - (A - ρ * k) =
        -ρ * ((⨍ s in 0..x, ⨍ t in 0..s, K t) - k) + e x := by ring
    rw [hid] at hClip
    calc
      |K x - k| ≤ |-ρ * ((⨍ s in 0..x, ⨍ t in 0..s, K t) - k) + e x| := hClip
      _ ≤ |-ρ * ((⨍ s in 0..x, ⨍ t in 0..s, K t) - k)| + |e x| := abs_add_le _ _
      _ = ρ * |(⨍ s in 0..x, ⨍ t in 0..s, K t) - k| + |e x| := by
        rw [abs_mul, abs_neg, abs_of_nonneg hρ0]
      _ ≤ ρ * M + η := add_le_add (mul_le_mul_of_nonneg_left havg hρ0) hloc.2.1
  have hMsup : M ≤ ρ * M + η := by
    apply csSup_le hSnonempty
    rintro y ⟨x, hx0, hxδ, rfl⟩
    exact himproved x hx0 hxδ
  have hMhalf : M ≤ ε / 2 := by
    apply le_of_not_gt
    intro hbad
    have hpositive := mul_pos (sub_pos.mpr hρ1) (sub_pos.mpr hbad)
    dsimp only [η] at hMsup
    nlinarith only [hMsup, hpositive]
  have hMsmall : M < ε := hMhalf.trans_lt (by linarith)
  have hnearδ : ∀ᶠ x in 𝓝 (0 : ℝ), x < δ := Iio_mem_nhds hδ
  have hsmall : ∀ᶠ x in 𝓝[>] (0 : ℝ), x < δ :=
    hnearδ.filter_mono nhdsWithin_le_nhds
  filter_upwards [self_mem_nhdsWithin, hsmall] with x hx0 hxδ
  change 0 < x at hx0
  simpa only [Real.dist_eq] using (hM x hx0 hxδ).trans_lt hMsmall

end RicciFlowSharpEstimate.Analysis
