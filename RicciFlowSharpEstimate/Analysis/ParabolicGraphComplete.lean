/-
Copyright (c) 2026 Ziyang Qin. All rights reserved.
No license is granted by this file.
Authors: Ziyang Qin
-/
import RicciFlowSharpEstimate.Analysis.ParabolicSobolev
import RicciFlowSharpEstimate.Analysis.WeightedWeakDerivativeLimit
import RicciFlowSharpEstimate.Analysis.WeakDerivativePrimitives
import RicciFlowSharpEstimate.Analysis.L2StrongMultipliers

/-!
# Completeness of the parabolic weak derivative graph

Completing the three weighted L² coordinates preserves both genuine weak
derivatives. Continuous interior representatives are chosen only after those
identities have been established, and every original strong limit is retained.
No mass normalization or endpoint condition enters this closed-graph statement.
-/

noncomputable section
namespace RicciFlowSharpEstimate.Analysis
open Set MeasureTheory Filter Topology
open scoped ContDiff
local notation "areaμ" => volume.restrict (Ioo (0 : ℝ) 1)

private theorem weighted_test_pairing_tendsto
    {a F0 : ℝ → ℝ} {F : ℕ → ℝ → ℝ}
    (ha : Continuous a) (ha0 : ∀ x ∈ Ioo (0 : ℝ) 1, a x ≠ 0)
    (hF : ∀ n, MemLp (fun x => a x * F n x) 2 areaμ)
    (hF0 : MemLp F0 2 areaμ)
    (hlim : Tendsto (fun n => eLpNorm ((fun x => a x * F n x) - F0) 2 areaμ)
      atTop (𝓝 0))
    (φ : ℝ → ℝ) (hφ : Continuous φ) (hφc : HasCompactSupport φ)
    (hφI : tsupport φ ⊆ Ioo (0 : ℝ) 1) :
    Tendsto (fun n => ∫ x, φ x * F n x) atTop
      (𝓝 (∫ x, φ x * (F0 x / a x))) := by
  have ht := memLp_two_Ioo_div_test ha ha0 hφ hφc hφI
  have hz : Tendsto (fun _ : ℕ => eLpNorm
      ((fun x => φ x / a x) - (fun x => φ x / a x)) 2 areaμ) atTop (𝓝 0) := by
    simp only [sub_self, eLpNorm_zero]
    exact tendsto_const_nhds
  have hp := (tendsto_integral_mul_of_tendsto_eLpNorm_two
    hF hF0 (fun _ => ht) ht hlim hz).2.2
  have hφzero (x : ℝ) (hx : x ∉ Ioo (0 : ℝ) 1) : φ x = 0 :=
    image_eq_zero_of_notMem_tsupport fun hxt => hx (hφI hxt)
  have hsource (n : ℕ) :
      (∫ x, (a x * F n x) * (φ x / a x) ∂areaμ) = ∫ x, φ x * F n x := by
    calc
      _ = ∫ x in Ioo (0 : ℝ) 1, φ x * F n x := by
        apply integral_congr_ae
        filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
        field_simp [ha0 x hx]
      _ = _ := setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => by
        simp only [hφzero x hx, zero_mul]
  have htarget : (∫ x, F0 x * (φ x / a x) ∂areaμ) =
      ∫ x, φ x * (F0 x / a x) := by
    calc
      _ = ∫ x in Ioo (0 : ℝ) 1, φ x * (F0 x / a x) := by
        apply integral_congr_ae
        filter_upwards [] with x
        ring
      _ = _ := setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => by
        simp only [hφzero x hx, zero_mul]
  simpa only [hsource, htarget] using hp

private theorem weak_derivative_of_weighted_strong_limits
    {a b R0 P0 : ℝ → ℝ} {R P : ℕ → ℝ → ℝ}
    (ha : Continuous a) (hb : Continuous b)
    (ha0 : ∀ x ∈ Ioo (0 : ℝ) 1, a x ≠ 0)
    (hb0 : ∀ x ∈ Ioo (0 : ℝ) 1, b x ≠ 0)
    (hseq : ∀ n, HasWeakDerivOn (Ioo (0 : ℝ) 1) (R n) (P n))
    (hR : ∀ n, MemLp (fun x => a x * R n x) 2 areaμ)
    (hP : ∀ n, MemLp (fun x => b x * P n x) 2 areaμ)
    (hR0 : MemLp R0 2 areaμ) (hP0 : MemLp P0 2 areaμ)
    (hRL : Tendsto (fun n => eLpNorm ((fun x => a x * R n x) - R0) 2 areaμ)
      atTop (𝓝 0))
    (hPL : Tendsto (fun n => eLpNorm ((fun x => b x * P n x) - P0) 2 areaμ)
      atTop (𝓝 0)) :
    HasWeakDerivOn (Ioo (0 : ℝ) 1) (fun x => R0 x / a x) (fun x => P0 x / b x) := by
  apply HasWeakDerivOn.of_tendsto_test_pairings hseq
    (locallyIntegrableOn_Ioo_div_weight ha ha0 hR0)
    (locallyIntegrableOn_Ioo_div_weight hb hb0 hP0)
  · intro φ hφ hφc hφI
    exact weighted_test_pairing_tendsto ha ha0 hR hR0 hRL (deriv φ)
      (hφ.continuous_deriv (by simp)) hφc.deriv (tsupport_deriv_subset.trans hφI)
  · intro φ hφ hφc hφI
    exact weighted_test_pairing_tendsto hb hb0 hP hP0 hPL φ hφ.continuous hφc hφI

private theorem raw_limit_of_toLp_tendsto
    {F : ℕ → ℝ → ℝ} (hF : ∀ n, MemLp (F n) 2 areaμ)
    (v : Lp ℝ 2 areaμ)
    (hlim : Tendsto (fun n => (hF n).toLp (F n)) atTop (𝓝 v)) :
    Tendsto (fun n => eLpNorm (F n - (v : ℝ → ℝ)) 2 areaμ) atTop (𝓝 0) := by
  have hl := (Lp.tendsto_Lp_iff_tendsto_eLpNorm'
    (fun n => (hF n).toLp (F n)) v).mp hlim
  apply hl.congr'
  apply Eventually.of_forall
  intro n
  apply eLpNorm_congr_ae
  filter_upwards [(hF n).coeFn_toLp] with x hx
  simp only [Pi.sub_apply, hx]

/-- A Cauchy sequence in the three canonical L² coordinates of the parabolic
weak graph has a genuine graph limit with continuous interior representatives.
Both weak derivatives and all three full-sequence strong limits are returned.
Raw zero functions are included; no mass-one predicate is imposed. -/
theorem exists_parabolic_graph_limit_of_cauchy
    (r p z : ℕ → ℝ → ℝ) (h : ∀ n, HasParabolicWeakDerivatives (r n) (p n) (z n))
    (hc : CauchySeq (fun n =>
      ((h n).memLp.toLp (r n),
        ((h n).memLp_weighted_deriv.toLp (fun x => Real.sqrt (x * (1 - x)) * p n x),
          (h n).memLp_weighted_secondDeriv.toLp
            (fun x => x * (1 - x) * Real.sqrt (x * (1 - x)) * z n x))))) :
    ∃ r0 p0 z0 : ℝ → ℝ,
      HasParabolicWeakDerivatives r0 p0 z0 ∧
      ContinuousOn r0 (Ioo (0 : ℝ) 1) ∧ ContinuousOn p0 (Ioo (0 : ℝ) 1) ∧
      Tendsto (fun n => eLpNorm (r n - r0) 2 areaμ) atTop (𝓝 0) ∧
      Tendsto (fun n => eLpNorm
        ((fun x => Real.sqrt (x * (1 - x)) * p n x) -
          (fun x => Real.sqrt (x * (1 - x)) * p0 x)) 2 areaμ) atTop (𝓝 0) ∧
      Tendsto (fun n => eLpNorm
        ((fun x => x * (1 - x) * Real.sqrt (x * (1 - x)) * z n x) -
          (fun x => x * (1 - x) * Real.sqrt (x * (1 - x)) * z0 x)) 2 areaμ)
        atTop (𝓝 0) := by
  obtain ⟨v, hv⟩ := cauchySeq_tendsto_of_complete hc
  let a : ℝ → ℝ := fun x => Real.sqrt (x * (1 - x))
  let b : ℝ → ℝ := fun x => x * (1 - x) * Real.sqrt (x * (1 - x))
  have ha : Continuous a := by dsimp [a]; fun_prop
  have hb : Continuous b := by dsimp [b]; fun_prop
  have ha0 (x : ℝ) (hx : x ∈ Ioo (0 : ℝ) 1) : a x ≠ 0 :=
    (Real.sqrt_pos.mpr (mul_pos hx.1 (sub_pos.mpr hx.2))).ne'
  have hb0 (x : ℝ) (hx : x ∈ Ioo (0 : ℝ) 1) : b x ≠ 0 := by
    exact mul_ne_zero (mul_ne_zero hx.1.ne' (sub_pos.mpr hx.2).ne') (ha0 x hx)
  have hvr := (continuous_fst.tendsto v).comp hv
  have hvp := (continuous_fst.tendsto v.2).comp ((continuous_snd.tendsto v).comp hv)
  have hvz := (continuous_snd.tendsto v.2).comp ((continuous_snd.tendsto v).comp hv)
  have hrL := raw_limit_of_toLp_tendsto (fun n => (h n).memLp) v.1 hvr
  have hpL := raw_limit_of_toLp_tendsto (fun n => (h n).memLp_weighted_deriv)
    v.2.1 hvp
  have hzL := raw_limit_of_toLp_tendsto (fun n => (h n).memLp_weighted_secondDeriv)
    v.2.2 hvz
  let P : ℝ → ℝ := fun x => v.2.1 x / a x
  let Z : ℝ → ℝ := fun x => v.2.2 x / b x
  have hfirst : HasWeakDerivOn (Ioo (0 : ℝ) 1) (v.1 : ℝ → ℝ) P := by
    have hRmem : ∀ n, MemLp (fun x => (1 : ℝ) * r n x) 2 areaμ := by
      simpa only [one_mul] using fun n => (h n).memLp
    have hRlim : Tendsto
        (fun n => eLpNorm ((fun x => (1 : ℝ) * r n x) - (v.1 : ℝ → ℝ)) 2 areaμ)
        atTop (𝓝 0) := by simpa only [one_mul] using hrL
    simpa only [div_one] using weak_derivative_of_weighted_strong_limits
      continuous_const ha (fun _ _ => one_ne_zero) ha0
      (fun n => (h n).weakDeriv) hRmem (fun n => (h n).memLp_weighted_deriv)
      (Lp.memLp v.1) (Lp.memLp v.2.1) hRlim hpL
  have hsecond : HasWeakDerivOn (Ioo (0 : ℝ) 1) P Z :=
    weak_derivative_of_weighted_strong_limits ha hb ha0 hb0
      (fun n => (h n).weakDeriv_deriv) (fun n => (h n).memLp_weighted_deriv)
      (fun n => (h n).memLp_weighted_secondDeriv)
      (Lp.memLp v.2.1) (Lp.memLp v.2.2) hpL hzL
  obtain ⟨p0, hp0, hPp, hPZ⟩ := hsecond.exists_continuous_representative_Ioo
    (by norm_num : (1 / 2 : ℝ) ∈ Ioo (0 : ℝ) 1)
  have hfirst' := hfirst.congr_ae EventuallyEq.rfl hPp
  obtain ⟨r0, hr0, hRr, hrp⟩ := hfirst'.exists_continuous_representative_Ioo
    (by norm_num : (1 / 2 : ℝ) ∈ Ioo (0 : ℝ) 1)
  have hpeq : (fun x => a x * p0 x) =ᵐ[areaμ] (v.2.1 : ℝ → ℝ) := by
    filter_upwards [hPp, ae_restrict_mem measurableSet_Ioo] with x hx hxI
    rw [← hx]
    dsimp only [P]
    field_simp [ha0 x hxI]
  have hzeq : (fun x => b x * Z x) =ᵐ[areaμ] (v.2.2 : ℝ → ℝ) :=
    ae_weight_mul_div_Ioo hb0
  have hgraph : HasParabolicWeakDerivatives r0 p0 Z := by
    refine ⟨hrp, hPZ, (memLp_congr_ae hRr).mp (Lp.memLp v.1), ?_, ?_⟩
    · exact (memLp_congr_ae hpeq).mpr (Lp.memLp v.2.1)
    · exact (memLp_congr_ae hzeq).mpr (Lp.memLp v.2.2)
  refine ⟨r0, p0, Z, hgraph, hr0, hp0, ?_, ?_, ?_⟩
  · apply hrL.congr' (Eventually.of_forall ?_)
    intro n
    apply eLpNorm_congr_ae
    filter_upwards [hRr] with x hx
    simp only [Pi.sub_apply, hx]
  · apply hpL.congr' (Eventually.of_forall ?_)
    intro n
    apply eLpNorm_congr_ae
    filter_upwards [hpeq] with x hx
    change a x * p n x - v.2.1 x = a x * p n x - a x * p0 x
    rw [hx]
  · apply hzL.congr' (Eventually.of_forall ?_)
    intro n
    apply eLpNorm_congr_ae
    filter_upwards [hzeq] with x hx
    change b x * z n x - v.2.2 x = b x * z n x - b x * Z x
    rw [hx]

end RicciFlowSharpEstimate.Analysis
