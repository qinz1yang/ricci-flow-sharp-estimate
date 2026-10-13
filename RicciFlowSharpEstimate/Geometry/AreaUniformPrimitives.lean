/-
Copyright (c) 2026 Ziyang Qin. All rights reserved.
No license is granted by this file.
Authors: Ziyang Qin
-/
import RicciFlowSharpEstimate.Geometry.AreaWeakPrimitives
import RicciFlowSharpEstimate.Geometry.AreaWarpBounds
import RicciFlowSharpEstimate.Analysis.WeakDerivativeLimits
import Mathlib.Topology.MetricSpace.Equicontinuity
import Mathlib.Topology.UniformSpace.Ascoli
import Mathlib.Topology.UniformSpace.UniformApproximation

/-!
# Uniform limits of the original normalized area primitives

A common positive curvature box gives a common Lipschitz bound for the
warping slopes. The zeroth moment gives a common Lipschitz bound for the
warps. Their weak L2 pointwise limits therefore converge uniformly on the
closed normalized interval. The original limit primitives are continuous
there and retain the quadratic bounds, slope bound and pole values.
-/

noncomputable section

namespace RicciFlowSharpEstimate.Geometry.AreaProfile

open Filter MeasureTheory Set

local notation "μ₀" => (volume.restrict (Ioo (0 : ℝ) 1))

private theorem memLp_area_of_continuous_curvature_box
    (K : ℝ → ℝ) (hK : Continuous K) (lo hi : ℝ) (hlo : 0 < lo)
    (hbox : ∀ x ∈ Icc (0 : ℝ) 1, lo ≤ K x ∧ K x ≤ hi) : MemLp K 2 μ₀ := by
  apply MemLp.of_bound hK.aestronglyMeasurable hi
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
  have hcurv := hbox x ⟨hx.1.le, hx.2.le⟩
  rw [Real.norm_eq_abs, abs_of_nonneg (hlo.le.trans hcurv.1)]
  exact hcurv.2

private theorem area_tendstoUniformlyOn_of_common_dist_bound
    (F : ℕ → ℝ → ℝ) (f : ℝ → ℝ) (C : ℝ)
    (hdist : ∀ n, ∀ x ∈ Icc (0 : ℝ) 1, ∀ y ∈ Icc (0 : ℝ) 1,
      dist (F n x) (F n y) ≤ C * dist x y)
    (hpoint : ∀ x ∈ Icc (0 : ℝ) 1,
      Tendsto (fun n ↦ F n x) atTop (nhds (f x))) :
    TendstoUniformlyOn F f atTop (Icc (0 : ℝ) 1) := by
  have hmod : Tendsto (fun t : ℝ ↦ C * t) (nhds 0) (nhds 0) := by
    simpa only [mul_zero, id_eq] using
      ((tendsto_id : Tendsto (fun t : ℝ ↦ t) (nhds 0) (nhds 0)).const_mul C)
  have heq : Equicontinuous (fun n (x : Icc (0 : ℝ) 1) ↦ F n x) :=
    Metric.equicontinuous_of_continuity_modulus (fun t ↦ C * t) hmod
      (fun n (x : Icc (0 : ℝ) 1) ↦ F n x)
      (fun x y n ↦ hdist n x x.property y y.property)
  have hpi : Tendsto (fun n (x : Icc (0 : ℝ) 1) ↦ F n x) atTop
      (nhds (fun x : Icc (0 : ℝ) 1 ↦ f x)) :=
    tendsto_pi_nhds.mpr (fun x ↦ hpoint x x.property)
  have hu := (heq.tendsto_uniformFun_iff_pi atTop
    (fun x : Icc (0 : ℝ) 1 ↦ f x)).mpr hpi
  apply tendstoUniformlyOn_iff_tendstoUniformly_comp_coe.mpr
  simpa only [Function.comp_def, UniformFun.toFun_ofFun] using
    (UniformFun.tendsto_iff_tendstoUniformly.mp hu)

section WeakLimit

variable (Kn : ℕ → ℝ → ℝ) (K0 : ℝ → ℝ)
    (hcont : ∀ n, Continuous (Kn n))
    (lo hi : ℝ) (hlo : 0 < lo)
    (hbox : ∀ n, ∀ x ∈ Icc (0 : ℝ) 1, lo ≤ Kn n x ∧ Kn n x ≤ hi)
    (hK0 : MemLp K0 2 μ₀)
    (hweak : ∀ v : Lp ℝ 2 μ₀,
      Tendsto (fun n ↦ ∫ s, Kn n s * v s ∂μ₀) atTop
        (nhds (∫ s, K0 s * v s ∂μ₀)))

include hcont hlo hbox hK0 hweak

/-- A common positive curvature box upgrades weak L2 convergence to uniform
convergence of the original warping slopes on the closed normalized interval. -/
theorem tendstoUniformlyOn_warpSlope_of_weak_L2 :
    TendstoUniformlyOn (fun n ↦ warpSlope (Kn n)) (warpSlope K0) atTop
      (Icc (0 : ℝ) 1) := by
  have hMem : ∀ n, MemLp (Kn n) 2 μ₀ := fun n ↦
    memLp_area_of_continuous_curvature_box (Kn n) (hcont n) lo hi hlo (hbox n)
  apply area_tendstoUniformlyOn_of_common_dist_bound _ _ (2 * hi)
  · intro n x hx y hy
    simpa only [dist_eq_norm] using
      Convex.norm_image_sub_le_of_norm_deriv_le
        (fun t _ ↦ (warpSlope_hasDerivAt (Kn n) (hcont n) t).differentiableAt)
        (fun t ht ↦ by
          calc
            ‖deriv (warpSlope (Kn n)) t‖ = 2 * Kn n t := by
              rw [deriv_warpSlope (Kn n) (hcont n), Real.norm_eq_abs, abs_mul,
                abs_of_nonneg (hlo.le.trans (hbox n t ht).1)]
              norm_num
            _ ≤ 2 * hi := mul_le_mul_of_nonneg_left (hbox n t ht).2 zero_le_two)
        (convex_Icc 0 1) hy hx
  · exact tendsto_warpSlope_of_weak_L2 Kn K0 hMem hK0 hweak

/-- The zeroth moments and a common positive curvature box upgrade weak L2
convergence to uniform convergence of the original warps. -/
theorem tendstoUniformlyOn_warp_of_weak_L2
    (hzero : ∀ n, (∫ x in (0 : ℝ)..1, Kn n x) = 2) :
    TendstoUniformlyOn (fun n ↦ warp (Kn n)) (warp K0) atTop
      (Icc (0 : ℝ) 1) := by
  have hMem : ∀ n, MemLp (Kn n) 2 μ₀ := fun n ↦
    memLp_area_of_continuous_curvature_box (Kn n) (hcont n) lo hi hlo (hbox n)
  apply area_tendstoUniformlyOn_of_common_dist_bound _ _ 2
  · intro n x hx y hy
    simpa only [dist_eq_norm] using
      Convex.norm_image_sub_le_of_norm_deriv_le
        (fun t _ ↦ (warp_hasDerivAt (Kn n) (hcont n) t).differentiableAt)
        (fun t ht ↦ by
          rw [deriv_warp (Kn n) (hcont n)]
          simpa only [Real.norm_eq_abs] using
            abs_warpSlope_le_two (Kn n) (hcont n)
              (fun z hz ↦ hlo.le.trans (hbox n z hz).1) (hzero n) t ht)
        (convex_Icc 0 1) hy hx
  · exact tendsto_warp_of_weak_L2 Kn K0 hMem hK0 hweak

/-- The original limiting slope is continuous on the closed interval even
when the limiting curvature is supplied only as a raw L2 function. -/
theorem continuousOn_warpSlope_of_weak_L2 :
    ContinuousOn (warpSlope K0) (Icc (0 : ℝ) 1) := by
  apply (tendstoUniformlyOn_warpSlope_of_weak_L2
    Kn K0 hcont lo hi hlo hbox hK0 hweak).continuousOn
  exact (Filter.Eventually.of_forall fun n ↦
    (warpSlope_continuous (Kn n) (hcont n)).continuousOn).frequently

/-- The original limiting warp is continuous on the closed interval without
any continuity assumption on the limiting curvature. -/
theorem continuousOn_warp_of_weak_L2
    (hzero : ∀ n, (∫ x in (0 : ℝ)..1, Kn n x) = 2) :
    ContinuousOn (warp K0) (Icc (0 : ℝ) 1) := by
  apply (tendstoUniformlyOn_warp_of_weak_L2
    Kn K0 hcont lo hi hlo hbox hK0 hweak hzero).continuousOn
  exact (Filter.Eventually.of_forall fun n ↦
    (warp_continuous (Kn n) (hcont n)).continuousOn).frequently

/-- The quadratic comparisons for the actual warps pass to the weak L2
curvature limit, using the exact zeroth and first moments of the sequence. -/
theorem warp_bounds_of_weak_L2
    (hzero : ∀ n, (∫ x in (0 : ℝ)..1, Kn n x) = 2)
    (hone : ∀ n, (∫ x in (0 : ℝ)..1, x * Kn n x) = 1)
    (x : ℝ) (hx : x ∈ Icc (0 : ℝ) 1) :
    lo * x * (1 - x) ≤ warp K0 x ∧ warp K0 x ≤ hi * x * (1 - x) := by
  have hMem : ∀ n, MemLp (Kn n) 2 μ₀ := fun n ↦
    memLp_area_of_continuous_curvature_box (Kn n) (hcont n) lo hi hlo (hbox n)
  have hpoint := tendsto_warp_of_weak_L2 Kn K0 hMem hK0 hweak x hx
  constructor
  · exact ge_of_tendsto' hpoint (fun n ↦
      (warp_bounds_of_curvature_bounds (Kn n) (hcont n) lo hi (hbox n)
        (hzero n) (hone n) x hx).1)
  · exact le_of_tendsto' hpoint (fun n ↦
      (warp_bounds_of_curvature_bounds (Kn n) (hcont n) lo hi (hbox n)
        (hzero n) (hone n) x hx).2)

/-- The normalized absolute slope bound is retained by the actual weak-limit
primitive throughout the closed interval. -/
theorem abs_warpSlope_le_two_of_weak_L2
    (hzero : ∀ n, (∫ x in (0 : ℝ)..1, Kn n x) = 2)
    (x : ℝ) (hx : x ∈ Icc (0 : ℝ) 1) : |warpSlope K0 x| ≤ 2 := by
  have hMem : ∀ n, MemLp (Kn n) 2 μ₀ := fun n ↦
    memLp_area_of_continuous_curvature_box (Kn n) (hcont n) lo hi hlo (hbox n)
  have hpoint := tendsto_warpSlope_of_weak_L2 Kn K0 hMem hK0 hweak x hx
  exact le_of_tendsto' hpoint.abs (fun n ↦
    abs_warpSlope_le_two (Kn n) (hcont n)
      (fun z hz ↦ hlo.le.trans (hbox n z hz).1) (hzero n) x hx)

/-- Both pole values of the original warp and its stored slope are retained
by the weak L2 curvature limit. -/
theorem warp_endpoints_of_weak_L2
    (hzero : ∀ n, (∫ x in (0 : ℝ)..1, Kn n x) = 2)
    (hone : ∀ n, (∫ x in (0 : ℝ)..1, x * Kn n x) = 1) :
    warp K0 0 = 0 ∧ warp K0 1 = 0 ∧ warpSlope K0 0 = 2 ∧ warpSlope K0 1 = -2 := by
  have hMem : ∀ n, MemLp (Kn n) 2 μ₀ := fun n ↦
    memLp_area_of_continuous_curvature_box (Kn n) (hcont n) lo hi hlo (hbox n)
  refine ⟨warp_zero K0, ?_, warpSlope_zero K0, ?_⟩
  · apply tendsto_nhds_unique
      (tendsto_warp_of_weak_L2 Kn K0 hMem hK0 hweak 1 (by norm_num))
    have hconst : (fun n ↦ warp (Kn n) 1) = (fun _ : ℕ ↦ (0 : ℝ)) := by
      funext n
      exact warp_one (Kn n) (hcont n) (hzero n) (hone n)
    rw [hconst]
    exact tendsto_const_nhds
  · apply tendsto_nhds_unique
      (tendsto_warpSlope_of_weak_L2 Kn K0 hMem hK0 hweak 1 (by norm_num))
    have hconst : (fun n ↦ warpSlope (Kn n) 1) = (fun _ : ℕ ↦ (-2 : ℝ)) := by
      funext n
      exact warpSlope_one (Kn n) (hzero n)
    rw [hconst]
    exact tendsto_const_nhds


/-- The original limiting warp has the original limiting slope as its genuine
weak derivative, without assuming smooth limiting curvature. -/
theorem hasWeakDerivOn_warp_of_weak_L2
    (hzero : ∀ n, (∫ x in (0 : ℝ)..1, Kn n x) = 2) :
    Analysis.HasWeakDerivOn (Ioo 0 1) (warp K0) (warpSlope K0) := by
  have hseq (n : ℕ) : Analysis.HasWeakDerivOn (Ioo 0 1) (warp (Kn n)) (warpSlope (Kn n)) := by
    have hc : ContDiff ℝ 1 (warp (Kn n)) := by
      apply contDiff_one_iff_deriv.mpr
      refine ⟨fun x => (warp_hasDerivAt (Kn n) (hcont n) x).differentiableAt, ?_⟩
      rw [deriv_warp (Kn n) (hcont n)]
      exact warpSlope_continuous (Kn n) (hcont n)
    have h := Analysis.hasWeakDerivOn_of_contDiff (U := Ioo 0 1) isOpen_Ioo hc
    rwa [deriv_warp (Kn n) (hcont n)] at h
  have hfLim := tendstoUniformlyOn_warp_of_weak_L2
    Kn K0 hcont lo hi hlo hbox hK0 hweak hzero
  have hbLim := tendstoUniformlyOn_warpSlope_of_weak_L2
    Kn K0 hcont lo hi hlo hbox hK0 hweak
  exact Analysis.hasWeakDerivOn_of_locallyUniformlyOn isOpen_Ioo hseq
    (fun n => (warp_continuous (Kn n) (hcont n)).continuousOn)
    (fun n => (warpSlope_continuous (Kn n) (hcont n)).continuousOn)
    ((continuousOn_warp_of_weak_L2 Kn K0 hcont lo hi hlo hbox hK0 hweak hzero).mono
      Ioo_subset_Icc_self)
    ((continuousOn_warpSlope_of_weak_L2 Kn K0 hcont lo hi hlo hbox hK0 hweak).mono
      Ioo_subset_Icc_self)
    (hfLim.tendstoLocallyUniformlyOn.mono Ioo_subset_Icc_self)
    (hbLim.tendstoLocallyUniformlyOn.mono Ioo_subset_Icc_self)

/-- The original limiting slope has weak derivative minus twice the actual
limiting curvature. Weak L² curvature pairings, rather than strong curvature
convergence, identify this derivative. -/
theorem hasWeakDerivOn_warpSlope_of_weak_L2 :
    Analysis.HasWeakDerivOn (Ioo 0 1) (warpSlope K0) (fun x => -2 * K0 x) := by
  have hseq (n : ℕ) :
      Analysis.HasWeakDerivOn (Ioo 0 1) (warpSlope (Kn n)) (fun x => -2 * Kn n x) := by
    have hc : ContDiff ℝ 1 (warpSlope (Kn n)) := by
      apply contDiff_one_iff_deriv.mpr
      refine ⟨fun x => (warpSlope_hasDerivAt (Kn n) (hcont n) x).differentiableAt, ?_⟩
      rw [deriv_warpSlope (Kn n) (hcont n)]
      exact continuous_const.mul (hcont n)
    have h := Analysis.hasWeakDerivOn_of_contDiff (U := Ioo 0 1) isOpen_Ioo hc
    rwa [deriv_warpSlope (Kn n) (hcont n)] at h
  have hb0 := (continuousOn_warpSlope_of_weak_L2 Kn K0 hcont lo hi hlo hbox hK0 hweak).mono
    Ioo_subset_Icc_self
  have hKI : IntegrableOn (fun x => -2 * K0 x) (Ioo (0 : ℝ) 1) volume :=
    (hK0.integrable (by norm_num)).const_mul (-2)
  apply Analysis.HasWeakDerivOn.of_tendsto_test_pairings hseq
    (hb0.locallyIntegrableOn measurableSet_Ioo) hKI.locallyIntegrableOn
  · intro φ hφ hφc hφI
    have hbLim := tendstoUniformlyOn_warpSlope_of_weak_L2
      Kn K0 hcont lo hi hlo hbox hK0 hweak
    exact Analysis.test_mul_integral_tendsto_of_locallyUniformlyOn isOpen_Ioo
      (fun n => (warpSlope_continuous (Kn n) (hcont n)).continuousOn) hb0
      (hbLim.tendstoLocallyUniformlyOn.mono Ioo_subset_Icc_self)
      (hφ.continuous_deriv (by simp)) hφc.deriv (tsupport_deriv_subset.trans hφI)
  · intro φ hφ hφc hφI
    have hφmem : MemLp φ 2 μ₀ :=
      (hφ.continuous.memLp_top_of_hasCompactSupport hφc μ₀).mono_exponent le_top
    let v : Lp ℝ 2 μ₀ := hφmem.toLp φ
    have hv : ⇑v =ᵐ[μ₀] φ := hφmem.coeFn_toLp
    have hid (G : ℝ → ℝ) :
        (∫ x, φ x * (-2 * G x)) = -2 * (∫ x, G x * v x ∂μ₀) := by
      calc
        _ = ∫ x in Ioo (0 : ℝ) 1, φ x * (-2 * G x) := by
          symm
          apply setIntegral_eq_integral_of_forall_compl_eq_zero
          intro x hx
          have hz : φ x = 0 := image_eq_zero_of_notMem_tsupport (fun hxφ => hx (hφI hxφ))
          rw [hz, zero_mul]
        _ = ∫ x, -2 * (G x * v x) ∂μ₀ := by
          apply integral_congr_ae
          filter_upwards [hv] with x hx
          rw [hx]
          ring
        _ = _ := integral_const_mul _ _
    simpa only [hid] using (hweak v).const_mul (-2)

end WeakLimit

end RicciFlowSharpEstimate.Geometry.AreaProfile
