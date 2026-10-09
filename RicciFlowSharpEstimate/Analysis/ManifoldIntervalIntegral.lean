/-
Copyright (c) 2026 Ziyang Qin. All rights reserved.
No license is granted by this file.
Authors: Ziyang Qin
-/
import DifferentialGeometry.Analysis.Integration.Measure.Parametric.FiniteIntegral
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace

/-!
# Smooth parameter integration on manifolds

Finite-interval integration preserves smoothness on a boundaryless manifold and
commutes with the actual vector-valued manifold derivative. Compact-parameter
bounds and integrability are supplied by the finite-measure integration engine.

The fixed-chart transfer and the smooth partial-derivative argument adapt Ziyang
Qin's pinned `DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.Parametric.CoefficientIntegral`.
The finite-measure engine is imported directly without its spectral consumers.
-/

noncomputable section

open MeasureTheory Set Filter Manifold
open scoped ContDiff Topology Interval

namespace RicciFlowSharpEstimate.Analysis

private theorem finite_interval_measure (a b : ℝ) :
    IsFiniteMeasure (volume.comap (Subtype.val : uIcc a b → ℝ)) := ⟨by
  rw [(MeasurableEmbedding.subtype_coe measurableSet_uIcc).comap_apply]
  simp⟩

private theorem intervalIntegral_eq_subtype {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] (f : ℝ → F) (a b : ℝ) :
    (∫ t in a..b, f t) = (if a ≤ b then (1 : ℝ) else -1) •
      ∫ t : uIcc a b, f t ∂volume.comap Subtype.val := by
  rw [integral_subtype_comap measurableSet_uIcc f, uIcc, integral_Icc_eq_integral_Ioc]
  exact intervalIntegral.intervalIntegral_eq_integral_uIoc _ _ _ _

private theorem contDiffOn_intervalIntegral {V F : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (n : ℕ∞) (a b : ℝ)
    {U : Set V} {S : Set ℝ} (hU : IsOpen U) (hS : IsOpen S) (hI : uIcc a b ⊆ S)
    {G : V × ℝ → F} (hG : ContDiffOn ℝ n G (U ×ˢ S)) :
    ContDiffOn ℝ n (fun x => ∫ t in a..b, G (x, t)) U := by
  have := finite_interval_measure a b
  have h := DifferentialGeometry.Integral.Measure.contDiffOn_integral_subtype_of_isCompact
    n (K := uIcc a b) isCompact_uIcc (volume.comap Subtype.val)
    hU (hU.prod hS) (fun p hp => ⟨hp.1, hI hp.2⟩) hG
  exact (h.const_smul (if a ≤ b then (1 : ℝ) else -1)).congr
    (fun x _ => intervalIntegral_eq_subtype (fun t => G (x, t)) a b)

private theorem fderiv_fst_contDiffOn {V F : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {G : V × ℝ → F} {U : Set V} {S : Set ℝ} (hU : IsOpen U) (hS : IsOpen S)
    (hG : ContDiffOn ℝ ∞ G (U ×ˢ S)) :
    ContDiffOn ℝ ∞ (fun p : V × ℝ => fderiv ℝ (fun z => G (z, p.2)) p.1) (U ×ˢ S) := by
  rw [(hU.prod hS).contDiffOn_iff] at hG ⊢
  intro p hp
  apply ContDiffAt.fderiv (n := ∞) (m := ∞)
  · exact (hG hp).comp _
      (by fun_prop : ContDiffAt ℝ ∞ (fun w : (V × ℝ) × V => (w.2, w.1.2)) (p, p.1))
  · fun_prop
  · exact le_rfl

private theorem hasFDerivAt_intervalIntegral {V F : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (a b : ℝ)
    {U : Set V} {S : Set ℝ} (hU : IsOpen U) (hS : IsOpen S) (hI : uIcc a b ⊆ S)
    {G : V × ℝ → F} (hG : ContDiffOn ℝ ∞ G (U ×ˢ S)) (x : V) (hx : x ∈ U) :
    HasFDerivAt (fun y => ∫ t in a..b, G (y, t))
      (∫ t in a..b, fderiv ℝ (fun y => G (y, t)) x) x := by
  have := finite_interval_measure a b
  let : CompactSpace (uIcc a b) := isCompact_iff_compactSpace.mp isCompact_uIcc
  have hG' := fderiv_fst_contDiffOn hU hS hG
  have hmap : ContinuousOn (fun p : V × uIcc a b => (p.1, (p.2 : ℝ))) (U ×ˢ univ) :=
    by fun_prop
  have hc : ContinuousOn (fun p : V × uIcc a b => G (p.1, p.2)) (U ×ˢ univ) :=
    hG.continuousOn.comp (by fun_prop) (fun p hp => ⟨hp.1, hI p.2.property⟩)
  have hc' : ContinuousOn
      (fun p : V × uIcc a b => fderiv ℝ (fun z => G (z, p.2)) p.1) (U ×ˢ univ) :=
    hG'.continuousOn.comp hmap (fun p hp => ⟨hp.1, hI p.2.property⟩)
  have hd := DifferentialGeometry.Integral.Measure.hasFDerivAt_integral_compactOn
    (volume.comap Subtype.val : Measure (uIcc a b)) hU
    (fun y (t : uIcc a b) => G (y, t))
    (fun y (t : uIcc a b) => fderiv ℝ (fun z => G (z, t)) y)
    hc hc'
    (fun y hy t => ((hG.contDiffAt ((hU.prod hS).mem_nhds ⟨hy, hI t.property⟩)).comp₂
      contDiffAt_id contDiffAt_const).differentiableAt (by simp) |>.hasFDerivAt) x hx
  convert hd.const_smul (if a ≤ b then (1 : ℝ) else -1) using 1
  · funext y
    exact intervalIntegral_eq_subtype (fun t => G (y, t)) a b
  · exact intervalIntegral_eq_subtype (fun t => fderiv ℝ (fun y => G (y, t)) x) a b

section Manifold

variable {E H M F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
    [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [NormedAddCommGroup F] [NormedSpace ℝ F]

omit [I.Boundaryless] in
private theorem contDiffOn_in_chart (n : ℕ∞) {f : ℝ × M → F}
    {U : Set M} {S : Set ℝ}
    (hf : ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, F) n f (S ×ˢ U)) (x : M) :
    ContDiffOn ℝ n (fun p : E × ℝ => f (p.2, (extChartAt I x).symm p.1))
      (((extChartAt I x).target ∩ (extChartAt I x).symm ⁻¹' U) ×ˢ S) := by
  have hsymm : ContMDiffOn 𝓘(ℝ, E) I n (extChartAt I x).symm
      ((extChartAt I x).target ∩ (extChartAt I x).symm ⁻¹' U) :=
    (contMDiffOn_extChartAt_symm x).mono inter_subset_left
  have hfst : ContMDiffOn 𝓘(ℝ, E × ℝ) 𝓘(ℝ, E) n (Prod.fst : E × ℝ → E)
      (((extChartAt I x).target ∩ (extChartAt I x).symm ⁻¹' U) ×ˢ S) :=
    contDiff_fst.contMDiff.contMDiffOn
  have hsnd : ContMDiffOn 𝓘(ℝ, E × ℝ) 𝓘(ℝ, ℝ) n (Prod.snd : E × ℝ → ℝ)
      (((extChartAt I x).target ∩ (extChartAt I x).symm ⁻¹' U) ×ˢ S) :=
    contDiff_snd.contMDiff.contMDiffOn
  exact (hf.comp (hsnd.prodMk (hsymm.comp hfst (fun p hp => hp.1)))
    (fun p hp => ⟨hp.2, hp.1.2⟩)).contDiffOn

/-- Integration over a fixed finite interval preserves regularity on an open
manifold domain. The parameter interval may have either orientation. -/
theorem contMDiffOn_intervalIntegral (n : ℕ∞) (a b : ℝ) {f : ℝ × M → F}
    {U : Set M} {S : Set ℝ} (hU : IsOpen U) (hS : IsOpen S) (hI : uIcc a b ⊆ S)
    (hf : ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, F) n f (S ×ˢ U)) :
    ContMDiffOn I 𝓘(ℝ, F) n (fun x => ∫ t in a..b, f (t, x)) U := by
  intro x hx
  apply ContMDiffAt.contMDiffWithinAt
  rw [contMDiffAt_iff_source, I.range_eq_univ, contMDiffWithinAt_univ,
    contMDiffAt_iff_contDiffAt]
  have hopen : IsOpen ((extChartAt I x).target ∩ (extChartAt I x).symm ⁻¹' U) :=
    (continuousOn_extChartAt_symm x).isOpen_inter_preimage
      (isOpen_extChartAt_target x) hU
  have hmem : extChartAt I x x ∈
      (extChartAt I x).target ∩ (extChartAt I x).symm ⁻¹' U := by
    refine ⟨mem_extChartAt_target x, ?_⟩
    simpa only [mem_preimage, extChartAt_to_inv] using hx
  exact (contDiffOn_intervalIntegral n a b hopen hS hI (contDiffOn_in_chart n hf x)).contDiffAt
    (hopen.mem_nhds hmem)

/-- The finite-interval integral of a jointly smooth parameter family is smooth. -/
theorem contMDiff_intervalIntegral (n : ℕ∞) (a b : ℝ) {f : ℝ × M → F}
    (hf : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, F) n f) :
    ContMDiff I 𝓘(ℝ, F) n (fun x => ∫ t in a..b, f (t, x)) := by
  rw [← contMDiffOn_univ]
  exact contMDiffOn_intervalIntegral n a b isOpen_univ isOpen_univ (subset_univ _)
    hf.contMDiffOn

omit [IsManifold I ∞ M] in
private theorem mvfderiv_eq_chart {g : M → F} {x : M}
    (hg : MDifferentiableAt I 𝓘(ℝ, F) g x) :
    mvfderiv I g x = fderiv ℝ (fun y => g ((extChartAt I x).symm y)) (extChartAt I x x) := by
  rw [hg.mvfderiv, I.range_eq_univ, fderivWithin_univ]
  rfl

/-- The vector-valued manifold derivative commutes with finite-interval integration
of a jointly smooth family on an open neighborhood of the parameter interval. -/
theorem mvfderiv_intervalIntegral_apply_of_contMDiffOn (a b : ℝ) {f : ℝ × M → F}
    {U : Set M} {S : Set ℝ} (hU : IsOpen U) (hS : IsOpen S) (hI : uIcc a b ⊆ S)
    (hf : ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, F) ∞ f (S ×ˢ U))
    (x : M) (hx : x ∈ U) (v : TangentSpace I x) :
    mvfderiv I (fun y => ∫ t in a..b, f (t, y)) x v =
      ∫ t in a..b, mvfderiv I (fun y => f (t, y)) x v := by
  have hopen : IsOpen ((extChartAt I x).target ∩ (extChartAt I x).symm ⁻¹' U) :=
    (continuousOn_extChartAt_symm x).isOpen_inter_preimage
      (isOpen_extChartAt_target x) hU
  have hmem : extChartAt I x x ∈
      (extChartAt I x).target ∩ (extChartAt I x).symm ⁻¹' U := by
    refine ⟨mem_extChartAt_target x, ?_⟩
    simpa only [mem_preimage, extChartAt_to_inv] using hx
  have hint := (contMDiffOn_intervalIntegral (⊤ : ℕ∞) a b hU hS hI hf).contMDiffAt
    (hU.mem_nhds hx)
  rw [mvfderiv_eq_chart (hint.mdifferentiableAt (by simp))]
  rw [(hasFDerivAt_intervalIntegral a b hopen hS hI
    (contDiffOn_in_chart (⊤ : ℕ∞) hf x) _ hmem).fderiv]
  change (∫ t in a..b, fderiv ℝ (fun y => f (t, (extChartAt I x).symm y))
    (extChartAt I x x)) (show E from v) = _
  have hG' := fderiv_fst_contDiffOn hopen hS (contDiffOn_in_chart (⊤ : ℕ∞) hf x)
  have hcont : ContinuousOn
      (fun t => fderiv ℝ (fun z => f (t, (extChartAt I x).symm z)) (extChartAt I x x))
      (uIcc a b) :=
    hG'.continuousOn.comp (continuousOn_const.prodMk continuousOn_id)
      (fun t ht => ⟨hmem, hI ht⟩)
  rw [ContinuousLinearMap.intervalIntegral_apply (μ := volume) hcont.intervalIntegrable]
  apply intervalIntegral.integral_congr
  intro t ht
  have hs : ContMDiffAt I 𝓘(ℝ, F) ∞ (fun y => f (t, y)) x :=
    (hf.contMDiffAt ((hS.prod hU).mem_nhds ⟨hI ht, hx⟩)).comp x
      (contMDiffAt_const.prodMk contMDiffAt_id)
  exact congrArg (fun L => L v) (mvfderiv_eq_chart (hs.mdifferentiableAt (by simp))).symm

/-- The manifold derivative of a jointly smooth finite-interval integral is the
integral of the manifold derivatives. -/
theorem mvfderiv_intervalIntegral_apply (a b : ℝ) {f : ℝ × M → F}
    (hf : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, F) ∞ f)
    (x : M) (v : TangentSpace I x) :
    mvfderiv I (fun y => ∫ t in a..b, f (t, y)) x v =
      ∫ t in a..b, mvfderiv I (fun y => f (t, y)) x v :=
  mvfderiv_intervalIntegral_apply_of_contMDiffOn a b isOpen_univ isOpen_univ
    (subset_univ _) hf.contMDiffOn x (mem_univ x) v

/-- At a fixed point and tangent vector, the applied manifold derivative of a
jointly smooth family depends continuously on the real parameter. -/
theorem continuousOn_mvfderiv_apply_of_contMDiffOn {f : ℝ × M → F}
    {U : Set M} {S : Set ℝ} (hU : IsOpen U) (hS : IsOpen S)
    (hf : ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, F) ∞ f (S ×ˢ U))
    (x : M) (hx : x ∈ U) (v : TangentSpace I x) :
    ContinuousOn (fun t => mvfderiv I (fun y => f (t, y)) x v) S := by
  have hopen : IsOpen ((extChartAt I x).target ∩ (extChartAt I x).symm ⁻¹' U) :=
    (continuousOn_extChartAt_symm x).isOpen_inter_preimage
      (isOpen_extChartAt_target x) hU
  have hmem : extChartAt I x x ∈
      (extChartAt I x).target ∩ (extChartAt I x).symm ⁻¹' U := by
    refine ⟨mem_extChartAt_target x, ?_⟩
    simpa only [mem_preimage, extChartAt_to_inv] using hx
  have hG' := fderiv_fst_contDiffOn hopen hS (contDiffOn_in_chart (⊤ : ℕ∞) hf x)
  have hcont : ContinuousOn
      (fun t => fderiv ℝ (fun z => f (t, (extChartAt I x).symm z)) (extChartAt I x x)) S :=
    hG'.continuousOn.comp (continuousOn_const.prodMk continuousOn_id)
      (fun _ ht => ⟨hmem, ht⟩)
  have heval : ContinuousOn
      (fun t => fderiv ℝ (fun z => f (t, (extChartAt I x).symm z))
        (extChartAt I x x) (show E from v)) S :=
    hcont.clm_apply continuousOn_const
  apply heval.congr
  intro t ht
  have hs : ContMDiffAt I 𝓘(ℝ, F) ∞ (fun y => f (t, y)) x :=
    (hf.contMDiffAt ((hS.prod hU).mem_nhds ⟨ht, hx⟩)).comp x
      (contMDiffAt_const.prodMk contMDiffAt_id)
  exact congrArg (fun L => L v) (mvfderiv_eq_chart (hs.mdifferentiableAt (by simp)))

/-- The applied manifold derivative of a globally smooth family is continuous in
its parameter at each fixed point and tangent vector. -/
theorem continuous_mvfderiv_apply {f : ℝ × M → F}
    (hf : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, F) ∞ f)
    (x : M) (v : TangentSpace I x) :
    Continuous (fun t => mvfderiv I (fun y => f (t, y)) x v) := by
  rw [← continuousOn_univ]
  exact continuousOn_mvfderiv_apply_of_contMDiffOn isOpen_univ isOpen_univ
    hf.contMDiffOn x (mem_univ x) v

/-- Applied derivatives of a jointly smooth family are integrable over every
finite interval contained in its open parameter domain. -/
theorem intervalIntegrable_mvfderiv_apply_of_contMDiffOn (a b : ℝ) {f : ℝ × M → F}
    {U : Set M} {S : Set ℝ} (hU : IsOpen U) (hS : IsOpen S) (hI : uIcc a b ⊆ S)
    (hf : ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, F) ∞ f (S ×ˢ U))
    (x : M) (hx : x ∈ U) (v : TangentSpace I x) :
    IntervalIntegrable (fun t => mvfderiv I (fun y => f (t, y)) x v) volume a b :=
  ((continuousOn_mvfderiv_apply_of_contMDiffOn hU hS hf x hx v).mono hI).intervalIntegrable

/-- Applied derivatives of a globally smooth family are integrable over every
finite parameter interval. -/
theorem intervalIntegrable_mvfderiv_apply (a b : ℝ) {f : ℝ × M → F}
    (hf : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, F) ∞ f)
    (x : M) (v : TangentSpace I x) :
    IntervalIntegrable (fun t => mvfderiv I (fun y => f (t, y)) x v) volume a b :=
  (continuous_mvfderiv_apply hf x v).intervalIntegrable a b

end Manifold

end RicciFlowSharpEstimate.Analysis
