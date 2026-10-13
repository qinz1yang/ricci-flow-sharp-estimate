/-
Copyright (c) 2026 Ziyang Qin. All rights reserved.
No license is granted by this file.
Authors: Ziyang Qin
-/
import RicciFlowSharpEstimate.Geometry.AreaJointActionCompactness
import RicciFlowSharpEstimate.Geometry.AreaScalarGraphRecovery
import RicciFlowSharpEstimate.Geometry.SmoothAreaRecoveryNormalization

/-!
# Actual joint weak limits with smooth geometric recovery

For an original normalized smooth sublevel sequence, the actual joint limit
has complete-action liminf control and a genuinely constructed smooth
recovery sequence. Recovery preserves the original ratio and both moments,
normalizes the physical mass exactly, and returns the original sphere
metrics and physically nonzero forms with all producer equations retained.
-/

noncomputable section

namespace RicciFlowSharpEstimate.Geometry.AreaProfile

open Set MeasureTheory Filter Topology DifferentialGeometry.Geometry.Curvature
open scoped ContDiff ENNReal

local notation "areaμ" => volume.restrict (Ioo (0 : ℝ) 1)

/-- Original normalized smooth sublevels produce a joint weak limit with
complete-action liminf control and an actual smooth geometric recovery
sequence. The smooth original sequence, not a recovery or limit package,
is the input. No symmetry, monotonicity or pole trace constraint is added. -/
theorem exists_joint_weak_limit_with_smooth_geometric_recovery
    (K r : ℕ → ℝ → ℝ) (κ Λ : ℕ → ℝ) (C B : ℝ) (hC : 1 ≤ C)
    (hK : ∀ n, ContDiff ℝ ∞ (K n)) (hr : ∀ n, ContDiff ℝ ∞ (r n))
    (hκ : ∀ n, 0 < κ n)
    (hbox : ∀ n x, x ∈ Icc (0 : ℝ) 1 → κ n ≤ K n x ∧ K n x ≤ Λ n)
    (hratio : ∀ n, Λ n / κ n ≤ C)
    (hzero : ∀ n, (∫ x in (0 : ℝ)..1, K n x) = 2)
    (hone : ∀ n, (∫ x in (0 : ℝ)..1, x * K n x) = 1)
    (hmass : ∀ n, probeMass (K n) (r n) = 1)
    (hA : ∀ n, meridionalAction (K n) (r n) ≤ B) :
    ∃ K0 r0 p0 z0 : ℝ → ℝ, ∃ κ0 Λ0 : ℝ, ∃ φ : ℕ → ℕ,
      StrictMono φ ∧ MemLp K0 2 areaμ ∧ MemLp K0 ∞ areaμ ∧ 0 < κ0 ∧ Λ0 / κ0 ≤ C ∧
      (∀ᵐ x ∂areaμ, κ0 ≤ K0 x ∧ K0 x ≤ Λ0) ∧
      Tendsto (fun n => κ (φ n)) atTop (𝓝 κ0) ∧
      Tendsto (fun n => Λ (φ n)) atTop (𝓝 Λ0) ∧
      (∫ x in (0 : ℝ)..1, K0 x) = 2 ∧ (∫ x in (0 : ℝ)..1, x * K0 x) = 1 ∧
      Analysis.HasParabolicWeakDerivatives r0 p0 z0 ∧
      ContinuousOn r0 (Ioo 0 1) ∧ ContinuousOn p0 (Ioo 0 1) ∧
      ContinuousOn (warp K0) (Icc (0 : ℝ) 1) ∧
      ContinuousOn (warpSlope K0) (Icc (0 : ℝ) 1) ∧
      Analysis.HasWeakDerivOn (Ioo 0 1) (warp K0) (warpSlope K0) ∧
      Analysis.HasWeakDerivOn (Ioo 0 1) (warpSlope K0) (fun x => -2 * K0 x) ∧
      IntervalIntegrable (fun x => meridionalActionDensity (warp K0 x) (warpSlope K0 x)
        (K0 x) (r0 x) (p0 x) (z0 x)) volume 0 1 ∧
      MemLp (fun x => Real.sqrt (warp K0 x) * weakMeridionalOperator K0 r0 p0 z0 x) 2 areaμ ∧
      MemLp (fun x => Real.sqrt (warp K0 x) * (K0 x * r0 x)) 2 areaμ ∧
      (∀ x ∈ Icc (0 : ℝ) 1, (2 / C) * x * (1 - x) ≤ warp K0 x ∧
        warp K0 x ≤ (2 * C) * x * (1 - x) ∧ |warpSlope K0 x| ≤ 2) ∧
      (warp K0 0 = 0 ∧ warp K0 1 = 0 ∧ warpSlope K0 0 = 2 ∧ warpSlope K0 1 = -2) ∧
      Integrable (fun x => warp K0 x * r0 x ^ 2) areaμ ∧ probeMass K0 r0 = 1 ∧
      (∃ x ∈ Ioo (0 : ℝ) 1, r0 x ≠ 0) ∧
      Tendsto (fun n => eLpNorm (r (φ n) - r0) 2 areaμ) atTop (𝓝 0) ∧
      TendstoLocallyUniformlyOn (fun n => r (φ n)) r0 atTop (Ioo 0 1) ∧
      TendstoLocallyUniformlyOn (fun n => deriv (r (φ n))) p0 atTop (Ioo 0 1) ∧
      TendstoUniformlyOn (fun n => warp (K (φ n))) (warp K0) atTop (Icc (0 : ℝ) 1) ∧
      TendstoUniformlyOn (fun n => warpSlope (K (φ n))) (warpSlope K0) atTop (Icc (0 : ℝ) 1) ∧
      (∀ v : ℝ → ℝ, Integrable v areaμ →
        Tendsto (fun n => ∫ x, K (φ n) x * v x ∂areaμ) atTop
          (𝓝 (∫ x, K0 x * v x ∂areaμ))) ∧
      (∀ v : Lp ℝ 2 areaμ,
        Tendsto (fun n => ∫ x, (x * (1 - x) * Real.sqrt (x * (1 - x)) *
          deriv (deriv (r (φ n))) x) * v x ∂areaμ) atTop
          (𝓝 (∫ x, (x * (1 - x) * Real.sqrt (x * (1 - x)) * z0 x) * v x ∂areaμ))) ∧
      (∀ v : Lp ℝ 2 areaμ,
        Tendsto (fun n => ∫ x, (Real.sqrt (warp (K (φ n)) x) *
          meridionalOperator (K (φ n)) (r (φ n)) x) * v x ∂areaμ) atTop
          (𝓝 (∫ x, (Real.sqrt (warp K0 x) * weakMeridionalOperator K0 r0 p0 z0 x) * v x ∂areaμ))) ∧
      (∀ v : Lp ℝ 2 areaμ,
        Tendsto (fun n => ∫ x, (Real.sqrt (warp (K (φ n)) x) *
          (K (φ n) x * r (φ n) x)) * v x ∂areaμ) atTop
          (𝓝 (∫ x, (Real.sqrt (warp K0 x) * (K0 x * r0 x)) * v x ∂areaμ))) ∧
      weakMeridionalAction K0 r0 p0 z0 ≤
        liminf (fun n => meridionalAction (K n) (r n)) atTop ∧
    ∃ (Ks rs : ℕ → ℝ → ℝ) (κs Λs : ℕ → ℝ),
      (∀ n, ContDiff ℝ ∞ (Ks n) ∧ ContDiff ℝ ∞ (rs n) ∧ 0 < κs n ∧
        (∀ x ∈ Icc (0 : ℝ) 1, κs n ≤ Ks n x ∧ Ks n x ≤ Λs n) ∧
        Λs n / κs n ≤ C ∧ (∫ x in (0 : ℝ)..1, Ks n x) = 2 ∧
        (∫ x in (0 : ℝ)..1, x * Ks n x) = 1) ∧
      Tendsto (fun n => eLpNorm (Ks n - K0) 2 areaμ) atTop (𝓝 0) ∧
      (∀ᵐ x ∂areaμ, Tendsto (fun n => Ks n x) atTop (𝓝 (K0 x))) ∧
      Tendsto (fun n => eLpNorm (rs n - r0) 2 areaμ) atTop (𝓝 0) ∧
      Tendsto (fun n => eLpNorm ((fun x => Real.sqrt (x * (1 - x)) * deriv (rs n) x) -
        (fun x => Real.sqrt (x * (1 - x)) * p0 x)) 2 areaμ) atTop (𝓝 0) ∧
      Tendsto (fun n => eLpNorm
        ((fun x => x * (1 - x) * Real.sqrt (x * (1 - x)) * deriv (deriv (rs n)) x) -
          (fun x => x * (1 - x) * Real.sqrt (x * (1 - x)) * z0 x)) 2 areaμ)
        atTop (𝓝 0) ∧
      Tendsto (fun n => probeMass (Ks n) (rs n)) atTop (𝓝 1) ∧
      Tendsto (fun n => meridionalAction (Ks n) (rs n)) atTop
        (𝓝 (weakMeridionalAction K0 r0 p0 z0)) ∧
    ∃ (N : ℕ) (α : ℕ → ℝ) (X : ℕ → ℝ → ℝ)
      (D : ℕ → RotationalProfile.PoleData) (R : ℕ → ℝ → ℝ)
      (hR : ∀ n, ContDiff ℝ ∞ (R n)),
      (∀ n, α n = 1 / Real.sqrt (probeMass (Ks (n + N)) (rs (n + N)))) ∧
      (∀ n, 0 < α n) ∧ Tendsto α atTop (𝓝 1) ∧
      (∀ n, ContDiff ℝ ∞ (fun x => α n * rs (n + N) x)) ∧
      (∀ n, probeMass (Ks (n + N)) (fun x => α n * rs (n + N) x) = 1) ∧
      (∀ n, ∃ x ∈ Ioo (0 : ℝ) 1, α n * rs (n + N) x ≠ 0) ∧
      (∀ n, meridionalAction (Ks (n + N)) (fun x => α n * rs (n + N) x) =
        α n ^ 2 * meridionalAction (Ks (n + N)) (rs (n + N))) ∧
      Tendsto (fun n => meridionalAction (Ks (n + N))
        (fun x => α n * rs (n + N) x)) atTop (𝓝 (weakMeridionalAction K0 r0 p0 z0)) ∧
      (∀ n, 0 < κs (n + N) ∧ Λs (n + N) / κs (n + N) ≤ C ∧
        (∀ x ∈ Icc (0 : ℝ) 1, Ks (n + N) x ∈ Icc (κs (n + N)) (Λs (n + N))) ∧
        (∫ x in (0 : ℝ)..1, Ks (n + N) x) = 2 ∧
        (∫ x in (0 : ℝ)..1, x * Ks (n + N) x) = 1) ∧
      (∀ n, ContDiff ℝ ∞ (X n) ∧
        heightCoordinate (Ks (n + N)) 0 = -1 ∧ heightCoordinate (Ks (n + N)) 1 = 1 ∧
        X n (-1) = 0 ∧ X n 1 = 1 ∧
        MapsTo (heightCoordinate (Ks (n + N))) (Icc (0 : ℝ) 1) (Icc (-1 : ℝ) 1) ∧
        MapsTo (X n) (Icc (-1 : ℝ) 1) (Icc (0 : ℝ) 1) ∧
        (∀ x ∈ Icc (0 : ℝ) 1,
          X n (heightCoordinate (Ks (n + N)) x) = x ∧
          (D n).a (heightCoordinate (Ks (n + N)) x) = 1 / Ks (n + N) x ∧
          R n (heightCoordinate (Ks (n + N)) x) = α n * rs (n + N) x ∧
          RotationalProfile.warp (D n).a (heightCoordinate (Ks (n + N)) x) =
            warp (Ks (n + N)) x) ∧
        (∀ v ∈ Icc (-1 : ℝ) 1,
          heightCoordinate (Ks (n + N)) (X n v) = v ∧
          deriv (X n) v * Ks (n + N) (X n v) = 1) ∧
        R n = (fun x => α n * rs (n + N) x) ∘ X n ∧
        (∀ x ∈ Icc (0 : ℝ) 1,
          deriv (D n).a (heightCoordinate (Ks (n + N)) x) =
            -deriv (Ks (n + N)) x / Ks (n + N) x ^ 3 ∧
          deriv (R n) (heightCoordinate (Ks (n + N)) x) =
            deriv (fun x => α n * rs (n + N) x) x / Ks (n + N) x ∧
          deriv (deriv (R n)) (heightCoordinate (Ks (n + N)) x) =
            deriv (deriv (fun x => α n * rs (n + N) x)) x / Ks (n + N) x ^ 2 -
              deriv (fun x => α n * rs (n + N) x) x * deriv (Ks (n + N)) x /
                Ks (n + N) x ^ 3) ∧
        (∀ p : RotationalSphere,
          metricScalarAt (D n).metric p / 2 = Ks (n + N) (X n (sphereHeight p))) ∧
        oneFormDissipation (D n).metric ((D n).meridionalOneForm (R n) (hR n)) =
          2 * Real.pi * meridionalAction (Ks (n + N)) (fun x => α n * rs (n + N) x)) ∧
      (∀ n, MapsTo (heightCoordinate (Ks (n + N))) (Ioo (0 : ℝ) 1) (Ioo (-1 : ℝ) 1)) ∧
      (∀ n, ∀ p : RotationalSphere,
        metricScalarAt (D n).metric p / 2 ∈ Icc (κs (n + N)) (Λs (n + N))) ∧
      (∀ n, (D n).meridionalOneForm (R n) (hR n) ≠ 0) ∧
      Tendsto (fun n => oneFormDissipation (D n).metric
        ((D n).meridionalOneForm (R n) (hR n))) atTop
        (𝓝 (2 * Real.pi * weakMeridionalAction K0 r0 p0 z0)) := by
  have hCpos : 0 < C := zero_lt_one.trans_le hC
  obtain ⟨K0, r0, p0, z0, κ0, Λ0, φ, hφ, hK02, hK0inf, hκ0, hratio0,
    hbox0, hκconv, hΛconv, hzero0, hone0, hgraph, hr0c, hp0c, hf0c, hb0c,
    hDf, hDb, hActionInt, hQmem, hVmem, hgeom, hpoles, hMassInt, hmass0, hnz,
    hstrong, hrlocal, hplocal, hF, hbF, hKweak, hzweak, hQweak, hVweak, hAliminf⟩ :=
    exists_normalized_joint_weak_limit_le_liminf_action K r κ Λ C B hC
      (fun n => (hK n).continuous) (fun n => (hr n).of_le (by simp))
      hκ hbox hratio hzero hone hmass hA
  have hGN (n : ℕ) := Analysis.hasParabolicWeakDerivatives_of_contDiff
    ((hr (φ n)).of_le (by simp))
  have hKW : ∀ v : Lp ℝ 2 areaμ,
      Tendsto (fun n => ∫ x, K (φ n) x * v x ∂areaμ) atTop
        (𝓝 (∫ x, K0 x * v x ∂areaμ)) :=
    fun v => hKweak v ((Lp.memLp v).integrable (by norm_num))
  have hRW : ∀ v : Lp ℝ 2 areaμ,
      Tendsto (fun n => ∫ x, r (φ n) x * v x ∂areaμ) atTop
        (𝓝 (∫ x, r0 x * v x ∂areaμ)) := by
    intro v
    have hvzero : Tendsto
        (fun _ : ℕ => eLpNorm ((v : ℝ → ℝ) - (v : ℝ → ℝ)) 2 areaμ) atTop (𝓝 0) := by
      simp only [sub_self, eLpNorm_zero]
      exact tendsto_const_nhds
    exact (Analysis.tendsto_integral_mul_of_tendsto_eLpNorm_two
      (fun n => (hGN n).memLp) hgraph.memLp (fun _ => Lp.memLp v) (Lp.memLp v)
      hstrong hvzero).2.2
  have hCommon (n : ℕ) : ∀ x ∈ Icc (0 : ℝ) 1,
      2 / C ≤ K (φ n) x ∧ K (φ n) x ≤ 2 * C :=
    curvature_bounds_of_ratio (K (φ n)) (hK (φ n)).continuous
      (κ (φ n)) (Λ (φ n)) C (hκ (φ n)) (hbox (φ n)) (hratio (φ n)) (hzero (φ n))
  obtain ⟨M, _, hMb⟩ := exists_uniform_parabolic_graph_bound
    (2 / C) (2 * C) (by positivity) (by positivity) B
  have hPb (n : ℕ) :
      (∫ x, (Real.sqrt (x * (1 - x)) * deriv (r (φ n)) x) ^ 2 ∂areaμ) ≤ M :=
    (hMb (K (φ n)) (r (φ n)) (hK (φ n)).continuous ((hr (φ n)).of_le (by simp))
      (hCommon n) (hzero (φ n)) (hone (φ n)) (hmass (φ n)) (hA (φ n))).2.1
  have hPpoint : ∀ᵐ x ∂areaμ,
      Tendsto (fun n => Real.sqrt (x * (1 - x)) * deriv (r (φ n)) x) atTop
        (𝓝 (Real.sqrt (x * (1 - x)) * p0 x)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
    exact (hplocal.tendsto_at hx).const_mul _
  have hPW : ∀ v : Lp ℝ 2 areaμ,
      Tendsto (fun n => ∫ x,
        (Real.sqrt (x * (1 - x)) * deriv (r (φ n)) x) * v x ∂areaμ) atTop
        (𝓝 (∫ x, (Real.sqrt (x * (1 - x)) * p0 x) * v x ∂areaμ)) :=
    fun v => Analysis.tendsto_integral_mul_of_ae_tendsto_of_integral_sq_bound
      (fun n => (hGN n).memLp_weighted_deriv) (Lp.memLp v) M hPb hPpoint
  obtain ⟨Ks, rs, κs, Λs, hScalar, hKsStrong, hKsAE, hRsStrong, hPsStrong,
    hZsStrong, hMassLimit, hActionLimit⟩ :=
    exists_smooth_scalar_recovery_of_weak_graph_pairings
      (fun n => K (φ n)) (fun n => r (φ n)) (fun n => κ (φ n)) (fun n => Λ (φ n))
      C K0 r0 p0 z0 hC (fun n => hK (φ n)) (fun n => hr (φ n)) (fun n => hκ (φ n))
      (fun n => hbox (φ n)) (fun n => hratio (φ n)) (fun n => hzero (φ n))
      (fun n => hone (φ n)) hK02 hgraph hKW hRW hPW hzweak hzero0 hone0 hmass0
  refine ⟨K0, r0, p0, z0, κ0, Λ0, φ, hφ, hK02, hK0inf, hκ0, hratio0,
    hbox0, hκconv, hΛconv, hzero0, hone0, hgraph, hr0c, hp0c, hf0c, hb0c,
    hDf, hDb, hActionInt, hQmem, hVmem, hgeom, hpoles, hMassInt, hmass0, hnz,
    hstrong, hrlocal, hplocal, hF, hbF, hKweak, hzweak, hQweak, hVweak, hAliminf,
    Ks, rs, κs, Λs, hScalar, hKsStrong, hKsAE, hRsStrong, hPsStrong, hZsStrong,
    hMassLimit, hActionLimit, ?_⟩
  exact exists_smooth_geometric_recovery_of_scalar_limits Ks rs κs Λs C
    (weakMeridionalAction K0 r0 p0 z0) (fun n => (hScalar n).1)
    (fun n => (hScalar n).2.1) (fun n => (hScalar n).2.2.1)
    (fun n => (hScalar n).2.2.2.1) (fun n => (hScalar n).2.2.2.2.1)
    (fun n => (hScalar n).2.2.2.2.2.1) (fun n => (hScalar n).2.2.2.2.2.2)
    hMassLimit hActionLimit

end RicciFlowSharpEstimate.Geometry.AreaProfile
