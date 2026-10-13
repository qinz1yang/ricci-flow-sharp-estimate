/-
Copyright (c) 2026 Ziyang Qin. All rights reserved.
No license is granted by this file.
Authors: Ziyang Qin
-/
import RicciFlowSharpEstimate.Geometry.AreaGeometricRealization
import RicciFlowSharpEstimate.Geometry.AreaProbeRayleigh
import RicciFlowSharpEstimate.Geometry.PhysicalProbeNonzero
import Mathlib.Tactic.Choose

/-!
# Unit-mass geometric sequence recovery from scalar limits

Smooth exact-moment curvature and probe sequences whose actual mass tends to one
have a positive-mass tail. The literal inverse-square-root mass normalization
tends to one and preserves the limit of the complete meridional action.

The accepted geometric producer realizes those same normalized probes. Its
inverse, reciprocal profile, probe, warp, derivative and curvature equations are
retained, together with the original shifted curvature boxes and ratio witnesses.
This is conditional sequence recovery from scalar limits; no scalar approximation
or continuous parameter family is asserted here.
-/

noncomputable section

namespace RicciFlowSharpEstimate.Geometry.AreaProfile

open Filter MeasureTheory Set DifferentialGeometry.Geometry.Curvature
open scoped ContDiff Topology

private theorem probe_nonzero_of_unit_mass (K r : ℝ → ℝ)
    (hr : Continuous r) (hmass : probeMass K r = 1) :
    ∃ x ∈ Ioo (0 : ℝ) 1, r x ≠ 0 := by
  by_contra hn
  have hz : EqOn r (fun _ => 0) (Ioo (0 : ℝ) 1) := by
    intro x hx
    by_contra hne
    exact hn ⟨x, hx, hne⟩
  have hc : EqOn r (fun _ => 0) (Icc (0 : ℝ) 1) := by
    have h := hz.closure hr continuous_const
    simpa only [closure_Ioo (by norm_num : (0 : ℝ) ≠ 1)] using h
  have hzero : probeMass K r = 0 := by
    unfold probeMass
    calc
      _ = ∫ _x in (0 : ℝ)..1, (0 : ℝ) := by
        apply intervalIntegral.integral_congr
        intro x hx
        have hx' : x ∈ Icc (0 : ℝ) 1 := by simpa using hx
        dsimp only
        rw [hc hx', zero_pow (by norm_num : (2 : ℕ) ≠ 0), mul_zero]
      _ = 0 := by simp
  rw [hzero] at hmass
  norm_num at hmass

private theorem exists_unit_mass_tail_of_scalar_limits
    (K r : ℕ → ℝ → ℝ) (A₀ : ℝ)
    (hK : ∀ n, ContDiff ℝ ∞ (K n)) (hr : ∀ n, ContDiff ℝ ∞ (r n))
    (hzero : ∀ n, (∫ x in (0 : ℝ)..1, K n x) = 2)
    (hone : ∀ n, (∫ x in (0 : ℝ)..1, x * K n x) = 1)
    (hmass : Tendsto (fun n => probeMass (K n) (r n)) atTop (𝓝 1))
    (hAction : Tendsto (fun n => meridionalAction (K n) (r n)) atTop (𝓝 A₀)) :
    ∃ (N : ℕ) (α : ℕ → ℝ),
      (∀ n, α n = 1 / Real.sqrt (probeMass (K (n + N)) (r (n + N)))) ∧
      (∀ n, 0 < α n) ∧ Tendsto α atTop (𝓝 1) ∧
      (∀ n, ContDiff ℝ ∞ (fun x => α n * r (n + N) x)) ∧
      (∀ n, probeMass (K (n + N)) (fun x => α n * r (n + N) x) = 1) ∧
      (∀ n, ∃ x ∈ Ioo (0 : ℝ) 1, α n * r (n + N) x ≠ 0) ∧
      (∀ n, meridionalAction (K (n + N)) (fun x => α n * r (n + N) x) =
        α n ^ 2 * meridionalAction (K (n + N)) (r (n + N))) ∧
      Tendsto (fun n => meridionalAction (K (n + N))
        (fun x => α n * r (n + N) x)) atTop (𝓝 A₀) := by
  have heventually : ∀ᶠ n in atTop, 0 < probeMass (K n) (r n) :=
    hmass.eventually (lt_mem_nhds zero_lt_one)
  obtain ⟨N, hN⟩ := eventually_atTop.1 heventually
  have hm (n : ℕ) : 0 < probeMass (K (n + N)) (r (n + N)) :=
    hN (n + N) (Nat.le_add_left N n)
  let α : ℕ → ℝ := fun n => 1 / Real.sqrt (probeMass (K (n + N)) (r (n + N)))
  have hαpos (n : ℕ) : 0 < α n :=
    one_div_pos.mpr (Real.sqrt_pos.mpr (hm n))
  have hmshift : Tendsto (fun n => probeMass (K (n + N)) (r (n + N)))
      atTop (𝓝 1) := hmass.comp (tendsto_add_atTop_nat N)
  have hsqrt : Tendsto (fun n => Real.sqrt (probeMass (K (n + N)) (r (n + N))))
      atTop (𝓝 1) := by
    simpa only [Real.sqrt_one] using hmshift.sqrt
  have hαlim : Tendsto α atTop (𝓝 1) := by
    have h := (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ))
      atTop (𝓝 1)).div hsqrt (by norm_num : (1 : ℝ) ≠ 0)
    simpa only [α, Pi.div_def, one_div_one] using h
  have hq (n : ℕ) : ContDiff ℝ ∞ (fun x => α n * r (n + N) x) :=
    contDiff_const.mul (hr (n + N))
  have hunit (n : ℕ) :
      probeMass (K (n + N)) (fun x => α n * r (n + N) x) = 1 := by
    change probeMass (K (n + N)) (normalizedProbe (K (n + N)) (r (n + N))) = 1
    exact probeMass_normalizedProbe _ _ (hm n)
  have hne (n : ℕ) : ∃ x ∈ Ioo (0 : ℝ) 1, α n * r (n + N) x ≠ 0 :=
    probe_nonzero_of_unit_mass _ _ (hq n).continuous (hunit n)
  have hscale (n : ℕ) :
      meridionalAction (K (n + N)) (fun x => α n * r (n + N) x) =
        α n ^ 2 * meridionalAction (K (n + N)) (r (n + N)) :=
    meridionalAction_const_mul _ _ (hK (n + N)) (hr (n + N))
      (hzero (n + N)) (hone (n + N)) (α n)
  refine ⟨N, α, fun _ => rfl, hαpos, hαlim, hq, hunit, hne, hscale, ?_⟩
  have heq : (fun n => meridionalAction (K (n + N))
      (fun x => α n * r (n + N) x)) =
      (fun n => α n ^ 2 * meridionalAction (K (n + N)) (r (n + N))) :=
    funext hscale
  rw [heq]
  have hshift := hAction.comp (tendsto_add_atTop_nat N)
  simpa only [Function.comp_def, one_pow, one_mul] using (hαlim.pow 2).mul hshift

/-- Scalar mass and complete-action limits give a unit-mass smooth sequence of
the actual rotational metrics and nonzero meridional forms. The normalization
and every geometric producer equation remain tied to the shifted input data;
the positive curvature boxes and their ratio witnesses are unchanged by scaling
the probes. This consumes scalar limits and does not construct their approximants. -/
theorem exists_smooth_geometric_recovery_of_scalar_limits
    (K r : ℕ → ℝ → ℝ) (κ Λ : ℕ → ℝ) (C A₀ : ℝ)
    (hK : ∀ n, ContDiff ℝ ∞ (K n)) (hr : ∀ n, ContDiff ℝ ∞ (r n))
    (hκ : ∀ n, 0 < κ n)
    (hbox : ∀ n, ∀ x ∈ Icc (0 : ℝ) 1, K n x ∈ Icc (κ n) (Λ n))
    (hratio : ∀ n, Λ n / κ n ≤ C)
    (hzero : ∀ n, (∫ x in (0 : ℝ)..1, K n x) = 2)
    (hone : ∀ n, (∫ x in (0 : ℝ)..1, x * K n x) = 1)
    (hmass : Tendsto (fun n => probeMass (K n) (r n)) atTop (𝓝 1))
    (hAction : Tendsto (fun n => meridionalAction (K n) (r n)) atTop (𝓝 A₀)) :
    ∃ (N : ℕ) (α : ℕ → ℝ) (X : ℕ → ℝ → ℝ)
      (D : ℕ → RotationalProfile.PoleData) (R : ℕ → ℝ → ℝ)
      (hR : ∀ n, ContDiff ℝ ∞ (R n)),
      (∀ n, α n = 1 / Real.sqrt (probeMass (K (n + N)) (r (n + N)))) ∧
      (∀ n, 0 < α n) ∧ Tendsto α atTop (𝓝 1) ∧
      (∀ n, ContDiff ℝ ∞ (fun x => α n * r (n + N) x)) ∧
      (∀ n, probeMass (K (n + N)) (fun x => α n * r (n + N) x) = 1) ∧
      (∀ n, ∃ x ∈ Ioo (0 : ℝ) 1, α n * r (n + N) x ≠ 0) ∧
      (∀ n, meridionalAction (K (n + N)) (fun x => α n * r (n + N) x) =
        α n ^ 2 * meridionalAction (K (n + N)) (r (n + N))) ∧
      Tendsto (fun n => meridionalAction (K (n + N))
        (fun x => α n * r (n + N) x)) atTop (𝓝 A₀) ∧
      (∀ n, 0 < κ (n + N) ∧ Λ (n + N) / κ (n + N) ≤ C ∧
        (∀ x ∈ Icc (0 : ℝ) 1, K (n + N) x ∈ Icc (κ (n + N)) (Λ (n + N))) ∧
        (∫ x in (0 : ℝ)..1, K (n + N) x) = 2 ∧
        (∫ x in (0 : ℝ)..1, x * K (n + N) x) = 1) ∧
      (∀ n, ContDiff ℝ ∞ (X n) ∧
        heightCoordinate (K (n + N)) 0 = -1 ∧ heightCoordinate (K (n + N)) 1 = 1 ∧
        X n (-1) = 0 ∧ X n 1 = 1 ∧
        MapsTo (heightCoordinate (K (n + N))) (Icc (0 : ℝ) 1) (Icc (-1 : ℝ) 1) ∧
        MapsTo (X n) (Icc (-1 : ℝ) 1) (Icc (0 : ℝ) 1) ∧
        (∀ x ∈ Icc (0 : ℝ) 1,
          X n (heightCoordinate (K (n + N)) x) = x ∧
          (D n).a (heightCoordinate (K (n + N)) x) = 1 / K (n + N) x ∧
          R n (heightCoordinate (K (n + N)) x) = α n * r (n + N) x ∧
          RotationalProfile.warp (D n).a (heightCoordinate (K (n + N)) x) =
            warp (K (n + N)) x) ∧
        (∀ v ∈ Icc (-1 : ℝ) 1,
          heightCoordinate (K (n + N)) (X n v) = v ∧
          deriv (X n) v * K (n + N) (X n v) = 1) ∧
        R n = (fun x => α n * r (n + N) x) ∘ X n ∧
        (∀ x ∈ Icc (0 : ℝ) 1,
          deriv (D n).a (heightCoordinate (K (n + N)) x) =
            -deriv (K (n + N)) x / K (n + N) x ^ 3 ∧
          deriv (R n) (heightCoordinate (K (n + N)) x) =
            deriv (fun x => α n * r (n + N) x) x / K (n + N) x ∧
          deriv (deriv (R n)) (heightCoordinate (K (n + N)) x) =
            deriv (deriv (fun x => α n * r (n + N) x)) x / K (n + N) x ^ 2 -
              deriv (fun x => α n * r (n + N) x) x * deriv (K (n + N)) x /
                K (n + N) x ^ 3) ∧
        (∀ p : RotationalSphere,
          metricScalarAt (D n).metric p / 2 = K (n + N) (X n (sphereHeight p))) ∧
        oneFormDissipation (D n).metric ((D n).meridionalOneForm (R n) (hR n)) =
          2 * Real.pi * meridionalAction (K (n + N)) (fun x => α n * r (n + N) x)) ∧
      (∀ n, MapsTo (heightCoordinate (K (n + N))) (Ioo (0 : ℝ) 1) (Ioo (-1 : ℝ) 1)) ∧
      (∀ n, ∀ p : RotationalSphere,
        metricScalarAt (D n).metric p / 2 ∈ Icc (κ (n + N)) (Λ (n + N))) ∧
      (∀ n, (D n).meridionalOneForm (R n) (hR n) ≠ 0) ∧
      Tendsto (fun n => oneFormDissipation (D n).metric
        ((D n).meridionalOneForm (R n) (hR n))) atTop (𝓝 (2 * Real.pi * A₀)) := by
  obtain ⟨N, α, hαeq, hαpos, hαlim, hq, hunit, hne, hscale, hlimit⟩ :=
    exists_unit_mass_tail_of_scalar_limits K r A₀ hK hr hzero hone hmass hAction
  have hpos (n : ℕ) (x : ℝ) (hx : x ∈ Icc (0 : ℝ) 1) : 0 < K (n + N) x :=
    (hκ (n + N)).trans_le (hbox (n + N) x hx).1
  have hreal := fun n => exists_smooth_geometric_realization (K (n + N))
    (fun x => α n * r (n + N) x) (hK (n + N)) (hq n) (hpos n)
    (hzero (n + N)) (hone (n + N))
  choose X D R hR hgeo using hreal
  have hVopen (n : ℕ) :
      MapsTo (heightCoordinate (K (n + N))) (Ioo (0 : ℝ) 1) (Ioo (-1 : ℝ) 1) := by
    intro x hx
    have hxc : x ∈ Icc (0 : ℝ) 1 := ⟨hx.1.le, hx.2.le⟩
    have hm := heightCoordinate_strictMonoOn (K (n + N))
      (hK (n + N)).continuous (hpos n)
    have hl := hm (by norm_num : (0 : ℝ) ∈ Icc (0 : ℝ) 1) hxc hx.1
    have hu := hm hxc (by norm_num : (1 : ℝ) ∈ Icc (0 : ℝ) 1) hx.2
    rw [heightCoordinate_zero] at hl
    rw [heightCoordinate_one _ (hzero (n + N))] at hu
    exact ⟨hl, hu⟩
  have hextra (n : ℕ) :
      (∀ p : RotationalSphere,
        metricScalarAt (D n).metric p / 2 ∈ Icc (κ (n + N)) (Λ (n + N))) ∧
      (D n).meridionalOneForm (R n) (hR n) ≠ 0 := by
    rcases hgeo n with ⟨_, _, _, _, _, _, hXmap, hbind, _, _, _, hcurv, _⟩
    constructor
    · intro p
      rw [hcurv p]
      exact hbox (n + N) _ (hXmap (sphereHeight_mem_Icc p))
    · apply ((D n).meridionalOneForm_ne_zero_iff (R n) (hR n)).2
      obtain ⟨x, hx, hnx⟩ := hne n
      refine ⟨heightCoordinate (K (n + N)) x, hVopen n hx, ?_⟩
      rw [(hbind x ⟨hx.1.le, hx.2.le⟩).2.2.1]
      exact hnx
  have hdiss (n : ℕ) :
      oneFormDissipation (D n).metric ((D n).meridionalOneForm (R n) (hR n)) =
        2 * Real.pi * meridionalAction (K (n + N)) (fun x => α n * r (n + N) x) := by
    rcases hgeo n with ⟨_, _, _, _, _, _, _, _, _, _, _, _, hd⟩
    exact hd
  refine ⟨N, α, X, D, R, hR, hαeq, hαpos, hαlim, hq, hunit, hne, hscale, hlimit,
    ?_, hgeo, hVopen, fun n => (hextra n).1, fun n => (hextra n).2, ?_⟩
  · intro n
    exact ⟨hκ (n + N), hratio (n + N), hbox (n + N), hzero (n + N), hone (n + N)⟩
  · have heq : (fun n => oneFormDissipation (D n).metric
        ((D n).meridionalOneForm (R n) (hR n))) =
        (fun n => 2 * Real.pi * meridionalAction (K (n + N))
          (fun x => α n * r (n + N) x)) := funext hdiss
    rw [heq]
    exact tendsto_const_nhds.mul hlimit

end RicciFlowSharpEstimate.Geometry.AreaProfile
