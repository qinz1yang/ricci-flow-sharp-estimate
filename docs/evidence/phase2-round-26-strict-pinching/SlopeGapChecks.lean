import RicciFlowSharpEstimate.Geometry.RotationalStrictPinching

noncomputable section
open Set MeasureTheory Filter Topology
open RicciFlowSharpEstimate.Geometry RicciFlowSharpEstimate.Geometry.AreaProfile
open DifferentialGeometry DifferentialGeometry.Tensor.RicciIdentity
open DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff ENNReal
local notation "areaμ" => volume.restrict (Ioo (0 : ℝ) 1)

local instance : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 2 + 1) :=
  ⟨finrank_euclideanSpace_fin⟩

-- Primary physical inputs suffice, without normalization or a reference mode.
example (K r : ℝ → ℝ) (hK : Continuous K) (hr : ContDiff ℝ 2 r)
    (hzero : (∫ x in (0 : ℝ)..1, K x) = 2)
    (hone : (∫ x in (0 : ℝ)..1, x * K x) = 1)
    (κ Λ : ℝ) (hκ : 0 < κ)
    (hbox : ∀ x ∈ Icc (0 : ℝ) 1, κ ≤ K x ∧ K x ≤ Λ)
    (hpinch : Λ ^ 2 ≤ 2 * κ * Λ + κ ^ 2 / 2) :
    3 * κ ^ 2 / 64 * (∫ x in (0 : ℝ)..1,
      warp K x * warpSlope K x ^ 2 * r x ^ 2) ≤ meridionalAction K r :=
  meridionalAction_ge_slope_mass_of_quadratic_pinching K r hK hr hzero hone κ Λ
    hκ hbox hpinch

-- The displayed weak object and every strong recovery limit stay tied.
example {C : ℝ} {K r p z : ℝ → ℝ} (hC : 1 ≤ C)
    (hupper : C ≤ 1 + Real.sqrt (3 / 2))
    (h : IsRecoverableAreaCompetitor C K r p z) :
    0 < weakMeridionalAction K r p z ∧
    ∃ Ks rs : ℕ → ℝ → ℝ,
      (∀ n, IsSmoothAreaCompetitor C (Ks n) (rs n)) ∧
      Tendsto (fun n => eLpNorm (Ks n - K) 2 areaμ) atTop (𝓝 0) ∧
      Tendsto (fun n => eLpNorm (rs n - r) 2 areaμ) atTop (𝓝 0) ∧
      Tendsto (fun n => eLpNorm
        ((fun x => Real.sqrt (x * (1 - x)) * deriv (rs n) x) -
          (fun x => Real.sqrt (x * (1 - x)) * p x)) 2 areaμ) atTop (𝓝 0) ∧
      Tendsto (fun n => eLpNorm
        ((fun x => x * (1 - x) * Real.sqrt (x * (1 - x)) * deriv (deriv (rs n)) x) -
          (fun x => x * (1 - x) * Real.sqrt (x * (1 - x)) * z x)) 2 areaμ)
        atTop (𝓝 0) ∧
      Tendsto (fun n => meridionalAction (Ks n) (rs n)) atTop
        (𝓝 (weakMeridionalAction K r p z)) := by
  obtain ⟨_, _, Ks, rs, hS, hKS, hRS, hPS, hZS, hA⟩ := h.exists_action_recovery hC
  exact ⟨h.action_pos_of_quadratic_pinching hC hupper,
    Ks, rs, hS, hKS, hRS, hPS, hZS, hA⟩

-- A genuine original smooth unit-mass member makes both weak conclusions nonvacuous.
example : 0 < ∫ x, warp (fun _ => 2) x * warpSlope (fun _ => 2) x ^ 2 *
      Real.sqrt 3 ^ 2 ∂areaμ := by
  exact (isSmoothAreaCompetitor_round 1 le_rfl).recoverable
    |>.integral_warp_mul_slope_sq_mul_probe_sq_pos le_rfl

example : 0 < weakMeridionalAction (fun _ => 2) (fun _ => Real.sqrt 3)
    (deriv (fun _ : ℝ => Real.sqrt 3)) (deriv (deriv (fun _ : ℝ => Real.sqrt 3))) := by
  exact (isSmoothAreaCompetitor_round 1 le_rfl).recoverable
    |>.action_pos_of_quadratic_pinching le_rfl
      (by have hs := Real.sqrt_nonneg (3 / 2 : ℝ); linarith)

-- The same arbitrary original metric and form remain in the all-form comparison.
example {C : ℝ} (hC : 1 ≤ C) (hupper : C ≤ 1 + Real.sqrt (3 / 2))
    (g : SmoothRiemannianMetric (𝓡 2) RotationalSphere)
    (hg : IsRepresentedRotationalMetric g) (κ Λ : ℝ) (hκ : 0 < κ)
    (hbox : ∀ x : RotationalSphere, κ ≤ metricScalarAt g x / 2 ∧
      metricScalarAt g x / 2 ≤ Λ) (hratio : Λ / κ ≤ C)
    (h : OneFormSection (I := 𝓡 2) (M := RotationalSphere)) :
    0 ≤ oneFormDissipation g h := by
  exact (rotationalSafeCaps_downward quadratic_pinching_mem_rotationalSafeCaps hC hupper).2
    g hg κ Λ hκ hbox hratio h

example : (1 + Real.sqrt (3 / 2) : ℝ) < rotationalThreshold ∧
    rotationalThreshold < conformalKillingThreshold :=
  ⟨quadratic_pinching_lt_rotationalThreshold, rotationalThreshold_lt_conformalKillingThreshold⟩
