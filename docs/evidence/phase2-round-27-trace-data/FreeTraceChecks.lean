/-
Copyright (c) 2026 Ziyang Qin. All rights reserved.
No license is granted by this file.
Authors: Ziyang Qin
-/
import RicciFlowSharpEstimate.Geometry.AreaAction
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# A private diagnostic for one explicit free-trace completion

The calculation concerns the complete Hamiltonian of the single produced
rational-angular family below. It asserts neither an angular classification nor
negativity of an integrated action. The original rotational goal remains open.
-/

noncomputable section

namespace RicciFlowSharpEstimate.Geometry.AreaProfile

open Filter Set MeasureTheory
open scoped Topology

private def completeHamiltonian (f b K r v Px Pf Pb Pr Pv : ℝ) : ℝ :=
  Px + b * Pf + (v / f) * Pr - (b * v / f) * Pv - Pv ^ 2 / (4 * f) +
    K * (-2 * Pb + r * Pv - b * r * v - b ^ 2 * r ^ 2 / 2) + f * K ^ 2 * r ^ 2

/-- This identity retains every term of the actual six-entry area density. -/
private theorem density_add_jet_eq_square (f b K r r1 r2 Px Pf Pb Pr Pv : ℝ)
    (hf : f ≠ 0) :
    meridionalActionDensity f b K r r1 r2 +
        (Px + b * Pf - 2 * K * Pb + r1 * Pr + (f * r2 + b * r1) * Pv) =
      f * (f * r2 + 2 * b * r1 - K * r + Pv / (2 * f)) ^ 2 +
        completeHamiltonian f b K r (f * r1) Px Pf Pb Pr Pv := by
  unfold meridionalActionDensity completeHamiltonian
  field_simp [hf]
  ring

private def traceAmplitude (b : ℝ) : ℝ := Real.sqrt ((9 / 16 : ℝ) * b)

private def freeTrace (f b : ℝ) : ℝ :=
  (9 / 8 : ℝ) * Real.log f + (4 / 3 : ℝ) * b * traceAmplitude b - b ^ 3 / 12

private def tracePotential (ε f b r v : ℝ) : ℝ :=
  freeTrace f b * r ^ 2 + 2 * traceAmplitude b * r * v +
    ε * f * r ^ 2 * v ^ 2 / (r ^ 2 + v ^ 2)

private def traceValue : ℝ := (9 / 8 : ℝ) * Real.log (3 / 8) + 11 / 12

private theorem traceAmplitude_one : traceAmplitude 1 = 3 / 4 := by
  unfold traceAmplitude
  rw [mul_one]
  apply (Real.sqrt_eq_iff_eq_sq (by norm_num) (by norm_num)).2
  norm_num

private theorem freeTrace_point : freeTrace (3 / 8) 1 = traceValue := by
  unfold freeTrace traceValue
  rw [traceAmplitude_one]
  ring

/-- The produced trace has the exact constant-axis square, without a sign hypothesis. -/
private theorem freeTrace_axis_identity (f b K : ℝ) (hf : f ≠ 0) (hb : 0 < b) :
    completeHamiltonian f b K 1 0 0 ((9 / 8) / f)
      (2 * traceAmplitude b - b ^ 2 / 4) (2 * freeTrace f b)
      (2 * traceAmplitude b) = f * (K - traceAmplitude b / f) ^ 2 := by
  have hg : traceAmplitude b ^ 2 = (9 / 16 : ℝ) * b := by
    exact Real.sq_sqrt (mul_nonneg (by norm_num) hb.le)
  have hnum : (9 / 8 : ℝ) * b - traceAmplitude b ^ 2 = traceAmplitude b ^ 2 := by
    nlinarith [hg]
  calc
    _ = f * K ^ 2 - 2 * K * traceAmplitude b +
        ((9 / 8 : ℝ) * b - traceAmplitude b ^ 2) / f := by
      unfold completeHamiltonian
      field_simp [hf]
      ring
    _ = f * K ^ 2 - 2 * K * traceAmplitude b + traceAmplitude b ^ 2 / f := by
      rw [hnum]
    _ = _ := by
      field_simp [hf]
      ring

private def pointPartialF (ε t : ℝ) : ℝ := 3 + ε * t ^ 2 / (1 + t ^ 2)

private def pointPartialB (t : ℝ) : ℝ := 5 / 4 + (3 / 4) * t

private def pointPartialR (ε t : ℝ) : ℝ :=
  2 * traceValue + (3 / 2) * t + (3 * ε / 4) * t ^ 4 / (1 + t ^ 2) ^ 2

private def pointPartialV (ε t : ℝ) : ℝ :=
  3 / 2 + (3 * ε / 4) * t / (1 + t ^ 2) ^ 2

private theorem traceAmplitude_hasDerivAt_one :
    HasDerivAt traceAmplitude (3 / 8) 1 := by
  have h := ((hasDerivAt_id (1 : ℝ)).const_mul (9 / 16 : ℝ)).sqrt (by norm_num)
  have hs : Real.sqrt (9 / 16 : ℝ) = 3 / 4 := by
    simpa only [traceAmplitude, mul_one] using traceAmplitude_one
  simp only [id_eq, mul_one, hs] at h
  norm_num only at h
  exact h

/-- The four point jets are derivatives of the displayed potential, not assumptions. -/
private theorem tracePotential_hasDerivAt_f (ε t : ℝ) :
    HasDerivAt (fun f => tracePotential ε f 1 1 t) (pointPartialF ε t) (3 / 8) := by
  have hlog := (Real.hasDerivAt_log (by norm_num : (3 / 8 : ℝ) ≠ 0)).const_mul (9 / 8 : ℝ)
  have hbase := ((hlog.add_const ((4 / 3 : ℝ) * 1 * traceAmplitude 1)).sub_const
    ((1 : ℝ) ^ 3 / 12)).mul_const ((1 : ℝ) ^ 2)
  have hrat := (((((hasDerivAt_id (3 / 8 : ℝ)).const_mul ε).mul_const
    ((1 : ℝ) ^ 2)).mul_const (t ^ 2)).div_const (1 + t ^ 2))
  convert (hbase.add_const (2 * traceAmplitude 1 * 1 * t)).add hrat using 1
  · funext f
    simp only [tracePotential, freeTrace, one_pow, Pi.add_apply, id_eq]
  · norm_num [pointPartialF]

private theorem tracePotential_hasDerivAt_b (ε t : ℝ) :
    HasDerivAt (fun b => tracePotential ε (3 / 8) b 1 t) (pointPartialB t) 1 := by
  have hid := hasDerivAt_id (1 : ℝ)
  have hbase := (((hid.mul traceAmplitude_hasDerivAt_one).const_mul (4 / 3 : ℝ)).const_add
    ((9 / 8 : ℝ) * Real.log (3 / 8))).sub ((hid.pow 3).div_const 12)
  have hcross := ((traceAmplitude_hasDerivAt_one.const_mul 2).mul_const 1).mul_const t
  convert ((hbase.mul_const ((1 : ℝ) ^ 2)).add hcross).add_const
    (ε * (3 / 8) * (1 : ℝ) ^ 2 * t ^ 2 / (1 + t ^ 2)) using 1
  · funext b
    simp only [tracePotential, freeTrace, one_pow, Pi.add_apply, Pi.sub_apply,
      Pi.mul_apply, Pi.pow_apply, id_eq]
    ring
  · norm_num [pointPartialB, traceAmplitude_one]

private theorem tracePotential_hasDerivAt_r (ε t : ℝ) :
    HasDerivAt (fun r => tracePotential ε (3 / 8) 1 r t) (pointPartialR ε t) 1 := by
  have hid := hasDerivAt_id (1 : ℝ)
  have hden : (1 : ℝ) + t ^ 2 ≠ 0 := by positivity
  have hrat := ((((hid.pow 2).const_mul (ε * (3 / 8))).mul_const (t ^ 2)).div
    ((hid.pow 2).add_const (t ^ 2)) (by simpa using hden))
  have hbase := ((hid.pow 2).const_mul (freeTrace (3 / 8) 1)).add
    ((hid.const_mul (2 * traceAmplitude 1)).mul_const t)
  convert hbase.add hrat using 1
  · funext r
    simp only [tracePotential, Pi.add_apply, Pi.pow_apply, Pi.div_apply, id_eq]
  · simp only [pointPartialR, freeTrace_point, traceAmplitude_one,
      Pi.pow_apply, id_eq]
    norm_num only [Nat.cast_ofNat, one_pow, mul_one, one_mul, Nat.reduceSub]
    field_simp [hden]
    ring

private theorem tracePotential_hasDerivAt_v (ε t : ℝ) :
    HasDerivAt (fun v => tracePotential ε (3 / 8) 1 1 v) (pointPartialV ε t) t := by
  have hid := hasDerivAt_id t
  have hden : (1 : ℝ) + t ^ 2 ≠ 0 := by positivity
  have hrat := (((hid.pow 2).const_mul (ε * (3 / 8) * (1 : ℝ) ^ 2)).div
    ((hid.pow 2).const_add 1) hden)
  have hbase := (hid.const_mul (2 * traceAmplitude 1 * 1)).const_add
    (freeTrace (3 / 8) 1 * (1 : ℝ) ^ 2)
  convert hbase.add hrat using 1
  · funext v
    simp only [tracePotential, one_pow, Pi.add_apply, Pi.pow_apply, Pi.div_apply, id_eq]
  · simp only [pointPartialV, traceAmplitude_one, one_pow, Pi.pow_apply, id_eq]
    norm_num only [Nat.cast_ofNat, mul_one, one_mul, Nat.reduceSub]
    field_simp [hden]
    ring

private def traceHamiltonian (ε t : ℝ) : ℝ :=
  completeHamiltonian (3 / 8) 1 2 1 t 0
    (pointPartialF ε t) (pointPartialB t) (pointPartialR ε t) (pointPartialV ε t)

/-- Substituting actual partial derivatives gives the same complete Hamiltonian. -/
private theorem traceHamiltonian_eq_potential_derivatives (ε t : ℝ) :
    traceHamiltonian ε t = completeHamiltonian (3 / 8) 1 2 1 t
      (deriv (fun _ : ℝ => tracePotential ε (3 / 8) 1 1 t) (1 / 4))
      (deriv (fun f => tracePotential ε f 1 1 t) (3 / 8))
      (deriv (fun b => tracePotential ε (3 / 8) b 1 t) 1)
      (deriv (fun r => tracePotential ε (3 / 8) 1 r t) 1)
      (deriv (fun v => tracePotential ε (3 / 8) 1 1 v) t) := by
  rw [deriv_const, (tracePotential_hasDerivAt_f ε t).deriv,
    (tracePotential_hasDerivAt_b ε t).deriv, (tracePotential_hasDerivAt_r ε t).deriv,
    (tracePotential_hasDerivAt_v ε t).deriv]
  rfl

private theorem traceHamiltonian_eq (ε t : ℝ) :
    traceHamiltonian ε t =
      pointPartialF ε t + (8 / 3) * t * pointPartialR ε t -
        (8 / 3) * t * pointPartialV ε t - (2 / 3) * (pointPartialV ε t) ^ 2 +
        2 * (-2 * pointPartialB t + pointPartialV ε t - t - 1 / 2) + 3 / 2 := by
  unfold traceHamiltonian completeHamiltonian
  ring

private theorem traceHamiltonian_zero (ε : ℝ) : traceHamiltonian ε 0 = 0 := by
  norm_num [traceHamiltonian, completeHamiltonian, pointPartialF, pointPartialB,
    pointPartialR, pointPartialV]

private theorem pointPartialF_hasDerivAt (ε : ℝ) :
    HasDerivAt (pointPartialF ε) 0 0 := by
  have hid := hasDerivAt_id (0 : ℝ)
  have h := (((hid.pow 2).const_mul ε).div ((hid.pow 2).const_add 1)
    (by norm_num)).const_add 3
  convert h using 1
  · funext t
    simp only [pointPartialF, Pi.div_apply, Pi.pow_apply, id_eq]
  · norm_num [Pi.pow_apply, id_eq]

private theorem pointPartialB_hasDerivAt : HasDerivAt pointPartialB (3 / 4) 0 := by
  convert ((hasDerivAt_id (0 : ℝ)).const_mul (3 / 4 : ℝ)).const_add
    (5 / 4 : ℝ) using 1
  · rfl
  · norm_num

private theorem pointPartialR_hasDerivAt (ε : ℝ) :
    HasDerivAt (pointPartialR ε) (3 / 2) 0 := by
  have hid := hasDerivAt_id (0 : ℝ)
  have hrat := ((hid.pow 4).const_mul (3 * ε / 4)).div
    (((hid.pow 2).const_add 1).pow 2) (by norm_num)
  have h := (((hid.const_mul (3 / 2 : ℝ)).const_add (2 * traceValue)).add hrat)
  convert h using 1
  · funext t
    simp only [pointPartialR, Pi.add_apply, Pi.div_apply, Pi.pow_apply, id_eq]
  · norm_num [id_eq]

private theorem pointPartialV_hasDerivAt (ε : ℝ) :
    HasDerivAt (pointPartialV ε) (3 * ε / 4) 0 := by
  have hid := hasDerivAt_id (0 : ℝ)
  have h := ((hid.const_mul (3 * ε / 4)).div
    (((hid.pow 2).const_add 1).pow 2) (by norm_num)).const_add (3 / 2 : ℝ)
  convert h using 1
  · funext t
    simp only [pointPartialV, Pi.div_apply, Pi.pow_apply, id_eq]
  · norm_num [id_eq]

/-- The angular parameter cancels in the first derivative of the complete Hamiltonian. -/
private theorem traceHamiltonian_hasDerivAt (ε : ℝ) :
    HasDerivAt (traceHamiltonian ε) (6 * Real.log (3 / 8) - 37 / 9) 0 := by
  have hid := hasDerivAt_id (0 : ℝ)
  have hF := pointPartialF_hasDerivAt ε
  have hB := pointPartialB_hasDerivAt
  have hR := pointPartialR_hasDerivAt ε
  have hV := pointPartialV_hasDerivAt ε
  have hbase := ((hF.add ((hid.const_mul (8 / 3 : ℝ)).mul hR)).sub
    ((hid.const_mul (8 / 3 : ℝ)).mul hV)).sub ((hV.pow 2).const_mul (2 / 3 : ℝ))
  have hcurv := ((((hB.const_mul (-2)).add hV).sub hid).sub_const (1 / 2 : ℝ)).const_mul 2
  convert (hbase.add hcurv).add_const (3 / 2 : ℝ) using 1
  · funext t
    exact traceHamiltonian_eq ε t
  · norm_num [pointPartialF, pointPartialB, pointPartialR, pointPartialV, traceValue]
    ring

private theorem traceHamiltonian_derivative_neg :
    6 * Real.log (3 / 8 : ℝ) - 37 / 9 < 0 := by
  have hlog : Real.log (3 / 8 : ℝ) < 0 := Real.log_neg (by norm_num) (by norm_num)
  linarith

/-- Every member of this specific produced family fails complete Hamiltonian positivity. -/
private theorem exists_negative_traceHamiltonian (ε : ℝ) :
    ∃ t : ℝ, 0 < t ∧ traceHamiltonian ε t < 0 := by
  have hs : ∀ᶠ t in 𝓝[>] (0 : ℝ), t⁻¹ * traceHamiltonian ε t < 0 := by
    simpa only [zero_add, traceHamiltonian_zero, sub_zero, smul_eq_mul] using
      ((traceHamiltonian_hasDerivAt ε).tendsto_slope_zero_right.eventually
        (Iio_mem_nhds traceHamiltonian_derivative_neg) :
        ∀ᶠ t in 𝓝[>] (0 : ℝ),
          t⁻¹ • (traceHamiltonian ε (0 + t) - traceHamiltonian ε 0) < 0)
  have ht : ∀ᶠ t in 𝓝[>] (0 : ℝ), 0 < t := eventually_mem_nhdsWithin
  obtain ⟨t, ht, hs⟩ := (ht.and hs).exists
  refine ⟨t, ht, lt_of_not_ge ?_⟩
  intro hn
  exact (not_lt_of_ge (mul_nonneg (inv_nonneg.mpr ht.le) hn)) hs

private def traceProbe (t x : ℝ) : ℝ := 1 + (8 * t / 3) * (x - 1 / 4)

private theorem traceProbe_hasDerivAt (t x : ℝ) :
    HasDerivAt (traceProbe t) (8 * t / 3) x := by
  convert (((hasDerivAt_id x).sub_const (1 / 4 : ℝ)).const_mul
    (8 * t / 3)).const_add 1 using 1
  · rfl
  · norm_num

private theorem traceProbe_deriv (t : ℝ) :
    deriv (traceProbe t) = fun _ => 8 * t / 3 := by
  funext x
  exact (traceProbe_hasDerivAt t x).deriv

private theorem round_state_and_probe (t : ℝ) :
    (1 / 4 : ℝ) ∈ Ioo (0 : ℝ) 1 ∧
    warp (fun _ => 2) (1 / 4) = 3 / 8 ∧
    warpSlope (fun _ => 2) (1 / 4) = 1 ∧
    traceProbe t (1 / 4) = 1 ∧
    deriv (traceProbe t) (1 / 4) = 8 * t / 3 ∧
    deriv (deriv (traceProbe t)) (1 / 4) = 0 ∧
    warp (fun _ => 2) (1 / 4) * deriv (traceProbe t) (1 / 4) = t := by
  rw [traceProbe_deriv]
  norm_num [warp_two, warpSlope_two, traceProbe]

private theorem round_moments_and_box (C : ℝ) (hC : 1 ≤ C) :
    (∫ _ in (0 : ℝ)..1, (2 : ℝ)) = 2 ∧
    (∫ x in (0 : ℝ)..1, x * (2 : ℝ)) = 1 ∧
    (∀ _ ∈ Icc (0 : ℝ) 1, (2 : ℝ) ≤ 2 ∧ (2 : ℝ) ≤ 2) ∧ (2 : ℝ) ≤ C * 2 := by
  constructor
  · norm_num
  constructor
  · rw [intervalIntegral.integral_mul_const]
    norm_num [integral_id]
  constructor
  · intro _ _
    exact ⟨le_rfl, le_rfl⟩
  · linarith

/-- The negative value occurs at an actual round interior state with an actual probe jet. -/
private theorem exists_negative_traceHamiltonian_at_round_state (ε : ℝ) :
    ∃ t : ℝ, 0 < t ∧
      completeHamiltonian (warp (fun _ => 2) (1 / 4))
        (warpSlope (fun _ => 2) (1 / 4)) 2 (traceProbe t (1 / 4))
        (warp (fun _ => 2) (1 / 4) * deriv (traceProbe t) (1 / 4)) 0
        (pointPartialF ε t) (pointPartialB t) (pointPartialR ε t) (pointPartialV ε t) < 0 := by
  obtain ⟨t, ht, hneg⟩ := exists_negative_traceHamiltonian ε
  refine ⟨t, ht, ?_⟩
  rcases round_state_and_probe t with ⟨hx, hf, hb, hr, hr1, hr2, hv⟩
  rw [hv, hf, hb, hr]
  exact hneg

end RicciFlowSharpEstimate.Geometry.AreaProfile
