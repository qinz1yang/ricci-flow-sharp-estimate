/-
Copyright (c) 2026 Ziyang Qin. All rights reserved.
No license is granted by this file.
Authors: Ziyang Qin
-/
import RicciFlowSharpEstimate.Geometry.WeakProbeBoundedPolarStates
import RicciFlowSharpEstimate.Geometry.WeakProbeContinuation
import RicciFlowSharpEstimate.Analysis.SingularFluxUniqueness
import RicciFlowSharpEstimate.Analysis.AbsolutelyContinuousReflection

/-! # Singular boundary uniqueness for the actual signed minimum -/

noncomputable section
namespace RicciFlowSharpEstimate.Geometry.AreaProfile
open Set MeasureTheory Filter Topology
local notation "areaμ" => volume.restrict (Ioo (0 : ℝ) 1)

private theorem polar_source_bound {x f b K r p q lam m : ℝ}
    (hx : 0 < x) (hx1 : x ≤ 1) (hm : 0 ≤ m)
    (hf : 0 ≤ f) (hfm : f ≤ m * x) (hb : |b| ≤ 2) (hK : |K| ≤ m) :
    |f * K * q + K * b * f * p / 2 - (K ^ 2 * f - K * b ^ 2 / 2) * r +
      lam * f * r| ≤
      (3 * m ^ 2 + m ^ 3 + 3 * m + |lam| * m + 1) * x *
        (|q| + |p| + |r| / x) := by
  let v := |r| / x
  let E := |q| + |p| + v
  have hv : 0 ≤ v := div_nonneg (abs_nonneg _) hx.le
  have hrv : |r| ≤ v := by
    change |r| ≤ |r| / x
    exact (le_div_iff₀ hx).mpr (mul_le_of_le_one_right (abs_nonneg _) hx1)
  have hrEq : |r| = x * v := by dsimp only [v]; field_simp
  have hqE : |q| ≤ E := by dsimp only [E]; linarith [abs_nonneg p]
  have hpE : |p| ≤ E := by dsimp only [E]; linarith [abs_nonneg q]
  have hvE : v ≤ E := by dsimp only [E]; linarith [abs_nonneg q, abs_nonneg p]
  have hE : 0 ≤ E := hv.trans hvE
  have h1 : |f * K * q| ≤ m ^ 2 * x * E := by
    rw [abs_mul, abs_mul, abs_of_nonneg hf]
    calc
      f * |K| * |q| ≤ (m * x) * m * E := by gcongr
      _ = m ^ 2 * x * E := by ring
  have h2 : |K * b * f * p / 2| ≤ m ^ 2 * x * E := by
    rw [abs_div, abs_mul, abs_mul, abs_mul, abs_of_nonneg hf]
    norm_num
    calc
      |K| * |b| * f * |p| / 2 ≤ m * 2 * (m * x) * E / 2 := by gcongr
      _ = m ^ 2 * x * E := by ring
  have h3 : |K ^ 2 * f * r| ≤ m ^ 3 * x * E := by
    rw [abs_mul, abs_mul, abs_pow, abs_of_nonneg hf]
    calc
      |K| ^ 2 * f * |r| ≤ m ^ 2 * (m * x) * E := by
        gcongr
        exact hrv.trans hvE
      _ = m ^ 3 * x * E := by ring
  have h4 : |K * b ^ 2 * r / 2| ≤ 2 * m * x * E := by
    rw [abs_div, abs_mul, abs_mul, abs_pow, hrEq]
    norm_num
    have hb2 : b ^ 2 ≤ (2 : ℝ) ^ 2 := by
      simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg b) hb 2
    calc
      |K| * b ^ 2 * (x * v) / 2 ≤ m * 2 ^ 2 * (x * E) / 2 := by gcongr
      _ = 2 * m * x * E := by ring
  have h5 : |lam * f * r| ≤ |lam| * m * x * E := by
    rw [abs_mul, abs_mul, abs_of_nonneg hf]
    calc
      |lam| * f * |r| ≤ |lam| * (m * x) * E := by
        gcongr
        exact hrv.trans hvE
      _ = |lam| * m * x * E := by ring
  have heq : f * K * q + K * b * f * p / 2 - (K ^ 2 * f - K * b ^ 2 / 2) * r +
      lam * f * r = (f * K * q + K * b * f * p / 2 - K ^ 2 * f * r) +
        K * b ^ 2 * r / 2 + lam * f * r := by ring
  rw [heq]
  calc
    _ ≤ |f * K * q| + |K * b * f * p / 2| + |K ^ 2 * f * r| +
        |K * b ^ 2 * r / 2| + |lam * f * r| := by
      have h12 := abs_add_le (f * K * q) (K * b * f * p / 2)
      have h123 := (abs_sub (f * K * q + K * b * f * p / 2)
        (K ^ 2 * f * r)).trans (add_le_add h12 le_rfl)
      have h1234 := (abs_add_le (f * K * q + K * b * f * p / 2 - K ^ 2 * f * r)
        (K * b ^ 2 * r / 2)).trans (add_le_add h123 le_rfl)
      exact (abs_add_le _ _).trans (add_le_add h1234 le_rfl)
    _ ≤ m ^ 2 * x * E + m ^ 2 * x * E + m ^ 3 * x * E +
        2 * m * x * E + |lam| * m * x * E :=
      add_le_add (add_le_add (add_le_add (add_le_add h1 h2) h3) h4) h5
    _ ≤ (3 * m ^ 2 + m ^ 3 + 3 * m + |lam| * m + 1) * x * E := by
      have hh : 0 ≤ (m ^ 2 + m + 1) * x * E := by positivity
      nlinarith only [hh]

private theorem polar_q_derivative_bound {x f b K r P lo m : ℝ}
    (hx : 0 < x) (hlo : 0 < lo) (hm : 0 ≤ m)
    (hfl : lo * x ≤ f) (hb : |b| ≤ 2) (hK : |K| ≤ m) :
    |(P - K * b * f * r / 2) / f ^ 2| ≤
      (1 / lo ^ 2 + m / lo) * (|P| / x ^ 2 + |r| / x) := by
  have hf : 0 < f := (mul_pos hlo hx).trans_le hfl
  have hc : |K * b * f * r / 2| ≤ m * f * |r| := by
    rw [abs_div, abs_mul, abs_mul, abs_mul, abs_of_pos hf]
    norm_num
    calc
      |K| * |b| * f * |r| / 2 ≤ m * 2 * f * |r| / 2 := by gcongr
      _ = m * f * |r| := by ring
  have hP : |P| / f ^ 2 ≤ (1 / lo ^ 2) * (|P| / x ^ 2) := by
    calc
      |P| / f ^ 2 ≤ |P| / (lo * x) ^ 2 := by gcongr
      _ = (1 / lo ^ 2) * (|P| / x ^ 2) := by field_simp
  have hr : m * |r| / f ≤ (m / lo) * (|r| / x) := by
    calc
      m * |r| / f ≤ m * |r| / (lo * x) := by gcongr
      _ = (m / lo) * (|r| / x) := by ring
  rw [abs_div, abs_of_pos (sq_pos_of_pos hf)]
  calc
    |P - K * b * f * r / 2| / f ^ 2 ≤ (|P| + m * f * |r|) / f ^ 2 :=
      div_le_div_of_nonneg_right ((abs_sub _ _).trans
        (add_le_add le_rfl hc)) (sq_nonneg f)
    _ = |P| / f ^ 2 + m * |r| / f := by field_simp
    _ ≤ (1 / lo ^ 2) * (|P| / x ^ 2) + (m / lo) * (|r| / x) := add_le_add hP hr
    _ ≤ (1 / lo ^ 2 + m / lo) * (|P| / x ^ 2 + |r| / x) := by
      have h1 : 0 ≤ (1 / lo ^ 2) * (|r| / x) := by positivity
      have h2 : 0 ≤ (m / lo) * (|P| / x ^ 2) := by positivity
      nlinarith only [h1, h2]

private theorem polar_derivative_flux_bound {x f K r q m lam : ℝ}
    (hx : 0 < x) (hm : 0 ≤ m) (hf : 0 ≤ f) (hfm : f ≤ m * x) (hK : |K| ≤ m) :
    |f * (q + K * r)| ≤ (3 * m ^ 2 + m ^ 3 + 3 * m + |lam| * m + 1) *
      x * (|q| + |r|) := by
  have he : 0 ≤ |q| + |r| := add_nonneg (abs_nonneg _) (abs_nonneg _)
  have hKr : |K * r| ≤ m * |r| := by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_right hK (abs_nonneg _)
  have hh : |q + K * r| ≤ |q| + m * |r| := by
    exact (abs_add_le _ _).trans (add_le_add le_rfl hKr)
  rw [abs_mul, abs_of_nonneg hf]
  calc
    f * |q + K * r| ≤ (m * x) * (|q| + m * |r|) :=
      mul_le_mul hfm hh (abs_nonneg _) (mul_nonneg hm hx.le)
    _ ≤ (m + m ^ 2) * x * (|q| + |r|) := by
      nlinarith only [mul_nonneg (mul_nonneg hm hx.le) (abs_nonneg r),
        mul_nonneg (mul_nonneg (sq_nonneg m) hx.le) (abs_nonneg q)]
    _ ≤ (3 * m ^ 2 + m ^ 3 + 3 * m + |lam| * m + 1) * x * (|q| + |r|) := by
      apply mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right ?_ hx.le) he
      nlinarith [pow_nonneg hm 3, mul_nonneg (abs_nonneg lam) hm]

private theorem zero_interval_of_signed_polar_system
    {f b K R p q P F : ℝ → ℝ} {lo m lam : ℝ}
    (hlo : 0 < lo) (hm : 0 ≤ m)
    (hcoef : ∀ x ∈ Ioo (0 : ℝ) (1 / 2),
      lo * x ≤ f x ∧ f x ≤ m * x ∧ |b x| ≤ 2)
    (hK : ∀ᵐ x ∂volume.restrict (Ioo (0 : ℝ) (1 / 2)), |K x| ≤ m)
    (hR : AbsolutelyContinuousOnInterval R 0 (1 / 2)) (hR0 : R 0 = 0)
    (hp : ContinuousOn p (Ioo (0 : ℝ) (1 / 2)))
    (hRD : ∀ x ∈ Ioo (0 : ℝ) (1 / 2), HasDerivAt R (p x) x)
    (hqlocal : ∀ a ∈ Ioo (0 : ℝ) (1 / 2), ∀ c ∈ Ioo (0 : ℝ) (1 / 2),
      AbsolutelyContinuousOnInterval q a c)
    (hq0 : Tendsto q (𝓝[>] (0 : ℝ)) (𝓝 0))
    (hP : AbsolutelyContinuousOnInterval P 0 (1 / 2)) (hP0 : P 0 = 0)
    (hF : AbsolutelyContinuousOnInterval F 0 (1 / 2)) (hF0 : F 0 = 0)
    (hbound : ∃ N : ℝ, 0 ≤ N ∧ ∀ x ∈ Ioo (0 : ℝ) (1 / 2), |p x| ≤ N ∧ |q x| ≤ N)
    (hSys : ∀ᵐ x ∂volume.restrict (Ioo (0 : ℝ) (1 / 2)),
      HasDerivAt q ((P x - K x * b x * f x * R x / 2) / f x ^ 2) x ∧
      HasDerivAt P (f x * K x * q x + K x * b x * f x * p x / 2 -
        (K x ^ 2 * f x - K x * b x ^ 2 / 2) * R x + lam * f x * R x) x ∧
      HasDerivAt F (f x * (q x + K x * R x)) x)
    (hFP : ∀ x ∈ Ioo (0 : ℝ) (1 / 2), F x = f x ^ 2 * p x) :
    ∃ δ : ℝ, 0 < δ ∧ δ < 1 / 2 ∧
      ∀ x ∈ Ioo (0 : ℝ) δ, R x = 0 ∧ p x = 0 ∧ q x = 0 ∧ P x = 0 := by
  let A := 3 * m ^ 2 + m ^ 3 + 3 * m + |lam| * m + 1
  let B := 1 / lo ^ 2 + m / lo
  let D := 1 / lo ^ 2
  have hA : 0 ≤ A := by dsimp only [A]; positivity
  have hB : 0 ≤ B := by dsimp only [B]; positivity
  have hD : 0 ≤ D := by dsimp only [D]; positivity
  apply Analysis.exists_zero_interval_of_singular_flux_bounds
    (by norm_num : (0 : ℝ) < 1 / 2) hA hB hD hR hR0 hp
    (by filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx; exact hRD x hx)
    hqlocal hq0 hP hP0 hF hF0 hbound
  · filter_upwards [hSys, hK, ae_restrict_mem measurableSet_Ioo] with x hS hKx hx
    rw [hS.2.1.deriv]
    have hc := hcoef x hx
    exact polar_source_bound hx.1 (by linarith [hx.2]) hm
      ((mul_pos hlo hx.1).trans_le hc.1).le hc.2.1 hc.2.2 hKx
  · filter_upwards [hSys, hK, ae_restrict_mem measurableSet_Ioo] with x hS hKx hx
    rw [hS.1.deriv]
    have hc := hcoef x hx
    exact polar_q_derivative_bound hx.1 hlo hm hc.1 hc.2.2 hKx
  · filter_upwards [hSys, hK, ae_restrict_mem measurableSet_Ioo] with x hS hKx hx
    rw [hS.2.2.deriv]
    have hc := hcoef x hx
    exact polar_derivative_flux_bound (lam := lam) hx.1 hm
      ((mul_pos hlo hx.1).trans_le hc.1).le hc.2.1 hKx
  · intro x hx
    have hc := hcoef x hx
    have hf : 0 < f x := (mul_pos hlo hx.1).trans_le hc.1
    calc
      |p x| = |F x| / f x ^ 2 := by
        rw [hFP x hx, abs_mul, abs_pow, abs_of_pos hf]
        field_simp
      _ ≤ |F x| / (lo * x) ^ 2 :=
        div_le_div_of_nonneg_left (abs_nonneg _) (sq_pos_of_pos (mul_pos hlo hx.1))
          (pow_le_pow_left₀ (mul_nonneg hlo.le hx.1.le) hc.1 2)
      _ = D * |F x| / x ^ 2 := by dsimp only [D]; field_simp

private theorem reflect_right_zero :
    Tendsto (fun x : ℝ => 1 - x) (𝓝[>] 0) (𝓝[<] 1) := by
  apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
  · simpa only [sub_zero] using
      (tendsto_const_nhds.sub (tendsto_id.mono_left nhdsWithin_le_nhds) :
        Tendsto (fun x : ℝ => 1 - x) (𝓝[>] 0) (𝓝 (1 - 0)))
  · filter_upwards [self_mem_nhdsWithin] with x hx
    change 0 < x at hx
    change 1 - x < 1
    linarith

/-- The actual minimizing probe and canonical operator cannot both have zero
trace at either physical pole. This is singular boundary uniqueness, without
source orientation, a curvature trace or a polar nondegeneracy premise. -/
theorem IsRecoverableAreaCompetitor.probe_pole_state_nonzero_of_minimum
    {C : ℝ} {K r p z : ℝ → ℝ} (hC : 1 ≤ C)
    (h : IsRecoverableAreaCompetitor C K r p z)
    (hr : ContinuousOn r (Ioo (0 : ℝ) 1))
    (hp : ContinuousOn p (Ioo (0 : ℝ) 1))
    (hmin : ∀ K' r' p' z' : ℝ → ℝ, IsRecoverableAreaCompetitor C K' r' p' z' →
      weakMeridionalAction K r p z ≤ weakMeridionalAction K' r' p' z') :
    let q := fun x => weakProbeEulerMomentum K r p z (weakMeridionalAction K r p z) x /
      warp K x ^ 2
    (Tendsto r (𝓝[>] (0 : ℝ)) (𝓝 0) → ¬ Tendsto q (𝓝[>] (0 : ℝ)) (𝓝 0)) ∧
      (Tendsto r (𝓝[<] (1 : ℝ)) (𝓝 0) → ¬ Tendsto q (𝓝[<] (1 : ℝ)) (𝓝 0)) := by
  let lam := weakMeridionalAction K r p z
  let f := warp K
  let b := warpSlope K
  let q := fun x => weakProbeEulerMomentum K r p z lam x / f x ^ 2
  let P := weakProbeEulerFlux K r p z lam
  let F := weakProbeDerivativeFlux K p
  let R := fun x => r (1 / 2) + ∫ s in (1 / 2 : ℝ)..x, p s
  have hC0 : 0 < C := zero_lt_one.trans_le hC
  have hg := h.geometry_bounds hC
  obtain ⟨_, _, hRAC, hReq, hRD, hRL, hRR, _⟩ :=
    h.probe_pole_integrability_of_minimum hC hr hp hmin
  obtain ⟨_, _, _, hQeq, hlocal, hSys⟩ :=
    h.probe_first_order_system_of_minimum hC hr hp hmin
  obtain ⟨_, hPAC, _, hP0, hP1, _, _, _, _, _, _⟩ :=
    h.probe_euler_flux_of_minimum hC hmin
  obtain ⟨hFAC, hF0, hF1, hFD⟩ := h.derivative_flux_absolutelyContinuous hC hp
  obtain ⟨_, _, N, hN, _, _, hNb⟩ := h.probe_bounded_polar_states_of_minimum hC hr hp hmin
  have hstate := h.probe_state_ne_zero_of_minimum hC hr hp hmin
  have hsub : Ioo (0 : ℝ) (1 / 2) ⊆ Ioo (0 : ℝ) 1 :=
    fun _ hx => ⟨hx.1, by linarith [hx.2]⟩
  have hACsub : uIcc (0 : ℝ) (1 / 2) ⊆ uIcc (0 : ℝ) 1 := by
    norm_num [uIcc_of_le]
    exact Icc_subset_Icc le_rfl (by norm_num)
  have hK : ∀ᵐ x ∂areaμ, |K x| ≤ 2 * C := by
    filter_upwards [hg.2.2.2.2] with x hx
    rw [abs_of_nonneg ((by positivity : (0 : ℝ) ≤ 2 / C).trans hx.1)]
    exact hx.2
  have hcoef (x v w : ℝ) (hx : x ∈ Ioo (0 : ℝ) (1 / 2))
      (hl : (2 / C) * x * (1 - x) ≤ v)
      (hu : v ≤ (2 * C) * x * (1 - x)) (hw : |w| ≤ 2) :
      (1 / C) * x ≤ v ∧ v ≤ (2 * C) * x ∧ |w| ≤ 2 := by
    refine ⟨?_, ?_, hw⟩
    · calc
        (1 / C) * x = (2 / C) * x * (1 / 2) := by ring
        _ ≤ (2 / C) * x * (1 - x) :=
          mul_le_mul_of_nonneg_left (by linarith [hx.2])
            (mul_nonneg (div_nonneg (by norm_num) hC0.le) hx.1.le)
        _ ≤ v := hl
    · exact hu.trans (mul_le_of_le_one_right (mul_nonneg (by positivity) hx.1.le)
        (by linarith [hx.1]))
  have hcoefL (x : ℝ) (hx : x ∈ Ioo (0 : ℝ) (1 / 2)) :
      (1 / C) * x ≤ f x ∧ f x ≤ (2 * C) * x ∧ |b x| ≤ 2 := by
    have hh := hg.2.2.1 x ⟨hx.1.le, (hsub hx).2.le⟩
    exact hcoef x (f x) (b x) hx hh.1 hh.2.1 hh.2.2
  have hSysL : ∀ᵐ x ∂volume.restrict (Ioo (0 : ℝ) (1 / 2)),
      HasDerivAt q ((P x - K x * b x * f x * R x / 2) / f x ^ 2) x ∧
      HasDerivAt P (f x * K x * q x + K x * b x * f x * p x / 2 -
        (K x ^ 2 * f x - K x * b x ^ 2 / 2) * R x + lam * f x * R x) x ∧
      HasDerivAt F (f x * (q x + K x * R x)) x := by
    filter_upwards [(ae_imp_of_ae_restrict hSys).filter_mono
      (ae_mono Measure.restrict_le_self),
      (ae_imp_of_ae_restrict hFD).filter_mono (ae_mono Measure.restrict_le_self),
      (ae_imp_of_ae_restrict hQeq).filter_mono (ae_mono Measure.restrict_le_self),
      ae_restrict_mem measurableSet_Ioo] with x hs hd he hx
    have hi := hsub hx
    have hrx := hReq hi
    change R x = r x at hrx
    refine ⟨?_, ?_, ?_⟩
    · simpa only [hrx] using (hs hi).2.1
    · simpa only [hrx] using (hs hi).2.2
    · simpa only [hrx, he hi] using hd hi
  constructor
  · intro hr0 hq0
    have hR0 : R 0 = 0 := tendsto_nhds_unique hRL hr0
    obtain ⟨δ, hδ, hδh, hz⟩ := zero_interval_of_signed_polar_system
      (by positivity : 0 < 1 / C) (by positivity : 0 ≤ 2 * C) hcoefL
      (hK.filter_mono (ae_mono (Measure.restrict_mono hsub le_rfl)))
      (hRAC.mono hACsub) hR0 (hp.mono hsub)
      (fun x hx => hRD x (hsub hx))
      (fun a ha c hc => (hlocal a (hsub ha) c (hsub hc)).2)
      hq0 (hPAC.mono hACsub) hP0 (hFAC.mono hACsub) hF0
      ⟨N, hN, fun x hx => hNb x (hsub hx)⟩ hSysL (fun _ _ => rfl)
    have hx : δ / 2 ∈ Ioo (0 : ℝ) δ := by constructor <;> linarith
    have hxI : δ / 2 ∈ Ioo (0 : ℝ) 1 := by constructor <;> linarith
    have hh := hz (δ / 2) hx
    have hrx : r (δ / 2) = 0 := by rw [← hReq hxI]; exact hh.1
    exact (hstate (δ / 2) hxI).elim (fun hn => hn hrx) (fun hh' =>
      hh'.elim (fun hn => hn hh.2.1) (fun hh'' =>
        hh''.elim (fun hn => hn hh.2.2.1) (fun hn => hn hh.2.2.2)))
  · intro hr1 hq1
    let fR := fun x => f (1 - x)
    let bR := fun x => -b (1 - x)
    let KR := fun x => K (1 - x)
    let RR := fun x => R (1 - x)
    let pR := fun x => -p (1 - x)
    let qR := fun x => q (1 - x)
    let PR := fun x => -P (1 - x)
    let FR := fun x => -F (1 - x)
    have href (x : ℝ) (hx : x ∈ Ioo (0 : ℝ) (1 / 2)) :
        1 - x ∈ Ioo (0 : ℝ) 1 := ⟨by linarith [hx.2], by linarith [hx.1]⟩
    have hR1 : R 1 = 0 := tendsto_nhds_unique hRR hr1
    have hRRAC : AbsolutelyContinuousOnInterval RR 0 1 := by
      simpa only [sub_zero, sub_self] using
        Analysis.absolutelyContinuousOnInterval_comp_sub_left (c := 1) hRAC
    have hPRAC : AbsolutelyContinuousOnInterval PR 0 1 := by
      simpa only [sub_zero, sub_self, PR, P, lam] using
        (Analysis.absolutelyContinuousOnInterval_comp_sub_left (c := 1) hPAC).fun_neg
    have hFRAC : AbsolutelyContinuousOnInterval FR 0 1 := by
      simpa only [sub_zero, sub_self, FR, F] using
        (Analysis.absolutelyContinuousOnInterval_comp_sub_left (c := 1) hFAC).fun_neg
    have hcoefR (x : ℝ) (hx : x ∈ Ioo (0 : ℝ) (1 / 2)) :
        (1 / C) * x ≤ fR x ∧ fR x ≤ (2 * C) * x ∧ |bR x| ≤ 2 := by
      have hh := hg.2.2.1 (1 - x) ⟨(href x hx).1.le, (href x hx).2.le⟩
      apply hcoef x (fR x) (bR x) hx
      · convert hh.1 using 1
        ring
      · convert hh.2.1 using 1
        ring
      · simpa only [bR, abs_neg] using hh.2.2
    have hKR : ∀ᵐ x ∂volume.restrict (Ioo (0 : ℝ) (1 / 2)), |KR x| ≤ 2 * C := by
      have hh := (volume.measurePreserving_sub_left 1).quasiMeasurePreserving.ae
        (ae_imp_of_ae_restrict hK)
      filter_upwards [hh.filter_mono (ae_mono Measure.restrict_le_self),
        ae_restrict_mem measurableSet_Ioo] with x hx hxI
      exact hx (href x hxI)
    have hpRC : ContinuousOn pR (Ioo (0 : ℝ) (1 / 2)) :=
      (hp.comp (continuous_const.sub continuous_id).continuousOn href).neg
    have hRRD (x : ℝ) (hx : x ∈ Ioo (0 : ℝ) (1 / 2)) : HasDerivAt RR (pR x) x := by
      simpa only [RR, pR, Function.comp_def, zero_sub, mul_neg_one, id_eq] using
        (hRD (1 - x) (href x hx)).comp x
          ((hasDerivAt_const x (1 : ℝ)).fun_sub (hasDerivAt_id x))
    have hqRlocal (a : ℝ) (ha : a ∈ Ioo (0 : ℝ) (1 / 2))
        (c : ℝ) (hc : c ∈ Ioo (0 : ℝ) (1 / 2)) :
        AbsolutelyContinuousOnInterval qR a c := by
      simpa only [sub_sub_cancel] using
        Analysis.absolutelyContinuousOnInterval_comp_sub_left (c := 1)
          (hlocal (1 - c) (href c hc) (1 - a) (href a ha)).2
    have hSysR : ∀ᵐ x ∂volume.restrict (Ioo (0 : ℝ) (1 / 2)),
        HasDerivAt qR ((PR x - KR x * bR x * fR x * RR x / 2) / fR x ^ 2) x ∧
        HasDerivAt PR (fR x * KR x * qR x + KR x * bR x * fR x * pR x / 2 -
          (KR x ^ 2 * fR x - KR x * bR x ^ 2 / 2) * RR x + lam * fR x * RR x) x ∧
        HasDerivAt FR (fR x * (qR x + KR x * RR x)) x := by
      have hsR := (volume.measurePreserving_sub_left 1).quasiMeasurePreserving.ae
        (ae_imp_of_ae_restrict hSys)
      have hdR := (volume.measurePreserving_sub_left 1).quasiMeasurePreserving.ae
        (ae_imp_of_ae_restrict hFD)
      have heR := (volume.measurePreserving_sub_left 1).quasiMeasurePreserving.ae
        (ae_imp_of_ae_restrict hQeq)
      filter_upwards [hsR.filter_mono (ae_mono Measure.restrict_le_self),
        hdR.filter_mono (ae_mono Measure.restrict_le_self),
        heR.filter_mono (ae_mono Measure.restrict_le_self),
        ae_restrict_mem measurableSet_Ioo] with x hs hd he hx
      have hy := href x hx
      have hRd := (hasDerivAt_const x (1 : ℝ)).fun_sub (hasDerivAt_id x)
      have hrx := hReq hy
      change R (1 - x) = r (1 - x) at hrx
      refine ⟨?_, ?_, ?_⟩
      · have hdq := (hs hy).2.1.comp x hRd
        change HasDerivAt qR _ x at hdq
        apply hdq.congr_deriv
        dsimp only [PR, KR, bR, fR, RR, P, q, f, b, lam]
        rw [hrx]
        ring
      · have hdp := ((hs hy).2.2.comp x hRd).neg
        change HasDerivAt PR _ x at hdp
        apply hdp.congr_deriv
        dsimp only [PR, KR, bR, fR, RR, pR, P, qR, q, f, b, lam]
        rw [hrx]
        ring
      · have hdf := ((hd hy).comp x hRd).neg
        change HasDerivAt FR _ x at hdf
        apply hdf.congr_deriv
        dsimp only [fR, qR, KR, RR, q, f, lam]
        rw [hrx, he hy]
        ring
    obtain ⟨δ, hδ, hδh, hz⟩ := zero_interval_of_signed_polar_system
      (by positivity : 0 < 1 / C) (by positivity : 0 ≤ 2 * C) hcoefR hKR
      (hRRAC.mono hACsub) (by simpa only [RR, sub_zero] using hR1)
      hpRC hRRD hqRlocal (hq1.comp reflect_right_zero)
      (hPRAC.mono hACsub) (by simp only [PR, P, lam, sub_zero, hP1, neg_zero])
      (hFRAC.mono hACsub) (by simp only [FR, F, sub_zero, hF1, neg_zero])
      ⟨N, hN, fun x hx => by simpa only [pR, qR, abs_neg] using hNb (1 - x) (href x hx)⟩
      hSysR (fun x hx => by dsimp only [FR, fR, pR, F, weakProbeDerivativeFlux]; ring)
    have hx : δ / 2 ∈ Ioo (0 : ℝ) δ := by constructor <;> linarith
    have hxH : δ / 2 ∈ Ioo (0 : ℝ) (1 / 2) := by constructor <;> linarith
    have hy := href (δ / 2) hxH
    have hh := hz (δ / 2) hx
    have hrx : r (1 - δ / 2) = 0 := by rw [← hReq hy]; exact hh.1
    have hpx : p (1 - δ / 2) = 0 := neg_eq_zero.mp hh.2.1
    have hPx : P (1 - δ / 2) = 0 := neg_eq_zero.mp hh.2.2.2
    exact (hstate (1 - δ / 2) hy).elim (fun hn => hn hrx) (fun hh' =>
      hh'.elim (fun hn => hn hpx) (fun hh'' =>
        hh''.elim (fun hn => hn hh.2.2.1) (fun hn => hn hPx)))

end RicciFlowSharpEstimate.Geometry.AreaProfile
