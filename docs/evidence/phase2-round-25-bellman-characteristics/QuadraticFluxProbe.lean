import RicciFlowSharpEstimate.Geometry.WeakProbeFirstOrderSystem
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.Deriv.Comp

noncomputable section

namespace RicciFlowSharpEstimate.Geometry.AreaProfile

private def fullFlux (K r s a c : ℝ → ℝ) (x : ℝ) : ℝ :=
  let f := warp K x
  let v := f * deriv r x
  f * (s x * r x ^ 2 + 2 * a x * r x * v + c x * v ^ 2)

private def fullRemainder (f b K s a c ds da dc r v : ℝ) : ℝ :=
  (2 * a - b * c + f * dc - f * c ^ 2) * v ^ 2 +
    (-K * b + 2 * s + 2 * f * da + 2 * f * c * (K - a)) * r * v +
    (f * (K ^ 2 + 2 * K * a - a ^ 2) + b * s + f * ds - K * b ^ 2 / 2) * r ^ 2

-- The coefficients are actual curves; their derivatives are literal deriv.
-- The following chain rule ties them to a field on the original geometry state.
private theorem geometry_field_hasDerivAt (K : ℝ → ℝ) (hK : Continuous K)
    (S : ℝ × ℝ × ℝ → ℝ) (x : ℝ)
    (hS : DifferentiableAt ℝ S (x, warp K x, warpSlope K x)) :
    HasDerivAt (fun y => S (y, warp K y, warpSlope K y))
      (fderiv ℝ S (x, warp K x, warpSlope K x)
        (1, warpSlope K x, -2 * K x)) x := by
  have hpath := (hasDerivAt_id x).prodMk
    ((warp_hasDerivAt K hK x).prodMk (warpSlope_hasDerivAt K hK x))
  exact hS.hasFDerivAt.comp_hasDerivAt x hpath

private theorem total_derivative_eq_partials
    (S : ℝ × ℝ × ℝ → ℝ) (x f b k : ℝ)
    (hS : DifferentiableAt ℝ S (x, f, b)) :
    fderiv ℝ S (x, f, b) (1, b, -2 * k) =
      deriv (fun y => S (y, f, b)) x + b * deriv (fun y => S (x, y, b)) f -
        2 * k * deriv (fun y => S (x, f, y)) b := by
  have hx := hS.hasFDerivAt.comp_hasDerivAt x
    ((hasDerivAt_id x).prodMk ((hasDerivAt_const x f).prodMk (hasDerivAt_const x b)))
  have hf := hS.hasFDerivAt.comp_hasDerivAt f
    ((hasDerivAt_const f x).prodMk ((hasDerivAt_id f).prodMk (hasDerivAt_const f b)))
  have hb := hS.hasFDerivAt.comp_hasDerivAt b
    ((hasDerivAt_const b x).prodMk ((hasDerivAt_const b f).prodMk (hasDerivAt_id b)))
  simp only [Function.comp_def, id_eq] at hx hf hb
  rw [hx.deriv, hf.deriv, hb.deriv]
  have hv : ((1, b, -2 * k) : ℝ × ℝ × ℝ) =
      (1, (0 : ℝ), (0 : ℝ)) + b • (0, (1 : ℝ), (0 : ℝ)) +
        (-2 * k) • (0, (0 : ℝ), (1 : ℝ)) := by
    ext <;> simp
  rw [hv, map_add, map_add, map_smul, map_smul]
  simp only [smul_eq_mul]
  ring

private theorem full_flux_hasDerivAt (K r s a c : ℝ → ℝ) (x : ℝ)
    (hK : Continuous K) (hr : ContDiff ℝ 2 r)
    (hs : DifferentiableAt ℝ s x) (ha : DifferentiableAt ℝ a x)
    (hc : DifferentiableAt ℝ c x) :
    HasDerivAt (fullFlux K r s a c)
      (warp K x * (meridionalOperator K r x + a x * r x +
          c x * (warp K x * deriv r x)) ^ 2 +
        fullRemainder (warp K x) (warpSlope K x) (K x) (s x) (a x) (c x)
          (deriv s x) (deriv a x) (deriv c x) (r x) (warp K x * deriv r x) -
        meridionalActionDensity (warp K x) (warpSlope K x) (K x)
          (r x) (deriv r x) (deriv (deriv r) x)) x := by
  have hf := warp_hasDerivAt K hK x
  have hp := (hr.differentiable (by norm_num) x).hasDerivAt
  have hrD : ContDiff ℝ 1 (deriv r) := hr.deriv'
  have hz := (hrD.differentiable (by norm_num) x).hasDerivAt
  have hv := hf.mul hz
  have h := hf.mul (((hs.hasDerivAt.mul (hp.pow 2)).add
    ((((ha.hasDerivAt.const_mul 2).mul hp).mul hv))).add
      (hc.hasDerivAt.mul (hv.pow 2)))
  convert h using 1
  · rfl
  · simp only [Pi.mul_apply, Pi.add_apply, Pi.pow_apply]
    unfold fullRemainder meridionalOperator meridionalActionDensity
    ring

private theorem complete_control_square (f b K s a c sx sf sb ax af ab cx cf cb r v q : ℝ)
    (hf : f ≠ 0) :
    f * q ^ 2 - K * b * r * v + (K ^ 2 * f - K * b ^ 2 / 2) * r ^ 2 +
      (b * (s * r ^ 2 + 2 * a * r * v + c * v ^ 2) +
        f * ((sx + b * sf - 2 * K * sb) * r ^ 2 +
          2 * s * r * (v / f) + 2 * (ax + b * af - 2 * K * ab) * r * v +
          2 * a * ((v / f) * v + r * (q - b * (v / f) + K * r)) +
          (cx + b * cf - 2 * K * cb) * v ^ 2 +
          2 * c * v * (q - b * (v / f) + K * r))) =
      f * (q + a * r + c * v) ^ 2 +
        fullRemainder f b K s a c (sx + b * sf - 2 * K * sb)
          (ax + b * af - 2 * K * ab) (cx + b * cf - 2 * K * cb) r v := by
  unfold fullRemainder
  field_simp
  ring

end RicciFlowSharpEstimate.Geometry.AreaProfile
