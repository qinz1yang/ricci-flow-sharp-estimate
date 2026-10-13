# Phase II: the unrestricted rotational threshold

Phase I is **COMPLETE**, accepted after rounds 0–16 at
`2bda267ca0a4bd965411af36b2c89dde4c78f7c7` and finalized at
`721fd81b76a3c841389761fbe55ce917e0926a44`. Its paper and evidence are preserved.
Phase II is **OPEN**. Its goal is to determine `C_rot` for all smooth one-forms
on the original represented rotational metric class, with a determining
characterization, justified selection, a universal lower bound, sharp smooth
counterexamples above it, and the correct endpoint scope. The results below
are variational prerequisites, not a threshold characterization.

## Round 0: complete-action variation

Let `K,r : ℝ → ℝ` be globally smooth, and impose the two normalized moments

\[
 \int_0^1K=2,\qquad \int_0^1xK=1.
\]
Use the **existing** area primitives and full six-entry action:

\[
 f(x)=2x-2\int_0^x(x-t)K(t)\,dt,\qquad
 f_1(x)=2-2\int_0^xK(t)\,dt,
\]
\[
 L_Kr=fr''+2f_1r'-Kr,
\]
\[
 A_K(r)=\int_0^1
 \left[f(L_Kr)^2-Kf_1r(fr'+f_1r/2)+K^2fr^2\right]dx.
\]
The accepted primitive calculus gives `f'=f₁`, `f₁'=-2K`,
`f(0)=f(1)=0`, and `f₁(0)=2`, `f₁(1)=-2`.

The new native factorization is

\[
 A_K(r)=\int_0^1\left[f(L_Kr)^2+\frac12ff_1K'r^2\right]dx. \tag{1}
\]
Indeed, the original density minus the right-hand density is the actual
derivative of `-K f f₁ r²/2`. Its endpoint values vanish because `f` vanishes,
without a condition on either endpoint value or derivative of `r`.
All terms are continuous and integrable. Neither (1) nor the Green identity
below requires positive curvature; positivity enters the normalization and
stationarity converse.

The actual Green flux is

\[
 G_K(r,s)=f^2(r's-rs'),\qquad
 G_K(r,s)'=f(L_Kr)s-fr(L_Ks).
\]
It vanishes at both endpoints for **all** smooth probes. Thus `L_K` is symmetric
for the weighted pairing `∫f r s`. Applying this identity to (1) gives

\[
 E_Kr=L_K(L_Kr)+\frac12f_1K'r,\qquad
 A_K(r)=\int_0^1frE_Kr. \tag{2}
\]
The exact variation, with the actual derivatives of `r+ts`, is

\[
 A_K(r+ts)=A_K(r)+2t\int_0^1fsE_Kr+t^2A_K(s). \tag{3}
\]
Consequently its parameter derivative at zero is `2∫f s E_Kr`.
This retains the full curvature potential; replacing the action by its leading
square alone would lose a term.

For `K>0` on `[0,1]`, the accepted concavity argument gives `f>0` in `(0,1)`.
The new stationarity theorem proves the equivalence

\[
 \left[\frac{d}{dt}\bigg|_{t=0}A_K(r+ts)=0
       \text{ for every globally smooth }s\right]
 \quad\Longleftrightarrow\quad E_Kr=0\text{ on }[0,1]. \tag{4}
\]
For the forward implication, take the legitimate smooth test `s=E_Kr`.
Its weighted-square integral is zero; continuity and positive interior weight
force `E_Kr=0` in the interior and then at the endpoints. This is an equivalence
for a **supplied smooth probe**, not an existence theorem for a nonzero kernel
or a proof that a joint optimizer exists.

Writing `q=L_Kr`, the endpoint values in (4) give

\[
 4q'(0)-K(0)q(0)+K'(0)r(0)=0,\qquad
 -4q'(1)-K(1)q(1)-K'(1)r(1)=0. \tag{5}
\]
These are consequences of the smooth equation. They are not asserted to be a
sufficient boundary-domain description for arbitrary singular solutions of the
fourth-order ODE. The leading coefficient of `E_K` is `f²`, which degenerates
at both poles; that distinction matters for any later spectral or compactness
argument.

If `r` is nonzero somewhere in `(0,1)`, the new positivity theorem gives
`m=∫f r²>0`. The explicit positive rescaling `c=1/√m` satisfies

\[
 \int_0^1f(cr)^2=1,\qquad A_K(cr)=c^2A_K(r). \tag{6}
\]
This establishes a legitimate scalar normalization and preserves action sign
and zero action. It does not manufacture a nonzero critical probe. At this
Round 0 checkpoint, metric-scale normalization and the completed
operator domain were separate obligations. Round 2 below supplies the exhaustive
smooth metric/probe normalization; a completed singular operator domain remains open.

## Original objects and pole scope

The existing `RotationalOneForms` producer permits every globally smooth height
probe, and `RotationalInvariantClassification` supplies globally smooth probes
for every original invariant smooth form. The forms vanish at the poles because
the geometric covectors vanish there; the scalar probes need not vanish.
The accepted smooth area inverse and `AreaGeometricRealization` construct actual
original metric/profile/probe data with the closed-interval coordinate equations
and actual first and second derivative laws. No singular angular coordinate or
independently supplied jets occur in the new packet.

The new `AreaVariationGeometry` consumers explicitly retain the same `D.metric`,
`D.meridionalOneForm`, height primitive, and physical equations

\[
 D.a(V_K(x))=1/K(x),\quad R(V_K(x))=r(x),\quad S(V_K(x))=s(x)
 \qquad(0\leq x\leq1).
\]
They prove the original dissipation version of (2), and

\[
 \frac{d}{dt}\bigg|_{t=0}Q_{g_D}(M_D(R+tS))
   =4\pi\int_0^1fsE_Kr. \tag{7}
\]
The metric is fixed throughout this variation. These are consumers of the
accepted tying equations, whose producer remains available; they do not rename
a scalar action as a geometric object.
The accepted Haar reduction and nonnegative nonzonal remainder remain unchanged.
No new universal positivity claim, extension to all positively curved surfaces,
or exhaustive normalized-area parametrization theorem is asserted by the Round 0
packet. Round 2 below supplies the latter smooth reduction.

## Native declaration map and evidence

All names below are in `RicciFlowSharpEstimate.Geometry.AreaProfile`.

| Result | Canonical source and declaration |
|---|---|
| Actual operator and smoothness | `Geometry/AreaActionFactorization.lean`: `meridionalOperator`, `meridionalOperator_contDiff` |
| Complete factorization (1) | Same module: `meridionalAction_eq_square_potential`; private actual flux derivative |
| Green derivative and automatic pole flux | `Geometry/AreaActionVariation.lean`: `meridionalGreenFlux_hasDerivAt`, `meridionalGreenFlux_endpoints`, `integral_warp_mul_operator_mul` |
| Euler operator, polarization and (2) | Same module: `meridionalJacobiOperator`, `meridionalJacobiOperator_contDiff`, `integral_meridionalOperator_pair_eq_jacobi`, `meridionalAction_eq_integral_jacobi` |
| Actual affine derivatives and (3) | Same module: `meridionalOperator_add_mul`, `meridionalAction_add_mul`, `meridionalAction_hasDerivAt` |
| Smooth stationarity (4) and endpoint values (5) | Same module: `meridionalAction_stationary_iff`, `meridionalJacobiOperator_zero`, `meridionalJacobiOperator_one` |
| Nonzero normalization and homogeneity (6) | Same module: `integral_warp_mul_sq_pos`, `meridionalAction_const_mul`, `exists_normalized_area_probe` |
| Original metric/form pairing and variation (7) | `Geometry/AreaVariationGeometry.lean`: `oneFormDissipation_eq_integral_jacobi_of_profile_probe`, `oneFormDissipation_meridional_hasDerivAt` |

The [source-bound Round 0 native gate](../evidence/phase2-round-0-final/receipt.json)
passed: three new modules were freshly elaborated; 149 unchanged phase-I source
elaborations were reused with verified hashes. The root aggregate, unsuppressed
declaration linters, exact signatures and actual transitive axiom closure passed
for 152 modules and 2,449 defining-module declarations, including 801 private
ones. Only `propext`, `Classical.choice` and `Quot.sound` occur in the checked
closures. The new packet has 19 public theorems and three actual operator/flux
definitions. The Round 0 outer review accepted this bounded packet at `cea7baa`; full phase-II
acceptance remains open. These notes are
separate from the accepted phase-I manuscript; its TeX and PDF are unchanged.

## Historical tools: bounded audit outcome

The supplied frozen historical tree does not contain
`ConnectionGlobalCalibrationRigidity.lean` or `ConnectionProjectedSFSRigidity.lean`.
Their exact statements and dependency closures remain unassessed. Missing files
are an evidence limitation, not a refutation of their contents. No old theorem
is imported into the new native packet.

The available downstream sources contain substantive results, with explicit
remaining premises:

- `ConnectionSmoothMeridianGeometricRealization.ClosedSphereZonalSafe` states
  universal nonnegativity of the original smooth meridional action in a curvature
  box. Its recovery consumer transports that supplied safety statement through
  genuine smooth geometric realization.
- `ConnectionPhysicalFiniteMeridianAssembly.CoordinatizedFiniteInterfaceTerminalPolarAssembly.action_glue` proves additive action
  from actual transported jets and interval telescoping. The final activity
  consumer still takes sphere safety, a coordinatized assembly for the relevant
  histories, an opposite completion and a zero-action pair. It does not produce
  a critical optimizer or global safety from a numerical branch.
- `FullBalancedBernsteinThreshold` has an endpoint-safety argument for its
  exhaustive negative-witness threshold. The final connection-identification
  theorem in `RotationalAllOneFormThreshold` requires candidate safety and
  failure of every larger cap. Equating that threshold with a candidate ratio
  under those assumptions does not evaluate the ratio.
- `ConnectionProjectedFeedback` proves a pointwise clamp maximization law.
  `ConnectionPhysicalHamiltonianReduction` needs strict physical concavity and
  actual coefficient/maximization identities. On its positive branch, the
  inspected strict-concavity condition is equivalent to `costate_N < -R/2`.
  The clamp algebra does not supply that sign or a fixed number of contacts.
- The available Bregman/Picone and active-costate leaves require their stated
  sign, zero-defect or endpoint-variation realization hypotheses. They are
  useful conditional tools, not an established global original-action calibration.

This is source-level research inventory. The historical manifest labels those
bytes unverified; current phase-I receipts are not compiler or transitive-axiom
evidence for the historical tree. The new packet uses only current accepted
native dependencies.

## Round 1: actual curvature variation and normalized conditions

The core curvature derivative needs continuous `K,ξ` and a globally smooth fixed
probe `r`. For original smooth variations, take both `K` and `ξ` globally smooth.
No derivative of the curvature is used in this calculation. Put

\[
 K_t=K+t\xi,\quad b=f_1,\quad p=r',\quad z=r'',\quad q=fr''+2br'-Kr.
\]
The actual affine primitive laws are

\[
 f_{K_t}=f+t\delta f,\quad b_{K_t}=b+t\delta b,\qquad
 \delta f(x)=-2\int_0^x(x-u)\xi(u)\,du,\quad
 \delta b(x)=-2\int_0^x\xi(u)\,du.
\]
The fixed affine term `2x` in the warp is retained. The new complete-density
coefficients, evaluated at the original `K,r`, are

\[
 \begin{aligned}
 \alpha&=q^2+2fqz-Kbrp+K^2r^2,\\
 \beta&=4fqp-Kr(fp+br),\\
 \gamma&=-2fqr-br(fp+br/2)+2Kfr^2.
 \end{aligned}
\]
An exact cubic expansion in `t`, followed by integration of continuous
coefficients, proves the actual parameter derivative

\[
 \frac{d}{dt}\bigg|_0 A_{K_t}(r)
 =\int_0^1(\alpha\delta f+\beta\delta b+\gamma\xi). \tag{8}
\]
This is differentiation of the existing complete action, not an assumed
first-variation field. The proof supplies every integrability condition.

For continuous coefficients the new generic Volterra pairing theorems transfer
prefix primitives to tail primitives. They are proved from actual FTC derivatives
and integration by parts, including either orientation of the endpoints.
Applying both kernel identities to (8) gives

\[
 \sigma(u)=\gamma(u)-2\int_u^1[(x-u)\alpha(x)+\beta(x)]\,dx,
 \qquad \delta A=\int_0^1\sigma(u)\xi(u)\,du. \tag{9}
\]
The switching density is continuous. Equation (9) supplies neither an obstacle
sign nor a count of contacts.

The two constraints on the direction,
`∫ξ=0` and `∫xξ=0`, preserve the original two curvature moments **exactly for
every parameter**. Both warp/slope variations vanish at both endpoints under
these constraints. Positivity of a continuous curvature on the compact physical
interval persists for all sufficiently small parameters of either sign.
A strict interior box has the same property. More generally, a direction whose
closed support in the physical interval lies strictly between the obstacles is
feasible for both signs, even if the original curvature touches an obstacle
elsewhere. The use of closed support supplies a uniform margin. Weak signs only
at contact points are not used as a substitute for a feasible neighborhood.
A segment `K+t(G−K)`, `0≤t≤1`, between two curvatures in the same closed box and
with the same normalized moments is genuinely one-sided feasible.

The normalized functional must account for the geometry dependence of the mass:

\[
 m(K,r)=\int_0^1f_Kr^2,\qquad
 \delta m=\int_0^1\delta f\,r^2.
\]
The new `normalizedProbe` is literally `r/√m`, and for `m>0` its mass is one.
For smooth normalized-moment data its complete action is the actual quotient
`\mathcal R(K,r)=A_K(r)/m(K,r)`.
For any real `μ`, define the corrected switching density

\[
 \sigma_\mu(u)=\sigma(u)+2\mu\int_u^1(x-u)r(x)^2\,dx.
\]
Native differentiation proves

\[
 \delta\bigl(A-\mu(m-1)\bigr)=\int_0^1\sigma_\mu\xi,
 \qquad
 \delta\mathcal R=\frac1m\int_0^1\sigma_{\mathcal R}\xi. \tag{10}
\]
Thus the mass correction is equivalent to replacing `α` by `α−μr²` in the
switching calculation. An arbitrary `μ` in the algebraic first identity is not
a claim that a Lagrange multiplier has been extracted from an optimizer.
The second identity fixes its coefficient to the actual Rayleigh quotient.

For smooth zero-moment curvature directions and positive initial mass, the
literal normalized curvature path has positive mass, unit normalized mass and
complete action equal to the quotient throughout a neighborhood of zero.
Consequently (10) is also the derivative of
`A_{K_t}(normalizedProbe K_t r)`. Local minima of these two scalar parameter
functions on any specified feasible parameter set are natively equivalent.
This proves the normalization bridge for this variation; it is distinct from
T6's exhaustive original-metric normalization.

For probe variations the actual quotient derivative is

\[
 \frac{d}{dt}\bigg|_0\mathcal R(K,r+ts)
 =\frac2m\int_0^1fs\,[E_Kr-\mathcal R(K,r)r]. \tag{11}
\]
With positive curvature, smooth data, both moments and positive mass, stationarity
under every smooth probe direction is equivalent to

\[
 E_Kr=\mathcal R(K,r)r\quad\text{on }[0,1]. \tag{12}
\]
The proof tests with the actual smooth residual and uses positive weighted mass
and endpoint continuity. At unit mass its eigenvalue is `A_K(r)`; a zero-mode
conclusion additionally requires zero action. A local minimum of the **literal
normalized-probe action** along every smooth probe direction implies (12).
No nonzero eigenfunction or optimizing pair is constructed.

The feasible parameter set used by the new curvature optimality consumers is
explicit: the same affine curvature must satisfy the box and both exact moments.
For a supplied `IsLocalMinOn` of the quotient on that set, a segment to any other
admissible curvature `G` gives

\[
 \int_0^1\sigma_{\mathcal R}(G-K)\geq0. \tag{13}
\]
For a zero-moment direction with closed support in the free region, the pairing
is zero, because both parameter signs are feasible. Strict interior box data
are a separate immediate consumer. These are justified directional necessary
conditions. They do not assert a joint minimizer, moment multipliers, global
sufficiency, principal-sheet signs, symmetry or finite contact structure.

### Round 1 native map

Area names below have prefix `RicciFlowSharpEstimate.Geometry.AreaProfile`.
Generic analysis names have the prefix indicated in the table.

| Result | Canonical declarations |
|---|---|
| Oriented primitive pairing | `Analysis.VolterraPairing.integral_mul_primitive_eq`, `integral_mul_kernel_eq` in `Analysis/VolterraPairing.lean` |
| Actual affine primitives and moments | `warp_add_mul`, `warpSlope_add_mul`, `warpVariation_hasDerivAt`, `warpSlopeVariation_hasDerivAt`, `curvature_moments_add_mul`, `curvature_variation_endpoints` in `Geometry/AreaCurvaturePrimitives.lean` |
| Complete density derivative (8) | Actual coefficient definitions and `meridionalAction_curvature_hasDerivAt` in `Geometry/AreaCurvatureVariation.lean` |
| Switching pairing (9) | `curvatureSwitchingDensity_continuous`, `curvatureFirstVariation_eq_integral_switching`, `meridionalAction_curvature_hasDerivAt_switching` in the same module |
| Probe mass, quotient and eigen-equation (11)–(12) | `probeMass_add_mul`, `probeMass_hasDerivAt`, `rayleighQuotient_hasDerivAt`, `rayleighQuotient_stationary_iff`, its unit-mass/zero-action specializations in `Geometry/AreaProbeRayleigh.lean` |
| Literal normalized probe | `probeMass_normalizedProbe`, `meridionalAction_normalizedProbe`, `normalized_probe_action_hasDerivAt`, `normalized_probe_euler_eq_of_isLocalMin` in the same module |
| Curvature mass correction (10) | `probeMass_curvature_add_mul`, `probeMass_curvature_hasDerivAt`, `action_sub_mass_curvature_hasDerivAt`, `rayleighQuotient_curvature_hasDerivAt` in `Geometry/AreaCurvatureVariation.lean` |
| Literal normalized curvature path | `normalized_curvature_action_hasDerivAt`, `eventually_normalized_curvature_variation`, `isLocalMinOn_normalized_curvature_iff` in the same module |
| Actual feasible neighborhoods/segments | The four compact-set and scalar interval theorems in `Analysis/AffineIntervalVariation.lean` |
| Constrained necessary conditions (13) | `Icc_subset_curvatureParameters_segment`, `curvatureParameters_mem_nhds_of_interior`, `curvatureParameters_mem_nhds_of_free_support`, `curvature_pairing_nonneg_of_isLocalMinOn_segment`, both zero-pairing consumers in `Geometry/AreaCurvatureOptimality.lean` |

The [Round 1 native gate](../evidence/phase2-round-1/receipt.json) passes for all
158 modules. It freshly elaborates the six new modules, reuses 152 unchanged
accepted source elaborations, and checks the root, unsuppressed declaration
linters, 956 signature queries and actual transitive axiom closures for 2,542
declarations, including 812 private declarations. Only the three permitted
foundational axioms occur. Its one fresh independent outer review passed at
`38bdb3139c7b57581649f9500b6f6dfd032c4a59`.
The accepted Round 0 source bytes and Phase-I paper remain unchanged.

The historical reconstructed first-variation declarations and their density and
primitive reconstruction equations were inspected as research evidence. The new
proof differentiates the current corrected primitives directly by exact cubic
expansion; no historical theorem, continuous-map reconstruction package or old
native certificate is imported. The available historical `C_FB` endpoint-safety
results remain substantive source evidence, as the Round 0 review records, but
still do not identify the unrestricted sharp number.

## Round 2: exhaustive normalization of original competitors

Start with arbitrary original `D : RotationalProfile.PoleData`, not prescribed
normalized curvature or a unit probe. Write `a=D.a`, let `f_a` be its original
height warp, and use the actual length and coordinate

\[
 \ell=\int_{-1}^1a(v)\,dv>0,\qquad
 X(v)=\ell^{-1}\int_{-1}^v a(s)\,ds.
\]
The accepted coordinate theorem gives `X(-1)=0`, `X(1)=1`, strict monotonicity
on the physical interval and `X'=a/ℓ>0` there. Its new smoothness theorem and the
native smooth interval inverse produce an auxiliary globally smooth extension
of the physical inverse. The native smooth quotient extension then produces a
globally smooth `K` agreeing with the accepted continuous transported curvature
on `[0,1]`. This construction works for every original `D` without additional
compatibility hypotheses.

`D.AreaNormalization` stores only this smooth `K` and its physical agreement
with the actual transported curvature. The package does not assume an action,
probe, independent derivative or safety certificate. `D.areaNormalization`
chooses it **before any probe**. Define the common smooth inverse by

\[
 V(x)=-1+\int_0^xK(t)\,dt.
\]
Physical integral congruence proves that this primitive is the physical inverse:
`V(X(v))=v` for `v∈[-1,1]` and `X(V(x))=x` for `x∈[0,1]`. It has the correct
endpoint values, `V'=K`, and sends interiors to interiors. The globally clamped
inverse is only used through its established continuous laws and physical
agreement; it is never declared globally smooth. Both moments and all
coefficient laws are derived from the same original profile:

\[
 K(X(v))=\frac{\ell}{a(v)},\qquad
 a(V(x))K(x)=\ell,\qquad
 \int_0^1K=2,\quad\int_0^1xK=1,
\]
\[
 f_K(X(v))=\frac{f_a(v)}\ell,\qquad
 f_{1,K}(X(v))=-2v. \tag{14}
\]
These equations hold on the closed physical intervals, including both poles.

For **every** smooth original height probe `R`, define `r=R∘V`. Its smoothness,
physical values and actual derivatives follow from this same map:

\[
 r(X(v))=R(v),\qquad
 r'=K(R'\circ V),\qquad
 r''=K^2(R''\circ V)+K'(R'\circ V).
\]
Differentiating the actual curvature equation on the nondegenerate closed
interval, including endpoints by derivative uniqueness, gives

\[
 K'(X(v))=-\frac{\ell^2a'(v)}{a(v)^3},\qquad
 L_Kr(X(v))=\frac{\ell}{a(v)}L_aR(v).
\]
Substitution into **every term of the complete six-entry density**, followed
by the actual Jacobian `dx=(a/ℓ)dv`, proves

\[
 A_K(R\circ V)=J_a(R),\qquad
 Q_{g_D}(M_D(R))=2\pi A_K(R\circ V). \tag{15}
\]
No unit-probe specialization or scale guess is used. The natural original-data
consumer requires only `D`, `R` and its smoothness. Conversely, any smooth area
probe `r` pulls back by `X`, and `A_K(r)=J_a(r∘X)`. Thus the entire smooth probe
class, including all smooth probe directions, is covered using fixed geometry.
The new generic closed-interval C² equality theorem supplies actual first- and
second-derivative agreement at both endpoints. The physical curvature, inverse,
probe jets and complete action are independent of the off-interval extension
choice. No Dirichlet or Neumann restriction has been added.

The original meridional form is zero exactly when `R` vanishes everywhere in
`(-1,1)`; the same holds for the azimuthal form. The proof uses the actual
cylinder pullback and endpoint covector laws. Interior nonvanishing is preserved
by `X,V`, so

\[
 M_D(R)\ne0
 \quad\Longleftrightarrow\quad
 m(K,R\circ V)>0.
\]
The same equivalence holds after the actual representing diffeomorphism.
Nonzero values only outside the physical interval do not qualify. For a
nonzero component, the existing literal probe `r/√m` has unit mass and
`Q=2πm A_K(r/√m)`. Zero components are handled separately. The new mass theorem
also retains the **actual original metric norm**, with its full scale:

\[
 \int_{S^2}|M_D(R)|_{g_D}^{2}\,d\mu_{g_D}
       =2\pi\ell^2m(K,R\circ V). \tag{16}
\]

The represented-class theorem chooses one `D`, one diffeomorphism `F` and one
normalization `N` before quantifying over all original forms and curvature boxes.
It returns `g=F* g_D`, the actual conjugated Haar projector `P_F`, its literal
meridional/azimuthal classification, and the complete original action split

\[
 Q_g(h)=2\pi\bigl[A_K(R\circ V)+A_K(S\circ V)\bigr]
                  +Q_g(h-P_Fh),\qquad Q_g(h-P_Fh)\geq0. \tag{17}
\]
The accepted equality criterion for the same remainder is retained. Original
positive curvature bounds `[κ,Λ]` give normalized bounds `[ℓκ,ℓΛ]`, with positive
lower endpoint and exact ratio `(ℓΛ)/(ℓκ)=Λ/κ`. Thus any universal unit-mass scalar
safety theorem for the stated smooth normalized moment/box class implies the
existing `rotationalSafeCaps` predicate for all original smooth forms. The
converse scalar-safety implication uses the accepted tied smooth realizer.
These are exhaustive **reduction theorems**, not a proof of safety at a new cap,
a determining characterization of the constant, or an existence theorem for an
original or relaxed optimizer.

### Round 2 native map

`N` names below have prefix
`Geometry.RotationalProfile.PoleData.AreaNormalization`; `D` names have prefix
`Geometry.RotationalProfile.PoleData`. All prefixes are relative to
`RicciFlowSharpEstimate`.

| Result | Canonical declarations |
|---|---|
| Actual endpoint derivative agreement | `Analysis.eqOn_derivatives_Icc` in `Analysis/ClosedIntervalDerivatives.lean` |
| Smooth coordinate and original-data producer | `Geometry.ReciprocalArea.coordinate_contDiff`, `D.AreaNormalization`, `D.nonempty_areaNormalization`, `D.areaNormalization` in `Geometry/SmoothAreaNormalization.lean` |
| Common smooth inverse, moments and coefficients (14) | `N.inverse_contDiff`, `inverse_hasDerivAt`, `inverse_coordinate`, `coordinate_inverse`, `curvature_pos`, `integral_curvature`, `integral_mul_curvature`, `curvature_coordinate`, `warp_coordinate`, `warpSlope_coordinate` in the same module |
| Original physical nonzero criteria | `D.meridionalOneForm_eq_zero_iff`, `meridionalOneForm_ne_zero_iff`, their azimuthal siblings in `Geometry/PhysicalProbeNonzero.lean` |
| Actual probe jets and full density/action (15) | `N.deriv_probe`, `deriv_deriv_probe`, `curvature_deriv_coordinate`, `meridionalOperator_coordinate`, `meridionalDensity_coordinate`, `meridionalAction_eq`, `oneFormDissipation_meridional_eq` in `Geometry/NormalizedAreaAction.lean` |
| Off-interval independence and reverse probe coverage | `N.curvature_deriv_eq_on`, `probe_derivatives_eq_on`, `meridionalAction_extension_independent`, `probe_comp_coordinate`, `meridionalAction_comp_coordinate`; `Geometry.AreaProfile.meridionalAction_congr` in the same module |
| Physical mass, literal normalization and actual norm (16) | `N.probe_nonzero_iff`, `probeMass_pos_iff_meridional_ne_zero`, its azimuthal sibling, `normalized_probe_action`, `integral_normSq_eq_probeMass` in `Geometry/NormalizedAreaMass.lean` |
| Scaled curvature and represented nonzero/action | `N.curvature_inverse`, `profile_mul_curvature`, `curvature_bounds_scaled`, the two `probeMass_pos_iff_pullback_*_ne_zero` theorems and `oneFormDissipation_pullback_meridional_eq` in `Geometry/NormalizedAreaHaar.lean` |
| Fixed-representation full Haar split (17) | `N.exists_conjugated_haar_area_dissipation`, `Geometry.IsRepresentedRotationalMetric.exists_normalized_area_representation` in the same module |
| Natural original-data and safety consumers | `D.oneFormDissipation_eq_normalizedAreaAction`, `N.oneFormDissipation_nonneg_of_normalized_safety`, `Geometry.rotationalSafeCaps_of_normalized_area_safety`, `Geometry.areaAction_nonneg_of_rotationalSafeCap` in the same module |

The six new canonical leaves contain 58 public theorems, three definitions and
one extension structure. Their evidence is recorded in the
[Round 2 native receipt](../evidence/phase2-round-2/receipt.json) and
[checkpoint record](../evidence/phase2-round-2/checkpoint.json). The single Round 2 outer review passed at `734dd5b`, including both delivered
checkpoints. The unchanged Round 0 and Round 1 reviews remain accepted. Phase-I source, paper and evidence bytes remain preserved.

Additional native regression checks use `D.a=c` for **arbitrary `c>0`**:
`ℓ=2c`, `X(v)=(v+1)/2`, physical `K=2` and `V(x)=2x−1`.
Both sides of (15) give `4/3` for `R=1` and `20/3` for the nonconstant `R(v)=v`;
the corresponding original geometric dissipations are `8π/3` and `40π/3`.
A separate consumer uses arbitrary `D,R` with no supplied coordinate equations.
These are exact kernel checks, not numerical evidence for a sharp value.

### Round 2 continuation: actual original-form variations

The same smooth normalization transports actual original-form variations at
arbitrary original scale. Two further native modules give direct geometric
consumers of the complete action and quotient calculus.
Fix the original `D` and its normalization **before** smooth probes `R,S`, and
write `r=R∘V`, `s=S∘V`. The actual original-form variation satisfies

\[
 \frac{d}{dt}\bigg|_0 Q_{g_D}(M_D(R+tS))
       =4\pi\int_0^1f_KsE_Kr. \tag{18}
\]
The same formula holds after the actual representing diffeomorphism, with the
same pullback metric, varying pullback form and fixed normalization. No profile
compatibility premise or new geometry is requested of the caller.

Stationarity of this original dissipation along **every original smooth
meridional direction** is equivalent to `E_Kr=0` on `[0,1]`. For the exhaustive
implication, any smooth area direction `s` comes from the actual original
`S=s∘X`; physical equality suffices inside the integral. The reverse implication
uses the same complete pairing. No endpoint restriction, nonzero kernel or
full joint optimizing pair is asserted.

Let the physical quotient use the literal original norm and volume:

\[
 \mathcal Q_D(R)=
 \frac{Q_{g_D}(M_D(R))}{\int_{S^2}|M_D(R)|_{g_D}^2\,d\mu_{g_D}}.
\]
The exact mass factor in (16) gives

\[
 \mathcal Q_D(R)=\ell^{-2}\mathcal R(K,r),\qquad
 \frac{d}{dt}\bigg|_0\mathcal Q_D(R+tS)
 =\frac{2}{\ell^2m(K,r)}\int_0^1 f_Ks
       [E_Kr-\mathcal R(K,r)r]. \tag{19}
\]
The derivative assumes the actual original form is nonzero, which supplies
positive physical mass. The algebraic quotient identity also handles zero mass
using Lean's totalized real division; no unit normalization or spectral meaning
is assigned to the zero form.

A local minimum of the **literal original quotient** along every original smooth
meridional direction therefore implies
`E_Kr=𝓡(K,r)r` on the closed physical interval. Its proof transports all directions
and reuses the accepted scalar stationarity equivalence. The coefficient is the
actual scalar quotient, or `ℓ²𝒬_D(R)`; it is not silently replaced by zero. This
is a fixed-geometry necessary-condition application. It still supplies no joint
minimum, critical-object existence or moment multiplier. Since ℓ varies with the
metric, the physical quotient itself is not invariant under metric scaling.
A future joint-minimum application must retain the normalized geometry scale
or the equivalent ℓ² correction; a minimum over unnormalized physical quotients
cannot simply be substituted for the normalized scalar problem.

| Result | Declaration, in `Geometry.RotationalProfile.PoleData.AreaNormalization` |
|---|---|
| Actual original dissipation derivative (18) | `oneFormDissipation_meridional_hasDerivAt` in `Geometry/NormalizedAreaVariation.lean` |
| Exhaustive original-direction stationarity | `oneFormDissipation_meridional_stationary_iff` in the same module |
| Same represented metric/form variation | `oneFormDissipation_pullback_meridional_hasDerivAt` in the same module |
| Literal physical quotient and derivative (19) | `oneFormDissipation_div_normSq_eq`, `oneFormDissipation_div_normSq_hasDerivAt` in `Geometry/NormalizedAreaRayleigh.lean` |
| Necessary condition from original directional minima | `oneFormDissipation_div_normSq_euler_eq_of_isLocalMin` in the same module |

The [continuation native receipt](../evidence/phase2-round-2-continuation/receipt.json)
reuses the unchanged initial Round 2 native inputs and records fresh checks of
these two leaves and the affected root. The single outer review of the coherent Round 2 packet passed at `734dd5b`;
unchanged mathematics and its matching native evidence remain accepted.

## Round 3: complete-action coercivity and both-pole mass control

Let `K` be continuous and `r` be C² on the real line. Assume the actual normalized
moments and a positive physical curvature box `0<κ≤K≤Λ` on `[0,1]`. These hypotheses
include every original smooth normalized competitor. No derivative of K is
bounded or used in the following estimate. Write

\[
 m=\int_0^1fr^2,\qquad U=\int_0^1r^2,\qquad
 \mathcal E=\int_0^1 f(L_Kr)^2,\qquad
 \mathcal G=\int_0^1 f^2(r')^2.
\]
Here `f=warp K`, its slope is the actual primitive `b=warpSlope K`, and `L_K`
uses the actual first and second derivatives of r. The energy `𝓔` is distinct
from the fourth-order Jacobi operator `E_K` used in earlier sections.

The native comparison of second derivatives and the two pole values gives

\[
 \kappa x(1-x)\leq f(x)\leq\Lambda x(1-x),\qquad
 |b(x)|\leq2,\qquad 0\leq f(x)\leq2\min(x,1-x). \tag{20}
\]
The quadratic comparisons require only the corresponding curvature bound and
moments. Nonnegative curvature suffices for the slope and two-pole upper bound.
No symmetry of the geometry or probe is assumed.

The actual weighted operator flux satisfies

\[
 (f^2r'r)'=frL_Kr+f^2(r')^2+fKr^2.
\]
The moments imply `f(0)=f(1)=0`, so both flux values vanish for every C² probe,
with unrestricted probe endpoint values. Integrating gives

\[
 \int_0^1frL_Kr=-\mathcal G-\int_0^1fKr^2.
\]
Multiplying a square by the nonnegative warp and integrating then proves the
parameterized interpolation estimate

\[
 4t\mathcal G\leq4t^2\mathcal E+m\qquad(t\geq0). \tag{21}
\]
This calculation retains the curvature term with its actual nonnegative sign.

For `w=x(1-x)`, a separate generic C¹ Hardy estimate is

\[
 U\leq12\int_0^1wr^2+4\int_0^1w^2(r')^2.
\]
It comes from the exact derivative of `w(1−2x)r²`, whose two boundary values are
zero, and a scalar square inequality. The numbers are consequences of that flux
and the absorption, not proposed values of a threshold. Transferring this estimate
through (20) gives

\[
 \kappa^2U\leq12\kappa m+4\mathcal G. \tag{22}
\]

The proof estimates the **original complete density**, not its smooth K′
factorization. For `q=L_Kr`, the explicit nonnegative-square decomposition implies

\[
 f q^2-Kbr(fp+br/2)+K^2fr^2
       \geq f q^2-\Lambda f^2p^2-3\Lambda r^2,
 \qquad p=r'.
\]
Thus `A≥𝓔−Λ𝓖−3ΛU`. Set

\[
 d=\Lambda(1+12/\kappa^2),\qquad
 \Gamma(\kappa,\Lambda)=\frac{d^2}{2}
             +\frac{36\Lambda}{\kappa}+\frac3\kappa+\frac1{\kappa^4}\geq0.
\]
Using (21) at `t=1/(2d)` and `t=κ²/4`, together with (22), yields respectively

\[
 \frac{\mathcal E}{2}\leq
 A+\left(\frac{d^2}{2}+\frac{36\Lambda}{\kappa}\right)m,
 \qquad
 U\leq\mathcal E+\left(\frac{12}{\kappa}+\frac4{\kappa^4}\right)m.
\]
The resulting homogeneous complete-action coercivity theorem is

\[
 \boxed{\ \frac{\mathcal E+U}{4}\leq A_K(r)+\Gamma(\kappa,\Lambda)m(K,r)\ }. \tag{23}
\]
The constants are chosen before K and r, depend only on the positive box, and
require no bounds on curvature derivatives. Negative action is allowed; the mass
correction in (23) is essential. This estimate supplies no new safe cap.

For `m=1` and `A≤B`, both `𝓔` and U are at most `4(B+Γ)`. The actual sum of the
weighted masses near the two poles is

\[
 P_\delta(K,r)=\int_0^\delta fr^2+\int_{1-\delta}^1fr^2.
\]
For every `0≤δ≤1`, (20) and integral monotonicity prove

\[
 0\leq P_\delta(K,r)\leq4\delta U
                  \leq16\delta(B+\Gamma). \tag{24}
\]
The two intervals may overlap; both contributions remain in the definition.
For every ε>0, the explicit choice

\[
 \delta_\varepsilon=
 \min\!\left(1,\frac{\varepsilon}{16(\max(B,0)+\Gamma)+1}\right)>0
\]
works for every admissible K,r and every radius `0≤t≤δ_ε`. This proves a single
modulus tending to zero for both weighted polar masses, uniformly over any
varying sequence with these bounds. No geometry or probe is chosen before the
uniform radius in that theorem.

The original ratio restriction is retained in the cap-class consumers. From
`∫K=2`, a positive box `[κ,Λ]` and `Λ/κ≤C`, integration of the box gives
`κ≤2≤Λ`, hence `2/C≤K≤2C`. The latter is an auxiliary common box for the estimate;
it does not replace the original ratio restriction. The native ratio-class
coercivity and polar-radius statements keep κ, Λ, their positive lower bound,
and `Λ/κ≤C` explicitly in their hypotheses. Their constants depend only on C
(and the action bound for the radius), even when the original boxes vary.

### Round 3 native map and scope

Geometry names in the table have prefix `Geometry.AreaProfile`; all prefixes are
relative to `RicciFlowSharpEstimate`.

| Result | Canonical declaration or source |
|---|---|
| Actual warp, slope and ratio bounds (20) | Six theorems in `Geometry/AreaWarpBounds.lean`, including `warp_bounds_of_curvature_bounds`, `warp_nonneg_le_two_mul_min`, `curvature_bounds_of_ratio` |
| Generic C¹ Hardy estimate | `Analysis.integral_sq_le_parabolic_weighted_energy` in `Analysis/ParabolicWeightedHardy.lean` |
| Actual energies and C² operator continuity | `probeOperatorEnergy`, `probeGradientEnergy`, `meridionalOperator_continuous_of_contDiff_two` in `Geometry/AreaProbeEnergy.lean` |
| Actual flux pairing and interpolation (21) | `integral_warp_mul_probe_operator`, `probeGradientEnergy_interpolation` in the same module |
| Transfer of Hardy (22) | `integral_sq_le_probeMass_gradient` in the same module |
| Complete density bound and homogeneous coercivity (23) | `probeOperatorEnergy_sub_le_action`, `actionMassCorrection`, `meridionalAction_coercive`, `exists_uniform_action_coercivity` in `Geometry/AreaActionCoercivity.lean` |
| Actual two-tail mass | `polarProbeMass`, `polarProbeMass_nonneg`, `polarProbeMass_le_four_mul_radius` in `Geometry/AreaPolarMass.lean` |
| Unit-mass bounds and uniform radius (24) | `probe_energies_le_of_unit_mass_action_le`, `polarProbeMass_le_of_unit_mass_action_le`, `exists_uniform_polar_mass_radius` in `Geometry/AreaActionCoercivity.lean` |
| Original ratio-class consumers | `meridionalAction_coercive_of_curvature_ratio`, `exists_uniform_polar_mass_radius_of_ratio` in the same module |

The packet has five new canonical leaves, 24 public theorems and four definitions.
Its [native receipt](../evidence/phase2-round-3/receipt.json) and
[checkpoint record](../evidence/phase2-round-3/checkpoint.json) bind the final inputs
and validation. The configured single Round 3 outer review is pending. Accepted
Phase-I and Phase-II rounds 0–2 remain preserved. The first-phase TeX/PDF is unchanged.

Exploratory exact rational polynomial integration tested `K=2` with `(1−x)^n`
and `x^n`, concentrating near the two different poles, before the coercivity
consumers were promoted. These computations were stress tests, not theorem
evidence. Additional native consumer checks cover both polynomial families for
**every natural n**, and a varying sequence of curvatures, probes and original
ratio boxes with unit mass, a common action bound and one shared radius. The actual proof of (23) is uniform over all
stated competitors and does not rely on those examples.

## Round 3 continuation: direct control of the remaining polar terms

The initial Round 3 estimate controls weighted mass. The continuation proves
additional derivative estimates and **direct** unweighted/remainder tail bounds;
these are not inferred from weighted mass tightness alone. Keep the actual
primitives f,b, operator q=L_Kr and positive box κ≤K≤Λ with both exact moments.
Continuous K and C² r still suffice, with no curvature derivative bound.
Put w(x)=x(1−x) and

\[
 H=\int_0^1 w(r')^2,\qquad J=\int_0^1 f^3(r'')^2.
\]

The actual flux `2 f² b (r′)²` vanishes at both poles. Its derivative, using
`f′=b` and `b′=−2K`, gives

\[
 \int_0^1 f(q+Kr)^2=J+4\int_0^1 f^2K(r')^2,
 \qquad J\leq2E+2\Lambda^2m. \tag{25}
\]

This identity does not differentiate K or require pole values of r or r′ to
vanish. A separate polynomial flux `w²(1−2x)p²` gives, for every C¹ function p,

\[
 \int_0^1 wp^2\leq10\int_0^1w^2p^2+\int_0^1w^3(p')^2.
\]

Apply it to p=r′, use f≥κw, (25), and (21) at t=1 to obtain

\[
 \kappa^3H\leq(10\kappa+2)E+
       (5\kappa/2+2\Lambda^2)m. \tag{26}
\]

For m=1 and A≤B, let D=max(B,0)+Γ(κ,Λ). One explicit bound chosen before all
competitors is

\[
 M=1+4D+
   \frac{4(10\kappa+2)D+5\kappa/2+2\Lambda^2}{\kappa^3}>0.
\]

Then E,U,G,H≤M. The first-power weight in H is stronger at the poles than the
squared-warp gradient bound G used in the initial coercivity argument.

For C¹ r define its two unweighted tails
`T_s=∫₀ˢr²+∫₁₋ₛ¹r²`. A tent with branches `(1−s)x` and `s(1−x)` has squared
height at most `s w`. Integrate the derivative of each affine branch times r²;
the internal boundary terms cancel exactly. The square inequality and reflection
then yield, for 0≤s≤1, a>0 and s≤a²,

\[
 T_s\leq2sU+2a(U+H). \tag{27}
\]

The second term is essential: a bound on U alone would not give uniform tail
integrability. The proof has no singular division by the vanishing warp and no
artificial endpoint condition.

The canonical remainder is defined by literal subtraction from the original
six-entry density:

\[
 R_K(r)=\operatorname{density}_K(r)-f(L_Kr)^2
       =-Kbfrr'-Kb^2r^2/2+K^2fr^2.
\]

Let `S_s=∫₀ˢ|R_K(r)|+∫₁₋ₛ¹|R_K(r)|`, the actual `polarActionRemainder`.
The already proved bounds |b|≤2 and 0≤f≤1, followed by a parameterized square
estimate, give for every t>0

\[
 S_s\leq(\Lambda/t+2\Lambda+\Lambda^2)T_s+2\Lambda tG. \tag{28}
\]

This controls the absolute complete remainder, including its negative unweighted
term and mixed derivative term. It does not replace either with a K′ potential.
For 0<t≤1 and 0≤s≤t⁴, apply (27) with a=t² and the common M bound:

\[
 T_s\leq6t^2M,\qquad
 S_s\leq(20\Lambda+6\Lambda^2)tM.
\]

Set Q=(6+20Λ+6Λ²)M, t=min(1,ε/(Q+1)), and δ=t⁴. For every ε>0 this δ>0,
δ≤1 works for **every** admissible K,r and **every** width 0≤s≤δ, with
`T_s≤ε` and `S_s≤ε`. The same theorem has an original-ratio consumer: C≥1,
varying κ,Λ>0 and Λ/κ≤C remain explicit, while the auxiliary [2/C,2C] box permits
one common radius before all competitors. No optimizer symmetry is assumed.

The continuation adds these native targets:

| Result | Canonical declarations (relative prefixes as above) |
|---|---|
| Weighted interpolation | `Analysis.integral_parabolic_mul_sq_le` in `Analysis/ParabolicDerivativeEnergy.lean` |
| Direct one- and two-pole unweighted estimates | `Analysis.integral_left_sq_le_parabolic_energy`, `Analysis.integral_polar_sq_le_parabolic_energy` in `Analysis/ParabolicPolarControl.lean` |
| Actual second-derivative identity and both derivative bounds | `integral_warp_operator_add_curvature_sq`, `integral_warp_cube_second_deriv_sq_le`, `integral_parabolic_deriv_sq_le` in `Geometry/AreaProbeRegularity.lean` |
| Complete remainder, absolute tails and (28) | `meridionalActionRemainder`, its C¹ continuity theorem, `polarActionRemainder`, `polarActionRemainder_le` in `Geometry/AreaActionPolarControl.lean` |
| Uniform sublevel and original-ratio consumers | `exists_uniform_probe_regularity_bound`, `exists_uniform_polar_action_radius`, `exists_uniform_polar_action_radius_of_ratio` in the same module |

These are four additional canonical leaves, eleven public theorems and two
definitions. Their final native receipt is recorded under
`docs/evidence/phase2-round-3-continuation/`. The single configured Round 3 outer
review remains pending for the combined packet; no independent acceptance is
inferred from the source simplifier advisory.

## Round 4 initial checkpoint: actual weak domain and a joint unit-mass limit

Round 3's combined estimate packet passed its single outer review at `2778716`.
Round 4 consumes those estimates to construct a limit; it does not supply
compactness or a limiting pair as a theorem premise. The native statement is
`Geometry.AreaProfile.exists_normalized_joint_weak_limit` in
`Geometry/AreaJointCompactness.lean`.

### The domain and its actual derivatives

Write U=(0,1), μ=Lebesgue measure restricted to U, and w(x)=x(1−x).
`Analysis.HasWeakDerivOn U r p` requires local integrability of both representatives
and the genuine distributional identity

\[
 \int_{\mathbb R}\varphi' r=-\int_{\mathbb R}\varphi p
 \quad\text{for every }\varphi\in C_c^\infty(U). \tag{29}
\]

The test products are proved integrable. The fundamental lemma for smooth
compact tests proves a.e. uniqueness of p; changing representatives a.e. preserves
the relation. `HasParabolicWeakDerivatives r p z` requires this relation for r,p
and for p,z, together with

\[
 r\in L^2(\mu),\qquad \sqrt w\,p\in L^2(\mu),\qquad
 w\sqrt w\,z\in L^2(\mu). \tag{30}
\]

Both derivatives belong to ordinary L² on every compact subset of U, because
the reciprocal weights are bounded there. Thus the domain has the stated local
second-order Sobolev regularity, expressed with genuine weak derivatives and L²
membership. Every globally C² probe embeds with its actual first and second
derivatives. No endpoint value or derivative trace is prescribed. Zero extensions
used to select representatives outside U are not trace conditions on this domain.
The final predicates use conjunctions with named theorem projections; their
conditions are not compiler-generated proof definitions.

### The constructed subsequence

Consider arbitrary sequences of continuous curvatures K_n and C² probes r_n,
positive box witnesses κ_n,Λ_n with Λ_n/κ_n≤C, C≥1, both exact normalized moments,
unit actual mass, and a common complete-action bound A(K_n,r_n)≤B. Then there
exist one strictly increasing φ:ℕ→ℕ, K_0,r_0,p_0,z_0 and κ_0,Λ_0 with:

- K_0 in L² and L∞ on U; κ_0>0, κ_0≤K_0≤Λ_0 a.e., Λ_0/κ_0≤C, and both
  original moments exactly 2 and 1. The original scalar witnesses κ_n,Λ_n
  converge to κ_0,Λ_0 on this same subsequence.
- Weak-* curvature convergence in the literal form of convergence of
  `∫K_(φ(n)) v` to `∫K_0 v` for **every** integrable real test v on U.
- Uniform convergence of the original `warp K_(φ(n))` and `warpSlope K_(φ(n))`
  on [0,1] to the original primitives of K_0. These limits are continuous on
  [0,1], retain both pole values, both slope values, the quadratic comparison
  with [2/C,2C], and the absolute slope bound 2. They satisfy the actual weak
  derivative laws Df=b and Db=−2K_0.
- `HasParabolicWeakDerivatives r_0 p_0 z_0`; r_0,p_0 are continuous on U.
  The probes converge strongly in L²(μ), and the probes and their actual first
  derivatives converge locally uniformly on U. The weighted actual second
  derivatives converge weakly in L² to w√w z_0, with every L² test retained.
- Genuine integrability and exact retention of the original mass

\[
 \int_0^1 f_{K_0}r_0^2=1,\qquad
 \exists x\in(0,1),\quad r_0(x)\ne0. \tag{31}
\]

  The result also supplies integrability of the literal complete weak density
  and L² membership of both its positive-square factors described below.

All these are conclusions of the producer. No limit, weak derivative, local
compactness property, preserved normalization or original-ratio retention is
assumed. The auxiliary common box [2/C,2C] controls constants; the returned
κ_0,Λ_0 retain the actual original ratio restriction separately.

Here is the dependency route used in the proof. The accepted coercivity and
parabolic estimates uniformly bound U,H and the weighted second derivative
energy. On every interior interval, the weight has a positive lower bound.
The actual FTC and an integrated square give

\[
 (r(x)-r(y))^2\leq |x-y|\int_a^b(r')^2,
 \quad (b-a)r(x)^2\leq2\int_a^b r^2+2(b-a)^2\int_a^b(r')^2. \tag{32}
\]

These give pointwise boundedness and equicontinuity for the probes and their
first derivatives on interior intervals. Sequential Arzela–Ascoli in the
compact-open topology produces locally uniform limits on all of U. The
verified unweighted polar estimate makes this family uniformly L² integrable;
Vitali convergence then upgrades the probe limit to global strong L².

The weighted second derivatives are extracted by sequential Banach–Alaoglu
and the native Riesz isometry for the real Hilbert space L²(μ). If their weak
limit is Z, set z_0=Z/(w√w) on U. A compact test divided by this nonvanishing
interior weight is itself an L² test. Passing the actual integration-by-parts
identity to the limit identifies Dp_0=z_0. Fatou's bound supplies the weighted
L² membership of p_0. This constructs the weak graph rather than assuming it.

For curvature, the original mean and ratio give
`κ_n∈[2/C,2]` and `Λ_n∈[2,2C]`. Compactness first extracts both scalars together;
Hilbert weak compactness then extracts the actual curvature. Testing a weak
limit against its negative part proves a.e. order closure, including varying
scalar bounds. The tests 1 and x preserve both moments. A common essential
bound extends L² pairings to all L¹ tests by bounded continuous approximation.
The indicator tests `1_(0,x)` and `(x−s)1_(0,x)` identify the original primitives,
including both endpoints; their common Lipschitz bounds upgrade this convergence
to uniform convergence. Later subsequences preserve every earlier convergence.

Finally, uniform warp convergence yields strong L∞ convergence of its coefficient,
while probes converge strongly in L². The native continuous L∞×L²→L² multiplier
and the L² inner product prove weighted square-integral convergence, hence (31).
This uses the uniformly converging **warp**, not a fictitious strong curvature
limit. A separate native argument also retains `∫r_0²≥1` from unit mass and f_n≤1,
which certifies physical nontriviality before the final weighted-mass assembly.

### Literal weak action, and what has not been proved

The geometric weak operator and action use the original primitives and the tied
weak derivatives from (29)–(30):

\[
 q=fz+2bp-Kr,\qquad
 A=\int_0^1\operatorname{meridionalActionDensity}(f,b,K,r,p,z). \tag{33}
\]

Under the actual coefficient bounds produced above, the graph gives
`√f q∈L²` and `√f(Kr)∈L²`. It also makes the mixed and negative terms integrable.
The native decomposition is exactly

\[
 A=\int f\,[q^2+(Kr)^2]-\int Kbfrp-\tfrac12\int Kb^2r^2. \tag{34}
\]

Specializing p,z to actual smooth derivatives agrees with `meridionalAction`
by definition. No totalized classical derivative is used for the weak limit,
and no K′ potential or missing jump/interface contribution replaces the density.
The coefficient-bound action lemma is an explicit auxiliary estimate; the joint
producer discharges all its premises for the returned object.

At the initial `0fe2595` checkpoint, full-action lower semicontinuity and the
two positive-square weak identifications were still open. The continuation below
supplies those identifications and the linear-K pairing limits. It does not
replace them with convergence of the whole remainder.

The review's oscillating example `K_n=2+cos(2πnx)` was checked as an exploratory
diagnostic using its actual primitives and normalized constant probe. Numerical
quadrature for n=1,4,16,64 keeps the curvature-square integral near 4.5 while
its complete actions tend toward 5 and its integrated remainders toward 0.5;
the limiting constant pair has action 4 and remainder 0. These computations
are **not** native theorem evidence. They confirm the need to retain both
positive squares in (34), and are not an asserted counterexample to lower
semicontinuity. No new sharp-cap value is inferred.

### Round 4 native map

All prefixes below are relative to `RicciFlowSharpEstimate`.

| Mathematical layer | Canonical sources and principal consumers |
|---|---|
| Weak derivative and weighted domain | `Analysis/WeakDerivative.lean`, `Analysis/ParabolicSobolev.lean`: `HasWeakDerivOn`, `HasParabolicWeakDerivatives`, a.e. uniqueness, smooth embedding and local L² |
| Actual interior compactness | `Analysis/IntervalDerivativeEnergy.lean`, `Analysis/LocallyUniformSubsequence.lean`, `Analysis/InteriorSobolevCompactness.lean`: actual interval bounds and `exists_subseq_locallyUniform_probe_deriv_of_weighted_energy` |
| Native weak Hilbert and curvature order limits | `Analysis/HilbertWeakSubsequence.lean`, `Analysis/L2WeakOrder.lean`, `Analysis/BoundedWeakPairing.lean` |
| Global probe convergence and identified weak derivatives | `Analysis/L2UniformIntegrability.lean`, `Analysis/WeakDerivativeLimits.lean`, `Analysis/WeightedWeakDerivativeLimit.lean` |
| Weighted mass continuity | `Analysis/L2WeightedMassContinuity.lean` |
| Actual curvature/scalar extraction | `Geometry/AreaCurvatureCompactness.lean`: `exists_curvature_subsequence_of_ratio_bound` |
| Original primitive identification and weak geometry | `Geometry/AreaWeakPrimitives.lean`, `Geometry/AreaUniformPrimitives.lean` |
| Actual sublevel probe producer | `Geometry/AreaProbeCompactness.lean`: `exists_subseq_strong_probe_of_action_bound`, `exists_subseq_weak_probe_of_action_bound` |
| Genuine weak action domain | `Geometry/WeakAreaAction.lean`: `weakMeridionalOperator`, `weakMeridionalAction`, positive-square membership, full density integrability and (34) |
| Joint unit-mass producer | `Geometry/AreaJointCompactness.lean`: `exists_normalized_joint_weak_limit` |

The 18 new leaves have final native evidence recorded separately in
`docs/evidence/phase2-round-4/`. Their single configured outer review remains
pending. Accepted rounds 0–3, Phase I, its paper bytes and all earlier receipts
remain unchanged.

## Round 4 continuation: the complete-action liminf of the original sequence

The continuation consumes the actual joint limit above. Its main theorem is
`Geometry.AreaProfile.exists_normalized_joint_weak_limit_le_liminf_action` in
`Geometry/AreaJointActionCompactness.lean`. Under the same smooth sublevel inputs,
it retains every conclusion of the initial joint producer and adds weak L²
pairings for both `√f_n q_n` and `√f_n K_n r_n`, together with

\[
 A_{\mathrm{weak}}(K_0,r_0,p_0,z_0)
 \leq \liminf_{n\to\infty} A(K_n,r_n). \tag{35}
\]

The right side is the liminf of the **original sequence**. It is not merely the
liminf along an arbitrary extracted subsequence. The complete density, its mixed
term, negative potential and positive curvature square are all retained.

### Identifying both positive factors

Write the actual graph coordinates as

\[
 P_n=\sqrt w\,r_n',\qquad Z_n=w\sqrt w\,r_n''.
\]

`exists_uniform_parabolic_graph_bound` derives a common L² bound for r_n,P_n,Z_n
from the accepted complete-action and derivative estimates. The initial producer
already gives weak convergence of Z_n and pointwise interior convergence of P_n.
On the finite physical measure space, the latter and its uniform L² bound imply
weak L² convergence against every L² test.

For the derivative part of the operator, use the actual coefficients

\[
 a_n=\frac{f_n\sqrt{f_n}}{w\sqrt w},\qquad
 c_n=\frac{2b_n\sqrt{f_n}}{\sqrt w}.
\]

They are evaluated a.e. in (0,1), where the denominators are nonzero. The actual
warp/slope estimates imply

\[
 0\leq a_n\leq\Lambda\sqrt\Lambda,\qquad
 |c_n|\leq4\sqrt\Lambda,
 \quad
 \sqrt{f_n}(f_n r_n''+2b_n r_n')=a_nZ_n+c_nP_n. \tag{36}
\]

Pointwise primitive convergence gives pointwise convergence of these bounded
coefficients. A native dominated-convergence lemma makes each coefficient times
one fixed L² test converge strongly in L². Weak/strong pairing then identifies
the weak limit in (36). This does not require uniform relative warp convergence
at the poles, a curvature derivative, or energy-tail vanishing.

For the curvature factor, testing `√f_n K_n r_n` against v in L² amounts to
pairing K_n with `r_n√f_n v`. The following native product principle supplies
strong L¹ convergence of that varying test:

\[
 x_n\longrightarrow x\text{ strongly in }L^2,\quad
 y_n\longrightarrow y\text{ a.e.},\quad
 \sup_n\|y_n\|_2<\infty
 \quad\Longrightarrow\quad
 \int|x_ny_n-xy|\longrightarrow0. \tag{37}
\]

Here the measure is finite and membership of the limit y in L² is derived by
Fatou. The proof establishes native uniform integrability using restricted
Hölder estimates and applies Vitali convergence; uniform integrability is not
an extra conclusion-containing premise. Apply (37) with x_n=r_n and
`y_n=√f_n v`. Bounded weak curvature pairings against all L¹ tests then give the
claimed potential-factor weak limit. Subtracting this from (36) identifies the
actual full factor `√f_n q_n`. Both factors and their limits have genuine L²
membership.

### Passing the signed terms and the complete action

The same product principle handles the coefficient of K in each signed term.
For the mixed term take `y_n=b_n f_n r_n'`; for the negative potential take
`y_n=b_n²r_n`. The pointwise limits come from the actual primitive and local
probe/derivative convergence. Their global L² bounds follow from

\[
 |b_nf_nr_n'|\leq2\Lambda|\sqrt w\,r_n'|,
 \qquad |b_n^2r_n|\leq4|r_n|. \tag{38}
\]

Consequently `b_n f_n r_n r_n'` and `b_n²r_n²` converge strongly in L¹ on the
whole physical interval. Pairing these with the uniformly bounded weak curvature
proves convergence of both literal signed integrals. Their limiting products
are proved integrable. The previously verified polar estimates enter through
global strong L² probe convergence; no additional tail assumption is introduced.

For each positive square, the supporting inequality

\[
 \int u_n^2\geq2\int u_nu_0-\int u_0^2
\]

and the identified weak pairing give lower semicontinuity. Adding both inequalities
and subtracting the genuinely converging signed integrals gives the full action
inequality. Concentration of positive operator energy is allowed. In particular,
no convergence of the whole remainder or action under oscillating curvature is
asserted; the diagnostic preceding this continuation remains relevant.

Finally, the mass-corrected coercivity bounds the smooth actions below by a finite
box-dependent constant, while the input sublevel bounds them above. A genuine
strictly increasing liminf subsequence is selected first. The initial joint
compactness producer then selects a further subsequence; all of its constraints,
weak derivatives, masses and convergences remain on the composed subsequence.
The new full-action inequality and scalar action convergence yield (35) for the
original sequence. No supplied weak pair, action minimum, compactness conclusion
or lower-semicontinuity conclusion is an input of this strengthened producer.

### Continuation native map and scope

| Role | Canonical source |
|---|---|
| Uniform integrability and strong L¹ products | `Analysis/L2PointwiseProducts.lean` |
| Weak/strong L² pairings and bounded varying multipliers | `Analysis/L2WeakMultipliers.lean` |
| Bounded curvature with varying strong L¹ tests | `Analysis/BoundedWeakPairingLimits.lean` |
| Weak square-integral lower semicontinuity | `Analysis/L2WeakLowerSemicontinuity.lean` |
| Actual uniform graph-coordinate bounds | `Geometry/AreaSublevelGraphBounds.lean` |
| Identified derivative-part weak limit | `Geometry/AreaDerivativeProductLimit.lean` |
| Curvature factor and both signed integral limits | `Geometry/AreaCurvatureProductLimits.lean` |
| Both full weak factors and complete-action LSC in the area topology | `Geometry/AreaActionLowerSemicontinuity.lean` |
| Actual constrained joint limit satisfying (35) | `Geometry/AreaJointActionCompactness.lean` |

The nine leaves add 18 public theorems. Native continuation evidence is recorded
in `docs/evidence/phase2-round-4-continuation/`; the initial `0fe2595` source and
receipt remain unchanged. One configured outer review remains pending for the
combined Round 4 packet. This closes the native limiting-action checkpoint;
it does not establish unrestricted smooth recovery or identify C_rot.

## Round 4 recovery: actual smooth approximants of produced joint limits

The new native headline
`AreaProfile.exists_joint_weak_limit_with_smooth_geometric_recovery` starts from
an original **smooth** normalized sublevel sequence, with varying positive box
witnesses and their actual ratio at most C. It produces the previous joint weak
limit and original-sequence action liminf inequality, together with a constructed
smooth recovery sequence. Both moments and the original ratio hold exactly at
every recovery index. A positive normalization gives physical mass exactly one;
the tied geometric producer returns actual smooth sphere metrics and physically
nonzero original forms whose dissipations converge to `2π A(K₀,r₀)`.

The source inputs are globally smooth K_n and r_n, as required for the original
geometric class. The previous continuous-curvature/C² compactness and LSC APIs
are unchanged. No symmetry, monotonicity, prescribed contact pattern, or new pole
value/derivative condition enters this construction.

### Global graph approximation and exact constraints

We use a native Hilbert-space convex approximation theorem, proved from geometric
separation and Riesz representation. A weakly converging Hilbert sequence admits
finite convex combinations from each tail converging in norm. Applying this to
a finite product gives **one common coefficient family** for

\[
  (K_n,\ r_n,\ \sqrt w\,r_n',\ w\sqrt w\,r_n''),\qquad w=x(1-x).
\]

The corresponding raw L² representative theorem ties each Hilbert combination to
the literal sum of the original functions. Thus the approximating r has its actual
first and second derivatives, with global convergence in both weighted derivative
norms. This supplies endpoint approximation at both poles for these produced
limits without cutting off the probes or introducing a permanent trace condition.
The original sublevel bounds and local derivative convergence supply the weighted
first-derivative weak pairing; the other three pairings come from the joint limit.

For finite nonnegative coefficients a_i summing to one, define

\[
 K^a=\sum_i a_iK_i,\quad r^a=\sum_i a_ir_i,\quad
 \kappa^a=\sum_i a_i\kappa_i,\quad \Lambda^a=\sum_i a_i\Lambda_i.
\]

Then κᵃ>0, κᵃ≤Kᵃ≤Λᵃ, and Λᵃ≤Cκᵃ follow from the original witnesses.
Both moments remain 2 and 1 by linearity. Every approximant is smooth, including
the degenerate constant-curvature box. No mass-one assertion is made for these
unnormalized mixtures. Strong curvature L² convergence implies L¹ convergence;
a further actual subsequence yields almost-everywhere curvature convergence.
The same subsequence retains all graph convergences and exact constraints.

This is an alternative to separate curvature mollification and moment correction
for the displayed source sequences: finite convex mixtures already have smooth
curvature and exact moments. It proves recovery for each limit constructed from
these unrestricted original smooth sequences. It does **not** prove density for
every arbitrary member of the maximal weak-derivative graph. Any later enlargement
of the variational domain or variation class must justify the additional density
or admissibility it uses; the distinction is not an assumption of the final theorem.

### Relative warp control and the complete action

For integrable K,L with equal zeroth and first moments, the actual primitive obeys

\[
 f_K(x)-f_L(x)=-2\int_x^1(s-x)(K(s)-L(s))\,ds,
\]

as well as its original left-pole formula. Combining the two gives

\[
 |f_K(x)-f_L(x)|\le4x(1-x)\int_0^1|K-L|,
 \qquad |b_K(x)-b_L(x)|\le2\int_0^1|K-L|. \tag{39}
\]

These are native statements for integrable curvature, with both moment identities
explicit. Relative control in (39), rather than absolute uniform warp convergence
alone, controls the coefficient of the weighted second derivative.

The strong-graph continuity theorem assumes a fixed positive box, both exact
moments, curvature L¹ and almost-everywhere convergence, and strong convergence of
the three probe graph coordinates. It assumes neither approximant unit mass nor
an action sublevel. Bounded varying-multiplier convergence in L² handles the six
coefficients of the literal operator, signed terms and mass. In particular,
`f√f/(w√w)` and `2b√f/√w` are bounded by box-only constants; their pointwise limits
follow from the actual primitives. Both positive factors converge strongly in L²,
and genuine L² product convergence passes the signed integrals. Consequently the
**entire** six-entry action and weighted physical mass converge, with integrability
proved. No K′ potential or interface omission is used.

This strong recovery topology differs from the weak topology of the initial
oscillating sequence. The earlier curvature-oscillation diagnostic still prevents
claiming full-action continuity for that original weak sequence. Convex approximation
constructs a new sequence for which the stronger hypotheses are proved.

Mass convergence to one supplies a late positive-mass tail. Multiplication by the
literal `1 / sqrt(probeMass)` gives exact unit mass; the factors converge to one,
and quadratic action scaling preserves the action limit. The accepted realizer
is consumed with these same normalized probes and curvatures. Its actual coordinate
and inverse, reciprocal profile, closed-interval jets, sphere curvature and
same-metric dissipation equations are retained. Physical nonzero probe values
produce nonzero original meridional forms. No continuous family of realizers in
a variation parameter is asserted by this sequence construction.

### Recovery native map and remaining scope

| Role | Canonical source |
|---|---|
| Native Hilbert convex approximation, simultaneous finite family | `Analysis/HilbertConvexApproximation.lean` |
| Actual raw L² convex mixtures | `Analysis/L2ConvexApproximation.lean` |
| Strong varying multipliers and literal product integrals | `Analysis/L2StrongMultipliers.lean` |
| Two-moment relative warp and slope bounds | `Geometry/AreaRelativeWarpContinuity.lean` |
| Smooth finite mixtures, actual jets, exact moments and original ratio | `Geometry/AreaSmoothConvexity.lean` |
| Constructed simultaneous smooth graph approximants | `Geometry/AreaConvexGraphRecovery.lean` |
| Complete strong-graph action and mass convergence | `Geometry/AreaStrongGraphContinuity.lean` |
| Actual scalar recovery from displayed weak graph pairings | `Geometry/AreaScalarGraphRecovery.lean` |
| Literal normalization and tied nonzero original geometric recovery | `Geometry/SmoothAreaRecoveryNormalization.lean` |
| Original smooth sublevels produce the weak limit and geometric recovery | `Geometry/AreaJointSmoothRecovery.lean` |

The ten leaves add 14 public theorems. The source-bound native receipt is
`docs/evidence/phase2-round-4-recovery/receipt.json`; all 202 prior native leaves and
both earlier Round 4 receipts remain unchanged. The configured single Round 4
outer review remains pending for the combined packet. No recovery sequence or
limiting-action conclusion is assumed by the final original-sequence producer.

## Round 4 minimum: attain the original smooth infimum in a recoverable class

`AreaProfile.exists_recoverable_area_minimizer` now takes only a ratio cap C≥1
and produces a physically nonzero joint weak pair whose complete action equals
the infimum over the actual normalized smooth curvature/probe class. It is minimal
against every competitor in the explicitly defined recoverable weak class.
`exists_area_minimizer_with_geometric_recovery` additionally returns original
smooth nonzero metric/form realizations approaching that value, with all curvature,
coordinate, inverse, jet and dissipation equations retained.

This is a joint existence theorem. The new `smoothAreaInfimum C` is the variational
value of the smooth meridional problem, **not a determining characterization of
C_rot**. No value of that infimum, threshold selection or universal safety at a
new cap is inferred merely from its definition or attainment.

### Smooth problem, nonemptiness and a genuine minimizing sequence

`IsSmoothAreaCompetitor C K r` means globally smooth K and r, positive original
box witnesses κ,Λ with Λ/κ≤C, both exact moments 2 and 1, and actual probe mass one.
Its action-value set is bounded below by
`−actionMassCorrection(2/C,2C)` using the complete-action coercivity theorem and
nonnegative operator/probe-square energies. The round pair K=2, r=√3 has mass one
and action four. Thus the class is nonempty and its real infimum is finite.

Mathlib's actual sequence approaching the infimum supplies action values and
original smooth witnesses. A common late shift places them in action sublevel
five, since the round value bounds the infimum by four. Five is an auxiliary
bound derived from that round competitor and convergence, not a proposed sharp
constant or an arbitrary numerical cutoff in the main result. The headline
minimizer theorem has no sequence, sublevel bound or minimizing object as input.

### The precise recoverable class and action transfer

`IsRecoverableAreaCompetitor C K r p z` requires curvature L² regularity, genuine
parabolic weak derivatives, a positive a.e. original ratio box, both exact moments,
unit physical mass, and a sequence of original **unit-mass** smooth competitors
converging strongly in curvature L² and in the three probe graph coordinates.
Neither action convergence, a desired lower bound nor minimality appears in this
definition. Every original smooth competitor embeds with its actual derivatives
and a constant sequence; the class excludes zero physical mass.

`IsRecoverableAreaCompetitor.exists_action_recovery` extracts an actual a.e.
curvature subsequence from strong L² convergence, derives the relative primitive
and strong-graph continuity hypotheses, and proves integrability plus convergence
of the complete action. Hence every member's weak action is at least the original
smooth infimum. This is a proved action consequence of the graph topology.
It is not a density theorem for every arbitrary member of the maximal weak graph.

For the limit of the minimizing sequence, the previous joint compactness/LSC
producer gives action at most the smooth infimum. Its convex recovery sequence
has strong graph convergence before normalization. The new scalar-multiplication
lemma proves that multiplication by the actual positive normalization factors,
which tend to one, preserves all three graph convergences with the **actual**
first and second derivatives. Consequently the produced unit-mass limit belongs
to the stated recoverable class. Action recovery then gives the reverse inequality:

\[
 A(K_0,r_0)=\inf\{A(K,r): (K,r)\text{ is an original normalized smooth competitor}\}.
\]

Every other recoverable competitor has action at least this value, so the produced
pair is a joint minimum on this class. Its probe and first derivative are continuous
in the interior, and its probe is nonzero at an actual interior point. No smooth
regularity of the minimizer, zero eigenvalue, moment multiplier or extra endpoint
condition is claimed.

### Original geometric meaning and native map

The original-form consumer constructs the normalized competitor from the actual
original profile, its produced area normalization, original all-sphere curvature
box, and nonzero original smooth meridional form. It proves

\[
 \operatorname{smoothAreaInfimum}(C)\le
 \ell^2\frac{Q_g(h)}{\int |h|_g^2\,d\mathrm{vol}_g},
 \qquad \ell=\operatorname{ReciprocalArea.length}(D.a),
\]

for that same metric and form. The physical nonzero hypothesis supplies the
positive denominator/normalization. The area scale is the actual profile length;
an uncorrected quotient over arbitrary metric scales is not being minimized.
The established all-form Haar sign transfer remains separate and unchanged.

The geometric recovery engine returns original smooth metrics/forms with the
same ratio cap, nonzero forms and dissipation tending to
`2π * smoothAreaInfimum C`. It retains the whole realizer interface rather than
replacing its metric, coordinate or probe by an unrelated witness. This sequence
statement supplies neither smooth attainment nor a continuous family in a variation
parameter.

| Role | Canonical source |
|---|---|
| Scalar multiplication in the actual strong graph topology | `Analysis/ParabolicGraphConvergence.lean` |
| Smooth competitor, finite infimum and actual minimizing sequence | `Geometry/SmoothAreaInfimum.lean` |
| Recoverable weak class, smooth embedding and proved action recovery | `Geometry/RecoverableAreaCompetitor.lean` |
| Actual physically nonzero weak minimum equal to the smooth infimum | `Geometry/AreaJointMinimum.lean` |
| Original geometric recovery; four exact limit ties strengthened in Round 5 | `Geometry/AreaMinimumGeometry.lean` |
| Original-form quotient comparison with exact physical scale | `Geometry/NormalizedAreaInfimum.lean` |

The six leaves add 21 public theorems and four definitions. Native evidence is in
`docs/evidence/phase2-round-4-minimum/`. All 212 prior native leaves and their
receipts are preserved. The single configured outer Round 4 review remains pending.

## Round 4 variation: the actual minimum satisfies the complete weak probe equation

`exists_recoverable_area_minimizer_weak_probe_equation C hC` now produces the
actual joint minimum together with its first justified necessary condition.
For every globally smooth real probe direction s, with no compact-support or
pole trace restriction, it proves

\[
 B_K(r,s)=\lambda\int_0^1 f_Krs,\qquad
 \lambda=A_K(r)=\operatorname{smoothAreaInfimum}(C).
\]

Here r has genuine weak derivatives p,z and the pairing is the literal complete
polarization

\[
 B_K(r,s)=\int_0^1\left[
 f q_r q_s-\frac{Kbf}{2}(rs'+sp)
 +\left(K^2f-\frac{Kb^2}{2}\right)rs\right],
 \quad q_r=fz+2bp-Kr,\quad q_s=fs''+2bs'-Ks.
\]

The curvature and primitives are the same actual K,f,b of the produced object.
Both potential terms and the mixed term are retained. No K′ potential is used
for the merely measurable limiting curvature. The theorem asserts a weak equation,
not a classical fourth-order pointwise equation or extra endpoint/interface laws.
Its eigenvalue is the actual minimum value; it is not assumed to vanish.

### Feasible variations in the actual class

Weak first derivatives are proved closed under addition and real scalar
multiplication by their integrable compact-test identities. Applying these laws
to both derivatives and to the weighted L² graph gives the corresponding genuine
second-order weak graph operations. For an actual smooth approximating probe,
adding a fixed smooth direction changes its actual first and second derivatives
by the derivatives of that same direction. All three strong graph differences
are unchanged by the common affine perturbation.

`IsRecoverableAreaCompetitor.normalized_probe_add_mul` proves that

\[
 \frac{r+ts}{\sqrt{m(K,r+ts)}}
\]

with the correspondingly scaled genuine weak derivatives belongs to the same
recoverable normalized class whenever its actual mass is positive. The proof
perturbs each original smooth recovery probe, extracts a common a.e. curvature
subsequence while retaining all strong limits, and proves convergence of the
perturbed physical masses. A late positive tail has literal positive normalization
factors converging to the limiting factor; the established scalar graph convergence
then supplies the required normalized smooth approximants. The curvature, both
moments and the original ratio witnesses remain unchanged. This is a proved
admissibility result, not a supplied feasible-path hypothesis.

The actual recoverable geometry supplies continuity of both primitives on the
closed interval, the common quadratic warp bounds, absolute slope bound, both
pole values and common a.e. curvature bounds. These follow from the displayed
smooth curvature approximation and the already proved primitive consumers.
They are not independent coefficient assumptions of the final minimum theorem.

### Integrability, mass correction and the minimum application

Polarization of three genuinely integrable complete densities proves integrability
of the pairing. Integral linearity then gives exact action and mass polynomials:

\[
 A(r+ts)=A(r)+2tB_K(r,s)+t^2A(s),\qquad
 m(r+ts)=1+2t\int_0^1 frs+t^2m(s).
\]

The public mass lemmas require only L² probes and the actual warp bound, without
irrelevant weak-jet premises. The action lemmas retain the tied weighted graph and
the actual curvature/primitive bounds. Derivatives follow from these polynomials;
there is no unjustified interchange of a derivative with a totalized integral.

The mass polynomial proves positivity in a neighborhood of t=0. Feasibility and
the actual joint minimum imply

\[
 A(r+ts)-A(r)m(r+ts)\ge0
\]

there, with equality at zero. Its derivative at zero is
`2 B_K(r,s) − 2 A(r)∫frs`, which must vanish. This proves the displayed weak
equation with the full probe-mass correction. The general minimum consumer is
then applied to the cap-only minimum producer, so the final theorem has no
assumed minimizing pair or directional local-minimum premise.

| Role | Canonical source |
|---|---|
| Genuine weak linearity and actual affine graph convergence | `Analysis/ParabolicWeakDerivativeAlgebra.lean` |
| Recoverable curvature subsequence and actual primitive bounds | `Geometry/RecoverableAreaGeometry.lean` |
| Complete weak pairing, integrability, action and mass polynomials | `Geometry/WeakAreaPolarization.lean` |
| Actual normalized smooth-direction feasibility in the weak class | `Geometry/RecoverableProbeVariation.lean` |
| Weak equation and application to the produced joint minimum | `Geometry/RecoverableProbeStationarity.lean` |

The five leaves add 23 public theorems and two definitions. Native evidence is in
`docs/evidence/phase2-round-4-variation/`. All 218 prior source leaves and receipts
are preserved. The single configured outer Round 4 review remains pending.

## Actual weak curvature inequalities from the joint minimum

The curvature continuation proves feasibility and the full one-sided necessary
condition for the same produced weak minimum. Its comparison curvatures are every
globally smooth J satisfying both exact moments and positive original box witnesses
with ratio at most C. No reflection, monotonicity or contact pattern is required.
The base curvature K and probe r need only belong to the stated recoverable weak
class, with their genuine weak derivatives p,z.

Write f=f_K, b=b_K, q=fz+2bp−Kr and set

\[
 dK=J-K,\quad df=f_J-f_K,\quad db=b_J-b_K,
 \qquad dq=df\,z+2db\,p-dK\,r.
\]

The literal full curvature derivative is the integral of

\[
\begin{split}
 V={}&df\,q^2+2f q\,dq
 -(dK\,b f+K\,db\,f+K b\,df)rp\\
 &-(dK\,b^2/2+K b\,db)r^2
 +(2K\,dK\,f+K^2df)r^2.
\end{split}
\]

`exists_recoverable_area_minimizer_weak_conditions C hC` produces the actual
nonzero unit-mass joint minimum, with action equal to the original smooth
infimum, global minimality in the recoverable class, the previous full weak
probe equation, and, for every such J,

\[
 0\le\int_0^1 V
       -\operatorname{smoothAreaInfimum}(C)\int_0^1(f_J-f_K)r^2.
\]

Only C≥1 is supplied to this producer. It does not assume a minimizing object,
feasible directional minima, a zero eigenvalue or a desired positivity conclusion.
The scalar objective retains the already proved original length-squared quotient
binding. This is a necessary condition, not a determining characterization.

### Actual feasible curvature paths and positive normalization

For integrable K,J on the physical interval, the original primitives obey the
exact affine laws for K_t=(1−t)K+tJ. Both moments remain exact for every real t.
`IsSmoothAreaCurvature` exposes the original smooth curvature constraints
independently of the probe; its conversion to/from the existing smooth competitor
keeps that competitor definition unchanged.

For t in [0,1], mixing the original lower and upper witnesses gives

\[
 \kappa_t=(1-t)\kappa_K+t\kappa_J>0,\qquad
 \Lambda_t=(1-t)\Lambda_K+t\Lambda_J\le C\kappa_t.
\]

The same mixing rule supplies witnesses for the weak pair and each smooth recovery
curvature. Auxiliary common bounds do not replace the original ratio condition.
Moreover f_K≤C²f_J by the actual quadratic warp comparisons. Since m(K,r)=1,
integrability and monotonicity give 1≤C²m(J,r), so m(J,r)>0. The affine mass law
then proves m(K_t,r)>0 throughout the entire convex segment, including t=1.
No positive-mass premise is left for the caller to supply.

`IsRecoverableAreaCompetitor.normalized_curvature_segment` constructs the actual
recoverable competitor

\[
 \left(K_t,\frac{r}{\sqrt{m(K_t,r)}},
 \frac{p}{\sqrt{m(K_t,r)}},\frac{z}{\sqrt{m(K_t,r)}}\right).
\]

Apply the same fixed segment to the original smooth recovery curvatures.
Their strong L² convergence and a common a.e. subsequence are retained; the
original probes and their three graph coordinates keep their strong convergence.
Full strong-graph mass continuity gives a late positive smooth tail. Its literal
normalization factors converge to the displayed factor; the scalar graph theorem
then proves normalized strong graph convergence and exact unit mass. Thus class
membership is constructed from actual smooth approximants, not postulated as a
feasible-path field. No new probe trace or pole condition enters.

### Integrability and the complete one-sided variation

The full density is exactly cubic along the affine curvature path. To justify
coefficient integration for nonsmooth K,r, the proof first establishes genuine
integrability of the actual complete densities at t=0,1/3,2/3,1. These are convex
curvature parameters with the proved physical coefficient bounds. Exact algebra
expresses each polynomial coefficient as a finite linear combination of those
integrable densities. In particular the linear coefficient is
`(-11 D_0 + 18 D_(1/3) - 9 D_(2/3) + 2 D_1)/2`, and it is exactly V above.
The four evaluation points are an exact polynomial identity, not a numerical
approximation or a finite-dimensional optimizer restriction.

Affine primitive laws and this coefficient integrability give the literal action
derivative at zero. The mass derivative is separately proved to equal
`integral (f_J−f_K)r²`; its interval integrability follows from the two actual
endpoint masses. No K′ expression or derivative of a totalized integral is used.
Although the polynomial identity holds for all real parameters, geometric
feasibility is asserted on the convex interval only.

Actual normalized minimality and quadratic probe scaling give
`A(K_t;r)−A(K;r)m(K_t,r)≥0` on [0,1], with equality at zero. Its derivative in
the inward tangent direction is nonnegative. Combining the full action and mass
derivatives proves the displayed inequality. Applying that consumer to the
previous cap-only producer gives both weak necessary conditions on one minimum.

| Role | Canonical source |
|---|---|
| Integrable-curvature affine primitive, moment and mass laws | `Geometry/AreaIntegrableAffine.lean` |
| Original smooth curvature constraints and convex mixed boxes | `Geometry/SmoothAreaCurvature.lean` |
| Complete weak curvature density, integrability and derivative | `Geometry/WeakCurvatureSegment.lean` |
| Positive mass and normalized recoverable convex segments | `Geometry/RecoverableCurvatureSegment.lean` |
| Actual minimum inequality and combined cap-only producer | `Geometry/RecoverableCurvatureOptimality.lean` |

The five leaves add 20 public theorems and three definitions. All 223 earlier
source leaves remain unchanged. Evidence for this continuation is recorded in
`docs/evidence/phase2-round-4-curvature/`; the single configured outer Round 4
review remains pending for the combined packet.

## An integrable curvature adjoint for the actual weak minimum

The next continuation gives the actual minimum's curvature inequality a legitimate
integral representation on the weighted weak domain. Let w=x(1−x), f=f_K,
b=b_K and q=fz+2bp−Kr. The three complete-action curvature coefficients are

\[
\begin{split}
 \alpha&=q^2+2fqz-Kbrp+K^2r^2,\\
 \beta&=4fqp-Kr(fp+br),\\
 \gamma&=-2fqr-br(fp+br/2)+2Kfr^2.
\end{split}
\]

They use the same original primitives and genuine weak derivatives. The new
coefficient theorem proves that alpha is measurable modulo null sets, w*alpha is integrable,
and beta and gamma are integrable. No unweighted integrability of alpha is
assumed or concluded. Substitution of actual derivatives recovers all three
existing smooth coefficients exactly.

### The weighted kernel and actual primitive identities

Define the unit-interval kernels

\[
 G(x,s)=\min(x,s)-xs,\qquad
 H(x,s)=\begin{cases}-s&s\le x,\\1-s&s>x.\end{cases}
\]

G is jointly continuous, H is jointly measurable, and on the physical square
`|G(x,s)|≤x(1−x)` and `|H(x,s)|≤1`. The slope branch at x=s is fixed explicitly.
For every integrable u and every x in [0,1], including both endpoints,

\[
\begin{split}
 \int_0^1G(x,s)u(s)\,ds
 &=x\int_0^1(1-s)u(s)\,ds-\int_0^x(x-s)u(s)\,ds,\\
 \int_0^1H(x,s)u(s)\,ds
 &=\int_0^1(1-s)u(s)\,ds-\int_0^xu(s)\,ds.
\end{split}
\]

Exact indicator integration proves these identities under genuine interval
integrability. For xi=J−K with both equal curvature moments, the affine moment
term vanishes. The original primitive formulas then give

\[
 f_J-f_K=2\int_0^1G(x,s)\xi(s)\,ds,\qquad
 b_J-b_K=2\int_0^1H(x,s)\xi(s)\,ds.
\]

The Dirichlet kernel records the warp's already fixed pole values. It imposes
no Dirichlet condition on the probe r or its weak derivatives.

For an s-finite first measure and a finite second measure, the generic Analysis
pairing theorem allows an almost everywhere measurable coefficient a with only
w*a integrable and an almost everywhere measurable kernel bounded by |w| on the
product measure. Its adjoint is integrable. A bounded almost everywhere measurable
test xi gives genuinely integrable primal and adjoint products and Fubini's
literal pairing identity. Product integrability is proved from the weighted
majorant before exchanging integrals. The coefficient itself need not be in L1.

For the physical coefficients, the graph supplies r, sqrt(w)*p and w*sqrt(w)*z
in L2. The actual bound f≤2Cw gives sqrt(w)*f*z in L2; bounded b,K then give
sqrt(w)*q in L2. Products of these factors control w*alpha, beta and gamma.
This also controls w*(alpha−lambda*r²) for every real lambda. The older smooth
Volterra pairing theorem requires continuous coefficients and is not silently
applied to this weaker domain.

### Full mass correction and the produced minimum

The actual L1 adjoint is

\[
 W_\lambda(s)=\gamma(s)
  +2\int_0^1G(x,s)(\alpha(x)-\lambda r(x)^2)\,dx
  +2\int_0^1H(x,s)\beta(x)\,dx.
\]

For every recoverable weak competitor and every original admissible smooth J,
`curvature_variation_eq_integral_adjoint` proves

\[
 \delta A_K[J-K]-\lambda\,\delta m_K[J-K]
   =\int_0^1W_\lambda(s)(J(s)-K(s))\,ds.
\]

All integrability follows from the primary class and curvature constraints.
Both original moments enter the primitive identities; the original box/ratio
keeps the comparison difference essentially bounded. The full mixed and positive
potential contributions remain in alpha, beta and gamma. No K′ potential,
pointwise classical derivative of the weak probe, or unweighted polar-tail
integrability premise is inserted.

`exists_recoverable_area_minimizer_with_curvature_adjoint C hC` takes C≥1 alone
and produces the same physically nonzero unit-mass minimum, its actual action
value and global minimality in the recoverable class, its full smooth-probe
equation, and

\[
 W_{\operatorname{smoothAreaInfimum}(C)}\in L^1(0,1),\qquad
 \int_0^1W_{\operatorname{smoothAreaInfimum}(C)}(J-K)\ge0
\]

for every current admissible smooth comparison curvature J. The mass multiplier
is pinned to the actual action/smooth infimum. This theorem does not extract
multipliers for the two curvature moments or assert pointwise switching signs.

| Role | Canonical source |
|---|---|
| Endpoint-valid kernels, bounds and integrable primitive formulas | `Analysis/UnitIntervalGreen.lean` |
| Weighted product integrability and genuine Fubini pairing | `Analysis/WeightedKernelPairing.lean` |
| Actual weak coefficients and their correct weighted integrability | `Geometry/WeakCurvatureCoefficients.lean` |
| Both-moment binding to the original warp and slope | `Geometry/AreaGreenPrimitives.lean` |
| L1 adjoint, full variation identity and actual minimum application | `Geometry/WeakCurvatureAdjoint.lean` |

The five leaves add 19 public theorems and six definitions; all 228 earlier
leaves remain unchanged. Native evidence is recorded in
`docs/evidence/phase2-round-4-adjoint/`. The same single configured outer Round 4
review remains pending.

## Round 4 nonsymmetric measurable-curvature recovery

The new primary measurable curvature class records almost-everywhere measurability,
an actual positive box κ≤K≤Λ with Λ/κ≤C, and the two exact physical moments.
Square integrability follows from that box. No symmetry, monotonicity or prescribed
contact pattern is part of this class.

The Analysis construction first approximates an L2 function smoothly in an enlarged
box. Clipping a native L2 approximation to the box decreases its error; native
uniform smooth approximation then restores smoothness with controlled enlargement.
Two nonnegative interior bumps supported in (1/8,3/8) and (5/8,7/8) have positive
masses and separated first-moment ratios. Their actual moment matrix has positive
determinant. Its explicitly inverted combinations ψ0,ψ1 have moment vectors
(1,0) and (0,1), compact interior supports, and a common finite bound B.

For an input with uniform margin δ and error tolerance ε, set
τ=min(δ,ε)/(2B+1). Smooth approximation has moment errors of absolute size at most
τ, by the probability-measure L2 bound. Adding the two corresponding multiples of
ψ0,ψ1 corrects both moments exactly. The correction is bounded by 2Bτ everywhere
and in L2. Thus the approximant stays in the original box and its total L2 error
is at most ε. Genuine integrability accompanies all moment identities.

For balanced moments (c,c/2), the mean lies in the original box. If c is either
box boundary, equality in the integral bound proves that the function is constant
almost everywhere, and exact constant recovery applies. Otherwise contraction
(1−t)K+tc creates the positive margin t*min(c−κ,Λ−c), preserves both moments, and
has explicitly controlled L2 error. The interior correction then gives arbitrary
accuracy in the original box. Choosing shrinking errors produces a single strong
L2 recovery sequence. This handles a degenerate box without division by its width.

`IsBoundedAreaCurvature.exists_smooth_recovery` specializes c=2 and returns the
same actual κ,Λ controlling the limit and every globally smooth approximant.
Every member has both original moments and the original ratio bound. It is a
nonsymmetric measurable-curvature density theorem, not maximal weighted-probe
graph density or a new smooth-attainment claim.

The actual joint minimum's adjoint is L1. Strong L2 recovery and a uniform essential
bound give convergence of its pairings against this L1 density, using the native
bounded-pairing theorem. Consequently
`exists_recoverable_area_minimizer_with_bounded_curvature_adjoint C hC` takes C≥1
alone and retains the physically nonzero unit-mass minimum, its full probe equation,
actual action value, and global recoverable minimality, with the adjoint inequality
now valid for **every bounded measurable admissible curvature**. This extends the
already justified full mass-corrected inequality by pairing continuity. It does not
assert continuity of the positive K² potential or the whole action under weak
curvature convergence, nor does it assume a new normalized weak path closure.

| Role | Canonical source |
|---|---|
| Smooth approximation with explicit box enlargement | `Analysis/SmoothBoxApproximation.lean` |
| Two fixed interior functions with invertible actual moments | `Analysis/InteriorMomentBasis.lean` |
| Quantitative exact-moment correction within a margin | `Analysis/InteriorMomentRecovery.lean` |
| Same-box balanced-moment recovery, including boundary means | `Analysis/BalancedMomentRecovery.lean` |
| Primary measurable physical curvature class and same-box recovery | `Geometry/BoundedAreaCurvature.lean` |
| Actual minimum's inequality for all bounded measurable comparisons | `Geometry/BoundedCurvatureOptimality.lean` |

These six leaves add 11 public theorems and one definition. All 233 prior leaves
remain unchanged. Native evidence is recorded in
`docs/evidence/phase2-round-4-nonsymmetric/`; the single configured outer Round 4
review remains pending for the combined packet.

## Round 4 moment qualification and genuine multipliers

The complete integrable curvature adjoint now has two **derived** moment
multipliers. This step uses the actual measurable-comparison inequality of the
produced minimum; neither multipliers nor constraint qualification are supplied
as hypotheses of the cap-only producer.

At a fixed positive box κ≤K≤Λ with κ<2<Λ, the constant curvature two is a strictly
interior feasible point for both physical moments. The already constructed
interior smooth moment basis gives perturbations 2+uψ0+vψ1. A quantified neighborhood
of (u,v)=(0,0) stays inside the box and changes the moments by exactly (u,v).
Qualification therefore does not require the minimizing curvature itself to have
a region strictly between its obstacles.

`Analysis.exists_box_moment_multipliers` proves the general balanced-moment
linear optimization theorem for any integrable real weight W on (0,1). Its convex
strict epigraph records the two moment deviations and the cost deviation. Actual
constrained minimality excludes the origin. The explicit moment perturbations
produce a nonempty open subset of this epigraph. Native Hahn–Banach separation
then gives a nonzero normal. Its cost coefficient is nonpositive by the vertical
ray, and cannot vanish: the two-sided moment neighborhood would force both other
coefficients to vanish as well. Normalizing this strictly negative coefficient
produces real numbers a,b and proves the literal unconstrained-box inequality

\[
 \int_0^1 (W(x)-a-bx)(J(x)-K(x))\,dx\ge0
\]

for every measurable J in the same box. Boundedness and integrability justify
every moment, cost, mixture and subtraction identity.

`Analysis.box_variational_inequality_iff` proves, for an arbitrary measure, that
this box inequality is equivalent to the a.e. conditions

\[
 K>\kappa\ \Longrightarrow\ W-a-bx\le0,\qquad
 K<\Lambda\ \Longrightarrow\ W-a-bx\ge0.
\]

The proof uses a genuinely measurable extreme selector built from a measurable
representative of the weight. Its nonpositive integrand has zero integral and
therefore vanishes almost everywhere. All pairings are integrable; zero measures
and degenerate boxes require no artificial exception or nonemptiness hypothesis.

`IsBoundedAreaCurvature.exists_strict_box` derives the required original witnesses
for every C>1. The mean bound gives κ≤2≤Λ. If either endpoint equals two, integral
equality forces K=2 a.e.; the box [1+1/C,C+1] then has ratio C and contains two
strictly. Otherwise the supplied box is already strict. At C=1, the original
ratio and mean force K=2 a.e.; the final producer uses [2,2], whose normal-cone
conditions carry no switching information.

`exists_recoverable_area_minimizer_with_moment_multipliers C hC` takes C≥1 alone.
It returns the actual physically nonzero unit-mass joint minimum, its full probe
equation and actual action value, global minimality in the recoverable class,
the integrable complete adjoint with mass multiplier equal to that action, an
original positive ratio box, and the two moment multipliers with the a.e. signs
above. The box is strictly mean-feasible whenever C>1; cap one is handled exactly.
No independent jets, omitted action terms, smoothness of the adjoint or prescribed
pole data are introduced.

| Role | Canonical source |
|---|---|
| Arbitrary-measure box inequality and a.e. complementarity equivalence | `Analysis/BoxVariationalInequality.lean` |
| Actual two-moment qualification, separation and multiplier extraction | `Analysis/BoxMomentMultipliers.lean` |
| Original positive ratio witnesses and cap-one degeneracy | `Geometry/AreaCurvatureBoxQualification.lean` |
| Genuine multipliers and signs for the cap-only produced minimum | `Geometry/AreaMomentMultipliers.lean` |

The four leaves add six public theorems and no definitions. All 239 previous
leaves remain unchanged. Native evidence is recorded in
`docs/evidence/phase2-round-4-multipliers/`. The same single outer Round 4 review
remains pending.

## Round 4 actual Euler fluxes and natural pole laws

The actual joint minimum now has globally absolutely continuous flux
representatives on the closed physical interval. The full smooth-test equation
produces these representatives and their endpoint laws; no trace condition is
added to the probe or its first weak derivative.

For the original primitives f,b, the tied weak operator q=fz+2bp−Kr and the actual
mass multiplier λ, the literal complete pairing gives the coefficients

\[
 U=f^2q,\qquad V=2fbq-\tfrac12 Kbfr,
\]
\[
 H=-fKq-\tfrac12 Kbfp+(K^2f-\tfrac12 Kb^2)r-\lambda fr.
\]

All three are globally integrable. This is proved before splitting their
integrals: the complete Lagrange pairing with the genuine smooth jets of 1, x and
x² isolates H, V+xH and 2U+2xV+x²H. Bounded coordinate multiplication on (0,1)
then gives separate integrability of H,V,U. The curvature may remain merely
bounded measurable, and the probe derivatives remain the genuine weak ones.
Every mixed and potential term and the mass correction are retained.

The resulting equation is

\[
 \int_0^1(U s''+V s'+H s)=0
 \quad\text{for every globally smooth }s.
\]

`Analysis.second_order_weak_euler_flux` proves a general L1 reconstruction on any
ordered bounded interval a≤b, including a=b. Define the actual primitives

\[
 P(x)=-\int_a^x H(t)\,dt,\qquad
 A(x)=\int_a^x(V(t)+P(t))\,dt.
\]

The constant test gives ∫H=0. Native integration by parts for absolutely
continuous primitives then gives ∫H s=∫P s′. Smooth antiderivative tests reduce
the equation to a first-order weak identity. Another primitive integration and
the native smooth-test separation theorem identify U=A almost everywhere.
The proof returns absolute continuity of both P and A, genuine a.e. derivative
laws P′=−H and A′=V+P, and

\[
 P(a)=P(b)=A(a)=A(b)=0.
\]

No limiting flux, regularity, primitive relation or endpoint value is a premise.
The unrestricted test class is essential here: compactly supported interior
tests alone would not yield these endpoint conclusions.

`weakProbeEulerFlux` and `weakProbeEulerMomentum` are the literal physical
primitives P and A at a=0. The actual minimum satisfies U=f²q=A a.e. and all four
zero pole traces. Since the original warp is continuous and strictly positive
inside (0,1), A/f² is a continuous interior representative of the actual weak
operator. The claim is an a.e. representative statement; no pointwise classical
meaning is assigned to an arbitrary weak second-derivative representative.

`exists_recoverable_area_minimizer_with_natural_flux C hC` takes C≥1 alone and
retains the same unit-mass, physically nonzero joint minimum, its full probe
equation, actual action and global recoverable minimality, original ratio/box,
cap-one conclusion and derived moment multipliers/complementarity. It adds the
actual flux primitives, absolute continuity, endpoint/derivative laws and
continuous interior operator representative. The original λ remains the actual
action/smooth infimum; zero action is not assumed.

| Role | Canonical source |
|---|---|
| General L1 weak Euler reconstruction with actual primitives and natural traces | `Analysis/SecondOrderWeakEuler.lean` |
| Complete physical coefficient formulas, literal pairing identity and integrability | `Geometry/WeakProbeEulerCoefficients.lean` |
| Actual minimum flux primitives, pole laws and interior operator representative | `Geometry/WeakProbeEulerFlux.lean` |

The three leaves add five public theorems and five definitions. All 243 previous
leaves remain unchanged. Native evidence is recorded in
`docs/evidence/phase2-round-4-flux/`. The same single outer Round 4 review remains
pending.

## Exact frontier and next target

Phase I is COMPLETE; Phase II is OPEN. The actual joint weak minimum now has
its full probe equation, derived moment multipliers with a.e. curvature box
complementarity, and two actual absolutely continuous Euler fluxes with natural
zero pole traces. The actual weak operator has a continuous representative on
the open physical interval. No condition on the endpoint values of r or p is
introduced.

Next analyze the remaining local regularity and coupled first-order relations
using these actual fluxes and the tied weak derivatives. Any curvature regularity,
interface structure, further weighted-probe recovery/normalized-pair closure or
original geometric path transfer used must be proved. Test the decisive global
comparison before expanding a structural family. The current statements do not
supply symmetry, a fixed switch count, smooth attainment or a zero eigenvalue.

T8–T10 still require a genuinely determining characterization and justified
selection, universal complete-action safety, original smooth negative witnesses
below every strictly larger cap, and precise unrestricted endpoint safety and
attainment scope. Necessary conditions and flux regularity do not identify C_rot.
Final native, independent-review, research/manuscript and delivery gates remain
mandatory; no required original-plan task is deferred.

## Round 5: same-minimum recovery and a complete-action comparison

The single Round 4 outer review at `a65205d` verified the 71-leaf direct-method
and necessary-condition development. Its M1 finding concerned two convenience
recovery conclusions: action convergence alone did not identify recovery of the
particular displayed minimum. Earlier joint recovery and minimum existence were
sound. The creation-time pending-review statements above are historical.

`IsRecoverableAreaCompetitor.exists_action_recovery` now returns all four strong
L² limits for its exact returned subsequence: curvature, probe, `sqrt(w)` times
its actual first derivative, and `w sqrt(w)` times its actual second derivative.
The outer action/mass integrability conjunctions remain in place.
`exists_area_minimizer_with_geometric_recovery` carries them to the exact shifted,
literally normalized tail appearing in its metric/form equations. There is no
second unrelated sequence. The public-consumer native driver extracts these four
limits, the same original form and both jets, actual curvature and dissipation,
and applies the new weak identity to the same displayed minimum. In particular,
negating the recovering sequence can no longer preserve convergence to a fixed
nonzero displayed probe merely because its quadratic action is unchanged.

Write `f=warp K`, `b=warpSlope K`, `w=x(1-x)`, and `q=fz+2bp-Kr` for the tied
weak derivatives `p=Dr`, `z=Dp`. For every globally smooth multiplier u the
complete algebraic identity is

\[
 A_K[ru]-B_K(r,ru^2)
 =\int_0^1 f\,[fru''+2(fp+br)u']^2
       -2f^2rq\,(u')^2.
\]

Here A is the literal complete action and B its full polarization. The mixed
`-Kbfrp` and potential `(K²f-Kb²/2)r²` contributions cancel in this difference;
they have not been dropped from either original expression. The pointwise
algebra theorem is explicitly about supplied jets; analytic consumers tie every
jet to the same actual or weak probe derivative.

Smooth multiplication preserves the genuine weak derivative graph:

\[
 D(ru)=pu+ru',\qquad D^2(ru)=zu+2pu'+ru''.
\]

The weak product rule uses compactly supported smooth test products. Its three
weighted graph coordinates are finite sums of bounded continuous coefficients
multiplying the original coordinates. The same formulas prove strong graph
continuity for actual smooth recovery probes. Applying the multiplier to a
single recovery sequence, then normalizing a positive-mass tail, proves
recoverable-class membership with exact moments, ratio and unit mass. No endpoint
trace is imposed on r or p, and no maximal-domain density is assumed.

At the actual recoverable minimum, normalized paths with multiplier `1+t u`
give genuine multiplicative stationarity. Using the square multiplier yields

\[
 A_K[ru]-\lambda\int_0^1 f(ru)^2
 =\int_0^1 f\,[fru''+2(fp+br)u']^2-2f^2rq\,(u')^2,
 \qquad \lambda=A_K[r]=\mathrm{smoothAreaInfimum}(C).
\]

The public weak theorem also returns integrability of the signed remainder,
proved from the integrable complete action and pairing densities. No sign of
r or q, classical smoothness of the weak minimum, or zero value of λ is inferred.

For smooth admissible K, a globally smooth reference r that is positive on
**[0,1]**, satisfies the actual Jacobi equation `J_K r=λr` there, and has
`L_K r≤0` there, gives

\[
 \lambda\int_0^1 f s^2\le A_K[s]
 \quad\text{for every globally smooth }s.
\]

The proof extends the smooth quotient s/r from the closed physical interval,
retains its actual first and second derivatives, and uses the complete Green
identity with vanishing geometric pole flux. Positivity is required only on
that interval. The certificate has no universal-inequality premise. The round
reference K=2,r=1 supplies a nonvacuous application with λ=4.

Two exact native tests delimit the proposed route. For K=2 and r=x−1/2,
`Lr=−10r`, `Jr=100r`, and `r Lr≤0`, but the interior node prevents smooth quotient
coverage. The test s=1 has mass 1/3 and complete action 4/3, contradicting an
all-probe bound with λ=100. This is a higher eigenfunction, not a minimum or zero
mode. Separately, r=1+x is positive on [0,1] but `Lr=2−10x` is positive at x=1/10.
It is nonstationary: `Jr=−44+100x` is not any scalar multiple of r on the interval.
This second example rules out deriving the operator sign from positivity alone;
it makes no claim about the sign of an actual minimizing eigenfunction.

The five new leaves add eight public theorems and no definitions. The 244
unchanged leaves of the reviewed 246-leaf parent, all 175 Round 3 leaves and all
149 Phase-I leaves are preserved; only the two identified recovery APIs change.
Source, signature, linter and actual axiom evidence is recorded in
`docs/evidence/phase2-round-5/`. The single configured Round 5 outer review is
pending. The accepted Phase-I manuscript is untouched.

## Current frontier after the comparison test

Phase I is COMPLETE; Phase II remains OPEN. The conditional fixed-geometry
comparison and actual-minimum identity do not give a reference of the required
sign/regularity, cover all curvature geometries at a cap, or select a threshold.
The exact nodal test forbids replacing these obligations by an arbitrary
stationary branch. Next prove or refute the nonvanishing/operator-sign and coupled
regularity properties actually needed for a uniform determining argument. Any
alternative route must retain global sufficiency and justified selection.

T8–T10 still require a genuinely determining characterization, universal scalar
safety and its all-original-form Haar transfer, smooth original negative witnesses
with ratio below every strictly larger cap, and exact unrestricted endpoint
safety/attainment. Further domain/interface/geometric-path bridges must be proved
when used. Final research/manuscript, native and independent-review gates remain
mandatory. No original-plan obligation is deferred or declared complete.


## Round 5 continuation: local weak regularity and the sign problem

The comparison checkpoint at `13dbfd3` is preserved. Its remaining reference-sign
and regularity conditions cannot be supplied by naming the actual minimum a
ground state. This continuation derives the local calculus needed to read the
coupled equations and determines exactly what an actual meridional source sign
implies in the smooth physical domain.

For `HasWeakDerivOn (a,b) r p`, the new native primitive theorem proves

\[
 r(x)=d+\int_c^x p(t)\,dt \quad\text{a.e. on }(a,b),\qquad c\in(a,b).
\]

Only local L¹ is assumed. A normalized compactly supported bump and the compact
primitive of a zero-mean test first show that a function with zero distributional
derivative is constant a.e. The actual local integral primitive has weak
derivative p by absolutely continuous integration by parts on an interior compact
interval enclosing the test. Every integral used there is proved integrable on
that interval. Continuous representatives then obey pointwise FTC, local absolute
continuity, a.e. genuine differentiation and, when p is continuous, a classical
first derivative and C¹ regularity. Countably many rational interior intervals
supply the a.e. derivative statement on the whole open domain.

Applying this twice to the parabolic graph shows that any continuous probe
representative is C¹ on (0,1), independently of the chosen weak derivative
representatives. Consequently, for every c strictly inside (0,1), there exist no
p,z such that `|x−c|` has the stipulated second weak graph. The linear probe
`x−c` itself embeds smoothly. This is an exact obstruction to using absolute
value as a general admissible sign reduction, not a statement that a produced
minimum is nodal. The endpoint distinction is real: `|x|` does belong to the graph
on (0,1), with weak derivatives 1 and 0. No pole smoothness condition was added.

For the actual recoverable curvature, the accepted weak primitive laws are reused:
`Df=b` and `Db=−2K`. The new weak FTC makes f classically differentiable with
derivative b in the interior and gives b local absolute continuity with its actual
a.e. derivative. No K′ exists or is needed in this argument.

Let λ be the actual unit-mass minimum action, P its literal Euler flux, A its
literal Euler momentum, and q=A/f². The continuous minimum representatives satisfy

\[
 \begin{aligned}
 r'&=p,\\
 p'&=(q-2bp+Kr)/f,\\
 q'&=(P-Kbfr/2)/f^2,\\
 P'&=fKq+Kbf p/2-(K^2f-Kb^2/2)r+\lambda fr.
 \end{aligned}
\]

The first identity holds at every interior point. The other three are genuine
a.e. `HasDerivAt` statements; p and q are absolutely continuous on every compact
interior interval, and r is C¹ there. The q field is the canonical A/f², a.e.
equal to the original tied weak operator. Its local absolute continuity follows
from A's already proved global absolute continuity and the C¹ reciprocal of the
strictly positive interior warp. The global P,A pole traces remain exactly the
previously proved natural flux traces. This theorem neither divides by f at a pole
nor assigns a classical derivative to an arbitrary weak second-jet representative.
The native consumer obtains this system from C≥1 alone and the accepted actual
minimum producer, with λ=`smoothAreaInfimum C`, unit mass and physical nonzero.

The smooth maximum principle is separate. For positive continuous K with both
exact moments and a C² probe r, it proves

\[
 L_Kr\le0\text{ on }[0,1]\Longrightarrow r\ge0\text{ on }[0,1],
 \qquad
 L_Kr<0\text{ on }[0,1]\Longrightarrow r>0\text{ on }[0,1].
\]

At an interior global minimum, r′=0 and r″≥0. At x=0 a closed-interval minimum
has r′≥0 and the actual operator is `4r′−Kr`; at x=1 it has r′≤0 and the operator
is `−4r′−Kr`. These physical first-derivative terms prove the same bound
`−Kr≤Lr` in all three cases. No Dirichlet or Neumann condition is imposed. A zero
probe with zero source shows why the non-strict version does not give strict
positivity. Combining the strict version with the delivered complete Picone
identity gives an all-smooth-probe bound from the actual Jacobi equation and
strictly negative meridional source, with no separately supplied probe sign.
The round reference r=1 verifies this certificate at λ=4.

Five new leaves contain fifteen public theorems and no definitions. All 251 prior
leaves and their receipts are unchanged. Native evidence is recorded in
`docs/evidence/phase2-round-5-regularity/`; the one configured Round 5 outer review
remains pending for the initial and continuation checkpoints. The accepted
Phase-I paper bytes are untouched.

## Current frontier after the local system

Phase II remains OPEN. The actual minimum now has the displayed local system,
but its meridional operator sign has not been established. The smooth maximum
principle requires C² regularity through both poles, which is not supplied by
interior C¹/local absolute continuity. It is therefore not silently applied to
the weak minimum. A valid weak pole maximum/comparison theorem or a justified
regularity bridge is still needed if this route uses that step. The absolute-value
corner theorem rules out a general positivity reduction by taking absolute value;
it does not rule out a positive minimum or an alternative comparison argument.

The decisive remaining work is to establish or refute the source-sign and
nonvanishing properties needed for a determining global route, while proving its
actual all-curvature coverage and threshold selection. Any spectral/structural
restriction, additional domain/interface/path bridge or endpoint use remains a
proof obligation. The original universal all-form safety, sharp smooth original
witnesses below every larger cap, exact endpoint/attainment and final manuscript/
evidence/review requirements remain active. No claimed cap or value of C_rot is
produced by this continuation.


## Round 5 weak poles: true derivative-flux traces and a weak maximum principle

The smooth maximum principle at `dd0a54e` cannot itself be applied to the weak
minimum through the poles. This continuation supplies a different proof in the
actual recoverable weak domain. It uses no absolute-value replacement of the
second-order graph and no new boundary value for r or p.

Define the literal derivative flux F=f²p. This is distinct from the existing
Euler flux P and momentum A. Interior C¹ regularity of f and local absolute
continuity of p give

\[
 F'=f(q+Kr)\quad\text{a.e.},\qquad q=fz+2bp-Kr.
\]

The source is globally integrable: the accepted weighted L² factors
`sqrt(f)q` and `sqrt(f)Kr` pair with `sqrt(f)`. The first-derivative graph condition
also gives integrability of F/x and F/(1−x). For either d=x or d=1−x and
w=x(1−x), the actual upper warp bound yields

\[
 |f^2p/d|\le(2C)^2|\sqrt w\,p|.
\]

The proof forms a genuine full-interval absolutely continuous primitive of the
integrable source, based at 1/2, and identifies it with F on (0,1) by local FTC.
A continuous function G on [a,b] with G(x)/(x−a) integrable on (a,b) must satisfy
G(a)=0; otherwise its reciprocal is continuous on a smaller interval, making
1/(x−a) integrable, a contradiction. Reflection proves the right-pole version.
Applying both to the actual flux primitive forces both traces to zero. Only then
is that primitive identified with the literal F on [0,1], proving its absolute
continuity and genuine zero traces. Substitution of f(0)=f(1)=0 alone was not used
as a continuity or trace argument.

The generic divergence maximum principle uses a C¹ interior function r and a
continuous zero-endpoint flux G, locally absolutely continuous, with
`G=A r'`, A≥0, and a.e. `G'=S≤c r`, c>0. It imposes no probe endpoint limit or
value. Set `psi=Real.smoothTransition(-r)` and H=G psi. The test is bounded in
[0,1], vanishes at nonnegative r and is positive at negative r. Local absolute
continuity and the genuine derivative laws give H'≤0 a.e.; the diffusion term is
`-A*(r')²*smoothTransition'(-r)≤0`. Both endpoint limits of H are zero because
`|H|≤|G|`. Thus H is zero throughout the interior. Derivative uniqueness and
strict positivity of c exclude negative r a.e., and continuity upgrades this to
pointwise interior nonnegativity. This is first-order AC calculus, not a claim
that the test is an admissible second-order variational competitor.

The physical consumer supplies A=f², G=F, S=f(q+Kr) and c=fK. Positive original
curvature and warp imply c>0 a.e.; the required actual flux traces have just been
proved. Hence the continuous representatives of every recoverable competitor
satisfy

\[
 q\le0\text{ a.e. on }(0,1)\quad\Longrightarrow\quad
 r\ge0\text{ at every point of }(0,1).
\]

The actual cap-produced minimum is a native consumer; its same flux is produced
without any source-sign premise, and its probe is nonnegative (with a positive
interior point from physical nonzero) if its actual operator is nonpositive a.e.
That operator sign is not inferred from stationarity or minimality.

Exact domain tests check both reciprocal divergences and a normalized nonconstant
round probe r=sqrt(10)x. It has mass one and nonzero derivatives sqrt(10) at both
poles while its actual f²p flux has true zero traces. A further generic test permits
an arbitrary negative raw probe value at a pole while the interior conclusion
holds. Thus the weak result concerns the physical interior, not arbitrary raw
endpoint representatives. The accepted smooth result retains its own closed-
interval C² scope. No Neumann or Dirichlet probe condition has been introduced.

Four new leaves add five public theorems and one literal flux definition. All
256 prior leaves and receipts are unchanged. Native evidence is in
`docs/evidence/phase2-round-5-weak-poles/`; the single Round 5 outer review remains
pending for all three checkpoints. The accepted Phase-I paper stays unchanged.

## Current frontier after weak pole comparison

The weak nonnegativity bridge under an a.e. source sign is now proved in the
actual domain, without global C² regularity. It still does not establish the
minimum's operator sign or strict interior nonvanishing, nor does it justify
quotient coverage of every smooth probe in the weak complete Picone identity.
Those are the next route-specific obligations; further pole, density, interface
or geometric-path results must be proved only when used.

The determining characterization and justified selection, universal complete
scalar safety and original all-form transfer, sharp original smooth witnesses
below every larger cap, exact unrestricted endpoint/attainment, and final
research/manuscript/native/independent-review gates remain mandatory. No new safe
cap or value of C_rot is claimed. Phase I is COMPLETE; Phase II is OPEN.

## Round 5 strict interior positivity under the actual source sign

The weak-pole comparison proves only nonnegativity from a nonpositive actual
operator. The next step now gives strict positivity on the physical interior
under that same source assumption. It uses no fourth-order eigen-equation and
no strict negativity of the source; actual unit mass excludes the zero solution.

The general strong maximum principle assumes a C¹ nonnegative function r on an
open interval, a continuous strictly positive diffusion coefficient A, a locally
absolutely continuous flux G=A r′, and an actual a.e. derivative satisfying
G′=S≤c r. The continuous upper coefficient c may have either sign. One positive
interior point forces positivity throughout the interval. No endpoint traces or
endpoint regularity are needed for this local propagation statement.

Here is the load-bearing zero-propagation argument. On a compact interior
interval [u,v], continuity and positivity give A≥m>0 and c≤C with C≥0. Absolute
continuity and the actual a.e. derivative inequality give, for s≤t in [u,v],

\[
 G(t)-G(s)\le C\int_s^t r.
\]

Integrability of the differentiated flux comes from its absolute continuity;
the source is not treated as a totalized integral without a domain argument.
If r(u)=0, its interior minimum has r′(u)=0 and hence G(u)=0. Put
R(x)=integral from u to x of r. The flux inequality and A≥m give
r′≤(C/m)R. For L=max(C/m,1),

\[
 H(x)=(r(x)+R(x))e^{-Lx},\qquad
 H'(x)=(r'(x)+r(x)-L(r(x)+R(x)))e^{-Lx}\le0.
\]

Both r and R are nonnegative, and H(u)=0. Thus r(v)=0. For a zero at v, the
backward primitive R(x)=integral from x to v of r and ordinary reflection give
the reverse propagation. The argument needs no transformation of an a.e.
curvature derivative under reflection. Any interior zero therefore contradicts
the supplied positive point.

The physical theorem first invokes the genuine weak-pole maximum principle for
the same recoverable competitor. If the resulting nonnegative probe had no
positive interior point, it would vanish a.e. on the physical interval and its
literal mass would be zero, contradicting mass one. The strong principle then
uses A=f², G=f²p, S=f(q+Kr), and the continuous upper coefficient c=2C f. The
original a.e. bound K≤2C and r≥0 justify S≤c r; no continuity or derivative of K
is introduced. Actual positive warp in (0,1) supplies strict interior diffusion.
Thus, for that same unit-mass object,

\[
 q\le0\quad\text{a.e.}\quad\Longrightarrow\quad
 r(x)>0\quad(0<x<1).
\]

The cap-only minimum producer is a native consumer, retaining its action equal
to the smooth infimum and the source sign as an explicit condition. This result
does not produce that sign from minimality or fix arbitrary endpoint values of
a weak representative.

An exact normalized round example distinguishes this result from the earlier
strict-source theorem. For v(x)=4x²−4x+3, native polynomial integration gives
mass(v)=57/35. Set alpha=1/sqrt(mass(v)) and r=alpha v. This is an original smooth
unit-mass competitor, and its actual operator is

\[
 q(x)=-88\,\mathrm{alpha}\,(x-1/2)^2.
\]

It is nonpositive and vanishes at the interior midpoint. The new physical theorem
still yields strict interior positivity. Domain checks also record that allowing
zero interior diffusion permits r=x², G=S=0 and c=1 with an interior zero and a
positive point elsewhere, while the identically zero probe cannot supply the
nonzero-point premise. These are native exact tests, not numerical evidence.

Two new leaves add two public theorems and no definitions. All 260 parent leaves
remain unchanged. The new source/native evidence is recorded under
`docs/evidence/phase2-round-5-strict-interior/`; the same single Round 5 outer
review remains pending for all four checkpoints. The Phase-I paper is preserved.

## Current frontier after strict interior comparison

Conditional strict interior nonvanishing is now delivered. The next substantive
route question is whether the actual minimum admits the required nonpositive
operator orientation. If that step is true, full-action quotient/endpoint
approximation must still justify coverage of every original smooth probe in the
weak Picone comparison. Strict interior positivity alone provides no uniform
positive lower bound through a pole and does not prove that coverage.

Every structural restriction and threshold selection actually used must be
proved. Determining C_rot, universal complete scalar safety and original all-form
transfer, sharp original smooth witnesses below every larger cap, precise
unrestricted endpoint/attainment and final research/manuscript/native/review gates
remain required. Phase I is COMPLETE; Phase II is OPEN.
