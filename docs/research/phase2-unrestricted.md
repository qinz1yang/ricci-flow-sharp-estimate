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

## Round 6: precise negative regime and sign symmetry

The Round 5 review at `9118e5a` accepts all four comparison checkpoints and both
recovery repairs in their stated scopes. Its next gate is to produce a one-sided
actual operator for an appropriately oriented joint minimum, or refute that
precise minimizing-object assertion. **That gate is not resolved in this packet.**
The new native results below establish two necessary inputs for the question;
they are not a substitute for its answer.

First, a global sign acts on the entire actual graph:

\[
 (r,p,z)\longmapsto(-r,-p,-z),\qquad
 q\longmapsto-q,\qquad m\longmapsto m,\qquad A\longmapsto A.
\]

`IsRecoverableAreaCompetitor.neg_probe` preserves the same curvature, original
box and ratio witnesses, both exact moments and unit mass. It uses the identical
recovering curvature sequence and negates the smooth probes. The accepted scalar
multiplication theorem passes all three strong weighted graph limits with their
actual derivatives to −r,−p,−z. The operator and complete-action sign laws retain
all density terms. By the unchanged action, actual global minimizing inequalities
also hold for the negated object. The native public consumer recovers that exact
negated graph, with all four strong limits and full-action convergence displayed.
No absolute-value replacement or independent weak jet is introduced. This proves
that orientation may be changed safely, not that either choice makes q one-sided.

Second, for every C≥1,

\[
 0\le\operatorname{smoothAreaInfimum}(C)
 \quad\Longleftrightarrow\quad C\in\operatorname{rotationalSafeCaps}.
\]

For the forward implication, the actual infimum lower bound gives nonnegativity
for each smooth unit-mass scalar competitor. The already accepted normalized Haar
transfer supplies safety for every original smooth one-form and represented
rotational metric. Conversely, original safe-cap membership controls every smooth
scalar competitor through the tied geometric realizer; nonemptiness of the smooth
class then gives the infimum bound. The hypothesis C≥1 is necessary for this
argument and is retained. There is no new definition of a threshold.

It follows that for every C strictly above the original rotationalThreshold,

\[
 \operatorname{smoothAreaInfimum}(C)<0.
\]

Indeed, a nonnegative value would put C in the original safe set and hence below
its supremum. The actual cap-produced minimum therefore has strictly negative
action, without assuming a zero eigenvalue or selecting a stationary branch.
The accepted strict inequality rotationalThreshold<C_CK supplies a nonempty
interval of such caps below C_CK. The native consumer returns a cap in that
interval, its actual unit-mass recoverable minimum, equality of its action to the
smooth infimum, and global minimality. It also checks the same minimum and its
full recovery after negation. This makes the relevant negative regime concrete
but still does not determine either its value or its operator sign.

## Round 6 route tests and precise unresolved step

The qualified curvature condition constrains the full corrected adjoint W−a−bx.
The accepted coefficients contain q², qz, qp and qr, together with the varying-
mass correction −lambda r² and Green pairings. Those inequalities cannot simply
be read as an inequality for q. A source-only local differentiation investigation
retains unsigned mixed terms and would require curvature smoothness/free-region
hypotheses not produced for the actual measurable minimum. No such hypothesis
has been added, and no new differentiated KKT theorem is claimed here. This
failed extraction attempt is not proof that every global use of curvature
optimality fails, and is not a counterexample to joint-minimum orientation.

A separate fixed-curvature investigation considered smooth exact-moment
K(x)=1/20+(663/20)(2x−1)^16, whose ratio is 664. It produced an auxiliary
rational-polynomial/parity proposal aimed at separating even and odd least-mode
values. That proposal has no native theorem, domain-closure proof or independent
acceptance in this project and is not used by any consumer. Its ratio is also
outside the needed cap interval below C_CK. It neither establishes nor refutes
the bounded-cap fixed-geometry claim or the actual joint-minimum claim. Higher
modes, arbitrary probes and numerical Ritz observations remain insufficient.
No outside theorem or sourced axiom was imported into the formalization.

The precise remaining question is whether actual globally minimizing pairs for
sufficient caps approaching rotationalThreshold from above within this interval
can be chosen with a one-sided q, after a single global sign change of all probe
jets. A valid alternative is a rigorous minimum-level counterexample and an
explicit change of global-comparison route. The sign-symmetry and negative-regime
theorems establish neither outcome. T9e remains active; Round 6's mainline success
condition is not met by these prerequisites alone.

If orientation is obtained, weak all-smooth-probe quotient/endpoint coverage still
requires its own proof. Every determining/cross-geometry/eigenvalue-sign argument,
original all-form safety theorem, sharp original smooth witness below every
larger cap, unrestricted endpoint/attainment result, and final manuscript/native/
independent-review/delivery gate remains mandatory. Phase I is COMPLETE; Phase II
is OPEN. Accepted Phase-I paper bytes and all earlier source/evidence are preserved.

## Round 6 continued route tests: no orientation conclusion

The following investigations are **provisional source-level derivations**. Their
analytic/domain steps have not been formalized or independently accepted. They
are recorded to delimit unsuccessful approaches; none is used as a Lean theorem,
a counterexample to joint-minimum orientation, or a determination of C_rot.

A proposed fixed-geometry shortcut would write B=−L, G=B inverse and
V=bK′/2, and demand a nonpositive off-diagonal kernel for G(V−lambda)G. A pole
calculation instead proposes a leading term

\[
 H_\lambda(\varepsilon,2\varepsilon)
 =\frac{K'(0)-\lambda}{8}\log(1/\varepsilon)+O(1).
\]

The argument uses the actual f=2x+O(x²) pole and a Green branch behaving as
1/(4x)+O(|log x|). If established on the physical inverse domain, flat polar
curvature and negative lambda would obstruct that uniform kernel sign. The
investigation also outlines flattening a negative smooth witness's curvature
near a pole and repairing both moments with two interior bumps, using strict
ratio room to retain a cap below C_CK. The required Green construction/asymptotic
and modification/domain bridges are not native results here. Even a proof of
this obstruction would reject only the kernel-sign shortcut: a lowest nullvector
can be one-sided without a nonpositive kernel. No orientation conclusion follows.

A separate attempt changes geometry and probe simultaneously. For smooth inputs,
choose a positive smooth t with integral of 1/t equal to one, set
Y(s)=integral from zero to s of 1/t, and write eta=t′/t. The proposed tied fields are

\[
 B=b-f\eta,\quad H=K+(b\eta+f\eta')/2,\quad
 F(Y(s))=f(s)/t(s),\quad K_{new}(Y(s))=t(s)H(s),\quad
 R(Y(s))=\sqrt{t(s)}\,r(s).
\]

Direct differential algebra gives the proposed operator transform
Q=q+(b eta/2−f eta²/4)r and q_new(Y(s))=t(s)^(3/2)Q(s). The physical pole slopes
make both moments automatic for smooth data. The original positive ratio box,
however, becomes a separate restriction on tH. The full transformed mass and
action, including all lower-order terms, would be

\[
 M_t=\int_0^1 fr^2/t,\qquad
 A_t=\int_0^1 t\{fQ^2+fH^2r^2-HBfrp-HBb r^2/2\}.
\]

To contradict a unit-mass minimum with value lambda, one must actually construct
a feasible t with A_t−lambda M_t<0 and justify recovery in the same cap. Neither
inequality nor recovery has been obtained from sign-changing q. Merely writing
the transformed weak graph and box is insufficient. Positive multiplication and
an increasing coordinate map also preserve any existing probe nodes.

The complete-flattening specialization illustrates the problem. For a smooth
strictly positive reference one can set t=(integral r²)/r², making R constant.
If this specialization retains the original cap below C_CK, the accepted CK
safety theorem would force its normalized action to be nonnegative, which is
larger than the original negative value. Thus flattening does not supply the
needed energy decrease even under extra favorable probe regularity. This is a
limitation of that construction, not a refutation of the actual sign assertion.

These bounded tests returned no sign producer and no joint-minimum counterexample.
The round's mainline gate remains unresolved. A next attempt must supply a new
global argument specific to the actual minimizing object, or a rigorous relevant
minimum-level refutation. It must not silently promote any unproved kernel sign,
transport feasibility, recovery or energy-lowering premise.

## Round 6 coupled search and second-variation test

The actual-minimum orientation claim remains unresolved. A bounded numerical
search found no candidate that refutes it, and a local second-variation test
produced no sign implication. The numerical results below are exploratory;
the full weak-path calculation is provisional. Only the explicitly identified
pointwise density algebra has fresh native evidence.

The search varied piecewise constant curvature on uniform cells and globally
polynomial probes with their actual first and second derivatives. It retained
both curvature moments and optimized the original lower box witness kappa with
kappa<=K<=C kappa. The warp and its slope were the literal primitives of that
same curvature. Cell Gaussian quadrature integrated the complete density and
physical mass, including both positive squares and both signed terms. For
polynomial degree d, d+2 nodes per cell suffice for exact integration in real
arithmetic; the implementation used floating arithmetic throughout. The
generalized least eigenvector supplied the probe, and the curvature gradient
included the varying-mass correction. No reflection symmetry or probe sign was
imposed. Orientation by the probe's mean occurred only when reporting results.

Thirty-six local searches covered 32/64/128 cells and probe degrees 10/20/24,
with caps 3, 4, 4.2, 4.8 and 4.93 in the combinations recorded in the evidence.
Twelve runs began at asymmetric extreme points of the same curvature polytope.
All reported local optimizer success, positive sampled probes and negative
sampled operators after the reporting orientation. The largest moment residual
was 2.23e-15 and largest box violation 3.59e-15. These residuals are floating
checks, not exact admissibility proofs. Representative seed-zero values are:

| Cells / probe degree | Cap | Computed normalized action | Largest sampled q |
|---|---:|---:|---:|
| 32 / 10 | 4.8 | -0.288865 | -2.553787 |
| 64 / 20 | 4.8 | -0.313330 | -2.539618 |
| 128 / 24 | 4.8 | -0.320013 | -2.530503 |
| 64 / 20 | 4.2 | -0.047170 | -2.641652 |
| 128 / 24 | 4.2 | -0.053274 | -2.621281 |

The changing values under refinement preclude treating these as certified
minimum values. Local optimizer success, agreement across starts and sampled
signs establish neither global minimality nor uniqueness, symmetry, pointwise
one-sidedness or a threshold. No C_rot estimate is asserted. Checks against the
round spectrum, direct complete-density evaluation and a fixed-vector Rayleigh
finite-difference gradient test passed. NumPy/SciPy and the scripts remained in
isolated scratch; project dependencies and pins were unchanged.

The independent source-level calculation considered compact smooth directions
psi,s with k=-psi''/2 and the tied path

\[
 K_t=K+tk,\quad f_t=f+t\psi,\quad b_t=b+t\psi',\qquad
 (r_t,p_t,z_t)=(r+ts,p+ts',z+ts'').
\]

Compact support gives both zero moments of k. It does not ensure that the path
stays in the original curvature box. Feasibility, recoverable-class membership
and the weak-path variation theorem still need formal proof for any direction
actually used. In particular, no free curvature interval is inferred from the
minimum. With h=psi', the actual operator expands as q_t=q+t a+t^2 c, where

\[
 a=fs''+2bs'-Ks+\psi z+2hp-kr,\qquad
 c=\psi s''+2hs'-ks.
\]

For the actual unit-mass value lambda, put

\[
\begin{aligned}
 V_0&=K^2f-Kb^2/2-\lambda f,& B_0&=Kbf,\\
 V_1&=2Kkf+K^2\psi-kb^2/2-Kbh-\lambda\psi,
 &B_1&=kbf+Khf+Kb\psi,\\
 V_2&=k^2f+2Kk\psi-kbh-Kh^2/2,
 &B_2&=khf+kb\psi+Kh\psi.
\end{aligned}
\]

The proposed full coefficient of t^2 in A_t-lambda m(t) is the integral of

\[
 Q=fa^2+2fqc+2\psi qa+V_0s^2+2V_1rs+V_2r^2
   -B_0ss'-B_1(rs'+sp)-B_2rp.
\]

Here m'(0)=integral(psi r^2+2frs). If g_1=(A_t-lambda m(t))'(0), the
normalized second derivative is 2 integral Q-2 m'(0)g_1. The qualified moment
conditions give g_1=integral(W-alpha-beta x)k. A one-sided feasible direction
may have g_1>0, in which case a negative second coefficient does not contradict
minimality. Second-order nonnegativity applies on the critical cone g_1=0;
arbitrary compact directions cannot be substituted for this condition. These
full weak-path assertions are source-level research, not new library theorems.

A separate native diagnostic does verify the exact pointwise identity, with
f,b,r,p fixed and D the canonical complete density,

\[
 D(f,b,K+tk,r,p,z+td)+D(f,b,K-tk,r,p,z-td)-2D(f,b,K,r,p,z)
 =2t^2 f\bigl((fd-rk)^2+(rk)^2\bigr).
\]

Substituting k=-psi''/2 gives the principal quadratic form

\[
 f(fs''+r\psi''/2)^2+fr^2(\psi'')^2/4.
\]

It is positive for a nonzero principal direction when f>0 and r is nonzero,
independently of the base q. Cancelling the first square leaves the second.
This rules out reading a q-sign condition from this principal test alone; it
does not rule out a global use of the full Hessian. The native diagnostic
asserts neither feasible variations nor a conclusion about a minimizing pair.

The missing step for this route is to construct, from sign change of the actual
q, a genuinely feasible critical direction and prove that the full integral
of Q is negative, retaining the mass correction and every lower-order term.
No such construction was obtained. A separate proposal to first produce an
actual zero-action critical pair would itself require a proof of existence and
regime relevance; a zero eigenvalue cannot be assumed. The Round 6 reviewer is
asked which exact minimum-level implication can justify the next step. T9e,
all-probe coverage and all determining/global/sharpness/endpoint gates remain
active. Source, output and scope bindings are recorded in the
[coupled-investigation record](../evidence/phase2-round-6-coupled/checkpoint.json).

## Round 7: the actual endpoint zero-action minimum

The Round 6 review accepts the prerequisite packet but finds the orientation
objective stalled. Its prescribed next step is now implemented: for the existing
original safe-set supremum C*=rotationalThreshold,

\[
 C_*\in\operatorname{rotationalSafeCaps},\qquad
 \operatorname{smoothAreaInfimum}(C_*)=0.
\]

`exists_zero_action_recoverable_area_minimizer` produces an actual recoverable
pair at C*, with unit physical mass, a nonzero interior probe value, continuous
interior probe and first derivative, zero complete action, and global minimality
against the full recoverable class. It returns the zero weak probe equation for
every globally smooth test, without endpoint restrictions, and a smooth sequence
with all four strong limits to that very K,r,p,z and action tending to zero.
No zero-value or operator-sign hypothesis occurs in either headline.

Endpoint safety uses the order structure of the actual nonempty bounded safe
set. Every 1<=D<C* is safe. If C*=1, the accepted cap-one theorem applies.
Otherwise contract each arbitrary smooth exact-moment curvature toward two,
keeping its arbitrary smooth probe fixed. For 0<t<1, the contracted positive box
has ratio strictly below C*, since

\[
 (1-t)\Lambda+2t<C_*((1-t)\kappa+2t)
\]

follows from Lambda<=C*kappa and C*>1. Both moments remain exact. Original scalar
safety at this smaller ratio and continuity of the complete action give endpoint
scalar safety; the accepted Haar transfer returns the original all-form result.
The proof does not use a CK plateau, a symmetry assumption, or probe normalization
along the contraction.

For zero value, choose C*<D<C_CK and caps
C_n=C*+(D-C*)/(n+1). Negative smooth unit-mass competitors exist at every C_n by
the actual negative-infimum theorem and nonemptiness of its value set. They lie
in the single cap D and action sublevel zero. Coercivity supplies a real lower
bound before the liminf comparison. The accepted joint compactness/recovery
producer gives a nonzero unit-mass limit with A_0<=liminf A_n<=0. Its same box
witnesses converge along one subsequence, and Lambda_n<=C_n*kappa_n passes to
Lambda_0<=C*kappa_0 with kappa_0>0. Keeping only the auxiliary D box would not
suffice.

`IsRecoverableAreaCompetitor.of_curvature_cap` closes this distinction. For a
recoverable pair at any cap and the same K admissible at a new cap, it recovers
K by smooth exact-moment curvatures in the new positive box, pairs them with the
existing smooth probe recovery, and takes a genuine curvature a.e. subsequence.
The strong graph theorem gives full action and mass passage. A positive-mass
tail is normalized by its literal inverse square root; graph scaling preserves
the same r,p,z and all actual derivative limits. No ordering of the two caps,
maximal-domain density or supplied action convergence is assumed. The degenerate
box and cap-one cases are included.

The resulting pair is genuinely recoverable at C*. Endpoint safety yields
0<=smoothAreaInfimum(C*)<=A_0<=0. Thus both quantities vanish, and the very same
limit is globally minimal. The public consumer applies the existing first-order
system and Euler-flux theorems to this pair: its multiplier is derived to be zero,
the canonical fluxes are absolutely continuous with natural zero pole traces,
and the weak operator agrees a.e. with the canonical interior representative.
The probe itself has no imposed boundary value or derivative.

Native source/root, required linters, exact signatures, actual axiom checks and
the silent public consumer pass; see the
[Round 7 evidence](../evidence/phase2-round-7/checkpoint.json). The single outer
review is pending. This proves endpoint safety and relaxed zero-action attainment,
not original smooth attainment or an identifying equation for C_rot. The next
sign question concerns existence of a suitable orientation of an actual endpoint
minimum. The earlier negative-near-threshold sign conjecture remains unproved
and unrefuted. All-probe coverage, determining selection, global comparison at
the determining value, original smooth sharpness and exact smooth equality/
attainment scope remain required. Phase I stays COMPLETE; Phase II stays OPEN.

## Round 8: the strict round gap and original smooth sharpness

The Round 7 outer review verifies the endpoint producer in its stated scope.
Round 8 adds four native theorems, with its own outer review still pending.
For round normalized curvature K=2, write f=warp K, q=L_K r,
m=integral(f r²), and G=integral(f²(r')²). The accepted square factorization
and weighted operator pairing give

\[
 A_K(r)=\int_0^1 f q^2,\qquad
 \int_0^1 f r q=-G-2m,\qquad
 0\le\int_0^1 f(q+2r)^2=A_K(r)-4G-4m.
\]

Consequently every smooth unit-mass round probe has action at least four.
Cap-one curvature equals two on the physical interval; the proof transports
this equality through its actual warp, slope, mass and action, without making
a false assertion about smooth extensions outside the interval. The existing
round constant probe attains four. Thus `smoothAreaInfimum_one` proves the
exact value four, and the already proved endpoint value zero yields
`one_lt_rotationalThreshold`. The native consumer applies the moment-multiplier
method directly to the same endpoint zero minimum. Strict mean qualification
does not assert a free curvature interval or an operator sign.

For any D>C*, choose C strictly between C* and D. The actual smooth action-value
set at cap C is nonempty and its infimum is negative, so it contains a negative
value. This supplies smooth K,r with the original positive box, both exact
moments and physical mass one. The original geometric realizer applied to these
very functions returns X,P,R, retaining both inverse identities, R=r composed
with X, the first and second probe jets, the all-sphere curvature equation and

\[
 Q_{P.\mathrm{metric}}(P.\mathrm{meridionalOneForm}(R))
   =2\pi A_K(r)<0,\qquad \Lambda/\kappa\le C<D.
\]

The returned metric is represented and its curvature box holds at every sphere
point, including both poles. Negative dissipation excludes the zero form in the
headline proof. The native consumer also checks the separate mass-based bridge:
if this original form vanished, its coefficient R would vanish on (-1,1),
continuity would extend this to [-1,1], and the exact forward probe equation
would make r vanish on [0,1], contradicting unit mass. No additional recovery
theorem or smooth endpoint extremizer is used.

### Endpoint sign selection: provisional route assessment

The main Round 8 objective remains unresolved. The following is exploratory
source-level analysis, not a new native theorem or a refutation of the exact
existential endpoint-sign target.

The actual zero-multiplier first-order system retains the terms involving Kb,
where b=f'. In a smooth diagnostic only, eliminating the canonical flux gives
L_K q=-(bK'/2)r and L_K r=q. The actual weak curvature is merely measurable;
one cannot insert K' or infer a cooperative system from zero action. In
particular, neither curvature monotonicity nor a sign of bK' has been proved.

Even granting an appropriate positive inverse of -L_K and recoverable solutions
u,v of L_K u=-q_+ and L_K v=-q_-, replacing r=v-u by w=u+v would give
L_K w=-|q|. But complete nullspace orthogonality would give
B(u,u)=B(u,v)=B(v,v)=b0>=0 and A_K(w)=4b0. The missing inequality is b0<=0,
as well as the actual component-domain and recovery producers. Generic inverse
positivity does not supply it. For example, the source-level matrix diagnostic
A=[[2,-1],[-1,2]], V=diag(-4,11) has positive inverse and
A²+V=[[1,-4],[-4,16]] positive semidefinite, yet its nonzero null vectors are
multiples of (4,1), whose -A image is (-7,2). This is an algebraic shortcut
obstruction, not a physical curvature example or a kernel-supported new result.

A further bounded investigation uses actual existing variation producers:
first normalize r+e s for a globally smooth s, then move curvature through
K_t=(1-t)K+tJ for an admissible smooth J. The two positive normalizations
combine to normalization of that same literal probe under K_t. This is a
source-level route to a feasible joint family at the original cap. The full
cubic curvature density and complete polarization would imply

\[
 F(t,e)=A_{K_t}(r+es)\ge0,\qquad
 F(t,\alpha t)=t d+t^2(e_2+2\alpha\ell+\alpha^2 a)+O(t^3),
\]

with a=A_K(s)>=0, d the actual full curvature-adjoint pairing, and e_2 the
complete second coefficient. When d=0 the necessary condition is
ell²<=a e_2. If the inverse-component direction were actually produced, it would
give ell(w)²<=4b0 e_2, still no upper sign on b0. When d>0, the first-order
term dominates. Strict moment qualification does not construct a nonzero
critical direction. The displayed unnormalized path K_t,r+alpha*t*s is affine.
Its normalized feasible representative generally has nonzero acceleration;
this calculation concerns F, whose sign is unchanged by positive mass
normalization. Differentiating the normalized action instead would require
those acceleration terms. Any different nonlinear path also needs its own
feasibility and complete second variation.

Thus no actual same-cap descent comparison under b0>0 has been constructed.
Producing such a comparison, or a different endpoint-specific selection
mechanism, remains the decisive research obligation. One nodal minimum would
not refute existence of another orientable joint minimum. No numerical starts,
assumed free region, principal-square shortcut or supplied-sign wrapper closes
this gap. The earlier nearby-negative sign conjecture remains unproved and
unrefuted.

The [Round 8 evidence](../evidence/phase2-round-8/checkpoint.json) distinguishes
the four native theorems from this provisional analysis. Specific all-smooth-
probe coverage, a genuinely determining characterization and selection,
comparison across all original geometries, precise original smooth endpoint
equality/attainment and all final review/manuscript gates remain required.
Phase I is COMPLETE; Phase II is OPEN.

## Round 9 first checkpoint: actual inverse domain and pole regularity

The Round 8 review accepts the strict round gap and original smooth negative
witnesses, but the endpoint sign objective remains open. Its prescribed next
child is the actual inverse split with simultaneous same-cap recovery. The
following are native prerequisites, not completion of that child.

Write f=warp K, b=warpSlope K and q=L_K r. The literal transformed function
y=f*r is absolutely continuous on [0,1], with y(0)=y(1)=0, y in L² and
y'=b*r+f*p in L². A generic first-weak-derivative theorem proves this using
the actual weak product, the linear pole bound on f, and square integrability
of r and sqrt(w)*p. Reciprocal-distance integrability forces the traces of the
absolutely continuous extension; substituting f=0 at a pole alone would not
establish them. The probe itself has no imposed endpoint value. For continuous
interior r,p, the same object's transformed derivative is locally absolutely
continuous and obeys

\[
 y''+(K/f)y=q\quad\text{almost everywhere on }(0,1).
\]

The actual f''=-2K law supplies the curvature term without differentiating K.
The public consumer applies both statements to the already produced zero
minimum, retaining its original recoverability and global minimality.

For smooth probes, the nonnegative square integral of f(q+kappa*r)^2 and the
accepted weighted operator pairing give the native estimate

\[
 \kappa^2 m+2\kappa G\le E,\qquad
 E=\int f q^2,\quad G=\int f^2(r')^2.
\]

The existing Hardy and derivative estimates then imply
integral(r²)+integral(w(r')²)+integral(w³(r'')²)<=M(kappa,Lambda)*E,
with M selected before every curvature and probe in that positive box. No
mass normalization, K′ bound or probe pole condition occurs. Separately,
w(x)r(x)²<=4*(integral(r²)+integral(w(r')²)) follows by applying the interval
pointwise estimate on [x/2,(x+1)/2]. This controls multiplication of curvature
L² errors by sqrt(w)*r in the upcoming inverse stability argument.

For pole regularity, finite C^n data on a closed interval are extended only
with that finite order: extend their within derivative inductively and
integrate, starting with continuous clamping. Weighted derivative averages
prove finite regularity of the released Hadamard factor. Factoring each of
two distinct simple endpoint zeros locally loses only one derivative.
The exact Dirichlet primitive gains two derivatives from its source. Dividing
by f therefore gives a one-derivative gain for the physical Green quotient,
whose endpoint values are its explicit weighted source moments divided by two.
The native consumer includes the merely continuous source |x-1/2|, so no
unproved smooth extension of finite-order source data enters this step.

The selected construction route now seeks the genuine contraction fixed point
of u=P_K(g+K*u), followed by this finite-order bootstrap and the accepted smooth
interval extension. The curvature row mass one half is the proposed contraction
mechanism and still needs its producer in the next packet. The weighted graph
estimate will support completion and stability for the actual weighted sources.
Neither smooth inversion nor simultaneous raw recovery is claimed by this
first checkpoint. The additional implication A_K(U+V)<=0 remains entirely
separate from existence of the inverse components.

The [native evidence](../evidence/phase2-round-9-prerequisites/checkpoint.json)
supports the preceding domain/estimate/regularity statements. It does not
identify C_rot, select an operator sign, establish arbitrary-probe coverage or
settle original smooth endpoint attainment. All original final gates remain.

## Round 9 second checkpoint: smooth inversion and graph completion

The actual Green map satisfies P_K K=1/2, including its explicit pole values.
Consequently u -> P_K(g+K*u) is a contraction on continuous functions on [0,1].
Its fixed point gains one derivative repeatedly through the finite-order pole
quotient theorem. Smooth interval extension then yields a global smooth probe
with -L_K u=g on the closed physical interval. The accepted maximum principle
proves nonnegativity for nonnegative sources and uniqueness of this probe on
[0,1]. Its extension outside that interval is not claimed unique. Zero sources
are included; neither physical probe pole values nor a K′ bound is prescribed.

For w=x(1-x), write G(u)=integral(u²)+integral(w(u′)²)+integral(w³(u″)²).
The weighted pointwise estimate and the exact equal-moment primitive laws give
integral(w*(L_K u-L_J u)²)<=60*G(u)*integral((K-J)²).
Combining this with the inverse graph bound proves
G(u-v)<=M*(2*integral(w*(g-h)²)+120*G(v)*integral((K-J)²))
for the actual inverse equations -L_K u=g and -L_J v=h. Only K requires the
stated positive box; M depends on that box and precedes all other data.

Separately, a Cauchy sequence of the three canonical weighted L² coordinates
has a limit with both genuine weak derivatives. Compactly supported weighted
test pairings pass the weak identities, and continuous interior representatives
are chosen afterwards. All three full-sequence strong limits are retained.
This statement does not assume or produce mass one.

The [native checkpoint](../evidence/phase2-round-9-inverse/checkpoint.json)
establishes these four theorems. Turning the quantitative stability into a
common-sequence inverse split, proving the complete action/mass passage and
normalizing positive-mass combinations remain the active child. The additional
geometry-specific inequality A_K(U+V)<=0 and all determining/global/endpoint
requirements remain open.

## Round 9 final packet: simultaneous inverse recovery

Starting with the actual recoverable endpoint probe, choose one existing
smooth curvature/probe recovery with curvature convergence also almost
everywhere. The three strong graph limits imply sqrt(w)*L_Kn(r_n) converges
strongly to sqrt(w)*q for the literal weak q=L_K r. This uses the actual
relative warp and slope primitives and bounded L² multipliers, without K′.

For epsilon_n=1/(n+1), the smooth regularizer
R_epsilon(t)=(sqrt(t²+epsilon²)+t)/2 gives nonnegative smooth sources
g_n^+=R_epsilon_n(q_n), g_n^-=R_epsilon_n(-q_n). Their difference is exactly
q_n and they converge in weighted L² to max(q,0), max(-q,0). This construction
does not require unweighted square integrability of q.

Solve -L_Kn U_n=g_n^+ using the actual smooth inverse. Its stability estimate
gives Cauchy convergence in all three canonical L² graph coordinates: comparing
to the zero probe first bounds the individual graph energies, and the two-index
estimate then controls their differences. Graph completeness produces U and
its genuine jets with continuous interior representatives. Strong operator
continuity identifies the same limit's source as max(q,0). Nonnegativity passes
through almost-everywhere subsequential convergence and interior continuity.

Define V_n=r_n+U_n and V=r+U, with both jets defined by those exact sums.
The exact source difference implies -L_Kn V_n=g_n^-. The physical maximum
principle makes V_n nonnegative without probe pole conditions; the full graph
limit is nonnegative and satisfies -L_K V=max(-q,0). Thus r=V-U, p=p_V-p_U
and z=z_V-z_U as literal functions, not just unrelated representatives.

The same K_n recovers every aU+bV together with its actual two derivative
coordinates. The complete six-entry action and mass converge with genuine
integrability. If the physical limiting mass is positive, a positive tail is
normalized by its actual mass and both jets are scaled by the same factor.
Raw components are never assigned a mass-one predicate. Zero source cases
are included. Since U,V are nonnegative and r=V-U has mass one,
mass(U+V)>=mass(V-U)=1; normalized sum recovery therefore has no supplied
positive-mass premise.

This completes the prescribed bounded inverse/recovery child by a direct
smooth-inverse completion route. The transformed zero-trace domain remains
proved in the first checkpoint. The proof uses the Green contraction, uniform
coercive graph estimates and completion in the original weighted graph; it
does not invoke an unproved H⁻¹ variational inverse, maximal-domain density,
or a bound on K′. The shared source and graph recovery replace those proposed
intermediate mechanisms without changing the split target.

The [native packet](../evidence/phase2-round-9-split/checkpoint.json) and consumer
retain the original endpoint minimum and produce these components without a
supplied operator-sign or positive-reference premise. They do not prove that
U, V or their sum minimizes the complete action. The remaining parent task is
still to prove A_K(U+V)<=A_K(V-U)=0 or construct a genuine negative same-cap
joint competitor when the complete cross pairing is positive. The inverse
construction itself gives no such upper sign. C_rot remains undetermined;
all-probe coverage, global sufficiency, original smooth endpoint classification
and final suite/manuscript acceptance remain required.

## Round 10 first checkpoint: whole-cap scale balance

The single Round 9 outer review verifies the actual inverse split. The next
research target remains the complete-action upper comparison, rather than any
further assumed-sign consequence.

The new native identity is

\[
 \int K W_\lambda=3A_K(r)-\lambda m_K(r),
\]

where W_lambda is the literal full curvature adjoint. Its proof uses the
own-curvature Green representations of both f and b, weighted Fubini, and
the exact cubic density identity in f,b,K. It does not treat rescaling K
alone as a feasible physical variation. The mass term has degree one.

At an actual zero minimum, integral K W_0 is zero. For any measurable
v in [1,C] with integral (x-1/2)v=0, the genuine curvature
J=2v/integral(v) has both physical moments and an original ratio-C box.
The accepted whole-cap adjoint inequality applies to this actual J. Therefore
K/kappa minimizes the linear cost integral W_0 v with only the centered
moment fixed; its total integral is free. An explicit perturbation of the box
midpoint proves qualification in the new one-moment separation theorem.

The resulting native multiplier t has residual Z=W_0-t(x-1/2), complementary
signs in the actual box [kappa,C*kappa], and

\[
 \int KZ=0,\qquad \int Z_+=C\int Z_-,\qquad
 \int W_0=(C-1)\int Z_-.
\]

All products and positive/negative parts are genuinely integrable. This
centering follows from comparisons allowing the box scale to vary; arbitrary
fixed-box multipliers cannot simply be renamed to impose it. The theorem does
not prove that Z is nonzero, that both obstacles are attained, or that the
inverse-component cross pairing has the desired upper sign.

The [native checkpoint](../evidence/phase2-round-10-scale/checkpoint.json)
contains these three statements and the same-endpoint consumer. Source-level
research also examines actual pole limits, a curvature clamp, finite transports
with exact moment corrections, reciprocal local variations, and repaired
hemisphere folds. Those investigations have not produced the strict complete-
action inequality. Their unformalized identities and proposed free-interval
argument remain provisional; no numerical or conditional calculation is
promoted to an endpoint-selection theorem. Implementation continues within
the unchanged Round 10 objective.

## Round 10 continuation: an actual free curvature interval

The next packet proves a regular representative of the curvature at an actual
joint minimum. Write q for the canonical continuous interior representative of
the literal weak operator. The complete curvature adjoint has the form
Z=2*f*r²*K+H, where H is locally absolutely continuous. This uses the actual
weighted Dirichlet adjoint and the actual slope-kernel adjoint; unweighted
integrability of the warp coefficient is not assumed. Complementarity gives
Kc=clip_[kappa,Lambda](-H/(2*f*r²)) wherever r is nonzero, and Kc=K almost
everywhere. At probe zeros the representative uses the boxed original K.
The weighted product Kc*f*r² remains locally absolutely continuous across
all zeros, without a hypothesis on their number or isolation.

For a zero-action minimum, this yields a genuine free interval. If Kc took
only its two box values wherever r is nonzero, continuity there would make
it locally constant. For the actual flux F=Kc*f*r²*b/2, the derivative would be

\[
 F'=f q^2-\mathcal D_K(r,r',r'')
\]

almost everywhere on every compact interior interval, where D is the COMPLETE
action density. At a probe zero, the nonnegative locally absolutely continuous
product Kc*f*r² has a local minimum; its derivative vanishes wherever it exists.
This proves the same flux law there, with no differentiation of measurable K.

The first parabolic graph bounds prove that the literal f*r² is globally
absolutely continuous and has true zero traces. The bound |F|<=Lambda*f*r²
then controls both pole limits. Local FTC and a global integral primitive give
integral(F')=0. Zero action would therefore imply integral(f*q²)=0. The warp
is positive inside, so q=0 almost everywhere; the accepted strong maximum
principle applied to the probe and its negation contradicts unit mass.
Consequently one interior point has nonzero r and strict curvature margins.
Continuity gives a nondegenerate closed interior interval and eta>0 with
f>=eta, |r|>=eta, and kappa+eta<=K<=Lambda-eta almost everywhere on that
interval, in the SAME original ratio box.

The four leaves contain five public theorems and no definitions. Their native
checkpoint is recorded in [the free-interval evidence](../evidence/phase2-round-10-free/checkpoint.json).
The supplemental consumer starts from the actual endpoint minimum and retains
its mass, zero complete action, global minimality and all four recovery limits.
A free interval permits local curvature perturbations; it does not construct a
negative direction. The strict complete-action comparison for the inverse sum
remains unproved, as do the determining/global and original smooth-endpoint gates.

## Round 11: finite comparison tests and the bounded API correction

The Round 10 outer review accepts the scale packet and verifies the
curvature/free-interval mathematics and native evidence. Its one API finding
is addressed by deriving source measurability inside the weighted Green
theorem: divide the measurable weighted source by x*(1-x), which is positive
almost everywhere on the physical open interval. The caller now supplies
only weighted integrability. No conclusion or physical domain is changed.

The Round 11 mainline remains the strict finite comparison, not this API
correction. Three bounded investigations below are **PROVISIONAL source-level
research**, not native selection theorems or endpoint counterexamples.

For the actual inverse sum s=U+V, choose the original scale-balanced box and
v0=K/kappa. Given any centered-moment v1 in [1,C], the full interval family
v_t=(1-t)v0+t*v1 and J_t=2*v_t/integral(v_t) retains both exact physical
moments and the original cap. Its raw Green primitives are linear in v_t.
With the genuine probe r+alpha*s and its summed jets, the normalized action
has the sign of a(t)+2*alpha*b(t)+alpha²*c(t), where all three coefficients
are COMPLETE cubic geometry pairings. At t=0 they are 0,0,4*beta/kappa³.
The nonnegative old-geometry source-change cost has not disappeared. The
concrete box reflection v1=C+1-v0 is admissible, but no strictly negative
finite coefficient combination has been established for it or another v1.

Weighted curvature sorting followed by probe reoptimization is distinct from
the rejected source-transport recipe. A round constant-probe first-variation
test favors sorting, but it does not prove the least-value comparison at the
endpoint. The actual zero-mode exchange weight depends on the probe and
Euler flux. Minimality supplies an inequality for allowed exchanges, not
the positional ordering needed by a finite rearrangement theorem. The
rearranged geometry's recovery and BV factorization would also need proof.

A separate repaired-cap family uses
R_a=(s'(a)*r-p(a)*s)/2, whose derivative at the cut is zero. Its original
complete action is beta*p(a)² and B(R_a,s)=-2*beta*p(a). Under beta>0
and p(a)≠0, it is therefore not a new zero mode; the original stationary boundary law
cannot erase its bulk terms. The affine warp repair itself changes the pole
slope. Only the full reflected/rescaled geometry is an admissible comparison,
so the original moment multiplier cannot be applied to the raw repair as
though it were a normalized tangent. The finite cap action remains unsigned;
its transformed recovery has not been assumed from linear-combination recovery.

None of these tests rejects existence of an orientable endpoint minimum or
proves the required negative same-cap competitor. No new inverse package,
conditional positivity wrapper, numerical start or discriminant theorem is
offered as a substitute. C_rot and all original global/endpoint/final gates
remain open. The [Round 11 evidence](../evidence/phase2-round-11/checkpoint.json)
records the bounded API delta separately from this unresolved research.


## Round 13: signed continuation and compact interior nodal structure

The current route uses the actual signed zero minimum. The former sufficient
operator-sign selection mechanism remains **UNRESOLVED and UNREFUTED**, parked
under the owner's route reassessment. None of the original determining,
selection, global sufficiency, original smooth endpoint or final acceptance
requirements is removed. Chronological descriptions above retain their scope
at the time they were written; source orientation is not a prerequisite for
this alternative.

The new native theorem packet establishes a structural statement that was not
previously available: the minimizing probe has no interior accumulation of zeros.
It is finite on every compact interior subset. The same statement applies to
any continuous recoverable global minimum at a cap C>=1; zero action is not a
premise of the general nodal theorem. The actual endpoint producer supplies one
such minimum together with zero action and all four smooth recovery limits.

Let f=warp K, b=warpSlope K, lambda=A_K(r), let P be the canonical integral Euler
flux and q the canonical Euler momentum divided by f². The accepted signed
first-order system is reused with these exact objects. It already supplies
r'=p, local AC of p and q, the literal operator's a.e. equality to q, and the
actual equations for p',q',P'. No new independent jets or state representatives
are introduced.

The first new step is weak uniqueness. On any compact interior interval, the
positive warp has a bounded reciprocal, and the original box bounds K while
|b|<=2. All four equations therefore have bounded linear coefficients. For
E=r²+p²+q²+P², the actual a.e. laws imply |E'|<=B E for a derived finite B.
Absolute continuity and the two integrating factors exp(±Bx) propagate any
zero of E in both directions. A simultaneously vanishing state would make
r zero throughout the physical interior, contradicting its actual mass one.
This argument uses no K derivative and imposes no physical probe pole value.

The local nodal engine treats each possible first nonzero coordinate. At a
zero of r, nonzero p directly gives isolation. If p=0 and q!=0, bounded lower
coefficients times vanishing states disappear in the a.e. derivative limit;
AC and FTC then give the actual nonzero derivative p'=q/f at the node. Rolle's
theorem transfers isolation to r. If r=p=q=0 and P!=0, the same argument gives
q'=P/f² and p'=0 there. Dividing the first p-equation by x-x0 yields a nonzero
a.e. limit of p'/(x-x0). FTC signs isolate the zero of p on both sides, followed
again by Rolle. This is not formal differentiation of a measurable curvature
or a claim of a full smooth Taylor expansion. Compactness and continuity then
make the zero set finite on any compact subset of (0,1).

The canonical leaves are `Analysis/AbsolutelyContinuousUniqueness`,
`Analysis/WeakSystemZeroIsolation`, `Geometry/WeakProbeContinuation` and
`Geometry/WeakProbeNodalSet`. The endpoint consumer retains the exact K,r,p,z,
unit mass, zero complete action, global minimality and all four strong limits.
The result does not assert a finite total node count as the poles are approached,
a finite switch count, symmetry, global smooth curvature or smooth attainment.
Its independent review is the single configured Round 13 outer delta review.

### Bounded matrix-certificate attempt — provisional and parked

Two source-only tests examined a node-compatible matrix certificate for the
complete action. With y=(r,p) and control z, the actual leading coefficient is
f³, the mixed vector is (-Kf²,2bf²), and the lower matrix has entries
Q11=2K²f-Kb²/2, Q12=-5Kbf/2 and Q22=4b²f. The Hamiltonian momentum is (-P,f²q).
These calculations retain the original mixed lower term; they are provisional
research calculations, not new native certificate theorems.

A compact clamped Jacobi frame can be selected by excluding clamped zero modes,
but the attempted exclusion uses original-form nonnegativity. Polar exhaustion
of its quadratic endpoint values likewise needs a lower bound supplied by that
same safety statement. A compact negative probe makes a fixed-endpoint value
unbounded below by adding arbitrary multiples of it. Thus neither tested selector
removes the determining/global safety dependency. This is an obstruction to
these two constructions, not a refutation of all matrix comparisons. The route
is parked after the two tests until a new curvature-dependent control mechanism
is available.

Logarithmic polar cutoffs suggest a separate possible coverage bridge: on an
annulus epsilon²<x<epsilon, a smooth cutoff in log(x)/|log epsilon| has both
integral x*eta'^2 and integral x³*eta''² tending to zero. This could cover every
original smooth probe without dividing by a positive reference. The estimates
and their proposed graph/action passage are still **PROVISIONAL** here; they
are not used by the nodal proofs or claimed as native results.

The next signed-route test is to combine the proved isolated-node behavior
with the actual curvature clamp and scale multiplier laws: determine what can
be controlled on both sides of each node and at the singular poles before any
global structural or branch assertion. No finite contact pattern is assumed.
The decisive remaining full goal is still an informative characterization with
appropriate selection and sufficiency across every original geometry and probe,
followed by exact original smooth endpoint classification and final delivery.

### Prospective qualification of the historical cap report

The historical hashed cap report is preserved. Its assertion that at least one
retained cap restriction is nonzero requires a chosen-cut proof. If both displayed
coefficients (s'(a),p(a)) vanish, its R_a is identically zero. Before using any
such cap, establish its actual nonzero restriction and positive physical mass
before normalization. The beta>0 qualifier in the chronological cap discussion
above is now explicit. Neither correction refutes endpoint selection.

## Round 14: simple nodes and the actual curvature-clamp traces

The signed route now resolves the interior node-interface step. The packet
uses one actual zero-action joint minimum and its canonical q,P, complete
adjoint, original box and centered multiplier. It makes no operator-sign
assumption. The [native checkpoint](../evidence/phase2-round-14-nodes/checkpoint.json)
records the new kernel-supported declarations; the single configured outer
delta review remains pending. No determining constant is claimed.

### Why the actual zero minimum has only simple interior nodes

At a hypothetical r(c)=p(c)=0, local weak second-derivative energy gives
p(x)^2 <= (c-x) E and r(x)^2 <= (c-x)^3 E on a left interval ending at c.
For shrinking intervals E tends to zero. A fixed smooth transition at width
epsilon therefore has vanishing errors chi'*r, chi'*p and chi''*r in L2.
The bounded interior weights preserve these limits in all three parabolic
graph coordinates. The cutoff jets are the actual product derivatives.

Closedness identifies both weak derivatives of the literal left cut. Its
complement is the right cut. A diagonal selection from the original smooth
sequence recovers both cuts on one common same-cap curvature sequence; the
smooth left and right probes sum exactly to the selected original probe.
All six derivative-graph limits survive this construction.

The accepted raw_graph_recovery theorem gives complete-action and physical
mass passage for each raw cut. Original zero minimality implies nonnegative
smooth action at the same cap. Both cut actions are consequently nonnegative,
and their exact local-density sum is the original zero action, so both vanish.
Their physical masses sum to one. Choose a positive-mass cut before normalizing
it. It is an actual zero-action global minimum and vanishes on an open interval,
contradicting the accepted nodal isolation theorem. Thus p(c) is nonzero at
every actual interior zero. The p=0/q!=0 and p=q=0/P!=0 possibilities are
excluded by this feasible full-action argument rather than omitted or assumed
nondegenerate. No physical probe boundary condition is added.

### Complete adjoint cancellation and the decisive cancelling case

Write f=warp K, b=warpSlope K, lambda=A_K(r), and use the canonical q,P.
Let R be the actual curvature adjoint minus its direct factor 2*f*r^2*K.
With A=weakCurvatureWarpCoefficient-lambda*r^2, B the slope coefficient,
and J the genuine Green-tail derivative, the new native theorem proves

    R' = 6*f*q*p - b*f*p^2 - 3*b*q*r - 2*P*r/f + 2*J - 2*integral(B),

and its locally AC derivative satisfies a.e.

    R'' = (2*f*p^2 + 6*q*r - 4*b*r*p + b^2*r^2/(2*f))*K
          + 3*b^2*p^2 - 3*b*q*p + 4*P*p/f - b*P*r/f^2.

All explicit curvature terms cancel in R'; the full second law is affine in
the original measurable K with continuous interior state coefficients. These
identities retain the complete lower action terms and follow from AC/FTC and
the actual signed equations, without differentiating K.

Choose kappa,t once from the accepted whole-cap scale-balanced producer.
Set H=R-t*(x-1/2), D=2*f*r^2, and use that same residual's complementarity
to obtain Kc=clip_[kappa,C*kappa](-H/D) off nodes, equal to original K a.e.
At nodes use the boxed original point value; these choices do not affect traces.
The theorem returns the full residual integrability, signs and scale balances
for these very same kappa,t, rather than identifying separate existential boxes.

At a node c the proved simple zero gives D/(x-c)^2 -> alpha=2*f(c)*p(c)^2>0.
If H(c)!=0, continuity forces an obstacle on both sides. If H(c)=0 but
H'(c)!=0, the first derivative forces the corresponding opposite obstacle
traces. The difficult case is H(c)=H'(c)=0. Put

    beta = 3*b(c)^2*p(c)^2 - 3*b(c)*q(c)*p(c) + 4*P(c)*p(c)/f(c).

The actual law becomes H''=alpha*Kc+beta+e with e->0. Two AC integrations
give a contracting feedback for the clipped quotient. A punctured-neighborhood
supremum estimate proves convergence without assuming a curvature limit:

    Kc -> clip_[kappa,C*kappa](-beta/(3*alpha)).

The Taylor estimate and contraction are general Analysis theorems. Their
point derivative and eventual denominator positivity are derived internally.
Together with the first-order cases they prove finite left and right curvature
limits at every actual interior probe zero. The displayed endpoint consumer
retains the exact K,r,p,z, unit mass, zero complete action, global minimality,
all scale balances and all four original strong recovery limits.

### Pole test and remaining determining gap

The actual accepted geometry bounds include f(0)=f(1)=0 and
0<f(x)<=2*C*x*(1-x) in the interior. Thus compact reciprocal-warp bounds
cannot be made uniform at either pole. In addition, arbitrary point values of
weak representatives at a pole are not trace data. The new argument uses only
compact interior intervals and does not turn weighted zero flux traces into
bounded r,q or curvature traces. This test identifies the precise missing
polar bridge; no general pole-limit theorem is asserted or used here.

The next signed-route obligation is the actual polar asymptotic/trace control
needed to use the coupled system globally. Finite interior node traces imply
neither a finite total node count nor finitely many obstacle contacts. An
independently determining characterization, justified selection, sufficiency
across every original geometry and smooth probe, exact original smooth endpoint
classification and final manuscript/evidence/delivery remain open. The parked
operator-sign and matrix-selector routes are not prerequisites for this work.

## Round 15: actual unweighted pole control and finite probe traces

The new signed-route result establishes unweighted L1 membership of the
literal weak meridional operator Q and the genuine first derivative p, and
finite one-sided traces of the same minimizing probe r at both physical
poles. An explicit primitive extends r absolutely continuously to [0,1],
agrees with it throughout the interior, retains derivative p there and bounds
the original probe globally. Neither trace is assumed nonzero. The
[native checkpoint](../evidence/phase2-round-15-poles/checkpoint.json) concerns
this packet; its single configured outer review is pending. The preceding
Round 14 interior packet is independently accepted and reused unchanged.

### The decisive complete-source estimate

Let lambda be the actual minimum action, P its canonical Euler flux, and
q the canonical Euler momentum divided by f². The accepted signed system
ties q to the literal Q a.e. The complete Euler source is

    P' = f*K*q + K*b*f*p/2 - (K²*f-K*b²/2)*r + lambda*f*r.

Every term is unweighted L2. Indeed r is L2, sqrt(w)*p is L2 and sqrt(f)*q
is L2 from the accepted graph/action bounds, while f,K,b have the original
physical bounds. The factor f improves the weighted p and q terms. This
estimate retains both potential terms, the mixed term and the true mass
multiplier. No unweighted p/q estimate is assumed at this stage.

Natural accepted zero traces and AC of P, combined with P' in L2, give
P/x and P/(1-x) in L1. The general endpoint theorem proves the square-root
increment bound by Cauchy-Schwarz and integrates distance^(-1/2). It requires
only the true AC function, its two zero traces and its actual derivative in
L2; no additional pointwise rate is an input.

### Singular integrals give q and p in L1

The tail kernel proves that integrability of t*S(t) on (0,b) implies
integrability of integral_x^b S(t) in x. Its product-measure row length t
provides the needed weight. The source itself need not be unweighted L1;
its a.e. measurability is recovered from the weighted product. The companion
head kernel proves that

    x^(-2) * integral_0^x t*g(t)

is L1 whenever g is L1. Its row integral is controlled by
t*integral_t^b x^(-2) dx = 1-t/b <= 1. Both are genuine native Fubini
arguments, with empty intervals handled and no separate positivity binder
for b. No external mathematical axiom is used.

For the actual q equation, write w=x(1-x), d=w/f and

    S = q' = (P-K*b*f*r/2)/f²,
    w*S = d²*(P/w) - d*(K*b/2)*r.

The original parabolic lower bound gives 0<d<=C/2. Since
P/w=P/x+P/(1-x), all terms on the right are L1. Applying the tail estimate
to genuine local AC/FTC on each half interval, with exact reflection at the
right pole, gives q in unweighted L1. The canonical a.e. equality transports
this conclusion to the original literal weak operator Q.

The accepted literal derivative flux F=f²*p is globally AC, has zero traces
and satisfies F'=f*(Q+K*r). The source Q+K*r is now L1. The two genuine
endpoint integral representations of F and the head estimate give
F/x² and F/(1-x)² in L1. The original lower bound on f then controls p on
both halves. The generic divergence theorem uses only a.e. coefficient bounds,
the tied flux equation and true derivative law; it derives p's measurability
internally. No assumed source sign, p bound or polar leading coefficient is
inserted. Curvature is never differentiated.

### The same probe has actual finite traces

The theorem displays

    R(x) = r(1/2) + integral_(1/2)^x p(t).

Unweighted p integrability makes R absolutely continuous on [0,1]. Genuine
weak FTC proves R=r throughout (0,1), and its classical interior derivative
is the same p. Its endpoint continuity therefore gives the original probe's
one-sided limits R(0) and R(1); compactness bounds r on the full interior.
These are derived traces. Arbitrarily assigned r(0),r(1) of an a.e. weak
representative are not boundary data and are not silently equated with them.
Only the natural flux has a zero boundary condition; no zero probe boundary
condition is introduced. Both zero-trace cases are included in the result.

The general physical theorem applies at any C>=1 to a continuous recoverable
global minimum, not just a zero-action endpoint. The concrete endpoint
consumer starts from the accepted original producer and retains the same
K,r,p,z, mass one, zero action, global minimality, full same scale residual and
literal interior clamp, all four strong recovery limits and action passage.
Those recovery limits remain the original weighted graph limits. No convergence
of the smooth recovery sequences' assigned pole values is asserted.

### Remaining polar and determining obligations

This closes the unbounded-probe uncertainty needed to analyze the r² factor
of the polar curvature adjoint. It does not give boundedness or finite traces
of p,q, or a curvature/clamp limit at a pole. Next use these new L1 estimates
with the actual signed equations to test the boundary behavior of f*p and
f*q, and combine it with the genuine Green/adjoint terms. Treat vanishing r
traces without a nondegeneracy premise. No finite total node count or fixed
obstacle-contact pattern is inferred from a finite possibly-zero trace.

An independently determining characterization, appropriate solution selection,
universal sufficiency across every original geometry and smooth probe, exact
original smooth endpoint equality/attainment and all-form transfer, and final
manuscript/evidence/delivery still remain open. The original C_rot objective
has not been replaced by a necessary system or variational definition.

## Round 16: actual weighted-state and regular-adjoint pole laws

The contracted pole test closes. The native
[checkpoint](../evidence/phase2-round-16-adjoint-poles/checkpoint.json) covers
four new theorems, their actual endpoint application and Q5's bounded API
generalization. The single configured outer delta review is pending; the
unchanged accepted proofs and their reviews are reused. C_rot remains
undetermined and Phase II remains OPEN.

### Actual weighted states, without polar nondegeneracy

Write f for the actual warp, b for its slope, lambda for the complete minimum
action, P for its canonical Euler flux and q for its canonical momentum/f².
The already proved unweighted integrability and the genuine equations give

    (f*p)' = q + K*r - b*p,
    (f*q)' = b*q + P/f - K*b*r/2.

Every right-hand term is L1. For the second equation, P/x and P/(1-x)
are L1 by the accepted complete-source L2 estimate and genuine zero flux
traces. With w=x(1-x), P/w=P/x+P/(1-x), and the original geometry gives
w/f<=C/2. Thus P/f is L1. No derivative of measurable K is taken.

The first equation is the direct derivative variant of the contracted
divergence argument: it uses the genuine tied jets and previously established
p integrability. A globally integrable derivative extends each weighted state
absolutely continuously. Its quotient by either endpoint distance is also L1,
because f/x and f/(1-x) are bounded and p,q are L1. The native reciprocal-
distance trace theorem forces both extension values to zero. Their natural
literal endpoint values are already zero, so the actual weighted functions
are AC on [0,1] and tend to zero at both poles. This is more than substituting
f=0 in the weighted flux: the interior limits and closed AC law are proved.

The public weighted-state theorem requires a continuous p representative but
does not require continuous r. Q5 independently removes both continuity
premises from the standalone a.e.-invariant Q-integrability theorem: canonical
momentum AC and the positive C1 warp directly yield q's local AC and derivative.
The old bundled first-order theorem is unchanged. The final probe and adjoint
trace statements retain hr/hp for their legitimate pointwise conclusions.

### Both genuine Green terms and the complete polar values

For the literal Dirichlet adjoint G(x)=integral kernel(s,x)*A(s), weighted
source integrability is enough. On the closed physical interval the exact
bound is |kernel(s,x)|<=s(1-s); the kernel is continuous in its second argument.
Native dominated continuity gives G continuous up to both poles with value
zero. Source measurability is derived by division by the positive interior
weight. The slope adjoint T already has an accepted globally AC extension
and zero endpoints; that result is consumed unchanged.

Here A is the full weak curvature warp coefficient minus lambda*r², and T
uses the actual slope coefficient. The lambda*r² correction is retained and
weighted integrable. The complete canonical regular part is

    W = -2*(f*q)*r - b*r*(f*p) - b²*r²/2 + 2*G + 2*T.

Use the same explicit R from Round 15, with R=r throughout the interior.
Since b tends to 2 and -2 and both weighted states and Green terms tend to
zero, W tends to -2*R(0)^2 and -2*R(1)^2. Either R trace may vanish. For every
fixed t, H=W-t*(x-1/2) has traces -2*R(0)^2+t/2 and -2*R(1)^2-t/2.
The endpoint consumer selects one existing kappa,t once and applies this law
to that same t while retaining the full residual, clamp, interior node laws,
unit mass, zero action, global minimum and all four original recovery limits.
It also checks Q integrability using only hC, the competitor and minimality.

These are limits of the canonical regular expression. The full weak adjoint
has an accepted a.e. representation tie; no pointwise limit of an arbitrarily
modified literal Q or full adjoint is asserted. Nor is convergence of the
recovery sequences' smooth pole values inferred from weighted graph recovery.

### Remaining determining and endpoint gap

The two-pole regular-adjoint values remove the previously uncontrolled weighted
state/Green boundary contribution. They do not control H/(2*f*r²) when both
numerator and denominator vanish. The next signed-route test must derive the
additional rates from the actual coupled equations, including zero R traces,
before using a divided polar chart or global contact pattern. No finite total
node/switch count, curvature pole limit or source orientation is assumed.
Apply the owner's two-unsuccessful-attempt rotation rule to that new keystone;
the old sign and matrix selectors remain parked, unresolved and unrefuted.

The necessary system still needs an informative determining characterization,
justified threshold selection and an independent universally sufficient
comparison over every original geometry and smooth probe. Every coverage and
Haar bridge actually used, original smooth endpoint equality/attainment and
all-form transfer, and final manuscript/native/review/private-delivery closure
remain required. Only AC1 and AC2 are fully met; no original result is deferred.

## Round 17: actual corrected states and first-order polar numerator rate

The bounded test succeeds through the genuine coupled flux equations. The
[checkpoint](../evidence/phase2-round-17-polar-rates/checkpoint.json) records
nine new leaves and twelve theorems; the configured single outer delta review
is pending. Round 16 and Q5 have passed their single outer review at 7a3d0bf;
unchanged accepted proofs and evidence are reused. Phase I remains COMPLETE,
Phase II remains OPEN, and C_rot remains undetermined.

### Decisive cancellation in the actual Euler flux

Fix one recoverable continuous global minimum at C>=1. Let lambda be its
complete action, f its actual warp, b its actual slope, P its canonical Euler
flux and q its canonical momentum/f². Use the accepted explicit same-probe
extension R=r(1/2)+integral_(1/2)^x p. Put

    uL=2-b,                 uR=2+b,
    EL=P-uL*b*R/2,          ER=P-uR*b*R/2.

Both corrected fluxes are AC on the physical closed interval. The genuine
Euler zero traces and the slope values give EL(0)=0 and ER(1)=0. Their
actual a.e. derivatives are T(uL) and T(uR), where the complete expression is

    T(u)=f*K*(q-K*r)+b*(f*K-u)*p/2+K*u²*r/2+lambda*f*r.

This follows by differentiating the actual AC product; only b'=-2K is used.
Measurable K is never differentiated. The original geometry bounds f/x and
f/(1-x), and bounds uL/x and uR/(1-x) by 4C. Accepted unweighted L1 control
of q,p,r then makes T(uL)/x and T(uR)/(1-x) integrable. The apparent
nonintegrable K*b*r/2 term of q' has cancelled in these corrected flux laws.

The genuine zero-flux integral representation, not an assigned zero value
alone, now gives EL/x² and ER/(1-x)² in L1. The corresponding endpoint
quotients EL/x and ER/(1-x) tend to zero. Actual parabolic lower bounds
transfer the inverse-square estimates to EL/f² and ER/f² on their respective
half intervals and give EL/f -> 0 and ER/f -> 0 at the poles. These bounds
use no source orientation, curvature limit or nonzero probe trace.

### Corrected operator traces and bounded actual states

The actual corrected coordinates satisfy

    QL=q+r*uL/(2f),         QR=q+r*uR/(2f),
    QL'=EL/f²+(K*r+p)*uL/(2f),
    QR'=ER/f²+(-K*r+p)*uR/(2f).

Local AC comes from the true tied coordinates. Their derivatives are L1 on
the corresponding half intervals, so tied anchored integral extensions give
finite actual limits qL and qR. Original primitive bounds control uL/f and
uR/f there, while R is already bounded; hence canonical q is bounded on the
whole interior, with the midpoint accounted for. The literal weak operator
equals q almost everywhere, as in the accepted Euler producer.

The genuine F=f²*p is AC, has both zero endpoint traces, and satisfies
F'=f*(Q+K*r). This source is now bounded almost everywhere. Its actual
endpoint primitives are bounded by constants times x² and (1-x)². Dividing
by the squared parabolic lower bound proves p bounded throughout (0,1).
The bound depends on the actual minimum; no uniform numerical bound across
all geometries is claimed. The result allows either or both R traces to vanish.
It proves finite corrected-q traces, not a polar limit of raw q or p.

### The complete regular-adjoint derivative rate

The full warp source improves from weighted L1 to unweighted L1:

    A=weakCurvatureWarpCoefficient-lambda*r²
     =3q²-4bqp+2Kqr-Kbrp+K²r²-lambda*r²       almost everywhere.

The proof uses the actual weak-operator equality, the new p/q bounds and
accepted r² integrability. No lower action term or mass correction is removed.
Write B for the actual slope coefficient and

    J(x)=integral_x^1 (1-s)*A(s)-integral_0^x s*A(s).

Unweighted A integrability makes both tails AC on [0,1]. Thus J tends to
integral_0^1(1-s)*A(s) and -integral_0^1 s*A(s). The accepted genuine derivative
of the canonical regular adjoint W is

    W'=6fqp-bfp²-3bqr-2Pr/f+2J-2*integral_0^1 B.

For every fixed t, let H=W-t*(x-1/2), a0=R(0), a1=R(1). The native theorem
proves limits of its actual derivative, not an independent supplied jet:

    H'-a0²*(2-b)/f -> -6*a0*qL+2*integral_0^1(1-s)*A(s)
                         -2*integral_0^1 B-t                 at 0+,
    H'+a1²*(2+b)/f ->  6*a1*qR-2*integral_0^1 s*A(s)
                         -2*integral_0^1 B-t                 at 1-.

Indeed, substitution of the actual corrected coordinates and flux gives

    -3bqr-2Pr/f = -3br*Qe+(b*r²/2)*(ue/f)-2Er/f.

The accepted fp zero trace, the new p/q bounds and E/f zero trace control
every remaining product. The difference between b*r²/2 and its endpoint
value tends to zero, and ue/f is bounded; no trace of ue/f is assumed.
When a probe trace is zero, its correction vanishes identically in the
displayed limit, giving a finite genuine H' trace even if that trace also
vanishes. For nonzero probe trace the explicit curvature-primitive term is
retained; the theorem does not claim that H' alone has a limit.

The endpoint consumer calls the actual zero-minimum producer once and selects
one kappa,t once from the accepted same-box theorem. It retains K,r,p,z,
physical mass one, zero complete action, global minimality, all scale-residual
balances, literal clamp/interior node laws, both older pole laws and all four
strong recovery limits and complete-action passage. Corrected-state and rate
constants from separate theorem calls are identified by uniqueness of limits;
no existential witnesses are silently equated. The new rate uses precisely
the same chosen t. Zero action simplifies only the actual lambda correction
in this endpoint consumer; the general theorem retains lambda.

### Exact remaining obstruction and next test

This supplies the contracted first-order numerator rate and removes the
unbounded p/q and unweighted Green-source obstructions. It does not prove a
limit of the cancelling quotient H/(2*f*r²). When the probe trace is nonzero
and H's endpoint value is zero, integrating the retained primitive term still
couples the quotient to averages of the unknown curvature. The next concrete
test is a genuine averaged-feedback estimate from the same clamp and these
rates, including its selection/contraction and all polar remainder bounds.
At a zero probe trace with cancelling H value and H' trace, the denominator
vanishes to higher order and further actual coupled rates remain unproved.
No Taylor expansion of measurable K, polar nondegeneracy, finite total node
count or prescribed contact pattern is supplied.

The curvature representative at a probe zero still uses clipped raw K.
An off-zero or a.e. polar result cannot become an everywhere Kc limit if
nodes can accumulate there without a proved representative/zero-set bridge.
None is claimed in this packet. A failed subsequent estimate would not
refute the whole signed route. Parked sign and matrix mechanisms remain
unresolved and unrefuted, not compulsory prerequisites.

An informative determining characterization and justified selection,
independently sufficient comparison over every original geometry and smooth
one-form with every used coverage/Haar bridge, original smooth endpoint
classification and all-form equality transfer, and final manuscript/native/
review/private delivery remain required. Accepted smooth superthreshold
witnesses are reused. Only AC1 and AC2 are fully met; no necessary condition
or polar rate is being substituted for the full C_rot determination.

## Round 18: actual polar clamp selection at nonzero probe traces

The averaged-feedback test succeeds in its contracted scope. Five new leaves
and ten native theorems are bound by the
[checkpoint](../evidence/phase2-round-18-polar-clamp/checkpoint.json). The one
configured outer delta review passes at 1c779db. Round 17's actual polar-rate
packet passes its single outer review at e33c0e1 and is reused unchanged.
C_rot remains undetermined; only AC1 and AC2 are fully met.

### Genuine endpoint FTC and actual primitive rates

For a locally differentiable H with actual zero trace at 0 and an L1 source
G, a finite limit of deriv H-G first gives integrability of deriv H on a
smaller endpoint interval. Native endpoint FTC then identifies H(x) with
integral_0^x deriv H; it does not assign a boundary value to raw H. Averaging
the vanishing remainder proves

    H(x)/x - average_(0,x) G -> L.

A remainder tending to zero has average tending to zero by its uniform
bound on a whole shrinking interval. No pointwise limit of the comparison
source G is needed. The same actual warp and its genuine derivative/slope
have f/x -> 2 and f/(1-x) -> 2, by native l'Hopital and accepted physical
endpoint values. No curvature derivative or curvature pole limit is supplied.

The literal slope primitive gives (2-b)=2*integral_0^x K, and its true total
moment gives (2+b)=2*integral_x^1 K. Bounded curvature averages and the first-
order warp rate show

    (2-b)/f - average_(0,x) K -> 0              at 0+,
    (2+b)/f - average_(x,1) K -> 0              at 1-.

The averages themselves may oscillate. Their boundedness, rather than a
presumed limiting value, controls multiplication by the vanishing warp error.

### The averaging contraction closes

Use canonical interval-average notation and write

    M_K(x)=average_(0,x) [s -> average_(0,s) K].

An a.e. bound on abs(K-c) is preserved by averaging. The variable-endpoint
average is integrable, so the same centered bound holds after the second
average. A bounded K satisfying the actual eventual law

    K(x)=clip(A-rho*M_K(x)+e(x)),  e -> 0,  0<=rho<1,

therefore tends to clip(A/(1+rho)). The native proof constructs the fixed
point and the supremum of abs(K-k) on a shrinking interval. It proves
M<=rho*M+(1-rho)*epsilon/2, forcing M<=epsilon/2. No selector, averaging
norm estimate, curvature trace or comparison conclusion is an extra premise.
The source is integrable and boxed; the averaged function is the literal K.

For the actual minimum put a=R(0), with a nonzero in this case, and retain
H=W-t*(x-1/2), D=2*f*r² and the complete constant L from Round 17. Replacing
K by the same Kc inside integrals is justified by its proved a.e. equality.
The derivative rate and endpoint FTC give, when H's left trace is zero,

    H(x)/x - a²*M_Kc(x) -> L,
    D(x)/x -> 4*a².

Thus -H/D equals -L/(4*a²)-M_Kc/4 plus a remainder tending to zero, even
when the averages have no limit. Its actual clipped feedback has gain 1/4.
The selected value is

    clip_[kappa,C*kappa](-L/(5*a²)).

The full complete-action Green terms remain in

    L=-6*a*qL+2*integral_0^1(1-s)*A(s)-2*integral_0^1 B-t.

Here qL is the actual corrected-q trace, A the actual warp coefficient and
B the actual slope coefficient. The physical theorem has zero complete
action; this is the actual lambda=0 specialization, not an erased mass term.
For noncancelling H trace, positivity of D near the pole gives the appropriate
constant obstacle saturation, derived from that trace and D tending to zero.

### Exact reflection, common multiplier and representative scope

At the right pole use y=1-x, the actual H(1-y), f(1-y), r(1-y) and Kc(1-y).
The genuine derivative changes sign, and the integral substitution identifies
the reflected average. Hence the selected cancelling trace is

    clip_[kappa,C*kappa](L_R/(5*R(1)^2)),
    L_R=6*R(1)*qR-2*integral_0^1 s*A(s)-2*integral_0^1 B-t.

The same kappa,t are selected once by the accepted node-clamp producer.
The new theorem retains its complete residual/complementarity/scale balances,
a.e. curvature tie, everywhere box, all interior node laws and the canonical
corrected-q trace equations. The accepted actual H values identify left
cancellation with t=4*R(0)^2 and right cancellation with t=-4*R(1)^2.
The two cancellations cannot be chosen independently for two nonzero traces.

At each nonzero probe trace, eventual nonvanishing of the same r is derived
from its actual limit. The representative therefore uses its literal divided
clamp throughout that polar neighborhood; the limit is an everywhere one-
sided limit of Kc, not merely an a.e./off-zero conclusion. Raw weak K remains
only a.e. equal and may have arbitrary point modifications. At zero probe
traces the theorem supplies no curvature limit or polar node exclusion.
The endpoint consumer retains the identical K,r,p,z, physical mass one, zero
action, global minimum, one common full scale/node/pole package and all four
strong original graph recovery limits with complete-action convergence.

### Remaining structural and full determining frontier

The nonzero-trace cancelling-clamp obstruction is removed. Zero-R cases still
need genuine higher numerator/denominator rates and any zero-set/representative
bridge used there. One concrete next test is to use the accepted corrected-q
trace and bounded p to derive the actual q and divergence-primitive leading
rates at a zero R trace, before assuming a nonzero leading coefficient or
excluding further cancellations. No such extra rate is certified here.

No total node/contact count, symmetry or finite-dimensional family is proved.
An informative determining characterization, justified threshold selection,
independently universal complete-action comparison across every original
rotational metric and smooth one-form, every used coverage/Haar/recovery
bridge, exact original smooth endpoint classification and all-form transfer,
and final manuscript/native/review/private delivery remain open. Existing
original smooth witnesses and endpoint safety are reused. Necessary local
clamp selection does not identify C_rot or prove cross-geometry sufficiency.

## Round 19: actual zero-trace leading rates and boundary uniqueness

The zero-R test succeeds in its contracted scope. Seven new leaves contain
eight public theorems and no definitions. The
[checkpoint](../evidence/phase2-round-19-zero-traces/checkpoint.json) binds
the source and same-endpoint consumer. Its mathematical/evidence review
passes at b31dc1e; Q7's remaining API delta is included in Round 20 below.
The accepted Round18 packet is reused unchanged. Phase I remains
COMPLETE, Phase II OPEN, and only AC1/AC2 are fully met.

### Hypothesis and decisive boundary test

Fix any actual recoverable global minimum at C>=1, with its continuous
interior representatives r,p, actual lambda=weakMeridionalAction, canonical
q=EulerMomentum/f², Euler flux P, genuine derivative flux F=f²p and explicit
R=r(1/2)+integral_(1/2)^x p. The accepted corrected-q limits and bounded
(2-b)/f or (2+b)/f imply q tends to its respective corrected trace whenever
the corresponding R trace is zero. No curvature trace is used.

The decisive hypothesis to reject is R(0)=qL=0. The original parabolic box
gives lo*x<=f<=m*x on the left half, with lo=1/C, m=2*C, abs(b)<=2 and
abs(K)<=m almost everywhere. Bounded actual p and endpoint FTC give
abs(r)<=N*x. Thus E=abs(q)+abs(p)+abs(r)/x has a finite envelope. The complete
source is retained literally:

    P'=f*K*q+K*b*f*p/2-(K²*f-K*b²/2)*r+lambda*f*r.

Its absolute value is at most A*x*E, for the explicitly derived nonnegative
A=3*m²+m³+3*m+abs(lambda)*m+1. Genuine zero-trace AC/FTC gives the actual
P primitive, hence P=O(x²). The actual equation

    q'=(P-K*b*f*r/2)/f²

then has an integrable bounded right side at the pole. Its local AC law and
zero q trace identify the same q with its endpoint primitive. No arbitrary
assigned value q(0) is used. The full derivative-flux equation and true zero
trace likewise give the literal F primitive and its bound for p. These yield
the three coupled integral inequalities for P,q,p together with
abs(r)<=integral_0^x abs(p).

### The shrinking-envelope contraction closes

The Volterra engine constructs M as the supremum of E on a sufficiently
small interval (0,delta); boundedness and nonemptiness are proved. The P
primitive gives abs(P)<=A*x²*M. It follows successively that

    abs(q)<=T*x*M,
    abs(p)<=U*x*M,
    abs(r)/x<=U*x*M,

for fixed nonnegative T,U. Hence M<=(T+2U)*delta*M. Choosing delta with
(T+2U)*delta<1 forces M=0, so the same r,p,q,P all vanish on that interval.
The accepted actual state-nonvanishing theorem contradicts this at an
interior point. Thus a zero probe trace forces qL!=0. The proof derives all
integral bounds from the genuine equations; none is an extra minimum-level
premise. Measurable K is never differentiated, and no source orientation,
limiting curvature, independent polar jet or finite-node assumption enters.

The reusable differential engine derives a.e. differentiability from its
local AC input by a countable rational-interval cover. It does not export
that derivable regularity as a separate user hypothesis.

### Genuine leading rates and exact reflection

For a genuine zero AC flux, an essential limit deriv(F)/x -> L gives the
ordinary limit F/x² -> L/2. The proof extracts a uniform a.e. error bound on
each whole shrinking interval, integrates the actual derivative by FTC and
controls the weighted quadratic remainder. Applied to F'=f*(q+K*r), the
accepted f/x -> 2, q -> qL and bounded K with r -> 0 give

    F/x² -> qL,   p -> qL/4,   r/x -> qL/4,   qL!=0.

The final probe quotient follows from its genuine derivative r'=p and
endpoint limit, not an imposed Taylor jet. The source limit is only essential;
the resulting F,p,r quotient limits are ordinary one-sided limits of their
actual representatives.

At the right pole reflect the full same functions by y=1-x:
rR=r(1-y), pR=-p(1-y), qR=q(1-y), PR=-P(1-y), FR=-F(1-y),
fR=f(1-y), bR=-b(1-y) and KR=K(1-y). The complete source, including lambda,
retains its form. AC reflection and the measure-preserving substitution are
proved/applied explicitly; geometric symmetry is not assumed. The genuine
tail primitive F(x)=-integral_x^1 f*(q+K*r) therefore gives

    q -> qR,   p -> -qR/4,   r/(1-x) -> qR/4,   qR!=0

when R(1)=0. Either or both R traces may vanish; nonzero qL/qR are outputs.
Their signs are unrestricted.

### Actual endpoint application and unresolved successor

The consumer calls the accepted endpoint producer once and the accepted
scale/node/nonzero-trace-pole package once. It retains that same kappa,t and
all residual/complementarity/balance laws. Corrected-q constants supplied by
the new theorem are tied to the package's constants by uniqueness of limits.
The same K,r,p,z, physical mass one, zero action, global minimality, four
strong original graph recovery limits and complete-action convergence remain.
No boundary nondegeneracy is supplied to the endpoint example.

The observed outcome is a proved zero-trace leading state and singular
boundary uniqueness, removing the tested structural obstruction. Higher
zero-R numerator/denominator cancellations in H/D and every polar zero-set
or representative bridge actually used remain successor obligations. No
curvature limit in those cases or global node/contact pattern is claimed.
The next signed-clamp test must consume these nonzero leading coefficients
in the complete adjoint at its actual cancellation order, without assuming
smooth K, symmetry or fixed switching. Its success would still require a
separate determining/selection and cross-geometry sufficiency argument.

An informative characterization of C_rot, justified threshold selection,
independent universal safety across every original rotational metric and
smooth one-form, all used coverage/Haar/recovery bridges, exact original
smooth endpoint equality/attainment and final manuscript/native/review/private
delivery remain open. Necessary boundary structure does not determine C_rot.

## Round 20: quadratic polar adjoint remainder and same-curvature saturation

The bounded zero-R clamp test succeeds. Four new leaves contain five public
theorems and no definitions. The
[checkpoint](../evidence/phase2-round-20-polar-saturation/checkpoint.json)
binds final sources, native evidence and the same-endpoint consumer. One
configured outer delta review passes at 4287e5f, including Q7. Phase I remains COMPLETE;
Phase II remains OPEN and only AC1/AC2 are fully met.

### Exact hypothesis and decisive estimate

Fix one genuine recoverable global minimum, its actual complete-action
multiplier lambda, canonical q=EulerMomentum/f², Euler flux P and the
explicit same-probe extension R. No curvature trace or nondegeneracy is
supplied. At a zero-R pole use inward distance d=x or d=1-x. The accepted
boundary theorem derives q*!=0, q -> q*, r/d -> q*/4 and the oriented limits
p -> q*/4 on the left and p -> -q*/4 on the right.

The accepted corrected fluxes are EL=P-(2-b)*b*R/2 and
ER=P-(2+b)*b*R/2, with EL/x -> 0 and ER/(1-x) -> 0. Boundedness of
(2-b)/x or (2+b)/(1-x), and R -> 0, therefore give P/d -> 0.
This is the rate actually used. The stronger suggested O(d²) estimate is
unneeded and is not claimed as a new result. Together with f/d -> 2 and
finite r/d and p limits, this controls both singular terms P*p/f and
b*P*r/f² without differentiating or taking a limit of measurable K.

The full actual second-adjoint density is

```text
S = (2*f*p² + 6*q*r - 4*b*r*p + b²*r²/(2*f))*K
    + 3*b²*p² - 3*b*q*p + 4*P*p/f - b*P*r/f².
```

The K coefficient tends to zero, and bounded K suffices for its essential
product limit. Both P terms tend to zero by the actual rate above. With
b -> 2 on the left and b -> -2 on the right, the remaining expression has
the same limit -3*q*²/4 at either pole. The regular-adjoint C1 identity and
genuine locally AC derivative tie this density a.e. to the actual H'' for
H=W-t*(x-1/2). All complete lower-action and mass-correction terms remain.

### Genuine remainder and actual obstacle selection

The reusable FTC engine derives local integrability from the uniform
essential second-derivative remainder, identifies the actual derivative
primitive using its finite trace, then integrates once more for H. Thus,
with h0 and h1 the genuine value and inward derivative traces,

```text
(Hhat(d) - h0 - h1*d)/d² -> -3*q*²/8,
D/d³ -> q*²/4 > 0,             D = 2*f*r².
```

For a zero left probe trace, h0=t/2 and
h1=LL=2*integral(1-s)*A(s)-2*integral B(s)-t. At the right pole,
h0=-t/2 and h1=-LR, where
LR=-2*integral s*A(s)-2*integral B(s)-t. The generic minimum theorem keeps
A=weakCurvatureWarpCoefficient-lambda*r²; the zero-action application sets
lambda=0. Exact reflection supplies the right inward minus sign and retains
the same functions; no geometric symmetry is used.

The nonzero r/d limit first proves an eventual node-free neighborhood.
Consequently the same boxed representative Kc equals the literal divided
clamp throughout that neighborhood, rather than just a.e. or off-zero.
If h0>0, or h0=0 and h1>0, it is eventually the lower obstacle kappa.
If h0<0, or h0=0 and h1<=0, it is eventually the upper obstacle C*kappa.
In the doubly cancelling case, (-H/D)*d -> 3/2, so -H/D -> positive
infinity. The nonzero quadratic term precludes a further cubic cancellation.

### Same-object application, outcome and remaining work

The physical producer selects one box and t from the accepted Round18
theorem once. Uniqueness of genuine corrected-q limits identifies the
constants from its additional minimum applications explicitly. It returns
the original full residual/complementarity/scale laws and node traces, the
accepted nonzero-R pole selections, the new zero-R laws and both unconditional
pole limits of that same Kc. The endpoint consumer starts from the actual
zero-minimum producer once and preserves identical K,r,p,z, unit mass, zero
action, global minimality, all four strong original graph recovery limits
and complete-action convergence. Either or both probe traces may vanish.

Q7 is a bounded accompanying API repair: local AC derives interior q
continuity internally, the redundant public premise is removed, and the
sole canonical physical caller is adapted without changing its headline.
A separate external consumer uses the revised minimal hypotheses. Its API
and affected native delta receive no mainline theorem credit.

The observed contribution closes the actual zero-R quadratic/saturation
obstruction; the needed rate has no remaining uncontrolled term. This
establishes necessary polar structure, not a determining constant. The next
principal test must confront a concrete determining/selection or
cross-geometry sufficiency implication before expanding contact-pattern
machinery. One possible unproved test is whether the complete centered
residual can vanish a.e.: the two pole values would force t=0 and both R
traces zero, while the new quadratic rate would oppose bounded divided
curvature. Any resulting scale/contact selection and any cap-expansion path
still need their actual same-object and admissible-path proofs. No such
successor implication is claimed here.

The proposed next comparison target has a strictly larger scope than the
accepted witnesses above rotationalThreshold: start at an arbitrary cap
C>1 with an actual zero-action global minimum and seek an original smooth
negative competitor below every cap C'>C. A candidate mechanism is complete
centered-residual nonvanishing, scale/contact selection and a moment-corrected
cap-expansion direction, using the actual free interval in the same box.
That same-box identification and every feasibility/recovery/action-error
bridge remain unproved. Success would exclude lower-cap zero minima and
justify a selection implication; it would still not determine C_rot.

An informative characterization and justified selection of C_rot,
independent safety for every original rotational metric and smooth
one-form, every used coverage/Haar/recovery bridge, exact original smooth
endpoint equality/attainment and all-form transfer, and final manuscript,
native, independent-review and private-delivery gates remain open. No total
node/contact count, finite switching family, symmetry, unique branch or
smooth attainment follows from this packet.

## Round 21: arbitrary-zero-minimum cap expansion

The principal theorem starts from an arbitrary C>1 with an actual
recoverable unit-mass global minimum K,r,p,z of zero complete action,
with continuous interior representatives r,p.
For every D>C it returns an original smooth negative metric/form witness
at C<Cbar<D. It does not assume C=rotationalThreshold or invoke the
previous theorem extracting witnesses above that threshold. Four new
leaves contain five public theorems and no definitions. The
[checkpoint](../evidence/phase2-round-21-cap-expansion/checkpoint.json)
binds the canonical source, native evidence and same-endpoint consumer;
its single configured outer delta review passes at 3cbeb6b.

### Complete residual and the actual common box

Fix one centered multiplier t. Write H for the canonical regular adjoint
minus t*(x-1/2), D=2*f*r² and Z for the complete centered weak adjoint.
The accepted representative tie is Z=H+D*K a.e. If Z were zero a.e.,
bounded curvature would imply |H|<=2*C*|D| a.e. The continuous H and D
extend this inequality throughout the interior; no continuity of Z or K
is supplied. The true pole limits of D are zero. The two accepted H
values then force t=0 and zero probe traces. The actual nonzero quadratic
remainder at such a pole contradicts the resulting cubic bound. Thus
the complete residual is not almost everywhere zero, for every t.

Select the accepted scale-balanced box once. Its integrable residual,
nonvanishing and balance force both positive and negative residual
masses to be strictly positive. Complementarity gives genuine contact
at both obstacles. These contacts identify any other positive curvature
box of ratio at most C: its lower and upper endpoints must be exactly
kappa and C*kappa. Only after this identification is the separately
produced free interval transferred into the chosen box. It has a uniform
curvature margin, positive warp/probe margin and Z=0 a.e. there.

### Exact moments and strict full-action descent

The general box-expansion engine needs only measurable bounded K,
positive real integral of max(-Z,0), and a strict free interval on which
Z=0. Positive real integral derives integrability of that negative part
under the totalized Bochner convention. Its measurable representative
defines a measurable indicator V. Two separated smooth bumps inside
the actual free interval give an invertible two-moment matrix, hence
a bounded smooth correction c with the same zeroth and first moments
as V. The direction V-c has both moments zero. A derived positive step,
bounded by the larger upper-box gap and free-interval margin, keeps
J=K+epsilon*(V-c) in the enlarged box. Its exact residual cost is
-epsilon*integral(max(-Z,0))<0. Full-source measurability/integrability
and an upper-contact premise are not additional public assumptions.

The exact moments cancel the centering term, so this is a strictly
negative pairing with the full curvature adjoint, retaining every warp,
slope and lower-action contribution. Same-box smooth curvature recovery
and the accepted bounded L1-pairing passage select an actual smooth
comparison with strict negative pairing. The original quadruple is
transported to the larger cap without assuming minimality there. The
existing complete segment derivative, including its finite higher-order
action terms, yields a genuine negative point. The segment has strictly
positive physical mass; actual normalization scales its action by a
positive square. Full-action recovery then selects a negative original
smooth area competitor. The geometric realizer retains the curvature,
both inverse maps, original probe and its true first/second jets,
same-metric dissipation, represented metric and nonzero one-form.
Choosing Cbar strictly between C and D gives the required ratio room.

### Outcome and next determining obligation

The decisive test succeeds through the complete chain, including actual
finite descent and smooth original realization. There is no remaining
uncontrolled term in this cap-expansion implication. The endpoint
consumer starts with the accepted endpoint producer once, retaining
the same K,r,p,z, unit mass, global minimum, full common scale/node/pole
laws and all four strong graph recovery limits and action convergence.
It invokes the new theorem without added sign/contact/selector inputs.
Two private integral-zero simplifications preserve every public type;
source advice and Root's statement audit are not independent acceptance.

This result advances threshold selection; global minimality in its input
still carries a universal comparison burden. A uniquely selected zero
of another variational value would not determine C_rot. The next
principal test must identify informative determining data and an actual
independent sufficiency implication across geometries, before expanding
contact-pattern bookkeeping without a proved dependency. All original
probe coverage and normalization/Haar/recovery bridges used by that
comparison, exact original smooth endpoint equality/attainment and
all-form transfer, and final manuscript/native/review/private-delivery
gates remain mandatory. No finite switching, symmetry, source sign,
finite-dimensional family, unique branch or smooth attainment is assumed.

## Round 22: direct signed-data test and an independent global comparison

The principal test was whether the complete signed zero-mode/flux,
regular-adjoint, scale/complementarity and physical two-pole laws imply
nonnegative complete action for every original changed geometry/probe,
without hmin, safe-cap membership, infimum identity or all-probe positivity.
The direct input system is frozen in the
[signed-data test](/tmp/hmz-fence-rfse-route-_1tj3d8t/math-target-round22-root-508dnjrd/signed-data-test.md).
It uses the same literal primitives, canonical momentum/flux, unit mass,
zero action, true jets, original box/moments and both zero/nonzero pole cases.
Its forward production is already covered by the accepted endpoint packet.
Freezing necessary laws is not new mathematical credit.

### Principal attempt: exact finite control and state excess

At a fixed state f,b,r,p the complete density has the exact control excess

```text
ell(f,b,K+k,r,p,z+w)-ell(f,b,K,r,p,z)-Dc*k-2*A0*w
  = f*(f*w-r*k)^2 + f*r^2*k^2.
```

Here Dc and A0 are the literal direct-curvature and second-probe coefficients.
The full simultaneous tangent retains all three curvature coefficients and
twice all three probe coefficients at lambda=0. Root natively checks the
exact finite polynomial, including every mixed and potential term, in the
source-only worker probe. The physical increments must still be the actual
warp/slope differences, J-K, s-r and the true first/second derivative
differences. Independently varied scalar entries are not physical examples.

The curvature tangent is the complete adjoint pairing; both exact moments
cancel its centering term. Scale/complementarity signs this linear pairing
even for a separately scaled ratio<=C comparison box. The probe tangent
has the genuine flux primitive A0*(s'-p)-P*(s-r), with vanishing actual
pole products. These first-order cancellations leave the finite state/mixed
integral explicitly recorded in the
[attempt note](/tmp/hmz-fence-rfse-route-_1tj3d8t/math-target-round22-root-508dnjrd/finite-comparison-attempt.md).
The integrated cancellation argument is a research calculation, not a new
canonical formalized theorem. Its sign is not produced by the control
squares. Even the fixed-geometry probe block contains the full action of
the probe increment. For a weak reference curvature it cannot simply be
called an original smooth comparison with J=K; the accepted normalized
probe perturbation and full-action recovery are the relevant bridges.

Outcome: the arbitrary-cap reverse implication remains **UNRESOLVED and
UNREFUTED**. No counterexample satisfying the full signed system and physical
domain was obtained. A negative scalar density diagnostic is not such a
counterexample. This one bounded attempt produced exact finite algebra and
identified the unsigned integral, without an independent global theorem.
The mechanism is parked rather than promoted into a mandatory lemma.

### Sole bounded alternative: whole-action boundary-null completion

A different mechanism constructs an actual comparison directly for every
original probe. Put f=warp K, b=f' and q=L_K r using the literal physical
primitives and derivatives. For constant box parameters kappa,Lambda,
the genuine flux

```text
F = 2*kappa*f^2*r*r' + (Lambda/2)*f*b*r^2
```

vanishes at both physical poles. Continuous K and a C2 probe suffice for
its classical derivative, because f'=b and b'=-2K. Adding F' to the full
six-entry action density gives exactly

\[
 f(q+\kappa r)^2+
 \left(2\kappa-\frac{\Lambda-K}{2}\right)f^2(r')^2+
 \frac{\Lambda-K}{2}(fr'+br)^2+
 \bigl(K^2+(2\kappa-\Lambda)K-\kappa^2\bigr)fr^2.
\]

Genuine endpoint FTC therefore proves the corresponding complete-action
identity. No derivative of K or condition on r's pole value/derivative is
used. If kappa>0 and kappa<=K<=Lambda<=2*kappa, the three square
coefficients are nonnegative, and

\[
 K^2+(2\kappa-\Lambda)K-\kappa^2
 \ge \kappa(2\kappa-\Lambda)\ge0.
\]

Thus the independently proved homogeneous bound is

\[
 A_K(r)\ge\kappa(2\kappa-\Lambda)\int_0^1fr^2.
\]

The value two follows from these exact coefficient signs; it is not an
arbitrary numerical cutoff. Probe nodes cause no division or chart change.
This comparison needs no reference mode, branch, source orientation, global
minimum or supplied positivity certificate. It signs the whole finite
original action rather than just a first variation.

### Original all-form scope, contribution and remaining target

The accepted exhaustive normalization and all-form Haar transport apply
the actual scalar bound on the same original metric and form, including
the nonnegative nonzonal remainder. Hence curvature ratio<=2 is universally
safe for ALL original smooth one-forms in the allowed rotational class,
and **2<=C_rot**. The proof includes ratio exactly two. Four public theorems
in two canonical leaves state the calibration, mass bound, original safe-cap
membership and threshold lower bound. The
[checkpoint](../evidence/phase2-round-22-pinching-safety/checkpoint.json)
binds native evidence and a consumer with a nonconstant normalized curvature,
arbitrary C2 probe and actual original all-form inputs. The source simplifier
recommends NO CHANGE; it is not an independent acceptance review.

The principal signed-data implication is still unproved; the successful
bounded alternative supplies a genuine independent universal comparison
on an explicit cap range. It does not determine C_rot, identify it with two,
prove a sharp selected branch, classify exact unrestricted-endpoint equality
or establish smooth attainment. The accepted sharp witnesses and strict
conformal-Killing upper bound remain unchanged. Future global work must
construct and select an informative sharp comparison beyond this constant
completion, with every used original coverage/domain/path/Haar/recovery
bridge. A variable coefficient or state-dependent comparison field is a
possible next test, not an assumed certificate or theorem. All original
determining, endpoint/all-form and final manuscript/native/review/private
delivery gates remain mandatory and OPEN; only AC1/AC2 are fully met.

## Round 23: construct and control a warp-dependent comparison field

The principal test succeeds in constructing an independent comparison beyond
the constant completion. Put `a=kappa`, `beta=Lambda-kappa^2*f/2` in
`F=2*a*f^2*r*r'+beta*f*b*r^2/2`. Its actual derivatives use only
`f'=b`, `b'=-2K`, the true probe jets and `Dbeta=-kappa^2*b/2`.
The canonical proof integrates the negative flux; both actual pole values
vanish from f=0. Continuous K and a C2 probe suffice, without probe sign
or artificial pole conditions.

The reachable-state inequalities are produced from the original geometry:

\[
 b^2+4\kappa f\le4\le b^2+4\Lambda f.
\]

Indeed the derivative of `b^2+4*c*f` is `-4*b*(K-c)`. The actual monotone
slope determines whether the comparison uses the left or right pole;
both exact moments and both pole values are retained, without symmetry.

Inflate the input upper endpoint to `C*kappa`, where
`C=1+sqrt(3/2)` and `C^2=2*C+1/2`. With `u=kappa*f`, `t=b^2` and
`k=K/kappa`, the complete calibrated density equals

\[
 f(q+\kappa r)^2+
 2\kappa\left(fr'+\frac{(C-k-u/2)b}{4}r\right)^2+
 \kappa G(C,u,t,k)r^2,
\]
\[
 G=u\bigl(k^2+(2-C)k-1+uk/2-t/2\bigr)
   +(C-k)t/2-(C-k-u/2)^2t/8.
\]

For `v=t/4`, the derived domain is `0<=v<=1`,
`(1-v)/C<=u<=1-v`, `1<=k<=C`. When v<1, substitute
`u=(1-v)*[(2*C-4)+(5-2*C)*y]`, `k=1+(C-1)*z` and derive
`0<=y,z<=1`. An explicit degree(3,2,2) polynomial expansion has 36
nonnegative coefficients, using the exact quadratic equation and its
derived rational brackets. At v=1, u=0 and
`G=(C-k)*(4-C+k)/2>=0`; no endpoint chart is assumed. The root arises
from `G(C,1/C,0,1)=(1/C)*(2-C+1/(2*C))`, not a numerical cutoff.

Genuine endpoint FTC therefore signs the whole original action when
`Lambda^2<=2*kappa*Lambda+kappa^2/2`. The accepted exhaustive
normalization/Haar bridge proves **1+sqrt(3/2)<=C_rot**, with ALL original
smooth one-forms and the displayed cap included. The
[checkpoint](../evidence/phase2-round-23-warp-calibration/checkpoint.json)
binds the final native packet and actual consumer. Source simplification
advice recommends NO CHANGE; the single outer delta review passes at 088b48f.

This is one successful field-construction test, with no bounded alternative.
The diagnostic calculation was exploratory; the exact coefficient proof and
actual original-object transfer supply the mathematics. No hmin, reference
mode, source orientation, assumed positivity, K derivative or finite switching
family is used. Round22's accepted comparison remains unchanged.

The new bound does not determine C_rot or select its sharp branch. In
particular no nonzero zero-action object at this field's cap is produced.
The next sharp-comparison test must construct comparison data together with
such an original-domain object and justify their selection; global minimality
must follow from the independent comparison before using accepted cap expansion.
Optimizing another lower bound or renaming a variational threshold is not
determination. All original smooth-endpoint/equality, used domain/recovery
bridges and final manuscript/native/review/private-delivery gates remain OPEN.

## Round 24: joint field and equality feasibility

The single principal target is a genuinely variable probe-independent field
and a compatible nonzero recoverable zero object at the same selected cap.
The complete remainder is kept as `A*p^2+B*p*r+D*r^2`, with
`A=2*a*f^2`, `B=f*((beta-K)*b+2*f*Da)` and
`D=f*(K^2+(2*a-beta)*K-a^2)+(beta-K)*b^2/2+(f*b/2)*Dbeta`.
The undivided saturation equations include `q+a*r=0` and both kernel
equations, with actual derivatives, both moments and unit physical mass.
No global minimum, safety premise, symmetry or finite switching is supplied.
The [checkpoint](../evidence/phase2-round-24-field-feasibility/checkpoint.json)
binds the private native sources, commands and outputs described below.

**Attempt 1.** Put `u=kappa*f`, `k=K/kappa`, `t=b^2` and test
`a=kappa*(1+alpha*u)`, `beta=kappa*(C-c*u)`.
The genuine complete product rule retains `Da=alpha*kappa^2*b` and
`Dbeta=-c*kappa^2*b`, without differentiating K. A conditional smooth
constant-upper polar-branch calculation motivates `alpha=1/8`,
`c=(2*C-1)/4`; it is not a produced law for the relaxed optimizer.

The decisive physical diagnostic takes `C=5/2`, `kappa=20/17`,
`Lambda=50/17` and
`K(x)=50/17-(480/17)*x^2*(1-x)^2`. This smooth curvature has both exact
moments and attains both box endpoints. Its actual midpoint state is
`f=7/17`, `b=0`, `K=kappa`. The genuine smooth probe
`r(x)=1-(25/289)*(x-1/2)^2` has `r=1`, `p=0`, `r''=-50/289` there,
so `q+a*r=0`. The full candidate calibrated density is exactly
`-4498900/410338673`. Positive physical normalization preserves this sign
and gives an actual `IsSmoothAreaCompetitor (5/2) K s`.

Outcome: this particular universally pointwise-nonnegative certificate is
refuted. Neither negative original action nor unsafety of cap 5/2 follows.
The calculation does not refute all affine fields or general variable fields.
No zero object, independent global comparison or determining data result.

**Supporting rigidity test.** For warp-only C1 fields at fixed `f>0`,
`a>0`, write `af=a_f`, `bf=beta_f`. The determinant numerator is

`H(k,t)=8*a*f*(k^2+(2*a-beta)*k-a^2)`
`+t*(4*a*(beta-k+f*bf)-(beta-k+2*f*af)^2)`.

Native calculus shows that a nonnegative affine pencil `P(k)+t*R(k)` on
an open rectangle, vanishing at an interior point, has `P=R=P'=R'=0`
there. Here `P=P'=0` would force `k^2+a^2=0`; hence H is strictly
positive inside such a rectangle. The exact identity
`8*a*Q=(4*a*w+(beta-k+2*f*af)*b*r)^2+H*r^2`, `w=f*p`, is checked too.
This obstructs this rectangular-enclosure method of free interior equality.
It is not a physical reachability theorem. Application to the accepted weak
free interval would still require same-box state-interior and weak equality
bridges, with the `a=0` and nodal cases treated separately. Those are not
proved or assumed here.

**Attempt 2.** Retain the actual history defect
`Phi=b^2+4*Lambda*f-4`, whose genuine derivative is
`4*b*(Lambda-K)`. At diagnostic cap `5/2`, test
`a=kappa*(1+u/8+gamma*Phi)` and
`beta=kappa*(5/2-u+eta*Phi)`, for arbitrary real constants gamma, eta.
The complete derivative proof includes
`Da=kappa^2*b*(1/8+4*gamma*(5/2-k))` and
`Dbeta=kappa^2*b*(-1+4*eta*(5/2-k))`.

On the enclosure boundary `k=5/2`, `t=4-4*u`, the determinant numerator
factors as `u*P(u)`, with P continuous and `P(0)=96*eta`. Its
nonnegativity throughout `0<u<2/5` requires `eta>=0`. At the actual
quartic midpoint above, `u=140/289`, `t=0`, `k=1`, `Phi=244/289`.
Nonnegative Q at `p=0,r=1` requires `eta<=-9/488`, for every gamma.
Native proofs establish this incompatibility. The midpoint is an actual
original state; physical realization of the enclosure boundary is not
proved. The conclusion rejects these enclosure conditions, not every
original-geometry comparison with these fields.

A separate literal-primitive fixture has
`w=15/256`, `I=1/630-w/70+w^2/30` and
`K=5/2-[x*(1-x)]^2*[x*(1-x)-w]^2/(2*I)`.
It is smooth, has both exact moments, lies in `[25/24,5/2]`, and satisfies
`K(1/16)=5/2`, `b(1/16)>0`, `b(1/16)^2+10*f(1/16)-4>0`.
Thus upper contact cannot be identified with constant-upper history. This
fixture supplies no sharp zero object or action sign.

**Contribution, gap and next action.** All three private probes have native
compiler, declaration-kind/linter and actual transitive-axiom checks. Their
types retain the stated restrictions. They add no canonical theorem or
global sharp comparison. After two substantive unsuccessful constructions,
the low-order warp/constant-history mechanism is parked UNRESOLVED and
UNREFUTED at full original scope. The contracted joint producer is STALLED.
The accepted lower bound remains `1+sqrt(3/2)`.

A different producer mechanism must control genuine slope/history dependence
jointly with the zero object, rather than refit constant coefficients or
optimize another beta-only bound. A possible next bounded test uses full-state
characteristic data or nonconstant gamma(u), eta(u), retaining every
`Phi*gamma'(u)` and `Phi*eta'(u)` term. No such producer, selection or
global extension is claimed. Every used weak/polar/interface/recovery bridge,
independent sharp-value safety, original smooth endpoint/all-form equality
and final Phase-II manuscript/native/review/private-delivery gate stays open.
