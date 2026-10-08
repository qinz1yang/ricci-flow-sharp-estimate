# Research derivation: quantitative stability and symmetry

Status: **unformalized research derivation**. The displayed estimates are not yet native Lean theorems and must not enter the paper as established results.

## Main conclusion and prerequisite

Let `C > 1`, `L = log C`, and let the proposed admissible optimizer `k_*` have
the obstacle intervals `[0, alpha]` and `[beta, 1]`, where
`0 < alpha <= beta < 1`.
Write

\[
 I(k)=\int_0^1\int_0^s2s\,e^{k(v)-k(s)}\,dv\,ds,
 \qquad \delta=k-k_*,\qquad D=I(k)-I(k_*).
\]

Both `k` and `k_*` are continuous and take values in `[0,L]`. The only
optimizer-specific input used below is the provisional exact calibration

\[
 D=P+R,\qquad P=\int_0^1 A(v)\delta(v)\,dv,
\]
\[
 R=\int_0^1\int_0^s2s e^{k_*(v)-k_*(s)}
  \left[e^{\delta(v)-\delta(s)}-1-\delta(v)+\delta(s)\right]dv\,ds,
\]

with

\[
 A(v)=
 \begin{cases}
 3(\alpha^2-v^2),&0\leq v\leq\alpha,\\
 0,&\alpha\leq v\leq\beta,\\
 -3(v-\beta)(v+1/(3\beta)),&\beta\leq v\leq1,
 \end{cases}
\]

and `k_* = 0` on the lower obstacle and `k_* = L` on the upper obstacle.
These give `A delta >= 0` everywhere and, in particular,

\[
 P\geq \int_0^\alpha3(\alpha^2-v^2)\delta(v)\,dv\geq0. \tag{1}
\]

Then the following entirely explicit estimate holds:

\[
 \boxed{\quad
 I(k)-I(k_*)\ \geq\ c(C)\int_0^1|k(v)-k_*(v)|^2\,dv,
 \qquad
 c(C)=\left(\frac{12C}{5\alpha}
                 +\frac{\log C}{2\alpha^3}\right)^{-1}>0.
 \quad} \tag{2}
\]

For the proposed optimizer, `alpha = (q^4 + 2q)^(-1/2)` with the uniquely
specified cap parameter `q`. Thus the constant depends only on the cap,
through exactly the same structurally derived contact parameter as the
optimizer. It uses no numerical certificate, auxiliary rational cap, or
arbitrary spatial cutoff. The constants `2`, `5`, and `12` below come from
Taylor's integral remainder and exact polynomial moments of the complete
lower obstacle. No optimality claim for the stability constant is made.

## 1. The correct uniform convexity constant is 1/(2C)

For real `x,y >= -L`, Taylor's formula in integral form gives

\[
 e^x-e^y-e^y(x-y)
 =(x-y)^2\int_0^1(1-t)e^{(1-t)y+tx}\,dt
 \geq\frac{e^{-L}}2(x-y)^2. \tag{3}
\]

Apply this with

\[
 x=k(v)-k(s),\qquad y=k_*(v)-k_*(s).
\]

Both differences belong to `[-L,L]` because both profiles are admissible.
The left side of (3) is exactly

\[
 e^{k_*(v)-k_*(s)}
 [e^{\delta(v)-\delta(s)}-1-\delta(v)+\delta(s)].
\]

Consequently, writing

\[
 Q(\delta)=\int_0^1\int_0^s2s(\delta(v)-\delta(s))^2\,dv\,ds,
 \qquad a=\frac1{2C},
\]

we get

\[
 R\geq aQ(\delta). \tag{4}
\]

Bounding the unweighted exponential remainder first on `[-2L,2L]` and then
bounding its prefactor separately would produce an unnecessary `C^{-3}`.
The segment in (3) stays inside the admissible difference range and proves
the stronger displayed constant directly.

## 2. An exact weighted-pair variance identity

This step does not assume any weighted variance theorem. For arbitrary
continuous `delta : [0,1] -> R`, put

\[
 \mu=\int_0^1\delta(x)\,dx,\qquad
 g(x)=\delta(x)-\mu,\qquad
 G(x)=\int_0^xg(v)\,dv,\qquad
 V=\int_0^1g(x)^2\,dx.
\]

Since the interval has length one, `integral g = 0`, so `G(0)=G(1)=0`.
Subtracting a constant does not change pair differences, so `Q(delta)=Q(g)`.
Expand the square in its defining integral. Fubini gives

\[
 \int_0^1\int_0^s2s g(v)^2\,dv\,ds
 =\int_0^1(1-v^2)g(v)^2\,dv,
\]

and the second square term gives `2 integral_0^1 s^2 g(s)^2 ds`. The cross
term is `-4 integral_0^1 s g(s) G(s) ds`. Since `G'=g`, integration by parts
gives

\[
 -4\int_0^1s g(s)G(s)\,ds
 =-2[sG(s)^2]_0^1+2\int_0^1G(s)^2\,ds
 =2\int_0^1G(s)^2\,ds.
\]

Thus the exact identity is

\[
 \boxed{\quad Q(\delta)
 =\int_0^1(1+x^2)g(x)^2\,dx+2\int_0^1G(x)^2\,dx\quad} \tag{5}
\]

and in particular

\[
 Q(\delta)\geq V. \tag{6}
\]

Every integrand is continuous on the compact triangle or interval; the
Fubini and integration-by-parts steps therefore have their usual elementary
integrability hypotheses. No derivative of `delta` is required: its
primitive `G` is continuously differentiable. Equations (1), (4), and (6)
now imply

\[
 D\geq P+aV. \tag{7}
\]

The constant mode is absent from (5), so (7) alone is not yet L2 coercivity.

## 3. Obstacle anchoring controls the constant mode

Use the whole lower-obstacle calibration weight, normalized to mass one:

\[
 w(v)=
 \begin{cases}
 \dfrac{3(\alpha^2-v^2)}{2\alpha^3},&0\leq v\leq\alpha,\\
 0,&\alpha\leq v\leq1.
 \end{cases}
\]

It is nonnegative and continuous, and direct integration gives

\[
 \int_0^1w=1,\qquad
 \int_0^1w^2
 =\frac9{4\alpha^6}
    \left(\alpha^5-\frac23\alpha^5+\frac15\alpha^5\right)
 =\frac6{5\alpha}. \tag{8}
\]

On the support of `w`, one has `0 <= delta <= L`. Hence `delta^2 <= L delta`
there and (1) yields

\[
 \int_0^1w\delta^2\leq bP,
 \qquad b=\frac{L}{2\alpha^3}. \tag{9}
\]

Set

\[
 r=\int_0^1(w-1)^2=\frac6{5\alpha}-1\geq0.
\]

The last inequality also follows from Cauchy--Schwarz and `integral w=1`;
it is immediate from `alpha <= 1` in this application. Weighted
Cauchy--Schwarz and (9) give

\[
 \left|\int_0^1w\delta\right|\leq\sqrt{bP}.
\]

Since `integral g=0`,

\[
 \mu=\int_0^1w\delta-\int_0^1(w-1)g,
 \qquad
 |\mu|\leq\sqrt{bP}+\sqrt{rV}.
\]

A two-dimensional Cauchy--Schwarz inequality then gives

\[
 \mu^2\leq
 \left(\sqrt b\sqrt P+\sqrt{r/a}\sqrt{aV}\right)^2
 \leq(b+r/a)(P+aV)
 \leq(b+r/a)D. \tag{10}
\]

The elementary variance identity is `integral delta^2 = V + mu^2`.
Combining `V <= D/a` from (7) with (10) proves

\[
 \int_0^1\delta^2
 \leq\left(b+\frac{1+r}{a}\right)D
 =\left(\frac{L}{2\alpha^3}+\frac{12C}{5\alpha}\right)D,
\]

which is exactly (2). This proves, rather than assumes, the obstacle
anchoring needed to remove the constant-shift invariance of the pair term.

## 4. Two-hemisphere stability and equatorial near-symmetry

Let `h : [-1,1] -> [0,L]` be continuous, with no reflection assumption.
Define

\[
 k_+(v)=h(v),\quad k_-(v)=h(-v)\quad(0\leq v\leq1),
\]
\[
 \mathcal D=I(k_+)+I(k_-)-2I(k_*).
\]

Apply (2) separately on the two hemispheres. The immediate full-profile
stability estimate is

\[
 \int_{-1}^1|h(v)-k_*(|v|)|^2\,dv
 \leq\frac{\mathcal D}{c(C)}. \tag{11}
\]

Subtracting the two hemisphere errors and using `(x-y)^2 <= 2x^2+2y^2`
gives

\[
 \int_0^1|h(v)-h(-v)|^2\,dv
 \leq\frac{2\mathcal D}{c(C)},
\]

or, on the full interval,

\[
 \boxed{\quad
 \int_{-1}^1|h(v)-h(-v)|^2\,dv
 \leq\frac{4\mathcal D}{c(C)}.\quad} \tag{12}
\]

For the actual equatorial symmetrization
`h_even(v) = (h(v)+h(-v))/2`, this also reads

\[
 \int_{-1}^1|h(v)-h_{\rm even}(v)|^2\,dv
 \leq\frac{\mathcal D}{c(C)}. \tag{13}
\]

Thus equatorial symmetry is a consequence of small deficit, not an
admissibility restriction. Neither the derivation nor these bounds uses a
balance hypothesis. If geometric admissibility additionally requires
balance, it can be imposed without changing this implication.

For an arbitrary positive continuous profile `a_profile` with
`a0 <= a_profile(v) <= C*a0`, take
`h(v)=log(a_profile(v)/a0)`. Then (11)--(13) control logarithmic asymmetry.
The mean value theorem for the exponential on `[0,L]` also gives

\[
 \int_{-1}^1|a_{\rm profile}(v)-a_{\rm profile}(-v)|^2\,dv
 \leq\frac{4(Ca_0)^2\mathcal D}{c(C)}. \tag{14}
\]

For the geometric reciprocal-curvature profile, the dissipation bridge instead uses
`h(v)=log(M/a_profile(v))`, where `M` is its maximum; the positive-log example above
is only a functional consequence for its separately defined deficit. A theorem
converting geometric dissipation to `mathcal D`
must separately prove its exact normalization and nonnegative remainder;
no such conversion is claimed here.

## 5. Endpoint and equality consequences

At `C=1`, admissibility forces `k=0` everywhere. The proposed parameter
is `q=1`, the contacts coincide at `alpha=beta=1/sqrt 3`, and the proposed
optimizer is also identically zero. Direct integration gives `I(0)=2/3`.
Every stability and symmetry error is zero. Formula (2) even has a finite
positive limit-value there, `c(1)=5/(12 sqrt 3)`, so it may be defined at
the endpoint with the trivial proof; no division by `log C` is needed.

For `C>1`, (2) implies that equality `I(k)=I(k_*)` forces
`integral |k-k_*|^2 = 0`. Continuity then implies `k=k_*` at every point
of `[0,1]` (otherwise a neighborhood has positive squared-error integral,
including one-sided neighborhoods at endpoints). This is a consequence
of coercivity, not a replacement for the optimizer-existence and exact
calibration prerequisites.

## 6. Exact reusable lemma boundaries and dependency order

These are proposed mathematical boundaries, not competing frozen Lean APIs.
Use the root-selected canonical namespace and interval-integral conventions.

1. **Exponential tangent remainder on a lower half-line.** Real `L,x,y`
   with `-L <= x` and `-L <= y` satisfy (3). Its proof only needs the
   derivative/second-derivative of `exp` and integral Taylor's theorem, or
   an equivalent native strong-convexity proof. The cap specialization has
   both differences in `[-L,L]`; `L >= 0` follows from `C >= 1`.
2. **Ordered weighted-pair variance identity on the unit interval.** For
   an arbitrary continuous real `delta` on `[0,1]`, define its actual
   Lebesgue mean, centered function, and primitive as above. Then (5)
   holds with the actual nested pair integral. Derive (6) as a corollary.
   Required leaves: bounded-integrand Fubini, the primitive derivative,
   and integration by parts; no Sobolev regularity is required.
3. **General probability-space variance-plus-anchor coercivity.** On a
   probability space let real `f,w` be square-integrable, `w >= 0`,
   `integral w = 1`, and suppose all anchor products are integrable. Let
   `V = integral (f-integral f)^2`, with `P >= 0`, `a > 0`, `b >= 0`,
   `D >= P+aV`, and `integral w*f^2 <= bP`. Then
   `integral f^2 <= ((integral w^2)/a+b)*D`.
   Proof: (10) and the variance identity. The integral of `w*f^2` must be
   explicitly integrable in this general form; square-integrability of
   `f,w` alone does not establish that product's integrability. For the
   current compact continuous application every such hypothesis follows.
4. **Lower obstacle polynomial moments.** For `0 < alpha <= 1`, the
   displayed actual piecewise weight `w` is nonnegative, has integral one,
   and squared integral `6/(5 alpha)`. These are direct polynomial
   integrations and can be private if there are no additional consumers.
5. **Canonical cap stability.** After the other owner's native exact
   calibration and optimizer admissibility are available, combine 1--4
   with `a=1/(2C)` and `b=(log C)/(2 alpha^3)` to prove (2). Do not expose
   a public final theorem that assumes its own optimizer/calibration
   conclusion; the public signature should quantify over actual
   cap-admissible continuous `k`, with the canonical `k_*` and `alpha`.
6. **Two-hemisphere consequences.** Quantify over the same continuous
   `h : [-1,1] -> [0,log C]`, compose with `v` and `-v`, and prove
   (11)--(13). Formula (14) is a separate exponential-Lipschitz corollary.

The only load-bearing upstream prerequisite specific to the optimizer is
the audited calibration/admissibility package. The weighted variance and
generic anchoring leaves can be formalized independently first. All native
proof, integrated-build, linter, axiom, and independent-review gates remain
open for this source-only packet.
