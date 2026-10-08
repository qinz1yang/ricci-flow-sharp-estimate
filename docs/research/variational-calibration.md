# Research derivation: all-cap exponential calibration

Status: **unformalized research derivation**. Only the parameter and generic pair-deficit layers listed in `../theorem-map.md` currently have native Lean evidence. The optimizer, value, rigidity and regularity claims below remain proof obligations and are not established manuscript results.

## 1. Precise domain and conclusion

Use ordinary Lebesgue measure, and let

\[
 \mathcal K_C=\{k\in C([0,1],\mathbb R):0\le k(v)\le\log C\text{ for every }v\in[0,1]\},\qquad C\ge1.
\]

The functional is the actual ordered-pair integral

\[
 I(k)=\int_0^1\int_0^s 2s\exp(k(v)-k(s))\,dv\,ds.
\]

Endpoint conventions in the triangle do not affect this integral. All inputs below are continuous on the closed interval, so every integrand is bounded and all uses of Fubini and elementary integration are legitimate.

There is a unique \(q\ge1\) such that

\[
 F(q):=\log q+\frac23(q^3-1)=\log C.
\]

Set

\[
 \alpha=(q^4+2q)^{-1/2},\qquad \beta=\alpha q^2,
 \qquad \phi(v)=\frac23\big((v/\alpha)^{3/2}-1\big)\quad(v>0).
\]

Define

\[
 E_*(v)=\begin{cases}
 1,&0\le v\le\alpha,\\
 \sqrt{v/\alpha}\,e^{\phi(v)},&\alpha\le v\le\beta,\\
 C,&\beta\le v\le1,
 \end{cases}\qquad k_*:=\log E_*.
\]

The formulas agree where the cases overlap. The exact prospective headline is:

> For every real \(C\ge1\), the just-defined \(k_*\) lies in \(\mathcal K_C\), and for every \(k\in\mathcal K_C\),
> \[
> I(k)\ge \frac23-\beta+\frac1{3\beta},
> \]
> with equality if and only if \(k(v)=k_*(v)\) for every \(v\in[0,1]\).

This is an actual minimum and a unique optimizer in the original continuous box-constrained problem. It does not redefine the target as an infimum or add an unproved producer hypothesis. An implementation with functions on \(\mathbb R\) must state uniqueness only on \([0,1]\); the original problem does not constrain exterior values.

All proposed formulas in the assignment are correct. No formula correction is needed.

## 2. Parameter existence, identities, and admissibility

On \([1,\infty)\), \(F\) is continuous, \(F(1)=0\), and

\[
 F'(q)=q^{-1}+2q^2>0.
\]

Also \(F(q)\ge\frac23(q^3-1)\to\infty\). The intermediate value theorem and strict monotonicity give existence and uniqueness for every \(\log C\ge0\). They also give \(q=1\iff C=1\), and

\[
 C=q\exp\!\left(\frac23(q^3-1)\right).
\]

The definitions imply

\[
 0<\alpha\le\beta<1,\qquad
 \beta^2=\frac{q^3}{q^3+2},\qquad
 1-\beta^2=2\alpha^2q=2\alpha^{3/2}\sqrt\beta.
\]

In particular \(\beta\ge1/\sqrt3\). Further useful consequences are

\[
 \frac\alpha q=\frac{1-\beta^2}{2\beta},\qquad
 \alpha^3=\frac{(1-\beta^2)^2}{4\beta},\qquad
 \alpha^{3/2}\beta^{3/2}=\frac\beta2(1-\beta^2).
\]

At the contacts,

\[
 E_*(\alpha)=1,\qquad
 E_*(\beta)=q\exp\!\left(\frac23(q^3-1)\right)=C.
\]

On a nonempty free arc,

\[
 k_*'(v)=\frac1{2v}+\frac{\sqrt v}{\alpha^{3/2}}>0.
\]

Thus the glued function is continuous, has values \(1\le E_*\le C\), and satisfies \(0\le k_*\le\log C\). This proves genuine admissibility without assuming it.

## 3. Why this free-arc formula is structurally derived

For an arbitrary positive continuous \(E\), put

\[
 P(v)=\int_0^v E(t)\,dt,\qquad
 Q(v)=\int_v^1\frac{2s}{E(s)}\,ds.
\]

The first-variation density for \(k=\log E\) is

\[
 A(v)=E(v)Q(v)-\frac{2vP(v)}{E(v)}.
\]

If a lower/free/upper obstacle profile has free arc \((\alpha,\beta)\), stationarity there asks \(A=0\). Writing \(y=P/E\) and differentiating \(E^2Q=2vP\) gives

\[
 2\frac{E'}E=\frac1v+2\frac EP,\qquad
 y'=-\frac{y}{2v}.
\]

Since the lower obstacle is \(E=1\), its contact data give \(P(\alpha)=\alpha\), \(E(\alpha)=1\). Consequently \(y(v)=\alpha^{3/2}/\sqrt v\). Solving \(P'/P=\sqrt v/\alpha^{3/2}\) yields

\[
 P(v)=\alpha e^{\phi(v)},\qquad
 E(v)=\sqrt{v/\alpha}\,e^{\phi(v)}.
\]

At the upper contact, \(Q(\beta)=(1-\beta^2)/C\); the stationarity identity gives \(1-\beta^2=2\alpha^{3/2}\sqrt\beta\). Defining \(q=\sqrt{\beta/\alpha}\) now forces precisely the stated \(\alpha,\beta,C\) equations.

This derivation motivates the candidate; it is not an assumption that every optimizer has this obstacle pattern. The explicit calibration below independently proves global optimality and uniqueness of this candidate.

## 4. Exact primitives and calibration density

For \(E=E_*\), define \(d=\beta-\alpha/q\). Direct differentiation and endpoint matching give

\[
 P(v)=\begin{cases}
 v,&0\le v\le\alpha,\\
 \alpha e^{\phi(v)},&\alpha\le v\le\beta,\\
 C(v-d),&\beta\le v\le1,
 \end{cases}
\]

and

\[
 Q(v)=\begin{cases}
 3\alpha^2-v^2,&0\le v\le\alpha,\\
 2\alpha^2e^{-\phi(v)},&\alpha\le v\le\beta,\\
 (1-v^2)/C,&\beta\le v\le1.
 \end{cases}
\]

For example, \(\phi'(v)=\sqrt v/\alpha^{3/2}\), so \((\alpha e^\phi)'=E_*\) and \((2\alpha^2e^{-\phi})'=-2v/E_*\). The latter formula agrees at \(\beta\) because

\[
 2\alpha^2 e^{-\phi(\beta)}=2\alpha^2q/C=(1-\beta^2)/C.
\]

The lower formula for \(Q\) then follows by integrating \(2s\) from \(v\) to \(\alpha\). The upper formula for \(P\) follows from \(P(\beta)=\alpha C/q\).

Substitution into the density gives exactly

\[
 A(v)=\begin{cases}
 3(\alpha^2-v^2),&0\le v\le\alpha,\\
 0,&\alpha\le v\le\beta,\\
 -3(v-\beta)\left(v+\frac1{3\beta}\right),&\beta\le v\le1.
 \end{cases}
\]

On the upper interval the direct expression is \(1-3v^2+2dv\). Factoring it uses

\[
 2d=2\beta-2\alpha/q=3\beta-1/\beta,
\]

which follows from \(1-\beta^2=2\alpha^2q\). Hence \(A\ge0\) on the lower obstacle and \(A\le0\) on the upper obstacle, with strict signs in their relative interiors away from the contacts.

## 5. Exact value

Since \(I(k_*)=\int_0^1 2vP(v)/E_*(v)\,dv\), the primitives above give

\[
 I(k_*)=\frac23\alpha^3
   +\frac43\alpha^{3/2}(\beta^{3/2}-\alpha^{3/2})
   +\frac23(1-\beta^3)-d(1-\beta^2).
\]

For a transparent simplification write \(u=1-\beta^2\). The first two terms equal

\[
 \frac23\beta u-\frac{u^2}{6\beta},
\]

and \(d=\beta-u/(2\beta)\). Therefore

\[
 I(k_*)=\frac23(1-\beta^3)-\frac13\beta u+\frac{u^2}{3\beta}
       =\boxed{\frac23-\beta+\frac1{3\beta}}.
\]

No approximate arithmetic or search is used.

## 6. Exact convex deficit and uniqueness

Let \(k\) be any continuous real-valued function on \([0,1]\), temporarily without a box constraint. Write

\[
 \delta=k-k_*,\qquad w_*(v,s)=2s\exp(k_*(v)-k_*(s)),\qquad R(x)=e^x-1-x.
\]

Subtracting the integrands and inserting the linear term gives the exact identity

\[
 I(k)-I(k_*)=
 \int_0^1 A(v)\delta(v)\,dv
 +\int_0^1\int_0^s w_*(v,s)R(\delta(v)-\delta(s))\,dv\,ds.
\]

Indeed, Fubini changes the linear pair term into

\[
 \int_0^1\!\!\int_0^s w_*(v,s)(\delta(v)-\delta(s))\,dv\,ds
 =\int_0^1\left(E_*(v)Q(v)-\frac{2vP(v)}{E_*(v)}\right)\delta(v)\,dv.
\]

The corresponding generic identity holds with any continuous baseline \(k_0\), with its own \(P,Q,A\); this is a natural shared formalization engine.

For \(k\in\mathcal K_C\), the identity can be written in a manifestly sign-controlled, fully explicit form:

\[
\begin{aligned}
 I(k)-\left(\frac23-\beta+\frac1{3\beta}\right)
  ={}&\int_0^\alpha3(\alpha^2-v^2)k(v)\,dv\\
   &+\int_\beta^1 3(v-\beta)\left(v+\frac1{3\beta}\right)(\log C-k(v))\,dv\\
   &+\int_0^1\int_0^s w_*(v,s)R(\delta(v)-\delta(s))\,dv\,ds.
\end{aligned}
\]

All three terms are nonnegative: the obstacle bounds handle the first two, and strict convexity of the exponential gives \(R(x)\ge0\), with equality exactly at \(x=0\). This proves the global minimum.

If equality holds, the last integral is zero. Its integrand is continuous and nonnegative on the closed triangle and its weight is strictly positive whenever \(0<v<s<1\). A positive value at an interior pair would, by continuity, give a rectangle of positive measure on which it stays positive, contradicting zero integral. Hence

\[
 \delta(v)=\delta(s)\qquad(0<v<s<1).
\]

Thus \(\delta\) is constant on \((0,1)\), and continuity extends this to \([0,1]\). Say \(\delta\equiv c\). Because \(k_*(0)=0\), admissibility gives \(c=k(0)\ge0\); because \(k_*(1)=\log C\), admissibility gives \(c=k(1)-\log C\le0\). Therefore \(c=0\). Conversely \(k=k_*\) plainly gives equality.

This argument proves pointwise uniqueness, not only almost-everywhere uniqueness. It uses continuity explicitly. For an implementation whose immediate integral lemma returns almost-everywhere equality, the continuous-to-pointwise upgrade is a real remaining lemma, not an automatic change of statement.

## 7. Degenerate endpoint and contact regularity

If \(C=1\), then \(q=1\) and \(\alpha=\beta=1/\sqrt3\). The free arc has empty interior, \(E_*\equiv1\), \(k_*\equiv0\), and every admissible \(k\) is already identically zero. Thus the unique minimum is \(I(0)=2/3\). The calibration formulas still agree and reduce to \(A(v)=1-3v^2\). Do not infer a derivative jump by applying a free-arc derivative formula when the arc is empty.

If \(C>1\), then \(0<\alpha<\beta<1\). The one-sided derivatives are

\[
 k'_{*,-}(\alpha)=0,\qquad k'_{*,+}(\alpha)=\frac3{2\alpha},
\]

and

\[
 k'_{*,-}(\beta)=\frac1{2\beta}+\frac q\alpha
   =\frac{1+2q^3}{2\beta},\qquad k'_{*,+}(\beta)=0.
\]

For \(E_*\), the respective jumps use slopes \(0,3/(2\alpha)\) and \(C(1+2q^3)/(2\beta),0\). Both functions are globally Lipschitz and piecewise real analytic, but neither is differentiable at either contact.

Consequently no \(C^1\) admissible \(k\) can attain this continuous-class minimum when \(C>1\): equality would force it to equal the nondifferentiable \(k_*\). This is only a one-dimensional optimizer nonattainment statement. It does **not** establish smooth geometric nonattainment for arbitrary CK forms, say anything about the Haar remainder, or prove a smooth approximation theorem.

## 8. Formalization dependencies and exact remaining gates

A coherent dependency order is:

1. Parameter existence/uniqueness and elementary positive-radical identities.
2. The explicitly glued profile, endpoint consistency, and actual continuity/box membership.
3. A generic exact exponential pair deficit identity for two continuous profiles, including Fubini.
4. The exact primitive formulas and the resulting explicit density.
5. Exact evaluation of \(I(k_*)\), nonnegative calibration, and equality classification.
6. Contact one-sided derivatives and the separate \(C=1\) endpoint.

These are prospective mathematical statements; root owns all Lean API choices. No geometric metric, curvature, producer, reflection assumption, blackbox, or source theorem was used. This packet does not supply Lean evidence, a blackbox registry entry, stability coercivity, smooth approximation, or geometric sharpness.

Remaining acceptance gates: native Lean implementation and compilation under the pinned release; compiler diagnostics and declared linters; actual transitive axiom closure; independent mathematical statement review; canonical integration and affected consumers. This packet is not an established manuscript result until those gates close.
