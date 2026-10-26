ATTACK REFUTED: a C¹ divergence-free field can have a C² vector potential while every Coulomb-gauge potential fails to be C².

This is a rigorous informal refutation of the proposed continuous-Poisson
obstruction, with partial Lean formalization of the gauge quantifier. It is
**neither a disproof nor a proof of the final clause of PMA 10.43**. In particular,
the endpoint survives this route; its general truth value remains unresolved
in this lane. There is no counterexample to the contract here.

Research lane: ticket #14, `research/t14-1043-cex`, based on
`05c9ea2f709ce854be0b794350a818d9ebd102f8`. Date: 2026-10-26.

The launch brief, `research/pma-ch10-b-43-blocker.md`, and
`rudin/Rudin/PMA/Chapter10/VectorPotentials.lean` were read in full. The source
was read at printed pp. 281–282 of `/root/sources/pma3.pdf` (PDF pp. 290–291),
including a rendered inspection of p. 281. The user-supplied
`/tmp/t14-lit-report.md` was read in full immediately after its availability
was announced. Its planar reduction is retained; its proposed gauge obstruction
needs the corrections below.

## 1. Explicit field and regularity — informal proof

Let

\[
 \rho=e^{-2},\quad D=\{(x,y):x^2+y^2<\rho^2\},\quad E=D\times(-1,1).
\]

This is an open convex domain, so the identity provides the required C² domain
equivalence. For \(r=\sqrt{x^2+y^2}>0\), set

\[
 L=\log(1/r),\qquad P=x^3-3xy^2=r^3\cos(3\theta),\qquad u=P\sqrt L.
\]

Set \(u(0,0)=0\). The polynomial \(P\) is homogeneous harmonic of degree 3.
Differentiating the displayed formula gives, for \(j=0,1,2\),

\[
 |D^j u|=O(r^{3-j}\sqrt L).
\]

The bounds for \(u\) and \(Du\) prove differentiability at zero successively;
the bound for \(D^2u\) proves continuity there. Thus \(u\in C^2(D)\) and its
derivatives through order 2 vanish at zero. These are direct derivative bounds,
using \(r^\varepsilon L^m\to0\) for \(\varepsilon>0\) and fixed \(m\).

For any radial \(s\),
\(\Delta(Ps)=P(s''+7s'/r)\). Consequently, with

\[
 q(r)=-3L^{-1/2}-\tfrac14L^{-3/2},\qquad
 f(x,y)=\frac{P(x,y)}{r^2}q(r),\qquad f(0,0)=0,
\]

we have \(\Delta u=f\), including at zero. Furthermore

\[
 q(r)\to0,\qquad rq'(r)=-\tfrac32 L^{-3/2}-\tfrac38L^{-5/2}\to0.
\]

Since \(P/r^2\) is smooth and homogeneous of degree 1 away from zero,
\(|f|=o(r)\) and \(|Df|\le C(|q|+r|q'|)=o(1)\). Thus \(f\in C^1(D)\),
with \(Df(0)=0\). Define

\[
 F(x,y,z)=(0,0,f(x,y)).
\]

Then \(F\in C^1(E)\) and \(\operatorname{div}F=0\). This datum need not satisfy
any extra Hölder assumption: along \(y=0,x>0\),
\(f_x=q+xq'\sim-3/\sqrt{\log(1/x)}\), which is not \(O(x^\alpha)\) for any
\(\alpha>0\). The field is in the actual C¹ class under investigation.

For the contract's convention of total functions on Euclidean space, extend
these functions arbitrarily outside \(E\); only their restrictions to the open
set are used.

## 2. Every Coulomb potential fails C² — informal proof

Put \(H=(-u_y,u_x,0)\), independent of \(z\). Then \(H\in C^1(E)\),
\(\operatorname{curl}H=F\), and \(\operatorname{div}H=0\), by the previous
Laplacian calculation and equality of mixed second derivatives of \(u\).
However, for \(x>0\),

\[
 H_2(x,0,z)=x^2\left(3\sqrt{\log(1/x)}-
 \frac1{2\sqrt{\log(1/x)}}\right).
\]

The value and first x derivative vanish at \(x=0\), whereas \(H_2/x^2\to+\infty\).
The second-order Taylor estimate for a C² function excludes this behavior.
Hence \(H\) is not C² near any point on the axis.

Suppose **any** \(B\in C^2(E)\), including a field depending on \(z\), satisfied
\(\operatorname{curl}B=F\) and \(\operatorname{div}B=0\). Then \(K=B-H\in C^1\)
has zero curl and divergence. Commutation of distributional derivatives gives

\[
 \Delta K=\nabla\operatorname{div}K-
 \operatorname{curl}\operatorname{curl}K=0.
\]

Each component of \(K\) is smooth by harmonic regularity. For completeness,
in this continuous case one can mollify on an interior ball, pass the spherical
mean-value identities to the locally uniform limit, and then integrate those
identities against a smooth normalized radial kernel. The resulting identity
\(K=K*\eta\) on a smaller ball proves smoothness. This is also an instance of
Weyl's lemma, [Kristensen, Theorem 14.1, p. 52](https://www.maths.ox.ac.uk/system/files/attachments/Lecture%20Notes.pdf).
Then \(H=B-K\) would be C², a contradiction. This proves the universal
**Coulomb** obstruction, with no boundary condition and no restriction on
the competitors' dependence on coordinates.

In fact the continuous-data Poisson system itself has no C² solution here:
\(\Delta H=(-f_y,f_x,0)=-\operatorname{curl}F\) distributionally. Any C²
solution of that same Poisson system would differ from \(H\) by a smooth
harmonic vector field, giving the same contradiction. Section 3 nevertheless
exhibits a C² solution of the original curl equation.

## 3. The same field has an explicit C² potential — informal proof

Define the convergent one-dimensional integral

\[
 a(r)=r^{-3}\int_0^r s^2q(s)\,ds,
 \quad V(x,y)=a(r)\frac{P(x,y)}{r^2}(x,y),
 \quad G=(-V_2,V_1,0),
\]

with \(V(0)=0\). This is an explicit quadrature, not an implicit PDE solution.
The fundamental theorem of calculus gives

\[
 ra'=q-3a,\qquad r^2a''=rq'-4q+12a,
 \qquad |a(r)|\le\tfrac13\sup_{0<s\le r}|q(s)|\to0.
\]

It follows that \(a,ra',r^2a''\to0\). The factor
\(W=(P/r^2)(x,y)\) is smooth homogeneous of degree 2 away from zero, so
\(|W|\le Cr^2, |DW|\le Cr, |D^2W|\le C\). Therefore

\[
 \frac{|V|}{r^2}\le C|a|\to0,\qquad
 \frac{|DV|}{r}\le C(|a|+r|a'|)\to0,\qquad
 |D^2V|\le C(|a|+r|a'|+r^2|a''|)\to0.
\]

The first two limits establish the derivatives at zero; the last proves their
continuity. Hence \(V\in C^2(D)\), with zero second jet at zero, and
\(G\in C^2(E)\). Finally, Euler's identity for the homogeneous factor, or
direct polar differentiation, gives

\[
 \operatorname{div}V=r\cos(3\theta)(3a+ra')=f,
 \qquad \operatorname{curl}G=(0,0,\operatorname{div}V)=F.
\]

The identities extend to the axis by continuity. This C² \(G\) is the
decisive refutation: no-C²-Coulomb does not imply no-C²-potential.

An explicit scalar gauge makes the lost regularity visible. Let

\[
 S=3x^2y-y^3=r^3\sin(3\theta),\quad
 b(r)=\sqrt L-\tfrac16L^{-1/2}-a(r)/3,\quad \chi=S b(r).
\]

Set \(\chi=0\) on the axis. The preceding estimates show \(\chi\in C^2(E)\).
The identities \(3b+rb'=3\sqrt L\) and
\(3b=3\sqrt L-\tfrac12L^{-1/2}-a\), checked using \(ra'+3a=q\), give
\(H-G=\nabla\chi\) by comparing polar components. Since \(H-G\) is not C²,
\(\chi\) is not C³. This is a permitted gauge, not an excluded one.

## 4. A whole class of attempted planar examples is repaired — informal proof

The calculation in Section 3 works for any smooth angular function \(\psi\)
and \(q\in C^1((0,\rho))\) with \(q(r),rq'(r)\to0\). Namely,

\[
 f(r,\theta)=r\psi(\theta)q(r),\qquad
 V(r,\theta)=r^2\psi(\theta)a(r)e_r,
 \quad a(r)=r^{-3}\int_0^r s^2q(s)\,ds
\]

give \(f\in C^1\), \(V\in C^2\), and \(\operatorname{div}V=f\), with the
same zero jets and estimates. Thus an isolated angular logarithmic singularity
of this form is not a counterexample to the planar divergence endpoint.
This statement is about this class only, not all C¹ planar data.

The natural radial-cutoff version of the literature report's dyadic Poisson
attack is also in this class. Choose a smooth radial cutoff \(\eta\), equal
to 1 on \([0,1]\) and 0 on \([2,\infty)\), put \(g=P\eta(r)\), and define

\[
 u_*(x,y)=\sum_{k\ge1}\frac1k2^{-3k}g(2^kx,2^ky).
\]

Derivatives of order \(j\le2\) of the kth summand are bounded by
\(C_jk^{-1}2^{-(3-j)k}\); uniform termwise differentiation proves
\(u_*\in C^2(\mathbb R^2)\) with zero second jet at zero. At \(x_N=2^{-N},y=0\),
\(u_{*,x}(x_N,0)/x_N^2=3\sum_{k=1}^N1/k\to\infty\). Thus its rotated
gradient \(H_*\) is not C². On the other hand, writing

\[
 Q(t)=t^2\eta''(t)+7t\eta'(t),\qquad
 q_*(r)=\sum_{k\ge1}k^{-1}Q(2^kr),
\]

gives \(\Delta u_*=r\cos(3\theta)q_*(r)\). At most two closed dyadic annuli
contribute at a given positive radius; their indices tend to infinity as
\(r\to0\). Boundedness of \(Q\) and \(tQ'\) proves
\(q_*,rq_*'\to0\). Section 4 therefore provides a C² planar primitive
and a C² vector potential \(G_*\). These are defined on the whole spaces:
\(q_*\) vanishes for \(r\ge1\), and the integral formula remains smooth for
all positive \(r\). Yet every Coulomb potential fails C² by the same harmonic
difference argument. This directly refutes this concrete radial dyadic
implementation, without asserting that every possible dyadic attack fails.

## 5. What remains of the literature report's settlement route

The planar reduction itself is exact. For any C¹ \(h\) on a planar open disk
\(D\), on \(D\times(-1,1)\) the field \(F=(0,0,h)\) has a C² vector potential
if and only if \(\operatorname{div}V=h\) has a C² planar solution. Given a
3D potential, restrict to \(z=0\) and put \(V=(G_2,-G_1)\); the third curl
component is precisely the planar divergence. Conversely use
\(G=(-V_2,V_1,0)\). This quantifies over all 3D potentials. A C¹ \(h\) with
no C² divergence primitive would settle the contract negatively; no such
datum is established here.

The supplied `/tmp/t14-lit-report.md` does not close this obligation:

1. Two potentials already known to be C² differ locally by a C³ scalar
   gradient. Comparing a **C¹ Coulomb representative** with a hypothetical
   C² potential permits a **C² scalar**, as both Section 3 and the Lean gauge
   equivalence show. Restricting that gauge to C³ is invalid.
2. Second derivatives of a vector potential change by third derivatives of
   the scalar gauge. Also, the trace-free symmetric part of \(DA\) suggested
   there is not gauge invariant: \(\chi=(x^2-y^2)/2\) changes it by
   \(\operatorname{diag}(1,-1,0)\), even while preserving Coulomb gauge.
3. Known C⁰ or Lipschitz input failures do not automatically supply a C¹
   datum with no C² primitive. The required regularity transfer needs a proof.
4. The scalar Poisson harmonic-difference argument remains valid, but it
   gives a smooth difference of solutions, not equality of the solutions.
   Its conclusion cannot be imported into the ungauged curl equation.

For arbitrary C² \(G\), the correct identity is
\(\Delta G=\nabla\operatorname{div}G-\operatorname{curl}F\). The first term
cannot be dropped. Solving \(\Delta\chi=-\operatorname{div}G\) to impose
Coulomb gauge would need \(\nabla\chi\in C^2\) to preserve the desired
regularity; Section 3 proves this need not be possible.

The lower endpoint distinction is documented by a primary source:
[Dacorogna–Fusco–Tartar (2003), pp. 239–245](http://www.bdim.eu/item?id=RLIN_2003_9_14_3_239_0&fmt=pdf)
proves continuous scalar data can have no Lipschitz divergence solution.
Its introduction explicitly distinguishes this from Laplace counterexamples,
because divergence solutions need not be gradients. That paper's result does
not establish the C¹-to-C² endpoint required here.

There is also a concrete obstruction to simply reusing its test family.
For compactly supported smooth \(\psi_N\) on the unit square, normalized by
\(\|\psi_{N,xx}\|_1+\|\psi_{N,yy}\|_1=1\), put
\(T_N(h)=\int h\psi_{N,xy}\). Although mixed-derivative L¹ norms can diverge,
for C¹ \(h\), integration by parts and the fundamental theorem of calculus give

\[
 |T_N(h)|\le\|h_y\|_\infty\|\psi_{N,x}\|_1
 \le\|h_y\|_\infty\|\psi_{N,xx}\|_1
 \le\|h_y\|_\infty.
\]

Thus this exact family is uniformly bounded on C¹. This estimate is an
independent calculation, not a claim that every higher-order variant fails.

No assertion that the problem is globally unpublished or open is justified
by the searches. The precise conclusion is that the sources checked here and
the constructions in this lane do not settle the endpoint. The literature
report's confidence percentages are conjectural assessments, not mathematical
evidence used in this report.

## 6. Kernel-proved content and limits

`rudin/Rudin/PMA/Chapter10/VectorPotentialGaugeResearch.lean` imports the existing
`VectorPotentials` module and introduces no endpoint assumption. Its namespace
is `Rudin.PMA.Chapter10.GaugeResearch`.

| Lean declaration | Proved assertion |
| --- | --- |
| `curl_add_eqOn`, `curl_sub_eqOn`, `curl_congr_eqOn` | Curl algebra and locality on open sets. |
| `curl_add_gradient_eqOn` | A C² scalar gauge preserves the curl of a C¹ potential. |
| `same_curl_difference_is_gradient` | C¹ potentials with equal curl differ by a C² scalar gradient on the contract's domains. |
| `exists_c2_potential_iff_exists_c2_gauge` | A fixed C¹ potential has a C² representative exactly when some C² scalar gauge makes its sum C². |
| `no_c2_potential_iff_all_gauges_fail` | Nonexistence of C² potentials is equivalent to failure for every permitted C² scalar gauge. |
| `rough_gauge_preserves_potential` | Given a non-C² gradient of a C² scalar, adding it to a C² potential produces a rough potential of the same field. |

The last lemma takes the roughness as a hypothesis; it does not kernel-prove
the logarithmic witness. The analytic construction, its derivative limits,
harmonic regularity argument, and quadrature are **informal proofs**, not Lean
proofs. No field lacking all C² potentials has been proved, informally or in Lean.

`rudin/Rudin/PMA/Chapter10/PlanarVectorPotentialResearch.lean`, namespace
`Rudin.PMA.Chapter10.PlanarResearch`, additionally kernel-proves:

- `divergence_verticalLift`: \((0,0,h(x,y))\) has zero divergence.
- `contDiff_verticalLift`, `contDiff_restrictPotential`, and
  `contDiff_liftPotential`: the constructions preserve the specified regularity.
- `c2_planar_primitive_of_c2_potential`: restriction of an arbitrary C² 3D
  potential, including one depending on \(z\), gives a C² planar primitive.
- `exists_c2_potential_iff_planar_divergence`: the exact whole-space equivalence.
- `contract_implies_c2_planar_divergence`: the unchanged contract would give
  a C² planar divergence primitive for every C¹ whole-plane datum.
- `planar_obstruction_disproves_contract`: a C¹ whole-plane datum with no
  C² planar primitive would disprove the unchanged contract. This is a
  conditional implication; its counterexample hypothesis is not established.

This second module treats the whole spaces, not general disks or cylinders.
The cylinder reduction in Section 5 remains informal. The whole-space dyadic
example in Section 4 fits the formal reduction's domain, but its analytic
properties are not formalized.

The targeted build of `Rudin.PMA.Chapter10.VectorPotentialGaugeResearch` passed.
The axiom audit of the eight principal gauge/curl lemmas reports only
`propext`, `Classical.choice`, and `Quot.sound`. Evidence files:
`/tmp/t14-cex-lean-build.log`, `/tmp/t14-cex-gauge-axioms.log`, and
`/tmp/t14-cex-lean-status.md`. No `sorry` or custom axiom is used.
The targeted planar-module build also passed, and seven principal planar
declarations have the same standard axiom sets. Additional evidence:
`/tmp/t14-cex-planar-build.log` and `/tmp/t14-cex-planar-axioms.log`.
Reproduce the focused compilation from `rudin/` with
`lake build Rudin.PMA.Chapter10.VectorPotentialGaugeResearch Rudin.PMA.Chapter10.PlanarVectorPotentialResearch`.
The modules are intentionally separate research imports; no root import or
Chapter 10 coverage audit was changed to present the endpoint as settled.

## 7. Checkpoint and disposition

The required checkpoint is `/tmp/t14-cex-checkpoint-1.md`. Its initial formulas
used the equally valid larger cylinder \(r<e^{-1},z\in\mathbb R\); this report
standardizes to the bounded cylinder in Section 1. Independent calculation and
adversarial review confirmed the signs, radial identities, endpoint derivative
estimates, and quantification over z-dependent Coulomb competitors.

The full contract and Chapter 10 audits remain unchanged. This is a partial
research branch, not a complete disproof, and does not justify a disproof PR.
The useful handoff is the exact planar-divergence problem together with the
prohibition on treating a rough Coulomb representative's gauge as necessarily
C³. A successful next counterexample needs a new all-gauges obstruction beyond
the logarithmic/angular Poisson singularity repaired above.
