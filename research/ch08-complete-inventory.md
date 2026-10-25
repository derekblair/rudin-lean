# Chapter 8 complete-lane inventory and prior candidate provenance

The source inventory below is preserved from `origin/ch8-codex-20261022`,
`research/pma-ch08-source-review.md` (prior review dated 2026-10-22).
It enumerates all 22 main-text numbered items and distinguishes previously
implemented 8.1–8.6 from then-pending 8.7–8.22. Statements about the old task
brief, acceptance, and pending work below describe that prior run, not this lane.
The current lane independently checks the printed source and records current
coverage in its final report; previous acceptance is provenance, not fresh
compilation evidence.

---

# PMA Chapter 8 independent source inventory review

Reviewer: `ch8_fidelity`, 2026-10-22. Source: authorized local third-edition PDF `/home/derekblair/projects/math/references/sources/pma3.pdf`, printed pp.172-195 (PDF pp.181-204), with the exercise boundary on printed p.196 (PDF p.205). Every relevant page was rendered and visually inspected in memory using the PDF skill; no source PDF copy, page image, extracted proof text, or extended exposition was saved. This record contains brief mathematical paraphrases only. `PROGRAM.md`, `PROGRESS.md`, `QUEUE.md`, and the Chapter 7 inventory/fidelity conventions were read before extraction. This source inventory is independent of the new implementation and is not a kernel-verification claim.

## Numbering discrepancy in the task brief

The brief's topic ranges do not match Rudin's third-edition numbering. The power-series section consists of **8.1-8.5**. Exponential/logarithmic functions occupy **8.6 and its surrounding unnumbered development**, printed pp.178-182. **8.7 is trigonometric**, and **8.8 is the fundamental theorem of algebra**. Thus numbered items 8.8-8.17 must not be labeled exponential/logarithmic results. Preserve Rudin's identifiers; report the discrepancy and distinguish completion of intended topics from completion of the brief's literal numeric ranges. The power-series section contains no separate numbered integration theorem; relevant ordinary integration can be attached to the foundational node if included, but must not be assigned an invented Rudin number.

## Source conventions

Power-series arguments are real. Coefficients are not restricted to real numbers, so the natural inherited Chapter 7 codomain is complex; a real-only implementation requires a proved complex bridge for full coverage. The opening discussion allows a positive convergence radius including infinity. A formulation for every finite positive radius can represent this through an explicit all-finite-subradii corollary. Series means limits of ordered finite partial sums. In particular, endpoint convergence in 8.2 may be conditional. A premise `Summable c` in a finite-dimensional normed space is stronger than the source's ordered-series premise and does not alone cover 8.2.

## Numbered power-series nodes

| Node | Brief statement and attached scope |
|---|---|
| **PMA-8.1**, theorem/corollary, pp.173-174 | A power series convergent throughout `(-R,R)` converges uniformly on every smaller centered closed interval; its sum is continuous and differentiable inside, and its derivative is the termwise differentiated series. The unnumbered corollary gives all iterated derivatives by the falling-factorial coefficient series and `f^(k)(0) = k! c_k`, including order zero. Coefficients are consequently unique. The following warning says that smoothness does not imply representation by the Taylor series; its exercise-specific construction is excluded, but the warning should be recorded when declaring all attached discussion covered. |
| **PMA-8.2**, theorem/application, pp.174-175 | If the ordered coefficient series converges to `s`, the power-series sum on `(-1,1)` tends to `s` as `x` tends to 1 from the left. Include existence/convergence of the interior power-series sum and endpoint continuity. Scaling gives continuity at any convergent endpoint of an interval of convergence. Attached application: if two ordered series and their Cauchy product all converge, the Cauchy-product sum is the product of the two sums (the result previously numbered 3.51). Absolute convergence is not an added premise. |
| **PMA-8.3**, theorem, pp.175-176 | For a double sequence, if each row's absolute-value series has sum `b_i` and the series of the `b_i` converges, both iterated complex sums exist and are equal. The source uses positive indices; a reindexing to naturals starting at zero is equivalent if explicit. Do not replace existence by an unqualified equality of totalized sums. |
| **PMA-8.4**, theorem, pp.176-177 | If a power series represents `f` on `(-R,R)` and `a` is interior, its Taylor series centered at `a`, with coefficients `f^(n)(a)/n!`, converges to `f(x)` whenever `|x-a| < R-|a|`. The radius bound is a guarantee, not a claim that it is the exact new radius. |
| **PMA-8.5**, theorem, pp.177-178 | Suppose two power series converge throughout the same open centered interval. If their equality set has an accumulation point anywhere in that interval, every corresponding coefficient agrees and the sums agree on the whole interval. An accumulation point only at an endpoint is insufficient. Restriction to accumulation at the original center would be weaker than the source. |

## Exponential and logarithmic continuation

**PMA-8.6**, theorem and surrounding development, pp.178-182:

- Define the complex exponential by its everywhere-convergent factorial power series; establish addition, value at zero, nonvanishing, reciprocal/negation, complex derivative, and finite-sum/product identities. Identify its real restriction with real exponentiation of `e`, including rational powers and the supremum convention described in the source.
- Numbered theorem clauses: real exponential is continuous and differentiable; its derivative equals itself; it is strictly increasing and positive; `exp(x+y)=exp(x)exp(y)`; limits are infinity at positive infinity and zero at negative infinity; for every natural `n`, `x^n exp(-x)` tends to zero at positive infinity.
- Attached logarithmic development: logarithm is the inverse of the real exponential on positive reals, is strictly increasing and differentiable there, has derivative `1/x`, has value zero at 1, and equals the oriented ordinary integral of `1/t` from 1 to `x`. Retain both inverse identities. It converts products of positive reals into sums and tends to infinity at infinity and negative infinity at zero from the right.
- Attached real powers: for positive base, `x^alpha = exp(alpha log x)` agrees with integer/rational powers and the earlier supremum convention. Its derivative is `alpha*x^(alpha-1)`; the integral has the power antiderivative when `alpha != -1` and logarithm when `alpha = -1`. Finally, `x^(-alpha)*log x` tends to zero at positive infinity for every positive real `alpha`.

The logarithmic integral should use or bridge explicitly to the repository's native Chapter 6 Riemann integral. A library Lebesgue integral identity by itself does not establish that native statement. Unnumbered prerequisite assertions can be proved as support theorems, but partial support does not complete every attached item of 8.6.

## Literal 8.7 boundary, beyond the intended exponential/log topic

**PMA-8.7**, theorem and surrounding trigonometric development, pp.182-184: complex exponential has period `2*pi*i`; real cosine and sine have period `2*pi`; `exp(i*t) != 1` for `0<t<2*pi`; each complex unit-circle point has a unique representation `exp(i*t)` with `t` in `[0,2*pi)`. Attached development identifies sine/cosine from the exponential, their values/derivatives, the norm-one identity, and pi via the first positive cosine zero. The unit-circle parametrization is a simple closed curve of length `2*pi`, with initial arcs of length equal to their parameter, connecting the analytic definitions to the usual geometric trigonometric functions. This is not a power-series numbered node. The next item, 8.8, asserts a root for every nonconstant complex polynomial.

## Complete numbered count and pending later scope

The chapter has **22 consecutive numbered main-text items, 8.1-8.22**. The last item begins on printed p.194 and ends on p.195; exercises begin on p.196 and are excluded. The following remaining inventory is a concise scope guide for pending work, not a completion claim. Fourier integrability here means the source's ordinary Riemann integrability, with complex integration as in Chapter 6. The gamma integrals are improper integrals, including endpoint and infinity convergence as needed.

| Node | Type and page | Brief scope |
|---|---|---|
| **PMA-8.8** | Theorem, pp.184-185 | Every complex polynomial with positive degree and nonzero leading coefficient has a complex root. |
| **PMA-8.9** | Definition/discussion, pp.185-186 | Define complex trigonometric polynomials in equivalent sine/cosine and exponential forms; include periodicity, exponential orthogonality, coefficient recovery, real-value conjugate symmetry, symmetric partial sums, and the Fourier coefficients/series of an integrable function. |
| **PMA-8.10** | Definition/examples, pp.186-187 | Define orthogonal and orthonormal complex function systems on an interval and Fourier coefficients relative to them; include the normalized exponential and sine/cosine systems, and distinguish Fourier-series notation from a convergence claim. |
| **PMA-8.11** | Theorem, pp.187-188 | The first `n` Fourier coefficients give the unique mean-square best approximation among combinations of the first `n` orthonormal functions; include the exact equality condition and finite norm-square identity/bound. |
| **PMA-8.12** | Theorem, p.188 | Bessel's inequality bounds the sum of squared Fourier-coefficient norms by the squared integral norm; the coefficients tend to zero. |
| **PMA-8.13** | Numbered discussion, pp.188-189 | For periodic integrable functions define symmetric trigonometric Fourier sums and Dirichlet kernels, identify their sine-quotient formula away from its zero denominator, and express partial sums as convolution integrals; include the finite mean-square identity. |
| **PMA-8.14** | Theorem/corollary, pp.189-190 | A local Lipschitz bound at a point implies pointwise convergence of its Fourier partial sums there; attached localization says local equality of two functions makes the difference of their partial sums tend to zero there. |
| **PMA-8.15** | Theorem, p.190 | Every continuous complex `2*pi`-periodic function admits a trigonometric polynomial approximating it within any prescribed positive uniform error on the whole real line. |
| **PMA-8.16** | Parseval theorem, pp.191-192 | Fourier partial sums of periodic Riemann-integrable functions converge in mean square; the integral inner product equals the coefficient inner product, and the norm-square Parseval identity follows. |
| **PMA-8.17** | Definition, p.192 | For positive real `x`, define gamma by the convergent improper integral of `t^(x-1)*exp(-t)` over `(0,infinity)`. |
| **PMA-8.18** | Theorem, p.192 | Gamma satisfies `Gamma(x+1)=x*Gamma(x)` for positive `x`, has factorial values at positive integers, and has convex logarithm on the positive reals. |
| **PMA-8.19** | Theorem/consequence, p.193 | A positive function on the positive reals with the gamma recurrence, value 1 at 1, and convex logarithm equals gamma; include the resulting Euler limit formula for every positive argument. |
| **PMA-8.20** | Theorem, pp.193-194 | For positive `x,y`, the beta integral over `(0,1)` equals `Gamma(x)*Gamma(y)/Gamma(x+y)`. |
| **PMA-8.21** | Numbered consequences, p.194 | Give the trigonometric beta integral, gamma value at one-half, the substitution expressing gamma using `exp(-s^2)`, the Gaussian integral, and gamma's duplication formula. |
| **PMA-8.22** | Stirling formula, pp.194-195 | As positive real `x` tends to infinity, `Gamma(x+1)/((x/e)^x*sqrt(2*pi*x))` tends to 1; this includes the factorial specialization. |

The literal 8.7 statement and its attached scope appear immediately above. Nodes 8.7-8.22 fall beyond the intended power-series then exponential/logarithmic topic sequence in this lane, notwithstanding the brief's inaccurate ranges.

## Review status

The source inventory and discrepancy above are established. Concrete new Lean statements require an independent comparison to this scope before completed-node acceptance. No new Lean production files were edited and no build or git mutation was performed during source extraction.

## Comparison with the production inventory

After completing the independent source extraction, the reviewer read
`research/pma-ch08-inventory.md`, SHA256
`870cf2ed10d39dd1b4924d7fd8bb6e539a50b5bfb60944da3f6defd7594a1e7a`.
**ACCEPTED:** its 22 identifiers, page mapping, brief statements, attached scopes,
numbering correction, and explicit distinction between this lane's 8.1-8.6 topic
scope and pending 8.7-8.22 agree with the independently inspected source. No
numbered source item is missing and no extra numbered node is invented.
