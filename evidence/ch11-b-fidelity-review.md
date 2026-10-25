# Chapter 11 second-half fidelity review

Source: `/home/derekblair/projects/math/references/sources/pma3.pdf`, printed
pp. 315–332, with the full numbered-node inventory in `ch11-b-inventory.md`.
The confirmed lane boundary is A: 11.1–11.23, B: 11.24–11.45.

This review compares statements and encodings with the source. It does not
replace the final build result or axiom audit. `L2.lean`, `Hilbert.lean`, and
`Fourier.lean` were read independently against the source. The reviewer also
implemented the extended-real and simple-integral compatibility additions in
`Integrals.lean`, so review of those additions is not independent authorship.
The separate L2/Hilbert worker subsequently reviewed the complete integral
module independently against 11.24–11.32 and accepted the statement scope,
including both finite signed parts, infinite signed invariance, set-local
hypotheses, and the incomplete-measure qualification.
The modules implementing 11.33 were subsequently reviewed by the separate
L2/Hilbert worker, including the native partition and integral bridges.
The final 11.33 review is recorded below.

## Numbered-node statement coverage inspected

| Node | Inspected coverage and qualifications |
|---|---|
| 11.24 | Nonnegative countable additivity includes infinity. Signed and complex integrable cases use convergent `HasSum`, with a direct extended-real signed-parts wrapper. Null deletion is covered for nonnegative, finite signed/complex, and admissible infinite signed integrals. |
| 11.25 | Null exceptional-set definition, equivalence relation, subset-integral invariance, finite almost everywhere, measurable real representative, and equality to the positive-minus-negative integral. Invariance includes infinite signed expressions where the source integral is defined. |
| 11.26 | Absolute-value integrability and integral bound for finite real/complex functions; extended-real wrapper proves the absolute-value integral finite and identifies the signed integral through its representative. |
| 11.27 | Domination implies integrability, with an extended-real wrapper giving both finite signed-part integrals. Almost-everywhere domination is allowed. |
| 11.28 | Genuine limit of integrals in the extended nonnegative line; supremum and given pointwise-limit formulations, explicit measurable supremum, almost-everywhere version, and a wrapper with hypotheses only on the integration set. |
| 11.29 | Sum integrability and integral additivity. Extended-real inputs are finite almost everywhere, and their sum has both signed-part integrals finite. |
| 11.30 | Integral/series interchange without finiteness assumptions, plus measurable series integrand and an almost-everywhere measurable form for restricted measures. |
| 11.31 | Fatou inequality for the pointwise lower limit, including infinite values, plus measurable lower limit and an almost-everywhere measurable form for restricted measures. |
| 11.32 | Integrability of every term and the limit, convergence of integrals, almost-everywhere variant, finite-measure bounded-convergence corollary, and direct extended-real signed-parts convergence. See the completeness qualification below. |
| 11.33 | Both native Riemann/Lebesgue integral comparison and the bounded-function continuity criterion are proved; the two attached fundamental-theorem assertions are also included. |
| 11.34 | Raw complex measurable functions, explicit finite squared-modulus integral criterion, square-root norm, quotient-norm bridge, and complex integral as real plus imaginary part. |
| 11.35 | Both product integrability and the Schwarz bound on the integral of its modulus. |
| 11.36 | Both closure under addition and Minkowski's norm inequality. |
| 11.37 | Quotient equality exactly matches almost-everywhere equality; quotient distance equals the raw difference norm; zero-distance criterion and metric instance are explicit. |
| 11.38 | Every interval L2 input has an arbitrarily close continuous approximation. The approximant is globally continuous, a stronger conclusion than continuity only on the interval. |
| 11.39 | Integral orthonormality, exact coefficient convention, raw-function coefficient bridge, Bessel inequality with summability, and least-square approximation including uniqueness. |
| 11.40 | Symmetric integer partial sums converge in the ordinary interval L2 norm; Parseval has the exact factor `1/(2π)`; zero-coefficient and equal-coefficient uniqueness are both included. |
| 11.41 | Norm convergence and eventual two-index Cauchy condition, each proved equivalent to the metric formulation. |
| 11.42 | Quotient completeness and explicit raw measurable-function limit versions. |
| 11.43 | Square-summable prescribed coefficients give a limit of the actual finite sums and recover all prescribed coefficients; raw-function form is also present. |
| 11.44 | Completeness uses exactly the zero-coefficients-imply-zero-norm criterion; the resulting Hilbert-basis construction proves the connection to library completeness. |
| 11.45 | Parseval, Fourier expansion, and the one-to-one isometric coordinate correspondence with square-summable sequences. |

No missing main conclusion was found in the inspected 11.24–11.45 statements.
The parenthetical on printed p. 328 that Fourier coefficients can also be
defined for L1 functions is covered by `pma11_39_l1_fourier_integrand`, in
addition to the coefficient definition and exact integral formula.

## Final independent review of 11.33

The native Chapter 6 `RIntegrable` and `RIntegral` are retained exactly. No
measurability premise is added to the bounded-function criterion. The forward
proof chooses summably small Darboux gaps and excludes the countable union
of partition endpoints to obtain ordinary continuity locally. The reverse
proof uses uniform partitions and dominated convergence of their gaps. The
integral comparison uses the exact identities between step-function integrals
and Darboux sums, then squeezes their common limit.

Repeated partition points give empty half-open cells and zero weights, while
the closed-cell extrema remain valid. Singleton intervals are included:
almost-everywhere assertions are vacuous and both integrals vanish. The final
continuity assertion is relative to the closed interval; the endpoint
distinction is null. `IntegrableOn` represents completed Lebesgue integrability
through almost-everywhere measurability, so non-Borel null modifications are
not excluded. The attached fundamental theorems require only the printed
integrability hypotheses and retain interval-relative endpoint derivatives.

## Integral semantics and the first-half dependency

The first-half names for 11.21–11.22 landed in commit
`dda199864725d8b6debcf32e0d2a36800c7c3cc1` during final verification. This lane
incorporated that commit and subsequently rebased onto
`d8c233c488ffe37172a6660af36d6b66ad7c68c2`. The integral semantics and direct native connections
are now both proved:

- `simple_integral_eq_finite_sum` identifies the library simple integral with
  the finite coefficient-times-level-set-measure sum inside the integration
  set.
- `nonnegative_integral_eq_sup_simple_sums` identifies the library nonnegative
  integral with the supremum of those sums over finite-valued nonnegative
  measurable simple functions below the integrand. It uses `ℝ≥0` simple
  values, so infinity is not silently allowed among the source's simple
  coefficients. Infinite integrands and infinite integral values are retained.
  A set-local variant requires the simple function to lie below the integrand
  only on the integration set, so no unprinted condition outside that set is
  introduced.
- The extended-real representative results start from finite positive and
  negative part integrals, prove finiteness almost everywhere, and prove that
  the Bochner integral of the real representative is exactly their difference.
  Subset versions and source-facing countable-additivity, absolute-integral,
  domination, addition, and dominated-convergence results use this connection.
- The signed expressions for null deletion and almost-everywhere invariance
  retain `EReal` differences, so one infinite part is not lost by a premature
  `toReal`. As in the source, they represent a signed integral only when both
  part integrals are not simultaneously infinite.

These are compatibility theorems, not replacement definitions or duplicate
first-half numbered nodes. `NativeIntegration.lean` proves direct connections
to `simpleIntegral`, `nonnegativeIntegral`, `IntegralDefined`,
`LebesgueIntegrable`, and `lebesgueIntegral`. Its native-facing versions of
11.24–11.32 include signed countable additivity, absolute integrability,
domination, addition, and dominated convergence with an extended-real native
integrable majorant. No first-half integral dependency remains unresolved.

## Encodings, generalizations, and the one semantic qualification

1. Nonnegative extended values use `ℝ≥0∞`; signed extended values use `EReal`.
   The simple-supremum and signed-parts equations above preserve the source's
   integral semantics. This is a representation change, not a finite-value
   restriction.
2. Integration over a measurable set is represented by a restricted measure.
   Several invariance lemmas hold even for arbitrary subsets, a generalization
   of the source's measurable-set hypotheses.
3. The real/complex integration lemmas are generalized to suitable normed
   vector spaces and to almost-everywhere strong measurability. The original
   measurable real and complex cases are included. Removing unused
   completeness hypotheses from those general lemmas does not alter their
   real/complex specialization.
4. A general measure space need not be complete. An arbitrarily prescribed
   almost-everywhere limit can fail strict measurability after changes on a
   null subset. The extended-real dominated-convergence declaration explicitly
   documents the resulting use of an almost-everywhere measurable
   representative. The raw-function completeness theorem chooses a measurable
   representative, rather than asserting that all arbitrary null modifications
   are measurable. This qualifies the source's informal null-modification
   language; it is not an unannounced complete-measure hypothesis.
5. Extended-real addition is total in Lean. For integrable summands, the
   opposite-infinity exceptional cases occur only on a null set. The addition
   wrapper explicitly documents that its totalized values there do not
   determine the integral.
6. Sequence indexing begins at zero instead of one. Cauchy tails use `≥ N`
   instead of `> N`. Both are harmless reindexings, documented at the relevant
   declarations.
7. After 11.37, `Lp ℂ 2 μ` implements the source's identification modulo null
   equality. Its use in orthonormal systems and completeness is accompanied
   by norm, equality, coefficient-integral, and raw-function bridges. It does
   not replace the source's Fourier coefficients by an unrelated abstract
   inner product.
8. Interval density and Fourier results allow `MemLp` representatives with
   almost-everywhere measurability. Thus they include Lebesgue measurable
   functions even when the ambient library measure is presented on Borel
   sets. No extra Borel-measurability hypothesis or endpoint periodicity
   requirement is imposed.
9. Fourier transfer uses normalized Haar measure on the additive circle,
   while the final interval norm is unnormalized. The proof explicitly
   converts by `2π` and proves the printed coefficient formula. The choice
   of a half-open fundamental interval affects only endpoints of measure
   zero; the final claims concern the closed interval from the source.

Apart from the explicit incomplete-measure qualification in item 4, these are
faithful representations or generalizations of the printed statements. The
final report should retain this list and independently record the final state
of 11.33, the first-half branch head, the complete target build, and the axiom
audit.
