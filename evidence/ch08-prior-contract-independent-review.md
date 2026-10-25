# Chapter 8 independent contract and source review

Reviewer: `ch8_fidelity`, 2026-10-22. Production proof authors: `root` (PowerSeries), `power_series_api` (Abel and Exponential), and `double_series` (DoubleSeries, Taylor and Operations). The reviewer authored no production proofs. Independent source scope is `research/pma-ch08-source-review.md`, based on direct visual reading of the local third-edition source. Separate independently authored boundary clients are in `Chapter08Probes.lean` and `Chapter08/ExponentialProbes.lean`.

**Typed-contract semantic verdict: ACCEPTED for numbered nodes 8.1-8.6 and the requested unnumbered addition/multiplication/integration supplements.** Kernel compilation, recursive permitted-axiom checks and exact production inclusion are separate gates owned by the integrating lane. No build was run by this reviewer. The source hashes below identify the reviewed snapshot; compilation-driven changes require a final delta check before this acceptance is attached to final production bytes.

| File in `rudin/Rudin/PMA/Chapter08/` | SHA256 at this review |
|---|---|
| PowerSeries.lean | `af7669152ab11b348b454ccfacb37928c67be845b7428377bd29dfd6e6552518` |
| Abel.lean | `2a7a23da0c64df9c38dff6975bd0f5e34f1a428a5d4fa86480c35b7498260239` |
| DoubleSeries.lean | `7cb78d7c111d3be2a9bc0f5e67a02c0020e988ba39e24f67db050787aae57e7e` |
| Taylor.lean | `9c666fab54b9e7a3a7b7ac073e5b9ca9a8a7d2d31e2ccb7a7be303af472c0347` |
| Operations.lean | `2b4ce0759198e1a2c854a8398d7b285c5edd64de0d36fd19aa3ba824245ae07a` |
| Exponential.lean | `cd7d31f6d45786bc4433d3c0bb878c1e4e0c2da6f43bf48fc1491c6167768bcd` |

## 8.1: representation, local uniform convergence and all derivatives

`Represents c f R` says every real argument with extended norm below `R` has the ordinary ordered power-series sum `f x`. Its coefficients and values are complex, and `R` may be infinite. No absolute-convergence premise is silently added. `realSeries_term_reference` connects the real scalar multiplication convention to Chapter 3's complex coefficient-left convention.

The contract yields uniform convergence on every nonnegative-radius closed centered subinterval, continuity throughout the open extended ball, existence of every successive real-parameter derivative, ordered-series formulas for all derivative orders, every factorial coefficient identity at zero, and coefficient uniqueness. The reindexing `n -> n+k` changes Rudin's falling factorial into `(n+1).ascFactorial k` correctly. Order zero and the constant coefficient are retained. The source's smaller intervals with reversed endpoints are empty and need no additional restriction; all nonempty intervals are represented. The source's all-orders corollary is not reduced to just first differentiability.

The final existential smooth/nonanalytic witness captures the attached warning that smoothness does not guarantee a local power-series expansion. The particular exercise construction is outside the node inventory. Equality of exact convergence radii of derivative series appears inside the source proof; it is not an additional numbered theorem/corollary obligation. The representation-to-analytic bridge first derives a radius bound from ordinary convergence, so it does not assume its own conclusion.

## 8.2: Abel, including conditional endpoints

Both the unit endpoint and every positive scaled endpoint retain `Chapter03.SeriesHasSum`, so conditional convergence is allowed. Interior `HasSum` is explicitly concluded before `tsum` is used as the represented value. The limit approaches from the left. The endpoint extension takes the supplied ordered sum at the endpoint, rather than Mathlib's unconditional `tsum`, and is continuous relative to the closed left half-line there. This local formulation is equivalent to the source's left approach through the convergence interval. The strengthened final contract also explicitly covers every negative endpoint, with approach from the right and continuity relative to the right half-line, by a proved coefficient reflection. No endpoint equality to an unconditional sum is asserted.

The attached Cauchy-product application uses the existing exact conditional `Chapter03.pma3_51_contract`, with no absolute-convergence assumption. It supplies the requested source application without inventing a new numbered node.

## 8.3: absolute double-series interchange

The detailed review is `ch08-double-series-independent-review.md`. The later addition of `set_option autoImplicit false` changes no mathematical declaration. Rows have specified ordinary sums of norms, the series of these norm sums converges ordinarily, and the conclusion supplies every complex row and column sum plus a common outer sum. The internal natural indices explicitly reindex the source's positive indices. No equality of possibly divergent totalized sums substitutes for existence.

## 8.4 and 8.5: recentering and identity

The Taylor contract represents the series at every interior real center with coefficients `iteratedDeriv n f a / n!`, throughout the guaranteed radius `R - |a|`. The radius is a lower guarantee, not an exact-radius claim. Infinite original radius is included, and the conclusion is an actual ordered sum, not a totalized equality.

The identity contract permits an accumulation point anywhere inside the interval. Removing the point before taking closure prevents a singleton equality from satisfying the premise. Taking closure of the global equality set is equivalent here to closure of its interval restriction because the accumulation point is interior. Both equality of every coefficient and equality of the represented functions on the complete interval are concluded. The proof applies analyticity on the preconnected ball, then the already reviewed coefficient uniqueness result.

## Requested operations supplement

`represents_add` and `represents_mul` give pointwise addition and multiplication with the correct original coefficients and Chapter 3 Cauchy convolution. Multiplication establishes interior absolute convergence before applying a valid Cauchy-product theorem.

The integration supplement retains the native Chapter 6 complex Riemann-Stieltjes predicates and integral. Its integrator is only required to be nondecreasing on the interval, not continuous. It obtains both integrability of the sum and convergence of the series of integrals. The ordinary specialization uses the identity integrator. The explicit monomial integral produces coefficient `(b^(n+1)-a^(n+1))/(n+1)` and includes `a=b`. These are unnumbered requested supplements, not fabricated Rudin nodes.

## 8.6: exponential, logarithm and real powers

The contract establishes the complex factorial-series identity, complex addition/zero/nonvanishing/reciprocal/derivative/finite-sum identities, and the real-to-complex restriction. All six numbered real-exponential clauses are included: regularity and derivative, positivity/strict increase, addition, both infinite-end limits, and decay of every natural power times the negative exponential. The Chapter 3 Euler number is explicitly identified with `exp 1`; real powers and the rational supremum convention connect to this same base.

Logarithm retains both inverse identities, its positive domain, normalization, strict increase, derivative, product formula and both boundary limits. Its integral statement has an explicit native Chapter 6 orientation convention, covering arguments below 1 as well as above 1; integrability is proved on each positive ordered compact interval.

Positive-base real powers are identified with `exp(alpha*log x)`, with integer and rational compatibility and the rational supremum convention for bases greater than 1. Their derivative, ordinary power integral, separate exceptional exponent `-1` logarithmic integral, and `x^(-alpha)*log x -> 0` for positive `alpha` are included. No zero/negative-base logarithmic extension is silently imposed as source scope.

## Scope and production limits

This accepts the intended first two topic sections. Rudin's true numbering has power series at 8.1-8.5 and exponential/logarithmic development at 8.6. There are 22 numbered Chapter 8 nodes in total. The task brief's ranges are inaccurate: 8.7 begins trigonometry, 8.8 is algebraic completeness, and 8.17 starts gamma. The review does not accept 8.7-8.22 as implemented, nor claim completion of the full chapter.


## Compilation-delta review: PowerSeries and Taylor

**ACCEPTED** after reading both complete current files. PowerSeries changed from
`3546884571cafbfe2b3bc2c26dc9e0b4902e9c95b134851d3dfacec5be7c1eac`
to `af7669152ab11b348b454ccfacb37928c67be845b7428377bd29dfd6e6552518`.
Taylor changed from
`7e0c16c5a9708cdac62d7dd538d54275a36435d2ce6a861efe277ecab2714e02`
to `1eb553c7b9c34d0792734f960c1a9acc5c8eb15f94a7f049458a565987a541fa`.
The latest reviewed hashes replace the corresponding table entries above.

The represented-series definition, derivative coefficient definitions, all
numbered contracts, domains and quantifiers are unchanged. PowerSeries now
makes the extended-norm/nonnegative-norm conversion explicit, supplies local
`HasSum`/`SeriesHasSum` annotations when identifying ordered limits, and splits
conversion/extensionality proof goals explicitly. Taylor similarly states the
ordinary-series type explicitly before simplifying its iterated derivative
formula. These changes alter proof elaboration, not the mathematical statement,
and introduce no extra premise or evaluation shortcut. The entire ordinary
convergence-to-analytic bridge and all derivative orders remain intact.

The reviewer read `evidence/ch08-power-series-compile-5.log`, which records a
successful module build for PowerSeries. This corroborates the integrating
lane's kernel-build report; this reviewer did not run a build. Taylor compilation,
final default inclusion, independent clients and the recursive axiom audit remain
separate pending gates at the time of this delta review.


## Compilation-delta review: Abel

**ACCEPTED** after reading the complete current Abel source. The updated hash is
`0d62e22630716fc1e93bf07b1f795be62d3768e1342ac0eef55cd502b64fa480`.
The definitions and `pma8_2_contract` are unchanged. The scaled-limit proof now
states the division map's continuity and target limit explicitly; the endpoint
proof separately establishes the extension's value at the endpoint and uses the
strict-inequality membership to exclude the equality branch nearby. The direct
`#print axioms` diagnostic was removed in favor of the separate chapter audit.
The ordinary endpoint premise, explicit interior sums, left limit, endpoint
continuity and conditional Cauchy-product consequence all remain intact. No
extra premise, contract weakening, or proof shortcut was introduced.


## Compilation-delta review: scoped norms, native integrals and exponential APIs

**ACCEPTED** after reading the complete current Taylor, Operations and Exponential
files. The latest reviewed snapshot hashes are:

- Taylor: `832384e9e2766a3543f7cd34421fa76fac0409e432cad647e0f218c7a5ee9304`.
- Operations: `2b4ce0759198e1a2c854a8398d7b285c5edd64de0d36fd19aa3ba824245ae07a`.
- Exponential: `cd7d31f6d45786bc4433d3c0bb878c1e4e0c2da6f43bf48fc1491c6167768bcd`.

All numbered contracts, represented-series/native-integral definitions and public
supplement theorem signatures are unchanged. Taylor and Operations explicitly
open the nonnegative/extended-real notation scopes and convert extended norm to
coerced nonnegative norm at ball-membership proof steps. The Taylor proof retains
an arbitrary interior center and the full radius bound. The monomial integral
proof now separates the real derivative calculation from multiplication by a
complex coefficient; its native FTC and degenerate-interval branches are intact.
Exponential fixes the monotone-set API application, unfolds conditional branches
with the pinned lemma names, proves the nonzero denominator explicitly, uses the
correct logarithmic-growth theorem namespace, and invokes the direct `1 < exp`
reference. No statement or domain is weakened and no additional assumption is
introduced. Compile status for these three files remained pending at this review;
no reviewer build was run.

PowerSeries remains accepted at
`af7669152ab11b348b454ccfacb37928c67be845b7428377bd29dfd6e6552518`,
Abel at `0d62e22630716fc1e93bf07b1f795be62d3768e1342ac0eef55cd502b64fa480`,
and DoubleSeries at
`7cb78d7c111d3be2a9bc0f5e67a02c0020e988ba39e24f67db050787aae57e7e`.

### Independent-client authorship check

The reviewer re-read their own independently authored nine opening boundary
clients at `Chapter08Probes.lean` hash
`4181b3e88474113e17482d8bda0f875d1e9cd2479696d99124b915fa1d58ec9d`.
Required `ENNReal`, `NNReal`, `BigOperators` and topology notation openings are
present. The five separate exponential clients are at
`Chapter08/ExponentialProbes.lean` hash
`ecb9347e8fdbfc9f29fbf94c9a82a3eecc6c530f397530585cc9d14eb4b2eb7e`;
that file does not use nonnegative/extended-real notation. Both probe files now
set `autoImplicit false`. These are authorship/intent checks, not an independent
review of the reviewer's own probe implementation; kernel compilation is still
required and owned by the integrating lane. None of the probe assertions was
weakened or replaced by a contract restatement.


## Final Taylor elaboration delta

**ACCEPTED** after reading the complete current Taylor source at
`9c666fab54b9e7a3a7b7ac073e5b9ca9a8a7d2d31e2ccb7a7be303af472c0347`.
The only further proof changes add multiplication associativity to the Taylor
coefficient simplification and omit the explicit point argument to `EqOn`, whose
point is inferred from membership in the pinned API. The 8.4 and 8.5 contracts and
all hypotheses remain unchanged. No theorem premise or conclusion was altered.

The reviewer also read `ch08-operations-compile-2.log` and
`ch08-exponential-compile-2.log`; both record successful module builds at their
latest accepted source. These logs corroborate the integrating lane's reports.
Final default inclusion, probes and recursive axiom audit remain separate gates.
No reviewer build was run.

### Probe elaboration and linter cleanup

The probe author's fixes preserve every client assertion. The conditional Abel
client now changes its target explicitly to the finite-range-sum `Tendsto` before
simplifying the real-to-complex map, avoiding an underapplied `PartialSums` target.
The updated opening client hash is
`37c3355eff1415f6b8072b04dac13e4ce48ad6e53fce4bd53b74f40d7bb7889d`.
The separate exponential clients received only two linter cleanups, with updated
hash `50cfdadd939ba80e57fd93e47bad71d05cc49eb97664485e428ee8cc2b6cc9da`.
These fixes await the integrating lane's compiler rerun. The reviewer read the
prior opening-client log: it records a successful Taylor build and only the
reported coercion elaboration error in the clients; no statement defect was
found. No build was run by this reviewer.


## Explicit negative-endpoint contract extension

**ACCEPTED** after reading the complete extended Abel source, SHA256
`2a7a23da0c64df9c38dff6975bd0f5e34f1a428a5d4fa86480c35b7498260239`.
The previous three conjuncts are preserved, and a fourth now explicitly covers
convergence at the negative endpoint `-R` for every `R > 0`: interior `HasSum`,
a limit through `nhdsWithin (Ioi (-R))`, and continuity of the endpoint-patched
sum relative to `Ici (-R)`. The coefficient premise remains an ordinary ordered
sum at that negative endpoint, so conditional convergence is retained. This
strictly strengthens the accepted contract and makes the attached source claim
about either endpoint mechanically explicit.

The reflection identity changes coefficients to `a_n*(-1)^n` and arguments to
`-x`, preserving each original term. The proof then transports the already
proved right-endpoint result across the continuous sign-reversal map, which
reverses the approach direction. No absolute-convergence or two-sided endpoint
hypothesis is added. The existing conditional-Abel boundary client projects the
unchanged first conjunct, so no projection edit was required. Compilation of
this extension remains pending at the time of review; no reviewer build was run.

### Additional independent integration clients

At the integrating lane's request, the reviewer added two further authored
clients to `Chapter08Probes.lean` and imported Operations. The first computes
the native integral of `x*I` over `[0,1]` as `I/2` and proves it is nonzero. The
second uses the termwise coefficient formula on a singleton and uniqueness of
ordered zero-series sums to derive native integrability and zero integral for
an arbitrary represented function. The file now has 11 theorem clients, with
hash `093390f7774efef783fc3e1d5d5e66d79ff5b0c42225a59f99db8d27a57d543c`.
These additions await compiler verification by the integrating lane.

## Final client build evidence inspected

The reviewer read `evidence/ch08-foundation-probes-final.log`, which records a
successful build including the extended signed Abel theorem and all 11 opening
boundary clients, and `evidence/ch08-exponentialprobes-final.log`, which records
a successful build of all five separate exponential clients. Current source
hashes remain exactly the accepted signed Abel hash
`2a7a23da0c64df9c38dff6975bd0f5e34f1a428a5d4fa86480c35b7498260239`,
opening client hash
`093390f7774efef783fc3e1d5d5e66d79ff5b0c42225a59f99db8d27a57d543c`,
and exponential client hash
`50cfdadd939ba80e57fd93e47bad71d05cc49eb97664485e428ee8cc2b6cc9da`.
All 16 authored boundary clients have therefore compiled in the integrating
lane. Default production build, final principal coverage and recursive axiom
audits remain distinct integration gates. No reviewer build was run and no
further source mutation was made during this final evidence inspection.
