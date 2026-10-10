# Chapter 6 jump-integrator statement preparation

## Source inspection

Independently inspected local PDF pages 138-141 (printed 129-132), using rendered page images. Only brief statement paraphrases and formalization choices are recorded here; no source proof text or book pages are retained in this workspace.

- **6.14:** The unit step is zero at all nonpositive arguments, including zero, and one at positive arguments. It is monotone. The exact value at zero must be retained.
- **6.15:** A bounded real function on the closed interval, continuous at a strictly interior point `s`, integrates against the translated unit step to its value at `s`. No global continuity of the integrand is assumed.
- **6.16:** The displayed hypothesis is **nonnegative**, `c_n >= 0`, not strictly positive. The weights form a convergent series; the atom locations are a sequence of distinct points strictly inside the interval; the integrand is continuous on the closed interval. The integral against the sum of these translated weighted steps equals the sum of weighted point values. The integrator series converges at every real input, is monotone, vanishes at the left endpoint, and equals the total weight at the right endpoint.
- **6.18:** The quadratic moment on the unit interval is expressed by the Stieltjes integral of `x^2`. For a mass function with continuous density, this equals the ordinary integral of `x^2` times that density. For finitely or countably many atoms, it is the corresponding weighted sum of squared locations. The general Stieltjes formulation also accommodates a continuous mass function without assuming it differentiable everywhere.

## Endpoint convention

The translated step in 6.14-6.16 is left-continuous: its value at the atom remains zero. The strict-interior hypotheses in 6.15 and 6.16 avoid boundary ambiguity. In particular, a step at the upper endpoint is zero throughout the integration interval and cannot account for a positive mass placed at that endpoint.

The physical language in 6.18 describes cumulative mass on the closed initial segment. That convention would count an upper-endpoint atom, using a right-continuous cumulative step instead. Consequently a direct 6.16 corollary will explicitly retain interior atoms. Any endpoint-inclusive 6.18 formulation must use an appropriate cumulative-mass convention, or explicitly account for the boundary term; it must not silently reuse the left-continuous step with an upper-endpoint atom. This choice has been reported to root before contract finalization.

## Dependencies and proposed API

The source uses native Riemann-Stieltjes integration. Contracts must use the chapter's Darboux-based predicate once root publishes its API, not assume equivalence to an unrelated measure integral. Chapter 4 already provides `JumpSumLeft` and `JumpSumRight`, pointwise summability and monotonicity under nonnegative summable weights, so the present source does not require strengthening weights to strict positivity.

Root published the native API in `Rudin/PMA/Chapter06/Basic.lean`: `RSIntegrable f alpha a b` includes boundedness, monotonicity of the integrator, and equality of its lower and upper Darboux integrals; `RSIntegral` is the lower integral, meaningful as an integral under that predicate. The proposed contracts now use those definitions directly.

Root approved the typed 6.14 contract. Its proof compiles and its recursive axiom print lists only `propext`, `Classical.choice`, and `Quot.sound`.

The native 6.15, 6.16, and 6.18 contracts also typecheck and have been submitted for root review before proofs. The 6.16 formal sequence starts at natural index zero, an innocuous reindexing of the source's index-one sequence. The quadratic-moment contract uses a general nondecreasing mass function without a differentiability premise in its first clause, then separately records the density and finite/infinite interior-atom specializations. The density clause permits the Riemann-integrable derivative of 6.17, which includes the source remark's continuous-density case. No terminal endpoint atom is silently included in the left-continuous atomic formula.

Root subsequently approved all three native contracts unchanged. Native `RSIntegrable` now also includes the interval-order guard `a <= b`, as required by independent review of the framework.

## Proof progress

6.15 is fully proved using the native definitions. For any partition, a nonzero step weight forces its closed cell to contain the atom; telescoping weights then bounds the point value between the lower and upper sums. A four-point partition with two nearby points around the relevant one-sided jump makes both sums arbitrarily close to that value. No continuity away from the atom, strict partition increments, or assumed criterion theorem is used. Its axiom audit contains only the three permitted standard axioms.

The series helpers for 6.16 prove pointwise summability, monotonicity, endpoint values, summability of weighted samples, and exchange of the finite cell sum with the absolutely convergent atomic series. Every partition therefore bounds the weighted sample series between its lower and upper sums. Native 6.8 continuous integrability, now imported from `Rudin.PMA.Chapter06.Integrability`, gives equality of the integral with that series. **PMA-6.16 is fully proved**, including all reviewed convergence and endpoint conjuncts.

As an additional source-fidelity probe for the caution following 6.10, `unitStep_source_caution` proves that the source step is discontinuous relative to `[-1,1]` at zero and is not integrable with respect to itself there. The general proof shows that every partition has lower sum zero and upper sum one, exposing the genuine obstruction from a shared jump. These are native Darboux claims rather than measure-integral claims.

The general monotone-mass quadratic integral exists, and both the finite and infinite atomic quadratic moments are proved. **PMA-6.18 is now fully proved** in the separately authorized `rudin/Chapter06MomentDraft.lean`, which imports the compiled Jump and Calculus modules. This keeps the dependency order acyclic as the calculus development grows. The contract in Jump is unchanged. The density proof specializes the independently reviewed full 6.17 theorem to the bounded quadratic function on `[0,1]`; it concludes both ordinary integrability of the density-weighted function and equality with the native Stieltjes integral. No continuity assumption is added to the density. The first conjunct remains valid for every nondecreasing mass function, including continuous mass functions that are not differentiable everywhere. Both atomic clauses retain interior support, as approved.

Standalone validation: `./lake-local env lean Chapter06JumpDraft.lean` and `./lake-local env lean Chapter06MomentDraft.lean`, both exit 0, no warnings or errors. Principal theorem and moment/caution helper axiom reports, including `pma6_18` and `quadraticMoment_density`, contain only `propext`, `Classical.choice`, and `Quot.sound`. Whole-source scans found no proof placeholders, `native_decide`, or new axiom declarations. Changes remain isolated to the authorized drafts and evidence files.
