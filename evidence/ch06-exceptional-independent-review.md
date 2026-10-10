# Independent review: PMA 6.10 and its endpoint lemma

Reviewer: `completion_evidence`, independently reviewing the parent's finite-exception proof and the separate endpoint worker's trimming lemma. Date: 2026-10-10. Outcome: **accepted**.

Final reviewed files:

- `rudin/Chapter06EndpointDraft.lean`, 126 lines, SHA256 `b4518141434d43a5d28f97944ba85b9af1c98cff1b19c910bddc2d4a70fe3e4b`.
- `rudin/Chapter06ExceptionalDraft.lean`, 119 lines, SHA256 `f611a715e8c85e43989fa9a196ceb7d93b55b40b9b3674dfd3bb98398fdfabfa`.

## Exact source hypotheses

The final 6.10 contract is the native integrability conclusion for a bounded function with a finite set of **relative** discontinuities on `[a,b]`, with `a≤b` and a nondecreasing integrator. Integrator continuity is required only at those actual discontinuities of the integrand. Good endpoints do not acquire an extra continuity requirement on the integrator.

The endpoint lemma explicitly assumes, separately at each endpoint, continuity of the integrand **or** continuity of the integrator. The source adapter chooses the first disjunct when the integrand is continuous there and invokes the source integrator-continuity hypothesis only in the other case. All endpoint continuity is relative to the closed source interval.

The numbered result also supplies the concrete nonintegrability example using the source left-continuous unit step as both function and integrator. The imported `unitStep_source_caution` separately proves its discontinuity and nonintegrability, so the attached shared-discontinuity caution has an actual counterexample.

## Complete endpoint proof review

`endpoint_local_gap_lt` has two valid estimates. If the integrand is continuous, its local oscillation is small and the cell's raw integrator mass is bounded by the whole interval's mass. If the integrator is continuous, boundedness controls the integrand oscillation while the difference of the two nearby integrator values is small. The positive denominators include `+1`, avoiding divisions by a zero global mass or a zero function bound.

`rsIntegrable_of_continuousOn_Ioo` trims two short endpoint tails, each with gap below `ε/3`, and chooses a compact middle interval strictly inside the open interval of integrand continuity. The middle has an integrable native continuous integrand and therefore a partition with gap below `ε/3`. Exact native concatenation gives a full-interval partition with total gap below `ε`. This proves the actual Darboux criterion without changing values at endpoints or representing the integrator by a measure.

## Complete finite-exception proof review

The induction splits at a selected exceptional point only when that point lies strictly inside the current interval. Integrator continuity at that point supplies the new endpoint disjunct for both pieces. All other exception and continuity hypotheses restrict to the pieces, and the proved native append theorem combines their integrability. An exceptional point outside the open current interval is removed without changing the interval or adding hypotheses.

The source adapter forms exactly the finite set of relative discontinuities. At interior points it correctly converts within-interval continuity to ambient continuity using an interval neighborhood. At the original endpoints it keeps the relative hypotheses and chooses the required disjunction. The degenerate interval branch invokes a proved native singleton-integrability theorem.

The two general induction helpers take a base theorem as an explicit parameter. Crucially, the completed `pma6_10` discharges that parameter with the actual proved `rsIntegrable_of_continuousOn_Ioo`; it does not leave the desired result or an equivalent integrability statement as an assumption.

## Finding resolved and independent checks

An earlier draft failed compilation only in the final step-counterexample wrapper: simplification did not unfold the unapplied higher-order step function. The author replaced that wrapper with the direct definitionally matching theorem. The reviewer did not edit proof source. The final hash above was freshly recompiled and accepted.

The endpoint draft compiled independently with exit zero and no warnings or errors. The final exceptional draft was independently compiled from its exact source with three appended axiom-print commands; it also completed with exit zero and no warnings or errors. All five endpoint/exception theorem checks use only `propext`, `Classical.choice`, and `Quot.sound`. Both hashes were rechecked after compilation. A lexical scan found no placeholders, custom axioms, unsafe or opaque declarations, or `native_decide`.

No remaining source-fidelity, endpoint, extra-hypothesis, circularity, or proof-validity findings remain. Production integration and chapter-wide validation remain the parent's responsibility.
