# Chapter 6 native Darboux definitions: independent review

Reviewed `rudin/Rudin/PMA/Chapter06/Basic.lean`, lines 1–63, directly against the independently established source conventions. Final reviewed SHA256: `729f146c950e4cdd3c804bdc23725ef98f516864c380cc5fe526a064018eac10`.

**Verdict: ACCEPTED for source representation and subsequent proof work.** This is a definition review, not acceptance of unproved Chapter 6 theorem nodes. Root reported the original definitions typechecked and is rebuilding after the one guard correction below; this reviewer did not independently run the compiler for this file.

## Semantic checks

- `Partition` (lines 12–17) is a finite weakly increasing endpoint chain. It preserves the printed nonstrict partition convention. Repeated points are allowed. The `n=0` extension forces equal endpoints and has no cells; it does not introduce a nonzero degenerate integral. Any partition's monotonicity and endpoint equations imply `a ≤ b`.
- `BoundedOn` (lines 19–20) is the usual uniform absolute bound on the closed interval. A separate nonnegative-bound premise is unnecessary on a nonempty interval: the existing inequality forces the bound nonnegative. The accepted ordered-interval guard ensures nonemptiness when used in integrability.
- Cells are closed intervals between consecutive points (lines 22–23), including singleton cells. Monotonicity makes every cell nonempty and contained in the whole interval. `cellLower` and `cellUpper` (lines 28–32) use real infimum/supremum of the actual image of each cell; under boundedness these have the intended finite extrema semantics, without asserting that extrema are attained.
- Integrator weights and sums (lines 25–38) use exactly successive integrator increments. `MonotoneOn α (Icc a b)` supplies nonnegative weights. A repeated endpoint pair contributes zero even for a discontinuous integrator. No right continuity, continuity, strict positivity of weights, or mesh restriction is imposed.
- The lower and upper integrals (lines 40–44) are the supremum of lower sums and infimum of upper sums over all such partitions. They are deliberately totalized real operations; bounds and nonempty-partition lemmas remain proof obligations before applying real conditional-completeness APIs.
- `RSIntegrable` (lines 46–48), after correction, includes ordered endpoints, boundedness of the integrand, monotonicity of the integrator, and equality of the two Darboux integrals. `RSIntegral` is the lower integral and is interpreted as the source integral under this predicate. Identity-integrator abbreviations preserve the ordinary Riemann specialization (lines 53–54).
- Tags (lines 56–61) lie in closed cells. The tagged sum has the intended same-cell weight. This permits endpoint tags and repeated partition points.

## Guard correction made by root

The first version omitted `a ≤ b` from `RSIntegrable`. For reversed endpoints the interval and partition type are empty; boundedness and monotonicity are vacuous, and the real empty supremum/infimum both totalize to zero. Thus the old predicate incorrectly classified every function and integrator as integrable on a reversed interval. The actual revised line 47 now includes `a ≤ b`. This resolves the issue while retaining ordered degenerate intervals, whose sums and integral are zero.

## Refinement contract precheck

The refinement author's proposed contracts were reviewed before proof work: `Q.Refines P` means `range P.point ⊆ range Q.point`; a common refinement has exactly the union of the two point sets; equal point ranges imply equality of lower and upper sums under the source boundedness and monotonicity hypotheses; refinement increases lower sums and decreases upper sums. These are semantically faithful, including repeated points and equal endpoints. File-level acceptance will require reading the actual typed contracts; no completed refinement theorem is certified here.

## Downstream obligations

Prove nonempty partitions for ordered endpoints, nonempty bounded cell images, bounded sets of sums, zero integral at equal endpoints, and refinement invariance before using the totalized extrema as source integrals. Keep derivative clauses on nondegenerate intervals so finite one-sided endpoint derivatives are meaningful. These obligations are consequences of the accepted definitions, not requests to strengthen source hypotheses.

## Calculus contract review over these definitions

The actual five contract definitions in `rudin/Chapter06CalculusDraft.lean`, lines 18–73, were read independently after the author requested pre-proof review. **Verdict: all five contracts ACCEPTED** after the two scope corrections below. The reviewed file prefix, lines 1–74 before its native FTC proof heading, has SHA256 `1f6bb9ebdbe8e378ae0ff7a35c99f71c99769cbb481f98fae0f682ef47e90b04`.

- `pma6_17_contract`: retains the full integrability equivalence for merely bounded f, assuming only ordinary Riemann integrability of the integrator's derivative. It imposes no derivative continuity or ordinary Riemann integrability of f. Its derivative is explicitly relative to the original nondegenerate closed interval, including endpoints.
- `pma6_19_contract`: the main transport is continuous, strictly increasing, and onto, with no derivative premise. On review its first conjunct was widened from strict to ordered endpoints so singleton transport is retained. The ordinary weighted substitution consequence uses a nondegenerate interval and a derivative that is Riemann integrable, with no extra continuity, nonvanishing, or inverse-differentiability hypothesis.
- `pma6_20_contract`: gives closed-interval continuity, explicit uniform continuity added during review, and the relative derivative at every relative continuity point of f, including the two endpoints. Its integrand need only be Riemann integrable. The nondegenerate interval premise prevents vacuous singleton derivative semantics.
- `pma6_21_contract`: requires the closed-interval derivative of F to be the Riemann-integrable f, and states the endpoint-difference identity without requiring continuity of f.
- `pma6_22_contract`: both derivative hypotheses use the original closed interval; only Riemann integrability of the two derivatives is required. Both products' integrability and the integration-by-parts identity are explicit conclusions.

An initial local compiler check caught an in-progress FTC rewrite mismatch between `id` and `(fun x => x)` and was reported to the author. The author corrected it without changing the accepted contract prefix. A fresh independent `./lake-local env lean Chapter06CalculusDraft.lean` run then exited **0**, with `pma6_21` recursively depending exactly on `[propext, Classical.choice, Quot.sound]` and no warnings. The checked 135-line file SHA256 is `92c1c6f705feb1b2737ef578131dacb3623d27597f11faef7f5650e409d9b218`.

The actual 6.21 proof at lines 77–131 was also read. On positive-width cells it obtains the mean-value slope from the interval derivative, bounds that value between the cell infimum and supremum, then multiplies by the nonnegative width. Repeated-point cells are handled explicitly by zero increments. Summing telescopes to the primitive's endpoint difference, and the native lower/upper Darboux integrals squeeze that difference using the integrability equality. No replacement integral semantics or unproved integral criterion is assumed. **Verdict: the reviewed 6.21 proof is ACCEPTED.** The other four accepted contract definitions had no completed proof in this snapshot and are not certified complete here.
