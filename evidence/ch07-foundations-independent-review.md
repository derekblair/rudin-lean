# Independent final review: PMA 7.1 and 7.7–7.9

Verdict: **ACCEPT** for the frozen canonical bytes below. Reviewer: `ch6_production`, independent of these modules' author. The complete Basic (56 lines) and Foundations (184 lines) sources were read against the accepted inventory and reviewed contracts; neither source was edited.

- `Rudin/PMA/Chapter07/Basic.lean`: SHA256 `b6b8b58999ad0025fd3ab28bc0ba3a4df5a07cc395158b99a14c05055bfa2b1a`.
- `Rudin/PMA/Chapter07/Foundations.lean`: SHA256 `941938d68a48db2a4e0ab70ba0b39d51828fc91602a4583ab449f8ad1c4d5742`.

## Fidelity and proof assessment

7.1 gives actual pointwise limits, the epsilon characterization, existence of a single limit function assembled from the individual limits, and ordered Chapter 3 partial-sum semantics for function series. The codomain is complex. Selection outside the stated domain is harmless: the function is set to zero there and no convergence outside the domain is claimed.

7.7 preserves a single eventual index for all domain points, includes pointwise convergence, and retains ordered series semantics. The equivalence of strict library estimates and non-strict source estimates is proved using half-epsilon in the necessary direction. 7.8 includes existence of the uniform limit and requires target completeness; its general normed-group statement specializes to complex numbers. The proof obtains pointwise limits from genuine Cauchy sequences, then uses the uniform Cauchy property to obtain uniform convergence. No additional boundedness or domain nonemptiness is assumed.

7.9 uses an extended nonnegative supremum, so an unbounded finite prefix is permitted. The helper proves uniform convergence equivalent to error convergence even without the source's pointwise premise, a valid stronger result; the numbered contract retains that premise. The real-supremum comparator has explicit boundedness and treats the empty domain separately. Its finite and nonnegative arguments justify conversion through `toReal`. No boundedness of every sequence member is added, and no totalized real supremum is used to conceal infinite error.

The remaining shared Basic definitions preserve the stated zero/successor indexing, native spike formulas, and sequential bounded-continuous-function closure semantics. No custom axiom, circular premise, weakened domain, or completion placeholder was found.

## Independent kernel and boundary checks

Each canonical source was freshly compiled directly with the pinned local Lean toolchain: both exited zero and generated no warnings or diagnostics. Logs: `ch07-independent-source-basic.log` and `ch07-independent-source-foundations.log`.

Fresh external client `rudin/Chapter07FoundationsReviewProbe.lean` compiles with exit zero and no warnings. Its ten authored theorem probes cover:

- Existence of a uniform limit on the empty domain, zero extended error there, and the bounded real-supremum comparator there.
- The concrete real sequence F(0,x)=x, F(n,x)=0 for n>0 on the entire real line: its initial error is infinity, yet it converges uniformly and its extended errors tend to zero via the numbered 7.9 theorem.
- Target completeness necessity on the nonempty one-point domain: without assuming completeness, the existence direction of the uniform Cauchy criterion implies `CompleteSpace V`. Consequently the criterion fails for any incomplete normed-group target.
- An explicitly complex constant sequence and the exact range-N ordered finite-sum definition.

`evidence/ch07-foundations-independent-client.log` records recursive axiom audits for all 26 imported Chapter 7 declarations and all 13 client declarations (including generated declarations). Only `propext`, `Classical.choice`, and `Quot.sound` occur. All four principal numbered declarations also passed individual axiom checks. The canonical sources contain none of `sorry`, `admit`, custom `axiom`, `unsafe`, `implemented_by`, or `extern`.

Initial client attempts exposed unresolved universe annotations for projections of the multi-universe 7.9 conjunction and a local real-norm normalization issue. Explicit client universe arguments and local arithmetic rewriting fixed those errors. These were client-only corrections; the accepted canonical sources were not changed. Final hashes were rechecked unchanged.

This verdict covers these four nodes and shared definitions; it is not a complete Chapter 7 or production-integration claim. No production writes, pushes, dependency changes, or book copies were performed.
