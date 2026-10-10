# PMA Chapter 4 Fidelity Review

Review dates: 2026-10-09–10 local time. Source: `/home/derekblair/sources/pma3.pdf`, printed pp.83–98 (PDF pp.92–107). The inventory contains exactly 34 numbered items. Only brief statements are retained; source proof text is excluded.

## Current verdict

**All 34 inventory entries and formal statement contracts independently reviewed — PASS. Final chapter verification passes.** The reviewer is independent of the inventory author and the three prospective statement authors. Every numbered item and its attached corollaries, examples, and substantive remarks was checked against the source before formalization. Every actual definition and every proposition conjunct was back-translated before proofs began; all three contract files and the shared definitions independently typecheck without errors or warnings.

## Source extraction checks

The complete heading sweep resolves OCR forms `42`, `49`, `411`, `421`, `427`, `4.2` (remark), and `4.9` (monotonic theorem) as 4.2, 4.9, 4.11, 4.21, 4.27, 4.12, and 4.29. The final numbered main-text item is 4.34; exercises are excluded. The source contains ten definitions, eighteen theorems, three worked-example nodes, and three substantive numbered remarks.

Independent rendered statement checks confirm the real-line domain in 4.20, all three pieces and endpoint conventions in 4.27(c), non-strict monotonicity in 4.28, prescribed jumps and one-sided continuity variants in 4.31, and the punctured-limit/arithmetic clauses in 4.33–4.34. The right limit in 4.25 explicitly permits `x=a`; its left definition is stated for interior points. A left limit at `b` is a valid optional generalization and is labeled as such rather than attributed to the source.

The corrected inventory retains the attached uniqueness corollary in 4.2, automatic continuity at isolated domain points in 4.5, closed-preimage corollary in 4.8, coordinate/polynomial/rational/norm examples in 4.11, integer-subspace uniform-continuity example in 4.20, all four discontinuity examples in 4.27, and the exact weighted construction and left/right-continuity variants in 4.31. Every numbered entry was checked, rather than sampled.

## Semantic requirements and source repairs

- Function limits at an ambient accumulation point use punctured domain neighborhoods. The approach point need not belong to the function's domain, and a limit need not equal the value at that point. Continuity uses the value and requires domain membership.
- Definitions 4.25–4.26 retain metric-valued functions on a real interval; real-valuedness is introduced explicitly in 4.28. Simple discontinuities use ordinary one-sided limits, with finite limits in the real specialization.
- The nonempty compact-domain assumption in 4.16 is necessary: an empty compact space contains no point at which an extremum can be attained.
- Definition 4.33 literally asks for `V∩E≠∅` while testing only `t≠x`. For `E={x}`, this permits every target as a vacuous limit and contradicts uniqueness in 4.34. The intended extension of 4.1 requires every approach neighborhood to meet the punctured domain, or equivalently a nontrivial approach filter. Both the inventory author and reviewer independently checked this correction.
- Quotients in 4.3 are restricted to nonzero denominators. In 4.4 and 4.34, a permissible denominator limit yields eventual nonvanishing; a global nonzero-denominator hypothesis would unnecessarily narrow the limit theorem. The everywhere continuity statement in 4.9 does require a nowhere-zero denominator.
- Extended-real operations are partial in the source and totalized in Mathlib. Node 4.34 needs explicit guards excluding opposite infinite summands, zero times infinity, two infinite operands in division, and every zero denominator.
- Relative continuity must agree with `ContinuousWithinAt`/`ContinuousOn` and the metric-subspace comparison in 4.12. Composition in 4.7 requires continuity of the outer function on the range of the inner function, not on an unnecessarily enlarged ambient domain.
- Connected sets include the empty set, consistent with Chapter 2's `IsPreconnected` comparator. Intermediate values in 4.23–4.24 are strict and attained at an interior point.
- The weighted construction in 4.31 must cover empty, finite, and infinite countable sets. An injective family indexed by an arbitrary countable type avoids falsely requiring an injective enumeration of a finite set by all of `ℕ`. Repeated indices would change the prescribed jump to the sum of the repeated weights.

## Fresh bounded prior-art check

A separate chapter author checked live primary GitHub snapshots at 2026-10-10 06:50 UTC (2026-10-09 local date), before formalization. The check used six search queries, eight default-branch HEADs, complete recursive source trees, a ReasBook release branch, and focused source headers/declarations. All inspected trees reported that they were untruncated. This is a bounded landscape record, not a claim of novelty or exhaustive absence; no external project was built or axiom-audited.

| Primary repository snapshot | Observed scope |
|---|---|
| [Neuron-Group/RudinAnalysis](https://github.com/Neuron-Group/RudinAnalysis/tree/a54a65f57ea2bd77922bc7c9b55908e3db241aef) | Inspected complete tree contains numerical-sequence modules through upper/lower limits, with no Chapter 4 continuity module. |
| [sinianluoye/LeanOfRudinAnalysis](https://github.com/sinianluoye/LeanOfRudinAnalysis/tree/a40f25c4a9f2f78e01c52077d7cbe5c05f7b0386) | Inspected complete tree contains Chapter 1/support source, with no Chapter 4 module. |
| [Splines/lean-continuous](https://github.com/Splines/lean-continuous/tree/823a4c93a1d2eadc42ce86e0f1ecbec99f5133a2) | Five Lean files cover real-function continuity, arithmetic, examples, and left/right continuity. |
| [drisspg/lean_ua](https://github.com/drisspg/lean_ua/tree/21d5aff3f597e2610e418b4146ada591abd7ffae) | Live tree contains Chapter 1–2 source only; later folders occur as a planned README layout. |
| [optpku/ReasBook main](https://github.com/optpku/ReasBook/tree/32fe9c0f542ccc499b7011166d26ddf42872b2ca) and [v4.30.0 release](https://github.com/optpku/ReasBook/tree/f9674e6420188b5921fdbff7917aaf0e10cfa8a0) | Main is the catalog/build layer; the release contains substantial Tao/Lebl continuity material. |
| [facebookresearch/atlas-lean](https://github.com/facebookresearch/atlas-lean/tree/3ad834a66cc5d1a4f923326fcb673b14a25e198b) | Complete tree has 12,565 Lean paths, including real-function limits, continuity, IVT, and uniform continuity; no path contains Rudin. |
| [stormj-UH/spivak-lean](https://github.com/stormj-UH/spivak-lean/tree/c24e9fcb7e96873ea9d4769c453be1b3ca48d211) | Chapters 5–8 include limits, continuity, interval extrema/IVT, and uniform-continuity examples. |
| [vltanh/lean4-analysis-tao](https://github.com/vltanh/lean4-analysis-tao/tree/bac39612b3745469e620212947a573eb91154166) | No continuity-named module occurs in the inspected complete tree. |

The inspected ATLAS material supplies real-domain punctured limit and epsilon–delta definitions, comparators, extrema/IVT, and uniform-continuity contracts: [Limits](https://github.com/facebookresearch/atlas-lean/blob/3ad834a66cc5d1a4f923326fcb673b14a25e198b/v1/Atlas/RealAnalysis/code/ContinuousFunctions/Limits.lean), [Continuity](https://github.com/facebookresearch/atlas-lean/blob/3ad834a66cc5d1a4f923326fcb673b14a25e198b/v1/Atlas/RealAnalysis/code/ContinuousFunctions/Continuity.lean), [IVT](https://github.com/facebookresearch/atlas-lean/blob/3ad834a66cc5d1a4f923326fcb673b14a25e198b/v1/Atlas/RealAnalysis/code/ContinuousFunctions/IVT.lean), [UniformContinuity](https://github.com/facebookresearch/atlas-lean/blob/3ad834a66cc5d1a4f923326fcb673b14a25e198b/v1/Atlas/RealAnalysis/code/ContinuousFunctions/UniformContinuity.lean). ReasBook supplies arbitrary metric-space continuity and compactness/extrema/uniform-continuity statements in [Tao Analysis II Chapter 2](https://github.com/optpku/ReasBook/tree/f9674e6420188b5921fdbff7917aaf0e10cfa8a0/ReasBook/Books/Analysis2_Tao_2022/Chap02), and real-function continuity in [Lebl Volume I Chapter 3](https://github.com/optpku/ReasBook/tree/f9674e6420188b5921fdbff7917aaf0e10cfa8a0/ReasBook/Books/IntroductiontoRealAnalysisVolumeI_JiriLebl_2025/Chap03).

These are substantial adjacent continuity formalizations, so describe the present corpus by its Rudin numbering, source fidelity, build results, and axiom audits. The listed public snapshots do not rule out other projects, branches, or differently named sources; their complete correctness and source fidelity were not certified. The user's explicit authorization to complete this corpus remains in force despite existing overlap.

## Formal statement review

Reviewed temporary files: `rudin/Chapter04SharedContracts.lean`, `rudin/Chapter04OpeningContracts.lean` (4.1–4.12), `rudin/Chapter04CompactContracts.lean` (4.13–4.24), and `rudin/Chapter04AdvancedContracts.lean` (4.25–4.34). The reviewer independently typechecked all four without errors or warnings and back-translated every definition and proposition conjunct. They contain actual definitions and proposition contracts, with no axioms or proof placeholders. Every node received an explicit independent PASS before its author began proving it.

| Node | Independent contract verdict and scope |
|---|---|
| 4.1 | PASS — ambient accumulation, exact punctured epsilon–delta predicate, unrestricted approach-point membership, and restricted-filter reference. |
| 4.2 | PASS — every sequence in the punctured domain, actual function composition, and unique limit. |
| 4.3 | PASS — literal pointwise complex operations/constants, explicit quotient domain, real inequalities, Euclidean sum/inner product/scalar multiple. |
| 4.4 | PASS — complex sum/product/quotient limits, denominator-limit guard only, restricted quotient domain, and Euclidean sum/inner product limits. |
| 4.5 | PASS — actual domain value and membership, point/global reference comparators, and isolated-point continuity. |
| 4.6 | PASS — domain and accumulation assumptions, with continuity equivalent to the punctured limit at the function value. |
| 4.7 | PASS — literal composition and outer continuity only on the inner function's range. |
| 4.8 | PASS — literal global continuity equivalent to both open and closed inverse-image characterizations. |
| 4.9 | PASS — complex sum/product continuity and quotient continuity with a nowhere-zero denominator. |
| 4.10 | PASS — every Euclidean coordinate and both vector/inner-product operations. |
| 4.11 | PASS — coordinate and norm 1-Lipschitz clauses, all natural-exponent monomials, arbitrary finite complex multivariate polynomials, rational domain, and composed norm. |
| 4.12 | PASS — both pointwise and global agreement with continuity of the induced metric-subspace map. |
| 4.13 | PASS — strict norm bound for all domain points and bounded-range reference, including empty domains. |
| 4.14 | PASS — arbitrary compact metric domain and continuous metric-valued image. |
| 4.15 | PASS — closed and bounded Euclidean image and literal boundedness. |
| 4.16 | PASS — nonempty compact domain, actual supremum/infimum equalities, and global maximum/minimum inequalities. |
| 4.17 | PASS — continuous actual bijection and continuity of its inverse. |
| 4.18 | PASS — one positive delta for every pair, `UniformContinuous` reference, and continuity consequence. |
| 4.19 | PASS — arbitrary compact metric domain and literal uniform continuity. |
| 4.20 | PASS — all three noncompact real-set counterexamples, boundedness guard on the third, and every metric-valued function on the integer subspace. |
| 4.21 | PASS — literal Euclidean cos/sin parametrization, actual equivalence, inverse discontinuity at the image of zero, noncompact interval, and compact unit circle. |
| 4.22 | PASS — image of every connected subset, including the empty set. |
| 4.23 | PASS — continuous closed-interval restriction, either strict endpoint ordering, and an interior preimage. |
| 4.24 | PASS — exact sin(1/x) function with zero value at zero, full strict intermediate-value property, and discontinuity at zero. |
| 4.25 | PASS — generic metric codomain, exact interval sequence tests, common bilateral limit, and the marked valid left-boundary extension. |
| 4.26 | PASS — disjoint/exhaustive classification restricted to discontinuities, with unequal limits or an equal limit differing from the value. |
| 4.27 | PASS — all four literal functions, complete continuity sets and missing one-sided limits, exact jump limits −2/2, and discontinuity kinds. |
| 4.28 | PASS — non-strict increasing/decreasing interval inequalities and all Mathlib monotonicity references. |
| 4.29 | PASS — both finite one-sided limits as the specified suprema/infima, value inequalities, and cross-point ordering for both directions. |
| 4.30 | PASS — at-most-countability of exactly the interior discontinuity set. |
| 4.31 | PASS — injective arbitrary countable point families, every positive summable weight family, both sided constructions, exact prescribed jumps, and empty/finite/infinite set realization. |
| 4.32 | PASS — literal real traces of rays/intervals and both cofinal neighborhood-basis references. |
| 4.33 | PASS — literal corrected punctured accumulation/limit tests, exact approach filter, nontriviality and Tendsto references, and finite-limit equivalence. |
| 4.34 | PASS — uniqueness under nontrivial approach, precisely defined sum/product/quotient cases, and restricted nonzero-denominator quotient domain. |

The routine `Continuous`/`ContinuousOn` references are matched by the opening batch's literal epsilon–delta/subspace comparators. All one-sided limits use ordinary metric topology; real limits are finite. The partial-arithmetic guards were independently checked for every combination of finite values, zero, and both infinities.

## Final verification

**PASS: 34/34 nodes, zero queued nodes.** Every node has a local commit preceded by a passing default `lake build` and namespace axiom audit. A second independent production reviewer confirms all 80 approved comparisons (79 distinct definitions/contracts) match the final source and all 34 principal theorem signatures prove exactly the reviewed contracts; details are in `pma-ch04-production-review.md`.

The final default build passes with `Chapter04Probes` imported: 18 independently authored boundary probes compile, and the recursive chapter audit checks 275 declarations including private/compiler-generated declarations. The probe namespace contributes 24 declarations within that total. The standalone chapter audit at node 4.34 checked 247 declarations; probe elaboration also introduces four additional parent-namespace equation declarations. Only `propext`, `Classical.choice`, and `Quot.sound` occur. `scripts/check_chapter.py 4` verifies all 34 source markers against the inventory, dependency order, progress counts and empty queue, and rejects proof placeholders/unauthorized axiom declarations.

No node reached the approximately 45-minute resistance cutoff. All commits remain local; nothing was pushed.
