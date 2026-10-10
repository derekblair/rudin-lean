# Chapter 7 equicontinuity and selection contracts

Status: the exact six typed contracts were independently accepted by oscillation in `ch07-equicontinuity-contract-independent-review.md`, and root independently read and accepted the entire draft at SHA-256 `4f3b28d22bfe251c3cac596b7a24d88390bbefcc5f98ade7b67492cdad322f74`. Root then explicitly authorized proof implementation in `rudin/Rudin/PMA/Chapter07/Equicontinuity.lean`. Owned nodes: PMA-7.19 and PMA-7.21–7.25. The accepted scope is `research/pma-ch07-inventory.md`, corroborated by `evidence/ch07-source-independent-review.md`.

Validation: `./lake-local env lean Chapter07EquicontinuityDraft.lean` passed with exit 0. The file contains definitions only, with no theorem, lemma, axiom, proof placeholder, or `native_decide`. Reviewed-ready draft SHA-256: `4f3b28d22bfe251c3cac596b7a24d88390bbefcc5f98ade7b67492cdad322f74`.

## Interfaces and conventions

- `PointwiseBoundedOn F E` puts its finite real bound after the point quantifier and before the family-index quantifier. `UniformlyBoundedOn F E` uses one finite real bound for all indices and points. `IndividuallyBoundedOn F E` puts a possibly different bound after each family index. All three work for normed additive codomains, explicitly including complex and real values.
- `SourceEquicontinuousOn F E` is the source's uniform condition: one positive delta for all pairs of points in E and all family members. The 7.22 contract explicitly includes equivalence to Mathlib `UniformEquicontinuousOn`, not to pointwise `EquicontinuousOn`, and uniform continuity of every member.
- Abstract sequences use natural-number indices. In the two concrete examples, formal index n means source index n+1, so peak locations and denominators never use a zero source index. Every subsequence is indexed by a `StrictMono` map from natural numbers to natural numbers.
- Empty and finite countable sets, empty compact sets, and singleton compact sets remain admitted. The 7.19/7.23 domain has no topological or metric assumption.
- Shared-foundation coordination with `remaining_scope`: the planned definitions are `PointwiseConvergesOn F f E := ∀ x ∈ E, Tendsto (fun n => F n x) atTop (𝓝 (f x))` and `UniformConvergesOn F f E := TendstoUniformlyOn F f atTop E`. This isolated draft writes those Mathlib predicates directly, so it does not depend on an unpublished/unapproved foundation module. Replacing them later by definitionally equal shared names will not change mathematical scope.

## Node coverage

| Node | Contract content |
| --- | --- |
| 7.19 | Explicit boundedness definition comparators; every countable subset of the domain of a pointwise bounded complex sequence admits one subsequence and one limit function converging at all its points. The consequence will use 7.23, separately from the definitions. |
| 7.21 | Exact moving peak `x² / (x² + (1-(n+1)x)²)`; term continuity, values between 0 and 1, uniform boundedness, pointwise zero limit, in-domain peak location `1/(n+1)` with exact value 1, and no uniformly convergent subsequence to any real function. Also the complex-valued n²-scaled 7.6 bump gives the failure of uniform boundedness despite individually bounded terms and pointwise convergence. The positive observation applies to every uniformly convergent sequence whose individual terms are bounded, retaining the full finite prefix. |
| 7.22 | Exact uniform equicontinuity definition, Mathlib comparator, individual uniform continuity, and failure for the 7.21 moving peaks. |
| 7.23 | Complex diagonal selection on an arbitrary countable subset, no domain topology; strict index increase and actual existence/convergence of a limit function. |
| 7.24 | On a compact subset of a metric space, uniform convergence of continuous complex terms implies source equicontinuity of the entire sequence. No continuity assumption on the limit is added. |
| 7.25 | Continuity, pointwise boundedness, and source equicontinuity on a compact set imply both uniform boundedness and a strictly indexed subsequence converging uniformly to a continuous complex function. Uniform boundedness is a conclusion, not a premise. |

Compact-subset formulations of 7.24/7.25 include the source's compact-metric-space statement by taking the full set, and apply directly to a compact subtype. Ambient limit functions are constrained only on the relevant set.

## Planned proof boundaries after acceptance

The boundedness observation reuses the exact n²-scaled PMA-7.6 witness; its local formula is only a definition and should be coordinated with the 7.6 owner to avoid duplicate substantive proofs. Its native integrals tend to positive infinity according to the accepted 7.6 inventory, which can contradict a common bound through the Chapter 6 integral estimate once those results are available. No native integral identity is asserted in this cluster. For compactness, use the reviewed pinned Mathlib APIs recorded in `ch07-api-landscape.md`, preserving the distinction between pointwise and common boundedness and between source uniform equicontinuity and library pointwise equicontinuity. Compactness-to-subsequence and bundled-map-to-uniform-convergence bridges must retain their metric/countability hypotheses.

The independent review and root oversight gates have passed; implementation is now authorized. This record does not itself claim any node proved or replace subsequent verification and hostile review.

## Completed implementation and local verification

Canonical source: `rudin/Rudin/PMA/Chapter07/Equicontinuity.lean`, SHA-256 `baffc08a75f000487493d784939d9b9af42f7c3b4441a52d73a6664aa9ec6ff0`. The original accepted contract draft remains unchanged at its reviewed hash. A direct textual comparison confirmed that every definition and contract, from `PointwiseBoundedOn` through `pma7_25_contract`, is unchanged in the canonical module.

All six numbered wrappers are now proved locally: `pma7_19`, `pma7_21`, `pma7_22`, `pma7_23`, `pma7_24`, and `pma7_25`.

- Countable selection uses a compact product of closed complex balls indexed by the countable domain subtype, followed by a strictly indexed convergent subsequence. This includes finite and empty domains without imposing any domain topology.
- Compact uniform boundedness is proved from the pointwise bounds and a finite cover at one source-equicontinuity tolerance. Only after deriving the common bound does the subsequence proof apply Mathlib's bounded-continuous-function Arzelà–Ascoli theorem.
- The 7.24 proof treats the finite prefix and uniformly controlled tail together. The source definition is explicitly compared with `UniformEquicontinuousOn` through the domain subtype.
- The moving peak has the exact source formula and a proved pointwise zero limit. Uniqueness of pointwise limits forces any proposed uniform subsequence limit to be zero; its reciprocal-index peaks contradict uniform convergence. The same peaks independently refute source uniform equicontinuity.
- The complex-valued `boundednessBump` is definitionally the complex cast of shared `IntegralSpikeSquared`. Individual boundedness and pointwise convergence reuse `integralSpikeSquared_continuous` and `integralSpikeSquared_pointwise` from `Chapter07.Examples`. A common bound would bound every native integral via `Chapter06.rsIntegral_abs_le_bound`, contradicting `integralSpikeSquared_integrals_atTop`. No measure/native integral substitution is made.

Verification completed:

1. `./lake-local build Rudin.PMA.Chapter07.Equicontinuity` passed with exit 0, 8,947 jobs, and no warnings in the canonical module.
2. `#print axioms` for all six wrappers returned only `propext`, `Classical.choice`, and `Quot.sound`.
3. Three separate stdin probes compiled successfully and used only the same permitted axioms: countable selection on the empty set for arbitrary functions; the complete Arzelà–Ascoli conclusion on an empty compact set; and a constant-in-space complex sequence `F n x = n` that is source-equicontinuous on a singleton but fails pointwise boundedness. The last probe checks that equicontinuity does not silently supply 7.25's boundedness premise.
4. The canonical file contains no proof placeholders, custom axioms, or `native_decide`.

There are no implementation blockers for these six nodes. Independent post-proof fidelity/hostile review and chapter-wide assembly remain owned by the parent/root; this record does not claim those later gates passed.
