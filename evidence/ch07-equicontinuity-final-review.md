# Independent final review: PMA 7.19 and 7.21–7.25

Verdict: **ACCEPT**. I read all 417 lines of the final canonical module, its shared definitions, and the accepted inventory. I authored none of the reviewed module. No missing conjunct, strengthened premise, vacuous selection result, wrong equicontinuity definition, or proof defect was found. This review is scoped to these six nodes, not the entire chapter.

## Frozen inputs and reproducible client

- `rudin/Rudin/PMA/Chapter07/Equicontinuity.lean`: SHA256 `baffc08a75f000487493d784939d9b9af42f7c3b4441a52d73a6664aa9ec6ff0`.
- `rudin/Rudin/PMA/Chapter07/Basic.lean`: `b6b8b58999ad0025fd3ab28bc0ba3a4df5a07cc395158b99a14c05055bfa2b1a`.
- `rudin/Rudin/PMA/Chapter07/Examples.lean`: `a25907d75b1bae77638eaaea291888989f6d9f319f0d2cea71ee74c9a25f9bd5`.
- `research/pma-ch07-inventory.md`: `f8e87ad7ccb765bfd4407e251958c5378552b209d32eca60a75e13e0ca9da0f0`.
- Persisted independent client: `rudin/Chapter07EquicontinuityReviewProbe.lean`, SHA256 `6708c235b026a88d8c94c71be647388af050a8a2739ec39d830051a52a489f17`.

From the isolated repository root, the following fresh checks passed with exit 0 and no warnings:

```sh
./lake-local env lean Rudin/PMA/Chapter07/Equicontinuity.lean
./lake-local env lean Chapter07EquicontinuityReviewProbe.lean
```

The client imports the canonical module, proves six boundary statements, verifies that all six `pma7_*` principals are actual kernel theorem declarations, and recursively checks the axioms of all 112 visible Chapter07/client declarations, including private/generated declarations after name normalization. Every dependency is among `propext`, `Classical.choice`, and `Quot.sound`. This is an imported-scope audit, not a claim that 112 is the final chapter-wide declaration count. A source scan found no placeholders, custom axioms, unsafe implementations, or alternate proof bodies; the only matches for “axiom” were `#print axioms` commands.

## Actual contracts and proofs

- **7.19:** The two boundedness definitions preserve their distinct quantifier orders. Pointwise boundedness is one finite bound for each point, uniformly over sequence indices; uniform boundedness is one bound over both. The attached countable-subset selection is proved by the later 7.23 theorem, without claiming that it follows from the definitions alone.
- **7.21:** The exact positive-index peak formula is retained with `n+1`. The denominator is proved positive, the values lie in `[0,1]`, the reciprocal peak lies in the closed interval (including index zero, where it is the right endpoint), and its value is one. Every strictly increasing subsequence remains pointwise zero and therefore cannot converge uniformly to any function. The preceding boundedness caution uses the native Chapter 6 integral growth of the squared spike to disprove a common family bound. The converse observation includes every individually bounded member: a fixed tail member bounds the limit and the finite prefix supplies the rest.
- **7.22:** `SourceEquicontinuousOn` places the distance bound before both points and the family index. Its equivalence is with Mathlib's **uniform** equicontinuity on the set. Individual uniform continuity and the failure for the peaks are explicit conclusions. There is no substitution of mere pointwise equicontinuity on arbitrary domains.
- **7.23:** Selection requires only countability and pointwise boundedness of complex values; the domain has no topology. The proof uses the countable subtype and compact coordinate balls, applies sequential compactness to their product, and extends the resulting limit by zero outside the selected set. The subsequence map is `StrictMono`. Finite and empty sets remain allowed.
- **7.24:** Compactness makes the continuous limit and finitely many initial members uniformly continuous. A finite-prefix bound combines with the uniform-convergence tail estimate, so the conclusion covers the full sequence. No continuity of an ambient extension is assumed.
- **7.25:** Both required conclusions are present: a uniform bound for the whole sequence and a strictly indexed uniformly convergent subsequence with continuous limit. The premise is only pointwise boundedness, not uniform boundedness. A finite compact cover first produces the latter; the bounded-continuous-function Ascoli argument then supplies selection on the compact subtype, with an arbitrary extension outside it. Empty compact sets are handled without extra nonemptiness assumptions.

The proof dependencies are acyclic. In particular, the selection appended to 7.19 explicitly uses 7.23, and the 7.21 spike caution uses existing 7.6/native Chapter 6 bounds. Library compactness is a proof route, not a replacement of the source's conclusions.

## Fresh adversarial boundary probes

The persisted client establishes:

1. Countable selection on an empty set, with an arbitrary domain type and no topology.
2. Countable selection on a singleton, still with no domain topology and only the bound at that point.
3. The single-member family `x ↦ x²` on the whole real line fails the source's equicontinuity definition. Its continuity cannot accidentally discharge uniform equicontinuity.
4. A sequence with first member `x ↦ (x : ℂ)` and all later members zero is equicontinuous on `[0,1]`; the first member still has endpoint distance one. This exercises inclusion of the finite prefix.
5. Both Ascoli conclusions for an arbitrary sequence on the empty compact set.
6. The exact peak sequence has no uniform limit on `[0,1]`, as a specialization of its stronger no-uniform-subsequence conclusion.

These probes supplement the complete source/proof reading; they do not claim exhaustive countermodel coverage. No reviewed source, production file, protected chapter, Git state, session, configuration, or credential was altered.
