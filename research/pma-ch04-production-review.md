# PMA Chapter 4: Independent Production and Boundary Review

Final actual-source review: 2026-10-10 07:14:36 UTC. This reviewer is independent of the production authors. Reviewed the program rules, approved inventory, approved fidelity report, actual production definitions, every numbered contract, all principal theorem signatures, and independent boundary examples/counterexamples. The approved source statements were already reviewed independently; this pass did not reproduce source proof text.

## Final production verdict

**PASS: every approved definition/contract and all 34 principal theorem signatures match the completed actual production file `rudin/Rudin/PMA/Chapter04.lean`.** The declaration-level comparison strips comments and whitespace while preserving all mathematical syntax. There are no missing declarations or substantive differences.

Reviewed production source SHA256: `71ac9841413d7046b72f943541667d91f77dfc77924fbc588c2dbea277754df8`.

| Approved file | Definitions/contracts compared with actual main | Result |
|---|---:|---|
| `Chapter04SharedContracts.lean` | 3 | All identical |
| `Chapter04OpeningContracts.lean` | 25 | All identical |
| `Chapter04CompactContracts.lean` | 18 | All identical |
| `Chapter04AdvancedContracts.lean` | 34 | All identical |
| **Total comparisons** | **80** | **Zero missing, zero differences** |

The 80 comparisons cover 79 distinct declarations because `OscillatingSine` appears in both compact and advanced approved batches. All 34 numbered principal contracts are included: 12 opening, 12 compact, and 10 advanced nodes. All principal signatures match exactly: `pma4_N : pma4_N_contract` for N = 1–24, and `node_4_N : Statement_4_N` for N = 25–34. The actual main includes all 34 proof declarations in the approved dependency order, including the deferred 4.24 following its 4.27 dependency.

Before final integration, every prospective draft declaration was also compared with its approved counterpart. In particular, the final weighted-jump production for 4.31 preserves the full arbitrary-countable-index, injective-point, positive-summable-weight construction, both continuity conventions, prescribed jumps, and exact-set realization for empty, finite, and infinite countable sets. Final extended production 4.32–4.34 preserves all ten approved neighborhood/accumulation/limit/partial-operation definitions and contracts. Both final advanced and extended drafts independently recompiled without warnings, and independent namespace audits passed with only `propext`, `Classical.choice`, and `Quot.sound`.

The comparison retains the substantive source requirements: ambient punctured accumulation; relative continuity and subspace comparators; only a nonzero denominator limit for limit algebra; compact-domain nonemptiness for extrema; empty-set connectedness; finite metric-valued one-sided limits; strict/interior IVT clauses; non-strict monotonicity; arbitrary countable injective weighted jump families; corrected punctured extended accumulation; and explicit partial-arithmetic guards. Source corrections remain documented in `pma-ch04-inventory.md` and `pma-ch04-fidelity.md`.

## Independent probes

`rudin/Rudin/PMA/Chapter04Probes.lean` is the integrated probe artifact and imports only `Rudin.PMA.Chapter04`. It contains 18 public probe theorems and two private geometric witnesses. The same probes were first independently compiled and audited in `rudin/Chapter04ProbesDraft.lean`. The probes use direct examples and counterexamples, rather than restating production theorem proofs.

| Probe | Boundary checked |
|---|---|
| `singleton_continuous_but_no_limit` | Every function is continuous on its singleton domain; no punctured limit at that singleton exists. |
| `limit_outside_domain` | The identity on `(0,∞)` has limit zero at zero, which is outside its domain. |
| `removable_value_disagrees` | Changing only the origin value to one preserves a zero limit and destroys continuity. |
| `denominator_may_vanish_away_from_approach` | A denominator vanishing at two still permits its reciprocal limit at zero. The original domain need not exclude all its zeros. |
| `zero_over_zero_limit_counterexample` | Both numerator and denominator tend to zero, while their quotient on the nonzero domain tends to one and cannot tend to totalized `0/0 = 0`. |
| `empty_compact_cannot_attain` | The empty set is compact but contains no point attaining even a constant value. |
| `empty_connected_image` | Rudin connectedness includes the empty set and its empty image. |
| `one_sided_boundary_asymmetry` | The identity admits the right limit at the left interval endpoint; the left limit there is excluded by the domain convention. |
| `constants_are_both_monotonic` | Constants satisfy both non-strict monotonicity directions. |
| `constant_not_first_kind` | Continuous constants are never first-kind discontinuities, despite having both sided limits at interior points. |
| `literal_example_values` | The piecewise jump takes zero at −2 and two at zero; the rational identity takes two at rational input two. |
| `empty_jump_family` | An empty index family yields zero for both sided jump constructions. |
| `singleton_jump_family` | At a singleton jump of size three, the strict construction is zero and the non-strict construction is three. |
| `repeated_jump_points_combine` | Two repeated points with unit weights produce jump two, demonstrating why the prescribed unit-jump theorem needs injectivity. |
| `singleton_extended_limit_rejected` | No extended target is a limit at a singleton domain point under the corrected punctured accumulation definition. |
| `forbidden_extended_sum_product` | Both opposite-infinity sums and all four zero-times-infinity order/sign cases are excluded. |
| `forbidden_extended_quotients` | All four infinity/infinity sign combinations and every zero denominator are excluded. |
| `permitted_extended_arithmetic` | Same-sign infinite sums, zero plus infinity, zero times zero, signed nonzero infinite products, finite over infinity, and infinity over nonzero finite values remain admissible. |

Validation completed with pinned Lean 4.34.1 and existing Mathlib oleans:

- `lake env lean -o .lake/build/lib/lean/Chapter04ProbesDraft.olean Chapter04ProbesDraft.lean` exits successfully with no errors or warnings.
- Namespace audit via `Rudin.PMA.Audit.checkNamespaceAxioms` checks all 24 public/private/generated probe declarations and permits only `propext`, `Classical.choice`, and `Quot.sound`.
- Placeholder scan finds no `sorry`, `admit`, or `native_decide` tokens in the probe source.

## Final integrated verification

**PASS.** The production owner completed the final default `lake build`: 8,944 jobs succeeded, including the canonical probe module importing the completed main. The reviewed main SHA256 remained `71ac9841413d7046b72f943541667d91f77dfc77924fbc588c2dbea277754df8`.

The final recursive `Rudin.PMA.Chapter04` axiom audit checks 275 declarations, including the probes, and permits only `propext`, `Classical.choice`, and `Quot.sound`. The probe-namespace audit separately checks 24 declarations, which are a subset of the recursive chapter audit. The standalone main audit before importing probes checked 247 declarations. These final integrated build/audit results were supplied by the production owner after the independent actual-source comparison; the independent draft/probe checks are recorded above.

All 34 production contracts and principal signatures have now passed independent preservation review; the 18 boundary probes pass in the canonical default build; and final build/axiom verification is complete.
