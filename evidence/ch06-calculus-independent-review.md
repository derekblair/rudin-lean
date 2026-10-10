# Independent proof review: PMA 6.17 and 6.19

Verdict: **ACCEPTED** for the completed 6.17 and 6.19 proofs in the reviewed snapshot. No hidden hypothesis, weakened implication, incorrect integral semantics, or unresolved proof obligation was found.

Reviewed source: `rudin/Chapter06CalculusDraft.lean`, 510 lines, SHA256 `96f15f23d9276a48cb567b89676fe548298d2e5864a6b581921c38bf43553db7`. The author paused edits while the reviewer independently compiled this exact source with `./lake-local env lean Chapter06CalculusDraft.lean` from the isolated root. Result: exit 0, no warnings or errors. The file's explicit axiom audits for `pma6_17`, `pma6_19`, and `pma6_21` returned only `propext`, `Classical.choice`, and `Quot.sound`. No `sorry`, `admit`, `native_decide`, custom `axiom`, or `unsafe` token appears in the source.

The reviewer did not author these calculus proofs. This review read the actual contracts and complete proof bodies, together with the accepted Chapter 6 inventory, the independent source inventory, and the earlier contract review. It does not claim a new inspection of the book's page images. The earlier independent source and contract reviews remain the statement-fidelity evidence. Subsequent appended declarations or changed imports require their own checking; this verdict identifies the exact snapshot above.

## 6.17: full equivalence with an integrable derivative

The contract uses the native `RSIntegrable` and `RSIntegral` definitions, with the identity integrator for ordinary Riemann integration. The integrand is merely bounded. The nondecreasing integrator has its specified actual derivative relative to the closed interval at every point, including one-sided endpoints. That derivative is Riemann integrable; its continuity is not assumed. Both directions of the integrability equivalence and the equality under integrability are present. The nondegenerate interval premise agrees with the accepted derivative convention.

On a positive-width cell, `calculus_ftc_cell_squeeze` applies the mean value theorem using continuity supplied by differentiability and ordinary interior derivatives obtained from the within-interval derivatives. Repeated-point cells are handled separately by zero increments. Thus the increment approximation is bounded by the derivative's cell oscillation times its width without assuming a continuous derivative.

The weighted cell comparison multiplies this error by an actual bound on the integrand. The bounds for weighted cell suprema and infima handle zero weights explicitly and positive weights by division. Monotonicity of the integrator supplies nonnegative Stieltjes weights; no unmentioned derivative positivity premise is introduced. Summing gives simultaneous upper- and lower-Darboux-sum error bounds for every partition.

The integrability transfer takes a common refinement of a partition controlling the derivative's ordinary gap and a partition controlling the known integrand's gap. The proved refinement theorem preserves both bounds, and the native gap criterion yields the other integrability assertion. The final proof invokes this argument in both directions, reversing the absolute-difference estimate for the reverse direction. A separate common-refinement comparison bounds the two integrals in both orders and establishes equality. None of these steps presupposes the conclusion or replaces native Riemann integrability by another integral theory.

## 6.19: transport, degenerate intervals, and weighted substitution

The first clause requires only a continuous, strictly increasing, onto interval map; it has no derivative or inverse-derivative premise. Its interval orders are weak, so the statement includes the jointly degenerate case.

Endpoint images follow from monotonicity and the image equality. Mapping a partition preserves its number of cells and repeated points. Continuity gives the exact image of every closed cell, including zero-width cells, so the cell value sets and integrator increments agree. Conversely, choosing preimages of the old partition points gives an ordered partition: strict monotonicity proves both order and endpoint uniqueness. This argument also works when both intervals are singletons. Surjectivity of partition transport identifies the complete ranges of lower and upper Darboux sums, proving equality of the native integrals directly. Boundedness and integrator monotonicity transport through the same map.

The weighted clause applies the general transport theorem with the identity integrator and then the completed 6.17 theorem on the new interval. The derivative is required to be Riemann integrable, without continuity, strict positivity, or a nonvanishing condition. The product has the correct order and evaluation, `f (φ y) * φ' y`, and the equality has the stated source-to-target orientation. This clause uses the preapproved nondegenerate derivative convention.

## Scope and remaining work

The reviewed snapshot also contains the completed native FTC proof 6.21, and its printed axiom result was independently observed. This report's requested detailed proof acceptance is for 6.17 and 6.19. Definitions of the 6.20 and 6.22 contracts are present, but this snapshot has no proofs of those two nodes; no completion for them is claimed here. There are no blockers for the accepted 6.17/6.19 snapshot.
