# PMA Chapter 6 calculus: contracts, proofs, and validation

Scope: PMA 6.17 and 6.19–6.22, checked against the local source PDF pages 140–143. Only statement paraphrases and original formal mathematics are retained. The book was read locally and was not copied, committed, or uploaded.

`rudin/Chapter06CalculusDraft.lean` uses the native closed-cell Darboux definitions through the Chapter06 Split and Integrability modules. Ordinary Riemann integration uses the identity integrator. All five concrete contracts have proof terms. There are no custom axioms, placeholders, or measure-based replacements of native Stieltjes integration.

## Accepted contract scope

- **6.17:** A monotone integrator has an actual derivative relative to the original closed interval, and that derivative is ordinarily Riemann integrable. For any bounded real integrand, Stieltjes integrability is equivalent to ordinary Riemann integrability of the derivative-weighted product. The integral values agree. Both directions are proved; derivative continuity is not assumed.
- **6.19:** A strictly increasing continuous map takes the entire source closed interval onto the target closed interval. Composition preserves Stieltjes integrability and the integral. This first clause includes singleton intervals (`a ≤ b`, `A ≤ B`). The derivative-weighted consequence uses nondegenerate intervals, an actual relative derivative of the substitution, and ordinary Riemann integrability of that derivative and the original integrand. The substitution derivative may vanish, and no smooth inverse is assumed.
- **6.20:** The indefinite ordinary Riemann integral is continuous and uniformly continuous on the entire closed interval. At every relative-continuity point of the integrand, including both endpoints, its actual relative derivative equals the integrand value. The proof also supplies an explicit Lipschitz estimate from an integrand bound. No property of the total representative outside the source interval is needed.
- **6.21:** An actual relative derivative on the closed interval that is ordinarily Riemann integrable integrates to the difference of antiderivative endpoint values. One-sided endpoint derivatives suffice.
- **6.22:** Both factors have actual relative derivatives which are ordinarily Riemann integrable. Both product integrands are proved integrable, and the integration-by-parts identity follows. These product integrability results are conclusions, not added hypotheses.

The derivative-based clauses use nondegenerate intervals. Native restrictions, estimates, zero-length integrals, and the first substitution clause include degenerate intervals. Total function representatives retain explicit source-domain membership.

All five concrete contracts were accepted by the independent `remaining_scope` reviewer before proof implementation. Review corrected the first substitution clause to include singleton intervals and explicitly retained primitive uniform continuity.

## Native proof structure

**6.21:** On every positive-width partition cell, actual relative differentiability gives continuity on the cell and ordinary differentiability in its interior. The mean value theorem bounds the antiderivative increment by the cell infimum and supremum of the derivative times the width. Zero-width cells give zero on all sides. Finite endpoint increments telescope; the supremum of lower sums and infimum of upper sums squeeze the endpoint difference. This proof uses no auxiliary integral representation.

**6.17:** The same cell estimate controls the discrepancy between integrator increments and sampled derivative times interval width. The discrepancy is bounded by the derivative's cell oscillation times width. For an integrand bounded in absolute value by M, the differences of both native upper sums and both native lower sums are bounded by M times the derivative's ordinary Darboux gap. Common refinements and the native integrability criterion transfer integrability in both directions. A second small-gap comparison gives equality of integrals. The source derivative need only be Riemann integrable.

**6.19:** Map each partition point through the strictly increasing continuous substitution. The image of every closed cell is precisely the interval between its mapped endpoints, so the cell value sets and integrator increments agree. Surjectivity of the map on the full interval permits lifting any target partition back to a source partition; strict monotonicity reflects point ordering. The ranges of lower and upper sums are therefore equal. This works on singleton intervals as well. The weighted consequence then follows from the proved 6.17.

**6.20:** Native interval splitting identifies a primitive increment with the integral on the intervening ordered interval. Native absolute bounds give the Lipschitz estimate in both endpoint orders. At a relative-continuity point, bound the integrand on each nearby intervening interval between its value at that point minus epsilon and that value plus epsilon. Native Darboux bounds give a first-order remainder at most epsilon times the distance. The relative little-o derivative criterion then proves the derivative, including at endpoints. No auxiliary linearity theorem for a shifted integrand or extension outside the domain is required.

**6.22:** Actual differentiability makes the original factors continuous on the source interval. The native continuous-integrability theorem and multiplication closure establish integrability of both product terms. Apply 6.21 to the product rule and use native additivity of the integral.

## Supporting declarations and boundary probes

- `calculus_singleton_integrals`: every total f and integrator alpha is natively integrable on `[a,a]`, with integral zero. This is derived from native Darboux bounds.
- `calculus_primitive_increment`: native integrability on each ordered subinterval and the exact primitive increment identity.
- `calculus_primitive_lipschitz`: absolute primitive increments are bounded by M times endpoint distance, for either endpoint order.
- `calculus_primitive_error_ordered` and `calculus_primitive_error`: the local first-order remainder estimate behind the relative derivative proof.
- `calculus_probe_constant_integrator`: every bounded integrand is integrable against a constant integrator with integral zero. This checks the vanishing-derivative case of the two-way conversion.
- `calculus_probe_singleton_substitution`: composition through a constant map between singleton intervals satisfies the full first substitution clause.
- `calculus_probe_relative_primitive_endpoints`: an integrand equal to a constant only on the closed interval gives that primitive derivative at both endpoints, with completely arbitrary values outside the interval.

## Validation and independent review

The command `./lake-local env lean Chapter06CalculusDraft.lean` checks the entire draft against the pinned local dependencies. Each of the five `pma6_*` proofs and the three boundary probes is audited with `#print axioms`; the required result is exactly `propext`, `Classical.choice`, and `Quot.sound`.

The completed 6.21 proof was independently accepted earlier. The `oscillation` reviewer independently compiled and accepted the full 6.17 and 6.19 proof core at SHA256 `96f15f23d9276a48cb567b89676fe548298d2e5864a6b581921c38bf43553db7`; the subsequent changes append 6.20/6.22 and boundary checks and import their native prerequisites. See `ch06-calculus-independent-review.md` for that core review. The `completion_evidence` reviewer subsequently independently read and accepted all new helpers, 6.20/6.22, and the three boundary probes, and independently compiled the entire final file with no warnings or errors. See `ch06-calculus-final-review.md`. The final frozen draft is 674 lines at SHA256 `ac36c016490bd347b592af764c1c6e5f544a6cd09ad7aac0c59a4c79da6c3c18`; all eight printed proofs have only the three permitted standard axioms.

No production checkout, Git state, global configuration, process session, or credential was changed. Chapter 5 is preserved.
