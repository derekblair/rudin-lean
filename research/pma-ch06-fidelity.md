# Chapter 6 fidelity record

Scope: all 27 numbered main-text items, with the attached consequences listed in
`pma-ch06-inventory.md`. Six definitions, twenty theorems and one substantive
remark; exercises are excluded. Independent local-book extraction accepted the
inventory before proof implementation. The later inventory edit changes only its
review-status sentence, not mathematical scope.

The accepted source convention uses finite nondecreasing partitions, permitting
repeated points and a singleton interval. Suprema and infima are over closed
cells. Integrator increments use the actual values of an arbitrary nondecreasing
real function; right continuity is not assumed. `RSIntegrable` asserts ordered
endpoints, boundedness, monotonicity of the integrator and equality of finite
Darboux integrals. `RIntegrable` specializes the integrator to the identity.

The principal theorem for item 6.n is `Rudin.PMA.Chapter06.pma6_n`. Chapter06.lean
imports the following implementation modules and provides the complete book-order
index. Item 6.3 bundles its common-refinement and repetition-invariance results.
The final kernel coverage check requires actual theorem declarations, not merely
comments or unproved proposition-valued contracts.

| Nodes | Implementation | Full scope and independent evidence |
|---|---|---|
| 6.1–6.2 | Basic, Definitions | Native definitions, nonnegative increments, bounded sums/integrals and ordinary specialization. `ch06-definitions-final-review.md`. |
| 6.3–6.7 | Refinement, Criterion | Exact union of partition points; repeated-point invariance; both refinement inequalities; lower≤upper; epsilon equivalence; all three tag/refinement clauses, including absolute values inside the weighted sum. `ch06-root-foundation-review.md`. |
| 6.8, 6.11, 6.13 | Integrability | Continuity, continuous composition, products, absolute-value integrability and inequality. `ch06-integrability-independent-review.md`. |
| 6.9 | Monotone | Both increasing and decreasing functions, requiring continuity of the integrator. `ch06-monotone-independent-review.md`. |
| 6.10 | Endpoint, Exceptional | Finite relative discontinuities, integrator continuity only at the bad points, endpoint cases and an actual shared-jump counterexample. `ch06-exceptional-independent-review.md`. |
| 6.12 | Integrability, Split, Properties | All function/integrator linearity clauses, order, restriction and interval addition, and the absolute integral bound. `ch06-properties-independent-review.md`. |
| 6.14–6.16 | Jump | Left-continuous unit step, interior atom formula, nonnegative summable countable atoms, integral series convergence and integrator endpoint values. `ch06-jump-moment-independent-review.md`. |
| 6.17, 6.19 | Calculus | Both directions of derivative-density integrability; no derivative continuity assumption. Exact partition transport for continuous strictly increasing onto substitution, plus its derivative-weighted consequence. `ch06-calculus-independent-review.md`. |
| 6.18 | Moment | Quadratic moment for arbitrary nondecreasing mass, derivative density and countable/finite interior atomic formulas. `ch06-jump-moment-independent-review.md`. |
| 6.20–6.22 | Calculus | Uniform continuity of the primitive, relative endpoint derivatives, native FTC, both product integrability conclusions and integration by parts. `ch06-calculus-final-review.md` and `ch06-basic-independent-review.md`. |
| 6.23–6.25 | Vector | Coordinate definition, all attached linearity/split/density/primitive consequences, vector FTC, norm integrability and bound. Explicit complex isometry/integral bridge, complex bound, addition, complex scalar multiplication and FTC. `ch06-vector-final-review.md`. |
| 6.26–6.27 | Curve | Native polygonal supremum length in extended nonnegative reals, curve/arc/closed/rectifiable definitions, proved equivalence with variation, and native Riemann integral of continuous speed. `ch06-curves-independent-review.md`. |

All evidence filenames in the table are under `evidence/`. Earlier review snapshots
are retained honestly; later reviews and the final manifest identify the assembled bytes.

The complex case is exposed explicitly by `pma6_23_complex` and
`pma6_25_complex`, not left to an informal identification. Zero-dimensional vector
integrability retains endpoint-order and integrator-monotonicity guards. The
curve theorem additionally covers degenerate intervals and more general real
inner-product spaces; this strengthens the finite-dimensional source case.

Derivative conclusions use interval-relative derivatives and ordinarily require
a nondegenerate interval. Integration definitions and non-derivative identities
admit ordered degenerate intervals. No infinite-interval integration, endpoint
atoms beyond the accepted source statement, signed integrators, or exercises are
claimed. No accepted contract conjunct is deferred or counted through a stub.

Independent fidelity review and the additional hostile gate are separate steps.
The repository's inherited PROGRAM does not itself define a PROVED stamp; the
additional hostile requirement comes from the subsequent coordination instruction.
Final gate outcomes and exact bytes are recorded in `pma-ch06-checks.md` and
`evidence/ch06-verification.json`. Chapter 6 remains an isolated deliverable, with
no production integration or Chapter 6 commits implied by proof completion.
