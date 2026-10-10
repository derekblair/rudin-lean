# Independent final review: PMA 6.20 and 6.22

Reviewer: `completion_evidence`, a fresh reviewer of the calculus worker's final additions. Date: 2026-10-10. Outcome: **accepted**.

Reviewed final file: `rudin/Chapter06CalculusDraft.lean`, 674 lines.

SHA256: `ac36c016490bd347b592af764c1c6e5f544a6cd09ad7aac0c59a4c79da6c3c18`.

Review scope: complete proof review of the new primitive helpers, 6.20, 6.22, and the final boundary probes (lines 509 onward), plus the corresponding public contracts. The earlier 6.17/6.19 proofs and 6.21 had separate independent reviewers; this report does not replace those reviews. The entire final file was compiled independently here.

## PMA 6.20

The contract at line 49 concludes continuity, uniform continuity, and the correct relative derivative of the native indefinite Riemann integral at every relative continuity point of the integrand. `HasDerivWithinAt` on the closed interval includes the appropriate one-sided endpoint assertions and does not require ambient continuity. Its strict interval guard matches the accepted inventory's convention for derivative clauses.

The native singleton-integral helper is proved from finite Darboux bounds. The increment helper uses the proved interval restriction/additivity result, including zero-length restrictions. The Lipschitz estimate handles both orders of the two points, using the absolute integral bound on the corresponding ordered subinterval. The global bound is shown nonnegative before constructing the Lipschitz constant, so neither the continuity nor uniform-continuity conclusion depends on an invalid signed bound.

For differentiation, the ordered local error estimate comes directly from the source Darboux bounds with values between `c-ε` and `c+ε`. The reversed orientation is proved with an explicit sign identity. Relative continuity at the base point bounds the integrand at every intervening point, giving the little-o remainder condition for the within-interval derivative. Values outside the source interval are never constrained or used as an unannounced hypothesis.

## PMA 6.22

The contract at line 66 includes integrability of **both** products and the full integration-by-parts identity. It assumes only the stated within-interval derivatives and Riemann integrability of those derivatives; continuity of the derivatives is not added.

The proof derives continuity of the two primitives from their derivatives, uses native continuous-integrand and product integrability, then applies the product derivative rule and the already proved native FTC2 to their product. Native integral additivity gives the stated sign and ordering of the two product integrals. No totalized expression is mistaken for an existence statement.

## Boundary probes

- The constant-integrator probe uses the full derivative-density reduction with zero density and proves integrability and integral zero for any bounded integrand.
- The singleton substitution probe preserves the source's ordered-degenerate substitution case. Strict monotonicity on the singleton is properly vacuous, and native singleton integrability is separately supplied.
- The endpoint primitive probe only assumes that the integrand is constant **on the source interval**; it derives both one-sided endpoint derivatives without an ambient continuity assumption.

No remaining source-scope, endpoint, orientation, circularity, or proof-validity findings were identified in the reviewed additions.

## Independent verification

`./lake-local env lean Chapter06CalculusDraft.lean` completed with exit zero and no warnings or errors against the final hash. The eight transitive axiom checks printed by the file—five numbered theorems and three boundary probes—each use only `propext`, `Classical.choice`, and `Quot.sound`. The final source hash was rechecked after compilation and remained unchanged. A lexical scan found no placeholders, custom axioms, unsafe or opaque declarations, or `native_decide`.

Production integration and the chapter-wide audit remain the parent's responsibility.
