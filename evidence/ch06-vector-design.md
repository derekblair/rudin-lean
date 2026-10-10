# PMA 6.23–6.25: native Euclidean and complex integration

Status: all three Euclidean contracts and both explicit complex bridge contracts have complete Lean proofs. Final author-verified draft: `rudin/Chapter06VectorDraft.lean`, 426 lines, SHA-256 `1830138b9712dc5c6bd97293c0396df8160da84c25be76f55f0069dc3962ff98`.

## Scope and accepted contracts

Only local statement blocks for 6.23–6.25 on PDF pages 143–145 were read. No textbook proof text was used and no book content was saved. The parent approved the actual Euclidean contracts and the explicit complex bridge design before their proofs were implemented.

The vector type is `EuclideanSpace ℝ (Fin n)`, with its Euclidean norm, rather than the supremum-norm function space. `VectorRSIntegrable` requires the common interval order and monotone integrator, and native scalar Riemann–Stieltjes integrability of each coordinate. `VectorRSIntegral` is the vector of those scalar integrals, constructed with `WithLp.toLp 2`. The guards are retained even for the zero-dimensional vector space, so empty-coordinate quantification cannot erase the valid-interval or monotonicity requirements.

6.23 includes the literal coordinatewise definition, integrand addition and real scalar multiplication, interval splitting, addition and positive scaling of the integrator, the full integrable-density equivalence and value identity, and continuity, uniform continuity, and within differentiation of the indefinite ordinary Riemann integral. The density clause assumes actual derivatives of the integrator and boundedness of the vector function; it does not replace the equivalence by only one direction. All derivative clauses retain nondegenerate `a < b`, including one-sided endpoint semantics on `Icc`.

6.24 proves the vector fundamental theorem for an actually differentiable primitive and an integrable vector derivative. It does not assume continuity of the derivative. 6.25 proves both integrability of the Euclidean norm and the norm-of-integral inequality, without an extra nonzero-integral premise.

## Proof structure

Coordinatewise scalar theorems establish every 6.23 algebraic, splitting, density, and primitive clause, as well as 6.24. The existing Chapter 5 derivative-components theorem transports actual real-parameter vector derivatives. A proved finite-sum helper includes both integrability and the integral identity, with an explicit zero-sum base case.

For 6.25, each coordinate square is integrable; the finite sum is the squared Euclidean norm. Continuous composition with real square root proves norm integrability. Integration of the inner product with a fixed vector commutes with that inner product by the finite-sum helper. Applying the scalar order theorem to the Cauchy–Schwarz inequality with the integral vector proves the desired norm bound. Integral nonnegativity is established separately, so the case of zero integral vector is handled without division.

All scalar integration predicates and values come from the native Darboux framework. No Bochner, Lebesgue, or library interval integral replaces that framework.

## Explicit complex specialization

`ComplexRSIntegrable` requires native real and imaginary coordinate integrability. `ComplexRSIntegral` is the real-coordinate integral plus `I` times the imaginary-coordinate integral. `complexVectorEncoding` is the actual real linear isometric equivalence `Complex.orthonormalBasisOneI.repr` into the two-dimensional Euclidean space.

The proved `pma6_23_complex_contract` identifies its coordinates with real and imaginary parts, proves exact norm preservation, proves complex integrability if and only if encoded vector integrability, proves that encoding commutes with the native integral, and proves equality of the two integral norms. `pma6_25_complex` consequently proves the explicit complex norm-integrability and integral-norm inequality. Additional native complex corollaries prove addition, multiplication by an arbitrary complex scalar, and FTC directly from the coordinate scalar theorems.

## Validation and probes

`./lake-local env lean Chapter06VectorDraft.lean` exits 0 with no warnings. Ten recursive axiom reports cover `pma6_23`, `pma6_24`, `pma6_25`, both complex contracts, the three native complex corollaries, and two boundary probes. All report only `propext`, `Classical.choice`, and `Quot.sound`. The file contains no `sorry`, `admit`, or custom axiom declaration.

The first boundary probe rejects a reversed integration interval even in dimension zero. The second proves that the constant purely imaginary unit is complex integrable on `[0,1]` and that its native ordinary integral is exactly the imaginary unit, checking both coordinate placement and reconstruction.

The source is frozen for independent final review in `evidence/ch06-vector-final-review.md`. No proof obligations remain in this draft. Integration into the assembled chapter remains the parent's responsibility.
