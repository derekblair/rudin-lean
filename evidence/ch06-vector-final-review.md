# Chapter 6 vector and complex integration: independent final review

**Verdict: ACCEPTED**, covering complete nodes 6.23, 6.24, and 6.25, their explicit complex specialization, and the additional native complex corollaries. No unresolved contract or proof obligation was found in this snapshot.

Reviewed `rudin/Chapter06VectorDraft.lean`, all 426 lines, SHA256 `1830138b9712dc5c6bd97293c0396df8160da84c25be76f55f0069dc3962ff98`. The file was read directly, independently compiled, and hashed again after compilation; the hash remained unchanged. The reviewer did not author these vector/complex definitions or proofs and made no source edits.

## Representation and source scope

- **Euclidean semantics, lines 16–25.** The value type is `EuclideanSpace ℝ (Fin n)` with its Euclidean norm; the integral is the vector of native scalar Darboux integrals using `WithLp.toLp 2`. This is not a supremum-norm function space. The integrability predicate explicitly retains ordered endpoints and a nondecreasing integrator even in dimension zero, preventing empty-coordinate quantification from discarding the source guards.
- **Full 6.23 scope, lines 27–62.** All attached consequences are present: coordinatewise definitions, integrand addition and arbitrary real scalar multiplication, interval splitting, integrator addition and positive scaling, the full derivative-density integrability equivalence and value identity, primitive continuity, uniform continuity, and relative derivatives at relative continuity points. Integrator density needs only a Riemann-integrable derivative. It does not require a continuous derivative or ordinary Riemann integrability of the original vector function.
- **Derivative interpretation, lines 51–62 and 66–69.** All inputs are real. Derivative clauses use nondegenerate closed intervals and actual `HasDerivWithinAt`, so endpoint derivatives retain the Chapter 5 one-sided meaning. The vector FTC assumes integrability of the derivative, not its continuity. Ordinary non-derivative integration identities keep ordered equal-endpoint cases through their helpers.
- **6.25 scope, lines 73–77.** Both integrability of the Euclidean norm and the norm-of-integral inequality are conclusions. There is no extra nonzero-integral assumption, no prior norm-integrability assumption, and no measure or Bochner integral substitution.

## Actual proof checks

The 6.23 algebra and splitting proofs at lines 83–137 apply the proved native scalar identities coordinatewise, then use Euclidean coordinate extensionality. The density proof at lines 139–177 obtains every scalar coordinate's bound from the vector norm bound and applies both directions of scalar 6.17. The scalar/vector multiplication order is explicitly reconciled.

The FTC proof at lines 179–185 uses the existing Chapter 5 component equivalence for a real-parameter derivative and scalar 6.21. The primitive proof at lines 187–204 applies scalar 6.20 to each coordinate, transfers coordinate continuity through the actual continuous linear equivalence with the Euclidean space, derives uniform continuity on the compact interval, and reconstructs the actual vector derivative from coordinate derivatives. The final 6.23 wrapper at lines 206–223 supplies every accepted conjunct.

For 6.25, the finite-sum helper at lines 225–241 has an explicit empty-sum case supplied by the native constant-integral theorem. Lines 243–252 prove integrability of the sum of squared coordinates, then use continuous square-root composition and the Euclidean norm identity. Lines 254–267 prove that native integration commutes with a fixed inner product. The main proof at lines 269–283 integrates the pointwise Cauchy–Schwarz bound using the integral vector as that fixed vector. It separately proves nonnegativity of the norm integral, so its final inequality also handles the zero integral vector without division.

## Explicit complex specialization

Lines 285–302 define the actual real linear isometry from complex numbers to two-dimensional Euclidean space using the orthonormal One/I basis. Native complex integrability means integrability of the real and imaginary coordinates; its integral reconstructs those two native scalar values as a complex number. The accepted complex contract identifies the coordinates, preserves the norm, proves the integrability equivalence, and proves that encoding commutes exactly with integration.

The actual proofs at lines 309–351 establish these claims and transport the Euclidean norm-integrability inequality to complex values. Lines 353–363 prove complex FTC through real derivative components. Lines 365–396 additionally prove native complex addition and multiplication by an arbitrary complex scalar; the latter expands the actual real and imaginary products, including the required negative cross term. No complex differentiability assumption is introduced for a real-parameter function.

## Independent compiler, axiom, and boundary checks

`./lake-local env lean Chapter06VectorDraft.lean` exited **0**, without warnings. The independent compiler run printed exactly `[propext, Classical.choice, Quot.sound]` for all ten audit targets:

- `pma6_23`, `pma6_24`, `pma6_25`;
- `pma6_23_complex`, `pma6_25_complex`;
- `complexRSIntegral_ftc`, `complexRSIntegrable_add`, `complexRSIntegrable_const_mul`;
- `vector_integrability_zero_dimension_guard_probe`, `complex_imaginary_constant_probe`.

The first actual probe, lines 398–402, rejects a reversed interval even for the zero-dimensional space. The second, lines 404–413, proves that the native integral of the constant imaginary unit on [0,1] is the imaginary unit, checking coordinate placement and complex reconstruction. The complete source scan found no proof placeholders, custom axiom declarations, native-decide use, or option changes.

This acceptance is for the reviewed stable draft and its native scalar dependencies. Root still owns the final module copy, assembled chapter build, and chapter-wide axiom/coverage audit.
