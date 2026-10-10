# Independent proof review: scalar integrability and algebra

Verdict: **ACCEPTED** for `pma6_8`, `pma6_11`, `pma6_13`, and the completed helpers implementing 6.12(a), (b), (d), and (e). No hidden assumption, continuity strengthening, or change to native Darboux semantics was found. This report does not certify the separate interval-splitting proof or the final 6.12 wrapper.

Reviewed source: `rudin/Chapter06IntegrabilityDraft.lean`, 558 lines, SHA256 `001823e4c51a56b9c0d0afbe13801a757200178eac396081dec3b7abb91d5cec`. The author confirmed this source was stable. The reviewer independently read the complete file and compiled it using `./lake-local env lean Chapter06IntegrabilityDraft.lean` from the isolated root. Result: exit 0, no warnings or errors. Hash checks before and after the review agreed. The seven printed audits for the three numbered theorems and four algebra helpers showed only `propext`, `Classical.choice`, and `Quot.sound`. A full-source scan found no `sorry`, `admit`, `native_decide`, custom `axiom`, or `unsafe` token.

The reviewer did not author these proofs. Statement scope was compared with the accepted Chapter 6 inventory and prior source/contract evidence. All conclusions use the existing `RSIntegrable` and `RSIntegral`; no measure integral or substituted definition is introduced. The interval guard, boundedness, and monotonicity stored in `RSIntegrable` are extracted explicitly and used in the proof bodies.

## 6.8: continuous integrands

The contract permits every nondecreasing integrator and requires continuity only of the integrand on the closed interval. It includes degenerate intervals through `a ≤ b`. The uniform partition has a positive number of cells even for a singleton interval, where all widths are zero. Compact continuity supplies both boundedness and uniform continuity. A sufficiently small cell width bounds every cell oscillation by a chosen positive quantity. Multiplying by nonnegative integrator weights and telescoping gives a Darboux gap bound depending on total integrator increment. The denominator uses that increment plus one, so a zero total increment causes no division problem. The already proved native gap criterion completes integrability. No continuity of the integrator is used.

## 6.11: continuous composition

The input function is assumed only Stieltjes integrable, with its values in the specified compact interval; it is never strengthened to a continuous function. The outer function is continuous on that interval, yielding boundedness and uniform continuity. The proof obtains a pointwise affine estimate of its oscillation: a small-input-distance case uses uniform continuity, and the complementary case uses its global bound divided by the positive continuity scale. That estimate transfers to cell suprema and infima. The resulting weighted sum is controlled by the original function's Darboux gap and the finite integrator increment. Choosing the original gap sufficiently small establishes the composition's native integrability. The range premise is used at every application of outer continuity or boundedness; no global extension of the outer function's continuity is assumed.

## 6.12: completed algebra and order helpers

- `rsIntegrable_add` gives integrability and the integral identity for the sum of two integrable functions. Cell lower and upper inequalities, a common refinement controlling both original gaps, and the native integral bounds yield the claimed sum identity.
- `rsIntegrable_const_mul` permits every real scalar, including zero and negative values. Its gap estimate uses the scalar's absolute value. Exact tagged-sum scaling and tagged-sum error bounds prove the integral identity; no invalid positive-scalar monotonicity argument is used for a negative scalar.
- `rsIntegral_mono` needs both functions integrable and a pointwise order on the interval. It compares cell infima using boundedness and transfers the comparison through nonnegative weights and the lower-integral supremum.
- `rsIntegral_abs_le_bound` applies the native integral bounds to the supplied two-sided pointwise bound and gives the required total-increment factor. No unmentioned integrand or integrator continuity enters.
- `rsIntegrable_integrator_add` proves the integrability and integral identity for the sum of two nondecreasing integrators under the two original integrability hypotheses. Both raw Darboux sums add exactly in the integrator, and the common-refinement sandwich theorem proves the result.
- `rsIntegrable_integrator_const_mul` has the source's positive-scalar premise. It proves monotonicity of the scaled integrator, exact scaling of both Darboux sums, and exact scaling of tagged sums, then applies the proved scaling criterion. Its premise is not silently weakened to allow negative integrator scaling.

The abstract sandwich and scaled-tagged-sum helper hypotheses are proved explicitly at these public applications. They are ordinary reusable lemmas, not additional assumptions in the numbered contracts.

## 6.13: products and absolute values

The product theorem assumes only the two native integrability hypotheses. Squaring is obtained from 6.11 on a bounded range, and the polarization identity reduces multiplication to squaring, addition, and arbitrary scalar multiplication. Thus the proof does not introduce continuity of either original function.

Absolute-value integrability is another valid use of 6.11. The integral inequality applies monotonicity to both the original function and its negative, using the proved negative-scalar integral identity. It yields the full absolute value of the integral bounded by the integral of the absolute value.

## Review limits

Definitions of contracts 6.9, 6.10, and 6.12 are present, but this source does not contain their completed numbered wrappers. The 6.12 interval-splitting clause is owned by a separate source and was outside this review. Acceptance here therefore covers the three completed nodes 6.8, 6.11, and 6.13, together with the specific 6.12 helpers above; it does not imply completion of all five 6.12 clauses. There are no blockers for the accepted snapshot.
