# Chapter 6 definitions: independent final review

**Verdict: ACCEPTED.** The actual native definition helpers and completed 6.1/6.2 proofs were read independently, compiled afresh, and audited recursively. No hidden regularity restriction or totalization gap remains in the reviewed statements.

## Reviewed source snapshots

- `rudin/Rudin/PMA/Chapter06/Basic.lean`: 215 lines, SHA256 `5192b99092c0fc7da7109b1e3ffd90446db62c73845b935172643456b46a3915`.
- `rudin/Chapter06BasicDraft.lean`: 100 lines, SHA256 `13adade605f2cff6904a9b5d24f06057595d0c760abc140dfd7831608c5ccf81`.
- `rudin/Rudin/PMA/Chapter06/Definitions.lean`: byte-for-byte identical to that draft, confirmed by `cmp` and matching SHA256.

This extends the earlier independent definition/source review. The reviewer did not author these helpers or the final 6.1/6.2 proofs and made no source changes during this review.

## Proof and fidelity findings

1. **Source partitions and interval guard.** `Basic.lean:12` retains weakly increasing finite chains, repeated points, and the harmless zero-cell case. The real infimum/supremum operations use actual closed-cell images. `RSIntegrable` at line 46 contains the corrected `a ≤ b` guard, bounded integrand, nondecreasing integrator, and equality of the two Darboux integrals. There is no continuity assumption on either function. The value alone is explicitly totalized and is not treated as existence.
2. **All extrema are justified.** Lines 64–137 prove every cell is nonempty and lies in the whole interval, prove nonnegative integrator weights, and obtain bounded cell images from the source boundedness predicate before applying conditional-completeness inequalities. Repeated-point cells cause no exception. The finite sum of increments telescopes exactly at lines 85–92.
3. **Finite sum and integral bounds are complete.** Lines 141–186 derive lower/upper sum bounds and boundedness above/below of their ranges. Lines 198–213 provide all four integral bounds. The latter proof uses an explicit single-cell partition to witness nonempty ranges on every ordered interval, and the established bounds to use real supremum/infimum correctly. It does not rely on an empty-set or unbounded-set default value. The lower-integral/upper-integral comparison is separately supplied by 6.5, as appropriate to the chapter dependency order.
4. **6.1 is the ordinary specialization.** `Definitions.lean:11` retains all accepted sum bounds, the four finite integral bounds, integrability iff equality under the source hypotheses, and the common integral value. The actual proof at lines 41–48 specializes the accepted native model to the identity integrator. It adds no restriction on partitions or integrand continuity.
5. **6.2 keeps arbitrary nondecreasing integrators.** The contract at lines 25–38 and proof at lines 50–56 include nonnegative weights, sum/integral bounds, integrability iff equality, common value, and the ordinary specialization. The proof uses the source hypotheses directly. No right-continuity, strictly positive weight, measure representation, or mesh limit is assumed.
6. **Constant and boundary cases are proved.** Lines 58–66 prove arbitrary real constant integrands have integral `c*(α(b)-α(a))`. Lines 68–78 prove every bounded integrand is integrable against a constant integrator with value zero. Lines 80–98 prove every function/integrator pair is integrable on the equal-endpoint interval with integral zero, deriving the singleton's boundedness and monotonicity instead of assuming them.

The explicit boundedness assumptions in 6.1/6.2 are the source convention, although the supplied lower/upper bounds would themselves imply boundedness. The contracts' integrability iff clauses are conditioned on precisely those source admissibility hypotheses, not a weaker equality of totalized expressions.

## Independent validation

Both `./lake-local env lean Rudin/PMA/Chapter06/Basic.lean` and `./lake-local env lean Chapter06BasicDraft.lean` exited **0**, without diagnostics. A separate Lean stdin audit importing the built `Definitions` module printed recursive axioms for `pma6_1`, `pma6_2`, `rsIntegral_const`, `rsIntegral_const_integrator`, `rsIntegral_same_endpoint`, and `darboux_integrals_bounds`: each is exactly `[propext, Classical.choice, Quot.sound]`.

Two independent boundary probes also compiled successfully in that stdin audit: for `b < a`, native `RSIntegrable f α a b` is impossible; and the partition type `Partition a b` is empty. They use the actual order guard and endpoint/monotonicity representation, respectively. No temporary Lean file or source edit was needed for these probes.

A textual scan found no proof placeholders, custom axiom declarations, native-decide use, or local option changes in either reviewed source. This verdict covers 6.1/6.2 and their reviewed native helpers; it does not certify unrelated chapter nodes or replace the final integrated chapter build.
