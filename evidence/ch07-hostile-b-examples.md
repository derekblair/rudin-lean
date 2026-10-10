# Additional hostile gate B: PMA 7.2–7.6

Verdict: **ACCEPT; no finding**. This is a fresh adversarial supplement covering the counterexample modules independently of their author/main B reviewer. I authored neither module. I read all 301 lines of Examples and all 206 lines of RationalIndicator, including their complete contracts and proofs, against the accepted inventory.

## Exact scope and frozen inputs

- `rudin/Rudin/PMA/Chapter07/Examples.lean`: SHA256 `a25907d75b1bae77638eaaea291888989f6d9f319f0d2cea71ee74c9a25f9bd5`.
- `rudin/Rudin/PMA/Chapter07/RationalIndicator.lean`: `edcdd11545100cbd19fb90d3382d5baf8a5a7b34907ca7afdf44560ad53fbe3d`.
- Shared `rudin/Rudin/PMA/Chapter07/Basic.lean`: `b6b8b58999ad0025fd3ab28bc0ba3a4df5a07cc395158b99a14c05055bfa2b1a`.
- Accepted `research/pma-ch07-inventory.md`: `f8e87ad7ccb765bfd4407e251958c5378552b209d32eca60a75e13e0ca9da0f0`.
- Persisted independent client `rudin/Chapter07ExamplesHostileProbe.lean`: `d33f83980d343f223ff7744a87eb66f2f078b11ce96448bc62038bf2f8d7dd69`.

Final hashes were checked again after the probes; all reviewed sources remained unchanged. Fresh actual-source compilation and the client passed with exit 0 and no warnings:

```sh
./lake-local env lean Rudin/PMA/Chapter07/Examples.lean
./lake-local env lean Rudin/PMA/Chapter07/RationalIndicator.lean
./lake-local env lean Chapter07ExamplesHostileProbe.lean
```

The client checks all five principal declarations are actual kernel theorems and recursively audits all 106 visible Chapter07/client declarations, including normalized private/generated names. Only `propext`, `Classical.choice`, and `Quot.sound` occur. This is the imported scope, not the final full-chapter declaration count. A source scan found no placeholders, custom axioms, unsafe implementations, or alternate proof bodies.

## Attacks on the actual source statements and proofs

**7.2: order of limits and totalization.** The positive parameters are represented by `m+1` and `n+1`. Both families of inner `Tendsto` assertions are present and proved before either `limUnder` is rewritten. Both iterated limits are then justified, and their inequality is explicit. A totalized limit operator alone cannot supply either conclusion.

**7.3: zero index and exceptional point.** The geometric terms start at index zero, unlike the positive-index examples. The exact ordered Chapter 3 series sum is zero at zero and `1+x²` elsewhere. Each term is continuous because its denominator is nonzero, including the zero-index denominator. The discontinuity proof treats the exceptional point. The use of an absolutely summable geometric library series in this particular proof is legitimate: it proves the ordered source conclusion for this series rather than changing a general series definition to unconditional summability.

**7.4: parity, factorial grids, and genuine native nonintegrability.** The inner limit uses the square of cosine, so cosine equal to minus one is handled correctly. The integer-grid branch proves every positive even power is one; the complementary branch proves cosine squared is strictly below one and obtains convergence to zero. For rational arguments, the denominator eventually divides the factorial, with the signed numerator retained. For irrational arguments, multiplying by a nonzero factorial cannot produce an integer. Both actual inner and outer limits are explicit before the iterated-limit wrapper. Rational/irrational density proves discontinuity at every real point. The native Darboux proof establishes cell extrema only for cells of positive width; repeated partition points are separately handled by zero weights. Lower sums are zero and upper sums equal `b-a`. Nonintegrability then uses the positive gap on **nondegenerate** intervals, without incorrectly excluding singleton integrability.

**7.5: derivative existence and positive shift.** The sequence is uniformly zero on the entire real line, not merely on compact sets. Each derivative is established by `HasDerivAt`; the conclusion about `deriv` at zero therefore cannot be a totalization artifact. The square-root denominator is positive by the `n+1` convention. The zero function's derivative is explicit and the sequence of derivatives at zero tends to positive infinity.

**7.6: both failures and native integrals.** Both source scalings are present, both functions are continuous and pointwise zero on the full closed interval, and both native Riemann integrabilities are proved. The exact coefficients include the extra `+2` in the denominator. A genuine primitive with interval-relative derivative is used in the native Chapter 6 FTC, then native scalar linearity supplies both integral identities. The squared scaling tends to infinity; the linear scaling tends to `1/2`. The zero limit is separately integrable with integral zero. No measure integral is substituted for the accepted Darboux integral.

All five source contracts retain their attached assertions. The proofs use existing library trigonometry, density, and powers, and the existing native Chapter 6 integral theory. These are explicit proof dependencies, not a claim of strict textbook-order development or completion of a later chapter. There is no circular use of the Chapter 7 uniform-integral theorem to establish these examples.

## Ten fresh hostile probes

The standalone client establishes:

1. At the negative-cosine point (`m=0`, `x=1`), every positive even power in 7.4 is exactly one.
2. The negative rational `-1/2` lies in the second factorial grid, has indicator value one, and has the asserted actual outer limit.
3. The irrational point `sqrt 2` has indicator value zero and actual grid-limit value zero.
4. The indicator is discontinuous at every chosen point while remaining natively integrable on that singleton with integral zero. This tests the necessity of `a<b` in the nonintegrability statement.
5. An explicit repeated-point partition `[0,0,1]` still has lower sum zero and upper sum one; a zero-width cell cannot erase the gap.
6. The zero-index geometric term at one is one, the sum at zero is zero, and the ordered series at one sums to two.
7. The first sine-example derivative at zero is one, testing the positive shift and actual derivative existence.
8. Both first spike integrals are exactly `1/4`, detecting indexing or factor errors.
9. The linear-spike integral sequence cannot tend to zero, using uniqueness against its actual limit `1/2`; the finite failure of interchange is substantive.
10. Both directions of the double-ratio inner-limit assertions and the inequality of their values are accessible together from the actual principal theorem.

Initial client elaboration adjustments were limited to reducing numeric expressions, making a repeated-partition equality definitional, and replacing a deprecated conditional tactic. These were probe repairs, not source changes. The final client contains no placeholder and emits no warnings.

No reviewed module, production/protected file, Git state, session, configuration, or credential was changed. This report assesses only 7.2–7.6. The singleton probe calls an existing Chapter 6 helper I previously authored; it is a boundary test of the reviewed interval claim, not an assertion that this report independently reviews that Chapter 6 helper.
