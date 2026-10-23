# Independent adversarial review of exponential development

Reviewer: `double_series`, 2026-10-22. The reviewer did not author
Exponential.lean or ExponentialProbes.lean. This review read both complete
files, the actual four development predicates and `pma8_6_contract`, the
independent source inventory, and the Chapter 1 positive-root and Chapter 6
native-integral definitions. No production file was edited and no build was
run by this reviewer.

| File relative to repository root | SHA256 |
| --- | --- |
| `rudin/Rudin/PMA/Chapter08/Exponential.lean` | `cd7d31f6d45786bc4433d3c0bb878c1e4e0c2da6f43bf48fc1491c6167768bcd` |
| `rudin/Rudin/PMA/Chapter08/ExponentialProbes.lean` | `50cfdadd939ba80e57fd93e47bad71d05cc49eb97664485e428ee8cc2b6cc9da` |

**Verdict: ACCEPTED.** No source-fidelity, domain, orientation, exceptional-case,
vacuity or circularity defect was found in the reviewed exponential/logarithmic
development. This covers numbered 8.6 and the attached development identified
by the source inventory, not subsequent trigonometric or algebraic nodes.
The integrating lane's compile-2 logs for both modules record successful
builds; default inclusion and the recursive permitted-axiom audit remain
separate gates. Acceptance identifies the exact source bytes above.

## Exponential and logarithm

The complex exponential is explicitly identified by an everywhere-convergent
factorial series, with its constant term included. Thus the library function
is connected to the source definition rather than merely named similarly.
Addition, zero, nonvanishing, negation/reciprocal, actual complex derivative,
finite-sum/product identities and the real restriction are all present. The
empty finite sum and n=0 factorial term retain their correct values.

The real predicate supplies continuity, actual derivatives, strict increase,
positivity, addition, both infinite-end limits and polynomial-times-exponential
decay for every natural order, including zero. Its base is the already defined
Chapter 3 Euler number, explicitly equated with exp 1. No independent or
unidentified constant called e has been introduced.

Logarithm has both inverse identities with the required positive-input guard
for exp(log x). Strict monotonicity, derivative and product conversion are
restricted to the positive domain. The limits are at positive infinity and
at zero from the right. Values of Mathlib's globally defined logarithm at
nonpositive arguments are not promoted to source claims.

## Rational powers and the supremum convention

The rational-root statement includes positivity of the result and uses the
actual signed integer numerator `q.num`, not a truncation to a natural. Its
denominator is the rational's nonzero natural denominator. For negative q,
the right side is the integer negative power and therefore the expected
reciprocal. For q=0, the statement still selects the positive unit value.
Together with the existing uniqueness of a positive nth root, this identifies
the source's rational-power convention without choosing an even negative
root. The independent client tests q=-1/2 at base 4.

The supremum statement quantifies all rational q<x, including negative q and
negative x. Its set is proved nonempty, and the least-upper-bound argument
uses rational density; it is not an equality of default suprema of possibly
empty or unbounded sets. The premise b>1 is the correct direction for an
increasing rational-power supremum. The proof establishes monotonicity on the
set and continuity at its supremum, thereby proving the full `IsLUB` property.
The Euler-base instance is explicitly included in the real exponential
predicate. Agreement with real/integer powers and the exp(alpha log x)
formula is separately present, so the supremum assertion is not standing in
for the rational-root identification.

## Native integrals and difficult boundaries

`RIntegrable` and `RIntegral` are the Chapter 6 identity-integrator aliases of
the native Riemann-Stieltjes definitions. `orientedRIntegral` selects that
integral on an ordered interval and negates the reversed native integral.
No Lebesgue integral or unexplained integral notation replaces the native
theory. Positive compact intervals have explicit native integrability proofs.

The primitive theorem treats a<b, a=b and b<a separately. The first and third
cases invoke the native fundamental theorem with valid positive endpoints;
the reversed case changes the sign. The equality case uses the established
singleton native integral, so zero-length intervals do not rely on an invalid
strict-interval FTC application. The resulting logarithmic formula covers
both x>1 and 0<x<1 when integrating from 1. The independent reverse-interval
client has the nonzero negative value -1.

For alpha≠-1, the proof derives alpha+1≠0 before cancelling the denominator
of the actual derivative of t^(alpha+1)/(alpha+1). All bases and both
integration endpoints are positive. Negative nonexceptional exponents are
therefore covered without crossing zero. The exceptional exponent alpha=-1
has a separate logarithmic formula with no division by zero; the independent
client evaluates it on a nondegenerate interval. For a=b both displayed
antiderivative differences vanish, consistently with the native integral.

Finally, x^(-alpha) log x tends to zero only under alpha>0. Its proof performs
the reciprocal rewrite eventually on x>0, which is valid for the atTop
filter; it does not silently use a global positive-domain hypothesis or
assert the false alpha=0 version.
