# Independent review: PMA 6.9

Reviewer: `completion_evidence`, independently reviewing the parent's implementation. Date: 2026-10-10. Outcome: **accepted**.

Reviewed file: `rudin/Chapter06MonotoneDraft.lean`.

SHA256: `93a69abdd3e242baa92eace347b551042157da49b4a83078e06abd469d832598`.

## Contract fidelity

The imported `pma6_9_contract` in `Rudin/PMA/Chapter06/Integrability.lean:17` explicitly covers both `MonotoneOn f (Icc a b)` and `AntitoneOn f (Icc a b)`, with `a≤b`, a nondecreasing integrator on the source interval, and relative closed-interval continuity of the integrator. Its conclusion is the native `RSIntegrable`, including source boundedness and the actual equality of lower/upper Darboux integrals. It does not replace the integrator by a right-continuous representative or require the integrand to be continuous.

## Complete proof review

- Lines 8–17 derive boundedness from the two endpoint values; no boundedness hypothesis is silently substituted for an existence conclusion.
- Lines 19–41 prove the actual infimum and supremum of a monotone function on each **closed** partition cell equal its endpoint values. Nonempty cells and bounded images justify the conditional-completeness operations, including repeated-point cells.
- Lines 43–52 prove the exact gap symmetry: both gaps are the sum of `(f(right)-f(left)) * (α(right)-α(left))`, in opposite factor orders.
- Lines 54–62 apply continuous-integrand integrability to `α` with `f` as its nondecreasing integrator, then transfer the small-gap criterion using the proved symmetry. This is a valid reuse of 6.8 and 6.6, not an assumption of 6.9.
- Lines 64–72 handle antitone functions by proving `-f` monotone and using the previously proved native scalar-integrability theorem at `-1`.
- The final wrapper selects the two source branches. Endpoint and degenerate intervals remain included. All hypotheses stay on the source interval.

No fidelity, circularity, or proof-validity findings remain.

## Independent verification

`./lake-local env lean Chapter06MonotoneDraft.lean` completed with exit zero and no warnings or errors. Separate transitive axiom checks passed for all seven declarations in the draft: each uses only `propext`, `Classical.choice`, and `Quot.sound`. Production integration and the final chapter audit remain the parent's responsibility.
