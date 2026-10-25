# Fourier definitions and orthonormal examples

Author: gamma subagent, 2026-10-24.
Source: PMA third edition, printed pp.185–187 (PDF pp.194–196).

`FourierDefinitions.lean` implements the remaining development at 8.9–8.10:
finite support is equivalent to a symmetric integer interval; both directions of
the complex sine/cosine representation; reality exactly when coefficients have
conjugate symmetry; and the complete real orthonormal sequence in the printed
order. The principal `pma8_9` and `pma8_10` contracts also collect the native
coefficient/integral formulas and the complex exponential example supplied by
`FourierExponentialExample.lean`. Fourier-series predicates assert coefficient
identities and existence of the relevant integrals, with no convergence assertion.
The relative-series predicate also requires an orthonormal family, matching the
printed scope.

The real system is built using paired exponential terms. A native finite Gram
formula proves all cross terms and normalizations, including the constant term.
Explicit formulas identify indices 0, 2n+1, and 2n+2 with the constant, cosine,
and sine; no positive frequency is omitted. Natural indices start at zero, as
documented in the shared base definitions. This is only a reindexing convention.
No mathematical hypotheses or conclusions were weakened.

Validation: `lake env lean Rudin/PMA/Chapter08/FourierDefinitions.lean` exited 0
with no warnings. `lake build Rudin.PMA.Chapter08.FourierDefinitions` exited 0;
see `evidence/ch08-fourier-definitions-build.log`. Source scan found no proof
holes, added axioms, or native-decision proof bypass.

SHA-256:
`838556f9c93699b817ac8e30457f13bab19c889cf79f0fb91e29b56a9869561b`.
Independent source review is delegated to the Fourier agent.
