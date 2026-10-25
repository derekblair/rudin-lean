# Independent source-fidelity review: PMA 9.42–9.43

Reviewer: determinants subagent, independent of the authorship of Integrals.lean.
Source: PMA third edition, printed pages236–238, read from the local PDF.

Reviewed source SHA-256:
`d8fdf7492f06244eeb62008a222d1d91ab45b4e344e2e07a9c3fc17eab3e5728`.

## PMA 9.42

The theorem uses the repository's native Riemann–Stieltjes integrability and
integral, with the original increasing integrator and parameter interval. It
concludes both integrability of the parameter derivative and an actual derivative
of the parameter integral, with the integral of that derivative as its value.

The explicit `hD` assumption records existence and values of the derivatives in
one neighborhood of s; `hU` records their uniform continuity at s in the parameter.
Together these express the existence implicit in the printed derivative notation
and the printed uniform condition. The neighborhood can be shrunk inside(c,d),
so the global Lean function representation adds no boundary requirement. No
continuity in the integration variable or uniform differentiability beyond the
printed condition is assumed. The auxiliary filter-limit theorems preserve the
native integral, rather than silently replacing it by a measure integral.

No substantive fidelity defect found.

## PMA 9.43

The two integrands, their signs, and the evaluation scale match the source.
The formalization establishes:

- absolute integrability of both integrands;
- the cosine difference-quotient estimate with the stated zero-increment convention;
- differentiation of the first integral to obtain the second;
- the differential equation, Gaussian closed form, and initial value;
- the divided integration-by-parts identity for a nonzero parameter;
- symmetric improper interval limits agreeing with the full-line integrals.

The use of Bochner integrals is explicitly identified in source, with actual
improper-limit theorems and absolute-integrability proofs. It is an equivalent
representation for these continuous absolutely integrable integrands.
The parameter restriction t≠0 in the divided identity is a necessary clarification
of the printed formula; the zero value is covered separately. This restriction
is documented at the theorem and must be listed in the final report.

No narrowed scope in the principal derivative, differential equation, or
closed-form theorem: all are proved for every real parameter.

## Verification boundary

This review concerns mathematical statements and their correspondence with the
printed source. The author reports the target and recursive audit build passing;
the integrating agent will run the final complete-module build and axiom audit.
