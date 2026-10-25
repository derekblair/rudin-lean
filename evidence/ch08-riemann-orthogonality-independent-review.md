# Independent native integral and orthogonality review

Reviewer: gamma sub-agent (not an author of these modules), 2026-10-25 UTC.
Files read in full: `rudin/Rudin/PMA/Chapter08/RiemannBridge.lean` and
`rudin/Rudin/PMA/Chapter08/Orthogonality.lean`.
Source checked: PMA third edition, printed pp.186–188, local reference PDF.

The Darboux bridge retains arbitrary native Riemann-integrable functions.
Integrability of the zero extension follows from measurable lower/upper step
functions, countable envelopes, vanishing integral gap, and almost-everywhere
equality. The conclusion is Lebesgue integrability; no continuity or additional
measurability assumption occurs. Half-open partition cells cover (a,b] uniquely,
so duplicate partition points and the omitted left endpoint are harmless.
Integral equality follows by squeezing between every lower/upper Darboux sum.
The coordinatewise complex and bounded-Lp consequences preserve this scope.

The 8.11 statement preserves arbitrary finite coefficients, mean-square minimality,
the exact equality iff all coefficients agree, the norm-square identity, and the
finite Bessel bound. The proof also establishes integrability of each error square.
The 8.12 statement proves actual summability of coefficient norm squares, the
infinite bound, and convergence of the complex coefficients to zero.
Zero-based indexing is equivalent to the source's positive indexing.

The explicit coefficient-integrability premise must be recorded in the final
report as a source clarification. The source introduces relative Fourier
coefficients by an integral and defines its series notation by those equations;
thus existence is implicit when it speaks of the Fourier series. Orthogonality
of pairwise products plus integrability of f alone does not imply existence of
these coefficient integrals. For example, multiplying every member of an
orthonormal system by a common nonintegrable modulus-one sign function preserves
all pairwise products. The implementation correctly states existence explicitly
and does not impose the stronger, unnecessary continuity or separate
integrability of the orthonormal functions. Relative to the source's meaningful
Fourier-series notation this is an explicit prerequisite, not a loss of its
well-defined cases; relative to a literal reading of only orthogonality and f
integrable it is an added premise. The node comment discloses it accurately.

Verdict: accepted with that disclosed source clarification. This is a source and
code review; independent kernel execution remains the chapter audit/build gate.
