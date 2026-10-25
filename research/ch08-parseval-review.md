# Independent Parseval source review

The integrating agent read `FourierParsevalBase.lean` and
`FourierParseval.lean` independently of their author and compared the contracts
with PMA 8.16, printed pp.191–192.

The main theorem retains complex Riemann-integrable periodic functions and
the normalization `1/(2*pi)`. It proves integrability of every remainder
square, convergence of its normalized native integral to zero, the mixed
integral formula with conjugation on the second function/coefficient, and
the norm-square formula. The source's symmetric integer partial sums are
explicit limits. Supporting unconditional sums are stronger conclusions,
not stronger hypotheses.

The circle-to-interval bridge keeps the same normalized Haar measure and
unscaled real coordinate. Native bounded Riemann-integrable functions are
proved to lie in L2; L2 membership is not assumed in the source-facing theorem.
The finite remainder identity uses the native integral algebra and Fourier
Gram matrix with diagonal `2*pi`. This also supplies the finite identity
attached to 8.13.

Verdict: the full 8.16 statement and its printed consequences are represented;
no continuity substitution, omitted conjugate, weakened convergence, or changed
normalization was found. Compilation is separately recorded in
`evidence/ch08-parseval-build.log`; the combined recursive audit is the final
kernel dependency gate.
