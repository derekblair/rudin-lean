# Independent source review: normalized exponential example

Reviewer: the Fourier convergence author, who did not author
`FourierExponentialExample.lean`.

Source: PMA third edition, printed pp.186–187, especially the example attached
to 8.10. The source was read directly from the local third-edition PDF during
the Fourier inventory.

Reviewed SHA256 of `rudin/Rudin/PMA/Chapter08/FourierExponentialExample.lean`:
`3232066269a76ca391e5be61ff0750553abc65a0bdd83beef4d78162d60649d0`.

`normalizedFourier n x` is exactly the integer-frequency exponential divided
by the positive square root of `2*pi`. The Gram theorem uses the native complex
Riemann integral on `[-pi,pi]`, proves existence of every displayed integral,
and has value one exactly on the diagonal and zero off it. The normalization
is checked through the square-root identity and nonvanishing of `2*pi`.

The natural-indexed system uses an equivalence with all integers. Injectivity
is used for off-diagonal orthogonality, and
`normalizedFourierSystem_all_frequencies` explicitly proves that every integer
frequency occurs. Thus this is the full printed system, not a one-sided or
finite subset. The change from one-based to zero-based sequence indexing
does not change the represented family.

Verdict: accepted for the normalized complex-exponential example of 8.10,
with no strengthened mathematical premise or missing frequency. This verdict
does not cover the separately authored real sine/cosine example.

Inspected compiler evidence: `evidence/ch08-exponential-example-build.log`
reports successful construction of this module (8952 jobs). The final chapter
namespace audit and integration build remain the integrating agent's gates.
