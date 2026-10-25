# Native Riemann integration bridge — 2026-10-24

`Chapter08/RiemannBridge.lean` proves that the existing Chapter 6 real and
complex Riemann integrability predicates imply library interval integrability,
and that the native integrals equal the library interval integrals. There is
no continuity, Borel measurability, or almost-everywhere measurability premise.
The native predicates already contain boundedness and ordered endpoints; these
are used without changing their scope. Equal endpoints and repeated partition
points remain permitted.

For each native partition, a finite measurable step function uses half-open
cells `(x_i,x_{i+1}]`. Their disjointness and coverage are proved, including
zero-width cells. Its library integral is exactly the corresponding Darboux
sum. The existing Darboux criterion selects upper and lower step functions
with gaps less than `1/(n+1)`. Their countable infimum and supremum are measurable,
share an integrable compactly supported bound, and sandwich the original
function restricted to `(a,b]`. Monotonicity of integration forces the envelope
integrals to agree; the envelopes are therefore equal almost everywhere.
This proves integrability of the original function without presupposing it.
Finally every partition's lower and upper sums bound its library integral;
the native supremum/infimum characterization identifies the two integrals.

Complex functions are handled through their real and imaginary parts, exactly
as in the native Chapter 6 definition. Native boundedness also yields membership
in every `Lp` space on the finite interval, including essential boundedness.

Targeted validation: `lake build Rudin.PMA.Chapter08.RiemannBridge` succeeded
with `Build completed successfully (8945 jobs).` The complete output is in
`evidence/ch08-riemann-bridge-build.log`. Recursive axiom auditing belongs to
the combined Chapter 8 audit. No earlier-chapter source file was modified.
