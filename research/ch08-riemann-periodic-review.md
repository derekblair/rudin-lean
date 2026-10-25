# Native periodic Riemann transport

Reviewed source: PMA 3rd ed., printed pages 188–190, especially the periodic interval observation attached to 8.13 and both convolution forms (78).

`RiemannPeriodic.lean` proves native ordinary Riemann integrability of a periodic function on every ordered compact interval from integrability on one period. It also proves native integrability after reflection and translation. The complex versions apply the real argument separately to real and imaginary parts.

The affine transport proofs construct translated/reversed Chapter06 partitions, identify each closed cell image exactly, and show both Darboux sums are unchanged. The native Darboux gap criterion therefore transfers integrability directly. Periodic extension first concatenates finitely many translated periods, shifts these to symmetric intervals, then restricts to an arbitrary bounded interval. Zero-width cells and degenerate intervals are covered by the same argument.

No continuity, measurability, almost-everywhere modification, or extra integrability hypothesis is imposed. The bridge is strictly within Chapter08 and preserves the Chapter06 definitions. In particular, the reflected periodic convolution integrand in 8.13 can use the actual native integral, not merely a Lebesgue integral with an asserted correspondence.

Validation: `lake env lean Rudin/PMA/Chapter08/RiemannPeriodic.lean` exited 0 without diagnostics. `lake build Rudin.PMA.Chapter08.RiemannPeriodic` succeeded, 8946 jobs. Log: `evidence/ch08-riemann-periodic-build.log`.

Reviewed file SHA-256: `fdce0cc68a3bb6656b906326f25e3660ad512595cfe0f56bdf91d91088dd823c`.
