# Chapter 8 Gamma section completion

Implemented and kernel checked nodes **8.17–8.22**, including all five numbered
consequences in 8.21 and the Euler limit attached to 8.19.
Source: third-edition PDF at
`/home/derekblair/projects/math/references/sources/pma3.pdf`, printed pp.192–195.

- `Gamma.lean`: integral definition, convergence, native compact-truncation limits,
  recurrence, factorial values, logarithmic convexity, Bohr–Mollerup uniqueness,
  Euler limit, beta integral and native two-endpoint improper limit. Generic
  continuous native/library integral equality is proved by FTC. Generic improper
  limits use native Chapter 6 compact integrals and permit independent endpoints.
- `GammaConsequences.lean`: trigonometric beta substitution with integrability,
  gamma at one half, square substitution with integrability, full Gaussian
  integral, duplication formula. Native improper-limit corollaries are provided
  for the three integral consequences.
- `GammaStirling.lean`: full real-argument Stirling limit plus factorial
  specialization. This is not a restriction to natural arguments. New proof
  extends the pinned library factorial limit by logarithmic convexity, a uniform
  mean-value estimate on each unit interval, and the floor limit.
- `GammaAudit.lean`: six contract comparisons and recursive namespace axiom gate.

## Validation

`lake build Rudin.PMA.Chapter08.GammaConsequences Rudin.PMA.Chapter08.GammaStirling`
exited 0: **Build completed successfully (8933 jobs).**
Log: `evidence/ch08-gamma-build.log`.

`lake build Rudin.PMA.Chapter08.GammaAudit` exited 0:
**Build completed successfully (8937 jobs).** The recursive gate checked **65
Chapter08 declarations**, including generated/private declarations, with only
`propext`, `Classical.choice`, and `Quot.sound`.
Log: `evidence/ch08-gamma-audit.log`.

Source scan found no proof holes, added axioms, or native-decision proof bypass.

## Conventions and deviations

No positive-real domain is narrowed and no mathematical premise is strengthened.
Lean uses total functions for the integral-defined gamma and real powers; every
source identity restricts gamma arguments to positive reals (or positive integer
shifts), and the real asymptotic is unaffected by values elsewhere. The improper
integral is constructed with the library Lebesgue integral, with integrability
proved and explicit native compact-truncation convergence. Thus this convention
does not replace the source integral by an unbridged totalized value.
The factorial formula also covers n=0, a valid additional case.

Separate independent review records cover 8.7–8.8 and 8.11–8.12.
No shared chapter index, PROGRESS, README, or Git history was modified by this agent.
