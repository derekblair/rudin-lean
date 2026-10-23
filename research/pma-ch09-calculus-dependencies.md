# Chapter 9 calculus implementation dependencies

The independent third-edition inventory fixes the mathematical contracts. This
note records implementation choices; it is not a passing-build claim.

- **9.10–9.20:** `HasTotalDerivative` is the explicit normalized Euclidean
  remainder limit. `hasTotalDerivative_iff` connects it to Mathlib's real
  Fréchet derivative. `C1On` means pointwise differentiability plus continuity
  of the operator derivative and is connected to `ContDiffOn ℝ 1` on open sets.
  Coordinate partials use actual one-variable `HasDerivAt`; the source warnings
  use `x₀*x₁/‖x‖²` and `x₀*x₁/‖x‖`, with partial existence at every point proved
  separately from continuity or total differentiability.
- **9.39–9.41:** the unequal-mixed-partial witness is the classical Peano
  rational example. The rectangle theorem uses two one-variable mean value
  theorems, including signed increments. The principal symmetry proof bounds a
  rectangular increment, then uses `norm_deriv_le_of_lip'` to derive the
  previously missing mixed derivative from continuity of the other mixed
  derivative at the one point. The arbitrary-dimensional `C²` corollary
  restricts to affine coordinate planes. It does not replace the principal
  theorem by a `ContDiff 2` theorem.
- **9.42:** the native Chapter 7 real Riemann–Stieltjes uniform-limit proof is
  generalized from a sequence to an arbitrary nontrivial filter with eventual
  integrability. A mean-value estimate gives uniform convergence of parameter
  difference quotients. The native integral theorem retains arbitrary
  monotone integrators, including discontinuous integrators, and singleton
  intervals. Compact continuity of the derivative is a separate sufficient
  condition; it is not imposed on the principal statement.
- **9.43:** Mathlib supplies the dominated parameter-integral derivative and
  `fourierIntegral_gaussian`. These are explicit forward library dependencies,
  including the Gaussian normalization referenced by Rudin as Chapter 8.21.
  The implementation proves a native continuous-Riemann/interval-integral
  bridge by applying both fundamental theorems to the same primitive. It then
  proves the two-endpoint improper limits of the native oriented integrals,
  local native integrability on every compact interval, and absolute improper
  convergence. Thus the complex Gaussian library identity is not the entire
  source contract and no totalized-integral identity substitutes for existence.

All library references refer to the checkout's pinned Mathlib revision, not a
floating online version. Compile logs, independent semantic acceptance, edge
clients, and the recursive axiom audit are separate evidence gates owned by the
root integration process.
