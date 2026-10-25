# Independent final Fourier source review

Reviewer: the inventory/bridge agent, independently of the Fourier-convergence proof author. Source: authorized local PMA third-edition PDF, printed pp.188–192 (PDF pp.199–203), with fresh direct reading of pp.189–190. Scope of this acceptance: numbered discussion 8.13, theorem 8.14 and both attached localization formulations, and the relation of 8.16 to their native integral conventions. Definition/examples 8.9–8.10 have a separate independent review.

## 8.13

Accepted. `pma8_13_contract` retains native complex Riemann integrability over one period and period 2π. Its Fourier sums use exactly the symmetric integer range −N through N and coefficient factor 1/(2π). The norm-square equality and finite bound have the same normalization. `fourier_error_identity` additionally supplies the exact finite mean-square remainder identity and proves native integrability of that remainder.

The Dirichlet kernel is the finite exponential sum; its sine quotient is asserted precisely where the denominator is nonzero. The supporting denominator-free identity handles the removable points correctly. Both convolution forms use the existing Chapter06 complex Riemann integral, and each integrand is proved natively integrable. Neither formula is accepted on the basis of a library integral alone. `periodic_riemann_integrable_every_interval` supplies the source's ordinary Riemann integrability on every bounded ordered interval; `periodic_riemann_integral_one_period` supplies independence of the starting point of a full-period integral. The generic partition transport underlying these facts is reviewed separately in `research/ch08-riemann-periodic-review.md`.

## 8.14 and its corollaries

Accepted. The only regularity premise is the printed local bound relative to the specified point: norm(f(x+t)−f(x)) ≤ M|t| for |t|<δ with δ>0. There is no global Lipschitz, continuity, differentiability, or extra measurable-function hypothesis. Native Riemann integrability and periodicity are the chapter's standing assumptions, retained in the principal contract.

The bounded sine quotient has its measurability and integrability proved from those assumptions; no unproved integral-existence assumption is used. The proof's use of the library Riemann–Lebesgue theorem is legitimate through the established general native integral bridge. The oscillation frequency is N+1/2, and the conclusion converges to the actual point value f(x), not merely a representative almost everywhere.

`fourier_localization` preserves arbitrary native Riemann-integrable periodic f and g and assumes only equality in some neighborhood of x. It proves the difference of their Fourier sums tends to zero. `fourier_tendsto_zero_on_open_interval` separately gives the printed zero-on-a-segment corollary at every interior point. No attached localization conclusion is omitted.

## 8.16 consistency

The Parseval implementation uses the same native Fourier coefficients and symmetric partial sums. Its mean-square limit, conjugated coefficient pairing, and norm-square identity have factor 1/(2π), with integrability included rather than inferred from totalized integrals. The source's arbitrary Riemann-integrable scope is preserved by the general Darboux-to-Lebesgue bridge. The principal contract retains periodicity, even though some support results prove the stronger interval-local statement.

## Verdict and validation

No mathematical scope deviation was found in 8.13–8.16. The restriction on the displayed sine quotient only makes explicit its domain of definition. Source-supported definitions and all attached conclusions listed above are present. The separate 8.10–8.12 coefficient-integrability clarification must remain disclosed in the final chapter report; it is not needed as an added premise for the concrete trigonometric Fourier system here.

Final convergence build: `lake build Rudin.PMA.Chapter08.FourierConvergence` succeeded, 8953 jobs, with no warnings in the final log `evidence/fourier-convergence-build.log`. Focused 8.13–8.15/support axiom output in `evidence/fourier-axiom-audit.log` lists only `propext`, `Classical.choice`, and `Quot.sound`. The root's whole-chapter build and declaration audit remain the final integration checks.

Reviewed final files:

| File under `rudin/Rudin/PMA/Chapter08/` | SHA-256 |
|---|---|
| `Fourier.lean` | `e85ddb5d07e201b84b255361cdb2da5ee7e17b0d726e523e87044c0888db1cea` |
| `FourierConvergence.lean` | `2f2676c0d96a46f24c1a773a044975bb4a35b9ff50ba7b4035af73ee7bd77284` |
| `RiemannPeriodic.lean` | `fdce0cc68a3bb6656b906326f25e3660ad512595cfe0f56bdf91d91088dd823c` |
| `FourierParseval.lean` | `b2e9f97064fbaf7f14f7b889cca162efe3a47496c135c5560a599f56970cb674` |
| `FourierParsevalBase.lean` | `e956802dd805f0a876ae9a2626bc055991febfd3bb3f2afb6639f5160f4196db` |
| `RiemannBridge.lean` | `30f397d3f5ad272a0529e0ab522656a58b0236b2ed062e91c4659c670fe29243` |
