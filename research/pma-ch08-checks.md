# Chapter 8 verification

This lane follows Rudin's actual numbered nodes: power series 8.1–8.5, then exponential/logarithm and attached real-power material 8.6. The full chapter inventory has 22 nodes; 8.7–8.22 are later topic work. See `pma-ch08-source-review.md` for the source/brief discrepancy and full scope.

## Statement and dependency discipline

The public power-series interface uses real arguments, complex coefficients, ordered Chapter 3 partial-sum limits, and an extended nonnegative radius (including infinity). `realSeries_term_reference` explicitly identifies real scalar action with the coefficient-left convention in Chapter 3. The analytic representation is proved from ordinary convergence, so no absolute-convergence premise is silently added. Abel's endpoint theorem explicitly permits conditional convergence and includes both positive and negative convergent endpoints with their correct one-sided limits. Independent clients include the alternating harmonic series as an actual conditional endpoint.

Pinned Mathlib provides analytic power-series differentiation, recentering, the analytic identity theorem, Abel's theorem, product summation, exponential/logarithmic calculus, and a smooth nonanalytic witness. These are explicit library dependencies; using them does not claim completion of later book chapters. The 8.2 Cauchy-product application reuses PMA 3.51, which already disclosed its forward library use of Abel's theorem.

Addition and multiplication are supplemental lemmas with the native Chapter 3 Cauchy product. Termwise integration uses the native Chapter 6 complex Riemann–Stieltjes integral and Chapter 7 uniform integration theorem; the ordinary-integral specialization includes the explicit monomial primitive and degenerate intervals. Logarithm and real-power integrals use native real Chapter 6 integration with an explicit orientation wrapper. They are not replacements by measure integrals.

## Environment and preserved chapters

Toolchain: Lean 4.34.1; Mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612`. The absent cache was fetched using the authorized `lake exe cache get`. No package installation or pin change.

A default baseline rebuild was interrupted under shared-memory pressure; a subsequent sequential baseline run was also stopped to address duplicate generated-library paging. Identical generated Mathlib/dependency cache files were temporarily shared with the other local lane after SHA-256 equality checks (manifest in the task directory). Only this checkout's cache paths were changed.

A previous local audit build was then located. Its 47 Chapter 1–7 source modules match this checkout byte for byte, and both toolchain/dependency pins match. Their generated artifacts were copied into this checkout; `evidence/ch08-prior-build-cache.json` records source and artifact hashes. The Chapter 8 modules and audit are freshly compiled. Replayed output from unchanged earlier audits is distinguished from the fresh Chapter 8 audit.

`python3 scripts/build_sequential.py` primes local modules in dependency order with one compiler, then runs the default `lake build`. All build invocations in this lane are sequential.

## Independent review and probes

The inventory and typed contracts were independently reviewed against the local third-edition source. See `evidence/ch08-contract-independent-review.md` and `evidence/ch08-double-series-independent-review.md`. Boundary clients are authored independently in `Chapter08Probes.lean` and `Chapter08/ExponentialProbes.lean`.

The first section audit verifies 5 actual principal theorems and 5 accepted-contract type comparisons. It recursively checks 74 declarations in `Rudin.PMA.Chapter08`, including the 13-declaration probe subset, and admits only `propext`, `Classical.choice`, and `Quot.sound`. All 11 independently authored foundation clients compile, including imaginary-valued native integration and a singleton termwise integral. The signed negative-endpoint addition closes the adversarial review advisory explicitly.

Evidence: `evidence/ch08-foundation-probes-final.log`, `ch08-foundation-audit.log`, `ch08-foundation-default-build.log`, `ch08-source-checks-foundation.log`, and exact source hashes in `ch08-foundation-manifest.json`. The default build passed before the first section commit. Earlier `*-compile*.log` and baseline logs retain the failed/interrupted diagnostic attempts; only the named final logs constitute completion evidence. Independent hostile reviews are `ch08-foundation-hostile-review.md` and `ch08-calculus-hostile-review.md`.

The first section integrates 8.1–8.5 and the operations supplements. The separately authored exponential/logarithm candidate is reviewed and module-tested, but counts as completed only when imported and audited in the next section. The chapter remains partial.
