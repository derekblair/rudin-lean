# Chapter 8 local production review — 2026-10-22

## Accepted scope

This lane completes **6/22 numbered nodes, PMA-8.1 through PMA-8.6**, plus the
requested unnumbered power-series operations. It does not complete Chapter 8.
The brief's numeric topic ranges differ from the third edition: power series are
8.1–8.5; exponential/logarithmic functions and attached real-power development
are 8.6. The full source inventory and discrepancy are documented independently
in `pma-ch08-source-review.md` and `pma-ch08-inventory.md`.

| Node | Principal theorem | Implementation and accepted content |
|---|---|---|
| 8.1 | `pma8_1` | `PowerSeries.lean`: ordered complex power series of a real argument, finite/infinite radius, local uniform convergence, continuity, all derivatives and factorial coefficients, uniqueness, smooth nonanalytic warning |
| 8.2 | `pma8_2` | `Abel.lean`: conditional endpoint convergence, interior sums, limits and endpoint continuity at either signed endpoint, attached conditional Cauchy-product consequence |
| 8.3 | `pma8_3` | `DoubleSeries.lean`: explicit existence of both iterated sums from ordered norm-row sums and their convergent outer series |
| 8.4 | `pma8_4` | `Taylor.lean`: recentering at any interior point, actual derivative coefficients, guaranteed radius including infinity |
| 8.5 | `pma8_5` | `Taylor.lean`: identity from accumulation anywhere inside the interval, equality of all coefficients and represented values |
| 8.6 | `pma8_6` | `Exponential.lean`: complex factorial series/algebra, six real exponential properties, Euler-number bridge, inverse logarithm, native oriented integrals, rational/supremum power conventions, derivatives, integrals and growth |

`Operations.lean` supplies addition, native Chapter 3 Cauchy multiplication,
and native Chapter 6/7 termwise complex Riemann–Stieltjes integration with
explicit integrated coefficients. It imposes no continuity assumption on a
monotone integrator and includes singleton intervals. No numbered nodes were
invented for these supplements. Explicit Mathlib analytic/Abel/asymptotic
results are library dependencies, not later-chapter completion claims.

## Independent review

The independent source/contract reviewer authored no production proofs and
provided all 16 client theorem statements/proofs. Actual third-edition source
scope and every contract were checked, including every final compilation delta.
`evidence/ch08-contract-independent-review.md` records acceptance and exact
hashes; `ch08-final-independent-review.md` reconciles final inclusion.

Adversarial reviewers were independent of the modules they reviewed:
`ch08-foundation-hostile-review.md`, `ch08-calculus-hostile-review.md`, and
`ch08-exponential-hostile-review.md`. The only advisory requested an explicit
negative-endpoint Abel bridge. That bridge was added, compiled, reviewed and
included in the principal contract; the advisory is closed.

## Kernel and source gates

- The first section's fresh audit checks 5 principal theorem declarations and
  contract type comparisons, then 74 namespace declarations, including the
  13-declaration subset supporting its 11 independent clients.
- The final fresh audit checks all 6 actual principal theorem declarations,
  6 contract type comparisons, and **103 namespace declarations**. Its
  **18-declaration probe subset** includes all **16 independent client theorems**
  and their support/generated declarations. Only `propext`, `Classical.choice`,
  and `Quot.sound` occur recursively.
- Both default `lake build` invocations passed before their respective local
  section commits. New Chapter 8 modules and the new audit were compiled in
  this checkout. Replayed unchanged older audits are labeled as replayed by Lake.
- Chapter 8 source/metadata checks pass at 6/22 with zero queued nodes. A separate
  code-only scan of all 11 Chapter 8/integration Lean files finds no `sorry`,
  `admit`, `native_decide`, `sorryAx`, `axiom`, or `unsafe` tokens. The historical
  diagnostic logs retain failed and interrupted attempts; they are not completion
  evidence. No error-recovery axiom occurs in the final recursive audit.
- All 47 Chapter 1–7 Lean files and the toolchain/dependency pins are unchanged
  from base `53968a9d10eae55484894602b5d8adaf3960b88b`. Their source/metadata
  checks also pass.

Final evidence is `evidence/ch08-final-audit.log`,
`ch08-final-default-build.log`, `ch08-source-checks-final.log`, and the exact
11-file `ch08-final-manifest.json`. First-section evidence is the corresponding
`ch08-foundation-*` set. Probe compilation is recorded in
`ch08-foundation-probes-final.log` and `ch08-exponentialprobes-final.log`.

## Reproducibility and resource handling

Lean 4.34.1 and the existing Mathlib pin are unchanged. The initially absent
precompiled cache was fetched with the brief-authorized `lake exe cache get`.
No software was installed. Shared host memory pressure required serialized
local module builds; `scripts/build_sequential.py` primes local modules in
import order before the default build. No other lane's process was stopped.

The generated build artifacts of 47 byte-identical older modules were reused
from a local prior audit with matching toolchain/dependency pins; provenance and
hashes are in `evidence/ch08-prior-build-cache.json`. This is not a claim that
all older modules were freshly elaborated in this lane. Every new Chapter 8
module and audit was freshly compiled.

Temporary sharing of byte-identical generated dependency-cache files reduced
duplicate paging. Only this checkout's generated cache was modified; the other
lane was read-only. All 115,871 temporary links were restored to regular files with their
original SHA-256 hashes; `evidence/ch08-cache-restoration.json` records the
result. The delivered checkout has no remaining temporary cache-sharing links.

## Pending work and handoff

PMA-8.7–8.22 remain unattempted and pending, covering trigonometry, the
fundamental theorem of algebra, Fourier material, gamma/beta and Stirling.
There are no needs-insight entries because every attempted numbered node was
completed. The source inventory identifies all remaining scope without adding
proof placeholders.

Local branch: `ch8-codex-20261022`. The first section commit is
`b7adfb383619080760be780e7adf8a883b618770`. The commit containing this report adds
the 8.6 continuation. The task-directory `CH8-LOG.md` records the exact complete
commit list. No push, pull request, merge, or other-branch edit was performed.
