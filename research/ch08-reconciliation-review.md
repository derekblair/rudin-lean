# Chapter 8 reconciliation and source review — 2026-10-24

The remote branch `origin/ch8-codex-20261022` contains previously unmerged
Chapter 8 work from commits `b7adfb3` and `ddee601`; its later Chapter 9–10
work is outside this lane. The eight imported Chapter 8 source/probe files
are byte-identical to that candidate. Exact hashes and prior provenance are
recorded in `evidence/ch08-reconciliation.json`. The two landed supporting
modules from merged PRs 1 and 2 are preserved. The new compatibility module
connects their coefficient-left convention and original convergence premises
to the recovered all-orders development.

All Chapter 1–7 source files, the toolchain, and dependency pins agree between
the recovered branch and this lane. No files in those scopes were imported or
changed. The recovered chapter-only build passed with 8953 jobs; its complete
log is `evidence/ch08-reconciled-build.log`. The chapter index and recursive
audit remain separate current-lane gates.

The prior reviews and manifest are stored with the `ch08-prior-` prefix. They
record earlier acceptance and builds, and are retained as historical evidence.
They do not certify the current combined chapter.

## Fresh source comparison of recovered 8.1–8.6

The current comparison read the printed statements and attached development
on pp.172–182 from the local third-edition source
`/home/derekblair/projects/math/tasks/rudin-review-20261024/source-evidence/baby_Rudin.pdf`
(PDF pages 183–193). The full prior 22-node inventory is retained with an
explicit provenance header in `ch08-complete-inventory.md`. No extended book
text has been stored.

- 8.1: real-variable complex-coefficient ordered series, every smaller compact
  interval, continuity and every derivative order, factorial coefficient values,
  coefficient uniqueness, and the smooth/nonanalytic warning are represented.
  Ascending factorials with shifted indices express the source's falling
  factorial coefficients. The extended radius includes infinity.
- 8.2: endpoint convergence can be conditional; both signed endpoints and the
  attached convergent Cauchy-product consequence are covered. The endpoint
  extension uses the actual ordered sum rather than an undefined unordered sum.
- 8.3: the source's norm-row hypotheses yield all inner sums and both outer
  sums. Naturals are explicitly identified with source indices shifted by one.
- 8.4: recentering allows any interior point and uses actual iterated derivatives;
  the reduced radius is a guaranteed domain, with no exact-radius claim.
- 8.5: the accumulation point may be any interior point. Deleting that point
  from the equality set before closure prevents isolated equality from sufficing.
- 8.6: the factorial series identifies the complex exponential; all six real
  clauses and attached logarithm/real-power development are present. The
  logarithm and power integrals use native Chapter 6 integration and explicitly
  handle reversed endpoints and the exceptional exponent minus one.

No narrowed mathematical scope or repaired false printed claim was found in
these six recovered node contracts. The shifted index conventions, extended
radius, explicit endpoint extension, and native integral orientation are
representation choices stated in the source comments. Pinned Mathlib results
supply analytic, exponential and asymptotic facts without claiming book-order
proof derivations. The new compatibility bridge is current authored work and
is subject to the current lane's build and audit.
