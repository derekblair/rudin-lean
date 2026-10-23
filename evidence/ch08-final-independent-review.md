# Chapter 8 final independent inclusion and hash reconciliation

Reviewer: `ch8_fidelity`, 2026-10-22. Scope: the authorized lane's 8.1-8.6 and
requested unnumbered power-series operations. **Final source/inclusion verdict:
ACCEPTED.** All six production support modules exactly match their latest
independently accepted bytes. The final chapter index and audit include all six
numbered proofs, both independently authored client files and the operations
supplement. No public contract has been weakened. The chapter remains partial:
6 of 22 numbered nodes; 8.7-8.22 are pending.

The reviewer authored no production proof. The reviewer did author the separate
boundary clients, so the discussion of their compilation is compiler-evidence
inspection, not an independent review of their own implementation. No build or
git mutation was performed by this reviewer. Only this evidence file was written
in the final inclusion review.

## Exact final code identity

Paths are relative to the repository root. The six support hashes agree exactly
with `evidence/ch08-contract-independent-review.md` and its accepted deltas.

| File | SHA256 |
|---|---|
| `rudin/Rudin/PMA/Chapter08/PowerSeries.lean` | `af7669152ab11b348b454ccfacb37928c67be845b7428377bd29dfd6e6552518` |
| `rudin/Rudin/PMA/Chapter08/Abel.lean` | `2a7a23da0c64df9c38dff6975bd0f5e34f1a428a5d4fa86480c35b7498260239` |
| `rudin/Rudin/PMA/Chapter08/DoubleSeries.lean` | `7cb78d7c111d3be2a9bc0f5e67a02c0020e988ba39e24f67db050787aae57e7e` |
| `rudin/Rudin/PMA/Chapter08/Taylor.lean` | `9c666fab54b9e7a3a7b7ac073e5b9ca9a8a7d2d31e2ccb7a7be303af472c0347` |
| `rudin/Rudin/PMA/Chapter08/Operations.lean` | `2b4ce0759198e1a2c854a8398d7b285c5edd64de0d36fd19aa3ba824245ae07a` |
| `rudin/Rudin/PMA/Chapter08/Exponential.lean` | `cd7d31f6d45786bc4433d3c0bb878c1e4e0c2da6f43bf48fc1491c6167768bcd` |
| `rudin/Rudin/PMA/Chapter08Probes.lean` | `093390f7774efef783fc3e1d5d5e66d79ff5b0c42225a59f99db8d27a57d543c` |
| `rudin/Rudin/PMA/Chapter08/ExponentialProbes.lean` | `50cfdadd939ba80e57fd93e47bad71d05cc49eb97664485e428ee8cc2b6cc9da` |
| `rudin/Rudin/PMA/Chapter08.lean` | `91fab07f19c78091a6c20c26a55059173b894b9c7030e27c17b3fcb331776b27` |
| `rudin/Rudin/PMA/Chapter08Audit.lean` | `92273825f91c2a43f6d3af276cedc6cd6941c948380263108316dfe76f9ff315` |
| `rudin/Rudin.lean` | `966e82e25167fb7fa0327ae27238c5438eea3a901804fc2450bb9f922214a5ce` |

The foundation section is recorded by local commit `b7adfb3`, whose source
manifest matches the final foundation modules and opening clients. The final
index adds Exponential and the 8.6 marker; the final audit adds its comparator,
principal lookup and the exponential client import. Changes to these two
integration files were read in full and are consistent with adding exactly one
numbered node. The root import file still brings in both Chapter08 and its audit.

## Inclusion and audit wiring

`Chapter08.lean` imports PowerSeries, Abel, DoubleSeries, Taylor, Operations and
Exponential, and has exactly the 8.1-8.6 markers in book order. It explicitly says
that later numbered items remain pending. It contains no replacement theorem
statements or proof wrappers that could diverge from the accepted contracts.

`Chapter08Audit.lean` has `autoImplicit false`, six type comparisons against the
actual accepted `pma8_n_contract` declarations, and a six-name environment check
that requires each `pma8_n` to be a kernel theorem, rather than a definition of a
proposition. Its two namespace audit calls use the existing Chapter 1 recursive
`collectAxioms` gate, whose implementation was read: only `propext`,
`Classical.choice` and `Quot.sound` are allowed. The chapter namespace audit
includes its probe and contract-comparator subnamespaces; the explicit probe
audit is a subset check, not an additional disjoint declaration count.

`rudin/lakefile.toml` retains default target `Rudin`, and `Rudin.lean` imports the
chapter audit. The default build therefore includes the actual coverage and
recursive-axiom gates rather than merely documenting commands to run later.
The pinned Lean and Mathlib versions are unchanged.

## Kernel evidence inspected

- `evidence/ch08-foundation-probes-final.log`: all 11 independent foundation and
  operation client theorems compile, including a conditionally convergent Abel
  endpoint, a nonzero imaginary native integral and a singleton termwise integral.
- `evidence/ch08-exponentialprobes-final.log`: all five separate exponential
  clients compile, including reverse integration direction and exponent `-1`.
- `evidence/ch08-final-audit.log`: a fresh successful Chapter08 and Chapter08Audit
  build reports **6 actual principal theorems**, **6 contract type comparisons**,
  and **103 recursively audited Chapter08 declarations**, including the
  **18-declaration probe namespace subset**. Only the three permitted axioms occur.
  This is fresh Chapter 8 output, distinct from replayed earlier-chapter output.

The earlier foundation default build was inspected through the integrating
lane's preserved section evidence. The reviewer subsequently read the completed
`evidence/ch08-final-default-build.log`: the default `Rudin` target built
successfully with 8.6 included (8985 jobs), and its imported Chapter08 audit
reported the same six-principal, 103-declaration and 18-probe-subset results.
The final default build replays the freshly completed Chapter08 audit; the
separate final-audit log above establishes that audit's fresh compilation.
`evidence/ch08-source-checks-final.log` also passes the 6/22 source/metadata
check and the forbidden-proof/unsafe-token scan of all 11 integration Lean files.

## Preservation and reporting

The reviewer independently recomputed SHA256 for all 47 earlier Chapter 1-7
source modules named in `evidence/ch08-preserved-chapters.json` and compared their
bytes directly with base commit `53968a9`: **47 matches, zero mismatches**. No
earlier chapter theorem source has changed. The review does not claim those old
chapters were freshly recompiled: the integrating lane transparently records
reuse of matching prior generated artifacts in its cache evidence.

The independently accepted complete inventory has 22 nodes and preserves
Rudin's numbering. The latest progress row says `6 / 22`; the queue distinguishes
pending later topics from attempted-and-blocked nodes. The source/brief numbering
correction is explicit. The accepted mathematical content keeps complex
coefficients, ordinary ordered series, infinite radii, both conditionally
convergent endpoints, all iterated derivatives, arbitrary interior accumulation
points, and native Chapter 6 integration. There is no unsupported claim of full
Chapter 8 completion or of completion of later chapters through Mathlib imports.

No source-fidelity or inclusion defect remains for the exact code hashes above.
The final audit, all clients, final default build and source checks have passed.
The concluding local commit and task log are owned by the integrating lane.

## Final manifest reconciliation

The reviewer independently parsed all 11 `source_sha256` entries in
`evidence/ch08-final-manifest.json`, recomputed their current file hashes, and
compared them with the 11 hashes in this review's table. All three maps are
identical: **11 files, zero mismatches**. Manifest counts match inspected kernel
logs: 6 principal theorems, 16 authored client theorems, 103 namespace declarations
and an 18-declaration probe subset. Its unattempted nodes are exactly 8.7-8.22,
and its needs-insight list is empty. No build or git mutation was performed by
the reviewer during this reconciliation.
