# Chapter 9 opening section verification

Verified scope: PMA-9.1–9.9, nine of the 43 independently inventoried nodes.
The user explicitly authorized this chapter while Chapter 8 remains partial.

All nine principal theorems compile with exact contract comparators. Independent
source and proof review accepted `Chapter09/Linear.lean` at SHA256
`a61832744979629254d50b5a7c9d8c6acaab123b516cd14919f320199cfa34e3`.
The proof author was `double_series`; the reviewer was `ch8_fidelity`; the root
authored the nine independent boundary clients. These cover empty spans,
nonempty subspace requirements, dimensions zero/one, singular and degenerate
invertibility, noncommutativity, negative scalar norms and zero-row norm bounds.

The recursive audit checks 61 namespace declarations including the nine probe
declarations. Only `propext`, `Classical.choice` and `Quot.sound` occur.
`evidence/ch09-opening-audit-compile.log` records actual theorem lookup and
nine type comparisons. `evidence/ch09-opening-source-check.log` records the
inventory/metadata/source-token check. The default project build passed and is
recorded in `evidence/ch09-opening-default-build.log`.

Later Chapter 9 candidates have not passed all completion gates and are not
counted by this section commit. Candidate contract review is distinct from
production proof verification. Prior chapter source preservation is recorded in
the baseline and opening manifests.
