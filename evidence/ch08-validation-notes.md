# Final Chapter 8 validation

The final source is identified by the hashes in `ch08-final-manifest.json`.
The decisive combined checks, both run from `rudin/`, are:

- `lake build Rudin.PMA.Chapter08 Rudin.PMA.Chapter08Audit`: exit 0,
  `Build completed successfully (8976 jobs).`
- `lake build`: exit 0, `Build completed successfully (9003 jobs).`

Their complete outputs are `ch08-final-target-build-audit.log` and
`ch08-final-lake-build.log`. The target build freshly executed the combined
Chapter 8 audit; the full repository build replayed that checked result.
There are 22 named principal proofs and 22 contract type comparisons.
The recursive namespace audit inspected 532 declarations, including private
and generated declarations, and permitted only `propext`, `Classical.choice`,
and `Quot.sound`. Its additional 18-declaration FidelityProbes audit is a
subset of those 532, not 18 additional declarations. Chapter08 imports its
audit, so the unchanged shared root module includes this gate in normal builds.

The final build outputs contain an informational `ring` tactic suggestion
from `GammaConsequences.lean`; the surrounding proof closes and the build
succeeds. There are no final build errors or warnings.

Earlier per-module and section logs record intermediate work, not final
verification of the combined chapter. In particular,
`ch08-orthogonality-development.log` preserves a failed draft compiler run;
the final source no longer has those errors. Files beginning `ch08-prior-`
are provenance from the previous candidate branch, as their names indicate.
The current source reviews and final combined build supersede those earlier
records for acceptance of this lane.

The explicit coefficient-integral existence premise in 8.11–8.12 is the
source clarification recorded at those nodes and in the final report.
The remaining representation conventions are enumerated in the final report.
Source fidelity reviews are separate from kernel verification; passing a
build by itself is not asserted to prove fidelity to the printed statements.
