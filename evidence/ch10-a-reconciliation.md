# Chapter 10 first-half reconciliation

The full chapter has 51 numbered nodes. This lane covers **10.1–10.26**;
the second lane starts at 10.27. The earlier source is
`ch8-codex-20261022` at `bb50a2079f8e189d8e282e2521bbadb64f4f98eb`.

## Result and integration boundary

All 26 principal proofs were reconciled and verified in an isolated snapshot
with the exact earlier Chapter 8–9 prerequisites. The live lane remains
**blocked on prerequisite integration**: its baseline lacks 13 required
Chapter 8–9 files and has a different Chapter 8 umbrella. The brief reserves
these files to other lanes, so none was changed in the live tree. This is not
a claim that the standalone lane build passes.

The candidate preserves 35 prior production modules and 10 probe modules byte
for byte. Four supplementary modules close attached claims missed by the prior
contracts:

- `PartitionComplements`: the complex-valued corollary of 10.8.
- `FormExampleGeometry`: the ellipse's area and boundary, the spherical image's
  volume, and explicit boundary identifications in 10.12.
- `ExactOneFormComplements`: the displayed derivative calculation in 10.19 and
  its nonvanishing under the actual surface-integral equality relation.
- `AffineOrientation`: the relative-orientation paragraph of 10.26, including
  the tuple-sign convention and affine reparametrization.

There are no outstanding mathematical proof gaps identified in 10.1–10.26.
The missing integration prerequisites remain a genuine blocker to the required
build in the live baseline.

## Validation

Pinned Lean: 4.34.1, commit `5045d0056413266e57c625dcd7c365b10e377c52`.
Pinned Mathlib: `d13f23b723b8a846827a245b89c10fc7d3f11612`.

In `.lane-validation/rudin`, the exact command
`lake build Rudin.PMA.Chapter10 Rudin.PMA.Chapter10Audit` exited **0**:
`Build completed successfully (9012 jobs).`

In `rudin`, the same command exited **1**, first failing to locate
`Rudin/PMA/Chapter09/ParameterIntegrals.lean`, with additional missing
Chapter 9 imports and consequent dependent-import failures. Full logs:
`ch10-a-final-build.log` and `ch10-a-lane-final-build.log`.

The final audit checked 26 principal theorem declarations and 26 contract
comparisons, five supplementary theorem declarations and one supplementary
contract comparison, and absence of all second-half principals. The recursive
namespace audit checked **907 declarations**, including the **79-declaration
probe subset**. Only `propext`, `Classical.choice`, and `Quot.sound` occur.
Source checks found no forbidden proof tokens. All 51 delivered Lean files
match the successful snapshot. All 196 existing baseline files outside the
Chapter 10 umbrella remain byte-identical.

The final verification command was recorded through `/root/bin/with-ledger.sh`.

## Source conventions and generalizations

These are flagged beside their nodes in `Rudin/PMA/Chapter10.lean` and must
also be carried into the final report:

- Coordinates start at zero; finite-subtype partition indices replace a finite list.
- Dimension-zero integration and surfaces are included as a harmless extension;
  the primitive factorization explicitly assumes positive dimension, matching
  the source's implicit need to select a coordinate.
- `IsPrimitiveOn` is defined on arbitrary sets. Its specialization to open sets
  matches 10.5; the open neighborhoods in 10.7 are explicit hypotheses.
- Functions are represented by total ambient functions with assertions restricted
  to their domains. Surface data stores the book's chosen neighborhood extension.
- Forms are homogeneous exterior-algebra fields with proved ordered-coefficient,
  native-integral, and operational-equality bridges. This does not substitute
  algebraic equality for the theorem about all surface integrals.
- The native Chapter 6 Riemann integral is retained. Measure integrals are used
  only through proved bridges. Area and volume in the 10.12 supplement use
  Lebesgue measure of the explicit finite-measure regions.
- Continuous maps do not bundle boundedness. Compact support supplies the
  boundedness of functions in the 10.8 corollary.
- The 10.11 regularity bridge covers every natural order, including C¹/C².
  The purely algebraic 10.13 index identities need no continuity.
- The 10.19 endpoint formula covers any ordered compact interval, including [0,1].
- The affine characterization in 10.26 applies to arbitrary real modules.
  For repeated vertices, the relative-orientation relation can have witnesses of
  both signs; no false uniqueness or equality of parametrizations is asserted.

No repaired false claim, strengthened definition, or unresolved narrowed
theorem is introduced by the supplements. Earlier real-only and omitted-remark
coverage gaps are explicitly repaired.

## Reproduce and unblock

With the source commit present in the local Git object database and the pinned
Mathlib cache already available, run:

```sh
python3 scripts/verify_ch10_a_reconciliation.py --build
```

The script checks provenance, source hashes, forbidden tokens and pins, then
builds within `.lane-validation`, without modifying live Chapter 8–9 files or
installing anything. The exact missing/differing prerequisite paths are listed
in `ch10-a-reconciliation-manifest.json` and `ch10-a-verification.json`.
Coordinated integration of those earlier prerequisites is required before the
same target can pass in the live lane. No merge was performed.
