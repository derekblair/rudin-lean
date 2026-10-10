# Chapter 7 foundations: definitions and PMA-7.1, 7.7–7.9

Author: remaining_scope. Date: 2026-10-10. All work is confined to the isolated workspace. The root independently accepted the actual typed contracts before implementation. The complete accepted `rudin/Chapter07FoundationsDraft.lean` remains a statement reference; canonical modules do not import it. Nodes 7.10–7.15 are assigned to the root's separate module.

## Frozen source

- `rudin/Rudin/PMA/Chapter07/Basic.lean`, 56 lines, SHA256 `b6b8b58999ad0025fd3ab28bc0ba3a4df5a07cc395158b99a14c05055bfa2b1a`.
- `rudin/Rudin/PMA/Chapter07/Foundations.lean`, 184 lines, SHA256 `941938d68a48db2a4e0ab70ba0b39d51828fc91602a4583ab449f8ad1c4d5742`.

Basic exposes pointwise and uniform convergence, ordered pointwise/uniform series, the source uniform Cauchy condition, extended nonnegative supremum error, both integral-spike examples, the Dini counterexample, and the bounded-continuous-function sequential closure predicates used by later nodes. Internal sequence indices are zero based; source positive indices correspond to `n+1` where applicable. The series definitions use the protected Chapter 3 ordered finite partial sums and `SeriesHasSum`, allowing conditionally convergent series.

## Proof scope and bridges

- **7.1:** the pointwise epsilon criterion, existence of a common function from individual pointwise limits, and ordered-series specialization. The limit outside the stated domain is chosen as zero; no restriction on the domain is added.
- **7.7:** the source non-strict norm epsilon condition is equivalent to Mathlib's strict uniform convergence condition by halving epsilon. Uniform convergence implies pointwise convergence; ordered partial sums give the series specialization.
- **7.8:** the uniform Cauchy condition is equivalent to Mathlib's uniform Cauchy sequence condition. Completeness supplies each pointwise limit, after which uniform Cauchyness supplies uniform convergence. The target is an arbitrary complete normed additive group, including the source complex numbers. The empty domain is permitted.
- **7.9:** `UniformError` takes its supremum in `ENNReal`. The uniform convergence criterion therefore permits infinite initial error suprema, and adds no all-index boundedness assumption. Its proof works even without the retained source pointwise-convergence premise. A separate boundedness-guarded theorem equates the error to the real supremum and identifies its `toReal` value. The empty-set case is proved separately; it yields zero. The nonempty comparator proves the real supremum is nonnegative and the extended supremum is finite before using `toReal`.

All four principal declarations are theorems of their accepted contracts: `pma7_1`, `pma7_7`, `pma7_8`, and `pma7_9`. Public reusable bridges are `uniformConvergesOn_iff_norm_le`, `uniformCauchyOn_iff_mathlib`, `uniformConvergesOn_iff_uniformError_tendsto`, and `uniformError_eq_real_sup`.

## Validation

- `./lake-local env lean Rudin/PMA/Chapter07/Foundations.lean`: exit 0, no diagnostics.
- `./lake-local build Rudin.PMA.Chapter07.Foundations`: successful, 8929 jobs; canonical module built.
- A fresh stdin client importing only the canonical Foundations module printed recursive axioms for all four principal declarations and both 7.9 helpers. Every report was exactly `propext`, `Classical.choice`, and `Quot.sound`.
- `python3 scripts/check_chapter07_preservation.py`: PASS for 26 inherited Chapter 5 files, 60 inherited Chapter 6 files, and the 127 production files. Production remained clean at `cc4328264872054cb72115dfcb3e025b1695ed5c`.

The author supplied these frozen hashes to the independent final reviewer. This author record does not substitute for that review or a final Chapter 7 integration gate.
