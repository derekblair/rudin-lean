# Chapter 1 verification log

Pinned Lean 4.34.1 and Mathlib d13f23b723b8a846827a245b89c10fc7d3f11612.
Every completed node is typechecked and followed by `lake build` before its local commit.
Independent back-translations are supplied by the fidelity review agent; Mathlib comparisons
are explicit wrapper proofs or equivalence lemmas in the chapter.

Source checked against the third edition PDF hosted by [Lehman College](https://www.lehman.edu/faculty/rbettiol/lehman_teaching/2020mat320/baby_Rudin.pdf).
The inventory incorrectly says 1.2 is absent: it is a remark on rational incompleteness,
folded into 1.1 under PROGRAM.md's rule for remarks. The requested target count stays 37.

| Node | Independent back-translation and fidelity | Reference/probe |
|---|---|---|
| PMA-1.1 | PASS: every rational has square unequal to 2; each positive rational below/above the threshold has a larger/smaller witness on the same side. | `irrational_sqrt_two`, `irrational_sqrt_ratCast_iff_of_nonneg`; witnesses verified by rational algebra. |
