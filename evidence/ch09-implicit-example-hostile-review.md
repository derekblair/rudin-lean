# Chapter 9 numerical implicit-function example: independent review

Reviewer: `double_series`, 2026-10-23. The reviewer did not author this module, invoke Lean, or alter its production source. The exact source inventory is `research/pma-ch09-inventory.md`, node 9.29, with the variable-order requirements in `research/pma-ch09-source-review.md`.

**Accepted:** `rudin/Rudin/PMA/Chapter09/ImplicitExample.lean`, SHA256 `15a99aa2ed7eaaaa88d6d297cb5d86df702b793b60d6e2f93e7eb5b7d088486e`.

The full contract and proof were read, together with `ImplicitNeighborhood` and the statement/proof of `pma9_28` in `Implicit.lean` (SHA256 `e2100612918cb6b390866c6341ded45e776900ef79c69bf99d91f696c67a6694`). The root's `evidence/ch09-implicit-example-compile.log` ends with successful compilation. Kernel and recursive-axiom verification remain separate integration gates.

The two functions, base point `a=(0,1)`, and parameter point `b=(3,2,7)` are literal versions of the source. Coordinates are shifted from the book's one-based indices to `Fin` indices. Both zero-value identities and global `C^1` regularity are proved. The derivative is obtained from the actual exponential, cosine, product, and coordinate derivative rules; its rows are `[2,3,1,-4,0]` and `[-6,1,2,0,-1]`.

The solved block is `A=[[2,3],[-6,1]]`, with determinant 20. Its asserted inverse `(1/20)*[[1,-3],[6,2]]` is checked on both sides before invertibility is established. The parameter block is `B=[[1,-4,0],[2,0,-1]]`. Direct multiplication gives `-A^-1 B=[[1/4,1/5,-3/20],[-1/2,6/5,1/10]]`, exactly the final derivative formula. In particular, neither block order nor the leading minus sign was lost.

The final theorem constructs the implicit function through `pma9_28`; it does not assume a function with the desired properties. `ImplicitNeighborhood` retains open neighborhoods containing the base points, `g(b)=a`, the defining identity, `C^1` regularity, and local uniqueness. The derivative equality is a map equality tested on every increment, so it determines all six component partial derivatives. No hypothesis or conclusion is vacuous, and no source omission or numerical discrepancy was found.
