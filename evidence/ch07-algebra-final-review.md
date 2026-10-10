# Independent final review: PMA 7.26–7.33

Reviewer: `/root/oscillation/curve_hostile`, independently reviewing the implementation authored by `/root/oscillation`. Date: 2026-10-10.

**Verdict: ACCEPT all eight nodes. No source-fidelity defect, weakened type, vacuous conclusion, proof defect, or prohibited axiom was found. No implementation correction is requested.**

## Frozen inputs and independence

Read the complete 756-line implementation afresh, including every supporting definition, contract, proof, and numbered wrapper. The draft `rudin/Chapter07AlgebraDraft.lean` and canonical `rudin/Rudin/PMA/Chapter07/Algebra.lean` are identical at SHA-256:

`44ebf1128a6a4f6409b4784c648ccecaf804a1ab354c406c02dcde638fde65c2`.

Compared actual types and proofs with:

- `research/pma-ch07-inventory.md`: `f8e87ad7ccb765bfd4407e251958c5378552b209d32eca60a75e13e0ca9da0f0`.
- `evidence/ch07-source-independent-review.md`: `40f5a154f8a772610c6f5f5bd79a9bc558787622243c8c056b39baece86d7ee7`.
- Taylor's independent pre-proof acceptance, `evidence/ch07-algebra-contract-review.md`: `c4b731faf06486b275620ef1bc4ba4b65fb721090b188c93aa710c7a3e1086eb`.

The original accepted 156-line contract file is recoverable exactly from the final source: retain the prefix before `theorem polynomialFunctionFamily_isAlgebra`, remove the added `BoundedContinuousFunction` opened scope, and append `end Rudin.PMA.Chapter07` with a newline. Its SHA-256 is exactly the accepted `c97092bf365866aaaef700957d445fcfd91c813ba37aae792de7ec20ac790d5a`. Thus all supporting definitions and all eight contracts are textually unchanged; the added scope supports proofs only.

This reviewer did not author these algebra proofs. No implementation, shared module, project metadata, Git state, configuration, credential, or book source was modified or accessed for this review. The only writes were this report and the root-requested standalone review client.

## Per-node source and proof findings

| Node | Finding |
| --- | --- |
| 7.26 | Accepted. Actual sequences of complex and real polynomials approximate on the entire ordered closed real interval. Complex evaluations use the real-to-complex embedding. Real and imaginary approximations are combined with a proved norm estimate. The sequence selection uses positive errors `1/(n+1)`. Continuity is required only on the interval, and singleton intervals remain covered. |
| 7.27 | Accepted. Subtracting each polynomial's own value at zero gives exactly `P n.eval 0 = 0` for every index. Convergence of those values follows by evaluating the original uniform limit at zero, which belongs to `[-a,a]` for every `a≥0`. The proof includes `a=0`; normalization is not merely asymptotic. |
| 7.28 | Accepted. The function algebra is explicitly nonempty and closed under addition, multiplication, and scalar multiplication, without a unit assumption. Uniform closure is an actual sequential uniform-limit predicate, not pointwise closure. The real and complex polynomial examples and interval closure equalities are proved. The interval-subtype extension is only a device to apply interval approximation; its required restriction continuity is proved. |
| 7.29 | Accepted. Domains are arbitrary types, with no topology or continuity hypothesis. Each algebra member has its own real bound. The proof temporarily gives the domain the discrete topology, represents each bounded raw function as a bounded continuous function, and proves both directions between sequential uniform limits and the bounded-function metric closure. `NonUnitalSubalgebra.topologicalClosure` preserves exactly the source operations. Uniform-limit boundedness is established separately; no common family bound, compactness, completeness, or unit is silently assumed. |
| 7.30 | Accepted. Separation retains the distinct-point condition. Nowhere vanishing retains `∀x, ∃f∈A, f x≠0`. The polynomial identity and constant-one members provide the stated specific examples; they are not assumed for a general algebra. Even-polynomial failure is witnessed at the distinct points −1 and 1. |
| 7.31 | Accepted. The generic field proof uses separate nonzero witnesses at the two points and a separating member. Its two intermediate functions vanish at opposite points, and all membership steps use only addition, multiplication, and scalar multiplication. Their required denominators are proved nonzero before interpolation. Both arbitrary real and arbitrary complex target values are preserved, without topology or a unit premise. |
| 7.32 | Accepted. The proof stays nonunital. Exact-zero polynomial evaluation is proved by factoring out `Polynomial.X`, so no constant-one member is needed. This yields absolute-value closure, then min/max closure. The lattice Stone–Weierstrass API receives a nonempty set and proved strong separation, including the coincident-point case via the original pointwise nonvanishing premise. Sequential closedness is correctly upgraded in the metric space of compact-domain continuous maps. The result is equality with all continuous real functions, including empty domains. |
| 7.33 | Accepted. Self-adjointness is exactly pointwise conjugation closure. The real-valued members form a real nonunital algebra; real/imaginary decomposition proves its separation and pointwise nonvanishing. Two real uniform approximations are combined to recover arbitrary complex continuous functions. The attached warning is an actual counterexample, described below. |

The explicit nonempty-algebra convention is the one independently accepted before implementation. It excludes the empty-family/empty-domain trap while allowing genuine nonunital algebras. No global nonzero witness replaces pointwise nonvanishing, and no constants are added to density hypotheses.

## Actual complex warning and library boundary

The witness is the algebra of complex polynomial restrictions to the closed unit disk. The implementation proves continuity of every member, separation, and pointwise nonvanishing. Its continuous conjugation function lies outside the sequential uniform closure.

If such polynomial approximants existed, their uniform convergence on the closed disk would imply local uniform convergence on the open disk. The pinned `TendstoLocallyUniformlyOn.differentiableOn` API applies on that open set and would give complex differentiability of conjugation at zero. The separate `complex_star_not_differentiable_zero` proof contradicts this through uniqueness of the real derivative and complex linearity, comparing values at 1 and `Complex.I`. The disk interior contains zero; no boundary differentiation or empty-domain shortcut occurs. Exclusion from the closure also proves the polynomial family is not self-adjoint.

This is a valid complex-analysis library dependency, explicitly documented by the author. It does not claim completion of a later textbook chapter. The pinned theorem is in `Mathlib/Analysis/Complex/LocallyUniformLimit.lean`; the lattice API is in `Mathlib/Topology/ContinuousMap/StoneWeierstrass.lean`. Both interfaces were inspected independently.

## Independent kernel checks and persisted boundary client

Ran from the isolated workspace:

```text
./lake-local env lean Rudin/PMA/Chapter07/Algebra.lean
./lake-local env lean Chapter07AlgebraReviewProbe.lean
```

Both final runs exited 0 without warnings or errors. The direct canonical compile printed all eight numbered theorem axiom sets; each is exactly `[propext, Classical.choice, Quot.sound]`. A source scan found no `sorry`, `admit`, custom `axiom`, `native_decide`, or `unsafe` occurrence.

The standalone client is `rudin/Chapter07AlgebraReviewProbe.lean`, SHA-256:

`f383d5c99e4e821a60fb1fb7e4d4acfcd1b95ef69c62f3ae10e84b6f45d212ac`.

Its six principal boundary checks are:

1. **Genuinely nonunital interpolation:** eventually-zero functions on `ℕ` form an algebra that separates points and vanishes nowhere pointwise. The client proves that it has no constant-one member and, more strongly, no member nonzero everywhere. It then instantiates 7.31 with prescribed distinct real values and prescribed nonreal complex values. This checks both unit and nonvanishing-quantifier boundaries.
2. **No common bound:** all real functions on a singleton are individually bounded, and the client proves that no common bound works for the whole family. Nevertheless, 7.29 supplies an algebraic, uniformly closed, bounded-member uniform closure.
3. **Zero-radius normalization:** 7.27 at `a=0` returns an actual approximating sequence with exact zero for every polynomial.
4. **Singleton without global continuity:** 7.26 approximates an arbitrary complex function on `[2,2]`; no global continuity assumption is supplied.
5. **Empty compact density:** 7.32 and the density component of 7.33 both apply on the empty compact metric subtype `[1,0]`. Algebra nonemptiness is supplied explicitly; point-dependent premises are discharged only because the domain is empty.
6. **Concrete complex obstruction:** the client simultaneously certifies continuity of conjugation on the closed disk and its exclusion from the actual polynomial uniform closure.

All six principal probe theorems also report exactly `[propext, Classical.choice, Quot.sound]`. Development-only failures in the empty-domain client were corrected in the client (destructing interval membership and fixing a local universe parameter); the implementation required no change. The canonical SHA-256 remained unchanged after review.

## Disposition

All eight nodes pass this independent final source-fidelity and proof review at the stated frozen hash. No blocker remains in this scope. Whole-chapter hostile review and root integration checks are separate gates and are not claimed by this report.
