# Independent pre-proof contract review: PMA 7.26–7.33

Reviewer: calculus agent (`/root/taylor`), not the author of these contracts. Date: 2026-10-10.

**Verdict: ACCEPT all eight actual contracts and their supporting definitions.** This is a source-fidelity/type review before proof implementation, not acceptance of proofs that have yet to be written.

Reviewed the entire 156-line `rudin/Chapter07AlgebraDraft.lean` at SHA-256 `c97092bf365866aaaef700957d445fcfd91c813ba37aae792de7ec20ac790d5a`, against `research/pma-ch07-inventory.md` at SHA-256 `f8e87ad7ccb765bfd4407e251958c5378552b209d32eca60a75e13e0ca9da0f0`. The source hash was unchanged after review and independent compilation. No source edits were made.

## Contract-by-contract findings

| Node | Finding |
| --- | --- |
| 7.26 | Both complex and real polynomial sequences are explicit. Complex evaluation is at the real argument embedded in ℂ. Uniform convergence is on the full `Icc a b`; only continuity on that interval is assumed. `a≤b` retains singletons. The limit function need not be continuous outside the interval. |
| 7.27 | Every approximating real polynomial has exactly zero value at zero, independently of its index. Uniform approximation to absolute value covers `Icc (-a) a` for every `a≥0`, including zero. |
| 7.28 | Both scalar fields have addition, pointwise multiplication, and scalar multiplication closure, with no unit premise. Sequential uniform closedness and uniform closure are defined by actual sequence limits. Both polynomial-algebra examples and both compact-interval uniform-closure equalities are present. The latter use functions on the interval subtype, which correctly represents the domain restriction. |
| 7.29 | Every member has its own finite bound: `∀ f∈A, ∃ M, ∀x, ‖f x‖≤M`. There is no common bound on A. The closure is asserted to be an algebra, uniformly closed, and to consist of bounded functions. Both real and complex targets and arbitrary domains are covered, without continuity assumptions. |
| 7.30 | Separation quantifies over distinct points. Nonvanishing is `∀x, ∃f∈A, f x≠0`, retaining point-dependent witnesses. Real and complex polynomial families on ℝ satisfy both properties; global-even real polynomials restricted to `[-1,1]` explicitly fail separation. |
| 7.31 | Both scalar fields allow arbitrary prescribed values at arbitrary distinct points. No compactness, topology, continuity, or unit premise is introduced. The interpolant must belong to A. |
| 7.32 | Every compact metric domain, including empty and singleton spaces, is allowed. The hypotheses are a nonempty nonunital real algebra, memberwise continuity, separation, and nowhere vanishing. The conclusion is equality of sequential uniform closure with all continuous real functions. Constants are not assumed. |
| 7.33 | Self-adjointness is defined as closure under complex conjugation through `star`. The complex compact-metric theorem has all four required algebra/continuity/separation/nonvanishing hypotheses plus self-adjointness. The attached failure is a genuine existential counterexample on the compact complex closed unit disk: an algebra satisfying all other premises, not self-adjoint, with a continuous function outside its uniform closure. No proof-dependent particular witness is imposed. |

## Nonempty and nonunital convention

The explicit `A.Nonempty` conjunct in `IsFunctionAlgebra` is accepted under the inventory's required convention. It is the ordinary algebra convention, and does not imply a multiplicative unit on a general domain. Scalar closure implies the zero function belongs to the family, but cannot supply a constant one function without further assumptions.

For an empty domain there is exactly one function to either field. A nonempty function family then contains that function, so its sequential uniform closure contains every function; the empty-space Stone–Weierstrass conclusions hold. If the empty family had instead been admitted as an algebra, separation and nowhere vanishing would both be vacuous on the empty domain while the closure equality would fail. The chosen convention prevents that defect without excluding ordinary nonunital algebras or excluding empty metric spaces.

The existence of one globally nonzero member was not substituted for pointwise nowhere vanishing. A common bound on the whole algebra was not substituted for memberwise boundedness. Uniform convergence was not weakened to convergence on compact subsets. No conclusion uses a totalized limit without a convergence witness.

## Verification and limitations

Ran `./lake-local env lean Chapter07AlgebraDraft.lean` in the isolated workspace. It exited 0 with no output or warnings. Lean/toolchain and pinned Mathlib are the existing local environment; no setup, installation, production write, session control, Git operation, or book copying occurred.

The file presently contains definitions only, so there are no theorem proofs or axiom dependencies to certify. Later proof review must check the nonunital-to-library bridge, exact-zero polynomial normalization, sequential closure identification, and the actual complex counterexample construction. No contract correction is required before those proofs begin.
