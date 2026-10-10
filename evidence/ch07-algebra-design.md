# Chapter 7 algebra and approximation design

Date: 2026-10-10. Scope: PMA-7.26 through PMA-7.33. Accepted inventory: `research/pma-ch07-inventory.md`, independently compared in `evidence/ch07-source-independent-review.md`. All eight accepted contracts now have complete checked proofs; independent post-proof/hostile review remains a separate gate.

The initial 156-line `rudin/Chapter07AlgebraDraft.lean` snapshot has SHA256 `c97092bf365866aaaef700957d445fcfd91c813ba37aae792de7ec20ac790d5a`. `./lake-local env lean Chapter07AlgebraDraft.lean` exited 0 with no warnings. That snapshot contained definitions and eight contracts, no theorem implementations, placeholders, or custom axioms. Taylor independently read and accepted all eight actual types before proof work, explicitly accepting the nonempty/nonunital convention; its own typecheck passed. The final source retains those contracts unchanged.

## Conventions requiring explicit review

- `IsFunctionAlgebra A` requires nonemptiness and closure under pointwise addition, multiplication, and scalar multiplication. It does not assume a unit, constant functions, continuity, compactness, or one bound common to all members. Nonemptiness is the inventory's explicit convention needed for empty domains; zero follows from any member by multiplying by zero.
- `AlgebraUniformClosure A` is defined by existence of a sequence in `A` converging uniformly to the given function. `IsAlgebraUniformlyClosed A` closes under all such sequence limits. They apply to raw functions on arbitrary types. A subset domain is represented by its subtype; no topology is needed for 7.29 or 7.31.
- `AlgebraFunctionBounded f` allows a finite real bound depending on `f`. It imposes no continuity and no bound shared by an algebra.
- `PolynomialFunctionFamily v` includes all polynomial evaluations along a domain map `v`. This covers real polynomials on a real set and complex polynomials evaluated at the embedded real points. `EvenPolynomialFunctionFamily` uses the exact semantic identity `p(-x)=p(x)`.
- `FunctionVanishesNowhere A` is `∀ x, ∃ f ∈ A, f x ≠ 0`. The witness may depend on `x`. `IsSelfAdjointFunctionFamily` is closure under pointwise complex conjugation (`star`).

## Clause mapping

| Node | Typed clauses |
| --- | --- |
| 7.26 | Both complex and real polynomial sequences converge uniformly on every ordered closed real interval, including singletons. The approximation is to functions continuous only on that interval. |
| 7.27 | On `[-a,a]`, `a ≥ 0`, each real polynomial has value exactly zero at zero, and the sequence converges uniformly to absolute value. |
| 7.28 | Separate real/complex definition comparators; raw sequential closure/closedness comparators; real and complex polynomial algebras on arbitrary domains; their uniform closures on closed real intervals are exactly the continuous functions. |
| 7.29 | For both real and complex algebras of individually bounded functions on arbitrary types, the uniform closure is a uniformly closed algebra and its members are bounded. |
| 7.30 | Separate real/complex separation and nonvanishing comparators; real and complex polynomial functions on the real line satisfy both; even real polynomials on `[-1,1]` do not separate points. |
| 7.31 | Nonunital, separating, nonvanishing real/complex algebras interpolate arbitrary values at two distinct points; no topology, continuity, or compactness hypotheses. |
| 7.32 | On an arbitrary compact metric space, a nonunital real algebra whose members are continuous, separating and nonvanishing has precisely all continuous functions as sequential uniform closure. Empty spaces are covered by the nonempty-algebra convention. |
| 7.33 | Definition of conjugation closure; the full analogous complex density theorem with self-adjointness; an existential algebra on the compact complex unit disk satisfying the other hypotheses but not self-adjointness, with a continuous function outside its uniform closure. |

## Intended reusable proof structure after acceptance

The pinned ordinary Weierstrass theorem directly supplies real approximations; complex approximations can combine real and imaginary polynomials. A sequence follows by choosing positive errors tending to zero. Subtracting each polynomial's value at zero gives the exact normalization in 7.27, with the approximation error adjusted accordingly.

For algebra closure, the uniform convergence topology on raw functions is relevant, not Pi pointwise topology. One option is a metric-space representation of bounded functions (which must not add continuity); another is direct epsilon/diagonal uniform approximation. Individual boundedness supplies multiplication continuity and boundedness of uniform limits. Closedness of the sequential closure needs an actual diagonal construction or a justified metric-closure equivalence.

Real Stone–Weierstrass in pinned Mathlib assumes a unital `Subalgebra`. A legitimate bridge must establish constants in the uniform closure from nonvanishing/separation, or use the lattice theorem after proving closure under absolute value and exact two-point interpolation. Constants may not be added to the input hypotheses. Complex density can use real/imaginary decomposition or a star-algebra bridge, retaining conjugation closure.

For the 7.33 warning, a possible concrete witness is complex polynomial restrictions to the closed unit disk and conjugation as the excluded continuous function. Uniform convergence of holomorphic functions on the disk interior preserves complex differentiability, using the pinned `TendstoLocallyUniformlyOn.differentiableOn` in `Analysis/Complex/LocallyUniformLimit.lean:136`; conjugation is not complex differentiable. This is a proposed proof route only, not a verified witness yet. Any used complex-analysis forward dependency will be reported, with no claim to have completed a later textbook chapter.

## Final proof snapshot and validation

Frozen draft: `rudin/Chapter07AlgebraDraft.lean`, 756 lines, SHA256 `44ebf1128a6a4f6409b4784c648ccecaf804a1ab354c406c02dcde638fde65c2`. Fresh `./lake-local env lean Chapter07AlgebraDraft.lean` exited 0 with no warnings or errors. Every `#print axioms pma7_26` through `#print axioms pma7_33` reported exactly `[propext, Classical.choice, Quot.sound]`. The source scan for `sorry`, `admit`, `native_decide`, custom `axiom`, and `unsafe` was empty. No contract was weakened while proving it.

- **7.26–7.28:** real approximation uses the pinned Weierstrass theorem; complex approximation combines real and imaginary polynomials with explicit error bounds. Choosing errors `1/(n+1)` constructs genuine uniform sequences. Subtracting each polynomial's exact value at zero proves 7.27. For compact-interval closure, a raw function defined only on the interval is extended arbitrarily outside it; a checked restriction equality proves precisely the required continuity on the interval. The other inclusion follows from uniform-limit continuity.
- **7.29:** arbitrary bounded functions are represented by bounded continuous functions on the same domain equipped locally with the discrete topology. This does not assume continuity of the source functions. The proof explicitly transfers sequential uniform convergence to the bounded-function metric and back, identifies the raw uniform closure with the relevant metric closure, and uses `NonUnitalSubalgebra.topologicalClosure` to retain addition, multiplication and scalar closure. Bounds depend on the individual member, including each uniform limit.
- **7.30–7.31:** polynomial separation/nonvanishing and failure of even-polynomial separation are explicit. Two-point interpolation constructs functions zero at one point and nonzero at the other by multiplying an existing point-separating function with point-specific nonzero members. It never assumes a constant-one member.
- **7.32:** the closed nonunital algebra is closed under absolute value by 7.27 and a proved polynomial-zero evaluation lemma. This gives pointwise min/max closure. Exact two-point interpolation yields strong separation of the corresponding set of continuous maps. The pinned lattice Stone–Weierstrass theorem, together with sequential closedness in the uniform metric, gives all continuous functions. Neither constants nor a unit were inserted into the premises.
- **7.33 density:** real-valued members are extracted from a self-adjoint complex algebra using the real and imaginary formulas. That real algebra remains nonunital, separating and nonvanishing. Applying 7.32 to both components and combining their uniform limits proves full complex density.
- **7.33 warning:** the witness is the algebra of complex polynomial restrictions to the closed unit disk. Its continuous conjugation function cannot be a uniform polynomial limit: restriction to the disk interior and pinned `TendstoLocallyUniformlyOn.differentiableOn` would make it holomorphic. A separate checked proof rules out complex differentiability of conjugation at zero by uniqueness of the real derivative and complex linearity. This also proves the algebra is not self-adjoint. This uses a complex-analysis library dependency; it is not a claim that a later textbook chapter is complete.

Root and hostile reviewer remaining_scope were notified of this exact frozen source and results. Root owns the canonical copy/build; no production integration is claimed here. No production, Chapter 5/6 source, root aggregator, Git state, toolchain, or configuration was edited by this author. The [prior-art](ch07-prior-art.md) and [API](ch07-api-landscape.md) reports record current public overlap and pinned library choices.
