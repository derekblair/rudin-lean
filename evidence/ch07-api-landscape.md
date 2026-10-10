# Chapter 7 pinned compactness and approximation API landscape

Date: 2026-10-10. Study author: oscillation, with independent read-only API lookup by curve_hostile. Scope: equicontinuity, compactness/Arzelà–Ascoli, sup-norm interfaces needed by those topics, and Stone–Weierstrass. Root owns uniform-convergence foundations; Taylor owns detailed native integral and derivative-limit bridges. No Chapter 7 contract or proof has been implemented or accepted by this study.

## Reproducible environment

Isolated root: `/home/derekblair/Documents/Codex/2026-10-10/task/rudin-ch05-isolated`.

- Toolchain: `leanprover/lean4:v4.34.1`.
- Mathlib: `d13f23b723b8a846827a245b89c10fc7d3f11612`, from `rudin/lake-manifest.json`.
- All relative library paths below begin at `rudin/.lake/packages/mathlib/Mathlib/`.
- Current `PROGRAM.md` was read. The old workspace PROGRAM path is absent. No additional applicable repository skill was found in the narrowed instruction scan.
- A fresh `./lake-local env lean --stdin` batch importing Mathlib checked the declarations below and exited 0. It only inspected existing declarations; no proof source or `.olean` output was added.
- The four `#print axioms` checks for bounded-map Ascoli, real Stone–Weierstrass, star-algebra Stone–Weierstrass, and ordinary polynomial approximation each reported only `propext`, `Classical.choice`, `Quot.sound`. This is an audit of those four declarations, not a claim that future Chapter 7 wrappers are verified.

Relevant source SHA256 values:

| File | SHA256 |
| --- | --- |
| `Topology/MetricSpace/Equicontinuity.lean` | `efa04bff777656cd09ebdf11e1d0614ad3012987958ff880f5054b8e9c6d827f` |
| `Topology/UniformSpace/Ascoli.lean` | `3bf0fc390c67bd333c3d05044d5c52b589b06e718e3af4a894d2cff2f7afd503` |
| `Topology/ContinuousMap/Bounded/ArzelaAscoli.lean` | `999b52f01003c82317fb85b709121ef2fe1be026ff5a08fbfb7e6dfe0fa99cc1` |
| `Topology/ContinuousMap/StoneWeierstrass.lean` | `71bd276dfa155bcc7719beaf5d281c288d17ebf0af793565b2eeb51ea3448bbe` |
| `Topology/ContinuousMap/Weierstrass.lean` | `02641e8b74594088d51707cd76f1826fec0ff529d38611c9e3e8b1628c875631` |

## Equicontinuity interfaces

`Topology/MetricSpace/Equicontinuity.lean:53`, `Metric.equicontinuousAt_iff`, is the direct metric comparator. For `F : ι → X → Y` between pseudometric spaces, it identifies `EquicontinuousAt F x₀` with:

```lean
∀ ε > 0, ∃ δ > 0, ∀ x,
  dist x x₀ < δ → ∀ i, dist (F i x₀) (F i x) < ε
```

The order of quantifiers retains a single δ for every family member. `Metric.uniformEquicontinuous_iff` in the same file gives the uniform counterpart. Source statements using absolute values for real/complex scalars require the norm/distance comparator, not a different quantifier order.

`Topology/UniformSpace/Equicontinuity.lean:138` defines `EquicontinuousOn` using relative neighborhoods. At line 189, `equicontinuous_restrict_iff F` identifies `Equicontinuous (S.domRestrict ∘ F)` with `EquicontinuousOn F S`. This supports representing a compact source set by its subtype without demanding global continuity outside the source set.

`Topology/UniformSpace/HeineCantor.lean:146`, `CompactSpace.uniformEquicontinuous_of_equicontinuous`, promotes equicontinuity to uniform equicontinuity on a compact uniform-space domain.

`Topology/UniformSpace/Ascoli.lean:168`, `Equicontinuous.tendsto_uniformFun_iff_pi`, assumes compact domain and equicontinuity of the family. It equates convergence in `UniformFun` with convergence in the product topology of functions. The latter means pointwise convergence. There is no separate continuity hypothesis on the limit. This may provide the final passage from a pointwise convergent subsequence to a uniformly convergent one; dense-subset convergence alone is not the premise of this theorem.

## Arzelà–Ascoli and subsequences

The simplest engine is `Topology/ContinuousMap/Bounded/ArzelaAscoli.lean:109`:

```lean
BoundedContinuousFunction.arzela_ascoli
  (s : Set Y) (hs : IsCompact s) (A : Set (X →ᵇ Y))
  (in_s : ∀ f x, f ∈ A → f x ∈ s)
  (H : Equicontinuous ((↑) : A → X → Y)) :
  IsCompact (closure A)
```

Ambient assumptions are `[TopologicalSpace X] [CompactSpace X] [PseudoMetricSpace Y] [T2Space Y]`. This demands **one common compact range set**. For real/complex or finite-dimensional targets, a uniform bound can provide that set. Pointwise boundedness alone does not immediately satisfy `in_s`; it needs a finite-cover equicontinuity argument or the more general API below.

`Topology/UniformSpace/Ascoli.lean:475`, `ArzelaAscoli.isCompact_closure_of_isClosedEmbedding`, instead takes:

- a family `𝔖` of compact domain subsets;
- a closed embedding of the ambient function space into `UniformOnFun 𝔖`;
- equicontinuity on each member of `𝔖`;
- for each relevant point `x`, a compact set `Q` containing every selected function value at `x`.

Here `Q` is allowed to depend on `x`. The theorem returns compact closure in the ambient index/function space. This closely matches pointwise relatively compact hypotheses, but the embedding and topology identifications must be proved. Merely writing `IsCompact (closure ...)` on an unbundled Pi type would use pointwise topology and would miss uniform compactness.

At `Ascoli.lean:500`, `ArzelaAscoli.isCompact_of_equicontinuous` transfers pointwise compactness of `ContinuousMap.toFun '' S` to compactness of `S : Set C(X,Y)`. On compact `X`, the continuous-map topology agrees with the required uniform topology.

Useful assembly interfaces:

| Declaration | Local file and line | Role / retained premise |
| --- | --- | --- |
| `ContinuousMap.equivBoundedOfCompact` | `Topology/ContinuousMap/Compact.lean:48` | Equivalence from `C(X,Y)` to bounded continuous functions on compact `X`. |
| `ContinuousMap.isUniformEmbedding_equivBoundedOfCompact` | same, 67 | The equivalence respects the uniform topology. |
| `ContinuousMap.isometryEquivBoundedOfCompact` | same, 94 | Metric version for compact source. |
| `IsCompact.tendsto_subseq` | `Topology/Sequences.lean:298` | Requires `FirstCountableTopology` of the ambient function space and produces `StrictMono φ`, a limit in the set, and convergence of the subsequence. |
| `BoundedContinuousFunction.tendsto_iff_tendstoUniformly` | `Topology/ContinuousMap/Bounded/Basic.lean:240` | Converts bundled metric convergence back to uniform convergence of actual functions. |

Do not infer sequential compactness from compactness in an arbitrary topology. The bounded-function metric space supplies the needed countability instance here. On noncompact domains, compact-open convergence is generally only uniform convergence on compact subsets. Bounded subsets of infinite-dimensional targets need not have compact closure, so pointwise boundedness cannot be generalized to arbitrary Banach targets without further assumptions.

## Sup-norm interfaces for continuous functions

`Topology/ContinuousMap/Compact.lean` provides `ContinuousMap.norm_coe_le_norm` (199), `ContinuousMap.norm_le` (207), `ContinuousMap.norm_lt_iff` (213), `ContinuousMap.dist_le` (121), and `ContinuousMap.dist_lt_iff` (134). These turn bundled sup-norm/distance bounds into pointwise bounds and back. The `_of_nonempty` variants explicitly require a nonempty source; the versions with a nonnegative/positive bound support empty compact domains.

These bundled types include continuity. They must not be used as the universal representation of all bounded, possibly discontinuous functions in Chapter 7's opening definitions. The foundational uniform convergence predicates work on raw functions. If a source sup is defined in `ℝ`, retain boundedness and empty-set conventions in the comparator rather than allowing totalized `sSup` to conceal an unbounded range.

## Stone–Weierstrass and polynomial approximation

All of the following are in `Topology/ContinuousMap/StoneWeierstrass.lean`:

| Line / declaration | Exact structural content |
| --- | --- |
| 265 `ContinuousMap.subalgebra_topologicalClosure_eq_top_of_separatesPoints` | For compact topological `X` and `A : Subalgebra ℝ C(X,ℝ)`, `A.SeparatesPoints` implies `A.topologicalClosure = ⊤`. No Hausdorff assumption on `X` is required by this declaration. |
| 313 `ContinuousMap.exists_mem_subalgebra_near_continuous_of_separatesPoints` | For such an `A`, every continuous `f : X → ℝ` is approximated uniformly within any positive ε by a member of `A`. |
| 323 `ContinuousMap.exists_mem_subalgebra_near_continuous_of_isCompact_of_separatesPoints` | Approximation on a compact subset, but the algebra members and target remain globally continuous maps on `X`. Use `C(K,ℝ)` for functions continuous only on `K`. |
| 401 `ContinuousMap.starSubalgebra_topologicalClosure_eq_top_of_separatesPoints` | For `[RCLike 𝕜]` and compact `X`, a point-separating `StarSubalgebra 𝕜 C(X,𝕜)` is dense. Complex conjugation closure is retained. |
| 165 `ContinuousMap.sublattice_closure_eq_top` | A nonempty set of continuous real maps closed under pointwise min/max and strongly separating points has full closure. `Set.SeparatesPointsStrongly`, in `ContinuousMap/Algebra.lean:747`, allows arbitrary prescribed values at two points. |

**Unitality is a live architecture risk.** `Subalgebra` and `StarSubalgebra` contain constants. If the accepted source contract only assumes addition, scalar multiplication, multiplication, separation, and nonvanishing, replacing it with `Subalgebra` would strengthen the hypothesis. A constants-in-closure or genuine nonunital bridge must first be proved. No generic nonunital/nonvanishing Stone–Weierstrass theorem was located in this file. Its later `ContinuousMapZero` results concern specialized functions vanishing at zero and do not directly supply this bridge. Complex separation without conjugation closure is also insufficient for the complex theorem.

`Topology/ContinuousMap/Weierstrass.lean:109` provides, in the **root namespace**:

```lean
exists_polynomial_near_of_continuousOn
  (a b : ℝ) (f : ℝ → ℝ)
  (hf : ContinuousOn f (Set.Icc a b)) (ε : ℝ) (hε : 0 < ε) :
  ∃ p : ℝ[X], ∀ x ∈ Set.Icc a b, |p.eval x - f x| < ε
```

It has no `a ≤ b` premise, so empty and singleton cases are admitted. The bundled counterpart `exists_polynomial_near_continuousMap` gives a sup-norm estimate. A polynomial sequence follows by choosing tolerances tending to zero. If the accepted source demands endpoint interpolation, that is a separate conclusion requiring a correction argument; this theorem alone supplies no endpoint equality. Complex-valued functions on a real interval can use componentwise real approximation with error accounting; complex polynomials on arbitrary compact complex sets cannot be asserted dense from this real interval theorem.

## Recommended dependency shape, pending exact inventory

1. Keep raw-function pointwise/uniform convergence and Cauchy definitions separate from bundled continuous-map infrastructure. Prove explicit comparators after source contracts are accepted.
2. Use domain subtypes for compact source sets to preserve within-domain continuity and endpoints.
3. Reuse the metric equicontinuity comparator; choose either pointwise-compact Ascoli or derive the common range bound before invoking bounded-map Ascoli.
4. Pass compactness through the metric function space, extract a strictly increasing subsequence, then expose `TendstoUniformly` on the original functions.
5. Reuse ordinary polynomial approximation directly where the source statement matches. Handle any endpoint constraints explicitly.
6. Resolve real nonunital/nonvanishing and complex star-closure assumptions before choosing a Stone–Weierstrass wrapper.
7. Keep Chapter 7 integration on native Chapter 6 `RSIntegral`. Detailed integral/derivative work belongs to [ch07-calculus-api.md](ch07-calculus-api.md), and the [public prior-art recheck](ch07-prior-art.md) records why nearby external statements are not automatic substitutes.

No API availability blocker was found for compactness or approximation. Remaining work is source-inventory acceptance, exact typed contracts, and the identified equivalence bridges. No Chapter 7 completion claim is made.
