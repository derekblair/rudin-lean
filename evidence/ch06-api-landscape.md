# Chapter 6 pinned API landscape and implementation recommendation

Read-only inspection on 2026-10-10. This report concerns the isolated snapshot's Lean 4.34.1 / Mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612`. No Chapter 6 builds, source changes, installs, network operations, Git operations, or session interactions were performed for this study. Paths below are relative to `rudin/.lake/packages/mathlib/Mathlib/`. The accepted scope is the 27 nodes in `research/pma-ch06-inventory.md`.

## Decision

Implement Rudin's weighted **closed-cell Darboux sums** and upper/lower integrals natively. Mathlib has useful finite-partition and bounded-variation infrastructure, but neither its right-continuous Stieltjes measure nor its uniform-mesh Riemann integral is a faithful definition for all the permitted discontinuous integrators. Any backend integral must enter through a proved equivalence with the relevant endpoint hypotheses.

The fastest reusable partition backend is `BoxIntegral.Prepartition` in dimension `Fin 1`, with the predicate `IsPartition`; keep a source-facing finite nondecreasing endpoint chain and prove its equivalence if that representation is already selected. A direct finite-chain implementation is also sound, but it must supply the common-refinement and regrouping lemmas described below. Do not require strict monotonicity of the source chain: repeated points are permitted and have zero weight.

## Two counterexamples that should become boundary probes

1. **Right-continuous normalization changes endpoint mass.** On `[0,1]`, take `α(x)=0` for `x≤0`, and `α(x)=1` for `x>0`. The source integral of the constant function `1` is `α(1)-α(0)=1`. Replacing `α` by its right limit gives constant value `1` on this interval, and its Stieltjes measure of `(0,1]` is zero.
2. **Uniform mesh convergence is stronger than the source definition.** For `a<c<b`, put `α(x)=0` for `x≤c`, `α(x)=1` for `x>c`; put `f(x)=0` for `x<c`, `f(x)=1` for `x≥c`. A partition containing `c` has lower and upper sums both equal to `1`: every cell on the left has zero weight and the weighted right cell has constant value `1`. Arbitrarily small cells straddling `c` admit tags on either side, giving tagged sums `0` or `1`. Thus the source integral exists while all sufficiently fine tagged sums do not converge.

These examples are elementary constructions, not copied source material. They distinguish the definitions; they do not contradict convergence over all refinements of a fixed sufficiently good partition.

## Exact finite-partition infrastructure

| API | Location | Use and remaining obligation |
| --- | --- | --- |
| `Box` | `Analysis/BoxIntegral/Box/Basic.lean:72` | A box is half-open `(lower,upper]` with strict coordinate inequalities. Use scalar **closed** `Icc (J.lower 0) (J.upper 0)` for cell extrema and tags. Handle the degenerate ambient interval separately. |
| `Prepartition`, refinement order | `Analysis/BoxIntegral/Partition/Basic.lean:54`, `:145` | Finite disjoint boxes within the ambient box. Smaller in this order means finer. |
| `Prepartition.inf_def` | `Analysis/BoxIntegral/Partition/Basic.lean:518` | Common refinement is exactly `π.biUnion (fun J => ρ.restrict J)`. |
| `sum_biUnion_boxes` | `Analysis/BoxIntegral/Partition/Basic.lean:312` | Regroup refined sums by the parent cell. |
| `IsPartition`, `.restrict`, `.inf` | `Analysis/BoxIntegral/Partition/Basic.lean:639`, `:685`, `:688` | Covering, restriction, and common-refinement coverage are already proved. |
| `BoxAdditiveMap.ofMapSplitAdd` | `Analysis/BoxIntegral/Partition/Additive.lean:143` | Construct raw interval content `J ↦ α(J.upper 0)-α(J.lower 0)`. The required binary split identity is subtraction telescoping; it needs no right continuity or monotonicity. |
| `BoxAdditiveMap.sum_partition_boxes` | `Analysis/BoxIntegral/Partition/Additive.lean:86` | Once the preceding content is built, total weight is `α(b)-α(a)`, including inside every parent cell of a refinement. |
| `splitMany` | `Analysis/BoxIntegral/Partition/Split.lean` | Force prescribed partition points and make finite fine partitions. |
| `Finset.orderIsoOfFin`, `orderEmbOfFin` | `Data/Finset/Sort.lean:186`, `:194` | For an independent endpoint-chain representation, sort the union of the two finite ranges. Range, minimum, and maximum lemmas are at `:216`, `:241`, `:246`. |

Recommended internal type for `a<b` is the subtype `{π : Prepartition I // π.IsPartition}`, where `I` is the one-dimensional box with endpoints `a,b`. Define the upper/lower sum by the finite sum of the cell supremum/infimum multiplied by the raw weight. Box additivity gives mass conservation; monotonicity of `α` on `[a,b]` gives nonnegative weights. Closed-cell inclusion and `csSup`/`csInf` monotonicity then give the two refinement inequalities after `inf_def` and regrouping.

Source correspondence is a real proof obligation: collapse repeated nodes of an endpoint chain, construct its adjacent half-open boxes, and prove their closed extrema and nonzero-weight terms are unchanged. Conversely, sort a one-dimensional full box partition's finitely many endpoints; disjointness and coverage force the boxes to be the successive nonempty intervals. This proves that the backend quantifies over exactly the source partitions, up to harmless zero-width cells. Do not declare the correspondence by definitional fiat.

If the source-native `Partition a b` is a monotone `Fin(n+1) → ℝ` with endpoint equalities, the concrete alternative is: define refinement by inclusion of point ranges; sort the union with `Finset.orderEmbOfFin`; prove insertion of one point preserves total weights and improves sums, then induct over the extra distinct points. Repeated values can be removed first because their contributions are zero. Another equivalent route uses an explicit monotone node-index map into the fine chain and a finite telescoping/regrouping lemma. This is more new finite combinatorics than the box backend.

## Prerequisite proof sequence: 6.1–6.7

1. Prove cell images are nonempty and bounded before using real `sSup`/`sInf`. A singleton repeated cell remains nonempty but has zero weight. Establish the common global bounds and telescoping total weights. For `a=b` every sum is zero.
2. Prove repetition invariance, a common refinement, and lower-sum increase / upper-sum decrease. Positivity of weights is essential here; strict positivity is unnecessary.
3. Deduce every lower sum is at most every upper sum by passing to a common refinement. The families of sums are nonempty and bounded, so their real supremum/infimum have the intended semantics.
4. Define integrability as source boundedness plus monotone integrator plus equality of these finite upper/lower integrals. The integral can be the lower integral, but every theorem using it must expose integrability or a separately sufficient boundedness hypothesis.
5. Prove equality iff every positive `ε` admits a partition with upper-minus-lower sum below `ε`, using the defining `csSup`/`csInf` approximation properties and common refinement.
6. Squeeze each tagged sum between its lower and upper sum. Prove the 6.7 two-tag estimate with the absolute value **inside** the sum, bounded by the partition's oscillation sum. The convergence assertion is for every refinement of a good partition, not arbitrary partitions with small mesh.
7. Keep the zero-total-weight case throughout: a nondecreasing integrator may be constant, and dividing by `α(b)-α(a)` without a case split is invalid.

## Existing integration APIs and their limits

`Analysis/BoxIntegral/Basic.lean:82` defines tagged `integralSum` for an arbitrary box-additive function. `HasIntegral` at `:164` takes a limit along a filter controlled by `IntegrationParams`, and `integral` at `:176` is totalized by zero. `Partition/Filter.lean:34–67` explains the controls; `Riemann` at `:236` uses a constant mesh bound and tags in each closed cell. The counterexample above rules it out as the general source definition even with the correct raw box content.

`Analysis/BoxIntegral/Integrability.lean:198` (`IntegrableOn.hasBoxIntegral`) explicitly assumes the non-Riemann mode. `ContinuousOn.hasBoxIntegral` at `:305` works for the Riemann mode, and the bounded almost-everywhere-continuous theorem at `:317` offers a further bridge once its hypotheses and the measure convention have been justified. Arbitrary almost-everywhere replacement is not a source Stieltjes invariance rule: values at jump points can matter.

`MeasureTheory/Measure/Stieltjes.lean:112` defines `StieltjesFunction` with monotonicity **and right continuity**. `Monotone.stieltjesFunction_eq` at `:250` reveals that the constructor replaces a monotone function by `rightLim`. `measure_Ioc` at `:528` assigns mass `α(b)-α(a)` to `(a,b]`; `measure_singleton` at `:533` uses `α(x)-leftLim α x`. The corresponding closed/open interval formulas are at `:572`, `:582`, and `:598`. These are exact existing theorems, but they concern the normalized right-continuous integrator. They do not justify changing the original integrator's endpoint values.

A possible later bridge for arbitrary source integrators is to extend the restricted integrator constantly outside `[a,b]`, right-regularize that extension, and integrate over **closed** `[a,b]`. Its endpoint atoms must recover the source right jump at `a` and left jump at `b`. This is only a proposed construction; total mass, cell inequalities, and integral equality must be proved before use. Even a valid bridge would not identify all Lebesgue-integrable functions with the source's Darboux-integrable functions.

For ordinary integration, first prove the native `α=id` integral agrees with Mathlib's interval integral and that source integrability implies `IntervalIntegrable`. This is the useful common gate for later FTC/vector APIs. A continuous-integrand-only bridge is insufficient for 6.17 and 6.20–6.22.

## Remaining theorem routes

- **6.8–6.10:** uniform continuity controls oscillation on good cells. For finite discontinuities, isolate bad points in intervals with small total raw `α` increments using continuity of `α` there; apply uniform continuity on the remaining compact pieces. Endpoints use relative continuity. For monotone `f`, use small `α` increments and telescope the changes of `f`; treat antitone `f` by negation.
- **6.11–6.13:** common refinements and oscillation estimates prove composition, products, absolute values, function linearity, and integrator linearity. A continuous composition proof cannot assume Lipschitz continuity. Restriction and adjacent-interval addition follow by forcing the dividing point into the partition. Integrator scaling is nonnegative; arbitrary negative scaling would leave the monotone-integrator domain.
- **6.14–6.16:** define the left-continuous step exactly (`0` at its jump), then prove its one-cell weighted sum estimate using integrand continuity at the jump. For countably many atoms, finite sums plus the error bound `M * tail-weight` prove convergence and the integral formula. Include summability and monotonicity of the integrator itself. A measure `dirac` calculation alone does not prove the source integral exists.
- **6.17:** use the mean value theorem on each cell and the ordinary Riemann criterion for `α'` to compare weighted sums with tagged sums of `f α'`. Both directions of integrability are required, with bounded `f`. Do not replace the source premise `α' ∈ R` by continuity of `α'`.
- **6.18:** specialize the proved atomic and derivative-density formulas to the quadratic integrand, retaining their existence hypotheses.
- **6.19:** the primary Stieltjes substitution is an exact transport of partitions by a continuous strictly increasing bijection; cell images and extrema and raw increments agree. It needs no derivative. Obtain the ordinary weighted consequence from 6.17. Existing derivative-based substitution theorems are not a replacement for this first clause.
- **6.20–6.22:** a direct proof from integral bounds and the mean value theorem is natural. After a complete ordinary-integral bridge, `MeasureTheory/Integral/IntervalIntegral/FundThmCalculus.lean:1140`, `integral_eq_sub_of_hasDerivAt_of_le`, supplies FTC2 with closed-interval continuity, open-interval derivative, and integrable derivative; it does not demand derivative continuity. `integral_hasDerivAt_right` at `:725` also needs measurability near the point and ambient continuity; use the within-interval version at `:867` for endpoint statements. Do not silently replace a relative hypothesis by ambient continuity.
- **6.23–6.25:** define source vector integrability coordinatewise before using vector integral APIs. Finite-dimensional equivalence permits the coordinatewise FTC; norm integrability follows from finite-dimensional continuity and scalar composition/algebra. The norm inequality can follow from Cauchy–Schwarz applied to the integral vector, avoiding any unproved Bochner identification.

## Curves: substantial reusable infrastructure, one missing bridge

`Topology/EMetricSpace/BoundedVariation.lean:61` defines `eVariationOn` in `ℝ≥0∞` as the supremum of finite sums of successive distances along monotone finite sequences; `BoundedVariationOn` at `:66` is its finiteness. `eVariationOn_eq_strictMonoOn` at `:125` removes repetitions. `Icc_add_Icc` at `:404`, `comp_eq_of_monotoneOn` at `:521`, and the Lipschitz composition estimates around `:1234` are useful exact APIs. This is very close to 6.26: pad endpoints and remove repetitions to prove equality with the source partition-length supremum. Retain `ℝ≥0∞` for possibly nonrectifiable curves; `toReal` turns infinity into zero and is safe only after finiteness is proved.

No direct C1-curve theorem identifying this supremum with the integral of speed was found. `Geometry/Manifold/Riemannian/PathELength.lean` defines an integral-of-speed quantity, so its defining identity does not prove the required polygonal-length equality. `MeasureTheory/Integral/CurveIntegral/Basic.lean` concerns integrals of one-forms, also not that missing equivalence.

Faithful 6.27 route: continuous derivative on a compact interval gives a norm bound, hence a Lipschitz estimate and finite variation. For the upper bound on length, integrate the norm derivative bound on every cell and sum; `MeasureTheory/Integral/IntervalIntegral/DistLEIntegral.lean:42`, `norm_sub_le_integral_of_norm_deriv_le_of_le`, supports that direction after the ordinary bridge. For the reverse bound, uniform continuity of the derivative makes each curve increment close to derivative-at-tag times cell width; sum the norm errors and compare with source Riemann sums for the continuous speed. This proves the genuine source integral identity, including the appropriate one-sided derivative assumptions at endpoints.

## Assignment boundary

6.1–6.7 is the prerequisite bottleneck. Parallel work can safely prepare exact contracts and local oscillation/series/variation helpers, but downstream source-integral theorems must import the agreed definitions rather than introduce competing totalized integrals. 6.26 and its partition-to-variation correspondence can proceed substantially independently. 6.27 still needs the genuine ordinary-integral bridge or a direct Riemann-sum proof.

## Subsequent authorized implementation: 6.3–6.4

After the read-only study, the parent chose the literal weakly monotone finite-chain representation and authorized this worker to implement `rudin/Chapter06RefinementDraft.lean`. The independent contract reviewer approved the exact union/refinement contracts before proving them. At 16:08 UTC the complete draft compiled with exit zero and no warnings, after roughly five minutes of implementation.

The final approach avoids a second partition backend. A generic list path-cost lemma proves refinement monotonicity for any cost with zero diagonal and the interval splitting inequality. Its induction permits repeated coarse points equal to the current starting point, so no strictness or index-selection assumptions enter. `List.ofFn` transfers the result to the source's finite-chain sums. Applying the lemma to the cell infimum times the raw weight proves the lower inequality; applying it to the negative cell supremum cost proves the upper inequality. Finite-set sorting constructs the exact union of partition-point ranges. Two opposite refinements prove repetition invariance.

The public results are `Partition.Refines`, `pma6_3_common_refinement`, `pma6_4_lower`, `pma6_4_upper`, `pma6_4`, and `pma6_3_repetition_invariant`. No continuous-integrator, strict-partition, or mesh premises were added. The source hash submitted for independent review is `d1590f0b5df2fec5986358b6d84c255a4535a90df0ac70b8bc5f4bbec9c6fcb0`. Production integration and chapter-wide validation remain the parent's responsibility.

The five public refinement theorem axiom checks contain only `propext`, `Classical.choice`, and `Quot.sound`. The parent independently read the entire proof, accepted its source fidelity, and built the integrated refinement module successfully.

## Subsequent authorized implementation: 6.5–6.7

The parent then assigned `rudin/Chapter06CriterionDraft.lean` with the full comparison, epsilon-gap equivalence, and three tagged-sum clauses. The 140-line draft compiled cleanly by 16:12 UTC (roughly three minutes). Its source hash is `e88daabe91d0ddd9145c79ff4aecbfd5c054b30fd27ea86c0a1b7743e3488715`.

The proof uses a common refinement to compare every lower sum with every upper sum, then the actual conditional-completeness approximation properties to establish the criterion. The tagged estimates retain the absolute value inside the weighted sum for two tags. The integral estimate explicitly assumes `RSIntegrable`; the refinement and two-tag clauses need only the source boundedness/monotonicity and the small partition gap. All results allow degenerate intervals and repeated points. The independent reviewer and parent received the stable file for their acceptance gates.
