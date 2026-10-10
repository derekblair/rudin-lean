# Chapter 6: bounded prior-art and infrastructure study

Date: 2026-10-10. Read current isolated `PROGRAM.md`; examined local Mathlib pinned at `d13f23b723b8a846827a245b89c10fc7d3f11612`. Read-only investigation plus this evidence file only. No implementation, dependency changes, source imports from the network, book copying, sessions, commits, or production changes.

**Finding:** reusable partition/order infrastructure exists, but this scan found no ready-made pinned Lean definition of Rudin's general closed-cell Darboux–Stieltjes integral. Verified Mizar prior art exists; its mesh-limit definition is not automatically equivalent to the requested Darboux/refinement definition.

## Verified public primary prior art

- Mizar [INTEGR22](https://mizar.uwb.edu.pl/version/current/html/integr22.html), by Narita, Nakasho and Shidama, received 2016: definition 1 uses actual integrator endpoint increments; definitions 3–7 develop bounded variation and tagged sums; definition 8 quantifies over all division sequences whose mesh tends to zero. Tags range over closed cells, as confirmed in [INTEGRA1 definition 4](https://mizar.uwb.edu.pl/version/current/html/integra1.html). This is relevant general-integrator formalization, including monotone integrators as a bounded-variation case; it is not a Lean import or a checked equivalence with the source's Darboux definition.
- Mizar [INTEGR23 theorem 21](https://mizar.uwb.edu.pl/version/current/html/integr23.html) proves integrability of a continuous integrand against a bounded-variation integrator on a closed interval. This supplies a verified prior-art comparator for the continuous-integrand existence theorem, not complete Chapter 6 coverage.
- Public Mathlib [partition documentation](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/BoxIntegral/Partition/Basic.html), [integration-filter documentation](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/BoxIntegral/Partition/Filter.html), and [Stieltjes-measure documentation](https://leanprover-community.github.io/mathlib4_docs/Mathlib/MeasureTheory/Measure/Stieltjes.html) corroborate the local interfaces below. Implementation decisions should use the pinned local source, since public documentation can advance.

Search boundary: targeted public queries for Lean/Mathlib, Coq, Isabelle/AFP and Mizar Riemann–Stieltjes formalization; direct inspection of the primary Mizar sources and Mathlib interfaces. No matching general Darboux–Stieltjes Lean implementation was verified in this bounded search. This is not a claim of novelty or an exhaustive absence result. Secondary search hits were used only to locate primary sources.

## Pinned reusable interfaces

Paths below are relative to `rudin/.lake/packages/mathlib/Mathlib/`.

| Need | Local interface | Fit and limitation |
| --- | --- | --- |
| Common refinements | `Analysis/BoxIntegral/Partition/Basic.lean`: `Prepartition.inf_def`, `IsPartition.inf`, `restrict`, `IsPartition.restrict`, `biUnion`, `sum_biUnion_boxes` | Finer partitions are smaller in its order. Coerced boxes are half-open, but `Box.Icc` supplies closed cells for extrema. |
| Explicit inserted cuts | `Analysis/BoxIntegral/Partition/Split.lean`: `splitMany`, split/refinement lemmas | Finite cuts and coverage infrastructure already exists. |
| Actual alpha increments | `Analysis/BoxIntegral/Partition/Additive.lean:137`: `BoxAdditiveMap.ofMapSplitAdd`; `sum_partition_boxes`; `toSMul` | In dimension one, content `α(upper)-α(lower)` is split-additive by telescoping without continuity. Nonnegativity follows separately from `MonotoneOn α` on the ambient interval. Construction has not yet been implemented. |
| Closed-cell tags | `Analysis/BoxIntegral/Partition/Tagged.lean:197`: `TaggedPrepartition.IsHenstock` | Tags lie in each `J.Icc`, including both endpoints. The bare tagged-prepartition structure only restricts tags to the ambient closed box. |
| Supremum/infimum bounds | `Order/ConditionallyCompleteLattice/Basic.lean`: `le_csSup`, `csSup_le`, `csInf_le`, `le_csInf`, `csSup_le_csSup`, dual infimum lemmas, `exists_lt_of_lt_csSup` | Use on `f '' Icc l u`, with explicit nonemptiness and boundedness. These are general order tools, not existing Darboux sums. |
| Finite ordered cuts | `Data/Finset/Sort.lean`: `orderEmbOfFin`, membership/range/min/max lemmas | Alternative direct one-dimensional partition representation; union of finite cut sets gives common refinement. |

The library's `Analysis/Calculus/Darboux.lean` concerns the derivative intermediate-value theorem, not Darboux integration. Content searches for upper/lower Darboux sums and Riemann–Stieltjes definitions found no dedicated source-facing layer. `Order/Interval/Finset/Gaps.lean` handles complements of disjoint closed intervals; it may help later but does not itself represent adjacent closed-cell partitions.

## Two decisive semantic checks

These are elementary mathematical diagnostics for the architecture, not new Lean claims.

1. **Right-limit normalization changes endpoint increments.** Pinned `MeasureTheory/Measure/Stieltjes.lean:112` bundles monotonicity and right continuity. `Monotone.stieltjesFunction` at line 220 replaces `α` by `rightLim α`. For `α(x)=0` when `x≤0` and `1` when `x>0`, the constant integrand `1` on `[0,1]` has source value `α(1)-α(0)=1`; the normalized Stieltjes measure gives `(0,1]` mass zero. Therefore directly replacing arbitrary `α` by that measure loses source endpoint information. A measure bridge would need a separate exact theorem and endpoint treatment.

2. **Uniform mesh and refinement convergence differ in general.** On `[0,1]` choose interior `c`, `α(x)=1` for `x>c` and zero otherwise, and `f(x)=1` for `x≥c` and zero otherwise. Every partition containing `c` has closed-cell upper and lower sums both equal to `1`: the left jump cell has zero alpha increment and the right one has constant integrand `1`. Arbitrarily fine partitions that straddle `c` still admit tagged sums `0` or `1`. Thus the source Darboux/refinement value exists while the all-small-mesh tagged limit fails. Pinned `IntegrationParams.Riemann` uses a constant mesh bound; neither it nor Mizar's mesh-limit predicate can be silently substituted for the general source definition.

## Architecture recommendation

Keep the reviewed source definition explicit: real bounded `f`, arbitrary `MonotoneOn α (Icc a b)`, strictly ordered finite partitions, extrema over each **closed** cell, and weights using the actual `α` values. Establish weight nonnegativity/telescoping, lower≤upper, monotonicity under refinement, common refinement, bounded/nonempty sum ranges, and the upper-minus-lower epsilon criterion before later chapter results.

Two viable representations remain: a small direct finite-cut structure, or one-dimensional `BoxIntegral.Prepartition` with extrema on `Box.Icc` and its already-proved refinement machinery. The second saves partition lemmas but needs a verified ordered-partition correspondence and one-dimensional coordinate adapters. Treat Mathlib's integral or measure as a later comparator under proved hypotheses. No decision here authorizes an implementation before independent statement review.

Findings, exact reusable names, the verified Mizar references, and both semantic diagnostics were sent to the root and the `completion_evidence` architecture agent during this investigation. All existing Chapter 5 source and evidence were preserved.
