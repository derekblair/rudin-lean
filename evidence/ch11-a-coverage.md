# Chapter 11 first-half coverage and downstream API

The source inventory in `ch11-a-inventory.md` lists all 45 numbered nodes.
This branch covers 11.1–11.23; lane B owns 11.24–11.45. All 23 first-half
numbered nodes have formal declarations. The ancillary narrative limitations
below are excluded from this numbered-node completion claim.

All declaration names below are in `Rudin.PMA.Chapter11`.

| Node | Main declarations / module |
|---|---|
| 11.1 | `SetRing`, `SigmaRing`, `pma11_1_inter`, `pma11_1_iInter` — Foundations |
| 11.2 | Extended-real admissibility, finite/countable additivity, `pma11_2_*` identities, `pma11_2_absolute_of_finite_total` — Foundations, SetFunctionSeries |
| 11.3 | `pma11_3` — Foundations |
| 11.4 | Mixed-endpoint intervals, elementary finite unions, product-volume formulas, decomposition independence, finite additivity, ring closure, disjoint decomposition, failure of sigma closure — Geometry, GeometryRing |
| 11.5 | `ContentRegular` — Construction |
| 11.6 | `pma11_6a`, all Stieltjes endpoint and degenerate formulas, `pma11_6b_regular`, `volumeRegularContent`, `stieltjesRegularContent` — Geometry, GeometryApproximation, StieltjesExample, Examples |
| 11.7 | `RegularContent.outer`, `outer_eq_iInf`, `outer_mono` — Construction |
| 11.8 | `RegularContent.outer_eq_content`, `outer_iUnion_le` — Construction |
| 11.9 | `RegularContent.setDistance`, `SetConverges`, `FinitelyMeasurable`, `RudinMeasurable` — Construction |
| 11.10 | `RegularContent.rudinMeasurable_sigmaRing`, `rudinMeasurable_iUnion_measure`, `finitelyMeasurable_iff`; native outer-value identifications — Construction, Examples |
| 11.11 | Open/closed measurability, closed/open approximation, Borel minimality and envelopes, Borel-plus-null decomposition, null sigma-ring, countable-null and Cantor results including stage volumes — Regularity, Euclidean, NullSets |
| 11.12 | `RingMeasureSpace`, measurable-space condition, native bridges, Lebesgue completion, counting and probability examples — Foundations |
| 11.13 | `MeasurableFunction`, `pma11_13_iff_measurable` — Measurable |
| 11.14 | `pma11_14`, `pma11_14_real` — Measurable |
| 11.15 | `pma11_15` — Measurable |
| 11.16 | `pma11_16` — Measurable |
| 11.17 | Sup/inf, upper/lower limits, extrema, positive/negative parts, pointwise-limit corollary — Measurable |
| 11.18 | `pma11_18`, `pma11_18_add_mul` — Measurable |
| 11.19 | `IsSimple`, `characteristic`, fiber decomposition, `simple_measurable_iff` — Simple |
| 11.20 | Arbitrary/measurable pointwise approximation, nonnegative monotone approximation, bounded uniform and simultaneous monotone/uniform approximation — Simple |
| 11.21 | `simpleIntegral`, range/fiber sum, `nonnegativeIntegral`, defining supremum, simple-function agreement — Integration |
| 11.22 | `IntegralDefined`, `lebesgueIntegral`, `LebesgueIntegrable`, finiteness equivalence, native real bridges — Integration |
| 11.23 | Bounded integrability, integral bounds, monotonicity, arbitrary real scaling, null sets, subset restriction — Integration |

## Source qualifications

1. **11.2:** a finite-value witness makes the set-function domain nonempty. The
   source's empty-set-value assertion presupposes this. `SetRing` itself retains
   the literal closure-only definition, including the empty family.
2. **11.4 and 11.11(f):** positive dimension is explicit for an empty interval,
   failure of sigma closure, and countable sets having zero volume. Dimension zero
   has a single point of volume one. Other geometry statements allow zero dimension.
3. **11.6(b):** the printed open-interval expression can be negative for a
   degenerate interval at a jump. `ENNReal.ofReal` supplies nonnegative outer
   values. Literal real formulas are proved for `a < b`; all degenerate cases are
   separate. Closed singletons retain the jump mass.
4. **11.9–11.10:** distances between arbitrary sets may be infinite. The code
   corrects the explanatory metric claim to an extended metric; an ordinary
   metric applies to the finite-measure component.
5. **General settings:** 11.14 also holds on any space with measurable opens. The
   construction works on a ring whose closed members are compact, with genuine
   elementary geometry and both examples proved and instantiated. It does not
   assume a countably additive input measure.
6. **11.21–11.23:** native lower integrals evaluate nonmeasurable functions, and
   native restrictions evaluate arbitrary integration sets. The source's intended
   domain remains measurable integrands and measurable sets. The signed expression
   is total in Lean; `IntegralDefined` specifies its integrand domain under the
   standing measurable-set convention. Some proofs give stronger statements:
   bounds and order apply to the total expressions, null-set values require no
   integrand measurability, and subset preservation holds for arbitrary subsets.
   Every source case is included, and these extensions are flagged in-code.
7. **Representations:** sequences start at zero; nonnegative quantities use
   `NNReal`/`ENNReal`, signed extended values use `EReal`; coordinate Euclidean
   space is `Fin p → ℝ`, with the supremum norm used in topological proofs.
   `extendedAbs` is proved equal to native extended absolute value. Simple
   approximation uses equivalent constructions instead of the source's particular
   dyadic algorithm. Native volume/Stieltjes measures verify the examples, and
   their outer values are proved equal to the countable-open-elementary-cover
   construction on every set.

## Ancillary material not formalized

- The unnumbered, externally referenced composition counterexample following
  11.18. The numbered continuous two-variable theorem and its sum/product cases
  are complete; this separate cautionary example is explicitly not claimed.
- The optional quotient-metric/closure interpretation following (29). The
  zero-distance setoid and distance estimates are proved, but no separate quotient
  metric instance or closure-identification theorem is constructed. The numbered
  sigma-ring and countable-additivity theorem does not depend on them.

## Downstream API

Import `Rudin.PMA.Chapter11`. Extended-real integration uses `positiveIntegral`,
`negativeIntegral`, `IntegralDefined`, `LebesgueIntegrable`, and
`lebesgueIntegral`. For real integrands, `lebesgueIntegrable_real_iff` and
`lebesgueIntegral_real` connect to Mathlib. `pma11_13_iff_measurable` connects the
source measurability criterion to native `Measurable`.

`RegularContent.extension` is the constructed measure; `extension_apply` equates
its values with `outer`. `volumeRegularContent_outer` and
`stieltjesRegularContent_outer` identify the named examples on all sets.

## Verification

`lake build Rudin.PMA.Chapter11 Rudin.PMA.Chapter11Audit` checks all modules and
23 groups of required declarations. The recursive audit visits every chapter
declaration, including private/generated declarations, and rejects all transitive
axioms except `propext`, `Classical.choice`, and `Quot.sound`. The exact final
build output is in `ch11-a-build.log`.
