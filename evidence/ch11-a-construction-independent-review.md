# Independent review: geometry and integration

Reviewer: construction worker, separate from the authors of Geometry, GeometryRing, Simple, and Integration.
Source checked: PMA third edition, printed pages 302–305 and 313–315; PDF pages 311–314 and 322–324.
Only brief statements and findings are recorded here.

## Result

No missing numbered conclusion or invalid strengthening was found in the reviewed geometry and 11.19–11.23 statements. The general regular-content construction is independent of the already constructed measures used to verify the Lebesgue and Stieltjes examples.

## 11.4 and 11.6

- `IsInterval` preserves independently open or closed endpoints in every coordinate. It requires nonnegative side lengths and permits degenerate boxes.
- `IsElementary` is literally a finite union of those boxes. The empty finite union also treats dimension zero correctly.
- GeometryRing proves the set ring property and finite disjoint interval decompositions; it does not replace elementary sets with all bounded Borel sets.
- The interval product formula, disjoint sum formula, and independence of decomposition establish agreement of `elementaryVolume` with the book's geometric definition, although the Lean representative is native volume.
- Failure of countable-union closure correctly requires positive dimension. Dimension zero is an exceptional case of the API and does not support the claimed counterexample.
- The Stieltjes endpoint formulas correctly use one-sided limits. Taking the right-continuous regularization of the monotone function is a faithful implementation of the four formulas.
- The printed formula for a degenerate open interval can be negative at a jump. The implementation explicitly repairs this with `ENNReal.ofReal`, and gives the literal real formula under strict endpoint order. Closed singleton intervals carry the jump; the other three degenerate intervals are empty.
- `GeometryApproximation.elementary_measure_regular` proves elementary closed/open approximation for every locally finite measure, including atomic measures. This supplies regularity of the Stieltjes example. Its proof does not discard boundary faces or use the volume-specific null-boundary argument.

## 11.19–11.20

- `IsSimple` means finite range only. It does not silently require measurability.
- Characteristic functions, the finite fiber decomposition, and the equivalence with measurability of fibers are all present.
- Pointwise approximation includes arbitrary nonmeasurable real functions. The temporary top sigma algebra is only a proof device; the exported theorem imposes no measurability premise.
- The nonnegative case includes increasing nonnegative approximations, with and without measurability.
- The bounded case includes uniform approximation. The bounded nonnegative case has one sequence satisfying monotonicity, uniform convergence, and conditional measurability simultaneously.

## 11.21–11.23

- Nonnegative simple functions use finite `NNReal` values; infinity is admitted for general nonnegative integrands and integral values.
- The simple-integral sum is expressed on disjoint fibers, and the general nonnegative integral has the required supremum over finite-valued measurable simple functions.
- Signed integrands retain both infinities through `EReal`. `IntegralDefined` distinguishes existence with one finite part from `LebesgueIntegrable`, which requires both parts finite.
- Finiteness of a defined integral is proved equivalent to integrability. The native real integral is supplied only as a compatibility theorem, not a restriction of the signed theory.
- All six 11.23 clauses are represented: bounded integrability, constant bounds, order, multiplication by every finite real scalar, null-set integrals, and restriction of integrability.
- Lean expressions also have values for arbitrary integration sets. The module now explicitly says that the book's domain assumes a measurable integration set. Their meaning outside that domain is an API totalization.
- The nonnegative integral also accepts nonmeasurable functions as a native lower-integral totalization. The root has been asked to state this explicitly beside 11.21 and include it with the totalization notes.

## Ancillary limitation outside the reviewed numbered conclusions

The unnumbered illustration after 11.18, asserting the existence of a Lebesgue measurable function and a continuous real function with nonmeasurable composition, is explicitly recorded as unproved in Measurable.lean. It must remain disclosed; the numbered continuous two-variable composition theorem and its sum/product cases are present.

## Verification performed by this worker

- `lake build Rudin.PMA.Chapter11.Construction`: success, 8925 jobs, no warnings in the final run.
- All 48 explicit Construction declarations: `#print axioms` reports only `propext`, `Classical.choice`, and `Quot.sound`.
- `lake build Rudin.PMA.Chapter11.GeometryApproximation`: success, 8926 jobs, no warnings.
- All four GeometryApproximation declarations: same allowed-axiom result, recorded in `ch11-a-geometry-approximation-axioms.lean` and `.txt`.
- The two owned source modules contain no admissions or custom axioms.

Construction's explicit source correction is retained: symmetric-difference outer measure can be infinite, so the quotient of all subsets carries an extended metric. An ordinary metric requires the finite-measure component.
