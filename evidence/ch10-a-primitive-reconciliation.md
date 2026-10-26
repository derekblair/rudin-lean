# Reconciliation review: PMA 10.5–10.8

Reviewed recovered source from `origin/ch8-codex-20261022`, commit
`bb50a2079f8e189d8e282e2521bbadb64f4f98eb`, now copied into
`rudin/Rudin/PMA/Chapter10/Primitive.lean` and `Partition.lean`.
Read the printed statements directly in `/root/sources/pma3.pdf`, printed
pp. 248–251 (PDF pp. 257–260), and checked the definition of support at
10.3 and the meaning of `C(X)` at 7.14. This is a source/fidelity review;
the coordinating agent owns the isolated build and axiom-audit results.
The recovered modules remain byte-identical. After the source review found the
complex-valued omission, the coordinating agent authorized a separate supplement,
`PartitionComplements.lean`; this has been added and compiled as described below.

## Acceptance and coverage

- **10.5: substantive claims covered.** `pma10_5_contract` includes the
  coordinate formula, equivalence with the sum over unchanged coordinates,
  the Fréchet derivative, every derivative-matrix entry, the Jacobian, and
  the equivalence between invertibility and a nonzero distinguished partial.
  `pma10_5` proves these claims using derivative rules and an actual
  determinant calculation. `coordinatePartial` is the derivative along the
  standard coordinate line, and `Euclidean n` has the Euclidean norm.
  The domain-definition caveat below must be disclosed.
- **10.6: covered, including projection range and kernel.** The contract
  proves the equivalence between exchanging basis vectors and exchanging
  coordinates, the involution identity, the complete coordinate projection
  formula, `P₀ = 0`, `Pₙ = id`, and the specified spans for both range and
  kernel. The latter are proved by `coordinate_span_iff`,
  `prefixProjection_range`, and `prefixProjection_ker`; they are not merely
  definitions. The four-dimensional example is the specialization of
  `flipOperator_apply`/`flipOperator_coordinateVector` at indices 1 and 3
  in zero-based indexing, together with linearity. There is no separately
  named four-dimensional specialization, but the universal formulas include
  both versions of that example.
- **10.7: full nonlinear local factorization covered.** The theorem assumes
  only the printed regularity, domain, zero-value, and invertible-derivative
  conditions, plus the explicitly documented positive-dimension convention.
  It does not assume any factorization or an elimination oracle. The output
  has exactly `n` primitive factors and exactly `n - 1` flip-or-identity
  factors. `composeMaps` applies the rightmost function first, and the final
  list puts `B₁,…,Bₙ₋₁` before `Gₙ,…,G₁`, as required. Each primitive
  factor has its own open neighborhood of zero, is C¹ there, fixes zero,
  and has invertible derivative at zero. The final equality holds on an
  open neighborhood contained in the original domain.
- **10.8 theorem: covered.** The cover is arbitrary, compactness produces
  an actual finite subcover, and the returned continuous real functions
  have values in `[0,1]` globally, closed supports subordinate to the cover,
  and sum exactly to one on the compact set. `tsupport` agrees with the
  book's closed-support definition. Finite-subtype indexing is equivalent
  to a finite list; distinct cover indices are an innocuous stronger output.
- **10.8 corollary: covered by recovered real case plus new complex supplement.**
  The same partition is proved to decompose every continuous real-valued
  function supported on the compact set, globally, with continuity and
  the required support condition for each summand. However, the formal
  quantifier is `f : C(Euclidean n, ℝ)`. Rudin 7.14 defines `C(X)` for
  bounded complex-valued continuous functions, and 10.3 explicitly allows
  real or complex support. The unqualified `C(ℝⁿ)` in the printed corollary
  therefore also includes complex-valued `f`. No complex corollary is in
  the recovered `Partition.lean` or `PartitionProbes.lean`. The new
  `PartitionComplements.lean` now proves `pma10_8_complex_corollary`, reusing
  the proved finite partition to give the complex-valued decomposition,
  continuity of each product, and its closed-support inclusion. It does not
  assume the desired decomposition. Boundedness itself is not a gap:
  compact support and continuity imply it.

## Why the hard part of 10.7 is genuine

`fixesPrefix_derivative` differentiates the local fixed-coordinate identities.
`exists_remaining_pivot` uses injectivity of the derivative to obtain a
nonzero entry in the remaining column; it does not assume a nonzero diagonal.
`local_primitive_elimination` builds the primitive map and flip, obtains its
C¹ inverse from the proved Chapter 9 inverse-function theorem, constructs
the residual map, and checks its derivative invertibility and enlarged fixed
prefix. `factorization_remaining` performs strong induction, handles the
last coordinate with one primitive and no flips, and maintains the exact
factor counts and composition order. `pma10_7` then intersects the equality
neighborhood with the original open set. Existing probes exercise dimension
one and a plane flip whose diagonal pivot vanishes.

## Conventions/deviations requiring disclosure

1. `IsPrimitiveOn G E` is defined on arbitrary sets and does **not** include
   `IsOpen E`, although 10.5 introduces primitive maps on open domains.
   This is a generalization, not a lost theorem: `PrimitiveNearZero` and
   10.7 explicitly impose open neighborhoods. The current comment says
   there is no built-in regularity but does not explicitly identify the
   dropped openness premise. Add a source-adjacent explanatory comment or
   record the generalization clearly in the final report.
2. Maps and scalar coordinate functions are total ambient functions with
   assertions restricted to their domains. This is the usual extension
   representation of functions originally defined only on an open set;
   no global smoothness is imposed.
3. Coordinates use `Fin n`, hence start at zero. Prefix lengths and the
   source's one-based coordinate counts agree.
4. The factorization explicitly assumes `0 < n`; its source-adjacent
   comment already identifies this conventional positive-dimension scope.
   No theorem for the optional zero-dimensional extension is claimed.
5. The recovered 10.8 corollary is restricted to real-valued functions.
   The new complex supplement closes that gap and identifies the source
   notation in its adjacent comment. This is no longer a remaining omission
   when both modules are imported.

## Dependencies and validation boundary

`Primitive.lean` directly imports `Chapter09.Inverse` and
`Chapter09.Determinants`; both import `Chapter09.Differentiation`, which
imports `Chapter09.Linear`. `Partition.lean` directly imports
`Chapter09.Linear` and Mathlib's partition-of-unity module. The earlier
`Linear.lean` imports the earlier `Chapter08` umbrella, so the recovered
proofs require the prior Chapter 8 dependency closure too. These are real
source prerequisites, not optional conveniences or theorem assumptions.
The coordinating agent's reconciliation manifest identifies missing
other-lane files and a differing Chapter 8 umbrella; this review does not
claim that the native lane builds without them.

The earlier `C1On` definition is differentiability at every domain point
plus continuity of the total derivative; its proved equivalence with
`ContDiffOn ℝ 1` on open sets is used correctly. The inverse-neighborhood
result returns a genuine open partial homeomorphism, a C¹ inverse, and the
inverse derivative, with a proof rather than an axiom. The determinant
bridge likewise proves invertibility iff nonzero determinant.

Source inspection found no placeholder or assumed-conclusion shortcut in
these two recovered modules. Kernel-level build success and allowed-axiom
closure must be read from the coordinating agent's final validation logs,
not inferred from this source review.

## Supplement validation

`PartitionComplements.lean` was copied into the isolated reconciled source
snapshot and checked with:

```text
cd .lane-validation/rudin
lake env lean Rudin/PMA/Chapter10/PartitionComplements.lean
```

Result: exit 0, no diagnostics. This uses the pinned toolchain and recovered
prerequisite source graph. It does not remove the native-lane prerequisite
blocker. Final umbrella build and axiom audit remain with the coordinator.

## Additional authorized supplement: displayed 10.19 calculation

The recovered `ExactOneForms.lean` proves `x dy` is not exact by its nonzero
closed-circle integral, but omits the displayed computation of its exterior
derivative. The separate `ExactOneFormComplements.lean` now proves
`exteriorDerivative_coordinateOneForm` for arbitrary coordinate indices and
`pma10_19_xdy_derivative`, giving `d(x dy) = dx ∧ dy ≠ 0` at every point of
the plane. Nonvanishing is proved by evaluating on the two standard basis
vectors, which gives the determinant of the identity matrix.

Validation command in `.lane-validation/rudin`:

```text
lake env lean Rudin/PMA/Chapter10/ExactOneFormComplements.lean
```

Result: exit 0. The only diagnostic was an unused simp argument, subsequently
removed without changing the proof. Neither recovered source module was
modified. The coordinating agent should import and audit both new supplement
modules in its final assembled target.

Following independent review, `ExactOneFormComplements.lean` also now proves
`pma10_19_dxdy_not_formEqOn_zero`: the constant two-form `dx ∧ dy` is not
`FormEqOn` to zero on the whole plane. It first proves this constant field is
a continuous homogeneous two-form, then applies the proved 10.15 separation
equivalence between agreement of every actual surface integral and pointwise
agreement. Thus the nonzero claim is explicit in the book's operational sense,
not only in the exterior algebra. The updated entire supplement was checked
again by the same pinned `lake env lean` command: exit 0, no diagnostics.
