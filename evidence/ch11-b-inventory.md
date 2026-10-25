# Chapter 11 second-half source inventory

Source: the supplied third-edition PMA PDF at
`/home/derekblair/projects/math/references/sources/pma3.pdf` (the brief's old
`~/sources/pma3.pdf` path no longer exists). Printed pp. 300–332 correspond to
PDF pp. 309–341. The main text contains 45 consecutive numbered nodes,
11.1–11.45. The fetched `evidence/ch11-a-inventory.md` assigns the first 23
nodes to lane A and the remaining 22, **11.24–11.45**, to this lane. Attached
unnumbered corollaries belong to the preceding numbered theorem; end-of-chapter
exercises are outside this numbered-node inventory.

This is an inventory of obligations, not a claim that every obligation below
has been formalized. The lane report records actual completion and gaps.

## Full numbered-node list

| Node | Printed page | Kind and short topic | Lane |
|---|---:|---|---|
| 11.1 | 301 | Definition: rings and sigma-rings of sets | A |
| 11.2 | 301–302 | Definition: extended-real additive set functions and elementary identities | A |
| 11.3 | 302 | Theorem: continuity under increasing unions | A |
| 11.4 | 302–303 | Definition: intervals, elementary sets, volume; decomposition properties | A |
| 11.5 | 303 | Definition: regular additive set function | A |
| 11.6 | 303–304 | Examples: volume and Stieltjes content regularity | A |
| 11.7 | 304 | Definition: outer measure from open elementary coverings | A |
| 11.8 | 304–305 | Theorem: extension and countable subadditivity | A |
| 11.9 | 305 | Definition: symmetric difference, distance and measurability | A |
| 11.10 | 305–308 | Theorem: measurable sigma-ring and countably additive measure | A |
| 11.11 | 309 | Remarks: regularity, Borel sets, null sets, Cantor example | A |
| 11.12 | 310 | Definition: measure and measurable spaces, with examples | A |
| 11.13 | 310 | Definition: measurable extended-real function | A |
| 11.14 | 310 | Example: continuous functions are measurable | A |
| 11.15 | 311 | Theorem: four equivalent level-set criteria | A |
| 11.16 | 311 | Theorem: measurable absolute value | A |
| 11.17 | 311–312 | Theorem: measurable suprema, infima, upper/lower limits; corollaries | A |
| 11.18 | 312–313 | Theorem: continuous composition of two measurable real functions | A |
| 11.19 | 313 | Definition: simple and characteristic functions | A |
| 11.20 | 313–314 | Theorem: simple approximation, including measurable/monotone variants | A |
| 11.21 | 314 | Definition: nonnegative simple and measurable integrals | A |
| 11.22 | 314–315 | Definition: extended signed integral and integrability | A |
| 11.23 | 315 | Remarks: six elementary integral properties | A |
| 11.24 | 315–317 | Theorem: countable additivity of set integrals; corollary | B |
| 11.25 | 317 | Remarks: almost-everywhere equality, invariance and finiteness | B |
| 11.26 | 317–318 | Theorem: absolute integrability and integral bound | B |
| 11.27 | 318 | Theorem: integrability from an integrable majorant | B |
| 11.28 | 318–319 | Theorem: monotone convergence | B |
| 11.29 | 319–320 | Theorem: integrability and integral of a sum | B |
| 11.30 | 320 | Theorem: interchange nonnegative series and integral | B |
| 11.31 | 320–321 | Theorem: Fatou inequality | B |
| 11.32 | 321–322 | Theorem: dominated convergence; bounded convergence corollary | B |
| 11.33 | 323–324 | Theorem: Riemann/Lebesgue comparison and continuity criterion | B |
| 11.34 | 326 | Definition: complex square integrability and norm | B |
| 11.35 | 326 | Theorem: Schwarz inequality and integrable product | B |
| 11.36 | 326 | Theorem: sum in L2 and triangle inequality | B |
| 11.37 | 326 | Remark: metric on the quotient by almost-everywhere equality | B |
| 11.38 | 326–327 | Theorem: continuous functions dense in interval L2 | B |
| 11.39 | 327–328 | Definition: orthonormal functions and Fourier coefficients | B |
| 11.40 | 328 | Theorem: trigonometric L2 convergence and Parseval; uniqueness corollary | B |
| 11.41 | 329 | Definition: convergence and Cauchy sequences in L2 | B |
| 11.42 | 329–330 | Theorem: completeness of L2 | B |
| 11.43 | 330–331 | Theorem: Riesz–Fischer | B |
| 11.44 | 331 | Definition: complete orthonormal system | B |
| 11.45 | 331–332 | Theorem: Parseval for complete orthonormal systems | B |

## Reconciliation and dependency boundary

The initial main revision was `87344489d0a8ce7fe00a37ef846a72fc70d33735`.
Its `Chapter11.lean` was the scaffold originating at `e179c39`; it did not
implement Chapter 11. Root's remote/PR inspection found no Chapter 11
implementation in `origin/ch8-codex-20261022` or PRs 1 and 2 (merged Chapter 8
work). The first-half branch is the source of truth for 11.1–11.23, and its
inventory fixes the split above. It is imported, not reimplemented here.

At the initial first-half rebase, the available module was
`Rudin.PMA.Chapter11.Measurable`, covering the measurable-function foundation;
native definitions for 11.21 and 11.22 had not yet landed. In particular,
`MeasurableFunction : (X → EReal) → Prop` is bridged to mathlib measurability
by `pma11_13_iff_measurable`, with a real-valued bridge
`pma11_13_real_iff_measurable`. Later integration against first-half definitions
must be recorded in the lane report; importing a foundation is not itself a
proof that its pending nodes are complete.

## Second-half fidelity obligations

- **11.24:** (a) The integral of a nonnegative measurable function defines a
  countably additive set function, including infinite values. (b) The same
  holds for a globally integrable signed function. The corollary identifies
  integrals on measurable sets whose difference is null. Covering only finite
  real integrals omits (a)'s infinite case and the extended-integral corollary.
- **11.25:** Define equality almost everywhere on a set, prove its reflexive,
  symmetric and transitive laws, and show integral invariance on every
  measurable subset when the integrals exist. Include the assertion that an
  integrable extended-real function is finite almost everywhere. For an
  everywhere real-valued function the latter assertion is tautological and
  does not replace the source assertion.
- **11.26:** Absolute value preserves integrability, and the absolute value
  of the signed integral is bounded by the integral of the absolute value.
  The source permits extended-real measurable representatives, finite almost
  everywhere. The complex extension is explained on printed p. 325.
- **11.27:** A measurable function dominated in absolute value by an integrable
  function is integrable. Domination is on the integration set, not necessarily
  the whole ambient space; using a restricted measure preserves this scope.
- **11.28:** An increasing nonnegative measurable sequence and its pointwise
  limit have convergent integrals; the limit may be positive infinity. A
  supremum formulation needs a bridge to the source's pointwise-limit form.
- **11.29:** Integrable summands have an integrable sum and additive integral.
  The printed formula is addition (visually verified), despite the OCR's
  occasional minus sign. Extended representatives require care at points
  where opposite infinities would make the sum undefined.
- **11.30:** The integral of a nonnegative measurable series is the sum of
  its integrals, allowing infinity. The sum function and its measurability
  should be represented; a finite-integral version alone is narrower.
- **11.31:** The integral of the pointwise lower limit of a nonnegative
  measurable sequence is bounded by the lower limit of its integrals.
  Both lower limits and integrals may be infinite.
- **11.32:** With an integrable majorant, the pointwise limit is integrable
  and the integrals converge. Include the stated almost-everywhere variant
  and the finite-measure, uniformly bounded convergence corollary. A theorem
  giving only convergence without integrability conclusions omits a stated
  consequence in the proof. The strict-measurability issue below matters for
  the almost-everywhere variant.
- **11.33:** (a) Riemann integrability gives Lebesgue integrability and equality
  of the two actual integrals. (b) A bounded function is Riemann integrable
  exactly when it is continuous almost everywhere. This requires the repo's
  Riemann definitions or a proved bridge, and completed Lebesgue measurability;
  a Borel-measurability assumption would narrow the source statement.
- **11.34:** Complex measurable raw functions with finite integral of squared
  norm, and the square-root norm formula. Printed p. 325 also supplies the
  prerequisite complex integral via real and imaginary parts. An L2 quotient
  encoding needs an explicit correspondence to these raw-function definitions.
- **11.35:** Both product integrability and the Schwarz integral bound.
- **11.36:** Both closure of L2 under addition and the triangle inequality.
- **11.37:** The pseudometric laws on raw functions, zero distance iff equality
  almost everywhere, and the induced quotient metric.
- **11.38:** For every L2 function on a compact real interval and positive
  tolerance, a function continuous on that interval approximates it in L2.
- **11.39:** Integral orthonormality with complex conjugation; each function
  belongs to L2; Fourier coefficients use the same convention. The following
  paragraph extends the trigonometric definition and recalls least-square
  approximation and Bessel's inequality for L2.
- **11.40:** Symmetric trigonometric partial sums converge in L2, the correctly
  normalized Parseval identity holds, and vanishing coefficients imply norm
  zero (hence uniqueness modulo null sets). An arbitrary Hilbert-basis theorem
  alone does not identify the trigonometric basis or its normalization.
- **11.41:** Norm convergence and the explicit eventual two-index Cauchy
  criterion, corresponding to the source's sequence definitions.
- **11.42:** Every L2 Cauchy sequence converges to an L2 function. A quotient
  completeness instance is useful with the raw-function bridge of 11.34/11.37.
- **11.43:** Square-summable prescribed coefficients of an orthonormal sequence
  produce an L2 limit of its finite sums, with those same Fourier coefficients.
- **11.44:** Completeness is defined by vanishing Fourier coefficients forcing
  norm zero; an alternative closed-span definition needs an equivalence proof.
- **11.45:** Parseval for a system complete in the sense of 11.44 and every L2
  function. The concluding correspondence with square-summable sequences
  follows using 11.43 and uniqueness.

## Measurability and completion cautions

The source's general measurable space after 11.12 need not carry a complete
measure. Consequently an arbitrary modification on a null subset need not be
strictly measurable. The pointwise limit of measurable functions is measurable,
but an arbitrarily assigned almost-everywhere limit only has an almost-everywhere
measurable representative. The informal assertion in the proof of 11.42 that
values at remaining points do not matter needs this qualification. It can be
handled by choosing a measurable representative, by assuming completion where
needed, or by explicitly using almost-everywhere measurability and documenting
the encoding. This also applies to the almost-everywhere extension of 11.32.

Mathlib's Bochner `Integrable` uses almost-everywhere strong measurability and a
finite norm integral, and its total real/complex integral returns zero outside
integrability. It cannot silently stand for the extended signed integral of
11.22. Mathlib's nonnegative `lintegral` does retain positive infinity; EReal
positive/negative parts and the finiteness bridge are necessary to account for
the source's signed extended representatives. These observations identify review
obligations, not completed bridge proofs.

Source review used text extraction for the whole chapter and visual checks of
printed pp. 315 and 319 to disambiguate formulas; no extended book passages are
stored in this inventory.
