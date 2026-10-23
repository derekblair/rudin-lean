# Chapter 10.31 continuous boundary forms: API research

Independent reviewer: ch8_fidelity. No implementation or build was performed.
All library paths below are relative to `rudin/.lake/packages/mathlib/Mathlib/`.

The source at printed pp.270–271 asserts parametrization independence for
every continuous boundary-degree form. C1-only equality is an intermediate
step, not the complete source statement. The Jacobian is required positive
only in the interior; boundary degeneracy must remain allowed.

The final paragraph on printed p.271 treats an arbitrary 2-surface with the
unit square as parameter domain. By the 10.10 convention this means C1. Its
integration functional equals the sum of its two triangle compositions, and
the oriented boundary consists of its four outer edge compositions. A direct
finite sum of genuine C1 Surface integrals preserves that scope; the C2
specialization can additionally use the C2Simplex chainBoundary API.

## Direct smooth approximation route

Use `Analysis/Calculus/BumpFunction/SmoothApprox.lean`, not a new
Stone–Weierstrass construction. In the following declarations E is a real
finite-dimensional normed vector space and F is a real Banach space:

```lean
ContinuousMap.dense_setOfPred_contDiff :
  Dense {f : C(E, F) | ContDiff ℝ ∞ f}

UniformContinuous.exists_contDiff_dist_le
  (hf : UniformContinuous f) (hε : 0 < ε) :
  ∃ g : E → F, ContDiff ℝ ∞ g ∧ ∀ a, dist (g a) (f a) < ε

Continuous.exists_contDiff_dist_le_of_forall_mem_ball_dist_le
  (hf : Continuous f) (hε : 0 < ε) :
  ∃ g : E → F, ContDiff ℝ ∞ g ∧ ∀ a, ∀ δ,
    (∀ x ∈ Metric.ball a ε, dist (f x) (f a) ≤ δ) →
    dist (g a) (f a) ≤ δ
```

The density theorem uses compact convergence. Its proof expands precisely the
neighborhood basis needed for a compact K and a positive approximation error:

```lean
mem_closure_iff_nhds_basis
  (nhds_basis_uniformity
    uniformity_basis_dist.compactConvergenceUniformity)
```

This yields a smooth g uniformly ε-close to a chosen global continuous F on
K. There is no need to extract a sequence or to assume global uniform
continuity. An alternative direct route, already used inside that library
proof, is uniform continuity of F on `Metric.cthickening 1 K`, followed by
the third declaration above with a sufficiently small ball radius.

To obtain the global continuous extension, use
`Topology/TietzeExtension.lean`:

```lean
ContinuousMap.exists_restrict_eq
  (hs : IsClosed s) (f : C(s, Y)) :
  ∃ (g : C(X, Y)), g.restrict s = f

Pi.instTietzeExtension : TietzeExtension (∀ i, Y i)
```

The ambient X must be a normal space and Y must satisfy TietzeExtension.
Euclidean space is normal, real scalars have the required extension instance,
and the Pi instance permits extension of the entire finite coefficient tuple.

Let K be the compact union of the images of all boundary faces under the two
parametrizations. For a degree k form take `ι := StandardIndex n k` and extend
the continuous map

```lean
fun x : K => fun S : ι => formCoefficient ω S.val x
```

to a global map into `ι → ℝ`. This is a finite-dimensional Banach codomain.
Smoothly approximate it on K and reconstruct the form as

```lean
fun x => ∑ S : ι, g x S • standardWedge S
```

This construction remains homogeneous of the required degree. Component
evaluation of g is smooth; finite coefficient expansion gives IsCFormOn.
Uniform error in the finite Pi norm implies the same error for each standard
coefficient. Empty coefficient index types cause no mathematical exception.

## Passing from C1 equality to continuous equality

For each fixed boundary face Φ, write its native integrand using standard
coefficients. The weights

```lean
fun u => evaluateForm k
  (fun j => fderiv ℝ Φ.map u (Pi.single j 1)) (standardWedge S)
```

are continuous on the compact parameter simplex. The existing
`continuousOn_evaluateForm_basis` and `Surface.continuousOn_integrand` APIs
provide the continuity ingredients. Therefore each weight is integrable and
its absolute-value integral is finite. Coefficient error at most δ bounds the
integrand error by δ times the finite sum of the absolute weights.

Use the proved native bridge `simplexRIntegral_eq_integral` only after native
existence from `ParameterDomain.integrable_of_continuousOn`. The relevant
quantitative library bounds in `MeasureTheory/Integral/Bochner/Basic.lean` are:

```lean
MeasureTheory.norm_integral_le_of_norm_le
  (hg : Integrable g μ) (h : ∀ᵐ x ∂μ, ‖f x‖ ≤ g x) :
  ‖∫ x, f x ∂μ‖ ≤ ∫ x, g x ∂μ

MeasureTheory.norm_integral_le_of_norm_le_const [IsFiniteMeasure μ]
  (h : ∀ᵐ x ∂μ, ‖f x‖ ≤ C) :
  ‖∫ x, f x ∂μ‖ ≤ C * μ.real Set.univ
```

Sum these estimates over the finitely many faces with the absolute integer
multiplicities. A fixed nonnegative bound C results. Choosing the coefficient
approximation error smaller than ε/(C+1) proves convergence of both boundary
integration functionals, and hence extends their equality from smooth forms
to the original continuous form. This epsilon argument avoids additional
sequence/filter bookkeeping and never needs derivatives of the original
continuous coefficients.

An alternative sequence argument is available through
`MeasureTheory.tendsto_integral_of_dominated_convergence` in
`MeasureTheory/Integral/DominatedConvergence.lean`: coefficient approximants
within one of their targets are dominated by the fixed continuous target
coefficients plus one, times the fixed absolute weight sum. The native
integrability obligations still precede that measure bridge.

This note addresses only the extension from C1 forms to continuous forms.
The C1 parametrization-independence proof must separately justify equality of
the interior top-degree integrals with the allowed boundary degeneracy; it
must not assume a C1 inverse at boundary points.

## Avoiding an inverse at degenerate boundary points

The existing `MeasureTheory/Function/Jacobian.lean:1213` API, already used by
SimplexChangeOfVariables, is stronger than needed for this issue:

```lean
MeasureTheory.integral_image_eq_integral_abs_det_fderiv_smul μ
  (hs : MeasurableSet s)
  (hf' : ∀ x ∈ s, HasFDerivWithinAt f (f' x) s x)
  (hf : Set.InjOn f s) (g : E → F) :
  (∫ x in f '' s, g x ∂μ) =
    ∫ x in s, |(f' x).det| • g (f x) ∂μ
```

It requires neither a nonzero derivative determinant nor an inverse at any
point of the closed measurable set. Apply it directly to the closed standard
simplex. Positivity on the interior and continuity of the determinant give
nonnegativity on the closure of the interior, which is the whole simplex.
The pertinent convex-set API is
`Convex.closure_interior_eq_closure_of_nonempty_interior` in
`Analysis/Convex/Topology.lean:261`. Closedness then removes the final closure.
Thus the absolute determinant can be replaced by the oriented determinant
without excluding degenerate boundary points or proving their images null.

## Finite unions of positive regions

Pinned API reconnaissance (read-only, no build): the required null-image result is already available directly, so local Lipschitz estimates and a finite neighborhood cover are unnecessary.

- `Mathlib/Analysis/Convex/Measure.lean:35`: `Convex.addHaar_frontier (μ : Measure E) (hs : Convex ℝ s) : μ (frontier s) = 0`, with the usual finite-dimensional real normed/Borel/additive-Haar instances. Apply to `convex_standardSimplex n` and `volume`.
- `Mathlib/MeasureTheory/Function/Jacobian.lean:556`: `addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero (hf : DifferentiableOn ℝ f s) (hs : μ s = 0) : μ (f '' s) = 0`. Here domain and codomain are the same finite-dimensional space, exactly as for `C2Simplex.coordinateMap`. Restrict the existing derivative on the open neighborhood to the frontier of the closed parameter simplex. This theorem does not require measurability of the null set or invertibility of its derivatives.
- `Mathlib/Topology/ContinuousOn.lean:580`: `ContinuousOn.image_closure` gives `f '' closure s ⊆ closure (f '' s)` when f is continuous on the closure. Together with compactness of the carrier, the dense-interior simplex lemma and the open-image theorem, this proves the carrier is the closure of its open image of the parameter interior. The root's current PositiveRegions proof follows this route correctly.
- The image of the parameter interior is open and lies in the carrier, hence lies in its interior. Since the carrier is closed, every point of its frontier is therefore the image of a parameter-frontier point. The two null-frontier APIs above show that the coordinate carrier frontier is null. No positive Jacobian assumption at boundary points is needed.
- `Mathlib/MeasureTheory/Constructions/BorelSpace/Basic.lean:454`: `interior_ae_eq_of_null_frontier (h : μ (frontier s) = 0) : interior s =ᵐ[μ] s`.
- `Mathlib/MeasureTheory/Integral/Bochner/Set.lean:76`: `setIntegral_congr_set (hst : s =ᵐ[μ] t)` replaces a set of integration by an almost-everywhere equal set.
- The same file, line 120: `integral_biUnion_finset (t : Finset ι) (hs : ∀ i ∈ t, MeasurableSet (s i)) (h's : Set.Pairwise (↑t) (Disjoint on s)) (hf : ∀ i ∈ t, IntegrableOn f (s i) μ)` identifies the integral over the finite union with the sum. Apply to the genuinely disjoint open interiors, and use their almost-everywhere equality with the carriers both termwise and on the finite union. Integrability is inherited from continuity on each compact carrier.
- An alternative induction can use `setIntegral_union₀ (hst : AEDisjoint μ s t) (ht : NullMeasurableSet t μ) (hfs : IntegrableOn f s μ) (hft : IntegrableOn f t μ)`. Pairwise disjoint interiors imply carrier intersections are contained in the union of the two null frontiers. The older name `integral_union_ae` is deprecated in this pin.

These are proof aids for actual native surface integrals: native existence must continue to be established before applying their already-proved set-integral bridge. The smooth approximation argument above then transfers the finite-union boundary equality from C1 to all continuous forms.
