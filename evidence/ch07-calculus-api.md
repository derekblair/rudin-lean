# Chapter 7 calculus API preparation

Status: mathematical/API study, 2026-10-10, followed by authorized implementation after independent contract acceptance. The API study was completed before the Chapter 7 inventory was supplied. The accepted inventory and typed contracts were then independently reviewed; full proofs of 7.16 and 7.17 now compile. The root authorized publication of the exact frozen draft as `rudin/Rudin/PMA/Chapter07/Calculus.lean`, and its module build passed. No book content was copied. These results are recorded in the completion addendum below; the preceding study remains an account of the API reasoning before implementation.

## Environment and scope

- Workspace: `/home/derekblair/Documents/Codex/2026-10-10/task/rudin-ch05-isolated`.
- Lean: `leanprover/lean4:v4.34.1`.
- Mathlib revision from `rudin/lake-manifest.json`: `d13f23b723b8a846827a245b89c10fc7d3f11612`.
- Mathlib paths below are relative to `rudin/.lake/packages/mathlib/Mathlib/`; native paths are relative to `rudin/`.
- Scope: uniform limits and the existing native Darboux/Stieltjes integral; differentiation with uniform convergence of derivatives and convergence at one point; ordered series corollaries. Oscillation owns broader public prior art, and its child owns compactness/Ascoli/Stone–Weierstrass APIs. Those searches were not duplicated.
- Preservation: no Chapter 5, Chapter 6, Rudin root, production, Git, installation, global configuration, credential, or session-control writes. Two Lean stdin clients contained only imports, namespace openings, and `#check` commands.

## Decision

The native uniform-limit integration bridge can be proved directly from Chapter 6's Darboux gap criterion and integral bound. This retains integrable approximants that need not be continuous and arbitrary monotone integrators without a continuity convention.

The pinned derivative-limit APIs are useful for the interior, but their open-set hypotheses do not preserve closed-interval endpoint derivatives automatically. A small direct mean-value/little-o argument on the closed interval is the recommended missing bridge. It avoids assuming that derivatives are continuous, bounded, or Riemann integrable.

Use Chapter 3's ordered partial sums for ordinary series. Mathlib's `SmoothSeries` theorems require summable majorants and default unconditional `Summable`, which are stronger assumptions than general uniform convergence of derivative partial sums and ordinary convergence at one point.

## Existing native integration API

All names in this section are in `Rudin.PMA.Chapter06`.

`Basic.lean:46–55` defines

```lean
RSIntegrable f α a b :=
  a ≤ b ∧ BoundedOn f a b ∧ MonotoneOn α (Icc a b) ∧
    lowerIntegral f α a b = upperIntegral f α a b
RSIntegral f α a b := lowerIntegral f α a b
```

`BoundedOn f a b` is an absolute bound on every point of `Icc a b`. Cells are closed intervals; `Partition.weight α i` is the endpoint increment of α. The integral value is totalized: its meaningful use must follow an integrability proof. Do not substitute a measure integral or infer integrability from convergence of these totalized values.

| Existing declaration | Exact useful assumptions and result |
| --- | --- |
| `rsIntegrable_iff_gap`, `Criterion.lean:36` | Given `hab : a ≤ b`, `BoundedOn f a b`, `MonotoneOn α (Icc a b)`, native integrability is equivalent to `∀ ε > 0, ∃ P, upperSum f α P - lowerSum f α P < ε`. |
| `cellLower_le_value`, `value_le_cellUpper`, `Basic.lean:118,123` | Given global interval boundedness and membership in a cell, bound the function value between the native cell infimum and supremum. |
| `cell_gap_le_of_oscillation`, `Integrability.lean:115` | Given `∀ x ∈ P.cell i, ∀ y ∈ P.cell i, |f x-f y| ≤ η`, conclude `cellUpper f P i-cellLower f P i ≤ η`. No extra continuity hypothesis. |
| `gap_le_of_cell_affine_gaps`, `Integrability.lean:441` | Given monotone α and cellwise `osc(h) ≤ η + C * osc(f)`, conclude `gap(h,P) ≤ η * (α b-α a) + C * gap(f,P)`. The cell inequality is the caller's obligation. |
| `rsIntegrable_add`, `Integrability.lean:281` | Integrability of f and g gives integrability of their pointwise sum and `I(f+g)=I(f)+I(g)`. |
| `rsIntegrable_const_mul`, `Integrability.lean:395` | Integrability of f and arbitrary real c give integrability of `c*f` and `I(c*f)=c*I(f)`. In particular c=-1 is available. |
| `rsIntegral_abs_le_bound`, `Integrability.lean:199` | Native integrability and `∀ x ∈ Icc a b, |f x| ≤ M` imply `|I(f)| ≤ M*(α b-α a)`. |
| `rsIntegral_same_endpoint`, `Definitions.lean:80` | For arbitrary f, α, a: `RSIntegrable f α a a ∧ RSIntegral f α a a=0`. |
| `vector_scalar_finite_sum`, `Vector.lean:225` | For a finite set s, `a≤b`, monotone α, and integrability of each `f j` for j∈s, gives integrability of the pointwise finite sum and equality to the finite sum of integrals. Despite its name this is a scalar helper. |

For later variable upper limits, `split_ordered hac hcb hf` in `Split.lean` gives both restrictions and integral additivity including endpoint cuts. It is not needed for the fixed-interval uniform-limit theorem.

### Concrete proof route: uniform limit and integral convergence

Write `S = Icc a b`, `A = α b-α a`, and `gap(f,P)=upperSum f α P-lowerSum f α P`. Assume for this design discussion each fₙ is natively integrable with respect to the same α on the same interval and fₙ tends uniformly to f on S. These are design inputs, not a frozen source contract.

1. Obtain `a≤b` and monotonicity from any approximant, hence `A≥0`. Extract one index N with `|f-f_N|<1` uniformly. An absolute bound M for f_N gives a bound M+1 for f. This proves the boundedness needed by the native criterion without continuity.
2. Under the stronger temporary uniform estimate `|f-f_N|≤δ`, any x,y in a partition cell satisfy
   `|f x-f y| ≤ 2δ + cellUpper f_N P i-cellLower f_N P i`.
   Use the value bounds for f_N, the triangle inequality, and `cell_gap_le_of_oscillation` to get the same bound for the cell gap of f.
3. `gap_le_of_cell_affine_gaps` with η=2δ and C=1 yields
   `gap(f,P) ≤ 2δ*A + gap(f_N,P)`.
   For ε>0 take `δ=ε/(4*(A+1))`, use uniform convergence to choose N, then f_N integrability to choose P with gap less than ε/2. Apply `rsIntegrable_iff_gap` to f. The denominator A+1 handles zero mass directly.
4. Only after f integrability is established, form fₙ-f using scalar multiplication by -1 and addition. Their integral identities and `rsIntegral_abs_le_bound` yield the reusable stability estimate
   `|I(fₙ)-I(f)| ≤ δ*A` whenever `∀ x∈S, |fₙ x-f x|≤δ`.
5. For integral convergence take `δ=ε/(A+1)`. No separate positive-mass branch or measure representation is needed. A singleton interval can either follow this proof or use `rsIntegral_same_endpoint` explicitly.

Small reusable lemmas worth implementing after contract approval are the cell perturbation estimate and the integral difference estimate. The latter alone cannot prove integrability of f, because it presupposes both integrability witnesses.

### Complex values and series

`Vector.lean:288–294` already defines `ComplexRSIntegrable f α a b` as native integrability of its real and imaginary components, and `ComplexRSIntegral` as the corresponding complex combination of the two real integrals. `complexRSIntegrable_iff_vector` and `complexRSIntegral_encoding` prove the connection to the finite-dimensional native integral.

`Complex.uniformContinuous_re`, `Complex.uniformContinuous_im`, and `UniformContinuous.comp_tendstoUniformlyOn` transfer uniform convergence to each component. Apply the scalar native result twice, then combine the two scalar integral limits. This preserves the complex target without introducing a measure-based definition. A finite-dimensional version follows componentwise if the inventory calls for it.

For a series apply the sequence result to the finite partial sums. `vector_scalar_finite_sum` supplies finite-sum integration. `Rudin.PMA.Chapter03.PartialSums a N` is exactly `∑ n ∈ Finset.range N, a n`; `SeriesHasSum a s` is `Tendsto (PartialSums a) atTop (𝓝 s)`. The verified `seriesHasSum_iff_conditional` identifies this with `HasSum a s (SummationFilter.conditional ℕ)`. Neither unconditional summability nor an M-test bound should enter a general termwise integration/differentiation corollary unless the source assumes it.

## Pinned uniform convergence APIs

These declarations were read at the pinned revision and checked by Lean through `import Rudin.PMA.Chapter06`.

| Declaration and source | Hypotheses/conclusion useful here |
| --- | --- |
| `Metric.tendstoUniformlyOn_iff`, `Topology/MetricSpace/Pseudo/Basic.lean:144` | `TendstoUniformlyOn F f p s ↔ ∀ ε>0, ∀ᶠ n in p, ∀ x∈s, dist (f x) (F n x)<ε`. Note the displayed distance order. |
| `Metric.uniformCauchySeqOn_iff`, `Topology/MetricSpace/Cauchy.lean:70` | For a nonempty semilattice index atTop: uniform Cauchy iff `∀ ε>0, ∃ N, ∀ m≥N, ∀ n≥N, ∀ x∈s, dist(F m x)(F n x)<ε`. |
| `TendstoUniformlyOn.tendsto_at`, `Topology/UniformSpace/UniformConvergence.lean:155` | Uniform convergence and x∈s give pointwise `Tendsto`. |
| `TendstoUniformlyOn.uniformCauchySeqOn`, same file:463 | Uniform convergence gives uniform Cauchy. |
| `UniformCauchySeqOn.cauchySeq`, same file:573 | Uniform Cauchy atTop and x∈s give a pointwise Cauchy sequence. The general filter form is `UniformCauchySeqOn.cauchy_map` at 565 and requires a nonbottom filter. |
| `cauchySeq_tendsto_of_complete`, `Topology/UniformSpace/Cauchy.lean:427` | In a complete uniform space, a Cauchy sequence has a limit. |
| `UniformCauchySeqOn.tendstoUniformlyOn_of_tendsto`, uniform convergence file:500 | Uniform Cauchy plus pointwise convergence at every x∈s gives uniform convergence to that limit. |
| `UniformContinuous.comp_tendstoUniformlyOn`, same file:253 | A uniformly continuous map applied to the values preserves uniform convergence. |

The completeness route can choose a limit on the interval subtype and extend it arbitrarily outside S. This avoids importing bounded-continuous-function spaces, whose continuity requirement is unsuitable for the native integration theorem.

## Pinned differentiation APIs and the endpoint gap

`Analysis/Calculus/UniformLimitsDeriv.lean` provides real/complex scalar-domain results with normed-space values. Its relevant main statements do not assume continuity of the derivatives, but do require open neighborhoods or open sets.

- `uniformCauchySeqOnFilter_of_deriv` (461): uniform Cauchy of derivative functions on `𝓝 x`; actual `HasDerivAt` eventually in `l ×ˢ 𝓝 x`; Cauchy values at x. Result: uniform Cauchy on `𝓝 x`.
- `uniformCauchySeqOn_ball_of_deriv` (467): derivative functions uniformly Cauchy on `Metric.ball x r`, actual `HasDerivAt` for all indices and every point of that ball, and Cauchy values at the center. Result: functions uniformly Cauchy on the ball.
- `cauchy_map_of_uniformCauchySeqOn_fderiv` (230): open preconnected s; uniform Cauchy Fréchet derivatives; actual derivatives for all indices and every point of s; an anchor x₀∈s with Cauchy values. Result: Cauchy values at any x∈s. This is pointwise output, with an interior anchor requirement.
- `hasDerivAt_of_tendstoUniformlyOn` (510): nonbottom l, `IsOpen s`, uniform convergence of derivative functions, eventual actual derivatives at every point of s, pointwise convergence of functions at every point of s, and x∈s. Result: `HasDerivAt g (g' x) x`.
- `hasDerivAt_of_tendstoLocallyUniformlyOn` and `hasDerivAt_of_tendstoUniformlyOnFilter` provide corresponding local/filter versions. The former still requires `IsOpen s`; the latter uses `𝓝 x`, not `𝓝[s] x`.
- The primed `hasDerivAt_of_tendsto_locally_uniformly_on'` version uses totalized `deriv` but also assumes eventual `DifferentiableOn`. Removing that existence assumption is invalid.

These results can verify interior derivative interchange after restriction to `Ioo a b`. They do not, by themselves, establish uniform convergence on all of `Icc a b` from an endpoint anchor, or preserve derivatives relative to `Icc a b` at a and b.

The boundary extension result `hasFDerivWithinAt_closure_of_tendsto_fderiv` in `Analysis/Calculus/FDeriv/Extend.lean:36` assumes differentiability on a convex open set, continuity of f relative to that set on its closure, **and a spatial limit of the derivative as y approaches the boundary**. A uniform limit over the sequence index does not supply that spatial derivative limit. It cannot be used here by silently assuming endpoint continuity of the limiting derivative.

### Exact closed-set tools

```lean
-- Analysis/Calculus/MeanValue.lean:695
Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
  (hf : ∀ x ∈ s, HasDerivWithinAt f (f' x) s x)
  (bound : ∀ x ∈ s, ‖f' x‖ ≤ C)
  (hs : Convex ℝ s) (xs : x ∈ s) (ys : y ∈ s) :
  ‖f y - f x‖ ≤ C * ‖y - x‖

-- Analysis/Calculus/Deriv/Basic.lean:272–277
HasDerivWithinAt.of_isLittleO :
  ((fun y => f y - f x - (y-x) • f') =o[𝓝[s] x] fun y => y-x) →
  HasDerivWithinAt f f' s x

-- Analysis/Asymptotics/Defs.lean:182–185
Asymptotics.IsLittleO.of_bound :
  (∀ ⦃c : ℝ⦄, 0<c → ∀ᶠ y in l, ‖r y‖ ≤ c*‖d y‖) → r =o[l] d
```

The first theorem allows scalar domain ℝ and values in ℝ, ℂ, or a real normed space. `convex_Icc` supplies its convexity. Its bound is required only for the derivative **difference** to which it will be applied, so individual derivatives need not be bounded.

`norm_image_sub_le_of_norm_deriv_le_segment'` in `MeanValue.lean:326` is another usable variant: actual derivatives within Icc at every point, a derivative bound on Ico, and x∈Icc imply `‖f x-f a‖≤C*(x-a)`. The convex symmetric form is simpler when the convergence anchor is an arbitrary point and x may lie on either side.

`HasDerivWithinAt.fun_sum` in `Deriv/Add.lean:210` gives actual derivatives for pointwise finite sums. `le_of_tendsto` passes an eventual real inequality to the limit under a nonbottom filter; this is sufficient for the approximation step below.

### Concrete proof route: anchor convergence and derivative uniform convergence

Subject to source confirmation, let S=Icc a b be nondegenerate, each fₙ have actual derivatives dₙ relative to S at every x∈S, let dₙ converge uniformly on S to d, and let fₙ(x₀) converge for an arbitrary x₀∈S. Use an actual derivative witness rather than totalized `derivWithin` alone. If the inventory states interior differentiability plus endpoint continuity instead, retain that distinction and use the corresponding interior mean-value hypotheses; do not strengthen it to endpoint derivative existence.

1. The derivative sequence is uniformly Cauchy. Apply the convex mean-value bound to fₙ-fₘ with derivative dₙ-dₘ. For all x∈S,
   `‖(fₙ-fₘ)(x)-(fₙ-fₘ)(x₀)‖ ≤ η*|x-x₀| ≤ η*(b-a)`.
2. Add the anchor difference. With anchor tolerance ε/2 and derivative tolerance `ε/(2*(b-a+1))`, obtain uniform Cauchy of fₙ on all of S. This allows x₀=a or x₀=b and makes no ordered-position assumption about x and x₀.
3. Pointwise completeness plus `UniformCauchySeqOn.tendstoUniformlyOn_of_tendsto` supplies a limit f and uniform convergence on S.
4. For a derivative at fixed x∈S, first prove the uniform approximation estimate for a large fixed N:
   `‖(f-f_N)(y)-(f-f_N)(x)‖ ≤ η*|y-x|` for every y∈S.
   Obtain it by applying the same MVT bound to fₘ-f_N, then pass m→∞ using pointwise limits and `le_of_tendsto`. Uniform Cauchy of the derivatives supplies the bound for every sufficiently large m and the chosen N.
5. Decompose the derivative remainder of f into the displayed approximation remainder, the known derivative remainder of f_N at x, and `(y-x) • (d_N(x)-d(x))`. Choose both derivative tolerances at most ε/3 and use the actual derivative of f_N for its relative-neighborhood remainder. `Asymptotics.IsLittleO.of_bound` and `HasDerivWithinAt.of_isLittleO` conclude the derivative relative to S, including its endpoints.
6. A series corollary applies this argument to ordered partial sums and uses `HasDerivWithinAt.fun_sum`. Convergence at one point remains ordinary ordered convergence. No unconditional `tsum` or absolute summability is needed for this route.

The direct relative little-o route avoids quotient division at y=x and avoids any extension of f outside S. Preserve `a<b` where derivative uniqueness or source endpoint existence is claimed; singleton relative derivatives have arbitrary coefficients and cannot stand in for nondegenerate endpoint semantics.

## Stronger APIs that must not replace the intended scope

`summable_of_summable_hasDerivAt_of_isPreconnected` and `hasDerivAt_tsum_of_isPreconnected` in `Analysis/Calculus/SmoothSeries.lean:60,89` require `Summable u`, an open preconnected set t, actual derivatives for every term and point, a bound `‖g' n y‖≤u n`, an anchor in t, and default `Summable (g · y₀)`. The target is complete. They are useful for an M-test corollary when its stronger hypotheses occur explicitly, but not as a substitute for the general source theorem.

Bochner/interval-integral convergence theorems establish the corresponding measure integral statements. The native Chapter 6 definition has no established equality with an arbitrary monotone-integrator measure representation. In particular, no right-continuity or left-continuity convention for α was imposed. Introducing a measure route would create additional bridge and endpoint obligations, not discharge the native theorem automatically.

Do not use FTC to prove the general derivative-interchange result by integrating dₙ. Merely existing derivatives need not be bounded or Riemann integrable, and their uniform convergence does not change this: a constant sequence of an unbounded derivative is uniformly convergent. A proof through Chapter 6's FTC would require extra assumptions. The proposed derivative route depends only on mean-value estimates and completeness; the integration route depends only on native Chapter 6, so they do not create a circular dependency.

## Prospective adversarial checks after contract approval

These are design checks, not newly implemented Lean theorems.

- Integration: a constant sequence at a discontinuous but Riemann-integrable step function; zero-mass integrator with bounded discontinuous functions; a jump integrator with functions continuous at its atom; singleton interval; complex-valued functions with a nonzero imaginary component. These expose accidental continuity, positive-mass, nondegeneracy, or real-only restrictions.
- Differentiation: constant-in-x functions isolate the anchor hypothesis; without the anchor, fₙ(x)=n has zero derivative but cannot converge. Include the anchor at each endpoint, a point on either side of an interior anchor, and an ambient absolute-value function restricted to [0,1] to distinguish a valid relative endpoint derivative from nonexistent ambient differentiability.
- A constant sequence of `f(x)=x² sin(1/x²)` with f(0)=0 has derivatives on [0,1] whose values are unbounded near 0. It tests that derivative continuity, boundedness, or integrability was not smuggled into the theorem.
- For series, an alternating harmonic series of constant functions converges uniformly in the spatial variable and has zero term derivatives; it tests retention of ordered conditional convergence instead of unconditional `Summable`.

## Verification and exact source snapshots

Two clients run as `./lake-local env lean --stdin` from the isolated root exited 0, without warnings. The first checked 28 names covering uniform convergence, differentiation, native integral bounds/finite sums, and Chapter 3 ordered-series definitions. The second checked five complex-value/coordinate-convergence names. Both imported the frozen canonical `Rudin.PMA.Chapter06`. These are availability/type checks, not proofs of the proposed Chapter 7 bridges.

| Read file | SHA-256 |
| --- | --- |
| `Rudin/PMA/Chapter03.lean` | `f711278f4e18ceeb1333cdda759a80635cf935d7c3658c1e984300eeb7808020` |
| `Rudin/PMA/Chapter06.lean` | `845f356f126f288456cf210526ecb29523776bff6f6cfe89a4ebba369747a373` |
| `Rudin/PMA/Chapter06/Basic.lean` | `5192b99092c0fc7da7109b1e3ffd90446db62c73845b935172643456b46a3915` |
| `Rudin/PMA/Chapter06/Criterion.lean` | `e88daabe91d0ddd9145c79ff4aecbfd5c054b30fd27ea86c0a1b7743e3488715` |
| `Rudin/PMA/Chapter06/Integrability.lean` | `001823e4c51a56b9c0d0afbe13801a757200178eac396081dec3b7abb91d5cec` |
| `Rudin/PMA/Chapter06/Vector.lean` | `1830138b9712dc5c6bd97293c0396df8160da84c25be76f55f0069dc3962ff98` |
| `Rudin/PMA/Chapter06/Calculus.lean` | `ac36c016490bd347b592af764c1c6e5f544a6cd09ad7aac0c59a4c79da6c3c18` |
| Mathlib `Analysis/Calculus/UniformLimitsDeriv.lean` | `f6531527febe7771f94e1dd6a0c45630d6a7ecccf04bcc6fb53505559de5e330` |
| Mathlib `Analysis/Calculus/MeanValue.lean` | `7e1e6f097fe92a2493ea5b4bc9a1896c850514604f26f863f812906fb500b856` |
| Mathlib `Analysis/Calculus/SmoothSeries.lean` | `293196f8d3e0fc74837fda06ee2b518ba5d917aba80e72c435311681473c14a1` |
| Mathlib `Topology/UniformSpace/UniformConvergence.lean` | `4a8ae31e5122a68de6a5dad6206ff231905d3c39965f1500ea6cf568d4c7126d` |

The accepted inventory resolved the source gates: complex sequence/series scope, the retained ordered-series integration corollary, nondegenerate derivative intervals, and derivatives relative to the full closed interval including endpoints. The definitions-only draft compiled cleanly with SHA-256 `3f8cac222481aa973cb4f65d92662a5034aec0b0378822d86d5a3e55f77d0acd`. It defines `pma7_16_contract`, `UniformDerivativeLimitProperty`, and `pma7_17_contract`; the last records both complex and real targets. Its internal zero-based sequence enumerates the source's positive-indexed terms in their existing order. Oscillation independently accepted these actual contracts before implementation; see `evidence/ch07-calculus-contract-independent-review.md`. Remaining_scope independently confirmed the same acceptance. The accepted contract definitions were preserved.

## Completion addendum

Both main theorems and four boundary probes are complete in the frozen 405-line source, SHA-256 `0bc805601a65a1261e944ae9d180b3cb0344c0d9484fc766f1d3df6c3411580d`. The draft `rudin/Chapter07CalculusDraft.lean` and published `rudin/Rudin/PMA/Chapter07/Calculus.lean` are byte-for-byte identical. The only preamble change since contract acceptance records that the review occurred; the contract definitions did not change.

- `pma7_16` proves native complex RS integrability of a uniform limit, convergence of the integrals, and the full ordered-series corollary. The scalar proof uses cell perturbations and the native gap criterion; only after limit integrability is established does it apply the integral difference bound. Real and imaginary components provide the complex proof.
- `pma7_17` is proved for complete real normed target spaces by `uniformDerivativeLimitProperty`, then instantiated for both ℂ and ℝ. It uses the single convergent anchor, uniform derivative Cauchy estimates, pointwise completeness, and the relative little-o argument. It assumes neither derivative continuity nor derivative integrability and uses no FTC/integral theorem.
- `uniform_integral_imaginary_step_probe` applies the complex theorem to an imaginary-valued discontinuous step integrable against the identity integrator.
- `uniform_integral_zero_mass_probe` accepts any bounded integrand against the constant zero integrator.
- `uniform_derivative_endpoint_probe` uses the right endpoint as anchor for the constant sequence of absolute-value functions on [0,1], retains derivatives at both relative endpoints, and explicitly verifies failure of ambient differentiability at zero.
- `uniform_integral_conditional_series_probe` uses the imaginary multiple of Chapter 3's alternating harmonic series, explicitly retains its failure of absolute convergence, and proves ordered convergence of its integral series to the imaginary multiple of its numerical sum.

Final draft compilation exited 0 without warnings. All six printed theorem/probe axiom sets were exactly `[propext, Classical.choice, Quot.sound]`. A source scan found no `sorry`, `admit`, custom `axiom`, unsafe marker, or kernel-check bypass. The canonical module build `./lake-local build Rudin.PMA.Chapter07.Calculus` succeeded (8945 jobs). Protected Chapter 6 aggregator, Basic, Integrability, Calculus, and Vector source hashes were rechecked unchanged; no Chapter 5/6 source or Rudin root was edited.

The root independently read all 405 lines and reported semantic/source acceptance after publication; its fresh imported-kernel client and recursive declaration audit remain separate final verification. No mathematical or implementation blocker remains for nodes 7.16–7.17.
