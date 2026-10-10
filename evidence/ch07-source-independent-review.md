# Chapter 7 independent source inventory and fidelity review

## Independent extraction

Read on 2026-10-10 from the authorized local PDF, `/home/derekblair/sources/pma3.pdf`: every complete main-text page, PDF 152–174 (printed 143–165), visually rendered in memory. No PDF, page image, extracted proof text, or extended exposition was saved or copied. The primary Chapter 7 inventory was not read before this independent list was saved. No Lean proof implementation or protected-file edit was performed.

**Count: 33 numbered nodes, PMA-7.1 through PMA-7.33**: 7 definitions, 7 examples, 18 theorems, 1 numbered corollary. The unnumbered integration corollary and other mathematical remarks are attached to the relevant nodes. Exercises start after 7.33 and are excluded.

General scope is complex-valued functions, with explicitly real-valued exceptions. Uniform convergence concerns the entire indicated set. Subsequence indices must be strictly increasing.

| Node | Kind; concise required content |
|---|---|
| 7.1 | Definition: pointwise limit of a function sequence; series sum as pointwise limit of partial sums. |
| 7.2 | Example: `m/(m+n)` has the two iterated limits 1 and 0, in the respective orders. Positive source indices must be represented faithfully. |
| 7.3 | Example: the continuous terms `x²/(1+x²)^n`, starting at n=0, sum to 0 at x=0 and to `1+x²` elsewhere; the sum is discontinuous. |
| 7.4 | Example: the iterated limit of `(cos(m! π x))^(2n)` is the rational indicator, with values 1 on rationals and 0 on irrationals. Include everywhere discontinuity and failure of ordinary Riemann integrability on nondegenerate intervals. |
| 7.5 | Example: `sin(nx)/sqrt(n)` tends to 0 (indeed uniformly); derivatives are `sqrt(n)*cos(nx)` and diverge to positive infinity at 0, whereas the limit derivative is 0. |
| 7.6 | Example: `n²*x*(1-x²)^n` tends pointwise to 0 on [0,1], but its native ordinary integrals equal `n²/(2n+2)` and diverge. Also retain the n-scaled variant, whose integrals tend to 1/2 while its limit integral is 0. |
| 7.7 | Definition: uniform convergence with one eventual index for every point; uniform series convergence through partial sums. Include implication to pointwise convergence. |
| 7.8 | Theorem: uniform convergence to some complex function iff the uniform Cauchy condition holds. No continuity, compactness, or boundedness assumption. |
| 7.9 | Theorem: under pointwise convergence to f, uniform convergence iff the supremum errors tend to 0. Suprema may initially be infinite; see precision requirements below. |
| 7.10 | Theorem: summable numerical majorants for term norms give uniform series convergence. The attached converse warning must not become an iff claim. |
| 7.11 | Theorem: uniform convergence on E and existence of each function's punctured limit at an accumulation point give convergence of those limits and the corresponding limit of f. The point need not belong to E. |
| 7.12 | Theorem: a uniform limit of continuous functions on E is continuous on E. Retain the failure of the converse, as supplied by 7.6. |
| 7.13 | Theorem: on compact K, continuous real functions decreasing pointwise to a continuous limit converge uniformly. Attached noncompact counterexample: `1/(nx+1)` on (0,1), decreasing to 0 but not uniformly. |
| 7.14 | Definition and attached properties: bounded continuous complex functions on a metric space; supremum norm, definiteness, triangle inequality, norm-difference metric, equivalence between metric convergence and uniform convergence, uniform closedness/closure. Compactness makes the boundedness requirement automatic. |
| 7.15 | Theorem: the space in 7.14 is complete in its supremum metric, for an arbitrary metric domain. |
| 7.16 | Theorem: for nondecreasing α on [a,b], uniform limits of native RS-integrable complex functions remain integrable, and their integrals converge to the limit integral. Include the attached uniform-series term-by-term integration corollary with existence of the series of integrals. |
| 7.17 | Theorem: differentiable functions on [a,b], convergence at one point of that interval, and uniform convergence of their derivatives imply uniform function convergence and differentiation of the limit throughout [a,b], including within-interval endpoint derivatives. Derivative continuity is not assumed. |
| 7.18 | Theorem: some continuous real function on all of ℝ is nowhere differentiable. The source's particular construction is a proof choice, not an additional mandatory theorem premise or conclusion. |
| 7.19 | Definition: pointwise bounded and uniformly bounded sequences. Include the attached countable-subset subsequence consequence (also covered by 7.23). |
| 7.20 | Example: the uniformly bounded continuous sequence `sin(nx)` on [0,2π] has no subsequence converging at every point. |
| 7.21 | Example: `x²/(x²+(1-nx)²)` on [0,1] is bounded by 1 and tends pointwise to 0, but equals 1 at 1/n; no subsequence converges uniformly. Retain the attached observation that uniform convergence of bounded terms implies uniform boundedness. |
| 7.22 | Definition: one positive δ controls every pair of points and every member of the family. This is uniform equicontinuity. Each member is uniformly continuous; the 7.21 family is not equicontinuous. |
| 7.23 | Theorem: a pointwise bounded sequence of complex functions on a countable set has one subsequence convergent at every point of that set. |
| 7.24 | Theorem: a uniformly convergent sequence of continuous functions on a compact metric space is equicontinuous in the 7.22 sense. |
| 7.25 | Theorem: pointwise bounded, equicontinuous continuous functions on compact K are (a) uniformly bounded and (b) have a uniformly convergent subsequence. |
| 7.26 | Theorem: continuous complex functions on [a,b] are uniform limits of polynomials; real-valued functions admit real-coefficient polynomial approximants. |
| 7.27 | Corollary: on [-a,a], absolute value is a uniform limit of real polynomials each vanishing at 0. |
| 7.28 | Definition: real/complex function algebras closed under addition, multiplication, and scalar multiplication; uniform closedness and sequential uniform closure. No requirement to contain constant one. Polynomial example and its uniform closure connect to 7.26. |
| 7.29 | Theorem: the uniform closure of an algebra of bounded functions is itself an algebra and is uniformly closed. No continuity or compactness assumption. |
| 7.30 | Definition: separates distinct points; vanishes at no point, with a potentially different witness at each point. Polynomials satisfy both; even polynomials on [-1,1] fail separation. |
| 7.31 | Theorem: a separating, nowhere-vanishing algebra interpolates any two prescribed scalar values at two distinct points. Both real and complex scalar versions. |
| 7.32 | Theorem: a separating, nowhere-vanishing algebra of continuous real functions on compact K has all continuous real functions as its uniform closure. Do not assume it is unital. |
| 7.33 | Theorem: the corresponding complex assertion requires closure under complex conjugation. Include the meaning of self-adjointness and the warning that the unrestricted complex analogue of 7.32 fails; the exercise-specific construction is excluded. |

## Fidelity and dependency requirements

- **7.9:** use the supremum of nonnegative norm errors in `ENNReal` (empty-set value 0), or an explicitly equivalent formulation. An unguarded real supremum is unsound for unbounded error ranges, and requiring every error range to be bounded narrows the source. Uniform convergence supplies eventual boundedness only. A real-supremum bridge may be stated when the relevant range is bounded.
- **7.11:** use a nontrivial punctured neighborhood within E, not continuity at a point assumed to lie in E. Accumulation prevents vacuous limits.
- **7.14–7.15:** bounded continuous maps are appropriate here; mere compact-domain continuous maps would narrow the source.
- **7.16:** preserve arbitrary nondecreasing α, including discontinuous α and zero total mass; no right-continuous normalization, Lebesgue/Stieltjes substitution, or continuity of the integrands. Use the protected Chapter 6 native real/complex RS definitions. The integration-limit and series-limit existence are conclusions.
- **7.17:** use a nondegenerate ordered interval for derivative uniqueness; endpoints are relative derivatives. The source does not require C¹ functions, convergence at every point, or prior existence of the function limit. An implementation restricted to interior derivatives needs a separate endpoint bridge.
- **7.22:** Mathlib's pointwise equicontinuity should not silently replace the source's uniform condition. On compact domains their equivalence can be proved, but the definition itself is on arbitrary sets.
- **7.25:** do not move uniform boundedness into the hypotheses or replace subsequence convergence by a weaker finite-net claim.
- **7.28–7.33:** a unital subalgebra alone narrows the statement; derive a unital closure or use an appropriate nonunital/set-based representation and a proved bridge. In 7.30 the quantifiers are `∀ x, ∃ g`, not `∃ g, ∀ x`. Keep real and complex scalar distinctions. Empty domains and empty families need explicit conventions if a set-based source algebra definition allows the latter vacuously.
- **Counterexamples:** 7.4 and 7.6 refer to native ordinary Riemann integration (`α = id`) from Chapter 6. A Bochner calculation is useful only after a proved equality for the relevant integrands. The 7.20 source proof invokes later 11.32; this forward proof dependency does not justify omitting the example. A verified Mathlib bounded-convergence argument or a different proof may discharge it without pretending Chapter 11 is already formalized.
- **Proof choices versus scope:** the particular nowhere-differentiable construction in 7.18, polynomial kernel in 7.26, and four proof stages in 7.32 are not separately numbered results or mandatory implementation algorithms. Equivalent complete proofs are acceptable. Explicit mathematical counterexamples and attached conclusions remain in scope.

Existing native Chapter 6 dependencies checked read-only: `rsIntegrable_iff_gap` in `Criterion.lean`, `Partition.sum_weights` in `Basic.lean`, the addition/scalar-multiplication and integral-bound lemmas in `Integrability.lean`, and the real/imaginary definitions `ComplexRSIntegrable` / `ComplexRSIntegral` in `Vector.lean` support 7.16 without changing the integral. The exact polynomial integrals in 7.6 can use native `pma6_21` in `Calculus.lean`. For 7.4, rational and irrational density should force the native lower/upper sums to 0 and b-a, with repeated-point cells contributing zero.

## Comparison status

**ACCEPTED:** the independently extracted scope agrees with `research/pma-ch07-inventory.md` at SHA-256 `d5a0b41e6c77e33ea46c92033be033813894c024783606bc7b4565bf617d64ad`. The primary file was first read only after this independent list had been saved and the inventor sent the stable-ready signal. Counts, domains, hypotheses, complex coverage, counterexamples, attached results, and exercise exclusions agree. No source omission or incorrect added premise was found.

The specifically requested scope choices are accepted:

- **7.10:** a verified example of uniform convergence without any summable absolute majorant is a faithful, informative realization of the source's converse-failure warning. No source-specific counterexample is prescribed.
- **7.19:** countable-subset selection is explicitly attached main-text content, and may be discharged by a specialization of 7.23; it is not a new numbered node or a reason for a circular definition.
- **7.21:** both introductory observations about boundedness are explicit main-text assertions. Reusing 7.6 for failure of uniform boundedness is faithful, and the positive uniform-convergence assertion must retain individual boundedness of all sequence members.
- **7.33:** a verified counterexample to the unrestricted complex analogue is warranted by the explicit source warning. The exercise-specific construction remains excluded, so any correct witness establishes that warning.

The primary file correctly reserves the nonempty, nonunital algebra convention for explicit typed-contract review. This acceptance fixes the inventory only: each typed contract still needs review before proof implementation, particularly the error-supremum representation, relative endpoints, uniform equicontinuity, and algebra closure conventions. The source extraction and comparison did not modify any Chapter 5/6 source or implement any Chapter 7 proof.

Subsequently, the actual principal type in `rudin/Chapter07NowhereDraft.lean` was independently read and accepted before its proof: `pma7_18_contract` is exactly `∃ f : ℝ → ℝ, Continuous f ∧ ∀ x : ℝ, ¬ DifferentiableAt ℝ f x`. This covers all real points and the full real derivative. The separate periodic-tent and series-witness definitions are optional proof infrastructure; the contract does not assume they work.
