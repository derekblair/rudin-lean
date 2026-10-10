# PMA Chapter 3 Inventory — Numerical Sequences and Series (3rd ed.)

Source: `/home/derekblair/sources/pma3.pdf`, verified 2026-10-09. Printed pp.47–78 are PDF pp.56–87. Scope: all 55 numbered items, including definitions with worked examples, substantive remarks, and nearby unnumbered consequences folded into their numbered parent. Exercises are excluded. These are brief mathematical paraphrases, with no proof text.

Series convergence means convergence of **ordered partial sums**, including conditional convergence. Bare Mathlib `Summable`/`HasSum` is not an unqualified substitute; an explicit conditional summation filter or partial-sum `Tendsto` is required. Positive-index and zero-index conventions must be compared explicitly where formulas depend on indices.

## Numbered nodes

- **PMA-3.1** (definition/examples, pp.47–48) — Metric convergence means `∀ε>0,∃N,∀n≥N,d(p_n,p)<ε`; divergence means no ambient limit; boundedness means bounded range; complex examples `1/n`, `n²`, `1+(-1)ⁿ/n`, `iⁿ`, and `1` respectively have `(limit,bounded,range)` `(0,T,infinite)`, `(none,F,infinite)`, `(1,T,infinite)`, `(none,T,finite)`, `(1,T,finite)`; reciprocals converge in `ℝ` but not in its positive-real subspace. Deps: 2.7, 2.18.
- **PMA-3.2** (theorem, p.48) — Convergence is eventual membership in every neighborhood of the limit; limits are unique; convergent sequences are bounded; every limit point of `E` is the limit of a sequence in `E`. Deps: 3.1, 2.18.
- **PMA-3.3** (theorem, p.49) — Complex sequence limits preserve sums, fixed scalar multiplication, fixed translations, products, and reciprocals when all terms and the limit are nonzero. Deps: 3.1–3.2.
- **PMA-3.4** (theorem, pp.50–51) — Euclidean sequence convergence is equivalent to convergence in every coordinate; limits preserve vector sums, inner products, and multiplication by convergent real scalar sequences. Deps: 1.36, 3.3.
- **PMA-3.5** (definition, p.51) — A subsequence is composition with strictly increasing integer indices; a subsequential limit is a limit of one; convergence to `p` is equivalent to convergence of every subsequence to `p`. Deps: 3.1.
- **PMA-3.6** (theorem, p.51) — Every sequence in a compact metric space has a convergent subsequence with limit in that space; every bounded Euclidean sequence has a convergent subsequence. Deps: 2.37, 2.41, 3.5.
- **PMA-3.7** (theorem, p.52) — The set of all subsequential limits of a metric sequence is closed. Deps: 3.5.
- **PMA-3.8** (definition, p.52) — A sequence is Cauchy iff `∀ε>0,∃N,∀m,n≥N,d(p_m,p_n)<ε`.
- **PMA-3.9** (definition, pp.52–53) — The diameter of a nonempty set is the supremum of its pairwise distances, allowing `+∞`; a sequence is Cauchy iff the diameters of its tail ranges tend to zero. Deps: 1.23, 3.8.
- **PMA-3.10** (theorem, p.53) — A set and its closure have the same diameter; a decreasing sequence of nonempty compact sets whose diameters tend to zero has an intersection consisting of exactly one point. Deps: 2.26, 2.36, 3.9.
- **PMA-3.11** (theorem, pp.53–54) — Convergent metric sequences are Cauchy; Cauchy sequences in compact metric spaces converge; every Euclidean Cauchy sequence converges, hence Euclidean convergence is equivalent to the Cauchy criterion. Deps: 3.6, 3.8–3.10.
- **PMA-3.12** (definition/examples, p.54) — Completeness means every Cauchy sequence converges; compact metric spaces and Euclidean spaces are complete; closed subsets of complete metric spaces are complete; `ℚ` with its usual distance is not complete. Deps: 3.11.
- **PMA-3.13** (definition, p.55) — A real sequence is monotonically increasing/decreasing when consecutive terms satisfy `≤`/`≥`; monotonic means either.
- **PMA-3.14** (theorem, p.55) — A monotonic real sequence converges iff it is bounded. Deps: 1.19, 3.13.
- **PMA-3.15** (definition, pp.55–56) — A real sequence tends to `+∞`/`-∞` iff it is eventually above/below every real threshold.
- **PMA-3.16** (definition, p.56) — Upper/lower limits are the supremum/infimum in the extended reals of all extended-real subsequential limits, including possible `±∞`. Deps: 1.23, 3.5, 3.15.
- **PMA-3.17** (theorem, p.56) — The limsup is a subsequential limit, is an eventual strict upper bound below every larger extended-real threshold, and is uniquely characterized by these properties; the analogous liminf statement holds with reversed inequalities. Deps: 3.16.
- **PMA-3.18** (examples, p.57) — A sequence containing all rationals has every real as a subsequential limit and upper/lower limits `+∞/-∞`; `(-1)ⁿ/(1+1/n)` has upper/lower limits `1/-1`; convergence to a real `s` is equivalent to both upper and lower limits equaling `s`. Deps: 1.20, 3.16–3.17.
- **PMA-3.19** (theorem, p.57) — Eventual termwise inequality `s_n≤t_n` implies inequalities between the corresponding liminfs and limsups. Deps: 3.16–3.17.
- **PMA-3.20** (theorem, pp.57–58) — For `p>0`, `1/nᵖ→0` and `p^(1/n)→1`; `n^(1/n)→1`; for `p>0` and real `α`, `n^α/(1+p)ⁿ→0`; if `|x|<1`, then `xⁿ→0`. Deps: 1.20, 3.1.
- **PMA-3.21** (definition, p.59) — Finite block sums add terms from `p` through `q`; partial sums are `s_n=∑_{k=1}^n a_k`; a series has sum `s` iff these sums tend to `s`, converges iff such a limit exists, and otherwise diverges; indexing from zero is also allowed. Deps: 3.1.
- **PMA-3.22** (theorem, pp.59–60) — A complex series converges iff `∀ε>0,∃N,∀m≥n≥N,‖∑_{k=n}^m a_k‖≤ε`. Deps: 3.11, 3.21.
- **PMA-3.23** (theorem, p.60) — A convergent series has terms tending to zero; the converse fails for the harmonic series. Deps: 3.22, 3.28 for the counterexample.
- **PMA-3.24** (theorem, p.60) — A nonnegative real series converges iff its partial sums are bounded. Deps: 3.14, 3.21.
- **PMA-3.25** (theorem, p.60) — Eventual domination `‖a_n‖≤c_n` by a convergent real series implies convergence of `∑a_n`; eventual `a_n≥d_n≥0` and divergence of `∑d_n` imply divergence of `∑a_n`. Deps: 3.22, 3.24.
- **PMA-3.26** (theorem, p.61) — For real `0≤x<1`, `∑_{n=0}^∞xⁿ=1/(1-x)`; for `x≥1`, the series diverges. Deps: 3.20, 3.21, 3.23.
- **PMA-3.27** (theorem, pp.61–62) — If `a_1≥a_2≥⋯≥0`, then `∑_{n=1}^∞a_n` converges iff `∑_{k=0}^∞2ᵏa_{2ᵏ}` converges (condensation). Deps: 3.24.
- **PMA-3.28** (theorem, p.62) — The positive-indexed real series `∑1/nᵖ` converges iff `p>1`; it diverges for `p≤1`. Deps: 3.26–3.27.
- **PMA-3.29** (theorem/examples, pp.62–63) — `∑_{n≥2}1/[n(log n)ᵖ]` converges iff `p>1`; `∑_{n≥3}1/[n log n log log n]` diverges, while `∑_{n≥3}1/[n log n(log log n)²]` converges. Deps: 3.27–3.28.
- **PMA-3.30** (definition, p.63) — With `0!=1` and `n!=1⋯n` for `n≥1`, define `e` as the sum of the convergent real series `∑_{n=0}^∞1/n!`. Deps: 3.25–3.26.
- **PMA-3.31** (theorem/estimate, pp.64–65) — `(1+1/n)ⁿ→e`; for `s_n=∑_{k=0}^n1/k!` and `n≥1`, `0<e-s_n<1/(n!n)`. Deps: 3.30.
- **PMA-3.32** (theorem, p.65) — `e` is irrational. Deps: 3.31.
- **PMA-3.33** (theorem, pp.65–66) — With `α=limsup ‖a_n‖^(1/n)`, `α<1` implies convergence and `α>1` divergence; `α=1` gives no conclusion, witnessed by the differing convergence of `∑1/n` and `∑1/n²`. Deps: 3.17, 3.25–3.26, 3.28.
- **PMA-3.34** (theorem/note, pp.66–67) — With eventually nonzero denominators, ratio limsup `<1` implies convergence; ratios `≥1` eventually imply divergence; ratio limit `1` gives no conclusion, as the harmonic and square-reciprocal series show. Deps: 3.23, 3.25–3.26, 3.28.
- **PMA-3.35** (examples, p.67) — For `a_{2n-1}=2⁻ⁿ,a_{2n}=3⁻ⁿ`, ratio liminf/limsup are `0/+∞` and root liminf/limsup `1/√3,1/√2`; for `a_{2n-1}=1/(2·4^(n-1)),a_{2n}=1/4^(n-1)`, ratio liminf/limsup are `1/8,2` and roots tend to `1/2`; both series converge while the ratio convergence criterion fails. Deps: 3.33–3.34.
- **PMA-3.36** (remarks, p.68) — The ratio convergence criterion implies the root convergence criterion; failure of the root convergence criterion prevents the ratio convergence criterion; the divergence conclusions of either test imply failure of the terms to tend to zero. Deps: 3.33–3.34, 3.37; see the source-interpretation correction below.
- **PMA-3.37** (theorem, p.68) — For positive real `c_n`, `liminf(c_{n+1}/c_n)≤liminf(c_n^(1/n))` and `limsup(c_n^(1/n))≤limsup(c_{n+1}/c_n)`, allowing infinite limits. Deps: 3.16–3.17.
- **PMA-3.38** (definition, p.69) — A complex power series has terms `c_nzⁿ`; its convergence disk may have radius zero or infinity, and convergence on its boundary can vary. Deps: 3.21.
- **PMA-3.39** (theorem, p.69) — For `α=limsup ‖c_n‖^(1/n)`, set `R=α⁻¹` with `0⁻¹=∞,∞⁻¹=0`; the power series converges for `‖z‖<R` and diverges for `‖z‖>R`. Deps: 3.33, 3.38.
- **PMA-3.40** (examples, pp.69–70) — Radii for `∑nⁿzⁿ`, `∑zⁿ/n!`, `∑zⁿ`, `∑_{n≥1}zⁿ/n`, and `∑_{n≥1}zⁿ/n²` are `0,∞,1,1,1`; on `‖z‖=1` the third diverges everywhere, the fourth converges except at `z=1`, and the fifth converges everywhere. Deps: 3.20, 3.28, 3.39, 3.44–3.45.
- **PMA-3.41** (theorem, p.70) — For `A_n=∑_{k=0}^na_k` and `A_{-1}=0`, `0≤p≤q` gives `∑_{n=p}^qa_nb_n=∑_{n=p}^{q-1}A_n(b_n-b_{n+1})+A_qb_q-A_{p-1}b_p`. Deps: 3.21.
- **PMA-3.42** (theorem, pp.70–71) — If partial sums of `a_n` are bounded, `b_0≥b_1≥⋯`, and `b_n→0`, then `∑a_nb_n` converges. Deps: 3.41.
- **PMA-3.43** (theorem, p.71) — If `|c_1|≥|c_2|≥⋯`, `c_{2m-1}≥0,c_{2m}≤0` for `m≥1`, and `c_n→0`, then `∑c_n` converges. Deps: 3.42.
- **PMA-3.44** (theorem, p.71) — A power series of radius `1` with real `c_0≥c_1≥⋯` and `c_n→0` converges at every `‖z‖=1` except possibly `z=1`. Deps: 3.26, 3.42.
- **PMA-3.45** (definition/theorem, p.71) — Absolute convergence means convergence of `∑‖a_n‖`; it implies ordinary convergence of `∑a_n`. Deps: 3.25.
- **PMA-3.46** (remarks/example, p.72) — Ordinary and absolute convergence agree for nonnegative terms; nonabsolute convergence means ordinary convergence with divergent norm series; the alternating harmonic series is nonabsolutely convergent; power series converge absolutely inside their disks, and the comparison/root/ratio convergence tests establish absolute convergence. Deps: 3.28, 3.33–3.34, 3.39, 3.43, 3.45.
- **PMA-3.47** (theorem, p.72) — Ordered series sums preserve termwise sums and multiplication by a fixed complex scalar. Deps: 3.3, 3.21.
- **PMA-3.48** (definition, p.73) — The Cauchy product has coefficients `c_n=∑_{k=0}^na_kb_{n-k}`. Deps: 3.21.
- **PMA-3.49** (example, pp.73–74) — `a_n=(-1)ⁿ/√(n+1)` converges nonabsolutely, but its Cauchy square diverges; its product coefficients satisfy `‖c_n‖≥2(n+1)/(n+2)` and do not tend to zero. Deps: 3.23, 3.28, 3.43, 3.48.
- **PMA-3.50** (theorem, pp.74–75) — If `∑a_n=A` is absolutely convergent and `∑b_n=B` converges ordinarily, their Cauchy product converges ordinarily to `AB`; either factor may be the absolutely convergent one. Deps: 3.48.
- **PMA-3.51** (theorem, p.75) — If ordinary sums of two series and their Cauchy product exist and equal `A,B,C`, then `C=AB`, without an absolute-convergence assumption. Deps: 3.48; its source proof is deferred until after 8.2.
- **PMA-3.52** (definition, pp.75–76) — A rearrangement composes the terms with a bijection of the positive integers, so every original index appears exactly once. Deps: 2.2, 3.21.
- **PMA-3.53** (example, p.76) — The alternating harmonic series has sum `s<5/6`; rearranging two successive positive terms then one successive negative term gives increasing block partial sums starting at `5/6`, limsup `>5/6`, and a convergent series whose sum differs from `s`. Deps: 3.43, 3.52.
- **PMA-3.54** (theorem, pp.76–77) — For any ordinarily but not absolutely convergent real series and extended-real `α≤β` (including `±∞`), a rearrangement exists whose partial sums have liminf `α` and limsup `β`. Deps: 3.16, 3.46, 3.52.
- **PMA-3.55** (theorem, p.78) — Every rearrangement of an absolutely convergent complex series converges ordinarily to the same sum. Deps: 3.45, 3.52.

## Fidelity conventions and source corrections

- Diameter must include infinite values. The pinned Mathlib reference is `Metric.ediam`. Its real-valued `Metric.diam` is zero for unbounded sets and therefore needs boundedness guards; it cannot directly implement the unqualified tail-diameter Cauchy criterion.
- PMA-3.10's singleton-intersection theorem requires nonempty stages, implicit in the source's diameter definition for nonempty sets.
- PMA-3.13 uses non-strict monotonicity. PMA-3.22 displays `≤ε`, not `<ε`; the criteria are equivalent, but the source statement should be retained or explicitly compared.
- PMA-3.26 includes `x=0` in its convergence case and all `x≥1` in its divergence case. PMA-3.27 includes zero terms. PMA-3.28 and PMA-3.29 include the divergent equality case `p=1`.
- PMA-3.34 ratios must have eventually nonzero denominators. Totalized division otherwise falsely certifies a series alternating zero and one as convergent.
- PMA-3.36's printed assertion that root-test inconclusiveness forces ratio-test inconclusiveness is valid for the **convergence criteria**. Read as a statement about both full tests, it is false: `a_n=1` has root limsup `1`, yet its ratios are always `1` and the ratio divergence criterion applies. The formal node must state convergence-criterion dominance and record this boundary counterexample, rather than assert the false stronger interpretation.
- PMA-3.40(a) uses `nⁿ`, not `n!`. Its five radius examples include their stated boundary classifications.
- PMA-3.41 uses `A_{-1}=0`; a natural-number implementation must handle this endpoint explicitly rather than replace it with `A_0` through truncated subtraction.
- PMA-3.53 asserts ordinary convergence of the rearrangement in the reader-verification bracket. Its changed-sum claim must not be replaced by mere existence of an arbitrary permutation.
- PMA-3.54 allows infinite target limits and equality `α=β`; a theorem confined to prescribed finite sums covers only a special case.
- Dependencies can cross later numbered items in this chapter (3.23/3.28, 3.36/3.37, 3.40/3.44). Formalize prerequisites first while preserving the original identifiers. Mathlib can supply source proofs explicitly deferred to later chapters.
- Exercises 1–25 on printed pp.78–82 are outside the numbered-main-text inventory.

## Count by numbered type

| Type | Count |
|---|---:|
| Definition (including attached examples) | 13 |
| Theorem (including unnumbered absolute-convergence definition at 3.45) | 35 |
| Examples | 5 |
| Substantive numbered remarks | 2 |
| **Total** | **55** |

## Formalization order

The explicit dependency order is:

`PMA-3.1`, `PMA-3.2`, `PMA-3.3`, `PMA-3.4`, `PMA-3.5`, `PMA-3.6`, `PMA-3.7`, `PMA-3.8`, `PMA-3.9`, `PMA-3.10`, `PMA-3.11`, `PMA-3.12`, `PMA-3.13`, `PMA-3.14`, `PMA-3.15`, `PMA-3.16`, `PMA-3.17`, `PMA-3.18`, `PMA-3.19`, `PMA-3.20`, `PMA-3.21`, `PMA-3.22`, `PMA-3.24`, `PMA-3.25`, `PMA-3.26`, `PMA-3.27`, `PMA-3.28`, `PMA-3.23`, `PMA-3.29`, `PMA-3.30`, `PMA-3.31`, `PMA-3.32`, `PMA-3.33`, `PMA-3.34`, `PMA-3.35`, `PMA-3.37`, `PMA-3.36`, `PMA-3.38`, `PMA-3.39`, `PMA-3.41`, `PMA-3.42`, `PMA-3.43`, `PMA-3.44`, `PMA-3.45`, `PMA-3.40`, `PMA-3.46`, `PMA-3.47`, `PMA-3.48`, `PMA-3.49`, `PMA-3.50`, `PMA-3.51`, `PMA-3.52`, `PMA-3.53`, `PMA-3.54`, `PMA-3.55`.
