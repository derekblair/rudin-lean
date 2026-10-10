# PMA Chapter 3 Fidelity Review

Review date: 2026-10-09. Source: `/home/derekblair/sources/pma3.pdf`, printed pp.47–78 (PDF pp.56–87). The inventory contains all 55 numbered items. Only brief statements are recorded; source proof text is excluded.

## Current verdict

**Complete: 55/55 nodes — PASS. The final default `lake build` passes, with zero proof placeholders and only the permitted axioms.** The contract reviewer is independent of the three statement authors. Every definition and every substantive statement conjunct was back-translated and compared against the inventory before proof. The reviewer independently ran `lake env lean` on all three contract files, each with no errors or warnings. The reviewer later authored proofs for 3.18 and 3.20 against the already approved contracts; the root author independently compared every principal production signature and the additional 3.18 sequence definition, finding exact matches — PASS.

## Source extraction checks

The full chapter was checked for numbered headings. OCR variants such as `3.200`, `325`, `328`, `330`, `349`, and comma separators were resolved against numbering and rendered pages. Two additional independent source reviews cover 3.21–3.37 and 3.38–3.55. Mathematical ambiguities were checked in page images, including non-strict monotonicity, the Cauchy-series `≤ε`, geometric divergence for every `x≥1`, the seven exact root/ratio example quantities, `nⁿ` in 3.40(a), the Cauchy-square lower bound in 3.49, and strict `>5/6` in 3.53.

Important attached clauses are retained: the five convergence/boundedness/range examples and positive-real ambient-space example (3.1); closed-subspace completeness and rational incompleteness (3.12); the iterated-log examples (3.29); the factorial tail estimate (3.31); boundary classifications for all five power series (3.40); absolute-convergence consequences (3.46); and ordinary convergence of the specific rearrangement in 3.53.

## Semantic requirements and source repairs

- Ordinary series convergence is convergence of ordered partial sums. Bare Mathlib `Summable`/`HasSum` describes a stronger summation filter and does not express conditional convergence. A partial-sum `Tendsto` or the explicit `SummationFilter.conditional ℕ` comparator is required.
- Positive and zero indexing must be related explicitly. Tail and finite-sum endpoints, factorial partial sums, the alternating parity convention, and example 3.35 must preserve their formulas.
- Diameter must allow infinity. `Metric.ediam` is the suitable reference; unguarded real-valued `Metric.diam` would incorrectly assign zero to unbounded tails. The nested compact intersection clause requires nonempty stages, implicit in the source's nonempty-set diameter definition.
- Upper and lower limits are extended-real extrema of extended-real subsequential limits. In particular, 3.17 must retain membership, eventual strict bounds, and uniqueness; 3.54 must allow finite and infinite targets, including equal targets.
- Ratio-test denominators must eventually be nonzero. Totalized zero division would falsely apply the convergence test to alternating zero/one terms.
- The sentence in 3.36 about root-test inconclusiveness implies a valid statement about the **convergence criteria**. As a claim about both full tests it is false: constant terms `1` have root limsup `1` but satisfy the ratio divergence criterion. The node must record convergence-criterion dominance, with this boundary correction and a counterexample probe.
- Summation by parts needs `A_{-1}=0`; natural-number truncated subtraction cannot silently replace this value by `A_0`.
- Mertens's result (3.50) requires absolute convergence of one factor only. The converse product statement (3.51) assumes three ordinary sums, with no additional absolute-convergence hypothesis.

## Fresh bounded prior-art check

Primary GitHub repositories were searched/read again before Chapter 3 work. This is a bounded landscape check, not a proof that no other formalization exists. Existing overlap does not change the user's explicit authorization to complete this corpus.

| Repository | Primary source findings | Scope of verification |
|---|---|---|
| [Neuron-Group/RudinAnalysis](https://github.com/Neuron-Group/RudinAnalysis/tree/a54a65f57ea2bd77922bc7c9b55908e3db241aef/RudinAnalysis/NumericalSequencesAndSeries) | Substantial Chapter 3 opening coverage: convergence, subsequences, Cauchy sequences, completeness, monotonicity, and extended upper/lower limits. | Inspected declaration lists and code placeholder tokens in five chapter modules plus a finite-iteration file; no external build or axiom audit was run. |
| [hbghlyj/rudin-chapter-1-lean](https://github.com/hbghlyj/rudin-chapter-1-lean/tree/82bbf3561add26536bc6efb96de4a11ce4d428d0/RudinChapter3) | Two short files contain selected sequence/series results. | Read `Sequences.lean` and `Series.lean`, seven named theorem declarations in total; no external build or axiom audit. |
| [sinianluoye/LeanOfRudinAnalysis](https://github.com/sinianluoye/LeanOfRudinAnalysis/tree/a40f25c4a9f2f78e01c52077d7cbe5c05f7b0386) | No Chapter 3 numerical-sequences/series candidate was found in the inspected tree. | Repository-tree inspection only. |
| [libmath/Rudin](https://github.com/libmath/Rudin/tree/eaa25d0f99b2e3dbc11e5a06f94c55aa72f0a7dc) | No Chapter 3 sequence/series candidate was found in the inspected tree. | Repository-tree inspection only. |
| [alexanderlhicks/baby-rudin-project](https://github.com/alexanderlhicks/baby-rudin-project/tree/ec5572390fba98d1d17d3a64b1bcc98105579800) | No Chapter 3 sequence/series candidate was found in the inspected tree. | Repository-tree inspection only. |

The inspected Neuron files contain 20 named declarations in `ConvergentSequences.lean`, 27 in `Subsequences.lean`, 21 in `UpperAndLowerLimits.lean`, and seven in `SomeSpecialSequences.lean`. The first three have no lexical `sorry`, `admit`, `axiom`, or `native_decide` tokens after comment removal; `SomeSpecialSequences.lean` has four `sorry` tokens. The separate finite-iteration file has 13 declarations and no such tokens. These are lexical observations, not correctness or completeness certifications. Repository HEAD hashes were confirmed with read-only `git ls-remote`; GitHub's unauthenticated commit API was rate-limited.

## Formal statement review

The historical temporary statement-review files were `rudin/Chapter03OpeningContracts.lean`, `rudin/Chapter03SeriesContracts.lean`, and `rudin/Chapter03AdvancedContracts.lean`; these scratch files are removed after production comparison. These contain actual definitions and `Prop` statement contracts, without axioms or proof placeholders. Contract-only hypotheses are parameters; their presence and intended quantification were checked. Later-numbered prerequisites will be integrated before dependent nodes while preserving Rudin identifiers.

| Node | Independent contract verdict and checked scope |
|---|---|
| 3.1 | PASS — literal metric convergence, divergence, centered boundedness, all five complex examples, and positive-real ambient-space contrast. |
| 3.2 | PASS — finite neighborhood exceptions, uniqueness, boundedness, and a sequence in the limit-point set. |
| 3.3 | PASS — all four algebra operations plus reciprocal with termwise and limit nonzero guards. |
| 3.4 | PASS — Euclidean coordinate equivalence, vector sum, real inner product, and convergent scalar sequence. |
| 3.5 | PASS — strictly increasing subsequence indices, actual composition, subsequential limit, every-subsequence equivalence, cluster-point reference. |
| 3.6 | PASS — compact-set membership and bounded Euclidean subsequences. |
| 3.7 | PASS — closed set of all subsequential limits. |
| 3.8 | PASS — literal two-index Cauchy criterion and `CauchySeq` reference. |
| 3.9 | PASS — `ENNReal` diameter, pairwise supremum reference, tail range, unqualified Cauchy equivalence. |
| 3.10 | PASS — diameter unchanged by closure, nonempty decreasing compact stages, unique intersection point. |
| 3.11 | PASS — convergent implies Cauchy, compact Cauchy convergence, Euclidean equivalence. |
| 3.12 | PASS — literal sequential completeness, `CompleteSpace` reference, compact/Euclidean/closed cases, rational incompleteness. |
| 3.13 | PASS — consecutive non-strict inequalities, increasing/decreasing alternative, `Monotone`/`Antitone` references. |
| 3.14 | PASS — monotonic hypothesis and convergence iff boundedness. |
| 3.15 | PASS — eventual real thresholds for both infinities and real-filter/EReal comparators. |
| 3.16 | PASS — all extended subsequential limits, their supremum/infimum, and filter limsup/liminf comparators. |
| 3.17 | PASS — membership, eventual strict bounds beyond the extremum, and unique characterization for both extrema. |
| 3.18 | PASS — arbitrary surjective rational enumeration, all real limits and both infinities; exact shifted oscillatory formula; finite-limit equivalence. |
| 3.19 | PASS — eventual inequality and both extended extrema. |
| 3.20 | PASS — all five limits, exact positive-index formulas, and each required parameter guard. |
| 3.21 | PASS — inclusive block sums, zero-index partial sums, positive-index Icc bridge, ordinary sums/convergence/divergence, explicit conditional-filter references. |
| 3.22 | PASS — complete complex Cauchy criterion with inclusive blocks and the displayed `≤ε`. |
| 3.23 | PASS — vanishing terms and the actual divergent harmonic counterexample. |
| 3.24 | PASS — nonnegative real terms and bounded partial sums. |
| 3.25 | PASS — eventual norm comparison and eventual nonnegative divergent lower comparison. |
| 3.26 | PASS — sum for every `0≤x<1`, including zero, and divergence for every `x≥1`. |
| 3.27 | PASS — positive indices, nonnegative terms including zero, non-strict decrease, exact condensation weights and indices. |
| 3.28 | PASS — real exponent, positive indices, equivalence with `p>1`. |
| 3.29 | PASS — log power criterion and both iterated-log examples, starting at 2 and 3 respectively. |
| 3.30 | PASS — factorial initial value/recursion, ordinary factorial-series sum, and exponential reference. |
| 3.31 | PASS — source exponential limit and strict two-sided tail estimate with inclusive factorial partial sum. |
| 3.32 | PASS — irrationality of the defined Euler number. |
| 3.33 | PASS — extended nonnegative root limsup, strict convergence/divergence criteria, both boundary witnesses. |
| 3.34 | PASS — eventual nonzero denominators, both source criteria, ratio-one witnesses. |
| 3.35 | PASS — both exact positive-index coefficient patterns; every ratio/root extremum, infinite ratio case, ordinary convergence and ratio convergence failure. |
| 3.36 | PASS with explicit source repair — convergence-criterion dominance, both failure-to-zero conclusions, constant-one boundary counterexample. |
| 3.37 | PASS — positive real terms, both root/ratio inequalities in `ENNReal`, including infinity. |
| 3.38 | PASS — coefficient times power definition, partial-sum comparator, convergence disk with zero/infinite radii permitted. |
| 3.39 | PASS — inverse root limsup radius, inverse-zero/infinity cases, strict inside/outside criteria. |
| 3.40 | PASS — all five exact coefficients and radii, all stated boundary classifications, zero heads for positive-index reciprocals. |
| 3.41 | PASS — inclusive source sum and correct initial partial sum at `p=0`, using half-open difference sum. |
| 3.42 | PASS — bounded complex partial sums and decreasing real factors tending to zero. |
| 3.43 | PASS — zero-index translation of source alternating parity, non-strict magnitude decrease and vanishing terms. |
| 3.44 | PASS — radius one, real decreasing coefficients, zero limit, and all unit-circle points except one. |
| 3.45 | PASS — ordinary convergence of norm series and implication for ordinary complex series. |
| 3.46 | PASS — actual nonabsolute definition/example; nonnegative equivalence; absolute inside-disk, comparison, root and guarded ratio conclusions. |
| 3.47 | PASS — ordinary sum identities for addition and scalar multiplication. |
| 3.48 | PASS — exact finite Cauchy coefficients and antidiagonal reference. |
| 3.49 | PASS — actual alternating square-root example, nonabsolute convergence, exact coefficient lower bound, failure of vanishing terms and product convergence. |
| 3.50 | PASS — ordinary sums and absolute convergence of either one factor only. |
| 3.51 | PASS — ordinary sums of both factors and their product, with no absolute hypothesis. |
| 3.52 | PASS — permutation composition and bijection reference, preserving every index exactly once. |
| 3.53 | PASS — exact two-positive/one-negative permutation; both ordinary sums, changed sum, first block `5/6`, strictly increasing blocks and strict limsup bound. |
| 3.54 | PASS — conditional real series, every ordered pair of extended targets including equality, actual permutation and partial-sum liminf/limsup. |
| 3.55 | PASS — every permutation of an absolutely convergent complex series has the same ordinary sum. |

## Reference equivalence, probes, and final checks

The final artifacts are `rudin/Rudin/PMA/Chapter03.lean`, `rudin/Rudin/PMA/Chapter03Probes.lean`, and `rudin/Rudin/PMA/Chapter03Audit.lean`. All 357 authored main declarations were compared against the reviewed contracts and production drafts: full definition/structure bodies and theorem signatures agree. No authored main declaration was omitted. All 50 opening proposition contracts also match their expanded production theorem signatures. Normalization only identifies equivalent namespace/type notation, noncomputable modifiers, whitespace/comments, and the approved unused reciprocal guard rename `hn` to `_hn`. All 36 middle and 37 advanced definition/contract bodies are preserved.

`Chapter03Probes.lean` contains 14 ordinary Lean theorem probes in `Rudin.PMA.Chapter03.FidelityProbes`. They first compiled against the 62 canonical definitions without assuming any contract proposition, and then compiled without errors or warnings against the actual chapter module. Separate theorem axiom checks found only `propext`, `Classical.choice`, and `Quot.sound`.

The probes check empty and infinite diameter (including the incompatible real-diameter zero totalization), non-strict monotonicity of a constant sequence, constant tails, partial-sum endpoints, zero heads for positive-index reciprocal coefficients, convergence at the center of every power series even when its radius is zero, the constant-one root/ratio counterexample, identically zero totalized ratios for alternating zero/one terms and actual divergence of that series, an ordinarily convergent but unconditionally nonsummable harmonic series, the first six indices of the specified rearrangement, and failure of a duplicate-term sequence to be a permutation rearrangement.

The final PMA-3.54 proves the approved proposition for arbitrary ordered extended-real targets, including equal and infinite targets, using an actual permutation of all indices. Every new helper definition and the stage witness were reviewed: positive/negative parts, finite used-index removal, positive prefix selection, distinct and exhaustive nested prefixes, the least containing stage, ordered real approximations, endpoint error bounds, and all intermediate sums. Its separate theorem axiom check is standard-only. The root author independently reviewed the reviewer-authored EReal error-transfer helper, and the complete construction passed production comparison.

Final verification:

- Inventory: exactly 55 unique numbered nodes, 3.1–3.55; all proved and integrated in dependency order.
- Complete default `lake build`: PASS after the probe/audit imports were added; every node also had a passing build before its local commit.
- Independent actual `Chapter03Audit.lean` check: 604 recursive declarations under `Rudin.PMA.Chapter03`; separate nested `FidelityProbes` audit: 21 declarations. The standalone main audit checked 581 declarations; compiling the probes adds 23, comprising 21 nested probe declarations and the two lazily generated parent equation lemmas `RatioLimsup.eq_1` and `RudinDiameter.eq_1`. All counts include generated declarations.
- Permitted axioms only: `propext`, `Classical.choice`, `Quot.sound`.
- Main/probe code after comment removal: no `sorry`, `admit`, `axiom`, or `native_decide` tokens.
- All statement reviews, reference comparisons, and probe checks: PASS, with the explicit 3.36 source correction documented above.

The historical temporary contract, draft, and probe-snapshot files served as independent review inputs. They are disposable after the final production comparison; the chapter, audit, probes, inventory, and this report retain the result.
