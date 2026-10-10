# Independent final review: PMA 6.14–6.16 and 6.18

Verdict: **ACCEPTED**, with no requested source fixes. The actual final definitions, all contract conjuncts, and all 33 theorem bodies in the two files were read independently of their implementation. The source was compared with the accepted Chapter 6 inventory, its independent source review, the native Chapter06 Basic definitions, and the Chapter04 jump-series definitions used by the proof. No reviewed source file was edited.

## Exact reviewed snapshots

- `rudin/Chapter06JumpDraft.lean`: 457 lines, SHA256 `ab56704088a99d95c29755f2ada3c7a491ea55af5f24be7cf19b51283e96c47a`.
- `rudin/Chapter06MomentDraft.lean`: 40 lines, SHA256 `21ccfad2cbbc3cbd0726a62a190f6092fd2b376690233dd340435b38bb89deb5`.

The corresponding isolated `Rudin/PMA/Chapter06/Jump.lean` and `Moment.lean` copies matched these hashes. Draft hashes were checked again after compilation and remained unchanged.

## Scope and semantic findings

**6.14 (Jump lines 14–25, proof line 69):** `UnitStep x` is exactly zero for `x ≤ 0` and one for `x > 0`; in particular its value at the jump is zero. `TranslatedStep s x` is the source translation. The contract also proves global monotonicity. `AtomicStepSum` uses precisely this step. Its bridge to Chapter04 `JumpSumLeft` preserves the strict condition `s i < x`, rather than silently substituting the right-continuous step.

**6.15 (contract line 28, proof line 225):** Both strict interior inequalities, boundedness of f on the full closed interval, and continuity only at the jump are retained. No continuity elsewhere is assumed. Although expressed as `ContinuousAt f s`, this has the source-relative meaning here because `a < s < b` makes the closed interval a neighborhood of s; it does not restrict f far outside the source interval. The conclusion supplies native integrability as well as the value identity. Every nonzero step weight forces its closed partition cell to contain s; the weights telescope to one. The explicit partition `[a,s,t,b]` puts its sole nonzero step increment on `[s,t]`, correctly respecting the step's value at s. Continuity at s gives arbitrarily tight lower/upper sums. All extrema have nonempty cells and the required value bounds; no totalized supremum is used as a substitute for existence.

**6.16 (contract line 36, proof line 325):** The contract retains arbitrary distinct interior locations, nonnegative summable weights, and continuity of f on the closed interval. Zero coefficients are admitted. It includes pointwise summability of the integrator series at every real x, monotonicity, both endpoint values, summability of the weighted samples, native integrability, and equality to the convergent sample series. The helper theorems prove a slightly stronger result without needing distinctness; the published source contract still includes it. This is a valid generalization, not an omitted obligation.

The series argument is substantive: pointwise step summability and monotonicity are transferred from the correctly oriented Chapter04 series; compact boundedness and nonnegative weights prove weighted-sample summability. Each cell's integrator increment is a convergent sum of weighted single-step increments. Finite cell sums are interchanged with those convergent series using explicit summability proofs. The sample sum lies between every native lower and upper sum. Continuous integrability for arbitrary monotone integrators then identifies their common value with the sample sum. The formal natural-number sequence begins at zero; this is the usual harmless reindexing of a source sequence beginning at one.

**6.18 (contract at Jump line 51, full proof at Moment line 28):** All four accepted clauses are present and proved:

1. The quadratic function has a native Stieltjes integral for every nondecreasing mass function on `[0,1]`, with no derivative or integrator-continuity premise. This includes continuous mass functions not differentiable everywhere.
2. For an actual relative derivative rho that is ordinarily Riemann integrable, the density-weighted quadratic function is Riemann integrable and its ordinary integral equals the Stieltjes moment. The bound on the quadratic function is proved on `[0,1]`, and the argument specializes the independently reviewed full 6.17. It does not add continuity of rho or use an unqualified totalized derivative.
3. The countable interior atomic moment has a summable weighted-square series, native integrability, and the stated series value.
4. The finite atomic moment, including the empty finite family, has native integrability and the finite weighted-square value. Finite summability and the finite-sum identity are established through the generic atomic theorem.

Both atomic clauses explicitly retain interior support. This matches the accepted inventory interpretation and avoids the false claim that the left-continuous step at the terminal endpoint counts that endpoint's mass. No endpoint-inclusive atomic formula is asserted.

The native `RSIntegrable` predicate still requires interval order, bounded integrand values, a nondecreasing integrator, and equality of native lower/upper Darboux integrals. No right-continuity premise or measure representation of the integrator is introduced anywhere in these proofs.

## Boundary and adversarial coverage

`translatedStep_self_sums` proves lower sum zero and upper sum one for every partition when the source step is integrated against itself across an interior jump. `translatedStep_not_RSIntegrable_self` therefore proves actual failure of native Darboux integrability. `unitStep_source_caution` additionally proves relative discontinuity at the jump on `[-1,1]`. This is a useful semantic check against an accidental measure-integral interpretation or loss of the closed-cell convention.

Strict interior hypotheses ensure nonempty, nondegenerate source intervals in 6.15 and 6.16. The moment interval is explicitly `[0,1]`. Repeated partition points and zero weights are handled by the general sum arguments. The nonnegative-weight hypotheses admit the zero-weight family without artificial positivity assumptions. No additional probe is required for acceptance of these nodes.

## Independent verification

- `./lake-local env lean Chapter06JumpDraft.lean`: exit 0, no warnings or errors.
- `./lake-local env lean Chapter06MomentDraft.lean`: exit 0, no warnings or errors, after the parent finished refreshing its Calculus dependency. The first attempt during that refresh failed only because `Calculus.olean` was temporarily absent; it was retried after the dependency was available.
- Recursive axiom reports for `pma6_14`, `pma6_15`, `pma6_16`, `pma6_18`, `quadraticMoment_density`, `atomicQuadraticMoment`, `finiteAtomicQuadraticMoment`, `atomicStepSum_integral_of_integrable`, `translatedStep_not_RSIntegrable_self`, and `unitStep_source_caution` list only `propext`, `Classical.choice`, and `Quot.sound`.
- Whole-source scans found no `sorry`, `admit`, `native_decide`, or custom axiom declarations.

This review covers the four numbered nodes and the additional shared-jump caution helpers. It does not replace a full chapter rebuild or review of unrelated nodes. No remaining blocker was found within this scope.
