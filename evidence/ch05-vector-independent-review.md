# PMA-5.16–5.19 independent source and proof review

Reviewer: opening-contract agent, independently reviewing the vector agent's actual implementation. Only this evidence file was edited during this review; the reviewed Lean file was not changed.

## Verdict

**PASS for the four actual contracts and their proofs.** No mathematical scope correction is required. The final draft was independently compiled with `./lake-local env lean Chapter05VectorDraft.lean`: exit status 0, no warnings or errors. The command's only output was the requested axiom reports.

Reviewed file: `rudin/Chapter05VectorDraft.lean`, 347 lines.

SHA256: `296861f877fc4c63b2e9df5814a7d8e51374427c018b5a491c39b979e8885e41`.

Review references: the accepted Chapter 5 inventory, especially items 5.16–5.19 and the endpoint/complex/supremum conventions; the independent accepted informal inventory at `/tmp/pma-ch05-source-review.md`; every definition, contract conjunct, helper proof, main proof, and final probe in the actual draft. No textbook proof text was copied or extracted for this review.

**Production integration obligation:** attach the exact open-interior/punctured-closed-interval source bridge for the vector derivative. `VectorDerivativeWithin` uses the punctured `Icc a b` approach and includes `a < b` and `x ∈ Icc a b`. The source uses the punctured `Ioo a b` approach. The opening module's proved `interval_punctured_Ioo_eq_Icc` equates these filters under precisely those guards, independently of the codomain or the function whose limit is taken. Root has retained ownership of adding this direct bridge during integration. Its mathematical justification is present; the final integrated bridge declaration and build remain root's verification obligation.

## Semantic comparison

### PMA-5.16

- The vector difference quotient uses a real scalar inverse, real input, and convergence of the norm of the difference from the proposed derivative. There is no accidental complex-input differentiability assumption.
- The derivative predicate contains both interval nondegeneracy and point membership. The `HasDerivWithinAt` comparator keeps both guards, covering the one-sided endpoint cases without vacuous isolated-point limits.
- The complex component characterization states both implications for the exact real and imaginary parts of the proposed derivative. Reconstruction uses the corresponding complex number, so it entails the differentiability-existence equivalence as well.
- The Euclidean characterization uses `EuclideanSpace ℝ (Fin n)` and the same derivative vector's coordinates. Its use of the Pi-space continuous linear equivalence preserves the Euclidean normed-space derivative rather than replacing the source norm with an unproved coordinate-limit assertion.
- Continuity, sums, complex multiplication, and the real inner-product rule have the correct domains and formulas. The complex quotient assumes nonzero denominator only at the evaluation point and concludes on the domain intersected with the nonzero-denominator set.
- Arbitrary-set helper statements are valid extensions. Their source interval specializations follow from the guarded derivative comparator; isolated-set behavior in bare library predicates is not represented as a source interval derivative.

### PMA-5.17

- The curve is a map from the real line into the complex numbers. Its trigonometric identity, endpoint value one at zero and at two pi, exact velocity, and unit velocity norm are all contract conjuncts.
- The final conjunct negates existence of an interior point satisfying the scalar mean-value equality. The proof uses the positive interval length and nonzero velocity norm, so it does not depend on the interval being empty or on an assumed failure theorem.

### PMA-5.18

- The phase is exactly `I / (x : ℂ)^2`, and the denominator function is exactly the real input plus its square times that phase's exponential.
- The velocity retains both the `2*x` and `-2*I/x` terms. The proof may use a complex derivative internally, but explicitly composes with the real inclusion; its proved result has input type `ℝ`.
- On the entire source interval `(0,1)`, the contract establishes both function derivatives, nonvanishing of the denominator and its derivative, both lower norm estimates, and the derivative-quotient upper bound.
- Both functions tend to zero from the right. The function quotient tends to one while the derivative quotient tends to zero on that same nonvacuous approach filter. The final separate probe proves that the function quotient cannot also tend to zero.
- Algebraic manipulations outside `(0,1)` are helper extensions only. The source quotient and derivative quotient are explicitly nonzero-denominator expressions throughout `(0,1)`; no source claim relies on division at zero.

### PMA-5.19

- The main theorem retains `a < b`, continuity on the closed interval, and derivatives only in the open interval. It neither requires endpoint derivatives nor continuity of the derivative.
- Its first conclusion is an actual interior witness for the derivative-norm inequality. There is no derivative bound or pre-existing supremum premise in this main conclusion.
- The uniform-bound conclusion is a separate implication. Boundedness of the derivative-norm range appears only in the finite real `sSup` consequence, where it is needed. This matches the accepted finite-supremum convention without restricting the main theorem.
- The stronger real-inner-product-space formulation specializes to every source Euclidean space. The proof derives the interior witness from the real scalar mean-value theorem applied to the scalar product with the endpoint displacement, then uses the inner-product norm bound.

## Kernel and boundary evidence

The independently rerun compiler reported exactly `[propext, Classical.choice, Quot.sound]` for each of:

- `pma5_16`, `pma5_17`, `pma5_18`, `pma5_19`;
- the left-endpoint and right-endpoint vector derivative probes;
- the degenerate-interval exclusion probe;
- the distinct-quotient-limit probe.

These are recursive dependency reports for those eight declarations. The complete production namespace audit is a separate root integration check.

The implementation contains no proof placeholders, custom axioms, or forbidden proof shortcuts. The main theorem signatures are exactly their corresponding `pma5_N_contract` propositions. The source was stable during the independent final compiler run.

Contract-body SHA256 fingerprints:

| Contract | Fingerprint |
|---|---|
| `pma5_16_contract` | `b06050f3dbdf1a93bfe29a1fb6d8885d3a90e80841061dae005e44680e76ca1a` |
| `pma5_17_contract` | `59b8967e00c1d9ef60819db6ebe33ff38fa17c9f2f93b5065208eeebe8ed6793` |
| `pma5_18_contract` | `f5b78cb580b359fc0015189ff962590072906409102f588bf4c45ce608319e1d` |
| `pma5_19_contract` | `13dee4559eaf66ac02b666348777895f2c97ae659b520e2347c0a5c4c78e0787` |

Fingerprints cover each exact definition block, with trailing whitespace trimmed and any subsequent module-comment header excluded; they do not normalize mathematical expressions.
