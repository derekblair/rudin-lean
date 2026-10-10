# Independent semantic review: PMA 5.6

**Verdict: ACCEPTED for the isolated draft. All nine contract conjuncts and the boundary probe match the accepted inventory. No semantic correction or blocker.**

Reviewer: fresh middle-node agent, which did not author the oscillation implementation. Read the actual definitions, contract, all proof helpers, final proof and boundary probe in `rudin/Chapter05OscillationDraft.lean`. Compared against `research/pma-ch05-inventory.md` and its independent acceptance in `evidence/pma-ch05-source-review.md`; also checked the invoked Chapter 4 zero-extension definition and nonexistence-of-one-sided-limit theorem. No book content was copied or reproduced.

Reviewed source SHA-256: `5435a5f94465a0017c7d1bafd4b73d4aa7db7ee292911d435f42561a044c4a2a`.

## Nine-conjunct fidelity check

| Conjunct | Actual formal claim | Finding |
| --- | --- | --- |
| 1 | `OscillationLinear 0 = 0` | Correct source zero extension. The leading factor makes the totalized reciprocal harmless at zero. |
| 2 | `Continuous OscillationLinear` | Full continuity on the real line, including zero, not merely continuity away from zero. |
| 3 | For every nonzero `x`, the linear example has derivative `sin(1/x) − cos(1/x)/x`. | Correct formula and required nonzero restriction. |
| 4 | The linear example is not differentiable at zero. | A genuine negative differentiability assertion, not an arbitrary derivative value. |
| 5 | `OscillationQuadratic 0 = 0` | Correct source zero extension. |
| 6 | `Differentiable ℝ OscillationQuadratic` | Every real point, including zero. |
| 7 | `HasDerivAt OscillationQuadratic 0 0` | The derivative at zero is explicitly zero. |
| 8 | For every nonzero `x`, the quadratic example has derivative `2*x*sin(1/x) − cos(1/x)`. | Correct formula and required nonzero restriction. |
| 9 | `¬ ContinuousAt (deriv OscillationQuadratic) 0` | Discontinuity of the actual derivative of the everywhere differentiable function, not of an unrelated totalized formula. |

The formulas use real inputs and real outputs. Their displayed reciprocal formulas agree literally with the source away from zero; the two explicit zero equalities prove agreement at zero as well. No unintended domain restriction or endpoint hypothesis is present.

## Proof and boundary checks

The first example's difference quotient at zero is identified with Chapter 4's zero-extended oscillating sine. Its proved lack of a finite right limit excludes differentiability at zero. The quadratic example's difference quotient is the continuous linear example, so its derivative at zero exists and is zero. At positive reciprocal multiples of `2π` arbitrarily near zero, its actual derivative is `−1`; this contradicts continuity at the derivative value zero.

The boundary probe `oscillationQuadratic_offZero_formula_wrong_at_zero` is meaningful: it proves that extending the off-zero formula to zero yields `−1`, while the true derivative there is `0`. Thus dropping the nonzero condition would change the mathematics.

Independent command `./lake-local env lean Chapter05OscillationDraft.lean` passed with exit 0. An independent in-memory compilation recursively audited every one of the draft's **19 named declarations**; all depend only on `propext`, `Classical.choice`, and `Quot.sound`. Source scanning found no proof placeholders, custom axioms, or native decision procedures.

The same in-memory compilation combined the unchanged oscillation and middle drafts and proved this additional integration probe, also using only standard axioms:

```lean
theorem oscillation_secondKind_independent_probe :
    Chapter04.SecondKindDiscontinuityOn (-1) 1 (deriv OscillationQuadratic) 0 := by
  have hi : (0 : ℝ) ∈ Ioo (-1) 1 := by norm_num
  have hnc : ¬ Chapter04.FunctionContinuousWithinAt (Ioo (-1) 1)
      (deriv OscillationQuadratic) 0 := by
    intro hc
    exact oscillationQuadratic_deriv_not_continuousAt_zero
      ((Chapter04.interval_continuity_iff (deriv OscillationQuadratic) hi).mp hc)
  refine ⟨hi, hnc, ?_⟩
  intro hlim
  have hn := (pma5_12 OscillationQuadratic (deriv OscillationQuadratic) (-1) 1
    (by norm_num) (fun x _ =>
      (oscillationQuadratic_differentiable x).hasDerivAt.hasDerivWithinAt)).2.2.2 0
  exact hn ⟨hi, hnc, hlim⟩
```

This verifies that 5.6(b), together with the full 5.12 corollary, indeed supplies the accepted second-kind possibility. The probe was not inserted into either source file.

## Scope and integration limits

Pinned Mathlib supplies trigonometric derivatives and periodicity, as expressly allowed by the inventory even though the book discusses these functions further in Chapter 8. The review does not claim that underlying library proofs obey book-order dependencies. No accepted mathematical scope of 5.6 is omitted. Full chapter integration and its final build remain the root's gate. This review wrote only this evidence file and did not modify any source, shared checkout, book, session, global configuration, Git commit, or remote state.
