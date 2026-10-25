# Source-fidelity review: PMA 9.39–9.41

Reviewer: determinants subagent, independent of the authorship of the original
9.39–9.41 definitions/proofs. Source: PMA third edition, printed pages 235–236.
The mixed-partial corollary was checked visually in the local PDF.

Final reviewed file SHA-256:
`dd0873bc49f66a487f71ed274657385b01f334d4fa6c33c012e9b4facc02bf1b`.

## Source comparison

- 9.39 defines coordinate partial derivatives by actual one-variable derivatives,
  then the second partial as composition in the printed order. Its C2 predicate
  explicitly requires the open domain, existence of the first partials,
  differentiability of those partial functions, and continuity of the second
  partials. This matches the printed definition, rather than silently replacing
  partial existence by a stronger total differentiability assumption on f.
- 9.40 assumes precisely existence of D1f and D2D1f on the open domain. Its
  rectangle is contained in that domain and both side lengths are nonzero.
  Unordered intervals preserve negative as well as positive side lengths.
  The point is in the interior in both coordinates, and the signed product hk
  appears in the conclusion. No derivative-continuity assumption was added.
- 9.41 assumes existence of D1f, D2f, and D2D1f in the open domain and continuity
  of D2D1f only at the distinguished point. It concludes existence of D1D2f
  with the stated derivative, rather than assuming that derivative exists.
- The direct corollary establishes the equality at every point under continuity
  on the domain. This is slightly stronger than the printed C2 corollary.

No substantive statement defect was found in the rectangle or weak mixed-partial
theorems. These proofs avoid replacing the weak printed hypotheses by C2.

## Changes resulting from review

The mapping C2 predicate could lose its open-domain requirement when the target
has zero coordinates. With the original author's agreement, the reviewer made
`IsOpen E` explicit outside the component quantifier.

The reviewer also added `pairCoordinates`, coordinate-slice compatibility lemmas,
and `pma9_41_of_pma9_39`: an explicit theorem taking the native two-coordinate C2
definition as hypothesis and concluding equality of the two second partials.
This closes the interface between the Fin2 definition and the pair-based theorem.
The core weak theorem and its proof were not changed. These appended bridge
lemmas are reviewer-authored and therefore need the integrating agent's own
inspection; they are not claimed to have an independent authorship review.

Verification: `lake build Rudin.PMA.Chapter09.HigherDerivatives` exited0 with
`Build completed successfully (8928 jobs).` There are two harmless unused simp
argument warnings in the finite-index bridge proof. Final namespace axiom auditing
is delegated to the integration audit.
