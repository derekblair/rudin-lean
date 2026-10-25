# Independent source-fidelity review: PMA 9.16 counterexamples

Reviewed the two warning assertions in PMA third edition, printed p. 215, and the counterexample modules below. These modules give explicit witnesses for those assertions; their comments explicitly distinguish the chosen witnesses from full solutions of the referenced exercises.

Reviewed source blobs:

- `rudin/Rudin/PMA/Chapter09/DiscontinuousPartials.lean`: `a8edcdf240566910af65e39b6cf29c00fe0d2e0a`
- `rudin/Rudin/PMA/Chapter09/PartialCounterexamples.lean`: `049c139d69145bd1c405945b17d3c7e5084736b2`

Result: both examples establish the required warnings with no hidden continuity or total-differentiability assumptions. No mathematical changes requested.

## Partial derivatives do not imply continuity

`DiscontinuousPartials.lean` uses `f(x,y) = xy/(x²+y²)`, with value zero at the origin under Lean's totalized division. The source establishes all coordinate partial derivatives at **every** point, not only at the origin. Away from zero the denominator is positive, giving ordinary total differentiability; on both coordinate axes through zero the function is identically zero. Along the punctured diagonal `(t,t)` the value is `1/2`, disproving continuity at zero by uniqueness of limits. The final existential theorem states exactly this failure of implication on Euclidean two-space.

## Even continuity and all partials do not imply differentiability

`PartialCounterexamples.lean` uses `g(x,y) = xy/‖(x,y)‖`, again zero at the origin. Its norm is the Euclidean norm, hence the displayed denominator is `sqrt(x²+y²)`. The bound `|g(x)| ≤ ‖x‖` supplies continuity at zero, and the quotient is differentiable away from zero. Both coordinate partials at zero exist and are zero; together with off-origin differentiability this supplies every coordinate partial everywhere. On the diagonal the identity `g(t • (1,1)) * ‖(1,1)‖ = |t|` contradicts total differentiability at zero via nondifferentiability of absolute value. The final existential theorem includes global continuity, all partials everywhere, and failure of total differentiability at zero.

Both modules use `EuclideanSpace ℝ (Fin 2)` and standard coordinate vectors. A scalar codomain is the book's real-valued special case. In the first module the coordinate vector is `pma9_coordinate`; in the second it is definitionally the same standard Euclidean basis vector. `HasLineDerivAt` and `LineDifferentiableAt` express the scalar coordinate partials from 9.16.

The sole fidelity variation is the explicitly documented choice of convenient witnesses rather than claiming to formalize the full exercises referenced by Rudin. A source search found no `sorry`, `admit`, or new axiom in either module. Compiler and recursive axiom results for the final imports are recorded by the root agent; author-reported named-build confirmation for `DiscontinuousPartials` was received (8925 jobs, success).

Final author-reported compiler confirmation: `lake build Rudin.PMA.Chapter09.PartialCounterexamples` exited 0, built in 5.5s, and printed `Build completed successfully (8924 jobs).` No warnings. Both reviewed source hashes remained unchanged after these final compiler confirmations.

The continuous-counterexample author also confirmed an axiom audit of 11 declarations at blob `049c139d69145bd1c405945b17d3c7e5084736b2`: only `propext`, `Classical.choice`, and `Quot.sound`.
