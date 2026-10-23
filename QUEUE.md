# Needs-insight queue

Statements that resisted proof automation and are waiting for a
mathematician's idea. Each entry records: chapter, statement reference,
what was tried, and what seems to be missing.

_PMA-10.43 has an unresolved C2 vector-potential clause, recorded below. Chapters 1–7 are complete. The isolated Chapter 8 lane covers 8.1–8.6; 8.7–8.22 remain pending rather than attempted-and-blocked. Chapter 9 is complete at 43/43 numbered nodes; Chapter 10 work is active under the user’s new instruction; Chapter 11 is pending. All completed nodes have passing builds and axiom audits._

## PMA-10.43 — C2 vector potential from C1 divergence-free data

**Status:** needs insight; the full numbered node is not completed.

**Exact statement:** on an open subset E of real three-space that is C2-equivalent
to a convex open set, every C1 vector field F with div F = 0 admits a C2 field G
with curl G = F on E. The C2 output was independently checked against the
authorized source at high resolution. No extra regularity assumption on F is
part of the accepted contract.

**Proved partial content:** both forward identities curl(grad u)=0 and
div(curl G)=0 for C2 inputs; the full C2 scalar-potential converse; all stated
form/operator bridges; and a separately named C1 vector-potential converse.
The exact full contract remains in VectorPotentials.lean, with no theorem
asserting the full contract and no proof placeholder.

**Tried:** the proved radial Poincaré homotopy and C2 coordinate transport yield
a C1 primitive. The scalar upgrade works because all first partials are the
C1 input components; the curl equation controls only antisymmetric combinations
and does not give that argument for a vector potential. Searches of the pinned
library and primary literature found regularized/Hölder sufficient results but
no verified proof at this exact integer endpoint. Known continuous-data
counterexamples do not by themselves refute this one-higher regularity claim.

**Missing:** a valid regularity/existence argument producing a C2 vector
potential for C1 divergence-free input, or a rigorous counterexample to the
printed statement. Local C2 solvability on balls would suffice with a proved
global patching argument. The accepted statement has not been weakened to a
C1 conclusion or strengthened to a C2 input. See
`research/pma-ch10-potential-regularity.md` for exact evidence and limitations.
Later independent nodes may be completed in book order with this explicit gap;
none is counted as completing PMA-10.43.
