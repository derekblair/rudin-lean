# Needs-insight queue

Statements that resisted proof automation and are waiting for a
mathematician's idea. Each entry records: chapter, statement reference,
what was tried, and what seems to be missing.

Chapters 1–9 are complete. Chapter 10 has 50 of 51 nodes complete; Chapter 11
is pending.

## PMA-10.43 — C² vector-potential converse

The exact four-clause contract remains in
`rudin/Rudin/PMA/Chapter10/VectorPotentials.lean`. Both forward identities and
the C² scalar-potential converse are proved. The separately labeled
`vectorPotential_c1_of_equivalent_convex` proves only a C¹ vector potential.
The final printed C² vector-potential clause is unproved; there is no
`pma10_43` principal theorem and no proof placeholder or added axiom.

This integration preserves the source lane's state and does not attempt the
separate research obligation. See [the retained blocker record](research/pma-ch10-b-43-blocker.md)
for attempted approaches and the missing regularity argument.
