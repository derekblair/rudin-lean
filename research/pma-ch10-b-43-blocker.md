# PMA 10.43: remaining vector-potential regularity obligation

The source is printed pp. 281–282. Its last clause asks for a **C² vector
potential** for a C¹ divergence-free field on an open domain C²-equivalent to
a convex open set. The exact clause is preserved in
`Rudin.PMA.Chapter10.pma10_43_contract` in `VectorPotentials.lean`.

Reconciliation source:
`bb50a2079f8e189d8e282e2521bbadb64f4f98eb`, branch
`origin/ch8-codex-20261022`. Its existing proof work is retained unchanged:

- `pma10_43_forward` proves both identities for C² input.
- `pma10_43_scalar_converse` proves the C² scalar potential conclusion.
- `vectorPotential_c1_of_equivalent_convex` proves a C¹ vector potential
  conclusion, explicitly distinguished from the printed C² conclusion.

The proved all-degree Poincaré lemma constructs a C¹ primitive of a closed C¹
form. This resolves existence with one continuous derivative but does not
establish the required second derivative. In the scalar case every first
partial equals a component of the given C¹ field, so `PotentialRegularity.lean`
can upgrade regularity. A curl equation only fixes antisymmetric combinations
of first partials; the scalar upgrade does not apply.

The prior branch already records attempted radial-homotopy regularity,
local/global potential approaches, and the reduction to the planar divergence
equation. The present independent source and proof review confirms that these
are not compiler or representation omissions. No proof of the exact endpoint
regularity and no rigorous counterexample have been established in this lane.
In particular, neither a merely C¹ conclusion nor an added Hölder hypothesis
is being substituted for the source statement.

Thus node 10.43 remains incomplete. There is no principal `pma10_43` theorem
and no axiom asserting its missing clause. `SecondHalfAudit.lean` explicitly
checks the principal remains absent and audits the existing partial results
with the other imported Chapter 10 declarations. All other assigned nodes
are reconciled against existing principal proofs, with fresh verification
recorded separately from this mathematical blocker.
