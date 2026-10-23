# The C2 vector-potential obligation in 10.43

Independent reviewer: ch8_fidelity. Status: unresolved; this note is not a counterexample or an approval to weaken the printed contract.

The authorized Rudin scan was inspected visually, including a high-resolution crop of printed p.282. The vector-potential conclusion in 10.43 explicitly requires C2 regularity for a divergence-free C1 input. The scalar-potential conclusion also requires C2, but its upgrade is elementary because all first partials equal the C1 input. That argument does not apply to a curl equation, which specifies only antisymmetric combinations of first partials.

The accepted radial homotopy proof of 10.39 produces a C1 primitive from a closed C1 form. It supplies a C1 vector potential in degree two. A separate regularity theorem is needed for the stronger printed 10.43 conclusion.

The scalar upgrade has been implemented and parent-compiled green in PotentialRegularity.lean, in particular contDiffOn_two_of_coordinatePartials_eq. Its complete proof was independently read: the finite coordinate expansion promotes the Fréchet derivative to C1, hence the scalar function to C2. Exact reviewed module SHA256: `7670f6c309da576976eb65205078fed0dd0fec9c70ff3f1c5cb37c1cde3d52d7`. This does not discharge the vector-potential clause.

Relevant primary sources consulted:

- Dacorogna, Fusco, Tartar, [On the solvability of the equation div u = f in L1 and in C0](https://www.bdim.eu/item?fmt=pdf&id=RLIN_2003_9_14_3_239_0), Rend. Lincei 14 (2003), pp.239–244. Their endpoint counterexample concerns continuous data with no Lipschitz solution. This does not, without an additional argument, refute the distinct C1-data/C2-solution assertion.
- Berselli and Longo, [Classical solutions of the divergence equation with Dini-continuous datum](https://arxiv.org/html/1712.07917), introductory discussion and main regularity setting. Dini continuity provides a sufficient classical regularity condition, while plain continuity can fail. The paper does not directly establish the required one-higher integer endpoint here.
- Khesin, Kuksin, Peralta-Salas, [KAM theory and the 3D Euler equation](https://www.math.toronto.edu/khesin/papers/KAM_Euler_AdvMath.pdf), Lemma2.3. Their stated surjectivity assertion for curl explicitly uses noninteger regularity. This is a warning against silently substituting a Hölder/Hodge theorem at an integer endpoint, not a proof that the present assertion is false.
- Wendl, [Analysis III notes](https://www.mathematik.hu-berlin.de/~wendl/Winter2019/Analysis3/Skript_DifferentialFormen.pdf), Theorem1.5, p.3. These independent lecture notes distinguish the C2 scalar potential from the merely C1 vector potential furnished by their Poincare argument. They supply the weaker comparison, not a counterexample to Rudin's stronger statement.

A useful reduction, independently checked: if every C1 divergence-free field on R3 had a C2 vector potential, then every C1 scalar f on R2 would admit a C2 planar vector field with divergence f. Apply the assertion to F(x,y,z)=(0,0,f(x,y)) and restrict the third component of curl G=f to z=0, using the planar field (G2,-G1). Establishing or refuting this exact planar surjectivity would settle the proposed obstruction. The known C0 counterexample cannot simply be differentiated or integrated without checking all other partial derivatives.

No production contract was changed on the basis of this research. The exact C2 vector-potential clause remains an outstanding mathematical requirement.
