# PMA 10.43: gauge regularization and a rigorous Coulomb obstruction

Ticket #14; research branch `research/t14-1043`, based on `05c9ea2f709ce854be0b794350a818d9ebd102f8`.

This is an **obstruction report**, not a proof or disproof of the printed clause. It adds a kernel-checked characterization of every allowable gauge, an informal local-to-global reduction, and an explicit admissible field for which every C² Coulomb representative is impossible even though a C² potential exists. The exact classical endpoint remains unresolved by this work. Neither the contract nor the Chapter 10 audits are changed, and the original blocker record is preserved.

## Evidence levels

- **Lean-proved:** the gauge classification and equivalences in `PMA1043Gauge.lean`; the full-plane divergence reduction and coordinate-antiderivative obstruction in `PMA1043Planar.lean`. The original first three clauses and C¹ potential theorem remain the input results.
- **Informally proved:** the explicit radial example, homogeneous-logarithmic Poisson obstruction, failure of C² Coulomb gauge, local-to-global patching, and the planar candidate analysis below. The complete arguments are supplied; they are not represented as kernel proofs.
- **External results:** only the precisely scoped published regularity results cited below. They are not imported into Lean.
- **Unresolved:** existence of some C² potential for every field in the unchanged contract. No claim that this question is open in the literature is made.

## Sibling research acknowledgement (2026-10-26)

[PR #24](https://github.com/derekblair/rudin-lean/pull/24), merged into main at `c1f0fa6f4905a97f77423a8eca4dce61f6cc5e68`, independently landed sibling results in [`rudin/Rudin/PMA/Chapter10/VectorPotentialGaugeResearch.lean`](../rudin/Rudin/PMA/Chapter10/VectorPotentialGaugeResearch.lean) and [`rudin/Rudin/PMA/Chapter10/PlanarVectorPotentialResearch.lean`](../rudin/Rudin/PMA/Chapter10/PlanarVectorPotentialResearch.lean). Those modules cover much of the gauge and planar mathematics presented in §§2 and 5 below. The coordinator-appointed review's overlap table classifies this PR's 32 theorem/lemma declarations (nine gauge and 23 planar) as follows:

- **19 duplicate mathematical statements** in the PR #24 modules.
- **1 equivalent repackaging:** `same_curl_iff_gradient_gauge` combines the same classification and its reverse implication.
- **7 newly named elementary map helpers** for the projection/inclusion representation, with no new mathematical reduction.
- **5 genuinely new theorem statements:** `pma10_43_contract_iff_gauge_regularization`, `c2_of_c3_regularizing_gauge`, `contDiff_planarCoordinateField`, `planarDivergence_coordinateField`, and `no_c1_planarDivergence_implies_no_c1_coordinatePrimitive`.

The substantive new results are the contract–gauge-regularization equivalence, the C³-gauge corollary, and the coordinate-antiderivative lifting obstruction; the two coordinate-field lemmas support that obstruction. No statement contradicts the sibling modules. This PR stands as an explicitly independent research snapshot. Consolidation of the overlapping interfaces is a maintenance question for later; no consolidation is claimed here.

## 0. Fidelity

The source is PMA, third edition, printed pp.281–282, visually inspected in the relocated local PDF `/home/derekblair/projects/math/references/sources/pma3.pdf` (PDF pp.290–291). The brief's `~/sources/pma3.pdf` path is absent. Printed 10.40 on p.280 defines C²-equivalence by a one-to-one C² map onto an open set, with a C² inverse.

The final clause of `VectorPotentials.lean` agrees: U,E are open subsets of R³, U is convex, both maps in `C2DomainEquivalence U E` are C² on their domains and inverse there, F is C¹, div F=0 on E, and the asserted G is C² with curl G=F on E. The ambient extensions need not be inverse or regular outside the domains. Quantifying over a witness of equivalence is equivalent to assuming one exists because the conclusion is independent of the witness. No source/contract mismatch was found. In particular, the C² output is printed, not an accidental formal strengthening.

## 1. The fixed radial operator really fails to gain the derivative

For a C¹ closed k-form, the radial coefficients are

    (Hω)_I(x) = Σ_j x_j ∫₀¹ t^(k−1) ω_{jI}(tx) dt.

One differentiation produces terms involving ω and Dω. A formal second differentiation contains

    Σ_j x_j ∫₀¹ t^(k+1) ∂m∂ℓω_{jI}(tx) dt,

which is not justified by C¹ input. Closure controls antisymmetric combinations; it does not give each Hessian entry. This is an actual regularity failure, not just a differentiation-proof gap.

For F(x,y,z)=(0,0,|x|^(3/2)) on R³, the radial potential with the repository's orientation is

    A=(2/7)(−y|x|^(3/2), x|x|^(3/2), 0).

It is C¹ and curl A=F. But ∂xx A₁=−(3/14)y|x|^(−1/2) off x=0, and A₁ is not twice differentiable at x=0,y≠0. Nevertheless

    G=(0,(2/5)x|x|^(3/2),0)

is C² and curl G=F. Moreover G−A=∇φ with φ=(4/35)xy|x|^(3/2), a C² scalar which is not C³ near those points. This example proves sharpness only for the fixed radial operator and explicitly disproves the inference from its failure to nonexistence.

## 2. Exact gauge obligation, now in Lean

`PMA1043Gauge.lean` proves, on the exact domains of the contract:

1. `same_curl_iff_gradient_gauge`: two C¹ fields have the same curl iff G=A+∇φ on E for some C² scalar φ.
2. `c2_vectorPotential_iff_regularizing_gauge`: for a fixed C¹ primitive A of F, existence of a C² primitive is equivalent to existence of φ∈C² with A+∇φ∈C².
3. `no_c2_vectorPotential_iff_no_regularizing_gauge`: nonexistence is equivalent to failure of this regularity for **every** C² scalar φ.
4. `c2_of_c3_regularizing_gauge`: if φ is C³ and A+∇φ is C², then A was already C². A repair of a non-C² primitive must therefore use the larger class of C² gauges.
5. `pma10_43_contract_iff_gauge_regularization`: the unchanged four-clause contract is equivalent to `VectorPotentialGaugeRegularization`, universally over the admissible F and their C¹ primitives.

The classification uses the existing scalar converse on G−A, together with curl linearity and curl∇φ=0. The reverse contract implication uses the existing C¹ vector primitive. These are equivalences and implications, not an unconditional existence theorem. No `pma10_43` principal is introduced.

## 3. A Poisson obstruction that is strong enough to test Coulomb gauge

The following direct calculation is informal mathematics. Work in B_R(0)⊂R³ with R<exp(−2); write r=|x| and t=log(1/r) off zero. Let P_m be a nonzero harmonic homogeneous polynomial of degree m≥2, Y_m=P_m restricted to the unit sphere, and define

    v_m=P_m log t,
    q_m(t)=−(2m+1)/t−1/t²,
    g_m=(P_m/r²)q_m(t).

Extend both by zero at the origin. Then v_m is C^(m−1), g_m is C^(m−2), and on the punctured ball

    Δv_m=g_m.

Indeed Δ(P_m L)=P_m[L''+(2m+2)L'/r], and L=log t has L'=−1/(rt), L''=(t−1)/(r²t²). Derivatives of v_m of order j≤m−1 are O(r^(m−j)log t) plus smaller terms; derivatives of g_m of order j≤m−2 are O(r^(m−2−j)/t). Difference quotients and these bounds give the claimed extensions through zero. The derivative tensor satisfies D^m v_m=(D^m P_m)log t+O(1/t), with D^m P_m a nonzero constant tensor, so v_m is not C^m.

**No C^m solution of Δu=g_m exists near zero, regardless of boundary conditions.** Normalize the degree-m spherical projection

    b(r)=∫S² u(rθ)Y_m(θ)dσ / ∫S²Y_m²dσ.

The eigenvalue m(m+1), polar Laplacian, and integration by parts on S² give

    b''+2b'/r−m(m+1)b/r² = r^(m−2)q_m(t).

Its general solution is

    b(r)=r^m log t+c r^m+d r^(−m−1).

Boundedness at zero forces d=0. Taylor expansion of a C^m function and orthogonality to spherical polynomials of degree below m give b=O(r^m), contradicting b/r^m=log t+c. This proves nonexistence. In particular m=2 gives continuous data with no C² Poisson solution, while m=3 gives C¹ data with no C³ Poisson solution.

### An admissible field with no C² Coulomb potential

Take P=P₃=x₁³−3x₁x₂², q=q₃, and

    a(t)=∫₀∞e^(−4s)q(t+s)ds,
    G₀(x)=x(P(x)/r²)a(t),       G₀(0)=0,
    F=curl G₀.

This integral is absolutely convergent. Differentiation under the integral gives a,a',a''→0 as t→∞; integration by parts gives 4a−a'=q. The prefactor xP/r² is smooth off zero and homogeneous of degree 2. For j≤2 its derivatives are O(r^(2−j)), so the product-rule bounds prove G₀∈C², with its derivatives through order 2 zero at zero. Direct differentiation gives

    div G₀=(P/r²)q=g₃,
    F(x)=a(t)(∇P(x)×x)/r²     (x≠0).

Thus F∈C¹ and div F=0, and G₀ already satisfies the exact desired conclusion on the open convex ball.

Suppose another C² potential G near zero also satisfied div G=0. On a smaller ball, H=G−G₀ is C² and curl-free, so H=∇ψ for a scalar ψ. Every first partial of ψ is C², hence ψ is C³. But Δψ=−g₃, contradicting the preceding Poisson obstruction (with sign reversed). Therefore **every C² Coulomb representative is excluded**, even locally, while the unrestricted C² potential G₀ exists.

The identity curl curl G=∇div G−ΔG therefore cannot justify a universal C² Coulomb construction from the exact hypotheses. Nor can one first assume a C² potential and normalize it to Coulomb gauge while preserving C²: the necessary C¹-to-C³ scalar Poisson step can fail. This is a rigorous obstruction to that proof route, not a counterexample to the printed clause.

## 4. The global problem reduces to the local endpoint on balls

Define the local ball principle: every C¹ divergence-free field on an open ball has a C² potential in a neighborhood of each point. **Informally, this principle is equivalent to the missing global clause**, using the existing global C¹ theorem.

The global clause implies the principle by identity equivalence on a ball. Conversely, let E,F satisfy the contract and let A∈C¹(E) be the already-proved primitive. The local principle supplies C² potentials H_i on a cover by small balls B_i⊂E. The scalar converse on each ball gives

    A−H_i=∇φ_i,       φ_i∈C²(B_i).

Choose a smooth locally finite partition {χ_i} subordinate to a locally finite refinement, with each support compactly contained in its assigned ball. Reindex the H_i,φ_i if necessary. Products extend by zero across the edge of each ball. Put

    Φ=Σχ_iφ_i,        G=A−∇Φ.

The locally finite sum Φ is C², so curl G=F. Expanding the derivative yields

    G=Σχ_iH_i−Σφ_i∇χ_i,

which is C². This also proves the gluing lemma on any open E with a global C¹ primitive. The domain equivalence is used only to obtain A; its third derivatives are never required. Thus the transport loss recorded in the original blocker does not need to be solved directly. The unsolved issue can be isolated on ordinary small Euclidean balls.

The partition argument is not Lean-formalized here; the exact gauge classification needed in it is.

## 5. Counterexample attack: planar divergence and the lifting gap

For an open planar domain D and open interval I containing z₀, set F(x,y,z)=(0,0,f(x,y)). Then f=div u with u∈C²(D;R²) iff F=curl G with G∈C²(D×I;R³). The lift is G=(−u₂,u₁,0). Conversely restrict **any** potential, including any z-dependent gauge, by u=(G₂(x,y,z₀),−G₁(x,y,z₀)); the third curl component gives div u=f. A disk times an interval is convex, so a C¹ datum without a C² divergence solution would meet the exact counterexample hypotheses.

**Lean status:** `PMA1043Planar.lean` proves the full-space version as `c2_verticalPotential_iff_planarDivergence`, with `ContDiff ℝ 2` on R³ and R². `pma10_43_contract_implies_planarDivergence` proves that the exact unchanged contract implies C² divergence solvability for every globally C¹ planar datum, using the identity equivalence on R³. The cylinder/local-domain variant just described is informal; it is not claimed as the formal theorem. Neither implication supplies a bad datum.

### Natural logarithmic candidates have explicit solutions

Let D=B_R(0)⊂R², R<exp(−T), and write r=|x|, θ=x/r, t=log(1/r). Suppose a∈C²(S¹), q∈C¹((T,∞)), and q,q'→0 at infinity. Define, off zero,

    f=r a(θ)q(t),
    b(t)=∫₀∞e^(−3s)q(t+s)ds,
    u=x r a(θ)b(t),

and extend f,u by zero. Then f∈C¹ and **u∈C² with div u=f**. To check it, rewrite b=e^(3t)∫_t^∞e^(−3v)q(v)dv. Thus b'=3b−q and b''=9b−3q−q', so b,b',b''→0. The prefactor x r a(θ) is C² off zero and homogeneous of degree 2; its differentiated bounds prove the C² extension, with all derivatives through order 2 zero at zero. Similarly f=O(r|q|), Df=O(|q|+|q'|) prove the C¹ extension. Euler homogeneity gives div u=r a(θ)(3b−b')=f.

This includes q=c/t+d/t² and finite combinations of smooth angular modes. These fields have actual C² potentials (−u₂,u₁,0), so bad Poisson representatives cannot make them counterexamples.

Even C¹ angular profiles are soluble if q∈C² and q,q',q''→0: split a into its average ā and zero-mean part, choose a periodic C² primitive A of a−ā, and use

    u=e_r r² ā b(t)+e_θ r² A(θ)q(t).

The polar divergence is r[ā(3b−b')+A'q]=r a q, and both terms extend C² by the same bounds. These constructions do not cover arbitrary C¹ data; angular frequency increasing toward zero or simultaneous radial/angular irregularity is not covered by the displayed fixed-profile estimates. Neither feature establishes failure in every gauge.

### A coordinate-antiderivative lift of a bad C⁰ datum is impossible

If g on an open domain is not the divergence of any C¹ vector field, it cannot equal ∂_j f for any jointly C¹ scalar f on that domain: the vector field f e_j would already have divergence g. This implication is elementary and gauge-independent. Its full-plane version for either coordinate is **Lean-proved** as `no_c1_planarDivergence_implies_no_c1_coordinatePrimitive`; it does not even need continuity of g as a separate assumption.

Consequently every individual differentiated equation div V_j=∂_j f for C¹ f already has the C¹ solution V_j=f e_j. A C² u would require V_j=∂_j u to satisfy these equations *simultaneously* with ∂_iV_j=∂_jV_i. That compatibility is not supplied by separate solvability. The known C⁰ divergence obstructions therefore cannot be lifted into the C¹-data problem by a same-domain coordinate antiderivative.

McMullen's Theorem 2.1 excludes all Lipschitz solutions for some L∞ data by open mapping and Ornstein's non-inequality. [Primary repository](http://nrs.harvard.edu/urn-3:HUL.InstRepos:9871963). The indexed primary abstract of Dacorogna–Fusco–Tartar reports continuous-data/Lipschitz nonsolvability. [Primary article record](https://www.bdim.eu/item?id=RLIN_2003_9_14_3_239_0). The full article was not fetched in this run, and the crossed reviewer could not independently retrieve the abstract; this contextual citation is not used in any new proof. Those data classes and derivative counts do not establish C¹-data/C² nonsolvability. The present lifting lemma identifies a specific impossible shortcut; it does not rule out a different higher-order duality or compatible construction.

Introducing an extra coordinate also leaves an uncontrolled term: differentiating div U=h normally and restricting to z=0 yields div_xy(U₁,z,U₂,z)|₀=h_z|₀−U₃,zz|₀. Dropping the final continuous term would impose an extra condition absent from the contract. No construction eliminating this freedom was proved.

These explicit positive constructions and the lifting obstruction are the stopping point of the counterexample attack. No candidate excluding all C² gauges was obtained.

## 6. What a further proof or disproof must supply

Costabel–McIntosh prove in Theorem 3.2 that their regularized Poincaré operators have order −1, and establish one-derivative gain on Sobolev/Besov scales, including B¹∞,∞→B²∞,∞; their Corollary 3.4, Remark 3.5 and Proposition 4.1 do not identify the integer output with classical C². [Primary preprint](https://arxiv.org/abs/0808.2614).

The differentiated-kernel estimate typically involves ∫₀^δω_DF(s)ds/s. C¹ gives a vanishing modulus, not a Dini integral. Berselli–Longo's Dini-data divergence result displays this integral in the derivative-convergence estimate before Theorem 16. It does not supply the required endpoint for arbitrary C¹ data after differentiation. [Primary preprint](https://arxiv.org/abs/1712.07917). No Dini or Hölder hypothesis is added to the contract here.

A sufficient approximation route would produce smooth potentials for smooth closed approximants F_j→F in C¹_loc, with locally uniform bounds through derivative order 2 and equicontinuous second derivatives. Arzelà–Ascoli and a diagonal argument then give C²_loc convergence; local integration on line segments verifies derivative compatibility and curl G=F. A uniform bound alone can yield a C¹,¹ limit and does not give continuous second derivatives. The Coulomb example proves that these controls cannot be universally available in Coulomb gauge. Their availability in some other gauge is unresolved.

An alternative sufficient estimate avoids requiring equicontinuity a priori: on fixed concentric balls, if every smooth divergence-free H has some smooth potential with C² norm on the smaller ball bounded by a constant times the C¹ norm on the larger ball, use smooth closed approximants and a subsequence with summable C¹ increments. Choose a controlled potential for each increment and sum in C² on the smaller ball. Linearity of the choices is unnecessary. The missing uniform estimate is not asserted; this is a precise target for another attack.

A disproof must furnish a C¹ field and exclude all C² gauges, exactly as the Lean criterion states. Failure of an operator, failure of Coulomb normalization, and continuous-data divergence counterexamples alone do not meet this requirement.

## Verification and review

The commands below record validation of the pre-merge research snapshot `c034f119`, run from `rudin/` unless noted otherwise. The production default build and explicit research-module builds passed. The research modules remain standalone: they are deliberately not added to the frozen production Chapter 10 inventory or its audits. The declaration count includes the overlap with PR #24 detailed in the sibling acknowledgement above.

- `lake build`: exit 0, 9204 jobs; existing recursive chapter audits passed.
- `lake build Rudin.Research.PMA1043Gauge`: exit 0.
- `lake build Rudin.Research.PMA1043Planar`: exit 0.
- `lake env lean ../research/pma10-43-axioms.lean`: exit 0; recursive axiom dependencies for all 32 new theorem/lemma declarations are only `propext`, `Classical.choice`, `Quot.sound`. This explicitly checks the standalone research modules in addition to the production default build.
- `python3 scripts/verify_ch10_integration.py` (repository root): exit 1 because its historical manifest has 19 stale file hashes. Every mismatching file is byte-identical to base commit `05c9ea2`; the new research files cause no inventory, reachability, principal-count, or forbidden-token error. This pre-existing provenance failure is not repaired in this scope. The contract, original blocker, production sources, and audits remain byte-identical to the base.

The merge of main `c1f0fa6` also inherits the integration failures recorded by the coordinator review: the same 19 stale hashes plus three inventory/reachability errors from the sibling modules. These are ticket #25's scope; this fix does not change the integration script or manifest.

Review status (2026-10-26): the programme's prescribed coordinator-appointed crossed review was **PENDING** when this report was written. As of this fix, that review (Codex on dominic) has been carried out and returned **FAIL on documentation grounds**; this fix cycle responds to those findings, and the landing decision follows its re-review. The author-arranged supplemental Claude review on dominic passed the obstruction-report category at commit `c1c787a`; it does not satisfy any landing gate. That supplemental reviewer independently re-elaborated both research modules and all 32 axiom checks; the informal proofs were checked mathematically and remain unformalized. The full default build was not independently repeated by that supplemental reviewer, and the citation limitation above is explicit. The supplemental review record identifies the exact documentation delta and reviewed bytes. No landing merge or change of node status is part of this research deliverable.
