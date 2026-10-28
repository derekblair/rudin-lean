# PMA 10.43: an exact quantitative obstruction

Date: 2026-10-27. Research lane `thm-1043-final-clause`, base main `83e06ca`. Outcome: **obstruction report**, not an endpoint proof or counterexample. Coordinator-appointed crossed review is pending; this lane has not arranged one.


## Additions beyond merged PRs #21 and #24

| Addition | Evidence level | Exact limit |
| --- | --- | --- |
| Closed-row trace and differentiated-column compatibility equivalences | Kernel-checked in [`PMA1043Compatibility.lean`](../rudin/Rudin/Research/PMA1043Compatibility.lean) | Whole-plane planar problem; no universal solvability assertion |
| Full contract iff the all-gauge quantitative condition (Q) | Informal proof, §§1–4 below | Neither (Q) nor its negation established |
| Gauge-independent adjoint certificates, including a higher-order planar template | Informal integration-by-parts proof, §5 | No divergent certificate sequence obtained |
| Increasing-frequency annular candidates repaired by explicit primitives | Informal estimates and reproducible computation, linked supplement | Does not cover arbitrary C¹ data or cancellation-heavy superpositions |

The issue body, its full comment history, both merged research branches, and the landed obstruction reports were read before this work. The old source branch's `VectorPotentials.lean` is byte-identical to current main's file. This report extends the existing obstruction; it does not repeat the previous fixed-angular-profile construction as new work. In particular, the full-contract ⇒ planar-solvability implication remains **one-way**. The quantitative equivalence below is a distinct, three-dimensional statement.

## Result and evidence level

The previously recorded local smooth-data C¹-to-C² estimate is **necessary as well as sufficient** for the exact final clause. More precisely, the clause is equivalent to boundedness of the minimum C² norm over **all** gauges, for smooth divergence-free fields on one fixed pair of concentric balls. This sharpens §6 of `research/pma10-43-endpoint-obstruction.md`, which gave the estimate only as a sufficient target.

This note supplies a complete ordinary-mathematics argument, including the functional-analytic necessity, the smooth-versus-C² output distinction, and a gauge-independent dual lower-bound certificate. **None of these new assertions is claimed as Lean-proved.** The existing C¹ global primitive and scalar gauge classification used in the patching step are kernel-proved in the repository; patching itself remains ordinary mathematics. No uniform bound or divergent sequence is established here, so the printed endpoint remains unresolved.

The functional-analytic input is the standard open mapping theorem for Fréchet spaces. A primary author-hosted source checked in this run is Kiril Datchev, *Fréchet spaces* (March 3, 2025), examples on p.2 and Theorem 2 on pp.2–3: <https://www.math.purdue.edu/~kdatchev/546/frechet.pdf>. It verifies that the compact derivative seminorms give the Cᵐ spaces their Fréchet structure, and that continuous linear surjections between these spaces are open. The reduction below is our derivation, not a claim from that source.

## 1. Fixed-radius formulation

Write B_r for the open Euclidean ball in R³ centered at zero. For a function defined near its closure, use the componentwise norm

    ||v||_{k,r} = max_{i, |α|≤k} sup_{x∈B̄_r} |∂^α v_i(x)|.

Let S be the vector space of smooth vector fields H defined on some neighborhood of B̄₁ and divergence-free on that neighborhood. The neighborhood can depend on H. For H∈S set

    m(H) = inf { ||A||_{2,1/2} :
      A is C² on some neighborhood of B̄_{1/2},
      curl A = H on some neighborhood of B̄_{1/2} }.

The set is nonempty for every such smooth H: the classical radial homotopy on a ball gives a smooth potential. This fact makes m finite; it does **not** give the missing C¹-to-C² bound. In the definition one may require A smooth without changing the infimum, as proved in §4.

The exact quantitative target is

    (Q) There exists C<∞ such that m(H) ≤ C ||H||_{1,1}
        for every H∈S.

The constant is independent of H and of its neighborhood of definition. There are no boundary conditions and no gauge choice. Equivalently, one can ask for an actual C² potential bounded by a fixed constant times ||H||_{1,1}: taking an element within ε of the infimum and slightly increasing the constant handles nonattainment; H=0 has potential zero. These two presentations have the same existence-of-a-constant content.

**Claim.** The exact final clause of `pma10_43_contract` is equivalent to (Q). Since the other three clauses are already proved, the whole existing contract is equivalent to (Q) as well. This assertion concerns the full three-dimensional problem; it does not identify the full contract with scalar planar solvability.

## 2. Necessity by Fréchet open mapping

Assume the exact final clause. Apply it to the identity equivalence on B₁. The map

    T : X = C²(B₁; R³) → Y = {F∈C¹(B₁;R³): div F=0},
    T(A) = curl A,

is therefore onto. Give X and C¹(B₁;R³) the usual topology of uniform convergence of all derivatives through their stated order on compact subsets. They are Fréchet spaces; Y is a closed subspace since divergence is continuous into C⁰(B₁). T is linear and continuous since first derivatives of curl A involve derivatives of A only through order two.

Consider the open neighborhood

    U = {A∈X : ||A||_{2,3/4}<1}.

By the open mapping theorem, T(U) contains a neighborhood of zero in Y. Choose an exhausting increasing sequence of compact balls in B₁. Thus, for some s<1 and ε>0,

    {F∈Y : ||F||_{1,s}<ε} ⊂ T(U).

For H∈S with M=||H||_{1,1}>0, put λ=ε/(2M). Then ||λH||_{1,s}≤ε/2<ε. Consequently λH=T(A₀) for some A₀∈U. Rescaling gives A=A₀/λ with

    curl A=H throughout B₁,
    ||A||_{2,3/4} < (2/ε) M.

Restrict A to a neighborhood of B̄_{1/2}; this proves (Q). If M=0, H is identically zero on B₁ and zero itself is the required local potential. This argument avoids any incorrect assumption that a seminorm on the larger space is a norm or that an infimum is attained.

This proves more than failure of a particular solution operator: if (Q) fails, surjectivity of T is impossible. It therefore yields existence of an admissible field without a C² potential on a ball, although this abstract contrapositive does not exhibit that field.

## 3. Sufficiency by summable approximation and gauge patching

Assume (Q), using its equivalent actual-solution formulation with a fixed enlarged constant C₀. First let F∈C¹(B₂;R³) be divergence-free. Mollify on a neighborhood of B̄₁, using kernels with sufficiently small supports. This gives smooth divergence-free H_j near B̄₁ converging to F in the C¹ norm on B̄₁. Derivatives commute with convolution and div F=0, so these approximants satisfy the closedness condition exactly.

Pass to a subsequence such that

    Σ_j ||H_{j+1}-H_j||_{1,1}<∞.

Choose A₀ for H₀ using (Q), and choose A_j for each increment H_j−H_{j−1}, j≥1, with

    curl A_j=H_j−H_{j−1},
    ||A_j||_{2,1/2}≤C₀||H_j−H_{j−1}||_{1,1}.

The series A₀+Σ_{j≥1}A_j and all its derivatives through order two converge uniformly on B̄_{1/2}. Integrating derivatives along interior line segments shows that the limit A is C² on B_{1/2}, with the expected derivatives. Curl is a first-order operator, so curl A=F there. No equicontinuity hypothesis on the entire family of second derivatives is needed: absolute convergence in the C² norm is the mechanism.

Translation and dilation give a C² potential near every point for every C¹ divergence-free field on an arbitrary open set. For a domain E allowed by the printed contract, the existing theorem `vectorPotential_c1_of_equivalent_convex` supplies a global C¹ primitive A. Choose a locally finite cover by balls B_i compactly contained in neighborhoods carrying C² local primitives H_i. On each B_i, the scalar converse gives

    A−H_i=∇φ_i,  φ_i∈C²(B_i).

Take a smooth partition of unity χ_i subordinate to the balls, with supports contained in them. Products are extended by zero. The locally finite scalar sum Φ=Σ_i χ_iφ_i is C² and

    G=A−∇Φ
      =Σ_i χ_iH_i−Σ_i φ_i∇χ_i.

The expanded expression is C², while the first expression and curl∇Φ=0 give curl G=F. This is exactly the previous informal gluing mechanism, reused here to complete the new quantitative equivalence. The C² domain equivalence enters only through the already-proved global C¹ primitive.

## 4. Why allowing smooth potentials does not alter m(H)

Fix H∈S and a C² potential A defined near B̄_{1/2}. Choose a slightly larger ball B_r on which both A and H are defined and curl A=H. On a still smaller intermediate ball, mollify A with scale δ. Then A_δ is smooth, curl A_δ=H_δ, and A_δ→A in C² on B̄_{1/2}. Since H is smooth, E_δ=H−H_δ tends to zero in C² on that closed ball and a neighborhood of it; it is divergence-free.

Let R be the fixed radial homotopy for closed two-forms on a ball, translated into vector fields. In standard orientation one can use

    (R E)(x)=∫₀¹ t (E(tx)×x) dt.

For smooth divergence-free E, curl R E=E. Direct product differentiation gives

    ||R E||_{2,1/2} ≤ K ||E||_{2,1/2}

for a finite constant K depending only on the fixed radius and norm convention. This is a same-regularity estimate, requiring C² input, and is unrelated to the open endpoint estimate. Therefore

    Ã_δ=A_δ+R E_δ

is a smooth exact potential of H near B̄_{1/2}, and ||Ã_δ−A||_{2,1/2}→0. Taking infima proves that the smooth and C² versions of m agree. In particular, restricting attention to smooth representatives for smooth data costs no strength in (Q); restricting to one fixed gauge or a finite-dimensional ansatz does cost strength.

## 5. A gauge-independent certificate for lower bounds

For any ψ∈C∞_c(B_{1/2};R³), define

    d(ψ)=sup { |∫ A·curl ψ| :
      A is C² near B̄_{1/2}, ||A||_{2,1/2}≤1 }.

Compact support removes all boundary terms, and curl is formally self-adjoint in the Euclidean integral pairing. Thus every potential A of H satisfies

    ∫H·ψ=∫A·curl ψ,
    |∫H·ψ|≤||A||_{2,1/2} d(ψ).

Consequently

    m(H) ≥ |∫H·ψ| / d(ψ)               when d(ψ)>0.

A computable sufficient upper bound on d(ψ) is available without optimizing over A. If compactly supported smooth functions Φ_{i,α} satisfy

    (curl ψ)_i = Σ_{|α|≤2} (-1)^|α| ∂^α Φ_{i,α},

then integration by parts gives

    d(ψ) ≤ Σ_{i,α} ||Φ_{i,α}||_{L¹}.

Therefore exact triples (H,ψ,Φ) with H divergence-free, ||H||_{1,1}≤1, and

    |∫H·ψ| / Σ||Φ_{i,α}||₁ →∞

would disprove the printed endpoint. This is a sufficient certificate family, not a claim that every possible blow-up is captured by the displayed smooth Φ representation. No such sequence has been found in this lane.

The useful distinction for computation is precise: minimizing a C² norm over a restricted Fourier/polynomial family computes an infimum **at least as large** as m(H). Growth of that restricted infimum supplies no lower bound on m(H). A certified dual inequality of the form above, by contrast, holds for every potential and defeats all gauges at once. Ordinary numerical residuals or an unsuccessful restricted optimizer are not these certificates.

### A concrete planar adjoint template

There is a particularly explicit planar version. Write D_r for the disk of radius r in R². If div u=h on D_{1/2}, u∈C², and ψ∈C∞_c(D_{1/2}), repeated integration by parts gives

    ∫ h ψ_xxyy
      =−∫ u₁ ψ_xxxyy−∫ u₂ ψ_xxyyy
      =−∫ (u₁)_yy ψ_xxx−∫ (u₂)_xx ψ_yyy.

Thus, for **every** divergence primitive u,

    |∫ h ψ_xxyy|
      ≤ ||D²u||_∞ (||ψ_xxx||₁+||ψ_yyy||₁).

The same cutoff geometry as above makes a local planar C¹-to-C² bound necessary if the full contract holds: apply the full three-dimensional estimate to H=(0,0,h(x,y)), then restrict A to z=0 and take u=(A₂,−A₁). If h is smooth near D̄₁, this H is smooth near B̄₁, its C¹ norm is the corresponding planar norm, and ||D²u||∞ on D_{1/2} is bounded by the C² norm of A on B̄_{1/2}.

It follows that the full contract implies the precise inequality

    N(ψ) ≤ C (||ψ_xxx||₁+||ψ_yyy||₁),

where

    N(ψ)=sup { |∫h ψ_xxyy| :
       h smooth near D̄₁, ||h||_{C¹(D̄₁)}≤1 }.

In particular, smooth pairs (h_j,ψ_j), normalized by ||h_j||C¹≤1, whose displayed ratio diverges would give an all-gauge disproof certificate. This higher-order adjoint template is a new calculation in this lane.

The unresolved numerator is a C¹ dual norm, **not** an unrestricted L¹ norm of a mixed derivative. One integration by parts only gives upper bounds such as N(ψ)≤||ψ_xyy||₁ and N(ψ)≤||ψ_xxy||₁. Replacing N by one of those larger quantities would invalidate a purported lower-bound argument. Choosing an arbitrary sign for one derivative of h is also invalid: h must have a jointly bounded continuous gradient, whose two components are compatible. Ornstein non-inequalities for unrestricted mixed-derivative L¹ norms therefore do not by themselves decide this displayed estimate. No failure of this estimate is claimed.

## 6. Fidelity recheck

The local source `/home/derekblair/projects/math/references/sources/pma3.pdf` was rendered and visually checked at PDF pages 289 and 290 (printed pp.280–281). The images are `pma-page-280.png` and `pma-page-281.png` in `/home/derekblair/lane-work/codex-rudin-1043/`. Text extraction of PDF pages 289–291 is retained there as `pma-fidelity-pages.txt`; its OCR confuses prime counts, so the regularity check relied on the rendered page.

Printed p.281 states C′ for the converse input F and C″ for the output G in (b′). Printed p.280 defines the equivalence using a one-to-one C″ map onto an open set and a C″ inverse. These agree with the unchanged `VectorPotentials.lean` contract and the `C2DomainEquivalence` structure. The formal contract's global ambient functions impose regularity and inverse identities only on their specified open domains. There is no newly discovered statement mismatch.

## 7. New kernel-checked compatibility criterion

Write a C¹ planar matrix by rows `a=(a₀,a₁)`, `b=(b₀,b₁)`, and columns `V₀=(a₀,b₀)`, `V₁=(a₁,b₁)`. The new module proves that a whole-plane scalar h has a C² divergence primitive if and only if there are such rows with

    a₀+b₁=h,
    ∂₁a₀=∂₀a₁,   ∂₁b₀=∂₀b₁.

This is `c2_planarDivergence_iff_compatibleTrace`. Forward, take the rows of Du; backward, integrate each closed C¹ row using the **already proved scalar converse**, obtaining C² components of u. The proof uses the repository's Chapter 10 machinery via horizontal embedding and restriction, with no unresolved endpoint assumption.

For C¹ h, `c2_planarDivergence_iff_compatibleColumns` gives the equivalent condition

    div Vⱼ=∂ⱼh  (j=0,1),
    ∂₁V₀=∂₀V₁.

The proof explicitly handles the constant missing from the differentiated equations: row closure identifies each derivative of the trace with the corresponding column divergence; trace−h is therefore constant. Subtracting this constant from one diagonal entry preserves closure and fixes the trace. No basepoint or boundary normalization is smuggled into the statement.

The existing coordinate-field construction supplies separate solutions `Vⱼ=h eⱼ`. The new `canonical_columns_compatible_iff_constant` proves that **these particular choices** are compatible exactly when h is constant. Other choices remain unrestricted. Thus the next positive proof must choose the columns simultaneously; separate existence cannot finish it. The trace criterion also transfers to all C² potentials of the vertical field by `c2_verticalPotential_iff_compatibleTrace`.

The earlier report already discussed compatibility informally. The new contribution here is its exact kernel-checked equivalence, the explicit constant correction, and the precise failure condition for the canonical choices. This does not create a full-contract↔planar equivalence.

## 8. Computational counterexample probe

The [annular supplement](pma10-43-annular-probe.md) supplies the explicit functions, derivative bounds, frequency isolation, and a mixed radial/angular packet extension. Its [standard-library script](pma10-43-annular-probe.py) produces the retained [results](../evidence/t14-quantitative/annular-frequency-results.json). It examines a candidate class left outside the earlier fixed-profile estimates: angular frequency increases without bound on shrinking annuli.

For the concrete example, `r_n=4^(-n)`, `m_n=2^n`, `a_n=1/(n m_n)`, with the compact C² cutoff χ(s)=64(s−1)³(2−s)³ on [1,2], the datum is

    h(r,θ)=Σ_n a_n r_n χ(r/r_n) cos(m_n θ).

It is C¹, and its derivative is not Hölder of any positive exponent at zero. Nevertheless the explicit tangential primitive

    u=Σ_n e_θ (a_n r_n r/m_n) χ(r/r_n) sin(m_n θ)

is C² and satisfies div u=h. Its Hessian tends to zero at the origin; the canonical radial primitive instead has unbounded Hessian. This is a positive construction for the candidate datum, not a counterexample to the printed clause. All regularity and asymptotic assertions in this paragraph are **informal proofs**, not Lean results.

The probe cross-checks exact rational constants and finite-difference identities. Sampled maxima are labelled as samples, never as certified suprema. Neither a finite numerical optimizer nor a finite family of witnesses is treated as a search over every gauge. The missing estimate concerns arbitrary data, where cancellations between many packets can make the actual C¹ norm much smaller than the sum of the separate packet bounds.

## 9. Verification, preservation, and review status

Author-lane validation on Lean `v4.34.1`, after the required `lake exe cache get` (8907 cached files):

| Command | Result and retained evidence |
| --- | --- |
| `lake build` in `rudin/` | Exit 0, 9208 jobs; [full production log](../evidence/t14-quantitative/lake-build.log) |
| `lake build Rudin.Research.PMA1043Compatibility` | Exit 0, 9069 jobs including replayed dependencies; [explicit target log](../evidence/t14-quantitative/compatibility-build.log) |
| `lake env lean ../research/pma10-43-compatibility-axioms.lean` | Exit 0; [audit log](../evidence/t14-quantitative/compatibility-axioms.log) |
| `PYTHONDONTWRITEBYTECODE=1 python3 scripts/verify_ch10_integration.py` | Exit 0; [verifier log](../evidence/t14-quantitative/integration-verifier.log) |
| `python3 research/pma10-43-annular-probe.py` | Exit 0; retained JSON matches the initial run byte-for-byte |

The [audit source](pma10-43-compatibility-axioms.lean) checks every declaration owned by the new module, including generated declarations: **24 total**. It also prints transitive axioms for all **21 explicit declarations** (7 definitions, 14 lemmas/theorems). Every dependency is among `propext`, `Classical.choice`, `Quot.sound`; no placeholders or custom axioms occur.

**Import scope:** the new research module is standalone and is not in the default `Rudin` import closure. The production build does not validate it; the explicit target and ownership-based audit above do. Both must be rerun when this module changes. Existing production sources, contract, Chapter 10 audits, integration manifest, pins, and prior research records are unchanged. The verifier retains all 51 contracts, 50 principals, and the explicit absence of `pma10_43`.

These checks are author-lane validation, not the programme's gating crossed review. A coordinator-appointed crossed review remains required before landing. No such review was arranged by this lane; nothing is merged and no issue closure is requested.

## What this does NOT show

- It does not establish (Q), nor does it exhibit a sequence violating (Q).
- It does not prove or disprove the C¹-to-C² endpoint.
- It does not upgrade the prior planar implication to a full-contract equivalence.
- The new quantitative equivalence and the dual certificate are ordinary mathematical arguments, not kernel-checked declarations.
- It does not claim the endpoint is unresolved everywhere in the published literature. Only the programme record and the specific functional-analytic source above were used for this addition.

- The annular constructions and quantitative equivalence are not promoted to kernel proofs by the successful compatibility-module audit.
- A successful obstruction-report deliverable does not settle node 10.43 or satisfy the acceptance gate for an unconditional proof/counterexample.
