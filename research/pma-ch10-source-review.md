# Chapter 10 independent source and fidelity review

Reviewer: `/root/ch8_fidelity`. Role for this chapter is independent source inventory and semantic review, with no production-proof authorship, Lean/lake invocations, or git mutations. Compilation reports below belong to the root's serialized build process and are not claimed as reviewer-run checks.

## Source and scope

The authorized existing third-edition source is `/home/derekblair/projects/math/references/sources/pma3.pdf`. The PDF skill was read and applied. Printed pp.245-288, corresponding to PDF pp.254-297, were rendered and visually inspected in memory; no source pages, extracted proof text, or copied proof prose were written to disk. The complete inventory is `research/pma-ch10-inventory.md`. It has 51 consecutive numbered items and includes attached assertions; exercises starting on printed p.288 are outside scope. The source's compact-domain regularity convention occurs on p.253.

## Semantic requirements carried into review

- Printed pp.245-248: use actual successive Chapter 6 Riemann integrals and explicit existence at each stage. A measure-integral bridge may be proved but cannot replace the native object. The simplex zero extension is generally discontinuous on the boundary, so its integrability needs a separate argument. Compact supports use closure of the nonzero set. Complex integrals can be explicitly reduced to real and imaginary parts.
- Printed pp.248-250: primitive-map differentiation requires differentiability only at the specified point. The factorization has exactly n primitive factors and n-1 flips or identities, with the written rightmost-first composition order. Positive dimension is the natural convention for selecting a primitive coordinate.
- Printed pp.251-253: partition support is closed support, not just pointwise nonvanishing. The change-of-variables integrand must be zero outside the map's open domain, and the Jacobian factor is absolute value. No global restriction on an arbitrary ambient extension of the map can be silently added.
- Printed pp.253-265: surface regularity means extension to an open neighborhood of the compact cell or simplex. Surfaces and pullback maps need not be injective or immersive. Form equality is equality of all surface integrals. An alternating-field representation needs coefficient and integral bridges, including actual separation by integrals in 10.15.
- Printed pp.266-275: orientation is equivalence for integration, not equality of maps. Degenerate simplices are allowed. Boundaries use alternating omitted-vertex faces. C2 chains are genuine pushforwards of affine simplices, not a predicate assuming Stokes. Positive-boundary independence in 10.31 concerns all continuous forms of boundary degree.
- Printed pp.275-280: exact C1 forms are closed under the ordinary exactness convention; requiring a C2 primitive would strengthen the definition. The convex primitive lemma 10.38 applies to arbitrary convex open domains, and 10.39 is the full global Poincare conclusion in every positive degree. The transport theorem requires a C2 map and C2 inverse. The cell-triangulation assertion in 10.41 remains part of the inventory.
- Printed pp.281-288: preserve vector-field/form identifications, volume and area integral interpretations, the full torus example, and normal/tangent conventions at degenerate parameter points. Classical Stokes and divergence must follow as identities of these integrals, not as definitions of their two sides.

## Initial accepted contracts

The following definitions and contracts were read independently against the corresponding source pages on 2026-10-23. All are semantically accepted. The hashes identify this review snapshot; a later production hash requires reconciliation even if the contract is unchanged. Contract hashes cover the `def pma10_n_contract : Prop := ...` text through its final term, with surrounding whitespace normalized to one trailing newline, and exclude the next declaration/comment.

| Module | Nodes | Snapshot SHA256 | Status |
| --- | --- | --- | --- |
| `rudin/Rudin/PMA/Chapter10/Integration.lean` | 10.1-10.4 | `db0054a17a9a065740596654ecb5b35b960b42dc6a4d5e3cfb8d2984230acdef` | Definitions/contracts accepted; numbered proofs not yet reviewed. |
| `rudin/Rudin/PMA/Chapter10/Primitive.lean` | 10.5-10.7 | `bdfbb5a982a94bbb09de1a23f717ee7160075813052864aeeaea7af8811987a2` | Definitions/contracts accepted; 10.5/6 proof implementations reviewed; full 10.7 proof review pending final compilation fixes. |
| `rudin/Rudin/PMA/Chapter10/Partition.lean` | 10.8 | `5d4a4e66629b73912921920fc23af3118763843dfbdf8f15d3dba06ae266a1b5` | Contract and complete proof accepted; root reports successful compilation. |

| Contract | SHA256 |
| --- | --- |
| `pma10_1_contract` | `0e7b3bf417ec493591f40c4d2fab5203b1cbdaca8414ef4c50de12a7cd7255a8` |
| `pma10_2_contract` | `0f68501ae1d3f7a7b2419951ee7920d091c43cc44ad1df09876cf00afc77e4e4` |
| `pma10_3_contract` | `68272ba642ece110eb2105562e42e66eede4ae63cb2cbbf33b68d9dbb33312b1` |
| `pma10_4_contract` | `0a1fa2e5371125ed1eadf3bf6198ca72170f10826d84d297f1ffc65aa590204a` |
| `pma10_5_contract` | `d62af8a417c7eff5dda46e640559f6eb647ff82bc52b9d74b4d96874f7c0c249` |
| `pma10_6_contract` | `23e206886222abb0aa5f16147f19a783ae4604dd3a51d5165977bacb9104dbf7` |
| `pma10_7_contract` | `7cea87365f33e76f6789c15c30108c3ec2606f3f8506fca3ae2489993aeb0954` |
| `pma10_8_contract` | `b44bdfd047fd1951676108ba2015ca8df80df812d39f47221de76d1b23ca9497` |

Integration acceptance includes zero dimension as a harmless extension; intermediate continuity; every integration order; real and complex containing-cell independence; and simplex zero-extension existence. The appended measure bridges are genuine supplementary equalities. Primitive acceptance includes arbitrary-point differentiation, the exact range/kernel projection assertions, and every factor's local C1, zero-fixing, and derivative-invertibility properties. Partition acceptance includes a finite subset of an arbitrary indexed open cover, globally bounded continuous functions with actual support inclusion, and decomposition of every continuous function supported in the compact set. Its proof uses compact finite subcover, the pinned partition-of-unity theorem, the sum identity on the compact set, and vanishing outside support; it does not add assumptions to the source assertion.

## Primitive final proof review and independent clients

The complete compiled `Primitive.lean` snapshot is independently accepted at SHA256 `200eb8e36d54cdf771415de92c1046cf4c92d64c123d0fed62a4ee7e64639f5b`. The three contract hashes remain those in the table above. The explicit operator type annotation in the factor-list mapping does not change the proposition. The proof derives the next nonzero pivot from injectivity of the actual derivative, constructs a primitive scalar-coordinate update, invokes the genuine local inverse theorem, and uses a flip to preserve the previously fixed coordinates. The induction retains exactly n primitive factors and n-1 flip-or-identity factors and restricts the resulting eventual equality to an open neighborhood inside E. The derivative, determinant, flip, and prefix range/kernel helper proofs were also read. Root reports the complete module compiled successfully; the reviewer ran no build.

`PartitionProbes.lean`, independently authored by this reviewer, has two public clients: an empty compact set covered by an actually empty index type, and strict positivity at each covered point together with forced vanishing outside the assigned cover member. Its SHA256 is `6f13bcde04f0f7f76182222195f28636a6913f179802bcce37fddc3e4293e401`; `evidence/ch10-partition-probes-compile.log` records successful compilation. `PrimitiveProbes.lean` adds dimension-one elimination of all flips, a plane flip with zero diagonal/nonzero off-diagonal pivot, and that map's full two-primitive factorization. These three clients await root compilation.

The shared representations in `FormsCore.lean` and `Surfaces.lean` were reviewed as architectural definitions, not as completed numbered nodes. Homogeneous exterior-algebra fields, scalar-coordinate regularity, evaluation by actual derivative minors, native parameter-domain integrals, and a separate equality-of-integrals relation are suitable. Numbered contracts still need explicit integrability, coefficient-expansion bridges, curve identification, and the nontrivial separation theorem.

Further nodes and final proof/hash reconciliation remain pending; this document does not claim Chapter 10 completion.

## Change-of-variables contract acceptance

The exact `pma10_9_contract` in `ChangeOfVariables.lean` is accepted before proof completion. File snapshot SHA256: `8aab5844f5da525713bb16d759f8373a057f6c0de8ad4387ac3055a4c4ed9544`; contract SHA256: `9bea02f2a1e23a6a170996c536d27c3a4fc753e737e09b5adcf76f031dd7828f`. Its standard coordinate matrix and Euclidean conjugation identities bridge the determinant convention to Chapter 9. The C1, injectivity, and nonzero-Jacobian assumptions are restricted to the open domain E. The conclusion provides an actual partial homeomorphism with source E and target its image, inverse continuity, and openness of the image. The transformed function is explicitly an E-indicator; its global continuity, compact support, support containment in E, native iterated-integrability witness, and native whole-integral equality are all conclusions. The original function also has a native iterated-integrability witness. No measure-only substitute or unrestricted global-map premise is used.

The complete initial 10.9 proof draft was also read, at snapshot `1420cfdc2dd0ff73c8d36dbd28e97052eea927911b99f2225db3760c88d419ae`. Its local inverse construction yields a genuinely open restriction, its inverse transports the compact support into a compact subset of E, and the explicit indicator then gives global continuity and the correct domain-restricted integral. The pinned measure-theoretic Jacobian theorem is connected by proved native integral equalities. This is semantic acceptance of the draft, not a compiler-pass claim.

## Native integral proof review and surface-definition contract

The complete `IntegrationProofs.lean` and `IntegrationMeasure.lean` proof drafts were read. The first derives native continuity/existence from the Chapter 6 integrability theorem and Chapter 9 uniform-limit lemma. Its one-dimensional measure bridge extends a continuous interval function and proves native congruence before using the existing interval-integral bridge. The second identifies cell volume with the product of restricted one-dimensional measures, proves the last-coordinate splitting formula, and inducts to the native integral equality; the dimension-zero product measure is explicitly a Dirac mass, not zero. Coordinate permutation, containing-cell independence, and real/imaginary component support and integral bridges follow. No missing existence assertion is replaced by an equality between totalized values. Initial semantic-review snapshots are `7ceed05ff97db102454e4d52ef1ad58a60d52ec3225c0e6e71d0f63df7b428b9` and `351ef57edae3336f5e77339d743da9b461439d62f2db81b3952c6ace904d862a`; compiler fixes and final hashes are pending.

`pma10_10_contract` is accepted at contract SHA256 `941e2ee4570cdf10e00ff694736d153e86d1082ccaea833e2e379b37123f7155`. It includes compact cell/simplex parameter domains, actual open-neighborhood C1 extensions, the unrestricted converse surface construction, and both directions of the one-dimensional regular-curve correspondence with parametrization round trips. The datatype and contract admit noninjective and degenerate maps. The source requirement that E be open appears explicitly in the numbered contract.

After pointwise EqOn elaboration fixes, all three independent `PrimitiveProbes.lean` clients compiled successfully in `evidence/ch10-primitive-probes-compile.log`, at SHA256 `5ff9f013feba37663b8f872b816ec64ee78273fcd6dad954071a4852bb42282d`. Four independently authored `IntegrationProbes.lean` clients await compilation: a collapsed first side of a two-dimensional cell with native integrability; dimension-zero native/measure evaluation; exchanged unequal intervals with a nonsymmetric integrand; and purely imaginary compact support and integral preservation.

## Worked form examples contract

`pma10_12_contract` is accepted before numbered proofs, at contract SHA256 `de31cca4ffdc0cd330e0c012ffb11fe8fea37afd34fac5227c314104212b1986`, file `FormExamples.lean` snapshot `76c2ff808ae8a1cc36a88ba461801d5efa5d351ca381d5ebc3ada17bef2117e7`. The first assertion is universal over genuine C1 curves in three-space with the source unit parameter interval. The ellipse assertions provide actual surfaces with the stated parametrizations, closedness, both native integrability witnesses, and the two opposite signed values. The spherical assertion provides an actual surface, the global derivative-determinant formula, native integrability and integral, full closed-unit-ball image, and interior injectivity. Surface existence does not assume the desired regularity or integral evaluations as premises. The source's geometric area/volume interpretation is to be tied explicitly to the native volume-element and Green identities in 10.44/10.45; a Haar-volume equality is not imposed as an additional substitute for the native example.

The completed `SurfaceDomains.lean` principal proof was also read at snapshot `7b7c83140d5a890564a7699d60454ea79ba91cccfe85cf87b0148114f7bdd77d`. It uses the proved compact-domain facts and actual construction/conversion definitions; the curve round trip uses uniqueness of the coordinate in `Fin 1`. Semantic acceptance is unchanged; root compilation is the remaining gate.

## Green integration reconciliation and 10.11 acceptance

Root subsequently reported successful compilation of `IntegrationMeasure.lean` and `SurfaceDomains.lean`. Exact final independent acceptance for 10.1-10.3 is: `Integration.lean` = `db0054a17a9a065740596654ecb5b35b960b42dc6a4d5e3cfb8d2984230acdef`; `IntegrationProofs.lean` = `7ceed05ff97db102454e4d52ef1ad58a60d52ec3225c0e6e71d0f63df7b428b9`; `IntegrationMeasure.lean` = `0123ef35e549e6bd0fc1dbfd9823d5650b5b9008114e285660de4d95568b4a7c`. The final changes make restricted measures explicitly SFinite, state the permutation coercion equality explicitly, and use the pinned complex-component continuity API. No accepted definition or numbered contract changed. The complete 10.10 acceptance hash remains `7b7c83140d5a890564a7699d60454ea79ba91cccfe85cf87b0148114f7bdd77d`.

The exact `pma10_11_contract` is accepted before its principal proof, at SHA256 `2005e8f51e71594407dff80e158795a46d9c8d1345ee1c361d031a21b8d7c710`; the `FormDefinitions.lean` snapshot is `a1621047e1a092858a71c8a9cb514f41aaa2ac081ab40f3a6f4f27ee0c98eb69`. It includes continuity and actual native integrability of every regular surface integrand; the full all-ordered-tuple coefficient/minor formula; the coefficient C-r regularity bridge; and the scalar zero-form existence, uniqueness on E, and point-evaluation correspondence. The later 10.14 still owes every homogeneous form's standard expansion, and 10.15 still owes separation by actual integrals; neither is claimed by this definition contract. `FormRegularity.lean` and `ScalarForms.lean` helper implementations were read and preserve these meanings.

The full initial `SimplexSlices.lean` and `Simplex.lean` proof drafts were read. Endpoint-value invariance is derived from the native indefinite integral and the mean-value theorem. Stopped slices are natively integrable at both extreme cutoffs as well as in the interior. Every simplex fiber, including collapsed fibers, has an explicit continuous variable-endpoint integral formula before the measure bridge is invoked. Permutation invariance follows using the actual simplex indicator and native existence. These drafts are semantically accepted pending root's compiler fixes and final hashes; no almost-everywhere-only existence claim or boundary-continuity premise replaces the source.

All four independent `IntegrationProbes.lean` clients subsequently compiled in `evidence/ch10-integration-probes-compile.log`; frozen SHA256 `a22d31edbeb4179ff4ed555c411834fa2027f6119cff4c50a44c072695fd37d3`.

## Elementary form operations contract

`pma10_13_contract` is accepted at SHA256 `e2b0cdbce34fe5cb12b5dc28b703d8b5b4c3f61763b8affa33476399eb18fd38`, from `FormOperations.lean` snapshot `81b58da953a86439666628d34888c1121cddbd8026515f501e69b3c277d332b8`. Its equality relation quantifies actual surface integrals; its zero relation uses the zero integral; and its scalar-plus-addition identity gives the source linearity and negation laws. Arbitrary transpositions negate coefficient wedges, repeated indices vanish, and degree above the ambient dimension implies both pointwise and functional zero. The swap/repetition clauses need no continuity assumption because the algebra-valued expressions are identical pointwise, a valid strengthening. Helper proofs were read: compact integrability and the proved native/measure bridge justify linearity; equality on E transfers by the surface mapsTo field; the over-dimension assertion uses an empty exterior-power basis. Principal compilation remains pending.

At root's request, the reviewer independently authored three `FormProbes.lean` clients and two `ChangeOfVariablesProbes.lean` clients. The form clients check a nonzero scalar integral at a zero-dimensional point, a genuinely noninjective constant curve with native existence and zero integral for arbitrary continuous coefficient one-forms, and a separated repeated wedge index. The change-of-variables clients compute the reflection Jacobian as minus one and apply the full native theorem on the proper positive ray to functions supported on the negative ray, retaining zero extension outside the domain. Both probe modules await root compilation and are not counted as compiled yet.

The complete initial `FormExamples.lean` and `SphereExamples.lean` proof drafts were read. They prove actual curve-coordinate derivatives and the product endpoint formula, evaluate the distinct sine-squared and cosine-squared ellipse densities, compute the spherical derivative determinant and native nested density integral, construct polar coordinates for every point of the closed unit ball, and recover the parameters only in the parameter interior. Boundary identifications are not suppressed. Their proof structures are semantically accepted pending compiler corrections and final hashes.

## Integral separation contract

`pma10_15_contract` is accepted before proof at SHA256 `b1c8396bfb50a1fcbcd6c503ca8fddaa323e65fc375d3cf15b3c3a86ff3dbc11`; initial `FormSeparation.lean` snapshot `f3c97f3a9867799b558041a29abd2d0b93762e6bc2f86370f21561f01169353f`. It quantifies an arbitrary open set and a genuine homogeneous continuous form. Vanishing of every actual native surface integral is equivalent both to vanishing of every standard increasing coefficient at every point and to pointwise zero of the form on E. There is no inserted nonempty-set or coefficient-vanishing premise. The current `StandardForms.standard_expansion` helper was also read: it obtains the finite standard expansion from the actual exterior-power basis and identifies its coordinates with the ambient exterior-algebra basis, rather than assuming the desired coefficient representation.


## Final native integration section and boundary clients

The final compiled simplex proof files are independently accepted in their entirety: `SimplexSlices.lean` SHA256 `e303ac72a9e0e49bb5ee2dd16216924b14166937e5f319303a0ef485c201e603`, and `Simplex.lean` SHA256 `a8d47dcf24e72f261138297ae8cb89479f5b189d091163dd0f843c881701a928`. Compiler corrections preserve the accepted native definitions and all four numbered contracts. Together with the three previously accepted integration files, these exact five files are recorded in `evidence/ch10-reviewed-production-manifest.json`; the exact four accepted contract texts and their hashes are recorded in `evidence/ch10-accepted-contract-snapshot.json`. Root reports successful compilation; no reviewer build was run.

`SimplexProbes.lean` supplies two independently authored boundary clients: the zero extension of a nonzero constant has an actual boundary jump while all native iterated integrals exist, and the collapsed boundary fiber has a nonzero endpoint value but an existing native integral equal to zero. They await root compilation. The determinant simplification in the independently authored constant-curve client was repaired without changing its proposition; its recompile is also pending.

## Standard form and integral-separation review

The exact 10.14 contract in `StandardForms.lean` is independently accepted. It includes the binomial count, the source integer tuple-sign convention, arbitrary injective-tuple sorting with the range preserved, repeated-index zero, continuous and C-r coefficient expansions, both displayed reordering examples, and the actual displayed two-form simplification. The accepted contract hash is `26d646b002f9160b771996fd9353321b20aa299d5db631b06007e3eba1b26680`. Proof completion and final file hash reconciliation remain separate gates.

The full initial `NativeSeparation.lean` and `FormSeparation.lean` proof implementations were independently read. A nonzero continuous coefficient yields a genuinely positive-sided native integration cell with a nonzero integral. An actual coordinate-axis surface maps that cell into E; its derivative and determinant-basis evaluation isolate the chosen coefficient. Functional vanishing therefore contradicts the native nonzero integral. Degree zero and degrees exceeding the ambient dimension are retained. Pairwise uniqueness is subsequently obtained using genuine form differences and native integral linearity. This establishes the intended semantic argument rather than defining functional equality to be pointwise equality. Compiler corrections and final hashes remain pending.

## Wedge products and exterior differentiation contracts

Exact 10.16-10.20 contracts are independently accepted before numbered proofs. In 10.16 the inversion count is the number of pairs with the second index smaller than the first; concatenation, overlap zero, sorted disjoint union, and associativity match the source. In 10.17 the product retains degree and coefficient continuity, has the full standard double expansion, and obeys both distributive laws, associativity, scalar multiplication on either side, and graded commutation. Zero degrees are included.

In 10.18 exterior differentiation uses the fixed coordinate basis, differentiates coefficients, and wedges their differentials on the left. It maps C1 forms to continuous forms of degree one higher, and includes both the scalar formula and its actual Frechet derivative evaluation. In 10.19 every genuine C1 curve has an explicitly integrable differential, endpoint evaluation, path independence, and closed-curve zero; `x dy` has no global C1 scalar primitive. The arbitrary parameter interval is a valid strengthening of the source unit interval. In 10.20 the graded Leibniz sign is tied to the first form's degree, and C2 regularity yields a C1 derivative and a zero second exterior derivative. No extra injectivity or nondegeneracy premise appears.

| Accepted contract | SHA256 |
| --- | --- |
| `pma10_16_contract` | `8696106f0066e6871b316fc6fcf3aaab63ee922b53d3f6cd18f0e29b1fb84dd9` |
| `pma10_17_contract` | `cd226f2d5a18f450050737f5b11dd3f5ff677ceeb75f3d9a23c9583724aee7ae` |
| `pma10_18_contract` | `03489f7559f5fe039c12a33fb7e907ec319ece63c8e917abd72d44b296072df5` |
| `pma10_19_contract` | `0fc995dbcea5c0e199e09da19ac24fc824424e1893b3383d5f6decee4d959a7d` |
| `pma10_20_contract` | `4ec387cad5c63605e18685a95fc2f3dbc2a98090329797a0a91938680d72705d` |


## Compiled surface and elementary-form reconciliation

The final complete proofs of 10.11 and 10.13 and all their local representation/regularity helpers were re-read independently. The native parameter-domain existence lemma covers both cells and simplex extensions; the zero-dimensional integral is actual evaluation. The 10.13 linearity argument proves measure-integral equalities from the native objects and invokes compact integrability, while antisymmetry and repetition are identities of the actual coefficient wedge expressions. The degree-above-dimension result uses the empty graded basis. Accepted contracts are unchanged. The final root `ch10-form-probes-compile.log` builds successfully with these dependencies, and `ch10-form-operations-compile.log` separately reports successful compilation.

| Accepted complete file | SHA256 |
| --- | --- |
| `rudin/Rudin/PMA/Chapter10/FormsCore.lean` | `9f718c1dc6ef5855805f01176a8aabffca9768f7c952e063f7f1ea31533382b1` |
| `rudin/Rudin/PMA/Chapter10/FormsAlgebra.lean` | `008151a4403139501ad36c4ea9333808fa2b456ebabadc616eb3faa67de92ce1` |
| `rudin/Rudin/PMA/Chapter10/Surfaces.lean` | `b4ca23167dfe07853dada56aa449e3de061fb6008387b51efa6d274bd6edc338` |
| `rudin/Rudin/PMA/Chapter10/SurfaceDomains.lean` | `7b7c83140d5a890564a7699d60454ea79ba91cccfe85cf87b0148114f7bdd77d` |
| `rudin/Rudin/PMA/Chapter10/FormRegularity.lean` | `4d914c2ed63a5c4faee84e4eda50377af3095cf01ad003c666ec7a5cbc228924` |
| `rudin/Rudin/PMA/Chapter10/ScalarForms.lean` | `30f681a8408eae0cc36c59ef07705d30fb11c6b6b272d06dd01e4ce9772bfb39` |
| `rudin/Rudin/PMA/Chapter10/FormDefinitions.lean` | `42a8630d7c0a0d3e90dce85f26832d7f7c2a5e4fb68653988505febe6e91314b` |
| `rudin/Rudin/PMA/Chapter10/FormOperations.lean` | `55939cdfe36cf842c638467e4bc082384a0c1a7cffc3ce06a05340f981fd9bae` |

All three independently authored `FormProbes.lean` clients now compile successfully. Frozen SHA256: `b11a1b9feeb7bd41456b7810616f20b9674e55ee41b6c70393c380a514c4c478`. The reflection probes remain blocked only by their production-module dependency at this checkpoint; they are not yet counted as compiled.


## Section gate through 10.7

Following root's report of the local 10.1-10.4 commit and successful section audit/default build, the canonical accepted-contract snapshot and reviewed-production manifest were extended through 10.7 only. All existing five module hashes were rechecked against disk, as were the exact accepted Primitive file and three contract hashes. The manifest now contains six production modules and seven numbered principals. The two independently authored simplex boundary clients compiled successfully in the opening section audit. The 10.8 canonical extension is intentionally deferred until root reports the 10.7 section commit.


The complete initial `WedgeProducts.lean` proof draft is semantically accepted at SHA256 `43456b72bca883e091592558b52a3b48d521bf46e81926d4e9ba3257f74f5628`. Its sign argument splits the literal tuple-sign product into within-block factors and cross-block factors, then counts exactly the negative cross differences. It identifies the sorted disjoint union by its actual range. Product coefficient continuity and the standard double expansion are proved from finite sums, and homogeneous expansions justify the graded exchange law. Compiler corrections and final hash reconciliation remain pending.


## Section gate through 10.8

After root reported local commit `20bf93b33aa9666a69d26c4053498c3b9fb32729` for 10.5-10.7 and successful source/audit/default gates, the canonical review records were extended through 10.8 only. The Partition file and contract hashes match the earlier independent accepted snapshots exactly; all previously recorded production hashes were also rechecked. The canonical manifest now contains seven modules and eight numbered principals.


## Pullback architecture and source requirements

Printed pp.262-266 were re-rendered in memory to confirm the 10.21-10.25 requirements. `PullbackAlgebra.lean` was independently read at SHA256 `f757098596f2d9d52cfba047a7d867c35d138a6ba5c4fde4f757f9f4b2346294`. Its actual derivative induces a covector pullback and then the exterior-algebra map; the pairing, contravariant composition, scalar, sum, wedge, and coordinate-product identities preserve the source meaning. This is architectural acceptance, not acceptance of yet-unwritten numbered contracts.

The numbered statements must keep C1 map regularity restricted to the open source set and a maps-into-target premise, with no injectivity or rank premise. The 10.21 coefficient formula must connect the algebra map to the standard composed-coefficient/product-of-coordinate-differentials expression and prove continuous homogeneous regularity. The 10.22 commutation with d requires C1 forms and a C2 map. The 10.23 composite uses three open domains and contravariant order. The 10.24 identity parametrization has the exact same cell or simplex domain as the original surface, with explicit Coord/Euclidean conversion and native integral existence. The 10.25 composed surface must be constructed using an open-neighborhood restriction/preimage; no premise may require the arbitrarily chosen ambient extension to map globally into the target. Its integral equality and both native integrability assertions must cover noninjective and degenerate maps, including dimension zero.


## Exterior derivative proof-draft review

All four initial exterior-derivative proof files were independently read and semantically accepted. Coordinate differentiation is connected to actual Frechet derivatives, with open-set locality and C2 mixed symmetry proved at each point. The derivative of a form is expanded in the fixed finite basis; wrong-degree coefficients vanish locally, preserving homogeneity. Coefficient regularity is reduced by exactly one order. The curve theorem first proves native integrability and the one-dimensional native/interval-integral equality, then applies the endpoint theorem to the actual scalar composite. A genuine closed ellipse with nonzero integral disproves global exactness of x dy. The product rule differentiates the finite coefficient expansion and inserts its sign only when moving a coordinate differential past the first homogeneous form. The second derivative is an explicit mixed-partial sum, whose antisymmetry cancels in characteristic zero. All three accepted contract hashes remain unchanged. These are draft-semantic snapshots, not claims that these four files have compiled.

| Initial reviewed proof file | SHA256 |
| --- | --- |
| `CoordinateDifferentiation.lean` | `28e818daf01b4ac68bbeb070f679fadddaa131db5835f607da809781722c4be4` |
| `ExteriorDerivative.lean` | `7fb907283f7a78bf085537d237be64e4ad9b38aa15d1dc91398f9b99b1ead26c` |
| `ExactOneForms.lean` | `53cd839329a33e16b25824f504befb1ec7dfc03f9844fb6e5c5b78fd1a8c70ba` |
| `ExteriorDerivativeRules.lean` | `6305a768fb0bd7654545b737a030178d812c1dcaea870178514c355729a9e5b5` |


## Compiled change-of-variables reconciliation and section gate

The complete final `ChangeOfVariables.lean` file was independently re-read and accepted at SHA256 `13f65cf7c6656ce2b0165252090ec8a6d0293493a71c72f86cc28a02bd504659`. The contract hash remains unchanged. Final proof corrections explicitly bridge the Euclidean/coordinatized derivative and its typeclass presentations, and preserve the previously reviewed local inverse, support, indicator continuity, and native/measure integral argument. `evidence/ch10-change-of-variables-probes-compile.log` records successful compilation of the production module and both independent reflection clients. Their frozen probe file SHA256 is `5b58f2cde3763635cdf1ee9507603e4a0af531dcaa954f780ec11f5b7eebc4d8`. At root's request the canonical accepted-contract snapshot and reviewed-production manifest now extend through 10.9 only, with eight production modules and nine numbered principals; every earlier production hash was rechecked against disk.

## Exact pullback contract acceptance

The full `SurfaceMaps.lean` constructors and exact 10.21-10.25 contracts in `Pullbacks.lean` are independently accepted. The surface map construction restricts its regularity neighborhood to its intersection with the target preimage; its native domain and actual composite map are preserved. The identity parameter surface retains the original native domain, using the explicit coordinate/Euclidean equivalence. The all-ordered coefficient formula is a faithful generalization of the standard representation alongside 10.14; scalar pullback is explicit. Pullback regularity and all native integrability conclusions are included. Composition has the correct contravariant order, and differentiation uses precisely C1 form/C2 map regularity. No injectivity, nonzero Jacobian, nonempty set, or positive dimension is imposed. Initial accepted SurfaceMaps SHA256: `57cef14a2c52733a6aea2d410f1aed3101031d524ffa49f75fd65d093d1c3dde`; Pullbacks SHA256: `43e60a43270bbc18999139d16d195fc08f1a909800517b4e48e7f1bc3bfa5aeb`.

| Accepted contract | SHA256 |
| --- | --- |
| `pma10_21_contract` | `88dd9ed877e8c06fec48765c26afe689b46072b8554d3360b245ecc458551585` |
| `pma10_22_contract` | `e74d14887f8f9687dab2eff9de039adf29368d871e04ef92a53b1ef1b9b3d84b` |
| `pma10_23_contract` | `1e618011a23e88fd47e968e1e59f8428bb2955f1df2c555f9d19519257f0855a` |
| `pma10_24_contract` | `4d9a697387cdcc37fd2591f6873bcff832439223d188afd33cbffbab91466df4` |
| `pma10_25_contract` | `d8977f02e88599ef463e6e6911ff64d24edc2b7a3bf4dfa656af04e82b0f4599` |

The independently authored `FormAlgebraProbes.lean` and `ExteriorDerivativeProbes.lean` provide six additional clients: nonsorted two-form product sign, nonzero coefficient detected by an actual natively integrable surface, cancellation in the displayed raw form, scalar differential evaluation on a mixed-sign tangent, nonlinear curve endpoint integration on [-1,2], and C1-only one-form self-product differentiation. They await root compilation.


## Final example, standard-form, separation, and pullback-helper review

The final compiled example files were re-read completely. Compiler corrections preserve the actual scalar coordinate derivative, native endpoint identity, two signed ellipse integrals, spherical derivative/determinant, three successive native density integrations, complete closed-ball image, and interior-only injectivity. StandardForms derives the literal tuple sign under sorting, both exact displayed reorderings, and raw-form simplification. NativeSeparation and FormSeparation retain positive-measure finite boxes (including dimension zero), explicit native existence, the actual coordinate-plane surface, coefficient extraction by the dual exterior basis, and functional separation. Their final corrections concern syntax, elaboration/typeclass transparency, and pointwise negation only; accepted numbered contracts are unchanged.

The compiled pullback helper proofs were independently read. Evaluation under the induced exterior map is proved in every degree from the determinant pairing, and it yields actual surface-integrand equality on the parameter carrier via the chain rule. The identity-parametrization equality explicitly cancels the coordinate/Euclidean equivalence. These are kernel-compiled helper implementations, not claims that 10.21-10.25 principals have all compiled. Root reported the following files green; exact complete-file acceptance follows.

| Accepted compiled file | SHA256 |
| --- | --- |
| `FormExamples.lean` | `3e3c5478483102de6c37a760989be5924bf2765c1606b3546d30b8544b0d802f` |
| `SphereExamples.lean` | `87aaef719f53e5071ed3e853b4802cd98d1fbe5f1be8a6bbfbd172cfbb0d187f` |
| `StandardForms.lean` | `a7ec125be843cc5617234a59768589b4daf81fa6166e3482d7d4f21c81dbbed4` |
| `NativeSeparation.lean` | `d28c2362cdd3201023171dc8fbfaccab4d4ed8125c69ba6ff9532ed77d7783b4` |
| `FormSeparation.lean` | `9dd2504bc1139aca174d960888601015abd7454da928d870a07a619ee89a9d1a` |
| `PullbackAlgebra.lean` | `beec993d5a18137da7e8d4016e74bbe91d68332d0b50d5c4697ee86c78ac4b4f` |
| `SurfaceMaps.lean` | `57cef14a2c52733a6aea2d410f1aed3101031d524ffa49f75fd65d093d1c3dde` |
| `PullbackEvaluation.lean` | `92e334104c5f09da34cad0354702572b907adc4b04119ecd324b2f8885dd3c01` |

The full SurfacePullbacks, PullbackRegularity, and PullbackDifferentiation drafts are semantically accepted. Surface integration equality follows from carrier-wise integrand equality, with native existence separately derived from continuity. The regularity theorem proves C-r pullback from a C-(r+1) map and C-r coefficients using the finite standard expansion. The scalar chain rule and closedness of ordered products of coordinate differentials yield the exact C1-form/C2-map differentiation identity; no C2 coefficient premise is introduced. Draft snapshots are below; compiler corrections/final hashes remain pending. The canonical section manifests remain through 10.9 only.

| Accepted proof draft | SHA256 |
| --- | --- |
| `SurfacePullbacks.lean` | `d617f06fdd932989c67b5fa7f0cc618547e480f9e309ebf928ead3a2850aba5d` |
| `PullbackRegularity.lean` | `c792ab242191f21941227b968281e27b38372412b49768a514c266a5329128fd` |
| `PullbackDifferentiation.lean` | `793325ccdf07f2c4f837cb6f5b1fb2d4e4a251be717903c058a402671cc08178` |


The earlier FormProbes do not by themselves cover the spherical part of 10.12. At root's request the reviewer therefore added `SphereExampleProbes.lean`, with two independent public assertions: actual boundary noninjectivity alongside interior injectivity, and a genuine natively integrable volume-example surface with positive integral despite a zero boundary Jacobian. These probes await root compilation; they do not alter the production theorem or impose immersion.


## Final wedge reconciliation and canonical section through 10.17

The complete final WedgeProducts implementation is independently accepted at SHA256 `2927b89be671cbf2bbaafb42755d5e8b27bb39ae07189a10d81f87b069a55c2d`. The only changes since the reviewed draft are explicit finite-index/coercion conversions, pinned API names, and finite-sum order rewrites. Both source contract hashes remain unchanged. Root reports WedgeProducts and all three independent FormAlgebraProbes clients compiled successfully; the probe SHA256 is `ba45873e165b84289977892b0a60ab5f152a3a34aed8b0ae1295cac50ed1768e`.

Following root's 10.9 section commit and request, the canonical accepted-contract snapshot and reviewed-production manifest were extended through 10.17 only. All fourteen added complete production files match their independent acceptance hashes, every earlier file still matches, and all eight added numbered contract texts match the original accepted hashes. The manifest contains 22 production modules and 17 principals. No CoordinateDifferentiation, exterior-derivative, or pullback module is included at this section boundary. SphereExampleProbes is an additional pending compiler gate and is not represented as already compiled.
