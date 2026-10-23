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


## Compiled derivative reconciliation and simplex-chain architecture

Both independent SphereExampleProbes clients compiled successfully in `evidence/ch10-sphere-example-probes-compile.log`; exact probe SHA256 `daa56dc02527d93716e68e2894361d45280e9dfe38f550aa9f14ac8e8799ce5d`. The previously accepted examples therefore now have explicit boundary-degeneracy coverage.

The complete final ExteriorDerivative file was re-read and is accepted at SHA256 `32563a37cb03475c0565a7f7c87998d10c7f6aba1c146d3b2c32bd4a8ced68ab`. Its compiled CoordinateDifferentiation dependency remains accepted at SHA256 `28e818daf01b4ac68bbeb070f679fadddaa131db5835f607da809781722c4be4`. Root reports successful compilation of 10.18. Corrections add an explicitly typed coefficient EqOn, pinned Finsupp sum APIs, a correctly typed grade index, and coefficient refolding; all three stored contracts in the file remain semantically unchanged, and the 10.18 contract hash was reverified. Canonical manifests are still held through 10.17 pending the next requested section boundary.

`SimplexChains.lean` architecture is independently accepted at snapshot SHA256 `db6007136017c15e4477458eac0b5fecaa287381f94553571100a132c4ae6f89` before numbered 10.26-10.30 contracts. A C2Simplex retains its actual ambient map, proof-only existence of an open C2 neighborhood of the closed standard simplex, and an actual maps-into-target assertion. Pre/postcomposition use actual maps and correct neighborhood preimages, with no immersion or injectivity premise. Free finite integer combinations represent source multiplicities and orientation signs; ChainEq separately quantifies all continuous homogeneous form integration functionals. It does not identify raw Finsupp equality with source equality. Numbered contracts still owe affine recovery, signed zero-simplices, omitted-vertex boundary with the special first face, triangle orientation, native integral and pushforward identities, boundary commutation, and affine/general boundary agreement. No quotient by ChainEq or boundary invariance is accepted merely from this datatype.


## Affine-simplex and affine-chain contracts

The exact 10.26 contract is fully accepted after adding the source's arbitrary-real-vector-space affine characterization. This clause has no topology or finite-dimensionality assumption and characterizes the existence of an actual AffineMap by its constant-plus-linear formula. The Euclidean clauses retain determination by zero and basis vectors, arbitrary/repeated vertices, actual derivative and Chapter 9 Jacobian, nondegenerate full-dimensional orientation, standard positive orientation, and both signed zero-simplices. The signed point formula scales the integral, not the map. The generic characterization helper was also read.

The exact 10.28 contract and definitions in AffineChains are accepted before proofs: actual ordered vertices and target containment; free finite integer multiplicities; weighted sums, addition, scaling and cancellation of native integrals; functional chain equality over continuous homogeneous forms; and exact compatibility with the C2 chain representation. Existing 10.11 gives native existence of each genuine form summand.

| Accepted contract | SHA256 |
| --- | --- |
| `pma10_26_contract` | `d6607989ca1194a23fc0bc6d7c70d97bb1908b96cb96b4f2f64947966f9bd71e` |
| `pma10_28_contract` | `f0c02a549d42a0bcf48602941dc76ff870208a7751e5db43271d7c0810845b13` |

## Further compiled proof reconciliation

The final ExactOneForms, PullbackRegularity, PullbackDefinitions, SurfacePullbacks, SimplexChains, and SimplexChangeOfVariables implementations were re-read. Root reports all compiled successfully. The corrections retain the native-to-interval bridge, exact endpoint primitive, C1 coefficient regularity, derivative-induced scalar differential formula, actual carrier-wise surface identities, and the free-chain semantics. The simplex coordinate-change helper proves native existence separately from the measure Jacobian identity and retains arbitrary dimensions. Exact accepted complete-file hashes follow; canonical records remain through 10.17 until the requested calculus section gate.

| Accepted compiled file | SHA256 |
| --- | --- |
| `ExactOneForms.lean` | `e2d3e476b4f2e896af46956680cc0241855a3b6211a7fee0be13a6e5588f7274` |
| `PullbackRegularity.lean` | `79bf2beba1a14313ed24968b323e3396b366a6a57b234cbe527d637e1e24a523` |
| `PullbackDefinitions.lean` | `8e72423af8572af10ea0752550c4503b85e181699371d9d6f0b85eb31dfb8015` |
| `SurfacePullbacks.lean` | `d617f06fdd932989c67b5fa7f0cc618547e480f9e309ebf928ead3a2850aba5d` |
| `SimplexChains.lean` | `db6007136017c15e4477458eac0b5fecaa287381f94553571100a132c4ae6f89` |
| `SimplexChangeOfVariables.lean` | `2f38999ec892d4469902cf9d910e17d075cbf1f85ccc44e880ba124c60de9de5` |

Five independently authored PullbackProbes clients await root compilation: constant-map positive-degree annihilation versus scalar preservation, C1 closed-form pullback, zero-dimensional identity-parameter evaluation, restricted composition despite an ambient extension leaving the target, and observable noncommuting affine-map pullback order.


## Boundary/orientation contracts and compiled product rule

The complete final ExteriorDerivativeRules proof was independently re-read and accepted at SHA256 `b8b8f63c33f72ae7e14ef1a378708d98860c183323b89c6ab986fcea01fe77f9` after root reported successful compilation of 10.20. Final repairs explicitly instantiate the finite coefficient derivative sum and reorder the two finite indices; no statement, regularity assumption, graded sign, or mixed-derivative cancellation changed. Two independent exterior-derivative probe elaboration errors were repaired using explicit function coercion equality and numerical normalization, with propositions unchanged; their recompile is pending.

The exact 10.27 contract is independently accepted: every vertex permutation, including permutations moving the zero vertex; arbitrary or degenerate vertex families; dimension zero; a genuine continuous homogeneous form on the open target; reordered target inclusion and both native integrability assertions; and the signed actual surface integral identity. The exact 10.29 contract is also accepted: alternating omitted-vertex faces, affine/C2 face agreement, the special first-face base vertex, zero-insertion standard faces, the triangle's signs, and exact affine/general boundary compatibility. AffineFaces definitions and initial helper proofs were read, including the explicit Fin.cons(1-sum) top-face formula and the double-face deletion identity. Their final compilation/hash reconciliation remains pending.

| Accepted contract | SHA256 |
| --- | --- |
| `pma10_27_contract` | `d75e22048b9fa251ea2155e8527c44628e62f9d2e7e94736c1e14d8469180484` |
| `pma10_29_contract` | `52e0071fb8e2d185cab9b636dc7c87f28a81f69c25e9b056022c8a853c3b29df` |

### Pullback differentiation and simplex proof review

The final compiled PullbackDifferentiation proof is independently accepted at SHA256 `2077ad901b15816a82276e35611061d3bf8f8339c63b9ccfe4986692070d42e0`. The finite coefficient expansion uses only C1 form coefficients, C2 map coordinates, the scalar chain rule, and the already proved graded product rule and mixed-partial cancellation. Both domains remain arbitrary open sets and the map is constrained only on its source domain. The final edits are the pinned finite-sum projection name and removal of a redundant closing tactic; the accepted 10.22 contract is unchanged.

The exact 10.30 contract in ChainMaps is accepted at contract SHA256 `e61f30fa51788a5aa6dbeced1d6308b4e2c15737610c6d016bccddc80740ebe4`: actual C2 map composition, native integrability of both integrands and pullback equality, integer-chain linearity, boundary commutation, and exact affine/general compatibility. No injectivity or immersion premise is present. Its draft module snapshot is `43db6d6c4bc1ef2413a16d2debbb43d397d09d966973e184500602df12e33f7e`; numbered proof compilation remains pending.

The complete SimplexOrientation draft (`0deb22a93245eedd898f76fd9eec173b6fe7b0f43cd5ece2a278cec0fffac7b7`) is mathematically accepted pending compilation: the augmented vertex determinant establishes the sign for every permutation, including moves of the zero vertex, in zero dimension and for degenerate vertices; the actual affine self-map preserves the standard simplex; native change of variables and the derivative chain rule produce the signed integral identity. Native existence is concluded for both vertex orders.

The complete SimplexFTC draft (`7a952d73da4b8f95db40fdc1f49a9428c66baf11aeb95a4579285346b4c23c93`) is mathematically accepted pending compilation. Both actual native existence assertions come from 10.4 before the equality proof. Disintegration is at an arbitrary chosen coordinate with all remaining coordinates ordered; stopped slices are identified pointwise for every base point, including collapsed fibers. The scalar FTC supplies the upper-minus-lower face expression. This helper introduces no vertex-orientation premise and does not substitute almost-everywhere existence for native integrability.

The complete AffineChains, AffineFaces, and SimplexBoundaries drafts were independently read after their numbered proofs were filled. The finite integer sums use actual native integrals; transfer to C2 chains preserves the actual parametrizing maps. Face maps have the stated barycentric description; deleting vertex zero changes the base vertex; the two-face deletion identity is an affine-map identity, not an assumed chain quotient. The 10.29 proof uses the alternating signs and gives exact affine/general compatibility. Draft snapshots (compilation pending at this review):

- `AffineChains.lean`: `c1a6ba37485db4343cccaacc0db8d6648b83464cf832a99e57b55d2bc1cd231d`.
- `AffineFaces.lean`: `1d01503fc62950100d6b7cf62a65b3cdf4a540645beb1814389b124f69d539fa`.
- `SimplexBoundaries.lean`: `4f5fb0e964d19ba85ec259f9dafae58a624e37ab7b0c65e8f1b3f186e22a5c6c`.

### Canonical reconciliation through 10.20

All 22 previously accepted production hashes were rechecked unchanged. The four final compiled exterior-differentiation modules match their independently accepted hashes, and exact contract hashes 18-20 are unchanged. Canonical records now contain 26 production modules and 20 numbered principals. The three independent ExteriorDerivativeProbes assertions compiled successfully in the parent process at SHA256 `ccff9065bd747e4340fd147cfbef1eb2287fcd5f853a59171b9ecdc64722492e`: mixed tangent evaluation, a nonlinear curve on [-1,2] with native endpoint value 33, and the C1 odd-degree product cancellation. The reviewer ran no builds. Chapters 10.21 onward remain outside these canonical manifests until their separate integration gate.

The final compiled AffineSimplices module is independently accepted at SHA256 `952393bfb0741aa222a1acfb7b23c3c0316cba9e74a5b80303885031d3b1467c`. All definitions, helper proofs and the principal assembly were read at these bytes. The exact revised contract 26 retains SHA256 `d6607989ca1194a23fc0bc6d7c70d97bb1908b96cb96b4f2f64947966f9bd71e`: the generic affine characterization has no finite-dimensional or topological restriction; all arbitrary and degenerate vertex constructions are actual maps; the derivative/Jacobian bridge and signed zero-simplices retain their source meanings. Final elaboration fixes did not weaken any clause.

The now-complete ChainMaps proof draft (`9a64b331e63ddd9c6bc8f155db7463c10e4b020e41b832cb025ae3cdf4ac1e5c`) is mathematically accepted pending compilation. The principal reuses the actual native surface-pullback theorem; boundary commutation is proved as equality of free-chain maps; affine compatibility uses the exact vertex map. The added chainIntegral_map helper derives the finite-chain native pullback equality by the linear-combination universal property.

### Canonical reconciliation through 10.25

All 26 prior production hashes were rechecked unchanged. The eight pullback modules match their independently reviewed final bytes, and exact contracts 21-25 match their accepted hashes. Canonical records now contain 34 production modules and 25 numbered principals. Parent compilation is green for all production and for the five independent PullbackProbes assertions, SHA256 `856e21baa0bcc5c164c9d141142a24cfc57ddf47ab2295743e5d4cd13601b805`. The probes test constant-map grade behavior, closed pullback regularity, dimension-zero native integration, a surface constrained only on its actual parameter domain, and contravariant order using noncommuting affine maps. The reviewer ran no builds. Later simplex modules remain outside these canonical manifests.

Final compiled AffineFaces, AffineChains (28), and SimplexFTC were reconciled against the prior full independent proof review. AffineFaces changes only clarify the real coordinate type and normalize the first-face scalar expression. AffineChains is byte-for-byte unchanged. SimplexFTC changes only make the insertNth dependent family explicit and expose a pointwise set-membership goal. Their mathematical statements, native existence conclusions, and proof strategies are unchanged. Accepted final hashes:

- `AffineFaces.lean`: `e8190800f232c21709e4928c4e972073fd4dbf07aa27f9985b76ce90e840d441`.
- `AffineChains.lean`: `c1a6ba37485db4343cccaacc0db8d6648b83464cf832a99e57b55d2bc1cd231d`.
- `SimplexFTC.lean`: `13aed6c37f0548629c64a1d4357525614490d20d678410bae8f81d827986cbee`.

The standardC2Simplex definition was moved without mathematical change from SimplexStokes to StandardSimplexSurface. The exact standardSimplexStokes_contract is independently accepted: arbitrary open Euclidean neighborhood containing the closed standard simplex, C1 boundary-degree form, d=0 included, and actual native surface/alternating-chain integral equality. The helper is not a replacement for the general C2-chain 10.33 statement. Native existence follows from existing genuine-surface regularity results, and no separate integrability premise was added.

The complete support-only SimplexFormFaces draft (`020bac31521a693bf809a6ac8e23e7dcc539350aa3d3ddabb0a6aaf60f68f00f`) is mathematically accepted pending compilation. Its first identity derives the left-wedged coordinate differential sign from a first-row cofactor expansion, keeping all remaining indices ordered. Its second identity uses the actual upper-face tangent frame e_(j+1)-e_0 and the augmented vertex determinant to derive the alternating coordinate-face evaluations. The homogeneous extension uses the already proved finite standard expansion, and both identities include d=0. These are algebraic helpers, not replacements for the native simplex FTC or Stokes integration statements.

### Boundary scope and Stokes transport

The 10.31 square-surface consequence on printed p.271 has the full C1 surface scope of 10.10. A finite sum of actual C1 triangle/edge Surface integration functionals preserves this scope; C2 chainBoundary is an additional specialization, not a replacement. Research for the all-continuous-form boundary-independence clause is recorded in `research/pma-ch10-boundary-approximation.md`, using existing smooth-density and Tietze APIs; no implementation was authored by the reviewer.

The exact pma10_33_contract is independently accepted at SHA256 `cbe3ea4381211eee7e485b55e9e334a9f1dc239fe56ed9c3a3182e803039dd59`: every finite integer C2 chain of positive dimension in arbitrary ambient dimension, and every C1 boundary-degree form on an open target. No injectivity, nondegeneracy, rank, or integrability hypothesis is introduced. The complete conditional StokesTransport proof was read: the parameter neighborhood is correctly restricted to the preimage of the form domain, the standard simplex is transported by the actual map, differentiation commutes with pullback under the stated C2/C1 regularity, native integration commutes with pushforward, and finite-chain linearity extends the result. The standard-simplex premise remains explicit in this helper until its separate proof is assembled.

Final parent-compiled SimplexBoundaries and ChainMaps are independently accepted at these exact hashes:

- `SimplexBoundaries.lean`: `8c9f54193e33656cd9ab80b424164366331b073e144f702b3d51f2befcb1b3ff`.
- `ChainMaps.lean`: `9a64b331e63ddd9c6bc8f155db7463c10e4b020e41b832cb025ae3cdf4ac1e5c`.

The final 29 edit only unfolds lmapDomain/mapDomain before the existing boundary-singleton rewrite. Contract 29 is unchanged; ChainMaps is byte-for-byte unchanged from its full proof review.

The final compiled SimplexOrientation module is independently accepted at SHA256 `e542c67929860c59867228284ad9248cc7a0ce7178716b8ed69ce0a2055e587b`, with unchanged contract 27 hash `d75e22048b9fa251ea2155e8527c44628e62f9d2e7e94736c1e14d8469180484`. Final proof edits name the transpose matrix, make determinant absolute-value coercions explicit, and type the multiplied continuous integrands. The proof still covers every vertex permutation, moving the base vertex, arbitrary degeneracy, and dimension zero.

The compiled conditional StokesTransport module is independently accepted at SHA256 `dcbe3ac1e4d4f514f9695d7b723123da145c4e04b4850398ca0e540de48ded2f`, together with StandardSimplexSurface `c48bc3156d2958639f180a60cd6bfbe7eece26aab9021b4795a7c538a95959cd`. This acceptance is for the definitions and conditional transport lemmas; the final numbered Stokes theorem still requires the separate standard-simplex proof. The native C1/C2 scopes and arbitrary finite-chain conclusion are unchanged.

The complete compiled StokesCoefficients proof is independently accepted at SHA256 `70d4aa42c11ca0967c7373f84fac79314b222d9f3e3f85c9cdb7ce8e2960ded0`. It derives regularity and coordinate derivatives of linear form evaluations from finite coefficient expansions, and connects the product-coordinate derivative to the Euclidean coordinate derivative through the actual linear equivalence. No norm or topology on the exterior algebra is assumed implicitly.

The full SimplexStokes draft is mathematically accepted at snapshot `941da97537191d522d90b2c03b6a5c92e364c290ed9933ed96fa51c3ce6d3b1a`, pending compilation. The scalar upper-face coordinate insertion is related to the actual face opposite zero by a vertex permutation. Its scalar integral is unchanged by that unsigned reparametrization; the orientation signs are separately derived from the actual face tangent frames. The standard full-dimensional derivative integrand is the signed sum of the coordinate derivatives of omitted coefficients. Applying the native scalar FTC and combining the finite sums yields the alternating boundary integral, with lower-face sign (-1)^(i+1). All compact native integrands are supplied by actual continuity, the coefficient regularity is exactly C1 on the open neighborhood, and d=0 is retained throughout.

### Canonical reconciliation through 10.30

All 34 prior production hashes were rechecked unchanged. The eight final simplex/chain modules match their independently reviewed bytes, including the actual-map C2 chain foundation and the native simplex change-of-variables helper. The five exact contract hashes 26-30 match their prior acceptance. Canonical records now contain 42 production modules and 30 numbered principals. The final independent SimplexChainProbes file compiled successfully at SHA256 `8c981630f64af9e6be95783a7dbff20ae6b99519684c86a31d160b690936694e`: an origin-moving transposition reverses the native integral, a repeated base vertex forces zero, and the segment boundary evaluates an arbitrary zero-form as terminal minus initial value. The last probe repair explicitly instantiated otherwise unused generic universes of pma10_26; no mathematical statement changed. The reviewer ran no builds. All later boundary/Stokes drafts remain outside these canonical manifests.

The exact pma10_32_contract is independently accepted at SHA256 `59966feb54931ef9a6b732deb6d95a176ffd4834e78ddba1f45e9d4827505d0c`. It retains the literal spherical map on [0,pi]×[0,2pi], full unit-sphere image, and the four actual counterclockwise interval edge maps: forward meridian, south-pole constant, reverse meridian, north-pole constant. For every continuous one-form on any target containing the image it concludes native integrability of all four edges, zero pole integrals, opposite meridian integrals, and total boundary functional zero. Neither exactness nor C1 form regularity is assumed.

The SurfacePrecomposition and RectangleEdges definitions and complete initial helper proofs were independently read and mathematically accepted pending compilation. Genuine C1 surface precomposition uses an open preimage neighborhood; interval reversal preserves its actual closed interval; the sign comes from its derivative determinant; constant-curve evaluation is zero for degree-one forms. Rectangle edge maps retain actual side intervals and allow degenerate cells. Draft hashes:

- `SphereBoundary.lean`: `bbdb9c43bc4f49a55eee0b7a04a0e0994ff042b36dbc8eb6661c6d9e66015b3a`.
- `SurfacePrecomposition.lean`: `cc601cf75fb8db1ed3b072078b563fe979c74b1afbc733b9b994dce99a4d046b`.
- `RectangleEdges.lean`: `62e7e06908c459df446c619a4fb131eabd95f26a5f0a2b67d9efa658971356ca`.
