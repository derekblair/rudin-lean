# Independent source contracts for PMA 10.42–10.51

Reviewer: `ch8_fidelity`. Source: authorized local third-edition PDF, printed pp.281–288 (PDF pp.290–297), visually rechecked in memory on 2026-10-23. These are proposed semantic contracts, not Lean declarations or completion claims. No proof text is copied. All coordinate indices below are zero-based. The existing `Euclidean`, `FormField`, `Surface`, `ParameterDomain`, `SimplexChain`, `PositiveRegion`, and native integral interfaces remain in force.

## Shared exact coordinate conventions

For `F : Euclidean 3 → Euclidean 3`, write `Fᵢ(x)=F(x)(i)` and `Dᵢf(x)=coordinatePartial f x i`. Define the following actual fields and forms:

- `grad u = (D₀u,D₁u,D₂u)`.
- `curl F = (D₁F₂−D₂F₁,D₂F₀−D₀F₂,D₀F₁−D₁F₀)`.
- `div F = D₀F₀+D₁F₁+D₂F₂`.
- `λ(F)=F₀ dx₀+F₁ dx₁+F₂ dx₂`.
- `ω(F)=F₀(dx₁∧dx₂)+F₁(dx₂∧dx₀)+F₂(dx₀∧dx₁)`.
- `volₙ=dx₀∧...∧dxₙ₋₁` and `densityForm(f)(x)=f(x)•volₙ`.

In standard increasing order, the coefficient of `dx₀∧dx₂` in `ω(F)` is **−F₁**. The middle cyclic term cannot be silently reordered without its sign. Tensor equalities on an open set should also imply the already-defined actual integral equality.

## 10.42 — field/form correspondence (printed p.281)

Quantify an arbitrary open `E ⊆ Euclidean 3` and any field continuous on `E`.

1. `λ(F)` is a genuine continuous one-form and `ω(F)` a genuine continuous two-form on `E`.
2. Every genuine continuous one-form on `E` is `EqOn` to `λ(F)` for some field continuous on `E`; every genuine continuous two-form is similarly `EqOn` to `ω(F)`. Include uniqueness on `E`, or prove injectivity of both correspondences there. No condition on arbitrary extensions outside `E` is needed.
3. The three operators have exactly the coordinate formulas above. A C1 scalar gives a continuous gradient; a C1 field gives continuous curl and divergence. These are actual regularity conclusions, not extra assumptions on the output operators.
4. For reuse in 43, establish the corresponding C1/C2 coefficient-to-field regularity equivalences and the inverse extraction formulas: one-form coefficients `{0},{1},{2}`; two-form coefficients `{1,2},−{0,2},{0,1}`.

## 10.43 — identities and potentials (printed pp.281–282)

On an arbitrary open `E ⊆ Euclidean 3`:

1. `ContDiffOn ℝ 2 u E → EqOn (curl (grad u)) 0 E`.
2. `ContDiffOn ℝ 2 G E → EqOn (div (curl G)) 0 E`.
3. If `E` is C2-equivalent to a convex open set, `ContDiffOn ℝ 1 F E` and `EqOn (curl F) 0 E` imply `∃ u, ContDiffOn ℝ 2 u E ∧ EqOn (grad u) F E`.
4. Under the same domain and input regularity, `EqOn (div F) 0 E` implies `∃ G, ContDiffOn ℝ 2 G E ∧ EqOn (curl G) F E`.

The equivalence should be the actual two-sided `C2DomainEquivalence` from a convex open subset of three-space to `E`, or an explicitly equivalent predicate. Do not assume a potential in this predicate. Empty domains need no exceptional exclusion.

The form bridges used by the source are substantive attached assertions:

`λ(grad u)=du`, `dλ(F)=ω(curl F)`, and `dω(F)=(div F)•vol₃`, with the appropriate C1 premises and equality on `E`. Thus zero curl is equivalent to closedness of `λ(F)`, and zero divergence to closedness of `ω(F)`. Equality to a gradient or curl is equivalent to the corresponding form derivative equality.

**Regularity check:** the printed converse statements really give C2 `u` and C2 `G`; both output superscripts were compared with the input C1 superscript at 520dpi. A C1 homotopy primitive alone does not yet prove item4. For item3, all first scalar derivatives equal the C1 components of `F`, giving the C2 upgrade. For item4, `curl G=F` only identifies antisymmetric combinations of first derivatives; a separate regularity argument or a stronger constructed primitive is needed. Neither a C2 premise on `F` nor a C1 conclusion for `G` preserves this source contract. Pulling back a C2 primitive through a merely C2 coordinate map also yields only an immediate C1 coefficient estimate, so this issue should be resolved explicitly rather than hidden in transport.

## 10.44 — volume element (printed p.282)

For every dimension `n`, the ordered basic top form is the volume element. Let `Φ : Surface n n E`, whose actual parameter domain is a cell or simplex, be injective on that closed domain, and let its coordinate Jacobian be positive there. Its existing regularity is **C1**, and must suffice. Let `f` be continuous **on the actual image** of `Φ`; global continuity on the ambient `E` is unnecessary.

Conclude actual native integrability of the density-form integrand, its formula

`surfaceIntegrand Φ (densityForm f) u = f(Φ(u))*Jac(Φ)(u)`,

and equality of its native parameter integral with the ordinary integral of `f` on the image (using the coordinate/Haar bridge already established). The image integral must be identified as the ordinary integral, not defined to equal the desired surface integral. Density one gives image volume and parameter-volume equality; dimension2 gives the area notation.

A stronger theorem allowing singular boundary derivatives with positive interior Jacobian is acceptable, but it must still cover arbitrary C1 parametrizations. Reusing `PositiveSimplex`, whose structure requires C2, alone narrows this item. The top-form integrand identity is useful without injectivity; only the image-integral conclusion needs it. Include the dimension-zero convention when the shared interfaces permit it.

## 10.45 — Green's theorem and area (printed pp.282–283)

For open `E ⊆ Euclidean 2`, a source31 region `R : PositiveRegion 2 E`, and scalar `α,β` of class C1 on `E`, conclude

`chainIntegral (α dx₀+β dx₁) R.boundary = regionIntegral R (D₀β−D₁α)`.

Here the region integral is identified with the ordinary image integral and with the native top-form chain integral. Include genuine integrability on every finite piece and boundary piece. The source's closed-region admissibility is the finite positive parametrized decomposition from31, not an arbitrary closed set assumed to carry a boundary.

Attached consequences, with the exact factors/signs:

- `(1/2)*chainIntegral (x₀ dx₁−x₁ dx₀) R.boundary = area(R.carrier)`.
- `chainIntegral (x₀ dx₁) R.boundary = area(R.carrier)`.

The intermediate derivative identity is `d(α dx₀+β dx₁)=(D₀β−D₁α)•vol₂`.

## 10.46 — normal, tangent plane, and surface area (printed pp.283–285)

For any C1 two-surface `Φ : Surface 2 3 E` and any parameter point `p` in its actual domain, let `A=DΦ(p)`, `a=A e₀`, `b=A e₁`. Define its directed normal by actual minors:

`N=(a₁b₂−a₂b₁,a₂b₀−a₀b₂,a₀b₁−a₁b₀)`.

1. For every `f` continuous on the surface image, prove actual native integrability of `f(Φ(p))*‖N(p)‖`; its integral defines the surface area integral. Density1 gives surface area. Neither injectivity nor rank2 is a premise of this definition/existence assertion.
2. `⟪N,a⟫=0=⟪N,b⟫`, and consequently `N` is orthogonal to the entire derivative range.
3. `det[a,b,N]=‖N‖²`. Rank2 is equivalent to `N≠0`; under rank2 this determinant is positive and the affine tangent image `Φ(p)+range A` has dimension2. Rank0/1 implies `N=0` and tangent-image dimension0/1 respectively.
4. The affine image of the unit parameter square has area `‖N‖`. For every parameter rectangle, its affine-image surface area is `‖N‖` times the rectangle's ordinary area. Translation of the affine map does not affect the result; degenerate rectangles and rank-deficient maps give zero.

These are area statements in the native parametrized-surface sense established here. Three-dimensional Haar volume of a planar image is not its area. A separate Hausdorff-area theory is not demanded by the text. The tangent plane is attached to the parameter point; no global surface-image injectivity should be added.

## 10.47 — the actual torus example (printed pp.285–286)

For every `0<a<b`, construct the actual C2/C1 maps and cells, rather than assuming their existence as premises:

`K=[0,a]×[0,2π]×[0,2π]`,
`Ψ(t,u,v)=(t cos u,(b+t sin u)cos v,(b+t sin u)sin v)`,
`D=[0,2π]²`, `Φ(u,v)=Ψ(a,u,v)`.

Required conclusions:

1. `Ψ` is injective on `interior K`; no closed-cell injectivity is asserted. Its Jacobian in the **(t,u,v)** order is `t*(b+t sin u)`. On `K` it is nonnegative and is strictly positive exactly when `t>0`.
2. Identify `Ψ(K)` with the closed solid torus, for example `{x | x₀²+(sqrt(x₁²+x₂²)−b)²≤a²}`. The actual native volume integral and ordinary image volume both equal `2*π²*a²*b`.
3. Regard the C2 cell surface as the actual finite chain furnished by41. Its boundary integration functional for **every continuous two-form** equals the functional of the outer surface `Φ` (or its actual rectangle chain). The `u=0,2π` pair cancels with opposite orientations, as does the `v=0,2π` pair; the `t=0` face has zero two-form integral because its two-dimensional derivative minors vanish. Its image is a circle, not a constant map. The `t=a` face has the positive `(u,v)` orientation.
4. Its normal is `N=a*(b+a sin u)*n`, where `n=(cos u,sin u cos v,sin u sin v)`. Prove `‖n‖=1`, positive scalar factor, and `‖N‖=a*(b+a sin u)` throughout `D`.
5. The actual native surface area is `4*π²*a*b`.
6. Prove outwardness, for example by a local positive normal displacement leaving the solid torus, or a positive derivative of its explicit defining function. A global ray-disjointness claim would be unnecessarily stronger and can fail after a ray travels through the hole. The source's displayed check at `u=v=π/2` gives the maximal z-coordinate `b+a` and `N=a*(b+a)e₂`.

## 10.48 — circulation, including zero velocity (printed pp.286–287)

Let `γ` be a C1 curve/surface in an open `E ⊆ Euclidean 3`, and `F` continuous on `E`. The source interval is `[0,1]`; using any actual `ParameterDomain 1` interval is a harmless generalization. Let `v(t)=γ'(t)` and choose `τ(t)=v(t)/‖v(t)‖` if nonzero, and `e₀` otherwise.

Prove `‖τ(t)‖=1` and `v(t)=‖v(t)‖•τ(t)`, including zero velocity. Prove actual native integrability and the three equal integral formulas: the finite coordinate sum of `Fᵢ(γ(t))*vᵢ(t)`; `⟪F(γ(t)),v(t)⟫`; and `⟪F(γ(t)),τ(t)⟫*‖v(t)‖`. These equal the one-form integral of `λ(F)`.

The arc-length notation abbreviates the last parameter formula and should connect to the Chapter6 C1-curve speed/length result. The choice of any unit fallback at zero velocity gives the same weighted integrand. Do not assert continuity of the normalized tangent itself: it need not be continuous at a zero of velocity. Nor may `F·τ` be treated as an unambiguous ambient function of the image when the curve is not injective.

## 10.49 — flux, including zero normal (printed p.287)

Let `Φ : Surface 2 3 E` be arbitrary C1 and `F` continuous on `E`. Its native `ω(F)` integral equals the actual native parameter integral of `⟪F(Φ(p)),N(p)⟫`. Define `ν=N/‖N‖` when nonzero and `e₀` otherwise; prove unit norm and `N=‖N‖•ν` everywhere. The same native integral equals that of `⟪F(Φ(p)),ν(p)⟫*‖N(p)‖`, the normal-component area notation.

Prove existence of these weighted integrals using equality to the continuous dot-normal integrand. Arbitrary unit fallback gives the same value at zero normal. Normalization need not be continuous; neither immersion nor injectivity may be assumed. The normal is indexed by the parameter point, including multiple preimages of a surface-image point.

## 10.50 — classical Stokes (printed pp.287–288)

For open `E ⊆ Euclidean 3`, C1 `F` on `E`, and every C2 two-surface with an actual cell or simplex parameter domain, conclude that the native flux of `curl F` through the surface equals circulation of `F` along its positively induced boundary chain. A finite C2 two-chain version may additionally be given, but the full C2 **cell surface** case must not disappear behind a simplex-only quantifier. Neither parametrization injectivity nor immersion is required.

Use the independently proved `dλ(F)=ω(curl F)` and49/48 integral bridges; the desired equality must not be built into the definitions of flux or circulation. Native domain and boundary integrability are part of a usable contract. The tangent and normal expressions retain their zero-vector conventions.

## 10.51 — divergence theorem (printed p.288)

For open `E ⊆ Euclidean 3`, C1 `F` on `E`, and a source31 positive region `R : PositiveRegion 3 E`, the ordinary region integral of `div F` equals the outward flux of `F` through `R.boundary`. Identify the left side with the native top-form chain integral and the right side with the sum of actual native normal-component area integrals on the oriented boundary pieces. Include integrability and the established functional independence of the region's positive decomposition.

The derivative bridge is `dω(F)=(div F)•vol₃`. No injectivity or globally defined normal is added to individual boundary parametrizations beyond source31's admissibility; orientations and finite multiplicities are retained. The conclusion is not a statement for arbitrary closed subsets without a prescribed admissible positive boundary.
