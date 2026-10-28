# PMA 10.43 proof attack

**Outcome: REDUCED-TO-ONE-LEMMA.** The unchanged printed contract is kernel-equivalent to the single symmetric first-order system stated below. Its solvability remains unproved. The module also kernel-proves an abstract quantitative lifting mechanism that retains every kernel direction and accommodates different outer-data and inner-output spaces. **Issue #14 remains open.**

Base: draft PR #27, branch `thm-1043-final-clause`, commit `c9d55a22e4a060c24bf754235bad24ab5deb71cf`. Author branch: `rudin1043-proof-attack`. All new Lean declarations are in `rudin/Rudin/Research/PMA1043ProofAttack.lean`; `PMA1043Compatibility.lean` is imported unchanged. No production statement, import inventory, toolchain pin, or Mathlib pin was edited.

This is author work and author verification. **No programme review has run on this work.** Collaborating agents contributed proofs and analytic research as authors, not reviewers. Nothing has been merged by this lane.

## The single remaining analytic lemma

The exact unproved proposition is `Rudin.PMA.Chapter10.SymmetricDerivativeLifting`.

For **every** pair of open sets `U,E ⊆ ℝ³`, every `C2DomainEquivalence U E` (a C² map with C² inverse on these domains), with `U` convex, and every ambient function `F : ℝ³ → ℝ³` that is C¹ on `E` and satisfies

```text
∂₀F₀ + ∂₁F₁ + ∂₂F₂ = 0 on E,
```

there exist three ambient row fields `Sᵢ : ℝ³ → ℝ³`, `i ∈ {0,1,2}`, such that each `Sᵢ` is C¹ on `E`, the matrix is symmetric on `E`, and

```text
Sᵢ(x)ⱼ = Sⱼ(x)ᵢ                  for every x ∈ E and i,j ∈ {0,1,2},
curl(Sᵢ)(x) = (1/2) ∂ᵢF(x)       for every x ∈ E and i ∈ {0,1,2}.
```

Here `∂ᵢF = (∂ᵢF₀,∂ᵢF₁,∂ᵢF₂)`. In scalar coordinates the nine equations are, for each `i`:

```text
∂₁Sᵢ₂ − ∂₂Sᵢ₁ = (1/2) ∂ᵢF₀,
∂₂Sᵢ₀ − ∂₀Sᵢ₂ = (1/2) ∂ᵢF₁,
∂₀Sᵢ₁ − ∂₁Sᵢ₀ = (1/2) ∂ᵢF₂.
```

**Norms and domains:** this is a qualitative lemma with no norm bound, boundary condition, compact-support condition, or prescribed choice of solution. Neither the domains nor the functions need be globally bounded. All regularity, symmetry, and equations are required only on the original open `E`; ambient extensions outside it are unrestricted. The unknown consists of six independent C¹ scalar entries because of symmetry. Only first derivatives of `F` and `S` occur. The quantitative norms used for the separate fixed-ball target are specified below.

### Why this is the entire gap

The new theorem

```lean
pma10_43_contract_iff_symmetricDerivativeLifting :
  pma10_43_contract ↔ SymmetricDerivativeLifting
```

is proved without either side as an assumption. The forward and reverse implications are kernel-checked, including the original domain quantifiers and all four clauses of the existing contract.

The construction uses

```text
K(F) = (1/2) [[0, −F₂,  F₁],
              [F₂, 0, −F₀],
              [−F₁,F₀, 0]].
```

The module proves `curl K(F)ᵢ = −(1/2) ∂ᵢF` on `E` when `div F=0`. Thus `M=K(F)+S` has C¹, curl-free rows. The already-proved scalar converse integrates each row on the **original** `E`, producing C² functions `Gᵢ` with `∂ⱼGᵢ=Mᵢⱼ`. The prescribed skew differences give `curl G=F`. Conversely, a C² potential gives `M=DG`; subtracting `K(F)` gives a symmetric C¹ solution of the displayed system. The other three contract clauses are supplied by the existing production theorems.

This reduction needs no unproved partition-of-unity theorem, domain transport estimate, local extension theorem, or extra regularity assumption. It extends PR #27's whole-plane planar compatibility criterion to the full three-dimensional contract. It changes the analytic unknown and isolates a simultaneous first-order compatibility problem; it does not establish a new existence estimate for that problem.

## Kernel-checked quantitative fragment

Inside `Rudin.PMA.Chapter10.ProofAttack`, for a continuous real linear map `T : X → Y`,

```text
allGaugeCost(T,x) = ‖[x]‖ in X/ker(T)
                 = inf { ‖z‖ : Tz=Tx }.
```

The exact infimum identity is proved, not merely used as an interpretation. The bound

```text
∃ C>0, ∀ x, allGaugeCost(T,x) ≤ C‖Tx‖
```

is equivalent to existence of some positive constant giving actual representatives `z` with `Tz=Tx` and `‖z‖≤C‖Tx‖`. The proof uses arbitrary positive slack and enlarges the constant from `C` to `C+1`; it does not assume that an infimum is attained. With `X` complete, dense range plus the quotient bound implies surjectivity. With both spaces complete, this becomes an iff by the Banach open mapping theorem.

The strongest approximation fragment is `lifting_extends_from_dense_submodule`:

> Let `X` be a real Banach space and `Y,Z` real normed spaces. Let `T:X→Z` and `R:Y→Z` be continuous linear maps and `D` a dense real linear subspace of `Y`. Suppose there is `C>0` such that every `y∈D` has some `x∈X` with `Tx=Ry` and `‖x‖≤C‖y‖`. Then every `y∈Y` has an `x∈X` with `Tx=Ry`.

There is no hypothesis that the choices of `x` are linear or continuous. The proof constructs the unique linear lift into the complete quotient `X/ker(T)`, extends it from the dense subspace, and then chooses a representative. The separate map `R` allows the outer-ball data norm and inner-ball curl equation to differ. The `R=id` specializations prove the dense-class surjectivity criterion and its Banach converse.

These are abstract normed-space results. The code does not instantiate `X,Y,Z,D,T,R` with classical C²/C¹ vector-field spaces, curl, restriction, and smooth closed data.

## Fixed-ball estimate and the analytic attack

Write `Bᵣ={x∈ℝ³:|x|<r}`. For a vector or matrix field defined near the closed ball, use the componentwise norm

```text
‖v‖ₖ,ᵣ = max over components a and multiindices |α|≤k
          of sup over x∈B̄ᵣ of |∂ᵅvₐ(x)|.
```

The actual-solution version of PR #27's quantitative target is:

> There exists `C>0` such that for every open `O⊇B̄₁` and every smooth `H:O→ℝ³` with `div H=0` on `O`, there are an open `V` with `B̄₁/₂⊆V⊆O` and `A∈C²(V;ℝ³)` satisfying `curl A=H` on `V` and `‖A‖₂,₁/₂≤C‖H‖₁,₁`.

The choices of `V,A` may depend on `H,O`; `C` may not. Every gauge remains allowed. The normalized-input and infimum formulations have the same existence-of-a-constant content, but no attainment or equality of the enlarged numerical constants is assumed.

**New informal matrix-norm observation.** Let `m(H)` be PR #27's infimum over all potentials, and let `m_J(H)` be the infimum of `‖M‖₁,₁/₂` over C¹ matrices defined near `B̄₁/₂`, with closed rows and skew differences `H`. Then `m_J(H)=m(H)` for these componentwise norms. A potential gives `M=DA` and the inequality `m_J≤m`. Conversely, integrate each row on a slightly larger ball and normalize `Aᵢ(0)=0`. On the half ball,

```text
|Aᵢ(x)| ≤ (Σⱼ |xⱼ|) ‖M‖₀,₁/₂ ≤ (√3/2) ‖M‖₀,₁/₂,
```

while `DA=M` and `D²A=DM`. Since `√3/2<1`, `‖A‖₂,₁/₂≤‖M‖₁,₁/₂`, proving the reverse inequality after taking infima. This calculation is ordinary mathematics in this report; its norm estimates are **not** Lean theorems in the new module. It supplies a first-order quantitative target without choosing Coulomb gauge.

The positive regularity results checked do not establish that estimate. Dacorogna–Moser's divergence estimates use Hölder exponents strictly between zero and one; no passage to the classical integer endpoint follows just by setting the exponent to zero. [Primary paper, Theorem 2](https://ems.press/content/serial-article-files/17385). Costabel–McIntosh's order-minus-one Poincaré operators give results on their stated Sobolev/Besov scales; integer `B²∞,∞` regularity does not assert classical C² regularity. [Primary preprint](https://arxiv.org/pdf/0808.2614). Berselli–Longo's classical divergence construction assumes a Dini modulus, including an integral of `ω(r)/r`; arbitrary continuous first derivatives provide no such hypothesis. [Primary preprint, Theorems 16 and 19](https://arxiv.org/pdf/1712.07917).

The proof stopped at simultaneous symmetric C¹ solvability of the displayed system, or, on the quantitative route, at a uniform bound for such completions. No positive endpoint estimate was obtained. The killed Coulomb and repairable annular routes were read and were not presented as new attempts or counterexamples.

### Quantitative-equivalence work that remains informal

The new abstract lifting theorem supplies one functional-analytic mechanism. A concrete proof of PR #27's full quantitative equivalence still needs classical function-space construction/completeness, continuity of curl and restriction, density of smooth divergence-free data with the required norm and domain conventions, localization, and gauge patching. Its necessity also needs the concrete Fréchet-space setup and open mapping application. These have not been silently imported as proved facts. The separate exact matrix reduction above integrates directly on `E` and does not depend on any of these unfinished steps.

## What this does NOT show

- It does not prove or disprove the printed C¹-to-C² vector-potential clause, and does not close #14.
- It does not prove the fixed-ball uniform estimate, its negation, or its equivalence to the contract in Lean.
- It does not prove the remaining symmetric first-order solvability lemma. The outcome is an exact qualitative reduction, with a separate abstract quantitative fragment.
- It does not assert that a selected Coulomb/radial representative suffices, that individual row/column solutions are compatible, or that Hölder, Dini, or Zygmund regularity gives the requested classical endpoint.
- It does not claim a literature-wide impossibility result or that the problem is open in the literature.
- The research module remains outside the default `Rudin` import closure. Its explicit target and module-wide audit are required in addition to the production build.

## Recorded author verification

Toolchain pin: `leanprover/lean4:v4.34.1`. Actual project output:

```text
Lean (version 4.34.1, x86_64-unknown-linux-gnu, commit 5045d0056413266e57c625dcd7c365b10e377c52, Release)
```

Mathlib commit: `d13f23b723b8a846827a245b89c10fc7d3f11612`.

New module SHA-256:

```text
6e6b870e7e82e3ce54c63be4f0eed1212dd5c0637091bb714411bfeb6b2a9ab2  rudin/Rudin/Research/PMA1043ProofAttack.lean
```

Full logs are committed under `evidence/t14-proof-attack/`; the command manifest records exact argv, absolute working directory, exit status, full-log location, and SHA-256. The originals remain under `/home/derekblair/lane-work/codex-rudin1043-proof2/evidence/`. Below, `lake` is `/home/derekblair/.elan/bin/lake`; Lean commands ran in `repo/rudin/`, and the Python commands in `repo/`.

| Exact command | Exit | Full retained log | SHA-256 |
| --- | ---: | --- | --- |
| `lake exe cache get` | 0 | `evidence/t14-proof-attack/cache-get.log` | `3a43c95124817f7cf0b604ecd44c589b4021b4f96e3efd53fe99d23b2b111dcb` |
| `lake build Rudin.Research.PMA1043ProofAttack` | 0 | `evidence/t14-proof-attack/proof-build-final.log` | `0c27956c62ed67e2050006ad4b1118ba0fbc55f87f826d9c6ba1fb873ea768ff` |
| `lake build` | 0 | `evidence/t14-proof-attack/full-build.log` | `58426c0a1abf304f4e7e6e4112964f6b9b4e37db5bb53876b3dc51eb1f12f3ae` |
| `env PYTHONDONTWRITEBYTECODE=1 python3 scripts/verify_ch10_integration.py` | 0 | `evidence/t14-proof-attack/integration-check.log` | `96f3f79e791515a21046abbeefecd864a00ff61d0690fb96bd937a8888c9827b` |
| `python3 evidence/t14-proof-attack/source-check.py` | 0 | `evidence/t14-proof-attack/source-check-final.log` | `c852bd0317e5c833553aedbbad7e18b96e3263cae6a06431cd870c576123295a` |
| `lake env lean --version` | 0 | `evidence/t14-proof-attack/toolchain.log` | `355a9a028f81641782d75d6e6b58dec70f29d2f61238a9e271690259d9bf5680` |

The explicit target completed 9071 jobs; the production build completed 9208 jobs. The module-owned audit checked **39 declarations**, including generated declarations. The printed dependencies below cover **all 31 explicit declarations**, including **all 20 proved lemmas/theorems**. Only `propext`, `Classical.choice`, and `Quot.sound` occur. The source scan found zero forbidden proof tokens.

The Chapter 10 integration verifier reported:

```text
PASS: 151 Chapter 10 modules, 25 probes, 51 contracts, 50 principals; 10.43 partial state retained.
PASS: 286 live project Lean sources scanned; zero forbidden proof tokens; all Chapter 10 modules reachable from default Rudin target.
PASS: 156 integration file hashes and 104 preserved main/pin hashes match.
```

The contract, compatibility module, manifest, Lake file, and toolchain pin are byte-identical to the prescribed base. Their hashes and the full declaration inventory are in `source-check-final.log`. The new research module is checked explicitly; the default build alone would not check it.

Development history is retained, including failures. The first baseline dependency build exited 1 after a missing `PartialContinuity.olean` during overlapping author builds. The prematurely started second build was terminated (signal 15; recorded process status −15), and a sequential retry succeeded. Intermediate target builds then exited 0. Author stdin experiments had ordinary elaboration failures before successful versions. `development-records.json` records every such command, exit status, full-log SHA-256 and absolute location, plus stdin snapshot hashes where applicable. These intermediate attempts are not substituted for the final module's successful build and complete audit.

### Complete printed dependency output

The following is the recorded audit and `#print axioms` output from `lake build Rudin.Research.PMA1043ProofAttack`. It is reproduced verbatim from the successful final build log and retained separately as `audit-output.log`.

```text
info: Rudin/Research/PMA1043ProofAttack.lean:485:0: Axiom audit coverage: Rudin.PMA.Chapter10.pma10_43_contract_iff_symmetricDerivativeLifting (module Rudin.Research.PMA1043ProofAttack); axioms used: [propext,
 Classical.choice,
 Quot.sound].
info: Rudin/Research/PMA1043ProofAttack.lean:485:0: Axiom audit coverage: Rudin.PMA.Chapter10.ProofAttack.lifting_extends_from_dense_submodule (module Rudin.Research.PMA1043ProofAttack); axioms used: [propext,
 Classical.choice,
 Quot.sound].
info: Rudin/Research/PMA1043ProofAttack.lean:485:0: Axiom audit module Rudin.Research.PMA1043ProofAttack: checked 39 declarations.
info: Rudin/Research/PMA1043ProofAttack.lean:485:0: Axiom audit for Rudin.Research.PMA1043ProofAttack: checked 39 declarations in 1 modules; axioms used: [propext,
 Classical.choice,
 Quot.sound]; no forbidden axioms.
info: Rudin/Research/PMA1043ProofAttack.lean:490:0: 'Rudin.PMA.Chapter10.curlMatrixSkew' depends on axioms: [propext, Classical.choice, Quot.sound]
info: Rudin/Research/PMA1043ProofAttack.lean:491:0: 'Rudin.PMA.Chapter10.CompatibleCurlRows' depends on axioms: [propext, Classical.choice, Quot.sound]
info: Rudin/Research/PMA1043ProofAttack.lean:492:0: 'Rudin.PMA.Chapter10.c2_vectorPotential_iff_compatibleCurlRows' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
info: Rudin/Research/PMA1043ProofAttack.lean:493:0: 'Rudin.PMA.Chapter10.CurlMatrixCompletion' depends on axioms: [propext, Classical.choice, Quot.sound]
info: Rudin/Research/PMA1043ProofAttack.lean:494:0: 'Rudin.PMA.Chapter10.pma10_43_contract_iff_curlMatrixCompletion' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
info: Rudin/Research/PMA1043ProofAttack.lean:495:0: 'Rudin.PMA.Chapter10.canonicalSkewRows' depends on axioms: [propext, Classical.choice, Quot.sound]
info: Rudin/Research/PMA1043ProofAttack.lean:496:0: 'Rudin.PMA.Chapter10.SymmetricRowsOn' depends on axioms: [propext, Classical.choice, Quot.sound]
info: Rudin/Research/PMA1043ProofAttack.lean:497:0: 'Rudin.PMA.Chapter10.curlMatrixSkew_canonical' depends on axioms: [propext, Classical.choice, Quot.sound]
info: Rudin/Research/PMA1043ProofAttack.lean:498:0: 'Rudin.PMA.Chapter10.contDiffOn_canonicalSkewRows' depends on axioms: [propext, Classical.choice, Quot.sound]
info: Rudin/Research/PMA1043ProofAttack.lean:499:0: 'Rudin.PMA.Chapter10.SymmetricCurlCorrection' depends on axioms: [propext, Classical.choice, Quot.sound]
info: Rudin/Research/PMA1043ProofAttack.lean:500:0: 'Rudin.PMA.Chapter10.compatibleCurlRows_iff_symmetricCurlCorrection' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
info: Rudin/Research/PMA1043ProofAttack.lean:501:0: 'Rudin.PMA.Chapter10.SymmetricCurlCompletion' depends on axioms: [propext, Classical.choice, Quot.sound]
info: Rudin/Research/PMA1043ProofAttack.lean:502:0: 'Rudin.PMA.Chapter10.pma10_43_contract_iff_symmetricCurlCompletion' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
info: Rudin/Research/PMA1043ProofAttack.lean:503:0: 'Rudin.PMA.Chapter10.vectorCoordinatePartial' depends on axioms: [propext, Classical.choice, Quot.sound]
info: Rudin/Research/PMA1043ProofAttack.lean:504:0: 'Rudin.PMA.Chapter10.curl_canonicalSkewRows_of_divergence_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
info: Rudin/Research/PMA1043ProofAttack.lean:505:0: 'Rudin.PMA.Chapter10.curl_canonical_add_eq_zero_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
info: Rudin/Research/PMA1043ProofAttack.lean:506:0: 'Rudin.PMA.Chapter10.SymmetricCurlSystem' depends on axioms: [propext, Classical.choice, Quot.sound]
info: Rudin/Research/PMA1043ProofAttack.lean:507:0: 'Rudin.PMA.Chapter10.symmetricCurlCorrection_iff_system' depends on axioms: [propext, Classical.choice, Quot.sound]
info: Rudin/Research/PMA1043ProofAttack.lean:508:0: 'Rudin.PMA.Chapter10.SymmetricDerivativeLifting' depends on axioms: [propext, Classical.choice, Quot.sound]
info: Rudin/Research/PMA1043ProofAttack.lean:509:0: 'Rudin.PMA.Chapter10.pma10_43_contract_iff_symmetricDerivativeLifting' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
info: Rudin/Research/PMA1043ProofAttack.lean:510:0: 'Rudin.PMA.Chapter10.ProofAttack.allGaugeCost' depends on axioms: [propext, Classical.choice, Quot.sound]
info: Rudin/Research/PMA1043ProofAttack.lean:511:0: 'Rudin.PMA.Chapter10.ProofAttack.allGaugeCost_le_norm' depends on axioms: [propext, Classical.choice, Quot.sound]
info: Rudin/Research/PMA1043ProofAttack.lean:512:0: 'Rudin.PMA.Chapter10.ProofAttack.allGaugeCost_eq_of_image_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
info: Rudin/Research/PMA1043ProofAttack.lean:513:0: 'Rudin.PMA.Chapter10.ProofAttack.exists_same_image_norm_lt_cost_add' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
info: Rudin/Research/PMA1043ProofAttack.lean:514:0: 'Rudin.PMA.Chapter10.ProofAttack.allGaugeCost_eq_sInf' depends on axioms: [propext, Classical.choice, Quot.sound]
info: Rudin/Research/PMA1043ProofAttack.lean:515:0: 'Rudin.PMA.Chapter10.ProofAttack.allGaugeCost_bound_iff_representative_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
info: Rudin/Research/PMA1043ProofAttack.lean:516:0: 'Rudin.PMA.Chapter10.ProofAttack.surjective_of_denseRange_allGaugeCost_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
info: Rudin/Research/PMA1043ProofAttack.lean:517:0: 'Rudin.PMA.Chapter10.ProofAttack.surjective_iff_denseRange_allGaugeCost_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
info: Rudin/Research/PMA1043ProofAttack.lean:518:0: 'Rudin.PMA.Chapter10.ProofAttack.lifting_extends_from_dense_submodule' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
info: Rudin/Research/PMA1043ProofAttack.lean:519:0: 'Rudin.PMA.Chapter10.ProofAttack.surjective_of_dense_submodule_bounded_lifts' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
info: Rudin/Research/PMA1043ProofAttack.lean:520:0: 'Rudin.PMA.Chapter10.ProofAttack.surjective_iff_dense_submodule_bounded_lifts' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

## Delivery and review status

The delivery is a draft PR stacked on draft PR #27's `thm-1043-final-clause` branch, with this report and recorded evidence. It does not close #14: the printed clause has not been proved. No programme review has run on this work; all build, source, and dependency checks above are author checks. The author lane has neither reviewed nor merged its own work.
