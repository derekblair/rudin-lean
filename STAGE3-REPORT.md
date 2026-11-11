# Stage 3 Report — Rudin PMA Exercise 10.43 (`rudin29-stage3-harmonic`)

- **Date:** 2026-11-10
- **Branch:** `rudin29-stage3-harmonic` (branched from PR #30 head `af3f4b9502b8347606722d50e0d619fce2d338b2`)
- **New Lean module:** `rudin/Rudin/PMA/Chapter10/FtildeHarmonic.lean` (1,734 lines; zero `sorry`/`admit`/`native_decide`; all 207 declarations audited on `[propext, Classical.choice, Quot.sound]`)
- **Stage 1/2 files:** untouched (`FtildeDisproofStatement.lean` still has its sole `sorry` at line 466)

---

## 1. Executive Verdict (Merits Failure of Clause 3)

Per the Stage 3 brief (`BRIEF.md` lines 87–89 and 101–102):

> *"If this clause fails on the merits (not on effort), stop and report the failure with the exact blocking lemma — do not quietly pivot to the proof-attack direction or re-scope to '10.43 in general'."*

**Clause 3 of `ftilde_witness` (`¬ SymmetricCurlSystem ftildeBall ftildeField`) is FALSE on the merits.**

Specifically, for the exact candidate field `ftildeField` on `ftildeBall = Metric.ball 0 1` defined in `rudin/Rudin/PMA/Chapter10/FtildeDisproofStatement.lean`:

1. **Clauses 1 and 2 of `ftilde_witness` are TRUE** (`contDiffOn_ftildeField`, line 1647; `divergence_ftildeField_eq_zero`, line 1653).
2. **`ftildeField` admits an explicit global closed-form $C^2$ vector potential `ftildePotentialG` on `ftildeBall`** (`contDiffOn_ftildePotentialG`, line 1338; `curl_ftildePotentialG_eq_ftildeField`, line 1597; `exists_c2_vectorPotential_ftilde`, line 1642).
3. **Consequently, `SymmetricCurlSystem ftildeBall ftildeField` is TRUE** (`symmetricCurlSystem_ftilde`, line 1680), **refuting Clause 3** (`not_ftilde_clause3`, line 1687) **and the `ftilde_witness` conjunction** (`not_ftilde_witness_goal`, line 1693).

All of the above—together with both the true Fourier symbol identity in Lemma L6 and the exact physical-space counterexample to Step G6's gauge-invariance transfer—are kernel-verified in `rudin/Rudin/PMA/Chapter10/FtildeHarmonic.lean` and replayed independently via `lake env leanchecker`. No re-scoping to Exercise 10.43 in general was performed.

---

## 2. Exact Blocking Step in the #29 Hand-Analysis Chain (`G1–G6` / `L1–L10`)

In tracking issue #29 (comment `6548746156`, formalized as the `L1–L10` roadmap), the disproof plan argued:

- **Biot–Savart branch (`L7`–`L9`):** For the compactly cut-off Biot–Savart representative $A_0$ with trace-free symmetric gradient $S^{(0)} = \operatorname{sym}_0(DA_0)$, the Calderón–Zygmund principal part produces
  $$\partial_k S^{(0)}_{ij}(x) = \text{ftildeC}_{ijk}\,\log|\log\|x\|| + \tilde{C}_{0,ijk} + o(1) \quad (x \to 0),$$
  where the fully symmetric rank-3 tensor $\text{ftildeC}_{ijk}$ (`ftildeC` in `FtildeDisproofStatement.lean`) is nonzero (`ftildePhi_ne_zero`). **This Biot–Savart blow-up is genuine.**
- **Lemma `L6` (pointwise Fourier symbol orthogonality):** At each fixed frequency $\xi \in \mathbb{R}^3$, every symmetrized transverse Biot–Savart symbol $\operatorname{Sym}(\xi \otimes \xi \otimes v)$ with $\xi \cdot v = 0$ is Frobenius-orthogonal to every symmetrized trace-free Hessian gauge symbol $c\,\xi^{\otimes 3} + d\,\operatorname{Sym}(\delta \otimes \xi)$. **This algebraic identity is TRUE** and proved as `l6_pointwise_fourier_orthogonality` (line 645).
- **Exact blocking step — Step `G6` (`L6` $\Rightarrow$ `L10` physical-space gauge-invariance transfer):** Step `G6` inferred from `L6` that no $C^2(\text{ftildeBall})$ scalar gauge $\varphi$ (coming from a vector-potential gauge change $A = A_0 + \nabla\varphi$ with $\operatorname{sym}_0(DA) = S^{(0)} + \operatorname{Hess}_0\varphi$) can cancel the $\text{ftildeC}_{ijk}\log|\log\|x\||$ blow-up of $\operatorname{Sym}(\partial S^{(0)})(x)$ as $x \to 0$. **This transfer is FALSE.**

### Why Step `G6` Fails Mathematically

1. **Plancherel/$L^2$ orthogonality vs. pointwise $L^\infty$ blow-up:** In `L6`, the two orthogonal subspaces of $\operatorname{Sym}^3(\mathbb{R}^3)$ depend on the unit frequency direction $\xi/\|\xi\|$. Integrating over $\xi \in \mathbb{R}^3$ via Plancherel therefore yields **global $L^2(\mathbb{R}^3)$ orthogonality**—not pointwise orthogonality at $x \to 0$, and not orthogonality of local $C^2(B_1)$ fields without boundary/decay conditions. Because $\log|\log\|x\|| \in L^2(B_1) \setminus L^\infty(B_1)$, a singular profile $\text{ftildeC}\log|\log\|x\||$ has finite $L^2$ norm near $0$ and can split into two $L^2$-orthogonal pieces whose $\log|\log\|x\||$ singularities cancel pointwise.
2. **Exact harmonicity of the cubic tensor `ftildeC` (`Section 2`):** The rank-3 symmetric tensor `ftildeC` is the exact constant third-derivative tensor $\nabla^3 P$ of the **harmonic** homogeneous cubic polynomial
   $$P(x) = \frac{-4x_0^3 + 16x_0 x_1^2 - 4x_0 x_2^2}{105}$$
   (`ftildeCubicGaugePoly`, line 661), which satisfies $\Delta P = 0$ (`laplacian_ftildeCubicGaugePoly`, line 664) and $\partial_k\partial_j\partial_i P(x) = \text{ftildeC}_{ijk}$ (`thirdPartial_ftildeCubicGaugePoly_eq_ftildeC`, line 672).
3. **Explicit $C^2(B_1)$ local gauge cancelling the $\log|\log\|x\||$ blow-up (`Section 2`):** Defining
   $$\varphi_{\mathrm{loc}}(x) = -P(x)\log|\log\|x\|| \quad (x \neq 0), \qquad \varphi_{\mathrm{loc}}(0) = 0$$
   (`ftildeLocalGauge`, line 757), the scale-critical $O(\|x\|^3 \log|\log\|x\||)$ decay gives $\varphi_{\mathrm{loc}} \in C^2(\text{ftildeBall})$ (`contDiffOn_two_ftildeLocalGauge`, line 944), while $\Delta P = 0$ kills the $\log|\log\|x\||$ term in $\Delta\varphi_{\mathrm{loc}}$ so that every third partial derivative of its trace-free Hessian satisfies
   $$\partial_k\big(\operatorname{Hess}_0 \varphi_{\mathrm{loc}}\big)_{ij}(x) + \text{ftildeC}_{ijk}\log|\log\|x\|| \longrightarrow 0 \quad (x \to 0,\; x \neq 0)$$
   (`tendsto_thirdPartial_traceFreeHessian_ftildeLocalGauge`, line 1060). Adding $\nabla\varphi_{\mathrm{loc}}$ to $A_0$ cancels the logarithmic blow-up of $\partial S^{(0)}$ at the origin.
4. **Global closed-form $C^2(B_1)$ vector potential (`Section 3`):** Bypassing Biot–Savart cutoffs altogether via exact spherical-harmonic Hodge inversion on $S^2$ (expanding the degree-7 numerators `ftildeV7` into spherical harmonics of degrees $\ell \in \{1,3,5,7\}$, solving $-\Delta_{S^2}\alpha_6 = r^7\,\hat{x}\cdot V$ and $-\Delta_{S^2}\beta_5 = r^6\,\hat{x}\cdot(\nabla\times V)$), `ftildePotentialG` (line 1322) takes the form
   $$G_i(x) = \psi(\|x\|)\frac{A_{6,i}(x)}{\|x\|^4} + \frac{J(\|x\|)}{\|x\|^3}\frac{B_{6,i}(x)}{\|x\|^4} \quad (x \neq 0), \qquad G(0) = 0,$$
   for explicit homogeneous degree-6 polynomials $A_{6,i}, B_{6,i}$ (`ftildeA6`, `ftildeB6`, lines 1318–1319). Because $\psi(r) = (-1/\log r) = o(1)$ and $0 \le J(r)/r^3 \le \psi(r)^2 = o(1)$ as $r \to 0^+$, both branches have $o(\|x\|^2)$ control with $G(0) = 0$, $DG(0) = 0$, $D^2 G(0) = 0$, yielding $G \in C^2(\text{ftildeBall})$ and $\nabla \times G = \text{ftildeField}$ everywhere on `ftildeBall`.

---

## 3. Inventory of Proved Declarations in `FtildeHarmonic.lean`

File: `rudin/Rudin/PMA/Chapter10/FtildeHarmonic.lean` (1,734 lines, 207 checked declarations in total).

| Section | Declaration | Line | Statement Summary |
| --- | --- | --- | --- |
| 1 | `evalPoly3` / `derivPoly3` | 55 / 59 | Formal 3-variable polynomial evaluator and symbolic partial derivative |
| 1 | `coordinatePartial_evalPoly3` | 163 | `coordinatePartial (evalPoly3 L) x j = evalPoly3 (derivPoly3 j L) x` |
| 1 | `coordinatePartial_homog_smooth` | 194 | Partial derivative of smooth degree-$(k+1)$ homogeneous function is degree-$k$ homogeneous |
| 1 | `radialHomogTerm` | 284 | $h(\|x\|)\,P(x)/\|x\|^{2m}$ for $x \neq 0$, extended by $0$ at $x = 0$ |
| 1 | `hasFDerivAt_radialHomogTerm_ne_zero` | 298 | Differentiability and closed-form partial derivative on `ftildeBall \ {0}` |
| 1 | `hasFDerivAt_radialHomogTerm_zero` | 353 | `HasFDerivAt (radialHomogTerm m h P) 0 0` under $h(r)r^{d-(2m+1)} \to 0$ |
| 1 | `contDiffOn_one_radialHomogTerm` | 467 | `ContDiffOn ℝ 1 (radialHomogTerm m h P) ftildeBall` |
| 1 | `contDiffOn_two_radialHomogTerm6` | 564 | `ContDiffOn ℝ 2 (radialHomogTerm 2 h P) ftildeBall` for degree-6 homogeneous $P$ |
| 2 | `l6_pointwise_fourier_orthogonality` | 645 | **L6 (true):** $\langle \operatorname{Sym}(\xi\otimes\xi\otimes v),\, c\xi^{\otimes 3} + d\operatorname{Sym}(\delta\otimes\xi)\rangle_F = 0$ when $\xi\cdot v = 0$ |
| 2 | `ftildeCubicGaugePoly` | 661 | Harmonic cubic $P(x) = (-4x_0^3 + 16x_0 x_1^2 - 4x_0 x_2^2)/105$ |
| 2 | `laplacian_ftildeCubicGaugePoly` | 664 | $\sum_{i} \partial_i\partial_i P(x) = 0$ |
| 2 | `thirdPartial_ftildeCubicGaugePoly_eq_ftildeC` | 672 | $\partial_k\partial_j\partial_i P(x) = \text{ftildeC}_{ijk}$ for all $i,j,k \in \operatorname{Fin} 3$ |
| 2 | `ftildeLogAbsLog` / `ftildeLocalGauge` | 688 / 757 | $\log|\log r|$ and $\varphi_{\mathrm{loc}}(x) = -P(x)\log|\log\|x\||$ |
| 2 | `traceFreeHessian` | 768 | $(\operatorname{Hess}_0\varphi)_{ij} = \partial_j\partial_i\varphi - \frac{1}{3}\delta_{ij}\Delta\varphi$ |
| 2 | `contDiffOn_two_ftildeLocalGauge` | 944 | `ContDiffOn ℝ 2 ftildeLocalGauge ftildeBall` |
| 2 | `tendsto_thirdPartial_traceFreeHessian_ftildeLocalGauge` | 1060 | **Refutes Step G6:** $\partial_k(\operatorname{Hess}_0\varphi_{\mathrm{loc}})_{ij}(x) + \text{ftildeC}_{ijk}\log|\log\|x\|| \to 0$ along `𝓝[≠] 0` |
| 3 | `ftildeJOverCube` / `ftildeJOverCube_bounds` | 1196 / 1219 | $J(r)/r^3$ and $0 \le J(r)/r^3 \le \psi(r)^2$ on $(0,1)$ |
| 3 | `ftildeA6` / `ftildeB6` / `ftildePotentialG` | 1318–1322 | Closed-form degree-6 polynomial numerators and global vector potential $G$ |
| 3 | `contDiffOn_ftildePotentialG` | 1338 | `ContDiffOn ℝ 2 ftildePotentialG ftildeBall` |
| 3 | `ftildeQ_eq_sum_mul_ftildeV` | 1414 | Euler's homogeneous theorem reducing `ftildeQ θ = ∑ n, θ n * ftildeV θ n` |
| 3 | `curl_ftildePotentialG_eq_ftildeField` | 1597 | `EqOn (curl ftildePotentialG) ftildeField ftildeBall` |
| 3 | `exists_c2_vectorPotential_ftilde` | 1642 | `∃ G, ContDiffOn ℝ 2 G ftildeBall ∧ EqOn (curl G) ftildeField ftildeBall` |
| 3 | `contDiffOn_ftildeField` | 1647 | Clause 1 holds: `ContDiffOn ℝ 1 ftildeField ftildeBall` |
| 3 | `divergence_ftildeField_eq_zero` | 1653 | Clause 2 holds: `EqOn (divergence ftildeField) 0 ftildeBall` |
| 3 | `symmetricCurlSystem_ftilde` | 1680 | `SymmetricCurlSystem ftildeBall ftildeField` holds |
| 3 | `not_ftilde_clause3` | 1687 | `¬ (¬ SymmetricCurlSystem ftildeBall ftildeField)` |
| 3 | `not_ftilde_witness_goal` | 1693 | Negation of the full 5-clause `ftilde_witness` conjunction |
| 4 | `checkModuleAxioms` + `#print axioms` | 1705–1733 | Module-wide axiom audit across all 207 declarations |

---

## 4. Build Log, Independent `leanchecker` Replay, and Axiom Audit

### 4.1 `lake build Rudin.PMA.Chapter10.FtildeHarmonic` (from `rudin/`, golden Mathlib cache symlinked)

Command:
```bash
cd /home/derekblair/projects/rudin/rudin-lean/rudin && PATH="$HOME/.elan/bin:$PATH" lake build Rudin.PMA.Chapter10.FtildeHarmonic
```

Output excerpt (exit code `0`, zero warnings in `FtildeHarmonic.lean`):
```text
info: Rudin/PMA/Chapter10/FtildeHarmonic.lean:1705:0: Axiom audit coverage: Rudin.PMA.Chapter10.contDiffOn_ftildeField (module Rudin.PMA.Chapter10.FtildeHarmonic); axioms used: [propext,
 Classical.choice,
 Quot.sound].
info: Rudin/PMA/Chapter10/FtildeHarmonic.lean:1705:0: Axiom audit coverage: Rudin.PMA.Chapter10.contDiffOn_ftildePotentialG (module Rudin.PMA.Chapter10.FtildeHarmonic); axioms used: [propext,
 Classical.choice,
 Quot.sound].
info: Rudin/PMA/Chapter10/FtildeHarmonic.lean:1705:0: Axiom audit coverage: Rudin.PMA.Chapter10.contDiffOn_two_ftildeLocalGauge (module Rudin.PMA.Chapter10.FtildeHarmonic); axioms used: [propext,
 Classical.choice,
 Quot.sound].
info: Rudin/PMA/Chapter10/FtildeHarmonic.lean:1705:0: Axiom audit coverage: Rudin.PMA.Chapter10.curl_ftildePotentialG_eq_ftildeField (module Rudin.PMA.Chapter10.FtildeHarmonic); axioms used: [propext,
 Classical.choice,
 Quot.sound].
info: Rudin/PMA/Chapter10/FtildeHarmonic.lean:1705:0: Axiom audit coverage: Rudin.PMA.Chapter10.divergence_ftildeField_eq_zero (module Rudin.PMA.Chapter10.FtildeHarmonic); axioms used: [propext,
 Classical.choice,
 Quot.sound].
info: Rudin/PMA/Chapter10/FtildeHarmonic.lean:1705:0: Axiom audit coverage: Rudin.PMA.Chapter10.exists_c2_vectorPotential_ftilde (module Rudin.PMA.Chapter10.FtildeHarmonic); axioms used: [propext,
 Classical.choice,
 Quot.sound].
info: Rudin/PMA/Chapter10/FtildeHarmonic.lean:1705:0: Axiom audit coverage: Rudin.PMA.Chapter10.l6_pointwise_fourier_orthogonality (module Rudin.PMA.Chapter10.FtildeHarmonic); axioms used: [propext,
 Classical.choice,
 Quot.sound].
info: Rudin/PMA/Chapter10/FtildeHarmonic.lean:1705:0: Axiom audit coverage: Rudin.PMA.Chapter10.laplacian_ftildeCubicGaugePoly (module Rudin.PMA.Chapter10.FtildeHarmonic); axioms used: [propext,
 Classical.choice,
 Quot.sound].
info: Rudin/PMA/Chapter10/FtildeHarmonic.lean:1705:0: Axiom audit coverage: Rudin.PMA.Chapter10.not_ftilde_clause3 (module Rudin.PMA.Chapter10.FtildeHarmonic); axioms used: [propext,
 Classical.choice,
 Quot.sound].
info: Rudin/PMA/Chapter10/FtildeHarmonic.lean:1705:0: Axiom audit coverage: Rudin.PMA.Chapter10.not_ftilde_witness_goal (module Rudin.PMA.Chapter10.FtildeHarmonic); axioms used: [propext,
 Classical.choice,
 Quot.sound].
info: Rudin/PMA/Chapter10/FtildeHarmonic.lean:1705:0: Axiom audit coverage: Rudin.PMA.Chapter10.symmetricCurlSystem_ftilde (module Rudin.PMA.Chapter10.FtildeHarmonic); axioms used: [propext,
 Classical.choice,
 Quot.sound].
info: Rudin/PMA/Chapter10/FtildeHarmonic.lean:1705:0: Axiom audit coverage: Rudin.PMA.Chapter10.tendsto_thirdPartial_traceFreeHessian_ftildeLocalGauge (module Rudin.PMA.Chapter10.FtildeHarmonic); axioms used: [propext,
 Classical.choice,
 Quot.sound].
info: Rudin/PMA/Chapter10/FtildeHarmonic.lean:1705:0: Axiom audit coverage: Rudin.PMA.Chapter10.thirdPartial_ftildeCubicGaugePoly_eq_ftildeC (module Rudin.PMA.Chapter10.FtildeHarmonic); axioms used: [propext,
 Classical.choice,
 Quot.sound].
info: Rudin/PMA/Chapter10/FtildeHarmonic.lean:1705:0: Axiom audit module Rudin.PMA.Chapter10.FtildeHarmonic: checked 207 declarations.
info: Rudin/PMA/Chapter10/FtildeHarmonic.lean:1705:0: Axiom audit for Rudin.PMA.Chapter10.FtildeHarmonic: checked 207 declarations in 1 modules; axioms used: [propext,
 Classical.choice,
 Quot.sound]; no forbidden axioms.
info: Rudin/PMA/Chapter10/FtildeHarmonic.lean:1721:0: 'Rudin.PMA.Chapter10.l6_pointwise_fourier_orthogonality' depends on axioms: [propext, Classical.choice, Quot.sound]
info: Rudin/PMA/Chapter10/FtildeHarmonic.lean:1722:0: 'Rudin.PMA.Chapter10.laplacian_ftildeCubicGaugePoly' depends on axioms: [propext, Classical.choice, Quot.sound]
info: Rudin/PMA/Chapter10/FtildeHarmonic.lean:1723:0: 'Rudin.PMA.Chapter10.thirdPartial_ftildeCubicGaugePoly_eq_ftildeC' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
info: Rudin/PMA/Chapter10/FtildeHarmonic.lean:1724:0: 'Rudin.PMA.Chapter10.contDiffOn_two_ftildeLocalGauge' depends on axioms: [propext, Classical.choice, Quot.sound]
info: Rudin/PMA/Chapter10/FtildeHarmonic.lean:1725:0: 'Rudin.PMA.Chapter10.tendsto_thirdPartial_traceFreeHessian_ftildeLocalGauge' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
info: Rudin/PMA/Chapter10/FtildeHarmonic.lean:1726:0: 'Rudin.PMA.Chapter10.contDiffOn_ftildePotentialG' depends on axioms: [propext, Classical.choice, Quot.sound]
info: Rudin/PMA/Chapter10/FtildeHarmonic.lean:1727:0: 'Rudin.PMA.Chapter10.curl_ftildePotentialG_eq_ftildeField' depends on axioms: [propext, Classical.choice, Quot.sound]
info: Rudin/PMA/Chapter10/FtildeHarmonic.lean:1728:0: 'Rudin.PMA.Chapter10.exists_c2_vectorPotential_ftilde' depends on axioms: [propext, Classical.choice, Quot.sound]
info: Rudin/PMA/Chapter10/FtildeHarmonic.lean:1729:0: 'Rudin.PMA.Chapter10.contDiffOn_ftildeField' depends on axioms: [propext, Classical.choice, Quot.sound]
info: Rudin/PMA/Chapter10/FtildeHarmonic.lean:1730:0: 'Rudin.PMA.Chapter10.divergence_ftildeField_eq_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
info: Rudin/PMA/Chapter10/FtildeHarmonic.lean:1731:0: 'Rudin.PMA.Chapter10.symmetricCurlSystem_ftilde' depends on axioms: [propext, Classical.choice, Quot.sound]
info: Rudin/PMA/Chapter10/FtildeHarmonic.lean:1732:0: 'Rudin.PMA.Chapter10.not_ftilde_clause3' depends on axioms: [propext, Classical.choice, Quot.sound]
info: Rudin/PMA/Chapter10/FtildeHarmonic.lean:1733:0: 'Rudin.PMA.Chapter10.not_ftilde_witness_goal' depends on axioms: [propext, Classical.choice, Quot.sound]
Build completed successfully (9073 jobs).
```

### 4.2 Independent Kernel Replay (`lake env leanchecker` from module clone)

Command:
```bash
cd /home/derekblair/projects/rudin/rudin-lean/rudin && PATH="$HOME/.elan/bin:$PATH" lake env leanchecker -v Rudin.PMA.Chapter10.FtildeHarmonic
```

Output (exit code `0`):
```text
replaying Rudin.PMA.Chapter10.FtildeHarmonic
```

### 4.3 Forbidden-Token Scan

Checked `rudin/Rudin/PMA/Chapter10/FtildeHarmonic.lean` for `sorry`, `admit`, `axiom` declarations, `native_decide`, `bv_decide`, `unsafe`, `implemented_by`, `extern`: zero occurrences.
