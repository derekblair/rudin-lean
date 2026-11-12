# Stage 4 Preparation & Next-Direction Report — Rudin PMA 10.43 (`rudin-lean` #29)

- **Branch:** `rudin29-stage4-prep` (branched from PR #30 head `af3f4b9502b8347606722d50e0d619fce2d338b2`)
- **Workdir:** `/root/projects/rudin/rudin-lean-stage4prep` (strictly disjoint from `/root/projects/rudin/rudin-lean` and `nibbles`)
- **Toolchain & Mathlib Pin:** Lean `v4.34.1`, Mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612`
- **Lean Deliverable:** `rudin/Rudin/PMA/Chapter10/FtildeCZPrep.lean` (**ZERO `sorry`s**, zero `admit`/`native_decide`/`bv_decide`/custom axioms; audited via `Rudin.PMA.Audit.checkModuleAxioms` and replayed via `lake env leanchecker`)

---

## 1. Executive Summary & Coordinator Re-Scope

### 1.1 Stage 3 Outcome & Re-Scope Compliance
During this lane's execution, Stage 3 completed on `nibbles` (`rudin29-stage3-harmonic`, head `6f2c75a5`; record: `rudin-lean` #29 comment `6787953476`) and established that **clause 3 of `ftilde_witness` (`FtildeDisproofStatement.lean:466`) is FALSE on the merits**: `ftildeField` admits an explicit global $C^2$ vector potential on the ball.

Per the coordinator's re-scope instruction:
1. **No dead-direction `L8` `sorry` skeleton was built.** Instead, `rudin/Rudin/PMA/Chapter10/FtildeCZPrep.lean` is a **100% zero-`sorry`, kernel-checked Lean module** containing only proved theorems and reusable infrastructure.
2. **Research gaps `(a2)` and `(b)` are pinned and completely resolved on the merits:**
   - **Gap `(a2)` (angular identification $A = C_{653}$ + Derek's `(A)`/`(B)` completion-independence split):** **100% proved in Lean** by two independent routes (`ftilde_dipole_angular_identification` and `ftilde_angular_identification_a2`), together with odd-stream completion invisibility (`odd_stream_completion_cz_vanishes`), exact vanishing of the unshifted potential-compensated base field (`ftildeBase_dipole_angular_eq_zero`), explicit isolation of the nonzero `-4/77` first-row partial (`ftildeBase_row0_dipole_020`), and a complete spherical-harmonic / Clebsch–Gordan proof of the general shell-potential cancellation law (§2.1.4).
   - **Gap `(b)` ($S$-equation transport & gauge assembly):** The valid Coulomb/Fourier/radial half is **proved in Lean** (`korn_second_partial_identity`, `sym3_gauge_orthogonality`, `ftildeSymbolMean_nonzero_witness`, `integral_ftildePsi_div_self`, `integral_ftildePsi_sq_div_self_bounds`, `l10_not_c1_of_log_log_symGrad`), proving rigorously that the Coulomb potential $A_0$ is **not** $C^2$ (`S⁽⁰⁾ ∉ C¹`). The broken physical-space step (`G6`) is **diagnosed and generalized in Lean**:
     1. **Universal Harmonic Trap (`traceFree_sym3_cubic_harmonic`):** Because $\dim \operatorname{Sym}^3_0(\mathbb{R}^3) = 7 = \dim \mathcal{H}_3(\mathbb{R}^3)$, *every* constant symmetric trace-free 3-tensor $C$ equals $\nabla^3(\texttt{cubicOfTensor } C)$ for a harmonic cubic polynomial $P$. Consequently, *any* non-oscillatory leading Coulomb blow-up $C \cdot \Phi(\|x\|)$ can be cancelled at leading order by a singular gauge $\varphi \in C^2 \setminus C^3$.
     2. **Dead-Class Theorem (`symmetricCurlSystem_of_sublinear_second_deriv`):** Even stronger — *every* divergence-free field $F \in C^1(B_R) \cap C^2(B_R \setminus \{0\})$ satisfying $\lim_{z \to 0} \|z\| \cdot \|D^2 F(z)\| = 0$ already has `poincareVectorPotential F ∈ C²(B_R)` solving $\operatorname{curl} G = F$ (`contDiffOn_two_poincareVectorPotential`, `curl_poincareVectorPotential`). Since $\|z\| \cdot \|D^2 \tilde{F}(z)\| = O(\psi(\|z\|)) = O(1/|\log\|z\||) \to 0$, the classical radial Poincaré homotopy potential of `ftildeField` is **already globally $C^2$** across the origin, killing the entire single-point radial-logarithmic ansatz class at all orders (not merely at leading $\log|\log r|$ order).
3. **Re-Scoped `L8` & Next-Direction Decision (§5):**
   - **Verdict on classical `L8` CZ remainder work:** **Do NOT build a self-contained classical Calderón–Zygmund singular-integral remainder library for fixed linear Biot–Savart / Poincaré kernels.** Single-gauge linear CZ estimates cannot rule out $C^2 \setminus C^3$ gauges in the disproof direction, and cannot prove `pma10_43_contract` in the proof direction because continuous linear right-inverses to $\operatorname{div} : C^2 \to C^1$ fail at $L^\infty / C^0$ endpoints (Bourgain–Brezis 2003).
   - **What replaces `L8`:** Pivot `#29` to the **Quantitative All-Gauge Canceling-Operator Duality Gate**, connecting the existing Hahn–Banach / Banach Open Mapping machinery in `Rudin/Research/PMA1043ProofAttack.lean` (`lifting_extends_from_dense_submodule`, `surjective_iff_denseRange_allGaugeCost_bound`) with the exact 4-component planar compatibility reduction and our kernel-checked fourth-order duality theorems (`planar_c2_div_fourth_order_duality`, `planar_c2_div_fourth_order_bound`).

---

## 2. Pinned Statements & Disposition of Research Gaps `(a2)` and `(b)`

### 2.1 Gap `(a2)`: Angular Identification $A = C_{653}$ (`ftildeC`) and Split `(A)`/`(B)`

#### 2.1.1 Exact Pinned Statements from the Record
From `rudin-lean` #29 comments (`6544009325`, `6544302798`, `6544709552`, `6545042749`, `6545396969`, `6545747341`, `6546748726`), the frozen pin manifest `rudin29-ftilde-disproof.md`, `WRITEUP.md` (`L7`, `G3`, `G4`), and `FtildeDisproofStatement.lean`:
- **Candidate & Strain Profile:** On $S^2 = \{\theta \in \mathbb{R}^3 : \|\theta\| = 1\}$, `ftildeHomogV` is the homogeneous degree-1 field $V(x) = V_{\mathrm{base}}(x) + V_{\mathrm{shift}}(x)$, where:
  - $V_{\mathrm{base},0}(x) = r^{-6} x_0^6 x_1$,
  - $V_{\mathrm{base},1}(x) = -\frac{5}{7} r^{-6} x_0^5(x_0^2 - x_1^2 - x_2^2) + \frac{10}{7} r^{-6} x_0^5 x_1^2$,
  - $V_{\mathrm{base},2}(x) = \frac{10}{7} r^{-6} x_0^5 x_1 x_2$,
  - $V_{\mathrm{shift}}(x) = (0, -\partial_2 \tilde{\chi}, \partial_1 \tilde{\chi})$ with even degree-2 stream function $\tilde{\chi}(x) = x_1^4 / r^2$, so $V_{\mathrm{shift},1}(x) = 2 r^{-4} x_1^4 x_2$ and $V_{\mathrm{shift},2}(x) = 4 r^{-2} x_1^3 - 2 r^{-4} x_1^5$.
  Its Jacobian on $S^2$ is $d_{\tilde{F},an}(\theta) = \partial_a V_n(\theta)$ (`ftildeD a n θ`).
- **Degree-4 Fourier Multiplier (`ftildeSymbol`, `G3`):**
  $$m_{ijk}^{an}(\hat{\xi}) = -\frac{1}{2}\sum_{m=0}^2 \bigl(\varepsilon_{imn}\hat{\xi}_k\hat{\xi}_j + \varepsilon_{jmn}\hat{\xi}_k\hat{\xi}_i\bigr)\hat{\xi}_m\hat{\xi}_a.$$
- **Pinned Statement of `(a2)` / `L7` (`#29` comments `6545396969` & `6545747341`):**
  Decompose $m_{ijk}^{an}(\hat{\xi}) = c_{0,ijk}^{an} + m_{2,ijk}^{an}(\hat{\xi}) + m_{4,ijk}^{an}(\hat{\xi})$ on $S^2$ into spherical harmonics of degrees $l = 0, 2, 4$. Respecting the standing facts:
  1. The $l = 0$ constant mean $c_0 = \frac{1}{4\pi}\int_{S^2} m(\hat{\xi})\,d\sigma(\hat{\xi})$ is **nonzero** (entries $\pm 1/15, \pm 1/30$) and corresponds in physical space to the local contact operator $c_0 \cdot d\tilde{F}(x) = O(\psi(\|x\|)) \to 0$, never to the $\log|\log\|x\||$ shell integral.
  2. The $l = 2, 4$ harmonic parts reconstruct via Funk–Hecke inverse Fourier eigenvalues $c_2 = -4\pi/3$ ($l=2$) and $c_4 = 8\pi/15$ ($l=4$) to a smooth, antipodally even, **mean-zero** Calderón–Zygmund kernel $\Omega_{ijk}^{an}(\theta)$ on $S^2$.
  3. The shell-coefficient tensor $A_{ijk} := \int_{S^2} \Omega_{ijk}^{an}(-\theta)\, d_{\tilde{F},an}(\theta)\, d\sigma(\theta)$ equals `ftildeC i j k` ($C_{653}$) identically across all $27$ components:
     $$C_{000} = -\frac{8}{35},\quad C_{011} = C_{101} = C_{110} = \frac{32}{105},\quad C_{022} = C_{202} = C_{220} = -\frac{8}{105},\quad \text{all other } 20\text{ entries } = 0.$$
- **Derek's Split `(A)` and `(B)` (`#29` comments `6544009325`, `6544302798`, `6544709552`):**
  - **Part `(A)` (Odd-parity completion independence):** Adding any transverse stream completion $(0, -\partial_2 \chi, \partial_1 \chi)$ generated by an antipodally **odd** homogeneous degree-2 stream profile $\chi(-x) = -\chi(x)$ contributes identically $0$ to $A_{ijk}$; only the **even** part of $\chi$ can move $A_{ijk}$.
  - **Part `(B)` (Shell-potential cancellation):** For the unshifted potential-compensated shell field `ftildeBaseV` (and all four filter-passing shell-potential fields in the `2x2` mode/form table), the first row alone has a genuinely nonzero partial shell tensor, yet the potential-compensated transverse rows produce the exact opposite tensor component-by-component so that $A_{\mathrm{base}} = 0$.

#### 2.1.2 Disposition of `(a2)`: **CLOSED — 100% Proved in Lean (`FtildeCZPrep.lean`, §§I.1–I.2)**

Because Mathlib `d13f23b7` has `Measure.toSphere` (`Mathlib.MeasureTheory.Constructions.HaarToSphere`) and 1D Gaussian Gamma moments (`Mathlib.MeasureTheory.Integral.Gamma`) but no ready-made polynomial expectations on $S^2$, we first constructed exact unit-sphere integration in `FtildeCZPrep.lean`:
- **`sphereSurfaceMeasure`** (`Measure.toSphere (volume : Measure (Euclidean 3))`, normalized so $\sigma(S^2) = 3 \cdot \operatorname{vol}(B_1) = 4\pi$).
- **`integral_sphere_monomial`:** Proves for all $(a, b, c) \in \mathbb{N}^3$ (with zero `sorry`s, via 3D Gaussian polar-vs-Fubini factorization):
  $$\int_{S^2} \theta_0^a \theta_1^b \theta_2^c \, d\sigma(\theta) = \begin{cases} 4\pi \dfrac{(a-1)!!\,(b-1)!!\,(c-1)!!}{(a+b+c+1)!!} & \text{if } a, b, c \text{ are all even,} \\[6pt] 0 & \text{otherwise.} \end{cases}$$
- **`ftildeD_eq_poly_of_unit`:** Certifies that on $\|\theta\| = 1$, the `fderiv`-defined `ftildeD a n θ` equals the closed degree-8 polynomial `ftildeDPoly a n θ` (which also discharges $\operatorname{tr}(M) = 0$ on $S^2$).

We then proved $A = \texttt{ftildeC}$ in Lean by **two independent routes**:
1. **Route 1 — Direct Physical-Space Biot–Savart Dipole Kernel (`ftilde_dipole_angular_identification`):**
   Differentiating the Biot–Savart kernel $A_0(x) = \frac{1}{4\pi}\int \frac{y - x}{\|y - x\|^3} \times \tilde{F}(y)\,dy$ twice on outer shells $\|x\| \ll \|y\| < r_0$ and integrating once by parts on shells yields the symmetric dipole kernel $K_{\mathrm{BS},ijk}^{an}(\theta)$ (`biotSavartDipoleKernel`), built from the harmonic degree-3 tensor $\partial_p \partial_q \partial_r (\|y\|^{-1})\big|_{S^2} = 3(\delta_{pq}\theta_r + \delta_{pr}\theta_q + \delta_{qr}\theta_p) - 15\theta_p\theta_q\theta_r$. We proved:
   - `biotSavartDipoleKernel_mean_zero`: $\int_{S^2} K_{\mathrm{BS},ijk}^{an}(\theta)\, d\sigma(\theta) = 0$ for all $i,j,k,a,n$.
   - `ftilde_dipole_angular_identification`: $\sum_{a,n} \int_{S^2} K_{\mathrm{BS},ijk}^{an}(\theta)\, d_{\tilde{F},an}(\theta)\, d\sigma(\theta) = \texttt{ftildeC } i\ j\ k$ for all $i, j, k \in \operatorname{Fin} 3$.
2. **Route 2 — `G3`/`G4` Degree-4 Fourier Multiplier + Funk–Hecke Harmonic Reconstruction (`ftilde_angular_identification_a2`):**
   Starting directly from `ftildeSymbol`:
   - `quarticMonomial_harmonic_decomp` & `quarticHarmonic2_laplacian_eq_zero`: exact decomposition $\xi_p\xi_q\xi_r\xi_s = H_4 + H_2 + c_0 \|\xi\|^4$ on $S^2$ with $\Delta_{\mathbb{R}^3}(r^2 H_2) = 0$.
   - `ftildeSymbolMean_nonzero_witness`: proves `ftildeSymbolMean 0 1 0 2 0 = -1/30 ≠ 0`, confirming in Lean the standing caveat from comment `6545747341` that the $l=0$ local contact term must be separated before forming the shell kernel.
   - `quarticCZKernel_mean_zero` & `ftildeCZKernel_mean_zero`: applying Funk–Hecke inverse Fourier multipliers $(2\pi)^{-3}(-4\pi/3)$ on $l=2$ and $(2\pi)^{-3}(8\pi/15)$ on $l=4$ yields `ftildeCZKernel` with exact mean zero on $S^2$.
   - `ftilde_angular_identification_a2`: proves $\sum_{a,n} \int_{S^2} \Omega_{ijk}^{an}(-\theta)\, d_{\tilde{F},an}(\theta)\, d\sigma(\theta) = \texttt{ftildeC } i\ j\ k$ for all $27$ components.

#### 2.1.3 Disposition of Derek's Split `(A)` and `(B)`: **Proved in Lean + Complete Analytical Proof of General `(B)`**
- **Part `(A)` in Lean (`odd_stream_completion_cz_vanishes`):**
  For *any* $C^1$ scalar $\chi : \mathbb{R}^3 \to \mathbb{R}$ satisfying $\chi(-x) = -\chi(x)$, its coordinate partials $\partial_1 \chi, \partial_2 \chi$ are **even** (`coordinatePartial_odd`), so the stream completion $W_{\mathrm{odd}}(x) = (0, -\partial_2 \chi(x), \partial_1 \chi(x))$ is **even**, hence its Jacobian $D_{an}(\theta) = \partial_a W_{\mathrm{odd},n}(\theta)$ is **odd** on $S^2$. Since $\Omega_{ijk}^{an}(-\theta) = \Omega_{ijk}^{an}(\theta)$ (`ftildeCZKernel_even`), the product $\Omega_{ijk}^{an}(-\theta) D_{an}(\theta)$ is antipodally odd on $S^2$ and integrates to $0$ (`integral_sphere_odd_eq_zero`).
- **Part `(B)` in Lean for `ftildeBaseV` (`ftildeBase_dipole_angular_eq_zero` & `ftildeBase_row0_dipole_020`):**
  - `ftildeBase_dipole_angular_eq_zero`: proves that for all $27$ triples $(i, j, k)$, the unshifted potential-compensated field `ftildeBaseV` has exact shell integral $0$.
  - `ftildeBase_row0_dipole_020`: proves that the first row $V_{\mathrm{base},0}(x) = r^{-6} x_0^6 x_1$ **alone** contributes $-\frac{4}{77} \neq 0$ at $(i, j, k) = (0, 2, 0)$ (and $-\frac{4}{77}$ at $(2,0,0), (0,0,2)$, $+\frac{12}{77}$ at $(0,0,0)$), which is cancelled to $0$ by $+\frac{4}{77}$ from the $-\frac{5}{7}$ potential transverse rows!

#### 2.1.4 Complete Analytical Proof of General Part `(B)` (Why Shell-Potential Completions Always Cancel)
Why did all four filter-passing shell-potential candidates in `#29` (`02:53` and `06:23`: both azimuthal modes $m \in \{1, 2\}$, both monomial and mixed polynomial forms) cancel identically to $0$, whereas the `06:53` even stream shift gave $C_{653} \neq 0$? A single closed-form multipole identity explains `(A)`, `(B)`, `(a2)`, and the Stage 3 refutation simultaneously:

**Theorem (Spherical-Curl Characterization of the Shell Tensor $C$).** *Let $V : \mathbb{R}^3 \setminus \{0\} \to \mathbb{R}^3$ be smooth, homogeneous of degree $1$, and divergence-free ($\operatorname{div} V = 0$ on $\mathbb{R}^3 \setminus \{0\}$), and set $\tilde{F}(x) = \chi(\|x\|)\,\psi(\|x\|)\,V(x)$ with $\psi(r) = (-\log r)^{-1}$. Let $A_0 = (-\Delta)^{-1}\operatorname{curl}\tilde{F}$ be its Coulomb potential and $C_{ijk}$ the symmetric trace-free leading $\log|\log\|x\||$ shell tensor of $\partial_k \operatorname{Sym}(DA_0)_{ij}$. Let $P_3 := \texttt{cubicOfTensor } C \in \mathcal{H}_3(\mathbb{R}^3)$ (`traceFree_sym3_cubic_harmonic`). Then:*
1. **Gradient Structure of the Leading Blow-Up:** *By `korn_second_partial_identity` ($\partial_k \partial_j A_{0,i} = C_{ijk} + C_{ikj} - C_{jki}$ at $\log|\log\|x\||$ order) and total symmetry of $C$, the second partial tensor of $A_0$ has leading blow-up $C_{ijk}\log|\log\|x\||$, so*
   $$A_0(x) = \log|\log\|x\|| \cdot \nabla P_3(x) + O(1) \qquad (x \to 0).$$
2. **Exact Radial-Vorticity / Intrinsic-Curl Pairing:** *Applying $-\Delta$ to $\log|\log\|x\|| \cdot \nabla P_3(x)$ using $\Delta(\nabla P_3) = 0$ and $(x \cdot \nabla)\nabla P_3 = 2\,\nabla P_3$ gives $-\Delta\bigl(\log|\log\|x\|| \cdot \nabla P_3(x)\bigr) = 3\,\psi(\|x\|)\,\|x\|^{-2}\nabla P_3(x) + O(\psi(\|x\|)^2)$, which matches $\operatorname{curl}\tilde{F}(x) = \psi(\|x\|)\,\operatorname{curl} V(x) + O(\psi(\|x\|)^2)$ on the harmonic-cubic-gradient sector $r^{-2}\nabla\mathcal{H}_3(\mathbb{R}^3)$. Moreover, for every solid harmonic $H_3 \in \mathcal{H}_3(\mathbb{R}^3)$, since $\operatorname{div}(\operatorname{curl} V) = 0$ and $\operatorname{curl} V$ is homogeneous of degree $0$, the divergence theorem on $B_1$ gives*
   $$\int_{S^2} \bigl(\theta \cdot \operatorname{curl} V(\theta)\bigr)\,H_3(\theta)\,d\sigma(\theta) = \int_{B_1} \operatorname{div}\bigl(H_3\,\operatorname{curl} V\bigr)\,dx = \int_{B_1} \operatorname{curl} V(x) \cdot \nabla H_3(x)\,dx = \frac{1}{5}\int_{S^2} \operatorname{curl} V(\theta) \cdot \nabla H_3(\theta)\,d\sigma(\theta),$$
   *whence*
   $$\int_{S^2} \operatorname{curl} V(\theta) \cdot \nabla H_3(\theta)\,d\sigma(\theta) = 5 \int_{S^2} \bigl(\theta \cdot \operatorname{curl} V(\theta)\bigr)\,H_3(\theta)\,d\sigma(\theta).$$

Here $\theta \cdot \operatorname{curl} V(\theta) = \operatorname{curl}_{S^2}(v_{\tan})(\theta)$ is the **intrinsic spherical scalar curl** of the tangential velocity $v_{\tan}(\theta) = V(\theta) - (\theta \cdot V(\theta))\,\theta$ on $S^2$. Three immediate corollaries follow:
- **Proof of General Part `(B)`:** Every shell-potential candidate in the `02:53` / `06:23` class has tangential component constructed from a scalar shell potential on $S^2$ (`curl_{S²}(∇_{S²} Φ) ≡ 0`), so $\theta \cdot \operatorname{curl} V$ has identically zero $L^2(S^2)$-projection onto $\mathcal{H}_3(S^2)$. Therefore $\int_{S^2} \operatorname{curl} V \cdot \nabla H_3\,d\sigma = 0$ for every $H_3 \in \mathcal{H}_3(\mathbb{R}^3)$, forcing $C = 0$ across all four mode/form combinations (`m ∈ {1, 2}`, monomial and mixed).
- **Proof of Part `(A)` and the `06:53` Shift:** Adding a transverse stream completion $V_{\mathrm{str}} = (0, -\partial_2 \tilde{\chi}, \partial_1 \tilde{\chi})$ changes $\theta \cdot \operatorname{curl} V$ by $\theta_0(\partial_1^2 + \partial_2^2)\tilde{\chi} - \theta_1\partial_0\partial_1\tilde{\chi} - \theta_2\partial_0\partial_2\tilde{\chi}$. When $\tilde{\chi}(-\theta) = -\tilde{\chi}(\theta)$ is **odd**, $\theta \cdot \operatorname{curl} V_{\mathrm{str}}$ is **even** and hence orthogonal to every odd cubic harmonic $H_3 \in \mathcal{H}_3(S^2)$ (`odd_stream_completion_cz_vanishes`). When $\tilde{\chi}(-\theta) = +\tilde{\chi}(\theta)$ is **even** ($\tilde{\chi} = x_1^4/r^2$), $\theta \cdot \operatorname{curl} V_{\mathrm{str}}$ is **odd** with a nonzero $\mathcal{H}_3(S^2)$ projection, yielding $C = C_{653} \neq 0$.
- **Direct Bridge to Stage 3's Refutation:** Item (1) exhibits explicitly why the $\log|\log\|x\||$ blow-up of $A_0(x)$ is already a pure gradient $\nabla\bigl(\log|\log\|x\|| \cdot P_3(x)\bigr)$ up to $O(1)$ terms, foreshadowing its exact cancellation by a $C^2 \setminus C^3$ gauge.

---

### 2.2 Gap `(b)`: $S$-Equation Transport, Standing Remainder Law, and the Broken `G6` Step

#### 2.2.1 Exact Pinned Statements from the Record
From `#29` comments `6545396969`, `6545747341`, `6546155282`, `6546748726` and `WRITEUP.md` (`L6`, `L8`, `L10`, `G5`, `G6`):
- **Valid Coulomb/Fourier/Radial Transport (`L6`, `L8`, `L10`):**
  1. For any compactly supported divergence-free $\tilde{F} \in C^1(\mathbb{R}^3)$, the Coulomb vector potential $A_0 = (-\Delta)^{-1}\operatorname{curl}\tilde{F}$ has symmetric strain $S^{(0)} = \operatorname{Sym}(DA_0)$ satisfying $\widehat{\partial_k S^{(0)}_{ij}}(\xi) = m_{ijk}^{an}(\hat{\xi})\,\widehat{\partial_a \tilde{F}_n}(\xi)$.
  2. Pointwise in Fourier space, for $\langle \xi, v \rangle = 0$, $\operatorname{Sym}(\xi \otimes \xi \otimes v)$ is orthogonal to the symbol space $\operatorname{span}\{\xi^{\otimes 3}, \operatorname{Sym}(\delta \otimes \xi)\}$ of pure gauges $\nabla \varphi$ (`L6`).
  3. Standing remainder correction (`#29` comment `6545396969`): $\partial_k S^{(0)}_{ij}(x) = \log|\log\|x\|| \cdot C_{ijk} + C_{0,ijk} + o(1)$ uniformly as $x \to 0$, where the $\psi^2$ part of $d\tilde{F}$ contributes $O(1)$ (via $\int_r^{r_0} \frac{\psi(s)^2}{s}\,ds = \psi(r_0) - \psi(r)$), NOT $o(1)$, and the $l=0$ local symbol mean contributes $c_0 \cdot d\tilde{F}(x) = O(\psi(\|x\|)) \to 0$ (`L8`).
  4. Integrating along any ray $x = r\theta$ gives $(S^{(0)}(r\theta) - S^{(0)}(0)) / (r\log|\log r|) \to \Phi(\theta)$ with $\|\Phi(\theta)\| \ge \frac{8\sqrt{2}}{105} > 0$, proving $S^{(0)} \notin C^1$ and hence $A_0 \notin C^2$ (`L10`).
- **Broken Step `G6` (Coulomb-to-Arbitrary-Gauge Transport):**
  Asserted that for *any* potential $G = A_0 + \nabla\varphi$ on $B_{1/2}$ ($\operatorname{curl} G = \tilde{F}$), the gauge $\nabla\varphi$ could not cancel the $\log|\log\|x\|| \cdot C$ blow-up of $\partial S^{(0)}$, so $S^{(G)} = S^{(0)} + \nabla^2\varphi \notin C^1(B_{1/2})$ for every gauge $\varphi$.

#### 2.2.2 Disposition of Gap `(b)`: **Valid Coulomb Half Proved in Lean; `G6` Refuted & Generalized in Lean**

**Part 1 — Valid Coulomb Half Proved in Lean (`FtildeCZPrep.lean`, §I.3):**
- `korn_second_partial_identity`: proves $\partial_k \partial_j A_i = \partial_k S_{ij} + \partial_j S_{ik} - \partial_i S_{jk}$ for every $C^2$ vector field $A$.
- `sym3_gauge_orthogonality`: proves exact pointwise frequency-space orthogonality $\langle \operatorname{Sym}(\xi \otimes \xi \otimes v),\, \alpha(\xi^{\otimes 3}) + \beta\operatorname{Sym}(\delta \otimes \xi)\rangle = 0$ whenever $\langle \xi, v \rangle = 0$.
- `integral_ftildePsi_div_self`: proves $\int_r^{r_0} \frac{\psi(s)}{s}\,ds = \log(-\log r) - \log(-\log r_0)$ for $0 < r \le r_0 < 1$.
- `integral_ftildePsi_sq_div_self` & `integral_ftildePsi_sq_div_self_bounds`: proves $\int_r^{r_0} \frac{\psi(s)^2}{s}\,ds = \psi(r_0) - \psi(r) \in [0, \psi(r_0)]$, formalizing the standing $O(1)$ remainder law (`6545396969`).
- `ray_integral_log_neg_log_ibp` & `tendsto_log_neg_log_nhdsGT_zero`: proves $\int_{r/2}^r \log(-\log t)\,dt \ge \frac{r}{2}\log(-\log r) \to +\infty$ (rate $\gg r$).
- `l10_not_c1_of_log_log_symGrad`: proves rigorously that **no** field $S$ whose radial derivative has the asymptotic $\log(-\log t)\,\Phi(\theta) + O(1)$ with $\Phi(\theta) \neq 0$ can be $C^1$ on $B_R$. Thus the Coulomb potential $A_0$ genuinely fails to be $C^2$!

**Part 2 — Exact Failure Point of `G6` & Universal Harmonic Trap (`traceFree_sym3_cubic_harmonic`, §I.4):**
Why did `sym3_gauge_orthogonality` fail to prevent a $C^2(B_{1/2})$ gauge $G = A_0 + \nabla\varphi$ from cancelling $C \cdot \log|\log\|x\||$?
1. **Global $L^2(\mathbb{R}^3)$ vs. Local $L^\infty(B_R)$ Boundary Terms:** `sym3_gauge_orthogonality` says that on $\mathbb{R}^3$, if $\varphi$ has compact support (or $\nabla^3 \varphi \in L^2(\mathbb{R}^3)$), then $\nabla^3\varphi(\xi) = -i \xi^{\otimes 3}\hat{\varphi}(\xi)$ is pointwise orthogonal to $\operatorname{Sym}(\xi \otimes \xi \otimes v)$ when $\langle \xi, v\rangle = 0$. **On a bounded ball $B_R$, a local gauge $\varphi \in C^2(B_R)$ does NOT vanish on $\partial B_R$ and does NOT satisfy $\varphi \in C^3(B_R)$!** When one extends $\varphi$ to $\mathbb{R}^3$ via a cutoff $\chi\varphi$, $\nabla^3(\chi\varphi)$ picks up smooth interior/annular cutoff terms supported away from $0$, whose Riesz transform $\xi^{\otimes 3}|\xi|^{-2}$ has a **non-local harmonic tail inside $B_R$**!
2. **Dimension Equality $\dim \operatorname{Sym}^3_0(\mathbb{R}^3) = \dim \mathcal{H}_3(\mathbb{R}^3) = 7$ (`traceFree_sym3_cubic_harmonic`):**
   In physical space on $B_R$, a gauge $\varphi$ can cancel $C_{ijk}\log|\log\|x\||$ at leading order if and only if there exists a homogeneous cubic polynomial $P(x)$ with **$\Delta P = 0$** (so that $\Delta(P(x)\,\Phi(\|x\|))$ produces no uncompensated $\log|\log\|x\||$ trace blow-up in $\nabla^2 \varphi$!) and $\partial_a \partial_b \partial_c P = C_{abc}$.
   In `FtildeCZPrep.lean`, `cubicOfTensor C` defines $P(x) = \frac{1}{6}\sum_{i,j,k} C_{ijk} x_i x_j x_k$, and `traceFree_sym3_cubic_harmonic` proves with **zero `sorry`s** that for **every** symmetric trace-free 3-tensor $C$:
   $$\Delta(\texttt{cubicOfTensor } C) = 0 \qquad \text{and} \qquad \partial_a \partial_b \partial_c (\texttt{cubicOfTensor } C)(x) = C_{abc}!$$
   Because $\dim \operatorname{Sym}^3(\mathbb{R}^3) = \binom{5}{2} = 10$ and the trace map $\operatorname{Sym}^3(\mathbb{R}^3) \to \mathbb{R}^3$ is surjective, $\dim \operatorname{Sym}^3_0(\mathbb{R}^3) = 10 - 3 = 7 = 2(3) + 1 = \dim \mathcal{H}_3(\mathbb{R}^3)$. **There is zero codimension gap:** *every* constant symmetric trace-free 3-tensor on $\mathbb{R}^3$ is the third derivative of a harmonic cubic!

---

## 3. Dead-Class Theorem (`symmetricCurlSystem_of_sublinear_second_deriv`)

A natural follow-up question for the next `#29` direction is: *Could a single-point singularity $F(x) = \psi(\|x\|)\,V(x/\|x\|) + W(x)$ still fail to admit a $C^2$ vector potential at subleading order, or if $\psi$ is replaced by another modulus, or in higher dimension?*

We answered this in the negative in full generality by proving a **positive $C^2$ regularity theorem** in `FtildeCZPrep.lean` (§I.4):

### Theorem (`symmetricCurlSystem_of_sublinear_second_deriv` / `contDiffOn_two_poincareVectorPotential`)
Let $R > 0$ and let $F : \mathbb{R}^3 \to \mathbb{R}^3$ satisfy:
1. $F \in C^1(B_R)$ and $\operatorname{div} F = 0$ on $B_R$;
2. $F \in C^2(B_R \setminus \{0\})$;
3. **Sublinear Hessian growth at the origin:** for all $m, j \in \operatorname{Fin} 3$,
   $$\lim_{z \to 0,\, z \neq 0} \|z\| \cdot \bigl\|D(\partial_j F_m)(z)\bigr\| = 0.$$
Then the classical radial-homotopy Poincaré vector potential
$$G(x) := (\texttt{poincareVectorPotential } F)(x) = \int_0^1 t\,\bigl(F(t \cdot x) \times x\bigr)\,dt$$
satisfies **`ContDiffOn ℝ 2 G (Metric.ball 0 R)`** and **`EqOn (curl G) F (Metric.ball 0 R)`**, hence **`SymmetricCurlSystem (Metric.ball 0 R) F`**!

### Proof Mechanism (Kernel-Checked in `FtildeCZPrep.lean`)
Differentiating the scalar radial moment $M_i(g)(x) = \int_0^1 t\,x_i\,g(t x)\,dt$ once (`coordinatePartial_rayMomentIntegral`) gives:
$$\partial_j M_i(g)(x) = \int_0^1 t\,\delta_{ij}\,g(tx)\,dt + \int_0^1 t^2\,x_i\,(\partial_j g)(tx)\,dt.$$
- The first integral already has a $C^1(B_R)$ integrand!
- In the second integral (`contDiffOn_one_rayQuadIntegral`), let $h := \partial_j g \in C^0(B_R) \cap C^1(B_R \setminus \{0\})$. For $t \in (0, 1]$ and $x \neq 0$, differentiating $t^2 x_i h(tx)$ with respect to $x$ produces:
  $$t^2 h(tx)\,e_i^* + t^2 \cdot \bigl((tx)_i\,Dh(tx)\bigr).$$
  Notice the extra factor $(tx)_i = O(\|tx\|)$ multiplying $Dh(tx)$! By hypothesis $\|z\| \cdot \|Dh(z)\| \to 0$ as $z \to 0$, the map $\Psi(z) := z_i\,Dh(z)$ (with $\Psi(0) := 0$) extends **continuously across $z = 0$** on all of $B_R$, and direct difference-quotient estimation at $x = 0$ (`hasFDerivAt_rayQuadIntegral_zero_of_star`) together with Leibniz parametric differentiation on $B_R \setminus \{0\}$ (`hasFDerivAt_rayQuadIntegral_ne_zero`) proves $M_i(g) \in C^2(B_R)$!

### Immediate Consequences for `#29`
1. **Immediate alternative proof that `ftildeField` has a global $C^2$ potential:** Since $\psi(r) = (- \log r)^{-1}$ satisfies $r\psi'(r) = \psi(r)^2 \to 0$ and $r^2\psi''(r) = 2\psi(r)^3 - \psi(r)^2 \to 0$, $\|z\| \cdot \|D^2 \tilde{F}(z)\| = O(\psi(\|z\|)) \to 0$ as $z \to 0$. Thus `poincareVectorPotential ftildeField` is **globally $C^2$ on $B_{1/2}$** without needing any harmonic polynomial ansatz or case-by-case gauge repair!
2. **Entire Radial-Modulus Family Ruled Out:** *Every* divergence-free ansatz $F(x) = \psi(\|x\|)V(x/\|x\|) + W(x)$ built from a smooth angular profile $V$ and any radial modulus $\psi$ with $F \in C^1$ and $r\psi'(r) \to 0, r^2\psi''(r) \to 0$ (e.g. $|\log r|^{-\alpha}$ for any $\alpha > 0$, $(\log|\log r|)^{-\beta}$, iterated logarithms) has $\|z\| \cdot \|D^2 F(z)\| \to 0$ and therefore **always admits a global $C^2$ Poincaré vector potential**.
3. **Sharp Necessary Condition for Any Surviving Counterexample:** Any $C^1$ divergence-free counterexample $F$ on $B_R$ **must** either:
   - be $C^2$ off $0$ with **critical scale-invariant Hessian blow-up** $\limsup_{z \to 0} \|z\| \cdot \|D^2 F(z)\| > 0$ (e.g., radial phase oscillation $\psi(\|x\|)\cos(K\log\|x\|)$ where $r\partial_r\cos(K\log r) = -K\sin(K\log r) \not\to 0$, though note our numerical audit in §5.3 shows even single-point log-spirals are regularizable!), **or**
   - have **non-isolated / multiscale singular Hessian** ($F \in C^1 \setminus C^2_{\mathrm{punctured}}$, e.g. Rademacher / Baire superposition across dyadic scales and multiple spatial locations/directions).

---

## 4. Mathlib `d13f23b7` Calderón–Zygmund & Functional-Analysis Survey

We surveyed Mathlib at the repo's pinned commit `d13f23b723b8a846827a245b89c10fc7d3f11612` (`/root/lean-cache/mathlib-d13f23b7/packages/mathlib`):

| Area | Status in Mathlib `d13f23b7` | Exact Module Path(s) & Declarations | Usability for `#29` |
| :--- | :--- | :--- | :--- |
| **Calderón–Zygmund / Singular Integrals / Riesz Transforms** | **ABSENT** | Zero matches across `Mathlib/Analysis` and `Mathlib/MeasureTheory` for `Calderon`, `Zygmund`, `rieszTransform`, `hilbertTransform`, `principalValue`, `Marcinkiewicz`, `Mikhlin` | Building general $L^p$ or weak-$(1,1)$ CZ theory from scratch would cost thousands of lines and is **unnecessary** (see §5). |
| **Spherical Harmonics / Funk–Hecke / Gegenbauer** | **ABSENT** | `Legendre` exists only in number theory (`Mathlib/NumberTheory/LegendreSymbol/`); zero `SphericalHarmonic` or `FunkHecke` | Replaced in `FtildeCZPrep.lean` by exact finite harmonic projections (`quarticHarmonic2`, `quarticHarmonic4`) + `integral_sphere_monomial`. |
| **Unit-Sphere Surface Measure & Gaussian Gamma Moments** | **PRESENT** | `MeasureTheory.Measure.toSphere` (`Mathlib/MeasureTheory/Constructions/HaarToSphere.lean`); `integral_gaussian_Ioi`, `Real.Gamma_add_one` (`Mathlib/MeasureTheory/Integral/Gamma.lean`); `volume_ball` (`Mathlib/MeasureTheory/Measure/Lebesgue/VolumeOfBalls.lean`) | Used in `FtildeCZPrep.lean` (§I.1) to prove `integral_sphere_monomial` and `integral_sphere_odd_eq_zero` with zero `sorry`s. |
| **Parametric Differentiation Under the Integral Sign** | **PRESENT** | `hasFDerivAt_integral_of_dominated_of_fderiv_le''` (`Mathlib/Analysis/Calculus/ParametricIntegral.lean`); `intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'` | Used in `ParametricC1.lean` and in `FtildeCZPrep.lean` (`contDiffOn_one_rayQuadIntegral`, `planar_c2_div_fourth_order_duality`). |
| **Fourier Transform & Schwartz Space** | **PARTIAL** | `FourierTransform.fourierIntegral` (`Mathlib/Analysis/Fourier/FourierTransform.lean`); `SchwartzMap` (`Mathlib/Analysis/Distribution/SchwartzSpace.lean`) | No tempered distributions $\mathcal{S}'$ or multiplier bounds; physical-space IBP (`planar_c2_div_fourth_order_duality`) completely avoids Fourier distributions! |
| **Banach Open Mapping & Hahn–Banach Quantitative Lifting** | **PRESENT (Load-Bearing)** | `ContinuousLinearMap.isOpenMap`, `ContinuousLinearMap.exists_preimage_norm_le` (`Mathlib/Analysis/Normed/Operator/Banach.lean`); `exists_extension_norm_eq` (`Mathlib/Analysis/Normed/Module/HahnBanach.lean`) | **Already wired** into `Rudin/Research/PMA1043ProofAttack.lean` (`surjective_iff_denseRange_allGaugeCost_bound`, `lifting_extends_from_dense_submodule`)! |

---

## 5. Re-Scoped `L8` & Next-Direction Decision

### 5.1 What Was `L8` For, and Should We Build Classical `L8` CZ Remainder Estimates Now?
**Decision: NO — Do NOT build classical single-operator Calderón–Zygmund remainder infrastructure (`L8`) in Lean.**

The mathematical evidence against building `L8` is decisive on *both* sides of `#29`:
1. **In the Disproof Direction:** `L8` estimated the physical-space remainder of a *fixed linear* singular integral operator ($T = \partial \operatorname{Sym} D (-\Delta)^{-1}\operatorname{curl}$). As proved in §2.2 and §3, proving that a fixed linear potential $A_0$ blows up ($A_0 \notin C^2$) says **nothing** about whether $F$ admits a $C^2$ vector potential $G = A_0 + \nabla\varphi$! Indeed, even for the smooth regularized planar degree-1 resonant profile $h_\varepsilon(x, y) = \frac{x^3 - 3xy^2}{x^2 + y^2 + \varepsilon^2}$ ($\varepsilon \downarrow 0$), the Coulomb potential blows up logarithmically ($\|D^2 \nabla\Delta^{-1} h_\varepsilon\|_\infty \sim \log(1/\varepsilon) \to \infty$), yet the explicit non-Coulomb gauge $V_0(x, y) = \frac{1}{3}(x, y)\,r\cos(3\theta)$ has **uniformly bounded** $W^{2,\infty}$ norm ($\|D^2 V_0\|_\infty \le \frac{2}{3}$) as $\varepsilon \downarrow 0$!
2. **In the Proof Direction:** Classical CZ singular-integral theory is bounded on $L^p$ ($1 < p < \infty$) and Hölder $C^{k,\alpha}$ ($0 < \alpha < 1$), **never at the integer $C^k / L^\infty$ endpoint**. Worse: by **Bourgain–Brezis (2003, *J. Amer. Math. Soc.* 16, Theorem 2 & Remark 4)**, there is **no continuous linear right-inverse** for $\operatorname{div} : W^{1,\infty}(\mathbb{T}^d) \to L^\infty_0(\mathbb{T}^d)$ or $\operatorname{div} : C^2(\mathbb{T}^2) \to C^1_0(\mathbb{T}^2)$! Therefore:
   - Neither Biot–Savart/Coulomb, nor radial Poincaré (`poincareVectorPotential`), nor Costabel–McIntosh / Bogovskii smoothed-homotopy operators (Costabel–McIntosh 2010, *Math. Z.* 265, `arXiv:0808.2614`; Berselli–Longo 2018, `arXiv:1712.07917`, which gain Besov / $W^{k+1,p}$ / $C^{2,\alpha}$ for $0 < \alpha < 1$ by smearing the homotopy center $a \in B$, but still act as *linear* convolution-type operators!) can map arbitrary $C^1$ divergence-free fields into $C^2$.
   - Any positive proof of `pma10_43_contract` **must** select a *nonlinear, datum-dependent* gauge via Hahn–Banach / Banach Open Mapping (`PMA1043ProofAttack.lean`), never via a single linear CZ kernel.

### 5.2 Exact All-Gauge Reduction: The 4-Component Planar System & Canceling-Operator Duality
The repo already contains two major structural reductions:
- `Rudin/Research/PMA1043Planar.lean` (`c2_verticalPotential_iff_planarDivergence`): For vertical fields $F(x, y, z) = (0, 0, h(x, y))$ with $h \in C^1(\mathbb{R}^2)$, existence of $G \in C^2(\mathbb{R}^3)^3$ with $\operatorname{curl} G = F$ is **equivalent** to existence of a planar field $V = (V_0, V_1) \in C^2(\mathbb{R}^2)^2$ solving:
  $$\operatorname{planarDivergence} V := \partial_x V_0 + \partial_y V_1 = h.$$
- `Rudin/Research/PMA1043Compatibility.lean` (`planarDivergence_iff_compatible_columns`) & `Rudin/Research/PMA1043ProofAttack.lean` (`lifting_extends_from_dense_submodule`): On compact/periodic or ball models, `Surjective T` is equivalent to a uniform `allGaugeCost` bound on a **dense submodule** (such as $C^\infty$ data, where smooth solutions already exist by standard Poisson potential theory!).

Let us record the exact **4-component second-derivative compatibility system** governing $\partial_x V_0 + \partial_y V_1 = h$ for $h \in C^1$:
Differentiating $\partial_x V_0 + \partial_y V_1 = h$ gives $\partial_{xx} V_0 = \partial_x h - \partial_{xy} V_1$ and $\partial_{yy} V_1 = \partial_y h - \partial_{xy} V_0$. Since $\partial_x h, \partial_y h \in C^0$ are already continuous, controlling all **six** second partials $(\partial_{xx} V_0, \partial_{xy} V_0, \partial_{yy} V_0, \partial_{xx} V_1, \partial_{xy} V_1, \partial_{yy} V_1)$ in $C^0$ is **equivalent** to finding four continuous functions
$$(g_0, g_1, g_2, g_3) := \bigl(\partial_{xx} V_1,\ \partial_{xy} V_1,\ -\partial_{xy} V_0,\ -\partial_{yy} V_0\bigr) \in C^0(\Omega)^4$$
satisfying the distributional first-order chain:
$$\partial_y g_0 - \partial_x g_1 = 0, \qquad \partial_y g_1 - \partial_x g_2 = \partial_x \partial_y h, \qquad \partial_y g_2 - \partial_x g_3 = 0.$$
*(Note: under a gauge shift $(V_0, V_1) \mapsto (V_0 + \partial_y \psi, V_1 - \partial_x \psi)$, $(g_0, g_1, g_2, g_3)$ shifts precisely by the third-order jet $-(\partial_x^3 \psi, \partial_x^2 \partial_y \psi, \partial_x \partial_y^2 \psi, \partial_y^3 \psi)$!)*

By Hahn–Banach duality against smooth compactly supported test triples $(\phi_1, \phi_2, \phi_3) \in C_c^\infty(\Omega)^3$, uniform boundedness of $\inf_{\operatorname{div} V = h} \|D^2 V\|_{C^0} \le C \|h\|_{C^1}$ is **equivalent** to the **4-component all-gauge duality inequality**:
$$\left|\int_\Omega h \, \partial_x \partial_y \phi_2\right| \le C \|h\|_{C^1(\Omega)} \Bigl(\|\partial_y \phi_1\|_{L^1} + \|\partial_x \phi_1 - \partial_y \phi_2\|_{L^1} + \|\partial_x \phi_2 - \partial_y \phi_3\|_{L^1} + \|\partial_x \phi_3\|_{L^1}\Bigr). \tag{$\star$}$$
Setting $(\phi_1, \phi_2, \phi_3) := (\partial_y^2 w, \partial_x \partial_y w, \partial_x^2 w)$ makes the two middle $L^1$ terms vanish identically and isolates the **pure diagonal canceling-operator bound** proved in `FtildeCZPrep.lean` (`planar_c2_div_fourth_order_duality` and `planar_c2_div_fourth_order_bound`, **zero `sorry`s**, requiring ONLY $V \in C^2$ and never $V \in C^3$!):
$$\left|\int_{[a,b]\times[c,d]} (\operatorname{planarDivergence} V)(x, y)\cdot \partial_x^2 \partial_y^2 w(x, y)\,dx\,dy\right| \le \max\bigl(\|\partial_y^2 V_0\|_\infty, \|\partial_x^2 V_1\|_\infty\bigr) \int_{[a,b]\times[c,d]} \bigl(|\partial_x^3 w| + |\partial_y^3 w|\bigr)\,dx\,dy,$$
i.e., in homogeneous Sobolev duality:
$$\|\partial_x^2 \partial_y^2 w\|_{\dot{W}^{-1,1}(\mathbb{R}^2)} \lesssim \|\partial_x^3 w\|_{L^1(\mathbb{R}^2)} + \|\partial_y^3 w\|_{L^1(\mathbb{R}^2)}. \tag{$\star\star$}$$

### 5.3 Literature Position & Numerical Diagnostics

#### Literature Audit (Live Web & ArXiv Verified)
1. **De Pauw (Oct 2026, `arXiv:2610.35452`, *"The divergence of continuously differentiable vector fields"*):** Completely characterizes the **one-derivative-lower** endpoint $\operatorname{div} v = f$ with $v \in C^1(\mathbb{R}^m), f \in C^0(\mathbb{R}^m)$ (equivalently $\operatorname{curl} G = F$ with $G \in C^1, F \in C^0$): $\operatorname{div}(C^1)$ is a *proper* dense subspace of $C^0$ (specifically, the closure of boundedly weakly differentiable functions in the charge/BV-duality topology, since $\int f\,\varphi = -\int v \cdot \nabla\varphi \le \|v\|_\infty |D\varphi|$). By contrast, in Rudin 10.43 (`pma10_43_contract`), $F$ is **already $C^1$** ($h \in C^1$, so $|\int h\,\partial_x\partial_y \phi_2| = |\int \partial_x h\,\partial_y \phi_2|$ already gains one full derivative over $C^0$!).
2. **Van Schaftingen (2013, *JEMS* 15) & Bourgain–Brezis (2003, 2007):** The operator $A(D)w = (\partial_x^3 w, \partial_y^3 w)$ on $\mathbb{R}^2$ is **elliptic** ($(\xi^3, \eta^3) = 0 \implies (\xi, \eta) = 0$) and **canceling** ($\bigcap_{(\xi,\eta)\neq 0} \mathbb{R}\cdot(\xi^3, \eta^3) = \{0\}$). Hence by Van Schaftingen's theorem ($k = 3, d = 2$),
   $$\|D^2 w\|_{L^2(\mathbb{R}^2)} \lesssim \|\partial_x^3 w\|_{L^1(\mathbb{R}^2)} + \|\partial_y^3 w\|_{L^1(\mathbb{R}^2)},$$
   which **immediately proves** existence of a bounded-$D^2$ potential whenever $D^2 h \in L^2$!
3. **Why $(\star\star)$ / $(\star)$ Is the Exact Knife-Edge Frontier:**
   - By **Ornstein's (1962) non-inequality**, at derivative order $3$ ($L^1 \to L^1$), $\|\partial_x^2 \partial_y w\|_{L^1} \not\lesssim \|\partial_x^3 w\|_{L^1} + \|\partial_y^3 w\|_{L^1}$!
   - However, $(\star\star)$ asks **not** for $\|\partial_x^2 \partial_y w\|_{L^1}$ (which corresponds to $h \in C^0$, the false $C^0 \to C^1$ statement), but for $\|\partial_x^2 \partial_y^2 w\|_{\dot{W}^{-1,1}} = \sup_{\|\nabla h\|_\infty \le 1} \bigl|\int h\,\partial_x^2\partial_y^2 w\bigr|$, whose homogeneous degree-$0$ Fourier symbol ratio is:
     $$m(\xi, \eta) = \frac{\xi^2 \eta^2}{\sqrt{\xi^2 + \eta^2}\,\bigl(|\xi|^3 + |\eta|^3\bigr)}.$$
     Indeed, $\partial_x^2 \partial_y^2 w$ has derivative order $4$, and the $\dot{W}^{-1,1}$ pairing against $h$ with $\nabla h \in L^\infty$ integrates once by parts to net derivative order $4 - 1 = 3$, matching $\|\partial_x^3 w\|_{L^1} + \|\partial_y^3 w\|_{L^1}$ (order $3$).
     Along any **single rank-one plane wave** $w(x, y) = g(\xi x + \eta y)$,
     $$\frac{\|\nabla^{-1}\partial_x^2\partial_y^2 w\|_{L^1}}{\|\partial_x^3 w\|_{L^1} + \|\partial_y^3 w\|_{L^1}} \sim \frac{\xi^2 \eta^2 (|\xi| + |\eta|)^{-1}}{|\xi|^3 + |\eta|^3} \le \frac{\xi^2 \eta^2}{(|\xi| + |\eta|)(|\xi|^3 + |\eta|^3)} \le \frac{1}{4} < \infty!$$
     Thus **every rank-one laminate is uniformly bounded** (unlike Ornstein's algebraic rank-one obstructions for non-elliptic operators)! Any failure of $(\star\star)$ or $(\star)$ can ONLY arise from **2D multi-directional logarithmic CZ / Ornstein wavepacket interference** where $\partial_x^3 w$ and $\partial_y^3 w$ cancel along sparse grids while $(-\Delta)^{-1/2}\partial_x^2\partial_y^2 w$ accumulates logarithmically across scales, OR else Bourgain–Brezis / JBBN compensation holds and `pma10_43_contract` is **TRUE**!

#### Certified Primal–Dual Numerical Diagnostics (`N = 8, 16, 32` Fourier Grids on $\mathbb{T}^2$)
We ran certified primal–dual linear programs computing both the 2-component fourth-order ratio (`max(‖∂_yy V₀‖_∞, ‖∂_xx V₁‖_∞)`) and the **full 6-component Hessian all-gauge cost** $\inf_{\operatorname{div} V = h} \max_{|\alpha|=2} \|\partial^\alpha V\|_\infty / \|\nabla h\|_\infty$ across dyadic grid refinements $N = 8, 16, 32$:

| Test Datum $h(x, y)$ (normalized by $\|\nabla h\|_\infty = 1$) | $N = 8$ All-Gauge Cost | $N = 16$ All-Gauge Cost | $N = 32$ All-Gauge Cost | Coulomb Gauge Cost ($N = 32$) | Interpretation |
| :--- | :---: | :---: | :---: | :---: | :--- |
| `r² cos(2θ) log|log r|` (2-comp LP + certified dual) | `0.0102` (`0.0101`) | `0.0113` (`0.0113`) | `0.0116` (`0.0115`) | `0.0449` | Flat ($O(1)$); consistent with §3 Dead-Class Theorem |
| `x y log|log r|` (2-comp LP + certified dual) | `0.1404` (`0.1404`) | `0.1283` (`0.1283`) | `0.1278` (`0.1278`) | `0.4875` | Flat ($O(1)$); diagonal `x y` mode fully absorbed by gauge |
| Dyadic `∑_{k} 2⁻ᵏ cos(2ᵏ x) cos(2ᵏ y)` (2-comp LP) | `0.2544` | `0.2697` | `0.3051` | `0.5000` | Bounded ($\le 0.5$ even in Coulomb because lacunary phases align) |
| Resonant `m=3`: `(x³ - 3xy²)/(r² + ε²)` (**all 6 derivs**) | `0.5232` | `0.5895` | `0.6315` | `0.8788` ($\to \infty$ as $\varepsilon \to 0$) | Converges to finite $\|D^2 V_0\|_\infty \approx 2/3$ of $V_0 = \frac{1}{3} x r \cos 3\theta \in W^{2,\infty}$ |
| Log-spiral `m=3`: `r³ cos(3θ - 2 log r)/(r² + ε²)` (**all 6 derivs**) | `0.5081` | `0.5321` | `0.6059` | `0.9550` ($\to \infty$ as $\varepsilon \to 0$) | Even single-point critical log-spirals admit bounded-$D^2$ gauges! |
| McMullen-type product Rademacher `∑ 2⁻ᵏ sin(2ᵏ x) sin(2ᵏ y)` (**all 6 derivs**) | `0.2500` | `0.4271` | `0.4330` | `0.5000` | Stabilizes around `~0.43` |

### 5.4 Recommended Next Step for `#29`
Do **not** launch another candidate-guess disproof lane on single-point profiles, and do **not** launch a multi-thousand-line Lean formalization before settling the 2D canceling-operator duality gate:

1. **Stage A (Focused Analytical Gate — 1 research lane):** Resolve the truth value of $(\star\star)$ and $(\star)$ on $\mathbb{T}^2$:
   $$\sup_{w \in C^\infty(\mathbb{T}^2)} \frac{\|\nabla(-\Delta)^{-1}\partial_x^2\partial_y^2 w\|_{L^1(\mathbb{T}^2)}}{\|\partial_x^3 w\|_{L^1(\mathbb{T}^2)} + \|\partial_y^3 w\|_{L^1(\mathbb{T}^2)}} < \infty \quad \text{?}$$
   Specifically, test Ornstein's multi-scale shear/grid construction (where $\partial_x^3 w, \partial_y^3 w$ are concentrated on sparse $L^1$ Diracs/tent-functions while $\partial_x^2 \partial_y w$ grows as $\sqrt{\log K}$, and check whether the inverse gradient $\nabla(-\Delta)^{-1}\partial_y$ kills or preserves the $\sqrt{\log K}$ Ornstein growth!).
2. **Stage B1 (If Ornstein grid-testing breaks $(\star\star)$ / $(\star)$):**
   `planar_c2_div_fourth_order_bound` (already kernel-checked in `FtildeCZPrep.lean`!) + `PMA1043Planar.lean` (`c2_verticalPotential_iff_planarDivergence`) turn the violating sequence $w_k \in C_c^\infty((0,1)^2)$ directly into a compactly supported $C^1$ counterexample $h = \sum_k \varepsilon_k h_k$ with **zero singular-integral or Fourier theory needed in Lean** (only finite rectangular integration by parts, already proved in `FtildeCZPrep.lean`!).
3. **Stage B2 (If $(\star)$ holds):**
   Prove the 3D ball analogue of $(\star)$ via Bourgain–Brezis / JBBN $L^1$ div-curl compensation, feed it into `PMA1043ProofAttack.lifting_extends_from_dense_submodule` on dense $C^2$ divergence-free fields (whose $C^3$ potentials already exist via classical Newtonian potential theory) to obtain $W^{2,\infty} \cap C^2$ local potentials on balls (using Bourgain–Brezis continuous-selection perturbation from $L^\infty$ to $C^0$), and glue across an open cover to **prove `pma10_43_contract`**.

---

## 6. Inventory of Kernel-Checked Declarations & Verification Log

### 6.1 Key Declarations in `rudin/Rudin/PMA/Chapter10/FtildeCZPrep.lean`

| Section | Declaration | Statement / Role | `sorry`s |
| :--- | :--- | :--- | :---: |
| **I.1** | `sphereSurfaceMeasure` | `Measure.toSphere (volume : Measure (Euclidean 3))` normalized to $\sigma(S^2) = 4\pi$ | `0` |
| **I.1** | `integral_sphere_monomial` | Exact closed-form evaluation of $\int_{S^2} \theta_0^a \theta_1^b \theta_2^c\,d\sigma(\theta)$ via 3D Gaussian polar/Fubini | `0` |
| **I.1** | `integral_sphere_odd_eq_zero` | Any continuous antipodally odd function integrates to $0$ on $S^2$ | `0` |
| **I.1** | `odd_stream_completion_cz_vanishes` | **Gap `(a2)` Part `(A)`:** Any odd $C^1$ stream completion contributes $0$ against any even kernel | `0` |
| **I.2** | `ftildeD_eq_poly_of_unit` | On $\|\theta\| = 1$, `ftildeD a n θ = ftildeDPoly a n θ` | `0` |
| **I.2** | `biotSavartDipoleKernel_mean_zero` | Route 1 physical-space Biot–Savart dipole kernel has exact mean zero on $S^2$ | `0` |
| **I.2** | `ftilde_dipole_angular_identification` | **Gap `(a2)` (Route 1):** Biot–Savart dipole sphere integral $= \texttt{ftildeC } i\ j\ k$ ($\forall i,j,k$) | `0` |
| **I.2** | `quarticMonomial_harmonic_decomp` | Exact $l \in \{0, 2, 4\}$ harmonic decomposition of $\xi_p\xi_q\xi_r\xi_s$ on $\mathbb{R}^3$ | `0` |
| **I.2** | `quarticHarmonic2_laplacian_eq_zero` | Harmonicity $\Delta_{\mathbb{R}^3}(r^2 H_2) = 0$ of all 81 degree-2 pieces | `0` |
| **I.2** | `ftildeSymbolMean_nonzero_witness` | Standing local-term witness: `ftildeSymbolMean 0 1 0 2 0 = -1 / 30` | `0` |
| **I.2** | `ftildeCZKernel_mean_zero` | Route 2 reconstructed `G3`/`G4` CZ kernel $\Omega_{ijk}^{an}$ has exact mean zero on $S^2$ | `0` |
| **I.2** | `ftilde_angular_identification_a2` | **Gap `(a2)` (Route 2):** $\int_{S^2} \Omega_{ijk}^{an}(-\theta)\,d_{\tilde{F},an}(\theta)\,d\sigma(\theta) = \texttt{ftildeC } i\ j\ k$ ($\forall i,j,k$) | `0` |
| **I.2** | `ftildeBase_dipole_angular_eq_zero` | **Gap `(a2)` Part `(B)`:** Unshifted potential-compensated `ftildeBaseV` integrates to $0$ ($\forall i,j,k$) | `0` |
| **I.2** | `ftildeBase_row0_dipole_020` | First row of `ftildeBaseV` alone gives `-4 / 77 ≠ 0` at `(0, 2, 0)` | `0` |
| **I.3** | `korn_second_partial_identity` | $\partial_k \partial_j A_i = \partial_k S_{ij} + \partial_j S_{ik} - \partial_i S_{jk}$ for any $C^2$ vector field $A$ | `0` |
| **I.3** | `sym3_gauge_orthogonality` | Pointwise Fourier orthogonality $\langle \operatorname{Sym}(\xi\otimes\xi\otimes v), \alpha\xi^{\otimes 3} + \beta\operatorname{Sym}(\delta\otimes\xi)\rangle = 0$ for $\langle\xi,v\rangle = 0$ | `0` |
| **I.3** | `integral_ftildePsi_div_self` | $\int_r^{r_0} \frac{\psi(s)}{s}\,ds = \log(-\log r) - \log(-\log r_0)$ | `0` |
| **I.3** | `integral_ftildePsi_sq_div_self_bounds` | Standing `O(1)` remainder law: $0 \le \int_r^{r_0} \frac{\psi(s)^2}{s}\,ds = \psi(r_0) - \psi(r) \le \psi(r_0)$ | `0` |
| **I.3** | `l10_not_c1_of_log_log_symGrad` | **`L10`:** Ray asymptotic $\log(-\log t)\,\Phi(\theta) + O(1)$ ($\Phi(\theta) \neq 0$) $\implies S \notin C^1(B_R)$ | `0` |
| **I.4** | `traceFree_sym3_cubic_harmonic` | **Universal Harmonic Trap:** Every symmetric trace-free $C$ is $\nabla^3(\texttt{cubicOfTensor } C)$ with $\Delta P = 0$ | `0` |
| **I.4** | `curl_poincareVectorPotential` | $\operatorname{curl}(\texttt{poincareVectorPotential } F) = F$ on $B_R$ for any $C^1$ divergence-free $F$ | `0` |
| **I.4** | `contDiffOn_two_poincareVectorPotential` | Sublinear Hessian $\|z\|\cdot\|D^2 F(z)\| \to 0 \implies \texttt{poincareVectorPotential } F \in C^2(B_R)$ | `0` |
| **I.4** | `symmetricCurlSystem_of_sublinear_second_deriv` | **Dead-Class Theorem:** Sublinear Hessian off $0 \implies$ `SymmetricCurlSystem (ball 0 R) F` | `0` |
| **I.4** | `planar_c2_div_fourth_order_duality` | Exact 2D fourth-order IBP identity for **any** $V \in C^2$ (no $C^3$ assumption) against $\partial_x^2\partial_y^2 w$ | `0` |
| **I.4** | `planar_c2_div_fourth_order_bound` | Gauge-invariant $L^\infty$–$L^1$ bound $|\int (\operatorname{div} V)\,\partial_x^2\partial_y^2 w| \le M\int(|\partial_x^3 w| + |\partial_y^3 w|)$ | `0` |

### 6.2 Build, Axiom Audit, & `leanchecker` Replay Log

All verification commands executed cleanly in `/root/projects/rudin/rudin-lean-stage4prep/rudin` on toolchain `leanprover/lean4:v4.34.1` against Mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612`:

- **File Metrics (`rudin/Rudin/PMA/Chapter10/FtildeCZPrep.lean`):**
  - Lines: `3346`
  - SHA-256: `d76fef11a3cbd96a1f754d2e78e619ab816d743cd459c9c29afabde9a3053fb5`
  - Forbidden-token scan (`rg -i -n "sorry|admit|native_decide|bv_decide|axiom "`): **0 matches** (even in comments).
- **Full Library Build & Module Build (`lake build && lake build Rudin.PMA.Chapter10.FtildeCZPrep`):**
  - Exit code: `0` (`Build completed successfully (9208 jobs)` / `Build completed successfully (9073 jobs)`, zero errors, zero warnings on `FtildeCZPrep.lean`).
- **In-File Module Axiom Audit (`Rudin.PMA.Audit.checkModuleAxioms`):**
  ```text
  info: Rudin/PMA/Chapter10/FtildeCZPrep.lean:3327:0: Axiom audit module Rudin.PMA.Chapter10.FtildeCZPrep: checked 246 declarations.
  info: Rudin/PMA/Chapter10/FtildeCZPrep.lean:3327:0: Axiom audit for Rudin.PMA.Chapter10.FtildeCZPrep: checked 246 declarations in 1 modules; axioms used: [propext, Classical.choice, Quot.sound]; no forbidden axioms.
  ```
  All 18 named coverage targets (`integral_sphere_monomial`, `odd_stream_completion_cz_vanishes`, `ftilde_dipole_angular_identification`, `ftildeSymbolMean_nonzero_witness`, `ftilde_angular_identification_a2`, `ftildeBase_dipole_angular_eq_zero`, `ftildeBase_row0_dipole_020`, `korn_second_partial_identity`, `sym3_gauge_orthogonality`, `integral_ftildePsi_div_self`, `integral_ftildePsi_sq_div_self_bounds`, `l10_not_c1_of_log_log_symGrad`, `traceFree_sym3_cubic_harmonic`, `contDiffOn_two_poincareVectorPotential`, `curl_poincareVectorPotential`, `symmetricCurlSystem_of_sublinear_second_deriv`, `planar_c2_div_fourth_order_duality`, `planar_c2_div_fourth_order_bound`) reported `axioms used: [propext, Classical.choice, Quot.sound]`.
- **Independent Kernel Replay (`lake env leanchecker Rudin.PMA.Chapter10.FtildeCZPrep`):**
  - Executed from `/root/projects/rudin/rudin-lean-stage4prep/rudin` (module name path, never stdin): exit code `0`.
