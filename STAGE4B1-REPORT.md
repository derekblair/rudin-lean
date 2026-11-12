# STAGE4B1-REPORT — Rudin PMA Theorem 10.43 Stage B1 Witness Instantiation (`¬ pma10_43_contract`)

- **Lane:** `carbon-rudin1043-stage4b1-20261112` (dominic, `agy --model gemini-4-carbon-high --effort high`)
- **Ticket:** `rudin-lean` #29 (`SymmetricDerivativeLifting` / Rudin PMA Theorem 10.43)
- **Branch:** `coordinator/rudin29-stage4b1` (branched from `origin/main` = `a14501c8d22a63d6b84584dbe5cdc5a94053b18b`; no rebase required as `origin/main` remained at `a14501c8d22a63d6b84584dbe5cdc5a94053b18b`)
- **Closed Target Statement:** `theorem not_pma10_43_contract : ¬ pma10_43_contract` (`rudin/Rudin/Research/Stage4B1Disproof.lean:905`, in `namespace Rudin.PMA.Chapter10`)

---

## §0. Pin Verification (Verified Inside Clone Before Lean Authoring and Re-Verified at Commit Time)

All §0 pins from `BRIEF.md` were verified inside `/root/projects/rudin/tasks/carbon-rudin1043-stage4b1-20261112/repo` before writing any Lean and re-verified byte-identical at commit time:

| Pin | Expected | Verified | Status |
|---|---|---|---|
| `origin/main` HEAD | `a14501c8d22a63d6b84584dbe5cdc5a94053b18b` | `a14501c8d22a63d6b84584dbe5cdc5a94053b18b` (`2026-11-12T10:58:53Z`, merge of PR #31) | PASS |
| Branch | `coordinator/rudin29-stage4b1` from `a14501c8` | `coordinator/rudin29-stage4b1` branched directly from `a14501c8d22a63d6b84584dbe5cdc5a94053b18b` | PASS |
| `rudin/Rudin/Research/PMA1043Stage4B1.lean` | blob `2b567de8306221bf6d0d2c73c4f53b7702aeca32`, 1,809 lines, sha256 `de8e3a0107c25f22b2a6e75a95baf2cbd9cd5c2f30e01fba63104310b89b6eb0` | blob `2b567de8306221bf6d0d2c73c4f53b7702aeca32`, 1,809 lines, sha256 `de8e3a0107c25f22b2a6e75a95baf2cbd9cd5c2f30e01fba63104310b89b6eb0` | PASS |
| `rudin/Rudin/PMA/Chapter10/FtildeCZPrep.lean` | blob `3ef282f5adc6adf4c17060da9a33279a13733013`, 3,348 lines, sha256 `4c92ac3a4a913e1607009a68214000d30c39f6022fe906be377982be50846a64` | blob `3ef282f5adc6adf4c17060da9a33279a13733013`, 3,348 lines, sha256 `4c92ac3a4a913e1607009a68214000d30c39f6022fe906be377982be50846a64` | PASS |
| `rudin/Rudin/PMA/Chapter10/FtildeDisproofStatement.lean` | blob `ae048cdba44c3ca32545ea2cf965fab44a45d646`, 485 lines, sha256 `1373120ecb51e4bb632886af97bf83a9b64f5a5e90ea5fbb07a935d14783f601` | blob `ae048cdba44c3ca32545ea2cf965fab44a45d646`, 485 lines, sha256 `1373120ecb51e4bb632886af97bf83a9b64f5a5e90ea5fbb07a935d14783f601` | PASS |
| `STAGE4-PREP-REPORT.md` | blob `e9d3528e3147f2ff43aea6774961bbba5604ebbc`, 299 lines, sha256 `1fd897796d60b1b37ece6c4a64517c251ffce2d3edd9febde71f79b974e63bf3` | blob `e9d3528e3147f2ff43aea6774961bbba5604ebbc`, 299 lines, sha256 `1fd897796d60b1b37ece6c4a64517c251ffce2d3edd9febde71f79b974e63bf3` | PASS |
| `rudin/Rudin/PMA/Chapter10/VectorPotentials.lean` (`pma10_43_contract` `:16-26`) | unmodified | blob `131b8b004b5bfe5ff8defae822485ee8294cd4f5`, 127 lines, sha256 `d7c1a926415911e523a70a29c0957bc63dc271b981f86c04dcbcb11ee37f4c84` | PASS |
| `rudin/lean-toolchain` | `leanprover/lean4:v4.34.1` | `leanprover/lean4:v4.34.1` | PASS |
| `rudin/lake-manifest.json` Mathlib `inputRev` | `d13f23b723b8a846827a245b89c10fc7d3f11612` | `d13f23b723b8a846827a245b89c10fc7d3f11612` | PASS |
| Golden Mathlib cache | `/root/lean-cache/mathlib-d13f23b7/packages` (symlink only) | `repo/rudin/.lake/packages -> /root/lean-cache/mathlib-d13f23b7/packages` | PASS |

---

## §1. `rudin/Rudin/Research/Stage4B1Waves.lean` — 1D Polynomial-Spline Waves & Plateau Cutoffs

- **Lines:** `951`
- **Module Declarations Audited (`checkModuleAxioms`):** `101`
- **Git Blob SHA:** `8149c2a4c37bdc7481e31bf44fcc8bac2eae58fd`
- **SHA-256:** `ab8c4bb8df27ae91017f85136f80bb7f78cb11a6969ffbd62479b7c8ea9b8abe`
- **Key Declarations (`namespace Rudin.PMA.Chapter10`):**
  - `hasDerivAt_clampSpline` (`:79`), `smoothstep9` (`:218`), `contDiff_smoothstep9` (`:253`): Closed-form degree-9 clamped transition spline `70 u⁹ - 315 u⁸ + 540 u⁷ - 420 u⁶ + 126 u⁵` on `[0, 1]`, proved `ContDiff ℝ (4 : ℕ)` via four explicit polynomial derivatives with boundary vanishing of derivatives `1..4`.
  - `boxCutoff1D` (`:299`), `contDiff_boxCutoff1D` (`:302`): Smooth `C⁴` outer cutoff supported in `[1/8, 7/8]` and equal to `1` on `[1/4, 3/4]`.
  - `etaWave` (`:341`), `contDiff_etaWave` (`:374`), `etaWave_periodic` (`:423`), `integral_etaWave_sq_ge` (`:446`): `1`-periodic `C⁴` plateau cutoff supported in `(δ/2, 1/2 - δ/2) + ℤ`, equal to `1` on `[δ, 1/2 - δ] + ℤ`, satisfying `1/2 - 2δ ≤ ∫_0^1 (etaWave δ t)^2 dt`.
  - `tauDerivWave` (`:481`), `contDiff_tauDerivWave` (`:522`), `tauDerivWave_antiperiodic` (`:575`), `abs_tauDerivWave_le_one` (`:610`), `etaWave_mul_tauDerivWave` (`:662`), `integral_tauDerivWave_sq_ge` (`:675`): `(1/2)`-antiperiodic `C⁴` square-wave spline with periodization seam placed inside the `+1` plateau at `1/4 + ℤ`, satisfying `|tauDerivWave δ t| ≤ 1`, the pointwise stopping identity `etaWave δ t * tauDerivWave δ t = etaWave δ t`, and `1 - 2δ ≤ ∫_0^1 (tauDerivWave δ t)^2 dt`.
  - `antiperiodicPrimitive` (`:725`), `tauWave` (`:851`), `gammaDerivWave` (`:855`), `gammaWave` (`:859`), `contDiff_tauWave` (`:862`), `contDiff_gammaDerivWave` (`:866`), `contDiff_gammaWave` (`:870`), `abs_tauWave_le` (`:901`), `abs_gammaDerivWave_le` (`:910`), `abs_gammaWave_le` (`:919`): Iterated `(1/2)`-antiperiodic `C⁴` primitives satisfying `Γ_δ''' = tauDerivWave δ` and uniform bounds `|tauWave δ t| ≤ 1/4`, `|gammaDerivWave δ t| ≤ 1/16`, `|gammaWave δ t| ≤ 1/64`.

---

## §2. `rudin/Rudin/Research/Stage4B1Staircase.lean` — Compactly Supported 3-Ray Stopped Staircase `(U_K, h_K)`

- **Lines:** `4,162`
- **Module Declarations Audited (`checkModuleAxioms`):** `238`
- **Git Blob SHA:** `3781466bb698a833fea10164ac09f9a70e0a0786`
- **SHA-256:** `268be13cf601e56b6e0ecea11b941d992becc931bb62b9ca50068d6ff222f038`
- **Key Declarations (`namespace Rudin.PMA.Chapter10`):**
  - `antiperiodic_phase_sign_bound_1d` (`:492`), `periodic_phase_sign_mean_bound_1d` (`:546`): Phase-shifted and nonzero-mean 1D equidistribution wrappers derived directly from `antiperiodic_haar_shift_bound_1d` (`PMA1043Stage4B1.lean:1611`), exploiting `|v_{r,x}| ∈ {1, 1/2} > 0` for all three exact rays `spin3Ray0..2`.
  - `staircaseU` (`:1256`), `staircaseH` (`:1260`), `contDiff_staircaseU` (`:1263`), `contDiff_staircaseH` (`:1268`): Closed-form `K`-scale 3-ray stopped-martingale spline pair on `[0, 1]²` with rapidly lacunary integer frequencies `staircaseM` (`:1158`), proved `ContDiff ℝ (4 : ℕ)`.
  - `staircaseU_zero_outside` (`:1273`), `staircaseH_zero_outside` (`:1279`), `vanishesThirdPartialsOnRectBdry_staircaseU` (`:1285`): Compact support inside `[1/8, 7/8]² ⊂ (0, 1)²` and vanishing of all 16 third-order boundary partials on `∂([0, 1]²)`.
  - `abs_staircaseH_le_one` (`:1477`), `abs_planarDx_staircaseH_le_half` (`:1583`), `abs_planarDy_staircaseH_le_half` (`:1695`), `norm_fderiv_staircaseH_le_one` (`:1807`): Uniform `C¹(ℝ²)` bounds independent of `K` via 3-ray zero-sum Abel summation (`spin3Ray0 + spin3Ray1 + spin3Ray2 = 0`) and the stopping identity `A_{k+1} · τ'_{δ,k} = A_{k+1}`.
  - `spin3_l1_staircaseU_le_one` (`:2513`), `spin3_l1_staircaseU_le_two` (`:2880`): Uniform spin-3 `L¹([0, 1]²)` bound `∫_0^1 ∫_0^1 (|spin3A1 (staircaseU K)| + |spin3A2 (staircaseU K)|) ≤ 1` (matching the Stage A theoretical `0.990..1.000` range, with `spin3A2` killed on pure ray waves by `spin3_three_ray_obstruction` and `spin3A1` telescoping along the stopped dyadic martingale).
  - `pairing_staircase_lower_bound` (`:4112`): Linear `((m + 1 : ℝ) / 4096) ≤ ∫_0^1 ∫_0^1 staircaseH (3 * (m + 1)) · ∂_x² ∂_y² (staircaseU (3 * (m + 1)))` lower bound via `x`-integration by parts, diagonal survival on `k % 3 ∈ {1, 2}` (`v_{k,x}² v_{k,y}² = 3/16`), and exponential off-diagonal decay.

---

## §3. `rudin/Rudin/Research/Stage4B1Disproof.lean` — Disjoint-Box `C¹` Gliding-Hump Sum & Unconditional `¬ pma10_43_contract`

- **Lines:** `921`
- **Module Declarations Audited (`checkModuleAxioms`):** `73`
- **Git Blob SHA:** `f18c0e0bd514dc4b0de0d72aa776909be0f5e9a9`
- **SHA-256:** `49a3a91cf429692d530c5ba3eb49d4f1d2303b2c15d6ecedaea6cc1431b4be9d`
- **Key Declarations (`namespace Rudin.PMA.Chapter10`):**
  - `affScalePt` (`:28`), `planarDx_comp_affScalePt` (`:72`), `planarDy_comp_affScalePt` (`:102`), `integral_2d_affScalePt` (`:155`): Exact 2D affine rescaling `(x, y) ↦ ((x - a) / r, y / r)` on `[a, a + r] × [0, r]`, coordinate-partial chain rules, and `r²` Jacobian identity for iterated interval integrals.
  - `boxA` (`:183`), `boxR` (`:186`), `boxB` (`:189`), `boxC` (`:192`), `boxD` (`:195`), `boxEps` (`:198`), `boxK` (`:204`), `hBox` (`:207`), `uBox` (`:211`), `glidingHumpF` (`:215`): Pairwise disjoint closed dyadic sub-squares `[2^{-(m+1)}, 5 · 2^{-(m+3)}] × [0, 2^{-(m+3)}] ⊂ [0, 1]²` accumulating only at `(0, 0)`, weights `ε_m = 1 / (m + 1) > 0`, rescaled witnesses `(uBox m, hBox m)` at depth `K_m = 3 (m + 1)²`, and global gliding-hump sum `glidingHumpF p = ∑' m, boxEps m * hBox m p`.
  - `contDiff_glidingHumpF` (`:695`): Proof of `ContDiff ℝ 1 glidingHumpF` on all of `ℝ²` via local finiteness away from `(0, 0)` (`glidingHumpF_eventuallyEq_sum_of_ne_zero`, `:509`), `HasFDerivAt` at `0` with zero derivative (`hasFDerivAt_glidingHumpF_zero`, `:602`), and uniform `1 / (M + 1)` decay of `‖fderiv ℝ glidingHumpF‖` near `0` (`norm_fderiv_glidingHumpF_le_inv_succ`, `:637`).
  - `not_pma10_43_contract` (`:905`): Exact unweakened unconditional statement
    ```lean
    theorem not_pma10_43_contract : ¬ pma10_43_contract
    ```
    instantiating `not_pma10_43_contract_of_spin3_gliding_hump` (`PMA1043Stage4B1.lean:1320`).

---

## §4. Scope Verification

- Diff against `origin/main` (`a14501c8d22a63d6b84584dbe5cdc5a94053b18b`) adds **only** the four authorized files:
  - `A  STAGE4B1-REPORT.md`
  - `A  rudin/Rudin/Research/Stage4B1Disproof.lean`
  - `A  rudin/Rudin/Research/Stage4B1Staircase.lean`
  - `A  rudin/Rudin/Research/Stage4B1Waves.lean`
- Zero existing `.lean` files, `lakefile.toml`, `lake-manifest.json`, `lean-toolchain`, `Rudin.lean`, or prior reports were modified.

---

## §5. Verification Evidence Summary

1. **`git diff --check origin/main..HEAD`:** Exit `0` (verified on staged index prior to commit and re-verified on `origin/main..HEAD` post-commit).
2. **Clean-Slate `lake build` (`build-stage4b1-clean-slate.log`):**
   - Command (after `rm -rf rudin/.lake/build`, retaining symlink `rudin/.lake/packages -> /root/lean-cache/mathlib-d13f23b7/packages`, never running `lake exe cache get`):
     `lake build Rudin.Research.Stage4B1Waves Rudin.Research.Stage4B1Staircase Rudin.Research.Stage4B1Disproof Rudin.PMA.Chapter10.FtildeCZPrep Rudin.Research.PMA1043Stage4B1 Rudin.PMA.Chapter10.FtildeDisproofStatement`
   - Exit code: `0`
   - `error:` lines: `0`
   - `sorry` warnings: `0`
   - Verbatim log tail (`build-stage4b1-clean-slate.log`, lines 1,452–1,462):
     ```text
     info: Rudin/Research/Stage4B1Staircase.lean:4145:0: Axiom audit module Rudin.Research.Stage4B1Staircase: checked 238 declarations.
     info: Rudin/Research/Stage4B1Staircase.lean:4145:0: Axiom audit for Rudin.Research.Stage4B1Staircase: checked 238 declarations in 1 modules; axioms used: [propext,
      Classical.choice,
      Quot.sound]; no forbidden axioms.
     ℹ [9077/9077] Built Rudin.Research.Stage4B1Disproof (9.6s)
     info: Rudin/Research/Stage4B1Disproof.lean:919:0: Axiom audit coverage: Rudin.PMA.Chapter10.not_pma10_43_contract (module Rudin.Research.Stage4B1Disproof); axioms used: [propext,
      Classical.choice,
      Quot.sound].
     info: Rudin/Research/Stage4B1Disproof.lean:919:0: Axiom audit module Rudin.Research.Stage4B1Disproof: checked 73 declarations.
     info: Rudin/Research/Stage4B1Disproof.lean:919:0: Axiom audit for Rudin.Research.Stage4B1Disproof: checked 73 declarations in 1 modules; axioms used: [propext,
      Classical.choice,
      Quot.sound]; no forbidden axioms.
     Build completed successfully (9077 jobs).
     ```
3. **Axiom Audit (`audit-stage4b1.log`):**
   - Exit code: `0`, `sorryAx` occurrences: `0`
   - Verbatim summary lines from `audit-stage4b1.log`:
     ```text
     Rudin.PMA.Chapter10.not_pma10_43_contract : ¬Rudin.PMA.Chapter10.pma10_43_contract
     Rudin.PMA.Chapter10.pma10_43_contract : Prop
     Axiom audit module Rudin.Research.Stage4B1Waves: checked 101 declarations.
     Axiom audit for Rudin.Research.Stage4B1Waves: checked 101 declarations in 1 modules; axioms used: [propext, Classical.choice, Quot.sound]; no forbidden axioms.
     Axiom audit module Rudin.Research.Stage4B1Staircase: checked 238 declarations.
     Axiom audit for Rudin.Research.Stage4B1Staircase: checked 238 declarations in 1 modules; axioms used: [propext, Classical.choice, Quot.sound]; no forbidden axioms.
     Axiom audit module Rudin.Research.Stage4B1Disproof: checked 73 declarations.
     Axiom audit for Rudin.Research.Stage4B1Disproof: checked 73 declarations in 1 modules; axioms used: [propext, Classical.choice, Quot.sound]; no forbidden axioms.
     'Rudin.PMA.Chapter10.not_pma10_43_contract' depends on axioms: [propext, Classical.choice, Quot.sound]
     'Rudin.PMA.Chapter10.pma10_43_contract' depends on axioms: [propext, Classical.choice, Quot.sound]
     'Rudin.PMA.Chapter10.not_pma10_43_contract_of_spin3_gliding_hump' depends on axioms: [propext, Classical.choice, Quot.sound]
     'Rudin.PMA.Chapter10.antiperiodic_haar_shift_bound_1d' depends on axioms: [propext, Classical.choice, Quot.sound]
     'Rudin.PMA.Chapter10.spin3_three_ray_obstruction' depends on axioms: [propext, Classical.choice, Quot.sound]
     ```
4. **`lake env leanchecker` Kernel Replay:**
   - `lake env leanchecker Rudin.Research.Stage4B1Waves`: exit `0`
   - `lake env leanchecker Rudin.Research.Stage4B1Staircase`: exit `0`
   - `lake env leanchecker Rudin.Research.Stage4B1Disproof`: exit `0`
5. **Raw Case-Insensitive Forbidden-Token Grep Across the Three New `.lean` Files:**
   - `sorry`: `0`
   - `admit`: `0`
   - `native_decide`: `0`
   - `bv_decide`: `0`
   - `sorryAx`: `0`
   - `axiom` (as a declaration): `0` (raw case-insensitive substring `axiom` occurs `3` times solely in `Rudin.PMA.Audit.checkModuleAxioms` at `Stage4B1Waves.lean:932`, `Stage4B1Staircase.lean:4146`, `Stage4B1Disproof.lean:920`)
   - `unsafe`: `0`
   - `implemented_by`: `0`
   - `ofReduceBool`: `0`
6. **Summary Table of Counts:**

| Module | File Path | Lines | Declarations (`checkModuleAxioms`) | Git Blob SHA |
|---|---|---:|---:|---|
| `Rudin.Research.Stage4B1Waves` | `rudin/Rudin/Research/Stage4B1Waves.lean` | `951` | `101` | `8149c2a4c37bdc7481e31bf44fcc8bac2eae58fd` |
| `Rudin.Research.Stage4B1Staircase` | `rudin/Rudin/Research/Stage4B1Staircase.lean` | `4,162` | `238` | `3781466bb698a833fea10164ac09f9a70e0a0786` |
| `Rudin.Research.Stage4B1Disproof` | `rudin/Rudin/Research/Stage4B1Disproof.lean` | `921` | `73` | `f18c0e0bd514dc4b0de0d72aa776909be0f5e9a9` |

---

## §6. Delivery & Review Status

- **Branch:** `coordinator/rudin29-stage4b1` (based on `main` `a14501c8d22a63d6b84584dbe5cdc5a94053b18b`).
- **Commit / PR Metadata Note:** Because a Git commit cannot embed its own commit SHA or a post-push PR number inside a tracked blob, the exact pushed `HEAD` SHA and draft PR number are recorded in the enclosing commit/PR metadata and in the task-directory deliverable `/root/projects/rudin/tasks/carbon-rudin1043-stage4b1-20261112/STAGE4B1-REPORT.md`.
- **Crossed Review Status:** No independent crossed review has run yet; this lane opens a draft PR only for coordinator-dispatched crossed review.

STAGE4B1 COMPLETE.
