# Crossed-pool review record: PMA 10.43 endpoint obstruction (ticket #14)

- Reviewer: Claude (Fable 5.1) on dominic, independent of the author pool (Codex chatgpt-live on bakkie).
- Final reviewed commit: `31b5b5d424f9c13d5a699831e602ff2bfab83c67` on `research/t14-1043` (draft PR #21). It is one documentation-only commit above the initially reviewed `c1c787a5bde7d8034ebdfe2ff010326ee7e3d7a9`, which is one commit above base `05c9ea2f709ce854be0b794350a818d9ebd102f8`.
- Verdict, obstruction-report category: **PASS**. No blocking findings at either commit.
- The exact endpoint, existence of a C² vector potential for every admissible C¹ divergence-free field, is neither proved nor disproved. Node 10.43 remains incomplete; this record does not change its status and authorizes no merge.
- Dates: initial review and documentation-delta review both 2026-10-26.

## Reviewed bytes (SHA256 at the final commit)

- `research/pma10-43-endpoint-obstruction.md`: `b92ab68ff76462cf267f74caeebe2408d3a96c2e7fccdf4cd444b89a0a4f9def`
- `rudin/Rudin/Research/PMA1043Gauge.lean`: `26c333e354005b10c76eef9cd73c14b102f0c01fb2215f543068401abf9808ee`
- `rudin/Rudin/Research/PMA1043Planar.lean`: `3baaef4ddb44caeb6ee3cc78ebe2cb22bfd338830d90af0c0b5d5e681edc746f`
- `research/pma10-43-axioms.lean`: `194924febb5ffa7004c74ca6fddb726e745ed7deb12de9ea7605f31b4ebdffd2`
- Complete initial review on dominic, `/tmp/t14-dominic-review.md`: `72272b178e43105890e6e99d25396f2db9e6f762dc51109cb3dbdcde0c1e652e`

## Scope of the documentation-delta review

`git diff c1c787a..31b5b5d` touches only the report: five single-paragraph edits, 5 insertions and 5 deletions, 179 lines before and after. The two Lean modules and the axiom file have identical git blobs at both commits. The contract in `VectorPotentials.lean`, the Chapter 10 tree and its audits, the original blocker record, and the build files are byte-identical to base. Nothing in the default target imports `Rudin.Research`. Because no checked byte changed, no build or axiom check was repeated for the delta.

The five edits are accurate and acceptable, and introduce no new mathematical claim:

1. The §3 Poisson lemma now states that the m-th derivative tensor of v_m equals (D^m P_m) log t plus O(1/t), with D^m P_m a nonzero constant tensor, so v_m is not C^m. This is the correct, direction-independent statement.
2. §5 now says that variable angular profiles and simultaneous radial/angular irregularity lie outside the fixed-profile estimates rather than defeating them, and that neither establishes failure in every gauge.
3. The Dacorogna-Fusco-Tartar citation now discloses that the full article was not fetched and that the crossed reviewer could not retrieve the abstract, and that the citation is contextual and used in no proof.
4. The Costabel-McIntosh order −1 result is now attributed to their Theorem 3.2, which matches the preprint.
5. The closing paragraph records the initial crossed PASS at `c1c787a` and its limits faithfully.

## Initial independent checks at c1c787a, and their limits

Kernel: both research modules were re-elaborated with Lean 4.34.1 against oleans built from sources byte-identical on the full 143-module import closure of the contract module, with the same toolchain and Mathlib revision. The axiom file printed exactly `propext`, `Classical.choice`, `Quot.sound` for all 32 theorem and lemma declarations, and those 32 targets are exactly the declarations of the two modules. The full default `lake build` was not independently rerun; the change is additive and outside the default target's import closure.

Mathematics: every informal argument was re-derived by hand, and the calculus identities of §§1, 3 and 5 were confirmed by finite differences with relative errors at or below 2e-7. Source fidelity was re-checked against printed PMA pp. 280-282: clause (b′) prints a potential of class C″, 10.40 defines C″-equivalence as the report states, and the repository's curl, divergence and two-form orientation match the printed definitions. McMullen's Theorem 2.1, Costabel-McIntosh's Theorem 3.2, Corollary 3.4, Remark 3.5 and Proposition 4.1, and the Dini integral before Berselli-Longo's Theorem 16 were verified from the papers. The Dacorogna-Fusco-Tartar abstract was unreachable from a primary record and is used in no proof.

## Key results by evidence class

Kernel-proved reductions, standard axioms only:

- On the contract's domains, two C¹ potentials of one field differ by the gradient of a C² scalar; a C² potential exists iff some C² scalar gauge regularizes a given C¹ primitive; a C³ gauge cannot repair a non-C² primitive; the unchanged four-clause contract is equivalent to this gauge-regularization statement.
- On full space, a C² vector potential for the vertical field (0,0,f) exists iff f has a C² planar divergence solution, with no restriction on the z-dependence of the gauge; the contract implies C² planar divergence solvability for every globally C¹ datum; a datum with no C¹ divergence solution has no C¹ coordinate antiderivative.

Informal constructions, checked but not formalized:

- For data of the form (P_m/r²) q_m(log(1/r)) with P_m a harmonic homogeneous polynomial of degree m, no C^m Poisson solution exists near zero, by degree-m spherical projection. The cubic case gives an admissible C¹ divergence-free field on a convex ball that has an explicit C² potential but no C² Coulomb-gauge potential, even locally. Coulomb and Poisson-normalization routes therefore cannot prove the clause.
- Partition-of-unity patching shows the global C² clause on any contract domain is equivalent to a local statement on Euclidean balls, using the C² equivalence only through the already proved global C¹ primitive.
- Explicit C² solutions exist for the logarithmic planar candidate families, and the fixed radial homotopy operator genuinely loses a derivative on a field that nevertheless has a C² potential.

Unresolved: existence of some C² potential for every admissible field, equivalently the local ball statement, equivalently gauge regularization. The report makes no claim about the literature status of this question.

## Findings

No blocking findings. The initial review's nonblocking items, a §3 wording nit, the unnumbered Theorem 3.2, and the unverified abstract, are addressed by the delta. Two informational items need no action: the helper lemma `coordinatePartial_neg_planar` is unused, and §0 cites the book at a machine-specific path.

## Pre-existing provenance failure

`scripts/verify_ch10_integration.py` exits 1 at the final commit with exactly 19 "Reviewed bytes changed" errors and no inventory, principal-count, reachability or forbidden-token error, reproduced in this review. All 19 files are byte-identical to base, so the failure predates this branch and belongs in its own ticket.

## Recommendation

Land as an obstruction report. Do not mark node 10.43 complete.
