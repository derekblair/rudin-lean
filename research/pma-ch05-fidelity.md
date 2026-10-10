# PMA Chapter 5 Fidelity Review — Differentiation

## Current verdict

**Isolated preparation: all 19 nodes proved and independently accepted.** The later independent source review is preserved at `../evidence/pma-ch05-source-review.md`. The historical prior-art evidence below is retained unchanged. The assembled isolated chapter passes the default build and recursive axiom audit (267 declarations, including nine standalone probes). Production integration is now verified on a local branch after fresh hostile reviews; see `pma-ch05-production-review.md`. No push was performed. A pinned baseline default build passed in the isolated workspace (see `../evidence/baseline-build.log`).

Historical pre-proof plan (subsequently completed): Chapter 4 was closed before Chapter 5 extraction began. The next review stages were independent acceptance of the Chapter 5 source inventory, followed by back-translation and typechecking of the actual statement contracts before proofs begin. The root agent retains ownership of production modules and git operations.

## Bounded prior-art check

Checked live primary GitHub sources on 2026-10-10, before beginning Chapter 5 extraction or formalization. Retrieval window: 2026-10-10T07:10:39.590069+00:00 through 2026-10-10T07:11:01.631820+00:00.

**Finding:** substantial adjacent differentiation material already exists. The inspected Rudin-specific repository trees did not expose a dedicated differentiation chapter. This is a bounded source-availability observation, not a novelty claim, exhaustive absence claim, or certification of any external project's correctness, completeness, axiom discipline, or fidelity to Rudin. Authorization to complete this corpus remains in force despite overlap.

### Method and bounds

Ran six public web searches, then independently resolved nine public repository default-branch HEADs using `git ls-remote ... HEAD`. Retrieved complete recursive GitHub API trees pinned to those commits. Also resolved ReasBook's live branch references and inspected its v4.30.0 release tree. All ten API responses reported `truncated: false`. The search indexes were noisy and are discovery aids only; the findings below are grounded in the pinned primary trees and source files.

Fetched and inspected focused headers/declarations in 17 source files: four ATLAS derivative files, four Spivak chapters, five Tao companion sections, and four ReasBook/Lebl sections. No external repository was built, imported into the corpus, or axiom-audited. Source presence and declaration names do not certify statement equivalence to PMA Chapter 5. This landscape pass performed no Chapter 5 inventory extraction or formal statement work.

Search queries:

- `site:github.com Rudin Lean differentiation Chapter 5`
- `site:github.com Neuron-Group RudinAnalysis differentiation`
- `site:github.com optpku ReasBook differentiation derivatives Lean`
- `site:github.com "Rudin" "Lean" "derivative"`
- `site:github.com/facebookresearch/atlas-lean "Differentiation"`
- `site:github.com "Principles of Mathematical Analysis" "Lean" "5"`

### Pinned repository evidence

| Repository snapshot | Commit | Lean paths | Observed scope |
|---|---|---:|---|
| [Neuron-Group/RudinAnalysis](https://github.com/Neuron-Group/RudinAnalysis/tree/a54a65f57ea2bd77922bc7c9b55908e3db241aef) | `a54a65f57ea2bd77922bc7c9b55908e3db241aef` | 19 | 19 Lean paths cover number systems, basic topology, and numerical sequences/series; no dedicated differentiation path appears in the inspected tree. |
| [sinianluoye/LeanOfRudinAnalysis](https://github.com/sinianluoye/LeanOfRudinAnalysis/tree/a40f25c4a9f2f78e01c52077d7cbe5c05f7b0386) | `a40f25c4a9f2f78e01c52077d7cbe5c05f7b0386` | 20 | 20 Lean paths contain Chapter 1 and supporting definitions/commands; no Chapter 5 path appears. |
| [Splines/lean-continuous](https://github.com/Splines/lean-continuous/tree/823a4c93a1d2eadc42ce86e0f1ecbec99f5133a2) | `823a4c93a1d2eadc42ce86e0f1ecbec99f5133a2` | 5 | Five Lean files cover continuity, algebra, examples, and sided continuity; no differentiation module appears. |
| [drisspg/lean_ua](https://github.com/drisspg/lean_ua/tree/21d5aff3f597e2610e418b4146ada591abd7ffae) | `21d5aff3f597e2610e418b4146ada591abd7ffae` | 7 | Seven Lean paths include only Chapter 1 and Chapter 2 directories, plus support/root files. A README chapter plan is not evidence of implemented Chapter 5 source. |
| [optpku/ReasBook](https://github.com/optpku/ReasBook/tree/32fe9c0f542ccc499b7011166d26ddf42872b2ca) | `32fe9c0f542ccc499b7011166d26ddf42872b2ca` | 18 | Default-branch tree contains the catalog/build layer; the separately inspected v4.30.0 release contains Lebl differentiation source. |
| [facebookresearch/atlas-lean](https://github.com/facebookresearch/atlas-lean/tree/3ad834a66cc5d1a4f923326fcb673b14a25e198b) | `3ad834a66cc5d1a4f923326fcb673b14a25e198b` | 12565 | 12,565 Lean paths include four explicit real-analysis derivative modules: Basic, MVT, Taylor, and Weierstrass. No inspected path contains Rudin. |
| [stormj-UH/spivak-lean](https://github.com/stormj-UH/spivak-lean/tree/c24e9fcb7e96873ea9d4769c453be1b3ca48d211) | `c24e9fcb7e96873ea9d4769c453be1b3ca48d211` | 162 | 162 Lean paths include Chapters 9–11 on derivatives and their consequences and Chapter 20 on Taylor approximation, with associated source/audit/problem modules. |
| [vltanh/lean4-analysis-tao](https://github.com/vltanh/lean4-analysis-tao/tree/bac39612b3745469e620212947a573eb91154166) | `bac39612b3745469e620212947a573eb91154166` | 14 | 14 Lean paths cover natural numbers, set theory, and support; no differentiation module appears. |
| [teorth/analysis](https://github.com/teorth/analysis/tree/2c165a0da64f1b2c8a0000600bc464ec77671c7a) | `2c165a0da64f1b2c8a0000600bc464ec77671c7a` | 109 | 109 Lean paths include Section_10_1 through Section_10_5, covering derivative definitions/rules, extrema/MVT, monotonicity, inverse derivatives, and l’Hôpital statements. |
| [ReasBook v4.30.0](https://github.com/optpku/ReasBook/tree/f9674e6420188b5921fdbff7917aaf0e10cfa8a0) | `f9674e6420188b5921fdbff7917aaf0e10cfa8a0` | 5070 | Lebl Volume I Chapter 4 has four differentiation sections. Focused declarations include derivative arithmetic, chain rule, Rolle, mean value/Cauchy mean value, Darboux, Taylor remainder, and inverse derivatives. |

### Focused source evidence

- ATLAS: [Basic](https://github.com/facebookresearch/atlas-lean/blob/3ad834a66cc5d1a4f923326fcb673b14a25e198b/v1/Atlas/RealAnalysis/code/Derivatives/Basic.lean#L15) contains a difference-quotient limit comparator and chain rule; [MVT](https://github.com/facebookresearch/atlas-lean/blob/3ad834a66cc5d1a4f923326fcb673b14a25e198b/v1/Atlas/RealAnalysis/code/Derivatives/MVT.lean#L35) contains named Fermat, Rolle, mean value, zero-derivative constancy, and derivative-monotonicity declarations. [Taylor](https://github.com/facebookresearch/atlas-lean/blob/3ad834a66cc5d1a4f923326fcb673b14a25e198b/v1/Atlas/RealAnalysis/code/Derivatives/Taylor.lean#L31) contains a Lagrange-remainder statement with explicit regularity assumptions; [Weierstrass](https://github.com/facebookresearch/atlas-lean/blob/3ad834a66cc5d1a4f923326fcb673b14a25e198b/v1/Atlas/RealAnalysis/code/Derivatives/Weierstrass.lean#L295) contains a nowhere-differentiability declaration. These are topic overlap, not a Rudin-numbered chapter certification.
- Spivak: [Chapter 9](https://github.com/stormj-UH/spivak-lean/blob/c24e9fcb7e96873ea9d4769c453be1b3ca48d211/SpivakCalculus/Chapter09.lean#L25) defines derivatives through its own limit predicate and includes differentiability/continuity examples. [Chapter 10](https://github.com/stormj-UH/spivak-lean/blob/c24e9fcb7e96873ea9d4769c453be1b3ca48d211/SpivakCalculus/Chapter10.lean#L165) includes quotient and chain rules. [Chapter 11](https://github.com/stormj-UH/spivak-lean/blob/c24e9fcb7e96873ea9d4769c453be1b3ca48d211/SpivakCalculus/Chapter11.lean#L125) includes Rolle/MVT and a finite zero-over-zero l’Hôpital statement; [Chapter 20](https://github.com/stormj-UH/spivak-lean/blob/c24e9fcb7e96873ea9d4769c453be1b3ca48d211/SpivakCalculus/Chapter20.lean#L381) includes Taylor remainder statements. Only the indicated files and declarations were inspected here; README completion claims were not adopted as independently checked facts.
- ReasBook release: [Lebl §4.1](https://github.com/optpku/ReasBook/blob/f9674e6420188b5921fdbff7917aaf0e10cfa8a0/ReasBook/Books/IntroductiontoRealAnalysisVolumeI_JiriLebl_2025/Chap04/section01.lean#L14) contains difference-quotient definitions and derivative rules. [Lebl §4.2](https://github.com/optpku/ReasBook/blob/f9674e6420188b5921fdbff7917aaf0e10cfa8a0/ReasBook/Books/IntroductiontoRealAnalysisVolumeI_JiriLebl_2025/Chap04/section02.lean#L616) contains extrema, Rolle/MVT/Cauchy MVT, monotonicity, and Darboux declarations. [Lebl §4.3](https://github.com/optpku/ReasBook/blob/f9674e6420188b5921fdbff7917aaf0e10cfa8a0/ReasBook/Books/IntroductiontoRealAnalysisVolumeI_JiriLebl_2025/Chap04/section03.lean#L257) contains Taylor remainder and second derivative tests; [Lebl §4.4](https://github.com/optpku/ReasBook/blob/f9674e6420188b5921fdbff7917aaf0e10cfa8a0/ReasBook/Books/IntroductiontoRealAnalysisVolumeI_JiriLebl_2025/Chap04/section04.lean#L14) contains inverse derivative statements. No source-fidelity equivalence was inferred from shared theorem names.
- Tao companion: [§10.1](https://github.com/teorth/analysis/blob/2c165a0da64f1b2c8a0000600bc464ec77671c7a/Analysis/Section_10_1.lean#L28), [§10.2](https://github.com/teorth/analysis/blob/2c165a0da64f1b2c8a0000600bc464ec77671c7a/Analysis/Section_10_2.lean#L82), [§10.3](https://github.com/teorth/analysis/blob/2c165a0da64f1b2c8a0000600bc464ec77671c7a/Analysis/Section_10_3.lean#L20), [§10.4](https://github.com/teorth/analysis/blob/2c165a0da64f1b2c8a0000600bc464ec77671c7a/Analysis/Section_10_4.lean#L24), and [§10.5](https://github.com/teorth/analysis/blob/2c165a0da64f1b2c8a0000600bc464ec77671c7a/Analysis/Section_10_5.lean#L24) supply nearby formal statements. The inspected files contain `sorry` placeholders, so their inclusion is evidence of adjacent statements/companion coverage, not completed proofs.

The complete path lists, retrieval timestamps, and fetched source snapshots are retained locally under `/tmp/pma-ch05-landscape/` for reproducibility. They are review inputs only; nothing was added to the repository's Lean modules or git history.

## Source inventory review

The later independent review accepted all 19 informal inventory nodes and attached consequences. Its verdict applies to the source inventory only, not to Lean statement/proof completion. See `../evidence/pma-ch05-source-review.md`.

## Formal statement review

All definitions and proposition conjuncts were reviewed against the accepted inventory before proof; fresh reviewers then accepted all six final node groups. The seven assembly inputs preserve reviewed declarations/proofs verbatim apart from moving imports and omitting diagnostic print commands. See `pma-ch05-checks.md` and `../evidence/ch05-assembly.json`.

## Final verification

Passed in isolated preparation: nineteen principal theorems, independent boundary probes, default build (8,946 jobs), source/coverage/metadata checker (19/19, zero queued), and recursive audit of 267 chapter declarations including nine standalone probes. Only `propext`, `Classical.choice`, and `Quot.sound` occur. Final build evidence: `../evidence/ch05-final-build.log`. This does not claim production integration, publication, or textbook-order restrictions on the underlying Mathlib proofs.

## Production integration update

The exact reviewed source has now been integrated with local section commits,
per-commit default builds and recursive axiom audits. Fresh hostile reviews
cover all nineteen nodes independently of their authors. Production evidence
is recorded separately in `pma-ch05-production-review.md`; historical isolated
results above retain their original context. No remote publication occurred.
