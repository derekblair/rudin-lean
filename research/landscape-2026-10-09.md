# Textbook/Subfield Formalization in Lean 4 — Landscape as of Oct 9, 2026

Facts only, verified via web search. "Complete" means every theorem (and, where noted, every exercise/problem) is machine-checked.

## A. Complete textbook formalizations

| Project | Book / subfield | Who | Coverage | Date / status | Repo |
|---|---|---|---|---|---|
| RepoProver / Algebraic Combinatorics | Darij Grinberg, *An Introduction to Algebraic Combinatorics* (grad textbook, arXiv:2506.00738) | Meta FAIR — Gloeckle, Rammal, Arnal, Munos, Cabannes, Synnaeve, Hayat | 340 of 344 target theorems (4 correctly identified as exercises); 45 chapters; ~130,000 lines; ~5,900 declarations; 52 files; Lean 4.28.0; blueprint site | Paper "Automatic Textbook Formalization" dated 2026-03-31 (arXiv 2604.03071, 2026-04-03); built in ~1 week by ~30,000 parallel Claude Opus 4.5 agents; cost ~$100k (survey estimate) | https://github.com/facebookresearch/repoprover (scaffold) · https://github.com/facebookresearch/algebraic-combinatorics (formalization) |
| SpivakCalculus | Michael Spivak, *Calculus* — both 3rd (1994) and 4th (2008) editions | Individual (stormj-UH) | 100%: all 30 chapters + 9 appendices; every theorem AND every problem, every lettered part; 9,110 declarations audited to use only propext/Classical.choice/Quot.sound; ~115,360 lines; 0 sorry/axiom/native_decide; includes transcendence of e (proved twice) and π | Completed late Sept 2026 (final write-up 2026-09-26) | https://github.com/stormj-UH/spivak-lean |
| basic-category-theory-lean4 | Tom Leinster, *Basic Category Theory* (arXiv:1612.09375) | Individual (whoiam1101) | 100% — 6/6 chapters; 0 sorries; standard axioms only; Lean 4.30.0 | Completed; last activity ~mid-Aug 2026 | https://github.com/whoiam1101/basic-category-theory-lean4 |

## B. Substantial / in-progress textbook formalizations

| Project | Book / subfield | Who | Coverage | Date / status | Repo |
|---|---|---|---|---|---|
| teorth/analysis | Terence Tao, *Analysis I* — Tao's own Lean companion | Terence Tao (UCLA) | Partial: §§2.1–2.3, ch.2 epilogue, 3.1, 4.1–4.3, 5.1–5.4; uses Mathlib from ch.3 onward; exercises left as sorry; ~1,481 theorems per 2026-09 harvest | Announced 2026-05-31 on Tao's blog; active | https://github.com/teorth/analysis |
| lean4-analysis-tao | Terence Tao, *Analysis I* (alternative take) | Individual (The-Anh Vu-Le / vltanh) | In progress: main text ch.2–11 + Appendices A, B (progress page updated 2026-04-14); NO Mathlib imports anywhere (rebuilds from Peano axioms); exercises also formalized | In progress | https://github.com/vltanh/lean4-analysis-tao |
| domain-theory-book-formalization | Samson Abramsky & Achim Jung, *Domain Theory* | Individual (chanyuxu) | In progress: ch.1–7 developing; interactive TeX-to-Lean reader covers ch.2–7 with 260 mapped definitions/props/lemmas/theorems/corollaries; remaining axiom/admit/sorry uses explicitly disclosed ("research preview", not proof-complete); Lean 4.30.0-rc2 | Active (updated ~Aug 2026) | https://github.com/chanyuxu/domain-theory-book-formalization |
| CLRS-Lean | Cormen et al., *Introduction to Algorithms* 4th ed. | TankTechnology org | Milestone 2026-09-08: 35/35 chapters "represented", 1,689 of 1,689 *selected* proof entries proved (+470 online-material entries); explicitly a selected core — NOT every theorem/exercise/pseudocode; no sorrys on main; Lean 4.32.0-rc1; Verso book site | Active (updated ~Sept 2026) | https://github.com/TankTechnology/CLRS-Lean |
| lean-scv | Several complex variables (subfield) | Individual (bjbraams) | 65 principal results (Cauchy/Taylor theory, Hartogs, Weierstrass, Cartan–Thullen, Bochner, plurisubharmonic, Runge…); every catalogued result proved; registered Palomar PALOMAR-2026-09-18-000008 v1; intended as Mathlib contribution | Active (updated ~Oct 5, 2026) | https://github.com/bjbraams/lean-scv |

## C. Scaled auto-formalization programs (breadth, not depth)

| Project | Scope | Who | Coverage | Date / status | Repo |
|---|---|---|---|---|---|
| ATLAS (Autoformalized Textbook Library At Scale) | Ug+grad textbooks across analysis, algebra, geometry, topology, combinatorics, probability, statistics, PDEs, number theory, TCS | Meta FAIR (follow-up to RepoProver) | LLM-generated (AutoformBot pipeline); per-book Lean sources + targets.yaml + report.json with automated faithfulness/proof-integrity scores; exact book list/coverage counts not publicly itemized | Companion paper "Formalizing Mathematics at Scale" (arXiv:2605.29955); repo active (updated ~Sept 30, 2026); visualizer at rammalahmad.github.io/atlas/ | https://github.com/facebookresearch/atlas-lean |
| ReasBook | Tao *Analysis II* (4th ed.), Rockafellar *Convex Analysis*, Lebl *Intro to Real Analysis*, Conforti–Cornuejols–Zambelli *Integer Programming* (+ research papers) | Peking University — Chenyi Li, Zichen Wang, Wanli Ma, Ziyu Wang; PI Zaiwen Wen; M2F autoformalization tool | Textbook-structured; ~290,000–300,000 LOC total; Lean 4.26.0 | Papers incl. arXiv:2403.11437, 2503.18806, 2503.18821, 2602.17016 | https://github.com/optpku/ReasBook |

## D. Adjacent large-scale formalizations (not textbooks, but occupying the same contested space)

- **FrenzyMath — Poincaré Conjecture** (https://github.com/frenzymath/Poincare-Conjecture): AI4M team (BICMR/Peking U.; Guoxiong Gao et al.). Lean 4 formalization following Morgan–Tian's *Ricci Flow and the Poincaré Conjecture*: ~3.2M lines completed in ~half a month at <$30k LLM+compute cost (frenzymath.com/news/poincare-formalization/). Its `formalized-sources/` tree includes source-faithful textbook sub-projects: **Hatcher *Algebraic Topology*** (Ch.0 published 2026-07-16, 0 sorries; blueprints for ch.0–1), **do Carmo *Riemannian Geometry***, **Petersen**, **Lee *Riemannian Manifolds***, **Lee *Smooth Manifolds***, **Topping**, **Chow–Knopf**, **Morgan–Tian**, **Cao–Zhu**, **Evans *PDE***, **Gilbarg–Trudinger**, **Thurston**. Active (updated ~Sept 28, 2026).
- **Anthropic — Fermat's Last Theorem** (https://github.com/anthropics/fermats-last-theorem): announced 2026-09-04. ~13M lines, 29,500 intermediate theorems, ~6B output tokens, 11 days on the Prove2Me platform (DAG of statements), led by Tianyi Peng; >5× Mathlib; verified by Kevin Buzzard; only Lean's three standard axioms; follows the Darmon–Diamond–Taylor exposition of Wiles. Token cost estimated ~$300k (secondary estimate). Also formalized Vinogradov's Three Primes Theorem in 3 days on consumer Claude Max plans.
- **Anthropic — Riemann zeta bound**: unreleased Claude research model raised the proven lower bound on zeta zeros on the critical line from 41.6% to 67.2% (67.25% simple + on the line); Lean-checked; ~60 subagents, ~650 candidate approaches, 31M tokens; reviewed by Brian Conrey, Dan Goldston, and two in-house mathematicians; not peer-reviewed as a math paper. Reported Aug 2026 (covered again Oct 2026). Youness Lamzouri published an alternative proof of the bound (preprint, 2026-09-08).

## Bottom line

As of Oct 2026, the only fully-completed canonical-textbook formalizations in Lean 4 are Grinberg (Meta, machine-generated), Spivak (individual), and Leinster (individual). Tao's *Analysis I* is covered twice but incompletely; CLRS, Domain Theory, Hatcher, and several complex variables are partially in flight; Meta's ATLAS is the only active program attempting many textbooks at once.

The "well-covered book" calibration lane is effectively closed for the obvious picks — anything famous is done, in progress, or inside ATLAS's blast radius.

## Rudin check (2026-10-09, at Derek's direction)

No systematic Lean 4 formalization of any Walter Rudin book exists (verified via web + GitHub search):
- *Principles of Mathematical Analysis* ("Baby Rudin"): only two tiny personal repos — sinianluoye/LeanOfRudinAnalysis (2 stars, last updated ~422 days ago, "learn analysis for fun" project) and Neuron-Group/RudinAnalysis (personal exam-review repo, "many processes in the proof may be slightly childish"). Plus a handful of Rudin exercises in the ProofNet benchmark (e.g. exercise 4.21a) and LaTeX solution repos (not Lean).
- *Real and Complex Analysis* ("Big Rudin"): zero formalization projects found — only citations in other projects' bibliographies.
- *Functional Analysis*: zero hits.
- Meta ATLAS book list is not publicly itemized — could not rule out Baby Rudin sitting in its undisclosed corpus. ATLAS is breadth-first LLM generation with automated faithfulness scores, a different artifact from a complete human-grade zero-sorry formalization.

Derek chose Rudin as the program's book family (2026-10-09). Recommendation: Baby Rudin first (fits the Phase 1 "well-covered book" calibration spec; Mathlib's analysis library covers the ground), pilot Chapter 3 (Numerical Sequences and Series), then Real and Complex Analysis → Functional Analysis with novelty increasing at each step.
