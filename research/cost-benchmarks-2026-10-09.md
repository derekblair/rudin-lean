# Cost/effort benchmarks for AI-assisted Lean formalization

Researched 2026-10-09. Cost bases differ across sources — see comparability caveats at the end.

## 1. Meta RepoProver — "Automatic Textbook Formalization" (Gloeckle et al. 2026)

Sources: the paper (arxiv.org/html/2604.03071); replication audit (github.com/emmaleonhart/replicating-automatic-textbook-formalization) — headline numbers independently reproduced (130,062 lines / 5,884 declarations / $429,025 no-cache / $100,149 cached / $14,025 output-token cost).

- 340 target theorems + definitions from Grinberg's *Introduction to Algebraic Combinatorics*, **340/340 proved** (100%)
- ~130,000 lines of Lean, ~5,900 declarations, 52 files, ~500 pages of source
- ~30,000 Claude 4.5 Opus agents over ~1 week; ~3,300 "successful agents"
- **Tokens: 83B input** (multi-counted dialog context) **+ 561M output**
- **Cost: ~$100K with prompt caching (back-of-envelope); $430K without.** Output-token cost alone ~$14K. Paper: "~$200 per page and $300 per target theorem or definition"
- ~50% of input tokens spent on *aborted* agents (early restarts, timeouts, thrashing)

Per-target: 561M / 340 ≈ **1.65M output tokens per target**; 83B / 340 ≈ 244M input tokens per target; $100K / 340 ≈ **$294 per target** (≈$17 per final declaration).

## 2. Anthropic FLT formalization (Sept 2026)

Source: Anthropic's research post (anthropic.com/research/formalizing-fermats-last-theorem), figures verified.

- 11 days; 13M lines of Lean; 29,500 intermediate theorems (30,300 proved, 29,500 used); ~6B output tokens from an internal model ~Claude Fable 5.1
- **$300K is a third-party list-price estimate, not Anthropic's figure** (6B × $50/M); internal cost "likely much cheaper"
- Per-theorem: 6×10⁹ / 29,500 ≈ **203,000 output tokens per intermediate theorem** (≈$10.17 at list price); 461 output tokens per line of Lean
- Lean 4.33.1, 60,475 modules; from-scratch `lake build` 5h32m at 96 jobs (peak 153 GB RAM); axioms exactly propext, Classical.choice, Quot.sound; independent Rust kernel (nanoda) checked 1,052,234 declarations; comparator confirmed the statement matches Mathlib's own FLT statement; failed early attempts ≈7% of non-boilerplate lines; Kevin Buzzard verified
- Follow-up: Vinogradov's Three Primes Theorem formalized in 3 days on three personal Claude Max plans

## 3. Other reported figures (2024–2026)

- **FirstProof benchmark (AI4M/PKU, arXiv:2602.05192):** 2 problems, zero-sorry, zero manual code, ~12,000 LOC — **~$1,950 total**
- **Clawristotle:** Vlasov-Maxwell-Landau steady-state theorem, ~10,445 LOC — **$200 subscription = $6,300 in tokens**
- **Prove2Me missions** (arXiv:2608.28433v2, Table 1 — warns costs not on a common basis): Exact Matrix Completion 81K LOC / $600 / 16 days; Sipser–Gács–Lautemann 55K LOC / $400 / 8 days; Bandit Algorithms textbook 151K LOC / $400 / 13 days; Intro to Linear Optimization 17K LOC / $200 / 7 days
- **LeanMarathon** (arXiv:2606.05400): 308M / 245M / 796M total tokens; $257 / $189 / $624 GPT-5.5-equivalent; 5,273 / 4,067 / 12,204 tool calls; agent active time up to 71h. One run caught a genuine gap in a published proof
- **LeanFlow** (arXiv:2607.20503v1): full pipeline in 1,043 / 1,278 API calls on two targets
- **GRD cost regimes** (statement-level only): cheap ~$0.01/claim; medium ~$0.10/claim; expensive ~$1–10/claim
- **Community note** (formal-foundry Zulip harvest): compute floor **$50–1,000 / up to 34h per hard target**; per-theorem repair loops "20–50+ rounds"
- **Aria (2025):** 91.6% compile / 68.5% faithful on ProofNet; flat NL2Lean baseline ~25–45% without retrieval

## 4. Formal-statement fidelity techniques ("does it say what the book says")

Consensus: faithfulness is "semi-decidable at best" — no metric replaces expert review; ReForm's ConsistencyCheck found human experts disagree with themselves 38.5% of the time on faithfulness labels.

1. **Back-translation** (arXiv:2511.12784, 2025): formal→informal via a second LLM, compare to original. SBERT cosine 62–78% on matched pairs. Coarse but catches gross drift. MerLean builds this in as a "Faithfulness Checking" stage.
2. **Symbolic equivalence + semantic consensus** (Liu et al. 2025, arXiv:2410.20936v1): multiple candidate statements, logical-equivalence clustering with Z3/Prover9. Catches quantifier-scoping bugs (∀∃ vs ∃∀ swaps that compile fine but are wrong).
3. **Reference-equivalence checking**: Anthropic's FLT comparator confirmed the statement matches Mathlib's own FLT statement. Works when a trusted reference exists.
4. **Prove-or-disprove fidelity** (formal-foundry harvest): needs no reference; reportedly catches ~25% of misformalizations.
5. **Metric-based ranking**: GTED (arXiv:2507.07399v1), ASSESS (arXiv:2509.22246), FormalAlign (arXiv:2410.10135) — moderate correlation with expert judgment; none replaces human review.
6. **Two-check discipline** (MathForm-8B): Syntax Check + Consistency Check reported separately — "a syntactically valid Lean statement that formalises the wrong theorem is worse than a compile error."
7. **Cheap static checks**: type-signature sanity, `#eval`/`decide` on concrete instances.
8. **Benchmarks for the problem itself**: IndiMathBench (Microsoft 2025) — statement-level faithfulness and hallucination detection.

## Comparability caveats

1. Cost bases differ: metered API (RepoProver $100K, FLT $300K est.) vs flat-rate subscriptions (Prove2Me $200–$600, Clawristotle $200→$6,300) — not on a common basis.
2. Token reporting differs: RepoProver reports input+output; Anthropic output only. Input multi-counting dominates RepoProver's 83B.
3. Caching assumptions: RepoProver's $100K is back-of-envelope with heavy prompt caching; uncached 4.3×.
4. Theorem granularity spans 3 orders of magnitude: 340 book targets vs 5,900 declarations vs 29,500 micro-lemmas. Per-theorem numbers are meaningless across this range without normalizing granularity.
5. Failed-work inclusion varies: ~50% of RepoProver input tokens on aborted agents; FLT ~7% of lines from failed runs.
6. Substrate differs: FLT leaned on Mathlib + Buzzard's blueprint + community infra; RepoProver's textbook was near-greenfield. Greenfield vs library-rich are different cost regimes.
7. $300K is not Anthropic's spend — third-party list-price estimate.
