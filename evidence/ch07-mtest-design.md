# PMA 7.10 M-test and converse design

The typed `pma7_10_contract` was copied verbatim from the independently accepted
`Chapter07FoundationsDraft.lean` contract block. It compiled before proof work.
The principal hypotheses remain a bound by a real majorant and convergence of
its **ordered** partial sums. There is no additional nonnegativity assumption,
nonempty-domain assumption, or unconditional complex-series substitution.

On a nonempty domain, the common norm bound at one point proves every majorant
term nonnegative. The already verified Chapter 3 theorem
`seriesConverges_iff_summable_nonneg` then justifies using the pinned uniform
M-test `tendstoUniformlyOn_tsum_nat`. Its finite-range sums are definitionally the
accepted ordered partial sums. On an empty domain, uniform convergence is
vacuous and the proof supplies the zero function without deriving any majorant
sign condition.

The converse witness is a complex-valued function series on `Unit`, constant in
the domain variable and equal to the real alternating harmonic sequence embedded
in `ℂ`. The already verified `Chapter03.alternatingHarmonic_converges` supplies an
ordered real limit. Continuity of the embedding and its finite-sum identity give
the ordered complex limit; the sequence of constant functions is uniformly
convergent. Any purported convergent norm majorant would be nonnegative and
summable, hence force absolute summability of the alternating harmonic series,
contradicting `Chapter03.alternatingHarmonic_not_absolute`. Thus conditional
ordered convergence is retained where essential to the counterexample.

The proof author did not modify Basic, Foundations, Chapter 3, shared metadata,
production, dependencies or configuration. Independent final review and the
later hostile gate are separate from this author design record.

## Completed proof delivery

Canonical module: `rudin/Rudin/PMA/Chapter07/MTest.lean` (66 lines), SHA256
`c364dc78a12a188264c39c24f8dfd5da1edc699491442d18cf78b2565aef3e05`.
The final draft is byte-identical, and the accepted contract block was compared
programmatically and retained verbatim. Direct compilation and the canonical
module build passed without warnings or errors; the build reported 8,928 jobs.
`#print axioms pma7_10` reports only the three permitted axioms.

The fresh `Chapter07MTestAuditScratch.lean` client checks the empty-domain case
without a majorant sign premise and the exact full converse assertion. Its final
run passed and recursively audited 17 imported Chapter 7 namespace declarations
using only `propext`, `Classical.choice`, `Quot.sound`. The second conjunction is
closed but the combined theorem also has a domain-universe parameter; clients
using that projection alone should write `pma7_10.{0}.2` or use the direct theorem
`mTest_converse_failure`. An initial client elaboration left that universe
unresolved; the final explicit-universe client passed without any proof-source
change. A stripped-source scan found no prohibited token.

No accepted conjunct is queued or omitted. Independent final source review is
requested separately and is not replaced by this author's validation record.
