# Chapter 6 integrability and algebra design

Owned draft: `rudin/Chapter06IntegrabilityDraft.lean`. All definitions use the accepted native closed-cell Darboux model in `Rudin.PMA.Chapter06.Basic`; no measure integral or mesh-limit definition is substituted.

## Accepted contracts

- 6.8: continuous integrands and arbitrary nondecreasing integrators, ordered intervals including equal endpoints.
- 6.9: both monotonicity directions for the integrand, and continuity of the nondecreasing integrator.
- 6.10: bounded integrand with finitely many relative discontinuities; integrator continuity is required only at those points. The attached shared-discontinuity caution is represented by the same left-continuous unit step used for both integrand and integrator on [-1,1].
- 6.11: continuous composition on a closed interval containing the original integrand's range.
- 6.12: all five parts, including arbitrary real integrand scaling, comparison, interior interval splitting, the absolute integral bound, and addition/positive scaling of integrators.
- 6.13: products, absolute-value integrability, and the absolute integral inequality.

The draft initially contained these concrete contracts only and typechecked cleanly. Root independently read and accepted all six contracts before proof implementation; their text has remained unchanged. A node with missing proof conjuncts remains incomplete; no source statement is weakened to accommodate proof difficulty.

## Planned proof dependencies

For 6.8, compact uniform continuity gives a partition with uniformly small oscillation; multiplying by nonnegative integrator increments and telescoping bounds the total Darboux gap. Combine this with the native epsilon-gap criterion from 6.6. Degenerate intervals have zero increments.

For 6.12, cell extrema bound sum/scalar integrands, common refinements combine epsilon-gap witnesses, and tagged or lower/upper sum bounds determine the resulting integral identities. Comparison and the absolute bound can be proved directly from native integral bounds. Interval splitting requires native partition concatenation/restriction, retaining repeated points.

For 6.11 and 6.13, use boundedness and continuous range composition, controlled cell oscillations, and the algebraic properties. For 6.9 and 6.10, construct partitions using uniform continuity of the integrator or small integrator variation near the finitely many exceptional points.

## Implemented and checked snapshot

The 558-line snapshot SHA256 is `001823e4c51a56b9c0d0afbe13801a757200178eac396081dec3b7abb91d5cec`. Running `./lake-local env lean Chapter06IntegrabilityDraft.lean` from the isolated workspace root exited **0**, with no warnings. Recursive axiom probes for `pma6_8`, `pma6_11`, `pma6_13`, `rsIntegrable_add`, `rsIntegrable_const_mul`, `rsIntegrable_integrator_add`, and `rsIntegrable_integrator_const_mul` each report exactly `[propext, Classical.choice, Quot.sound]`.

- **6.8 complete:** native equally spaced partitions permit repeated points and equal endpoints. Compact uniform continuity bounds cell oscillations; weighted sums telescope against the arbitrary nondecreasing integrator. Apply the native epsilon-gap criterion. Public helper: `rsIntegrable_of_continuousOn`.
- **6.11 complete:** compact uniform continuity of the outer function gives the pointwise estimate `|φ(u)-φ(v)| ≤ η + C|u-v|` on its range interval, for a suitable nonnegative C. Small distances use uniform continuity; large distances use its compact absolute bound. Transfer that estimate to cell oscillations and native Darboux gaps. This proof adds no continuity or measurability hypothesis to the integrand. Public helper: `rsIntegrable_comp`.
- **6.13 complete:** continuous square composition and the algebraic polarization identity prove product integrability. Absolute-value composition proves its integrability; integral comparison and negative scalar multiplication prove the absolute integral inequality. Public helpers: `rsIntegrable_mul`, `rsIntegrable_abs`.
- **6.12(a), (b), (d), (e) proved as helpers:** `rsIntegrable_add`, unary `rsIntegrable_const_mul` for arbitrary real scalars, `rsIntegral_mono`, `rsIntegral_abs_le_bound`, `rsIntegrable_integrator_add`, and unary `rsIntegrable_integrator_const_mul` for positive scalars. Every algebra helper includes the exact integral identity as well as integrability. Addition uses common refinements and cell-extrema bounds. Scaling uses native tagged sums and controlled Darboux gaps. No unrelated integrand or integrator premise is needed by either unary scaling helper.

**6.12 is not yet marked complete:** interval splitting (part c) is owned by the separate refinement author, and the complete `pma6_12` wrapper awaits that actual theorem. Root has taken over the proofs of 6.9 and the finite-discontinuity assertion of 6.10 in separate drafts. The jump author has already supplied the shared-step nonintegrability and explicit discontinuity witnesses for 6.10. Their accepted contracts remain in this draft for final assembly.

All writes in this assignment are limited to this draft and this design evidence. The shared project and source PDF were not changed or copied. Root owns module snapshots, integration, chapter audit, and any Git operations. Independent proof review of this snapshot remains a separate acceptance gate.

## Endpoint helper for the finite-discontinuity theorem

Root subsequently assigned the separate `rudin/Chapter06EndpointDraft.lean` and accepted its exact helper signature before implementation. Its completed 126-line snapshot SHA256 is `b4518141434d43a5d28f97944ba85b9af1c98cff1b19c910bddc2d4a70fe3e4b`. `./lake-local env lean Chapter06EndpointDraft.lean` exits **0**, with no warnings. Recursive axiom probes for both `endpoint_local_gap_lt` and `rsIntegrable_of_continuousOn_Ioo` report exactly `[propext, Classical.choice, Quot.sound]`. The source contains no proof placeholders, custom axioms, or native-decide use.

The main helper assumes a nondegenerate ordered interval, a bounded integrand, a nondecreasing integrator, continuity of the integrand on the open interval, and at each endpoint a disjunction: the integrand is relatively continuous there or the integrator is. It concludes native Riemann–Stieltjes integrability, without replacing either disjunction by integrator continuity.

The local lemma makes a short single-cell Darboux gap arbitrarily small when either function is continuous at its reference point. Integrand continuity gives a small cell oscillation times the globally bounded integrator increment. Integrator continuity gives a small increment times the globally bounded integrand oscillation. The main proof chooses disjoint short endpoint tails, uses 6.8 on the compact middle interval, and concatenates all three actual partitions with the proved native append-sum identities. Each gap is below one third of the requested error.

The helper is ready for root's finite induction over interior discontinuities. It is a proof dependency for 6.10, not an independent numbered source node and not by itself a completed proof of the full finite-discontinuity theorem.
