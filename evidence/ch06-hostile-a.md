# Chapter 6 hostile gate A: nodes 6.1–6.13

Verdict: **PASS — no blocking finding.** This is a new adversarial pass over actual final source bytes, separate from earlier fidelity review. All ten assigned support modules were read in full, including proof bodies and contract definitions. The final aggregator was read and its new `pma6_3` wrapper was included. No proof module or production file was modified.

## Frozen source hashes

- `Basic.lean`: `5192b99092c0fc7da7109b1e3ffd90446db62c73845b935172643456b46a3915` (215 lines).
- `Definitions.lean`: `13adade605f2cff6904a9b5d24f06057595d0c760abc140dfd7831608c5ccf81` (100 lines).
- `Refinement.lean`: `d1590f0b5df2fec5986358b6d84c255a4535a90df0ac70b8bc5f4bbec9c6fcb0` (256 lines).
- `Criterion.lean`: `e88daabe91d0ddd9145c79ff4aecbfd5c054b30fd27ea86c0a1b7743e3488715` (140 lines).
- `Integrability.lean`: `001823e4c51a56b9c0d0afbe13801a757200178eac396081dec3b7abb91d5cec` (558 lines).
- `Monotone.lean`: `93a69abdd3e242baa92eace347b551042157da49b4a83078e06abd469d832598` (76 lines).
- `Split.lean`: `d235d56777fc5e5a25db12e834769fd2192273d55a9d5921ceb80b857499a888` (337 lines).
- `Endpoint.lean`: `b4518141434d43a5d28f97944ba85b9af1c98cff1b19c910bddc2d4a70fe3e4b` (126 lines).
- `Exceptional.lean`: `f611a715e8c85e43989fa9a196ceb7d93b55b40b9b3674dfd3bb98398fdfabfa` (119 lines).
- `Properties.lean`: `a50ff1516880bd4110cb95e7b81baf44a64980ca2400aa1e377f2b093e8634c1` (26 lines).
- Aggregator `Chapter06.lean`: `845f356f126f288456cf210526ecb29523776bff6f6cfe89a4ebba369747a373`; review scope includes its new `pma6_3` wrapper.
- Accepted inventory: `5e2ead64c3941180f1b3cf4bd8d086c980e40b19df36363c046d3b463f24a68f`.

## Scope, attacks, and findings

The accepted inventory and its independent source review were used as the specification. This pass covers every main-text clause of PMA 6.1–6.13, the native definitions they use, and the actual new aggregator wrapper for 6.3. It does not rely on the earlier acceptance of these modules as its verdict.

| Scope | Hostile checks | Result |
| --- | --- | --- |
| 6.1–6.2 | Reversed intervals, nonempty cells, repeated points, totalized extrema, boundedness, integrator order, identity specialization, finite sum/integral bounds | Native `RSIntegrable` retains `a ≤ b`, boundedness, monotonicity, and lower/upper equality. Cells are closed and nonempty. All bounds and ordinary specializations are retained. |
| 6.3–6.4 | Exact union versus mere superset, repeated-point deletion, refinement direction, zero-width cells | Common refinement has exactly the union of point ranges. Both inequalities have the correct direction. Repetition invariance and the new wrapper preserve all conditions. The private path-cost proof handles repeated points through zero diagonal cost. |
| 6.5–6.7 | Comparison across different partitions, both directions of the criterion, absolute value inside versus outside the tag sum, value claims without integrability | Common refinement justifies cross-partition comparison. The criterion keeps boundedness and monotonicity. The sum of absolute differences is retained. Integral approximation explicitly requires native integrability. |
| 6.8–6.9 | Accidental continuity of the integrator in 6.8; loss of antitone integrands in 6.9; singleton intervals | Continuous integrands admit arbitrary monotone integrators. Both monotonicity directions for f are proved when the integrator is continuous. Ordered singleton intervals remain covered. |
| 6.10 and endpoint support | Discontinuities only in the open interval, hidden base theorem assumption, circular proof, continuity outside the source domain, shared endpoint jumps | Exceptional points are measured relative to the full closed interval. The final theorem supplies its base from the separately proved trimmed-interval theorem. Both endpoint alternatives are checked. The shared-jump caution is present. Fresh endpoint probes distinguish an admissible integrand jump from a forbidden common jump. |
| 6.11 | Continuity of the outer function outside its value interval, hidden monotonicity, singleton range | Only continuity on the stated value interval is used, and no monotonicity is assumed. A client with arbitrary outer function on a singleton range compiles. |
| 6.12 | Missing algebraic clauses, negative scalar restriction, lost absolute value, continuity at the split, endpoint cuts, double-counted jump | All five source parts are present: integrand addition and arbitrary real scaling; order; restrictions and additivity; absolute bound; integrator addition and positive scaling. The split helper also allows endpoint cuts. A concrete left-continuous jump is allocated to the right subinterval without duplication. |
| 6.13 | Hidden continuity assumptions on either factor, dropped integrability of absolute value, wrong sign in the integral bound | Products of merely integrable functions and the full absolute-value conclusion are proved. A product of endpoint-discontinuous integrands compiles. |

No weaker substitute for a source conclusion, unstated regularity requirement, vacuous existence claim, or circular dependency was found. In particular:

- The functions `1/x` and a zero integrator provide a deliberate trap: every native Darboux gap is zero, but `RSIntegrable` is false because boundedness fails. Both facts were freshly proved, so the criterion's boundedness gate is doing necessary work.
- A decreasing integrator is rejected even for a zero integrand. Thus cancellation or zero values do not bypass the integrator convention.
- A shared jump at the **left endpoint** of `[0,1]` has lower sum zero and upper sum one for every partition and is not integrable. This fresh probe is stronger at the boundary than the existing strictly interior shared-jump example. The same step integrand is admitted against the identity integrator by the actual final 6.10 theorem.
- The two valid tag choices `(0,2)` and `(1,1)` on partition `(0,1,2)` have equal tagged sums but sum of absolute cell differences equal to two. This prevents confusing 6.7's stronger conclusion with an absolute value applied only after summation.
- The zero-cell singleton partition and an explicitly repeated point both behave correctly. Repetition preserves lower and upper sums, and every total function has zero integral on a singleton.

The import graph of all 15 Chapter6 support modules was independently checked and is acyclic. In particular, `Exceptional` uses `Endpoint`; `Endpoint` uses already proved `Integrability` and `Split`; the main finite-exception theorem does not assume itself or its base. The aggregator's `pma6_3` is exactly the pair of the existing common-refinement and repetition theorems, with no additional hypothesis or unproved assertion.

## Verification results

- Independently compiled the actual frozen sources `Basic`, `Definitions`, `Refinement`, `Criterion`, `Integrability`, `Monotone`, `Split`, `Endpoint`, `Exceptional`, and `Properties` with `./lake-local env lean Rudin/PMA/Chapter06/<name>.lean`: **all ten exit 0, no warnings or errors**.
- Independently compiled the final aggregator with `./lake-local env lean Rudin/PMA/Chapter06.lean`: **exit 0, no warnings or errors**.
- Compiled the complete fresh client below through Lean stdin: **exit 0, no warnings or errors**. It contains **19 named theorem probes**, including support facts validating the concrete examples. Every one was recursively audited with `#print axioms`; all use exactly `propext`, `Classical.choice`, and `Quot.sound`.
- Independently printed recursive axioms for all thirteen principal `pma6_1` through `pma6_13` proofs, including the new wrapper: all use exactly those same three standard axioms.
- Scanned the ten source modules for `sorry`, `admit`, `native_decide`, and custom axiom declarations: none found. Their hashes were rechecked after the compile run and were unchanged.
- Client drafting needed beta-reduction and finite-index normalization fixes in the evidence code. These were client elaboration issues, resolved in the final passing run; no source-module change was requested or made.

The transient inventory-status wording noted during the read had already been corrected by the parent. The final inventory hash recorded above has accepted scope wording; this is **resolved and not a current finding**.

## Limits and reproducibility

This gate combines a full source/contract read with targeted universal and concrete formal probes; it does not claim that a finite collection of examples alone proves source fidelity. It covers 6.1–6.13 and their stated dependencies, not the later scalar/vector/curve nodes. Imported pinned Mathlib and earlier chapters are trusted at their existing audited boundaries. No book content was copied and no credential, process session, global configuration, production checkout, or Git state was accessed or altered by this pass.

The reproducible Lean client has SHA256 `b43dc3bde7fdff61a075ffd031af56c1a23a4f31b1157d20177ce8107966ded3`. Run from the isolated root:

```sh
python3 - <<'PYPROBE' | ./lake-local env lean --stdin
from pathlib import Path
text = Path('evidence/ch06-hostile-a.md').read_text()
print(text.split('```lean\n', 1)[1].split('```', 1)[0])
PYPROBE
```

## Reproducible fresh compile probes

The following independent client code is compiled through Lean stdin; it does not modify any proof module.

```lean
import Rudin.PMA.Chapter06
open Set
open scoped BigOperators
noncomputable section
namespace Rudin.PMA.Chapter06.HostileA
open Rudin.PMA.Chapter06

-- An equality between totalized integrals must not admit reversed intervals.
theorem reversed_rejected (f α : ℝ → ℝ) : ¬ RSIntegrable f α 1 0 := by
  intro h
  linarith [h.1]

-- Even zero Darboux gaps do not establish integrability of an unbounded function.
theorem unbounded_zero_integrator_rejected :
    ¬ RSIntegrable (fun x : ℝ => x⁻¹) (fun _ => 0) 0 1 := by
  intro h
  obtain ⟨M, hM⟩ := h.2.1
  have hpos : 0 < |M| + 1 := by positivity
  have hx : (|M| + 1)⁻¹ ∈ Icc (0 : ℝ) 1 := by
    constructor
    · exact (inv_pos.mpr hpos).le
    · exact (inv_le_one₀ hpos).mpr (by linarith [abs_nonneg M])
  have hh := hM ((|M| + 1)⁻¹) hx
  dsimp only at hh
  rw [inv_inv, abs_of_pos hpos] at hh
  linarith [le_abs_self M]

theorem unbounded_zero_gap (P : Partition 0 1) :
    upperSum (fun x : ℝ => x⁻¹) (fun _ => 0) P -
      lowerSum (fun x : ℝ => x⁻¹) (fun _ => 0) P = 0 := by
  simp [upperSum, lowerSum, Partition.weight]

-- A decreasing integrator is excluded even for the zero integrand.
theorem decreasing_integrator_rejected :
    ¬ RSIntegrable (fun _ : ℝ => (0 : ℝ)) (fun x => -x) 0 1 := by
  intro h
  have hm := h.2.2.1 (show (0 : ℝ) ∈ Icc 0 1 by norm_num)
    (show (1 : ℝ) ∈ Icc 0 1 by norm_num) (by norm_num : (0 : ℝ) ≤ 1)
  norm_num at hm

-- A zero-cell partition is available precisely on a singleton interval.
def zeroCells (a : ℝ) : Partition a a :=
  ⟨0, fun _ => a, fun _ _ _ => le_rfl, rfl, rfl⟩

theorem zero_cells_and_integral (f α : ℝ → ℝ) (a : ℝ) :
    lowerSum f α (zeroCells a) = 0 ∧ upperSum f α (zeroCells a) = 0 ∧
      RSIntegrable f α a a ∧ RSIntegral f α a a = 0 := by
  refine ⟨?_, ?_, rsIntegral_same_endpoint f α a⟩
  · exact Finset.sum_eq_zero (fun i _ => Fin.elim0 i)
  · exact Finset.sum_eq_zero (fun i _ => Fin.elim0 i)

def repeated : Partition 0 1 where
  n := 2
  point := ![0, 0, 1]
  mono := by intro i j h; fin_cases i <;> fin_cases j <;> simp_all
  left := rfl
  right := rfl

theorem repeated_range :
    range repeated.point = range (Partition.single (by norm_num : (0 : ℝ) ≤ 1)).point := by
  apply Set.Subset.antisymm
  · rintro _ ⟨i, rfl⟩
    fin_cases i
    · exact ⟨0, rfl⟩
    · exact ⟨0, rfl⟩
    · exact ⟨1, rfl⟩
  · rintro _ ⟨i, rfl⟩
    fin_cases i
    · exact ⟨0, rfl⟩
    · exact ⟨2, rfl⟩

theorem repetition_and_common_refinement (f α : ℝ → ℝ)
    (hf : BoundedOn f 0 1) (hα : MonotoneOn α (Icc 0 1)) :
    lowerSum f α repeated = lowerSum f α (Partition.single (by norm_num : (0 : ℝ) ≤ 1)) ∧
      upperSum f α repeated = upperSum f α (Partition.single (by norm_num : (0 : ℝ) ≤ 1)) :=
  pma6_3.2 _ _ repeated_range hf hα

abbrev twoCells : Partition 0 2 where
  n := 2
  point := ![0, 1, 2]
  mono := by intro i j h; fin_cases i <;> fin_cases j <;> simp_all
  left := rfl
  right := rfl

theorem cancellation_tags_legal :
    TaggedBy twoCells ![0, 2] ∧ TaggedBy twoCells ![1, 1] := by
  constructor <;> intro i <;> fin_cases i <;> norm_num [Partition.cell, twoCells]

-- Equal tagged sums can conceal a nonzero sum of absolute cell differences.
theorem cancellation_does_not_replace_sum_of_abs :
    taggedSum id id twoCells ![0, 2] = taggedSum id id twoCells ![1, 1] ∧
      (∑ i : Fin twoCells.n, |(![0, 2] : Fin 2 → ℝ) i - (![1, 1] : Fin 2 → ℝ) i| *
        twoCells.weight id i) = 2 := by
  change (∑ i : Fin 2, (![0, 2] : Fin 2 → ℝ) i * twoCells.weight id i) =
      (∑ i : Fin 2, (![1, 1] : Fin 2 → ℝ) i * twoCells.weight id i) ∧
    (∑ i : Fin 2, |(![0, 2] : Fin 2 → ℝ) i - (![1, 1] : Fin 2 → ℝ) i| *
      twoCells.weight id i) = 2
  norm_num [Fin.sum_univ_two, Partition.weight, twoCells]

theorem absolute_inside_source_conclusion {f α : ℝ → ℝ} {a b ε : ℝ}
    (P : Partition a b) (hf : BoundedOn f a b) (hα : MonotoneOn α (Icc a b))
    (hgap : upperSum f α P - lowerSum f α P < ε)
    (s t : Fin P.n → ℝ) (hs : TaggedBy P s) (ht : TaggedBy P t) :
    (∑ i, |f (s i) - f (t i)| * P.weight α i) < ε :=
  (pma6_7 P hf hα hgap).2.1 s t hs ht

-- Continuous integrands still admit a discontinuous integrator.
theorem continuous_against_jump : RSIntegrable id UnitStep (-1) 1 :=
  pma6_8 id UnitStep (-1) 1 (by norm_num) continuousOn_id (pma6_14.2.2.monotoneOn _)

-- The antitone branch is actually usable.
theorem decreasing_integrand : RSIntegrable (fun x : ℝ => -x) id 0 1 := by
  apply pma6_9 _ _ 0 1 (by norm_num)
  · exact Or.inr (fun _ _ _ _ h => neg_le_neg h)
  · exact fun _ _ _ _ h => h
  · exact continuousOn_id

-- The left endpoint may be a genuine discontinuity of the integrand.
theorem endpoint_jump_against_id : RSIntegrable UnitStep id 0 1 := by
  apply pma6_10.1 UnitStep id 0 1 (by norm_num)
  · have heq : TranslatedStep 0 = UnitStep := by funext x; simp [TranslatedStep]
    exact heq ▸ translatedStep_bounded 0 0 1
  · exact fun _ _ _ _ h => h
  · apply (Set.finite_singleton (0 : ℝ)).subset
    intro x hx
    by_contra hx0
    have hc : ContinuousAt UnitStep x := by
      have heq : TranslatedStep 0 = UnitStep := by funext y; simp [TranslatedStep]
      exact heq ▸ (translatedStep_continuousAt_of_ne (s := 0) (by simpa using hx0))
    exact hx.2 hc.continuousWithinAt
  · intro x _ _
    exact continuous_id.continuousWithinAt

-- A shared left-endpoint jump must still fail the closed-cell Darboux predicate.
theorem shared_endpoint_jump_rejected :
    ¬ RSIntegrable (TranslatedStep 0) (TranslatedStep 0) 0 1 := by
  have hm := (translatedStep_monotone 0).monotoneOn (Icc (0 : ℝ) 1)
  have hb := translatedStep_bounded 0 0 1
  have hlo (P : Partition 0 1) : lowerSum (TranslatedStep 0) (TranslatedStep 0) P = 0 := by
    apply le_antisymm
    · apply Finset.sum_nonpos
      intro i _
      by_cases hw : P.weight (TranslatedStep 0) i = 0
      · simp [hw]
      · have hcell := translatedStep_cell_of_weight_ne_zero P i hw
        have hv := cellLower_le_value hb P i hcell
        simpa [TranslatedStep, UnitStep] using
          mul_le_mul_of_nonneg_right hv (P.weight_nonneg _ hm i)
    · simpa only [zero_mul] using lowerSum_lower_bound hm
        (fun x _ => (translatedStep_mem_unit_interval 0 x).1) P
  have hup (P : Partition 0 1) : upperSum (TranslatedStep 0) (TranslatedStep 0) P = 1 := by
    apply le_antisymm
    · convert upperSum_upper_bound hm
        (fun x _ => (translatedStep_mem_unit_interval 0 x).2) P using 1
      norm_num [TranslatedStep, UnitStep]
    · have hsum : (∑ i : Fin P.n, P.weight (TranslatedStep 0) i) = 1 := by
        rw [P.sum_weights]
        norm_num [TranslatedStep, UnitStep]
      apply hsum.symm.trans_le
      apply Finset.sum_le_sum
      intro i _
      by_cases hr : P.point i.succ ≤ 0
      · have hl : P.point i.castSucc ≤ 0 := (P.cell_order i).trans hr
        simp [Partition.weight, TranslatedStep, UnitStep, hr, hl]
      · have hv : 1 ≤ cellUpper (TranslatedStep 0) P i := by
          simpa [TranslatedStep, UnitStep, hr] using
            value_le_cellUpper hb P i ⟨P.cell_order i, le_rfl⟩
        simpa only [one_mul] using mul_le_mul_of_nonneg_right hv (P.weight_nonneg _ hm i)
  have : Nonempty (Partition 0 1) := Partition.nonempty (by norm_num)
  intro h
  have heq := h.2.2.2
  have hl : (lowerSum (TranslatedStep 0) (TranslatedStep 0) : Partition 0 1 → ℝ) = fun _ => 0 :=
    funext hlo
  have hu : (upperSum (TranslatedStep 0) (TranslatedStep 0) : Partition 0 1 → ℝ) = fun _ => 1 :=
    funext hup
  simp [lowerIntegral, upperIntegral, hl, hu] at heq

-- A split at the jump allocates the source step increment to its right interval.
theorem jump_split_values :
    RSIntegral (fun _ => (2 : ℝ)) UnitStep (-1) 1 = 2 ∧
      RSIntegral (fun _ => (2 : ℝ)) UnitStep (-1) 0 = 0 ∧
      RSIntegral (fun _ => (2 : ℝ)) UnitStep 0 1 = 2 := by
  have h1 := (rsIntegral_const (c := (2 : ℝ)) (by norm_num : (-1 : ℝ) ≤ 1)
    (pma6_14.2.2.monotoneOn _)).2
  have h2 := (rsIntegral_const (c := (2 : ℝ)) (by norm_num : (-1 : ℝ) ≤ 0)
    (pma6_14.2.2.monotoneOn _)).2
  have h3 := (rsIntegral_const (c := (2 : ℝ)) (by norm_num : (0 : ℝ) ≤ 1)
    (pma6_14.2.2.monotoneOn _)).2
  norm_num [UnitStep] at h1 h2 h3
  exact ⟨h1, h2, h3⟩

theorem endpoint_splits {f α : ℝ → ℝ} {a b : ℝ} (h : RSIntegrable f α a b) :
    RSIntegral f α a b = RSIntegral f α a a + RSIntegral f α a b ∧
      RSIntegral f α a b = RSIntegral f α a b + RSIntegral f α b b :=
  ⟨split_rsIntegral le_rfl h.1 h, split_rsIntegral h.1 le_rfl h⟩

-- Composition only needs continuity on the actual value interval, even a singleton.
theorem composition_local_range (φ : ℝ → ℝ) :
    RSIntegrable (φ ∘ (fun _ : ℝ => (0 : ℝ))) id 0 1 := by
  have hf := (rsIntegral_const (c := (0 : ℝ)) (by norm_num : (0 : ℝ) ≤ 1)
    (show MonotoneOn (id : ℝ → ℝ) (Icc 0 1) from fun _ _ _ _ h => h)).1
  apply pma6_11 _ _ φ 0 1 0 0 hf
  · intro x hx
    exact ⟨le_rfl, le_rfl⟩
  · apply (continuousOn_const : ContinuousOn (fun _ : ℝ => φ 0) (Icc (0 : ℝ) 0)).congr
    intro x hx
    have : x = 0 := le_antisymm hx.2 hx.1
    simp [this]

-- Scalar multiplication of integrands admits negative and zero scalars.
theorem negative_and_zero_scalars :
    RSIntegral (fun _ : ℝ => (-3 : ℝ) * 2) id 0 1 = -6 ∧
      RSIntegral (fun _ : ℝ => (0 : ℝ) * 2) id 0 1 = 0 := by
  have h := rsIntegral_const (c := (2 : ℝ)) (by norm_num : (0 : ℝ) ≤ 1)
    (show MonotoneOn (id : ℝ → ℝ) (Icc 0 1) from fun _ _ _ _ h => h)
  have hn := (pma6_12.1 _ _ _ 0 1 (-3) h.1 h.1).2.2.2
  have hz := (pma6_12.1 _ _ _ 0 1 0 h.1 h.1).2.2.2
  simp only [h.2, id_eq] at hn hz
  constructor <;> linarith

-- Products do not require either integrand to be continuous.
theorem discontinuous_product_integrable :
    RSIntegrable (fun x => UnitStep x * UnitStep x) id 0 1 :=
  pma6_13.1 _ _ _ 0 1 endpoint_jump_against_id endpoint_jump_against_id

#print axioms reversed_rejected
#print axioms unbounded_zero_integrator_rejected
#print axioms unbounded_zero_gap
#print axioms decreasing_integrator_rejected
#print axioms zero_cells_and_integral
#print axioms repeated_range
#print axioms repetition_and_common_refinement
#print axioms cancellation_tags_legal
#print axioms cancellation_does_not_replace_sum_of_abs
#print axioms absolute_inside_source_conclusion
#print axioms continuous_against_jump
#print axioms decreasing_integrand
#print axioms endpoint_jump_against_id
#print axioms shared_endpoint_jump_rejected
#print axioms jump_split_values
#print axioms endpoint_splits
#print axioms composition_local_range
#print axioms negative_and_zero_scalars
#print axioms discontinuous_product_integrable
#print axioms pma6_1
#print axioms pma6_2
#print axioms pma6_3
#print axioms pma6_4
#print axioms pma6_5
#print axioms pma6_6
#print axioms pma6_7
#print axioms pma6_8
#print axioms pma6_9
#print axioms pma6_10
#print axioms pma6_11
#print axioms pma6_12
#print axioms pma6_13
end Rudin.PMA.Chapter06.HostileA
```
