# Independent final review: PMA 7.11–7.15

Reviewer: `/root/taylor`, not the author of `Continuity.lean`. Date: 2026-10-10.

**Verdict: ACCEPT the actual five contracts, all eleven theorem bodies, and supporting definitions used by this module.** No source correction or unresolved semantic finding.

## Frozen inputs

| File | SHA-256 |
| --- | --- |
| `rudin/Rudin/PMA/Chapter07/Continuity.lean` (198 lines) | `8dae8b99a9de2d8b996c47e62ad3ae5396efb503b36a686374f0349a4efa1977` |
| `rudin/Rudin/PMA/Chapter07/Basic.lean` | `b6b8b58999ad0025fd3ab28bc0ba3a4df5a07cc395158b99a14c05055bfa2b1a` |
| `rudin/Rudin/PMA/Chapter07/Examples.lean` | `a25907d75b1bae77638eaaea291888989f6d9f319f0d2cea71ee74c9a25f9bd5` |
| `rudin/Rudin/PMA/Chapter07/Calculus.lean` | `0bc805601a65a1261e944ae9d180b3cb0344c0d9484fc766f1d3df6c3411580d` |
| `rudin/Rudin/PMA/Chapter04.lean` | `71ac9841413d7046b72f943541667d91f77dfc77924fbc588c2dbea277754df8` |
| Accepted `research/pma-ch07-inventory.md` | `f8e87ad7ccb765bfd4407e251958c5378552b209d32eca60a75e13e0ca9da0f0` |
| Independent imported client, reproduced below | `5751949bc6be0204a95cdeabc22826902d1e3e7a9ea59e1a3d50c29ddb8b513b` |

The final canonical source hash was rechecked unchanged after review and compilation. No proof module, protected chapter, production checkout, Git state, configuration, credential, or existing session was altered. A temporary client was compiled at `/tmp/ch07-continuity-review.lean`; its full source is retained below so the temporary file is not needed for reproducibility.

## Source and proof findings

- **7.11:** Uniform convergence holds on all of E. Neither membership of x in E nor continuity of the functions is assumed. The source accumulation-point predicate is the actual punctured-neighborhood nonbottom condition from Chapters 2 and 4. The proof derives Cauchy convergence of A by passing the uniform error estimate to each pair of punctured limits, then constructs the common limit by completeness. The final filter interchange uses the same punctured domain. No totalized limit or vacuous isolated-point limit is substituted.
- **7.12:** The main conclusion preserves complex values, arbitrary metric domains/subsets, and memberwise relative continuity. The library continuous-limit API accepts the supplied all-index continuity witnesses. The converse failure retains continuous approximants, pointwise convergence to the continuous zero function, and failure of uniform convergence on [0,1]. The latter follows from actual native Riemann integral divergence in Examples and the native uniform-limit integral theorem in Calculus. It does not substitute a Bochner integral, and does not rely on the continuity-limit theorem being proved. The numerical integral divergence has already been proved independently of this module.
- **7.13:** The positive theorem requires compactness of K, continuity of each member and the limit, pointwise convergence, and decreasing values at every point. The invoked pinned `Antitone.tendstoUniformlyOn_of_forall_tendsto` has exactly those hypotheses. The explicit reciprocal example uses the source's positive indexing via n+1, proves continuity, antitonicity, convergence to zero, and nonuniformity. The test point `1/(2*(N+1))` belongs to (0,1) and produces the exact value 2/3, contradicting a 1/2 uniform error bound. No compactness premise is used in that counterexample.
- **7.14:** The bundled space represents exactly the bounded continuous complex functions, with an individual finite real bound. Its norm is the supremum of pointwise norms, and its distance is the norm of the difference. The actual Mathlib metric instance on bounded continuous maps supplies positivity and the metric laws; the contract also states the requested norm-zero and triangle identities. Metric/uniform convergence equivalence is on the full domain. Sequential uniform closedness and closure from Basic are proved equivalent to the metric closedness and closure. The compact-domain boundedness consequence is included. Empty domains are admitted and verified by the client.
- **7.15:** Both the actual completeness instance and explicit existence of a bounded continuous complex limit for any metric Cauchy sequence are present. No compactness of the domain is imposed. The underlying pinned completeness instance constructs a pointwise limit and verifies its boundedness, continuity, and norm convergence; it is not a new axiom or a replacement of the function space.

All five typed statements match the accepted inventory, including attached cautions. Source scans found no `sorry`, `admit`, custom `axiom`, `unsafe`, or kernel-check bypass marker in Continuity. This review reads the native integral dependency boundary used by 7.12; it does not relabel the reviewer's own Calculus proof as an independent review of that dependency. The root separately reviewed Calculus.

## Verification

1. `./lake-local env lean Rudin/PMA/Chapter07/Continuity.lean` exited 0 with no warnings or errors.
2. The independent client below imported the canonical compiled module and exited 0 without warnings.
3. Its recursive `collectAxioms` audit covered every public/private/generated declaration under `Rudin.PMA.Chapter07` visible through this import, plus every client declaration: **119 declarations**. Only `propext`, `Classical.choice`, and `Quot.sound` occurred. This count is for this exact import environment, not a claim that all eventual Chapter 7 modules were already included.
4. The same client checked that `pma7_11` through `pma7_15` are actual `.thmInfo` declarations rather than definitions of propositions.

The eight fresh boundary probes verify: a limit point outside E; rejection of an isolated singleton as a limit point; noncompactness of the Dini example's domain derived from the theorem and counterexample together; zero norm on the empty domain; empty-family uniform closure on the empty domain; a nonzero imaginary constant's norm on a singleton; exclusion of an unbounded continuous complex function from the bounded space; and completeness on the noncompact real domain. These are additional to the author's main proofs.

## Reproducible client

```lean
import Rudin.PMA.Chapter07.Continuity
open Set Filter Topology
open scoped BoundedContinuousFunction
open Rudin.PMA
open Rudin.PMA.Chapter07

namespace ContinuityReview

theorem limit_outside_domain :
    (0 : ℝ) ∉ Ioi 0 ∧
      ∃ a : ℂ, Tendsto (fun _ : ℕ => Complex.I) atTop (𝓝 a) ∧
        Chapter04.FunctionLimitOn (Ioi 0)
          (fun x : ℝ => if 0 < x then Complex.I else 0) 0 a := by
  have hp : Chapter02.IsLimitPoint (0 : ℝ) (Ioi 0) := by
    intro r hr
    refine ⟨r / 2, by simp; linarith, by linarith, ?_⟩
    rw [Real.dist_eq]
    have he : |0 - r / 2| = r / 2 := by rw [zero_sub, abs_neg, abs_of_pos (by positivity)]
    rw [he]
    linarith
  let f : ℝ → ℂ := fun x => if 0 < x then Complex.I else 0
  have hlim : Chapter04.FunctionLimitOn (Ioi 0) f 0 Complex.I := by
    refine ⟨hp, fun ε hε => ⟨1, by norm_num, ?_⟩⟩
    intro x hx _ _
    simpa [f, show 0 < x from hx] using hε
  have hu : UniformConvergesOn (fun _ : ℕ => f) f (Ioi 0) := by
    apply Metric.tendstoUniformlyOn_iff.mpr
    intro ε hε
    exact Eventually.of_forall (fun _ _ _ => by simpa using hε)
  exact ⟨by simp, pma7_11 (Ioi 0) (fun _ => f) f 0 (fun _ => Complex.I) hu hp (fun _ => hlim)⟩

theorem no_isolated_limit_point : ¬ Chapter02.IsLimitPoint (0 : ℝ) {0} := by
  intro h
  obtain ⟨q, hq, hne, _⟩ := h 1 (by norm_num)
  exact hne (by simpa using hq)

theorem dini_domain_not_compact : ¬ IsCompact (Ioo (0 : ℝ) 1) := by
  intro hK
  obtain ⟨hF, hanti, hpoint, hf, hnot⟩ := pma7_13.{0}.2
  exact hnot (pma7_13.1 _ _ _ hK hF hf hpoint hanti)

abbrev EmptyReal := (∅ : Set ℝ)

theorem empty_bcf_norm (h : EmptyReal →ᵇ ℂ) : ‖h‖ = 0 := by
  apply ((pma7_14 (X := EmptyReal)).2.2.1 h).mpr
  intro x
  exact False.elim x.2

theorem empty_bcf_closure :
    BCFUniformClosure (∅ : Set (EmptyReal →ᵇ ℂ)) = ∅ := by
  simpa using ((pma7_14 (X := EmptyReal)).2.2.2.2.2.1
    (∅ : Set (EmptyReal →ᵇ ℂ))).2

theorem singleton_bcf_imaginary_norm :
    ‖BoundedContinuousFunction.const (Icc (0 : ℝ) 0) Complex.I‖ = 1 := by
  let : Nonempty (Icc (0 : ℝ) 0) := ⟨⟨0, by simp⟩⟩
  rw [(pma7_14 (X := Icc (0 : ℝ) 0)).2.1]
  simp

theorem unbounded_continuous_not_bcf :
    ¬ ∃ h : ℝ →ᵇ ℂ, ∀ x : ℝ, h x = (x : ℂ) := by
  intro hh
  obtain ⟨_, M, hM⟩ := ((pma7_14 (X := ℝ)).1 (fun x => (x : ℂ))).mp hh
  have hm := hM (|M| + 1)
  have hpos : 0 ≤ |M| + 1 := by positivity
  simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hpos] at hm
  linarith [le_abs_self M]

theorem noncompact_bcf_complete : CompleteSpace (ℝ →ᵇ ℂ) :=
  (pma7_15 (X := ℝ)).1

end ContinuityReview

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let names ← env.constants.foldM (init := #[]) fun names rawName _ => do
    let name := privateToUserName rawName.eraseMacroScopes
    return if (`Rudin.PMA.Chapter07).isPrefixOf name ||
      (`ContinuityReview).isPrefixOf name then names.push rawName else names
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in names do
    let axioms ← collectAxioms name
    let bad := axioms.filter fun ax => !allowed.contains ax
    if !bad.isEmpty then throwError "Forbidden axioms in {name}: {bad}"
  for name in #[``pma7_11, ``pma7_12, ``pma7_13, ``pma7_14, ``pma7_15] do
    match env.find? name with
    | some (.thmInfo _) => pure ()
    | _ => throwError "Not an actual theorem: {name}"
  logInfo m!"Continuity independent client: {names.size} Chapter07/probe declarations recursively axiom-audited; five principal declarations are actual theorems."
```
