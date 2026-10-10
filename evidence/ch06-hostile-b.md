# Chapter 6 additional hostile gate B: 6.14–6.16 and 6.18

**Verdict: PASS for the assigned four-node scope. No confirmed mathematical, contract-fidelity, or vacuity defect found.**

Reviewer: `/root/vectors`. I authored none of these nodes. This is a fresh additional hostile gate, independent of the earlier fidelity review. I read the accepted inventory, the actual complete frozen Jump and Moment sources, the relevant native Darboux definitions, the invoked Chapter 4 jump-summability/monotonicity lemmas, and the scalar density theorem's public premises. I also consulted only the local book's statement/remark blocks for these nodes on PDF pages 138–141. No book proof text or book content was copied or saved.

## Frozen bytes reviewed

| File | SHA-256 |
| --- | --- |
| `research/pma-ch06-inventory.md` | `5e2ead64c3941180f1b3cf4bd8d086c980e40b19df36363c046d3b463f24a68f` |
| `rudin/Rudin/PMA/Chapter06/Jump.lean` | `ab56704088a99d95c29755f2ada3c7a491ea55af5f24be7cf19b51283e96c47a` |
| `rudin/Rudin/PMA/Chapter06/Moment.lean` | `21ccfad2cbbc3cbd0726a62a190f6092fd2b376690233dd340435b38bb89deb5` |

The following imported framework/dependency snapshots were also recorded for reproducibility; this is not a fresh complete review of every declaration in those files.

| Dependency | SHA-256 |
| --- | --- |
| `Basic.lean` | `5192b99092c0fc7da7109b1e3ffd90446db62c73845b935172643456b46a3915` |
| `Definitions.lean` | `13adade605f2cff6904a9b5d24f06057595d0c760abc140dfd7831608c5ccf81` |
| `Integrability.lean` | `001823e4c51a56b9c0d0afbe13801a757200178eac396081dec3b7abb91d5cec` |
| `Calculus.lean` | `ac36c016490bd347b592af764c1c6e5f544a6cd09ad7aac0c59a4c79da6c3c18` |

The Jump and Moment hashes were unchanged after inspection and independent compilation.

## Contract and proof attacks

**6.14 — value at the jump.** The actual definition uses `x ≤ 0` for the zero branch. The contract covers all nonpositive arguments, all strictly positive arguments, and monotonicity; it does not silently substitute a right-continuous step. The translated step has value zero at its atom. Fresh probes checked these exact boundary values and an infinite atomic sum at one of its own atoms.

**6.15 — continuity scope and endpoint support.** The atom is strictly inside the interval. Integrability is asserted in addition to the value identity. Boundedness is retained over the entire integration interval, while continuity is needed only at the atom. Although the Lean premise is `ContinuousAt`, a fresh general bridge proves that relative continuity on the closed interval suffices because the atom is interior. A concrete probe takes a bounded integrand with a discontinuity at one quarter and an atom at one half; it proves lack of global continuity and still obtains the integral value one. A shared-jump probe proves nonintegrability when continuity at the atom is removed.

The proof's nonzero-weight cell includes the atom, so cell infimum/supremum bounds apply to its value. The three-cell close partition places the active cell immediately to the right of the atom, as required by the left-continuous step convention. It does not switch conventions at partition points.

**Endpoint attack.** For the constant integrand one on `[0,1]`, an atom at the right endpoint has native integral zero, whereas the analogous atom at the left endpoint has integral one. Both integrability assertions and values were compiled. Thus the strict interior support restriction is mathematically substantive; this review does not claim that the displayed interior point-mass formula extends unchanged to both endpoints.

**6.16 — totalization and hidden restrictions.** The contract explicitly asserts summability of the defining series at every real argument, global monotonicity of its sum, both endpoint values, summability of the weighted sample series, native Stieltjes integrability, and the value equality. No conclusion is merely an equality of totalized `tsum` expressions. The proof establishes absolute domination using nonnegative summable weights, justifies subtraction and finite-sum interchange with explicit summability hypotheses, and uses native Darboux lower/upper bounds to identify the integral. It introduces neither a measure integral nor an unproved series-integral interchange.

The distinct-support hypothesis is retained in the contract. Its being unused by stronger helper proofs is harmless: repeated locations also satisfy the helper formulas, but the source-facing theorem keeps the source hypothesis. The proof does not secretly demand finitely many atoms, a positive distance of support from the endpoints, or a nonnegative integrand. A concrete infinite example uses locations `1/(n+2)`, nonzero weights `(1/2)^n`, and constant integrand minus one. The locations are proved injective and strictly interior while accumulating at zero. The defining series and sample series are summable, the endpoint mass is two, and the native integral is minus two. At the first atom, the sum equals one, showing that its own jump weight is excluded at that exact point. A negative-weight probe separately proves failure of monotonicity, confirming that the nonnegativity premise has real content.

**6.18 — all reductions and the broader class.** The actual contract has four parts: quadratic integrability for every nondecreasing mass function, the integrable-density reduction with integrability of the weighted density, the countably atomic formula with sample summability and integrability, and the finite atomic specialization. The density branch requires actual within-derivatives, including one-sided endpoint semantics, and Riemann integrability of the density; it does not add continuity of the density. Its proof invokes the complete scalar density theorem on the bounded continuous quadratic integrand.

The first clause admits much more than the two reduction formulas. A fresh probe constructs the continuous nondecreasing function `x + |x - 1/2|`, proves that it is not differentiable at the interior point one half, and still proves its quadratic moment is native Stieltjes integrable. Thus this clause is not an empty claim about an uninhabited class. The nonlinear smooth-density example `m(x)=x²` gives moment one half. A two-atom example gives the exact value `29/16`; an empty finite family gives an integrable zero moment.

## Fresh kernel checks

The following independent commands completed with exit 0 and no warnings:

- `./lake-local env lean Rudin/PMA/Chapter06/Jump.lean`
- `./lake-local env lean Rudin/PMA/Chapter06/Moment.lean`
- `./lake-local env lean --stdin` with the complete probe block below.

The final probe script has 211 lines and SHA-256 `cdb432185e9822340f2403d652438229073434bf4d83fe10538bc6048fe1b524`, including its final newline. All twelve probe declarations have recursively reported axiom sets exactly `[propext, Classical.choice, Quot.sound]`. The four numbered theorem declarations have the same standard-only axiom sets. The two source-module recompilations printed ten standard-only recursive axiom reports for their numbered results and key helpers. Earlier probe-elaboration errors were fixed in the review-only script; none required any source-module change.

| Probe | Adversarial outcome |
| --- | --- |
| `step_boundary` | The jump value is zero, not one. |
| `endpoint_atoms_differ` | Right and left endpoint atoms produce different native integrals. |
| `relative_continuity_at_atom_suffices` | No extra global-domain continuity is needed. |
| `discontinuity_away_from_atom_allowed` | Lack of global continuity does not invalidate 6.15. |
| `shared_jump_rejected` | Shared jumps can genuinely destroy integrability. |
| `genuine_infinite_signed_integrand` | Infinite accumulating support and negative integrand are accepted, with nonzero exact value. |
| `geometric_atom_excludes_its_own_jump` | The infinite sum preserves the exact left-continuous convention at an atom. |
| `negative_atom_is_not_monotone` | Removing nonnegative weights would break monotonicity. |
| `finite_quadratic_moment_value` | Two distinct atoms give the exact finite moment. |
| `empty_atomic_moment` | The zero-atom finite case is integrable with value zero. |
| `nonlinear_density_moment` | A nonconstant density gives the correct moment one half. |
| `continuous_nondifferentiable_mass_allowed` | Quadratic integrability extends beyond the two reduction formulas. |

## Limits

This verdict covers only 6.14–6.16 and 6.18 at the recorded bytes. It is not a whole-chapter production approval or an independent reconstruction of every imported theorem. The density probe uses a continuous density; absence of a hidden density-continuity premise was checked in the actual quantified contracts and proof application, rather than by constructing an additional discontinuous derivative example. No endpoint atomic formula beyond the accepted interior-support scope is asserted. No proof module or production file was changed.

## Reproducible review-only probes

```lean
import Rudin.PMA.Chapter06.Moment
import Rudin.PMA.Chapter06.Definitions
open Set Filter
open scoped Topology BigOperators
noncomputable section
namespace Chapter06HostileB
open Rudin.PMA.Chapter06

theorem step_boundary :
    UnitStep 0 = 0 ∧ UnitStep (-1) = 0 ∧ UnitStep 1 = 1 ∧
    TranslatedStep (1 / 2) (1 / 2) = 0 := by
  norm_num [UnitStep, TranslatedStep]

theorem endpoint_atoms_differ :
    RSIntegrable (fun _ : ℝ => (1 : ℝ)) (TranslatedStep 1) 0 1 ∧
    RSIntegral (fun _ : ℝ => (1 : ℝ)) (TranslatedStep 1) 0 1 = 0 ∧
    RSIntegrable (fun _ : ℝ => (1 : ℝ)) (TranslatedStep 0) 0 1 ∧
    RSIntegral (fun _ : ℝ => (1 : ℝ)) (TranslatedStep 0) 0 1 = 1 := by
  have hr := rsIntegral_const (c := (1 : ℝ)) (show (0 : ℝ) ≤ 1 by norm_num)
    ((translatedStep_monotone 1).monotoneOn (Icc 0 1))
  have hl := rsIntegral_const (c := (1 : ℝ)) (show (0 : ℝ) ≤ 1 by norm_num)
    ((translatedStep_monotone 0).monotoneOn (Icc 0 1))
  refine ⟨hr.1, ?_, hl.1, ?_⟩
  · convert hr.2 using 1
    norm_num [TranslatedStep, UnitStep]
  · convert hl.2 using 1
    norm_num [TranslatedStep, UnitStep]

theorem discontinuity_away_from_atom_allowed :
    ¬ ContinuousOn (TranslatedStep (1 / 4)) (Icc (0 : ℝ) 1) ∧
    RSIntegrable (TranslatedStep (1 / 4)) (TranslatedStep (1 / 2)) 0 1 ∧
    RSIntegral (TranslatedStep (1 / 4)) (TranslatedStep (1 / 2)) 0 1 = 1 := by
  have h := pma6_15 0 1 (1 / 2) (TranslatedStep (1 / 4)) (by norm_num) (by norm_num)
    (translatedStep_bounded _ _ _) (translatedStep_continuousAt_of_ne (by norm_num))
  refine ⟨?_, h.1, ?_⟩
  · intro hc
    exact translatedStep_not_continuousWithinAt (by norm_num : (0 : ℝ) < 1 / 4)
      (by norm_num : (1 / 4 : ℝ) < 1) (hc _ (by norm_num))
  · convert h.2 using 1
    norm_num [TranslatedStep, UnitStep]

theorem shared_jump_rejected :
    ¬ RSIntegrable (TranslatedStep (1 / 2)) (TranslatedStep (1 / 2)) 0 1 :=
  translatedStep_not_RSIntegrable_self (by norm_num) (by norm_num)

def locations (n : ℕ) : ℝ := 1 / (n + 2 : ℝ)
def weights (n : ℕ) : ℝ := (1 / 2 : ℝ) ^ n

theorem locations_inside (n : ℕ) : locations n ∈ Ioo (0 : ℝ) 1 := by
  have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
  constructor
  · exact one_div_pos.mpr (by positivity)
  · dsimp [locations]
    exact (div_lt_one (by positivity : (0 : ℝ) < n + 2)).mpr (by linarith)

theorem locations_injective : Function.Injective locations := by
  intro i j hij
  dsimp [locations] at hij
  have hden : (i : ℝ) + 2 = (j : ℝ) + 2 := inv_inj.mp (by simpa only [one_div] using hij)
  exact_mod_cast (by linarith : (i : ℝ) = (j : ℝ))

theorem genuine_infinite_signed_integrand :
    (∀ x : ℝ, Summable (fun i => weights i * UnitStep (x - locations i))) ∧
    AtomicStepSum locations weights 0 = 0 ∧ AtomicStepSum locations weights 1 = 2 ∧
    Summable (fun i => weights i * (-1 : ℝ)) ∧
    RSIntegrable (fun _ : ℝ => (-1 : ℝ)) (AtomicStepSum locations weights) 0 1 ∧
    RSIntegral (fun _ : ℝ => (-1 : ℝ)) (AtomicStepSum locations weights) 0 1 = -2 := by
  have h := pma6_16 0 1 locations weights (fun _ => -1) locations_inside locations_injective
    (fun n => by dsimp [weights]; positivity) summable_geometric_two continuousOn_const
  have ht : (∑' i, weights i) = 2 := tsum_geometric_two
  refine ⟨h.1, h.2.2.1, ?_, h.2.2.2.2.1, h.2.2.2.2.2.1, ?_⟩
  · exact h.2.2.2.1.trans ht
  · simpa only [mul_neg_one, tsum_neg, ht] using h.2.2.2.2.2.2

theorem finite_quadratic_moment_value :
    RSIntegrable QuadraticPosition
      (AtomicStepSum (![1/4, 3/4] : Fin 2 → ℝ) (![2, 3] : Fin 2 → ℝ)) 0 1 ∧
    RSIntegral QuadraticPosition
      (AtomicStepSum (![1/4, 3/4] : Fin 2 → ℝ) (![2, 3] : Fin 2 → ℝ)) 0 1 = 29/16 := by
  have hs : ∀ i : Fin 2, (![1/4, 3/4] : Fin 2 → ℝ) i ∈ Ioo (0 : ℝ) 1 := by
    intro i; fin_cases i <;> norm_num
  have hinj : Function.Injective (![1/4, 3/4] : Fin 2 → ℝ) := by
    apply StrictMono.injective
    apply Fin.strictMono_iff_lt_succ.mpr
    intro i
    fin_cases i
    norm_num
  have hc : ∀ i : Fin 2, 0 ≤ (![2, 3] : Fin 2 → ℝ) i := by
    intro i; fin_cases i <;> norm_num
  have h := pma6_18.2.2.2 2 _ _ hs hinj hc
  refine ⟨h.1, ?_⟩
  convert h.2 using 1
  norm_num [Fin.sum_univ_succ]

theorem empty_atomic_moment :
    RSIntegrable QuadraticPosition
      (AtomicStepSum (fun i : Fin 0 => i.elim0) (fun i : Fin 0 => i.elim0)) 0 1 ∧
    RSIntegral QuadraticPosition
      (AtomicStepSum (fun i : Fin 0 => i.elim0) (fun i : Fin 0 => i.elim0)) 0 1 = 0 := by
  simpa using pma6_18.2.2.2 0 (fun i => i.elim0) (fun i => i.elim0)
    (fun i => i.elim0) (fun i => i.elim0) (fun i => i.elim0)

theorem nonlinear_density_moment :
    RSIntegrable QuadraticPosition (fun x : ℝ => x ^ 2) 0 1 ∧
      RSIntegral QuadraticPosition (fun x : ℝ => x ^ 2) 0 1 = 1 / 2 := by
  have hm : MonotoneOn (fun x : ℝ => x ^ 2) (Icc 0 1) := by
    intro x hx y hy hxy
    nlinarith [hx.1, hy.1]
  have hd : ∀ x ∈ Icc (0 : ℝ) 1,
      HasDerivWithinAt (fun t : ℝ => t ^ 2) (2 * x) (Icc 0 1) x := by
    intro x _
    convert ((hasDerivAt_id x).fun_pow 2).hasDerivWithinAt using 1 <;> simp only [id_eq, mul_one]
    ring
  have hrho : RIntegrable (fun x : ℝ => 2 * x) 0 1 :=
    rsIntegrable_of_continuousOn (by norm_num) (continuous_const.mul continuous_id).continuousOn
      (fun _ _ _ _ h => h)
  have h := pma6_18.2.1 _ _ hm hd hrho
  have hdF : ∀ x ∈ Icc (0 : ℝ) 1,
      HasDerivWithinAt (fun t : ℝ => t ^ 4 / 2) (x ^ 2 * (2 * x)) (Icc 0 1) x := by
    intro x _
    convert (((hasDerivAt_id x).fun_pow 4).div_const 2).hasDerivWithinAt using 1 <;> simp only [id_eq, mul_one]
    ring
  have hF := pma6_21 (fun t : ℝ => t ^ 4 / 2) (fun x => x ^ 2 * (2 * x)) 0 1
    (by norm_num) hdF h.1
  refine ⟨pma6_18.1 _ hm, ?_⟩
  have hh := h.2.trans hF
  norm_num at hh ⊢
  exact hh

def kinkMass (x : ℝ) : ℝ := x + |x - 1/2|

theorem continuous_nondifferentiable_mass_allowed :
    Continuous kinkMass ∧ Monotone kinkMass ∧
    ¬ DifferentiableAt ℝ kinkMass (1/2) ∧
    RSIntegrable QuadraticPosition kinkMass 0 1 := by
  have hc : Continuous kinkMass := continuous_id.add ((continuous_id.sub continuous_const).abs)
  have hm : Monotone kinkMass := by
    intro x y hxy
    have hh := abs_sub_abs_le_abs_sub (x - 1/2) (y - 1/2)
    rw [show x - 1/2 - (y - 1/2) = x - y by ring,
      abs_of_nonpos (sub_nonpos.mpr hxy)] at hh
    dsimp [kinkMass]
    linarith
  have hn : ¬ DifferentiableAt ℝ kinkMass (1/2) := by
    intro hd
    have ha : DifferentiableAt ℝ (fun x : ℝ => |x - 1/2|) (1/2) := by
      convert hd.sub differentiableAt_id using 1
      funext x
      dsimp [kinkMass]
      ring
    have ha' : DifferentiableAt ℝ (fun x : ℝ => |x - 1/2|) (id 0 + 1/2) := by simpa using ha
    have hcomp := ha'.comp 0 (differentiableAt_id.add_const (1/2 : ℝ))
    apply not_differentiableAt_abs_zero
    simpa only [Function.comp_def, add_sub_cancel_right, id_eq] using hcomp
  exact ⟨hc, hm, hn, pma6_18.1 _ (hm.monotoneOn _)⟩

theorem geometric_atom_excludes_its_own_jump :
    AtomicStepSum locations weights (1/2) = 1 := by
  have hs := atomicStepSum_summable (s := locations)
    (show Summable weights from summable_geometric_two)
    (fun n => by dsimp [weights]; positivity) (1/2)
  unfold AtomicStepSum
  rw [hs.tsum_eq_zero_add]
  have hz : weights 0 * UnitStep ((1/2 : ℝ) - locations 0) = 0 := by
    norm_num [weights, locations, UnitStep]
  rw [hz, zero_add]
  have htail : (∑' n, weights (n + 1) * UnitStep ((1/2 : ℝ) - locations (n + 1))) =
      ∑' n, weights (n + 1) := by
    apply tsum_congr
    intro n
    have hlt : locations (n + 1) < (1/2 : ℝ) := by
      dsimp [locations]
      apply (div_lt_iff₀ (by positivity : (0 : ℝ) < (n + 1 : ℕ) + 2)).mpr
      have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
      norm_num only [Nat.cast_add, Nat.cast_one]
      linarith
    rw [pma6_14.2.1 _ (sub_pos.mpr hlt), mul_one]
  rw [htail]
  have hw := (show Summable weights from summable_geometric_two).tsum_eq_zero_add
  have ht : (∑' n, weights n) = 2 := tsum_geometric_two
  have hw0 : weights 0 = 1 := by norm_num [weights]
  rw [ht, hw0] at hw
  linarith

theorem negative_atom_is_not_monotone :
    ¬ Monotone (AtomicStepSum (fun _ : Fin 1 => (1/2 : ℝ)) (fun _ : Fin 1 => (-1 : ℝ))) := by
  intro h
  have hh := h (by norm_num : (0 : ℝ) ≤ 1)
  norm_num [AtomicStepSum, tsum_fintype, Fin.sum_univ_succ, UnitStep] at hh

#print axioms geometric_atom_excludes_its_own_jump
#print axioms negative_atom_is_not_monotone

theorem relative_continuity_at_atom_suffices {a b s : ℝ} {f : ℝ → ℝ}
    (has : a < s) (hsb : s < b) (hb : BoundedOn f a b)
    (hc : ContinuousWithinAt f (Icc a b) s) :
    RSIntegrable f (TranslatedStep s) a b ∧ RSIntegral f (TranslatedStep s) a b = f s :=
  pma6_15 a b s f has hsb hb (hc.continuousAt (Icc_mem_nhds has hsb))

#print axioms relative_continuity_at_atom_suffices

#print axioms step_boundary
#print axioms endpoint_atoms_differ
#print axioms discontinuity_away_from_atom_allowed
#print axioms shared_jump_rejected
#print axioms genuine_infinite_signed_integrand
#print axioms finite_quadratic_moment_value
#print axioms empty_atomic_moment
#print axioms nonlinear_density_moment
#print axioms continuous_nondifferentiable_mass_allowed
end Chapter06HostileB
```

