# Chapter 7 hostile review B: 28 nodes independently reviewed

Result: **PASS**, 2026-10-10, completed at approximately 17:15 UTC. Reviewer: `completion_evidence`, independent of the authors of all nodes covered here. No mathematical fidelity, missing-case, circularity, vacuity, totalization, or axiom finding remains.

Exact semantic coverage is **PMA-7.1 and PMA-7.7 through PMA-7.33**, 28 numbered nodes. PMA-7.2–7.6 are excluded from this independent semantic verdict because this reviewer implemented those examples; a separate reviewer covers them. This is the additional hostile B gate, not a replacement for the earlier preproof contract and final fidelity reviews.

The review directly read all 2,495 lines of the nine canonical support files below, including every contract, definition, principal proof and helper. It compared those actual statements and proof paths against the accepted inventory and this reviewer's prior independent visual extraction from the local book. It did not take other reviewers' conclusions as evidence. No book text, proof excerpts, PDF copies or page images are reproduced here. The accepted inventory SHA256 was `f8e87ad7ccb765bfd4407e251958c5378552b209d32eca60a75e13e0ca9da0f0`.

## Exact node coverage and attacks

All file references below are under `rudin/Rudin/PMA/Chapter07/`.

| Node | Principal proof | Independent attack and result |
|---|---|---|
| 7.1 | Foundations.lean:55 | Pointwise limits require actual convergence; the existence equivalence constructs a function only from certified pointwise limits. Series remain ordered Chapter 3 partial sums. PASS. |
| 7.7 | Foundations.lean:85 | One index works for the entire domain; strict/non-strict tolerances are bridged with half-epsilon. General normed codomain includes complex values. PASS. |
| 7.8 | Foundations.lean:107 | Complete codomain is explicit, and Cauchy data construct a genuine limit function. Empty domains and arbitrary domain types survive. PASS. |
| 7.9 | Foundations.lean:175 | Error is an ENNReal supremum, allowing infinite initial errors. Real-sup comparison has precisely the needed boundedness guard; empty supremum is treated separately. PASS. |
| 7.10 | MTest.lean:62 | The majorant uses ordered convergence; nonnegativity is derived on nonempty domains and the empty case is handled separately. Constant alternating harmonic terms give uniform convergence without any summable absolute majorant. PASS. |
| 7.11 | Continuity.lean:65 | Accumulation-point hypothesis produces a nontrivial punctured relative filter; the point need not belong to the domain. Both the sequence of inner limits and the outer limit genuinely converge. PASS. |
| 7.12 | Continuity.lean:191 | Arbitrary metric-domain subsets and complex functions retained. Converse caution has continuous approximants and continuous pointwise limit, with failure of uniform convergence proved via divergent native integrals. PASS. |
| 7.13 | Continuity.lean:177 | Decrease is pointwise, compactness and limit continuity explicit; noncompact `(0,1)` example has denominator strictly positive, actual pointwise convergence and a moving witness to nonuniformity. PASS. |
| 7.14 | Continuity.lean:92 | Bounded continuous complex functions live on arbitrary metric spaces, not only compact ones. Norm, zero characterization, distance, uniform/metric convergence and sequential closure bridges all use genuine bounded functions. Compact boundedness is separate. PASS. |
| 7.15 | Continuity.lean:125 | The complete-space instance is for the full bounded continuous complex function space; the produced limit belongs to that space. PASS. |
| 7.16 | Calculus.lean:178 | Native Chapter 6 Darboux integrals are retained through the entire proof. Neither integrator continuity nor positive mass is added. Complex sequence and ordered-series limits are both actual convergence statements; finite-sum linearity establishes the series identity. PASS. |
| 7.17 | Calculus.lean:303 | Derivatives are relative to the full nondegenerate closed interval, with both endpoints. Only one function value converges initially. The proof obtains uniform Cauchy control by the mean-value bound, then an actual function limit and little-o derivative estimate. No derivative continuity, integrability or ambient-extension hypothesis is smuggled in. PASS. |
| 7.18 | Nowhere.lean:220 | The existential theorem covers all real points. The tent-series witness has certified summability and continuity. Half-period shifts kill the entire tail, a dominant finite term yields growing difference quotients, and differentiability's local linear bound gives the contradiction. No totalized divergent tsum or source-construction obligation. PASS. |
| 7.19 | Equicontinuity.lean:158 | Point-dependent bounds and one common uniform bound have the correct quantifier order. The attached countable-subset consequence genuinely supplies one strict subsequence for all points. PASS. |
| 7.20 | NoSubsequence.lean:150 | Positive frequencies, exact `[0,2π]` domain, uniform bound and continuity are explicit. Strict subsequence indices are essential to orthogonality. Dominated convergence applies internally to adjacent squared differences and contradicts their fixed positive integral. No native-integral identity is claimed here. PASS. |
| 7.21 | Equicontinuity.lean:397 | Exact moving-peak formula, denominator positivity, bound, pointwise limit, reciprocal peaks and failure for every strict uniformly convergent subsequence retained. Both attached boundedness observations are proved. PASS. |
| 7.22 | Equicontinuity.lean:362 | The distance tolerance is uniform over both domain points and every family index. The explicit equivalence is with `UniformEquicontinuousOn`, not merely pointwise equicontinuity. Each member's uniform continuity and the peak counterexample are proved. PASS. |
| 7.23 | Equicontinuity.lean:156 | Countable includes empty and finite sets; no topology is required on the domain. Compact product selection supplies a strict index map and genuine pointwise limits. PASS. |
| 7.24 | Equicontinuity.lean:255 | The finite initial segment is included using a separate modulus before combining it with the uniform tail and limit modulus. All members, not merely a tail, are equicontinuous. PASS. |
| 7.25 | Equicontinuity.lean:223 | Pointwise boundedness remains the premise. A finite-cover argument proves full uniform boundedness before Arzelà–Ascoli supplies a strict uniformly convergent subsequence with continuous limit. Empty compact sets do not break the construction. PASS. |
| 7.26 | Algebra.lean:285 | Both real and complex polynomial sequences are constructed on all ordered compact intervals, including singleton intervals. Complex coefficients and evaluation at the complex coercion of the real variable are explicit. PASS. |
| 7.27 | Algebra.lean:297 | Every polynomial is normalized to vanish exactly at zero; subtracting its constant value preserves uniform convergence. `a=0` survives. PASS. |
| 7.28 | Algebra.lean:350 | Nonempty, non-unital algebra convention is explicit and accepted; constants are not added. Real/complex operations, sequential uniform closure and both polynomial closure examples are complete. PASS. |
| 7.29 | Algebra.lean:452 | Only individual boundedness is assumed, on an arbitrary domain. The temporary discrete topology is internal to a proved BCF closure bridge, not an extra premise. The bridge uses `NonUnitalSubalgebra` and proves both algebra closure and sequential closedness. PASS. |
| 7.30 | Algebra.lean:194 | Separation concerns distinct pairs. Nowhere vanishing has a point-dependent witness. Real/complex polynomial examples and failure of even polynomials to separate `-1,1` are explicit. PASS. |
| 7.31 | Algebra.lean:238 | Interpolation uses the separating function and separate nonzero witnesses at each point, with nonzero denominators proved. No unit, compactness or continuity is assumed; real and arbitrary complex target values retained. PASS. |
| 7.32 | Algebra.lean:588 | The non-unital algebra reaches lattice closure using exactly-zero polynomials, then strong two-point interpolation and compact lattice approximation. Empty-space behavior is sound because the algebra is nonempty. No unit is added. PASS. |
| 7.33 | Algebra.lean:740 | Self-adjointness constructs the real/imaginary real algebra, with separation and nonvanishing explicitly transferred. The independent failure witness is polynomial functions on the closed complex unit disk; conjugation is continuous but cannot be a uniform polynomial limit because it is not complex differentiable at zero. All witness premises are proved. PASS. |

Dependency boundaries: 7.20 legitimately uses pinned Mathlib measure-integral dominated convergence only to prove a statement about pointwise subsequences; this is not a Chapter 11 completion claim or an implicit Chapter 6 integral replacement. The 7.33 failure witness uses the pinned holomorphic uniform-limit theorem. The statement permits such a witness. The tent witness for 7.18 is a proof choice rather than an omitted book-construction obligation.

## Fresh verification and independent probes

Every reviewed canonical module was freshly compiled directly with `./lake-local env lean Rudin/PMA/Chapter07/<Module>.lean`: Basic, Foundations, MTest, Continuity, Calculus, Nowhere, NoSubsequence, Equicontinuity and Algebra. All nine returned exit 0 with no warnings/errors. The compiler commands did not modify source files. A scan of those files found no `sorry`, `admit`, `native_decide`, `axiom` or `unsafe` token.

A new standalone probe suite was written independently at `/tmp/ch07-hostile-b-main-probes.lean`, importing the frozen canonical Chapter 7 integration. It contains **13 proved boundary/fidelity theorems in 173 lines**; its exact source is retained verbatim below so the temporary file need not be preserved. Final SHA256: `1a682e39f3f2df29c6e78909266cd3e13baa38a22cd10381c0e09feb826338f8`.

The final fresh compiler invocation returned exit 0, no warnings/errors, and:

```text
Axiom audit for Rudin.PMA.Chapter07: checked 344 declarations; only propext, Classical.choice, and Quot.sound.
```

This recursively audits every imported Chapter 7 declaration, including the new probes. Inclusion of 7.2–7.6 in that mechanical audit does not expand this reviewer's independent semantic coverage.

The new probes establish: an unbounded identity error is infinite; uniform convergence still permits that infinite initial error; empty-domain uniform existence and countable selection need no global bounds; an imaginary constant integrated against the source's left-continuous step retains mass at the left endpoint; the complex derivative theorem admits a deliberately bad exterior extension; a genuine non-unital algebra and its uniform closure exclude one; empty algebra is excluded even on an empty domain while the nonempty zero algebra is dense there; singleton absolute-value approximation keeps exact zero; a continuous singleton family on a noncompact domain need not satisfy source uniform equicontinuity; and nowhere vanishing does not require one member nonzero everywhere.

## Frozen source hashes

Hashes were captured before reading and checked again after fresh compilation/probes; all nine were unchanged.

| Canonical support module | SHA256 |
|---|---|
| Basic.lean | `b6b8b58999ad0025fd3ab28bc0ba3a4df5a07cc395158b99a14c05055bfa2b1a` |
| Foundations.lean | `941938d68a48db2a4e0ab70ba0b39d51828fc91602a4583ab449f8ad1c4d5742` |
| MTest.lean | `c364dc78a12a188264c39c24f8dfd5da1edc699491442d18cf78b2565aef3e05` |
| Continuity.lean | `8dae8b99a9de2d8b996c47e62ad3ae5396efb503b36a686374f0349a4efa1977` |
| Calculus.lean | `0bc805601a65a1261e944ae9d180b3cb0344c0d9484fc766f1d3df6c3411580d` |
| Nowhere.lean | `6d04835c41bda7f4315fc7ac3e65c32b1ccc1e778b8ea145a424193d7d406612` |
| NoSubsequence.lean | `a0f5e92e41fe61bbda351ab4a0497ef621ec7f3ceb7f136f742dfaca2c69f7b6` |
| Equicontinuity.lean | `baffc08a75f000487493d784939d9b9af42f7c3b4441a52d73a6664aa9ec6ff0` |
| Algebra.lean | `44ebf1128a6a4f6409b4784c648ccecaf804a1ab354c406c02dcde638fde65c2` |

No production files, canonical proofs, protected Chapter 5/6 files, root imports, Git state, credentials, configuration or pre-existing sessions were changed. There is no remaining blocker for this 28-node hostile B verdict. Whole-chapter acceptance also requires the independent B review of 7.2–7.6 and the parent's final integration checks.

## Exact independent probe source

```lean
import Rudin.PMA.Chapter07
import Rudin.PMA.Chapter01Audit

noncomputable section
open Set Filter Topology
open scoped ENNReal
namespace Rudin.PMA.Chapter07.HostileB

def badInitial (n : ℕ) (x : ℝ) : ℝ := if n = 0 then x else 0

theorem identity_error_infinite : UniformError (fun x : ℝ => x) (fun _ => 0) univ = ⊤ := by
  apply ENNReal.eq_top_of_forall_nnreal_le
  intro r
  have h : ENNReal.ofReal ‖(r : ℝ) - 0‖ ≤
      UniformError (fun x : ℝ => x) (fun _ => 0) univ := by
    unfold UniformError
    exact le_iSup_of_le (⟨(r : ℝ), mem_univ _⟩ : (univ : Set ℝ)) le_rfl
  simpa [UniformError, Real.norm_eq_abs, abs_of_nonneg r.coe_nonneg] using h

theorem uniform_despite_infinite_initial_error :
    UniformConvergesOn badInitial (fun _ => 0) univ ∧
    UniformError (badInitial 0) (fun _ => 0) univ = ⊤ ∧
    Tendsto (fun n => UniformError (badInitial n) (fun _ => 0) univ) atTop (𝓝 0) := by
  have hu : UniformConvergesOn badInitial (fun _ => 0) univ := by
    apply Metric.tendstoUniformlyOn_iff.mpr
    intro ε hε
    filter_upwards [eventually_ge_atTop 1] with n hn x _
    simpa [badInitial, show n ≠ 0 by omega] using hε
  refine ⟨hu, ?_, (uniformConvergesOn_iff_uniformError_tendsto _ _ _).mp hu⟩
  change UniformError (fun x : ℝ => x) (fun _ => 0) univ = ⊤
  exact identity_error_infinite

theorem empty_domain_has_limit_without_any_pointwise_bound (F : ℕ → ℝ → ℂ) :
    ∃ f : ℝ → ℂ, UniformConvergesOn F f ∅ := by
  apply (pma7_8 F ∅).mpr
  intro ε _
  exact ⟨0, fun _ _ _ _ _ hx => False.elim hx⟩

theorem empty_countable_selection (F : ℕ → ℝ → ℂ) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ f : ℝ → ℂ,
      ∀ x ∈ (∅ : Set ℝ), Tendsto (fun n => F (φ n) x) atTop (𝓝 (f x)) := by
  exact pma7_23 ∅ F countable_empty (fun _ hx => False.elim hx)

theorem native_complex_left_endpoint_mass :
    Chapter06.ComplexRSIntegrable (fun _ => Complex.I) Chapter06.UnitStep 0 1 ∧
    Chapter06.ComplexRSIntegral (fun _ => Complex.I) Chapter06.UnitStep 0 1 = Complex.I ∧
    Tendsto (fun _ : ℕ => Chapter06.ComplexRSIntegral
      (fun _ => Complex.I) Chapter06.UnitStep 0 1) atTop (𝓝 Complex.I) := by
  have hm := Chapter06.pma6_14.2.2
  have hr := Chapter06.rsIntegral_const (c := (0 : ℝ)) (α := Chapter06.UnitStep)
    (a := 0) (b := 1) (by norm_num) (hm.monotoneOn _)
  have hi := Chapter06.rsIntegral_const (c := (1 : ℝ)) (α := Chapter06.UnitStep)
    (a := 0) (b := 1) (by norm_num) (hm.monotoneOn _)
  have hI : Chapter06.ComplexRSIntegrable (fun _ => Complex.I) Chapter06.UnitStep 0 1 :=
    ⟨by simpa using hr.1, by simpa using hi.1⟩
  have he : Chapter06.ComplexRSIntegral (fun _ => Complex.I) Chapter06.UnitStep 0 1 = Complex.I := by
    simp [Chapter06.ComplexRSIntegral, hr.2, hi.2, Chapter06.UnitStep]
  have ht := (pma7_16.1 (fun _ _ => Complex.I) (fun _ => Complex.I)
    Chapter06.UnitStep 0 1 (by norm_num) (hm.monotoneOn _) (fun _ => hI)
    (calculus_constFamily_uniform _ _)).2
  exact ⟨hI, he, by simpa only [he] using ht⟩

def badExterior (x : ℝ) : ℂ := if x ∈ Icc (0 : ℝ) 1 then (x : ℂ) * Complex.I else 100

theorem complex_derivative_uses_relative_endpoints :
    ∃ f : ℝ → ℂ,
      TendstoUniformlyOn (fun _ : ℕ => badExterior) f atTop (Icc 0 1) ∧
      f 1 = Complex.I ∧ HasDerivWithinAt f Complex.I (Icc 0 1) 0 ∧
      HasDerivWithinAt f Complex.I (Icc 0 1) 1 := by
  have hd (x : ℝ) (hx : x ∈ Icc (0 : ℝ) 1) :
      HasDerivWithinAt badExterior Complex.I (Icc 0 1) x := by
    have h : HasDerivWithinAt (fun y : ℝ => (y : ℂ) * Complex.I) Complex.I (Icc 0 1) x := by
      simpa using ((Complex.ofRealCLM.hasDerivAt (x := x)).mul_const Complex.I).hasDerivWithinAt
    apply h.congr_of_mem _ hx
    intro y hy
    simp [badExterior, hy]
  obtain ⟨f, hf, h1, hdf⟩ := pma7_17.1 (fun _ => badExterior)
    (fun _ _ => Complex.I) (fun _ => Complex.I) 0 1 1 Complex.I (by norm_num)
    (by norm_num) (fun _ => hd) (by simp [badExterior])
    (calculus_constFamily_uniform _ _)
  exact ⟨f, hf, h1, (hdf 0 (by norm_num)).1, (hdf 1 (by norm_num)).1⟩

def zeroAtFalse : Set (Bool → ℝ) := {f | f false = 0}

theorem genuine_nonunital_algebra :
    IsFunctionAlgebra zeroAtFalse ∧ (fun _ : Bool => (1 : ℝ)) ∉ zeroAtFalse := by
  refine ⟨⟨⟨fun _ => 0, rfl⟩, ?_, ?_, ?_⟩, ?_⟩
  · intro f hf g hg
    change f false + g false = 0
    simp_all [zeroAtFalse]
  · intro f hf g hg
    change f false * g false = 0
    simp_all [zeroAtFalse]
  · intro c f hf
    change c * f false = 0
    simp_all [zeroAtFalse]
  · simp [zeroAtFalse]

theorem nonunital_closure_still_excludes_one :
    IsFunctionAlgebra (AlgebraUniformClosure zeroAtFalse) ∧
    IsAlgebraUniformlyClosed (AlgebraUniformClosure zeroAtFalse) ∧
    (fun _ : Bool => (1 : ℝ)) ∉ AlgebraUniformClosure zeroAtFalse := by
  have hb (f : Bool → ℝ) (_ : f ∈ zeroAtFalse) : AlgebraFunctionBounded f := by
    refine ⟨|f false| + |f true|, fun x => ?_⟩
    cases x <;> simp only [Real.norm_eq_abs] <;>
      linarith [abs_nonneg (f false), abs_nonneg (f true)]
  have h := pma7_29.1 Bool zeroAtFalse genuine_nonunital_algebra.1 hb
  refine ⟨h.1, h.2.1, ?_⟩
  rintro ⟨F, hF, ht⟩
  have h0 : Tendsto (fun n => F n false) atTop (𝓝 0) := by
    simpa only [show (fun n => F n false) = (fun _ : ℕ => 0) from
      funext (fun n => hF n)] using (tendsto_const_nhds :
        Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0))
  have heq := tendsto_nhds_unique (ht.tendsto_at false) h0
  norm_num at heq

theorem empty_algebra_excluded_even_on_empty_space :
    ¬ IsFunctionAlgebra (∅ : Set (Empty → ℝ)) := by
  intro h
  exact not_nonempty_empty h.1

theorem empty_space_zero_algebra_dense :
    AlgebraUniformClosure ({fun _ : Empty => (0 : ℝ)} : Set (Empty → ℝ)) =
      {f : Empty → ℝ | Continuous f} := by
  have hA : IsFunctionAlgebra ({fun _ : Empty => (0 : ℝ)} : Set (Empty → ℝ)) := by
    refine ⟨by simp, ?_, ?_, ?_⟩
    all_goals intros; apply Set.mem_singleton_iff.mpr; funext x; exact x.elim
  exact pma7_32 Empty _ hA (fun _ _ => continuous_of_discreteTopology)
    (fun x => x.elim) (fun x => x.elim)

theorem singleton_abs_approximation_keeps_exact_zero :
    ∃ P : ℕ → Polynomial ℝ, (∀ n, (P n).eval 0 = 0) ∧
      TendstoUniformlyOn (fun n x => (P n).eval x) (fun x : ℝ => |x|)
        atTop ({0} : Set ℝ) := by
  simpa using pma7_27 0 le_rfl

theorem pointwise_equicontinuity_would_be_too_weak :
    (∀ _i : Unit, Continuous (fun x : ℝ => x ^ 2)) ∧
      ¬ SourceEquicontinuousOn (fun _ : Unit => fun x : ℝ => x ^ 2) univ := by
  refine ⟨fun _ => continuous_id.pow 2, ?_⟩
  intro h
  obtain ⟨δ, hδ, hd⟩ := h 1 zero_lt_one
  have hneq : δ ≠ 0 := ne_of_gt hδ
  have hdist : dist δ⁻¹ (δ⁻¹ + δ / 2) < δ := by
    rw [Real.dist_eq]
    have he : δ⁻¹ - (δ⁻¹ + δ / 2) = -(δ / 2) := by ring
    rw [he, abs_neg, abs_of_pos (half_pos hδ)]
    exact half_lt_self hδ
  have hb := hd δ⁻¹ (mem_univ _) (δ⁻¹ + δ / 2) (mem_univ _) hdist ()
  rw [Real.dist_eq] at hb
  have hi : δ⁻¹ * δ = 1 := inv_mul_cancel₀ hneq
  have hl := (abs_lt.mp hb).1
  nlinarith [sq_nonneg δ]

def pointDependentWitnesses : Set (Bool → ℝ) :=
  {f | f = (fun x => if x then 0 else 1) ∨ f = (fun x => if x then 1 else 0)}

theorem nowhere_vanishing_does_not_require_one_global_witness :
    FunctionVanishesNowhere pointDependentWitnesses ∧
      ¬ ∃ f ∈ pointDependentWitnesses, ∀ x, f x ≠ 0 := by
  constructor
  · intro x
    cases x
    · exact ⟨fun x => if x then 0 else 1, Or.inl rfl, by norm_num⟩
    · exact ⟨fun x => if x then 1 else 0, Or.inr rfl, by norm_num⟩
  · rintro ⟨f, hf, hn⟩
    rcases hf with rfl | rfl
    · simpa using hn true
    · simpa using hn false

end Rudin.PMA.Chapter07.HostileB

run_cmd Rudin.PMA.Audit.checkNamespaceAxioms `Rudin.PMA.Chapter07
```
