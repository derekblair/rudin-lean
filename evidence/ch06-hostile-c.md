# Hostile gate C: final Chapter 6 calculus, vector, and curve nodes

**Verdict: PASS.** This is an explicit additional hostile gate for PMA-6.17 and PMA-6.19–6.27, separate from the earlier source-fidelity and ordinary proof reviews. No weakened or vacuous theorem, missing accepted conjunct, unproved existence assertion, concealed continuity requirement, wrong endpoint semantics, or new axiom was found. The reviewer authored none of the three reviewed modules.

## Frozen sources

| Module under `rudin/Rudin/PMA/Chapter06/` | Lines | SHA256 |
|---|---:|---|
| `Calculus.lean` | 674 | `ac36c016490bd347b592af764c1c6e5f544a6cd09ad7aac0c59a4c79da6c3c18` |
| `Vector.lean` | 426 | `1830138b9712dc5c6bd97293c0396df8160da84c25be76f55f0069dc3962ff98` |
| `Curve.lean` | 371 | `0fcd03a02ba4b7c7a57a647b14befac8b93fa006238ed13abc910849362d1b50` |

The exact definitions, contracts, and proof bodies were read against `research/pma-ch06-inventory.md`, `evidence/ch06-source-independent-review.md`, and the earlier contract/proof evidence. Hashes remained unchanged after checking. The inventory introduction's historical “acceptance is pending” wording is not used as the acceptance record; the independent inventory's final explicit acceptance is the controlling record.

Direct standalone Lean compilation of Calculus and Vector passed independently with no warnings or errors. Their numbered theorem and complex bridge audits returned only `propext`, `Classical.choice`, and `Quot.sound`. A supporting reviewer independently read and directly compiled Curve at the exact hash above, with the same permitted-axiom results. A scan of all three final modules found no `sorry`, `admit`, `native_decide`, custom `axiom`, or `unsafe` token. No reviewed module was edited.

## Fresh adversarial probes

The new reviewer-owned suite `/tmp/ch06-hostile-c-probes.lean` is 246 lines, SHA256 `8464b1caae34a9f87b8721e82085627eacb3a5f89d28101818b1c1929f5f7670`. Its final compile, `./lake-local env lean /tmp/ch06-hostile-c-probes.lean`, exited 0 with no warnings or errors. All twelve explicitly audited conclusions used exactly the three standard axioms. The suite is reproduced verbatim below so the evidence does not depend on temporary-file retention. Its examples are additional to the authors' embedded probes.

1. **An actual discontinuous integrable density.** Set `mass(x) = 4x + x² sin(1/x)` and `rho(x) = 4 + deriv (x² sin(1/x))`, using Chapter 5's proved zero extension and derivative existence. The suite proves the oscillatory derivative is bounded by 3 on `[-1,1]`, proves continuity away from zero, proves `rho` Riemann integrable through the finite-discontinuity theorem, proves the actual derivative relation, and proves the mass function nondecreasing. It also proves `rho` is not continuous on the source interval. The full scalar and vector density equivalences, in both directions with integral identities, instantiate for these explicit functions and arbitrary bounded integrands. Thus the noncontinuous-derivative premise is demonstrably inhabited, not merely omitted syntactically.
2. **FTC and both parts products with that same derivative.** The suite instantiates 6.21 and the complete 6.22 conjunction with `F=mass`, `f=rho`, `G=id`, and `g=1`. Both required products are integrable and the exact endpoint identity follows without continuity of `rho`.
3. **A genuinely nondifferentiable substitution.** The map `kink(x)=x+|x|/2` is proved continuous and strictly increasing, onto `[-1/2,3/2]` from `[-1,1]`, and not differentiable at zero. Main 6.19 still transports the constant integrand and gives its native Stieltjes integral equal to 2. No derivative hypothesis was smuggled into the main substitution result.
4. **A vanishing substitution derivative.** The weighted 6.19 clause instantiates for `x↦x³` on `[-1,1]`. The derivative is zero at the interior point zero, while the density `3x²` is integrable with integral 2. Positivity/nonvanishing of the derivative and differentiability of the inverse are not needed.
5. **Relative endpoints with a bad total extension.** The function equal to 17 for negative inputs and 2 otherwise is proved globally discontinuous at zero. Nevertheless its primitive has the correct within-interval derivative 2 at both endpoints of `[0,1]`. This checks that endpoint conclusions refer to the original closed interval, not a silently assumed globally continuous extension.
6. **Zero-dimensional safeguards.** A zero-dimensional vector integrand against `α(x)=-x` on `[0,1]` is rejected, despite there being no coordinates to check. With the identity integrator it is admitted and its norm integral is zero. This tests the explicit order and integrator-monotonicity guards against vacuous coordinate quantification.
7. **Both complex coordinates.** Complex multiplication by `1+i` applied to the constant integrand `i` gives integral `-1+i`. This exercises the real-imaginary cross terms and catches a dropped imaginary coordinate or incorrect sign in complex scalar linearity.

The supporting independent curve reviewer additionally compiled six fresh standard-axiom probes via Lean standard input: rejection of reversed intervals; polygonal length 1 for repeated partition points `[0,0,1,1]`; rectifiability and zero length in Euclidean dimension zero; the C¹ nonconstant line formula; equal images but different lengths for `abs` on `[-1,1]` and identity on `[0,1]`; and rejection of the incorrect zero endpoint derivative for the identity map. These are supporting reviewer results, not claims that those six proof scripts are embedded in the suite below.

## Attempts to break the statements and proofs

**6.17, 6.19–6.22.** The final contracts retain merely bounded `f` for density conversion, the integrable actual derivative, both directions of equivalence, and conditional integral equality. Main substitution asks for continuity, strict increase, and onto image only; weighted substitution separately adds derivative existence and integrability. The primitive theorem retains both continuity and uniform continuity plus the derivative at every relative continuity point, including endpoints. Integration by parts explicitly concludes integrability of both products before the identity. The derivative predicates are nonvacuous on the nondegenerate intervals specified in these contracts. The actual proofs use native Darboux bounds, common refinements, cell mean-value estimates, partition transport, and within-interval derivative estimates; they do not substitute a measure-integrability assertion for native Riemann integrability.

**6.23–6.25.** The coordinate definition carries interval order and integrator monotonicity outside the coordinate quantifier. The six-conjunct 6.23 contract contains the coordinate identification, arbitrary real vector linearity, interval splitting, integrator linearity, full density equivalence and identity, and primitive continuity/uniform continuity/derivative. The reverse density implication is actually proved coordinatewise. The Euclidean derivative bridge supplies the full vector derivative, not only an unconnected family of scalar equalities. 6.24 retains the actual derivative and coordinate integrability premises. The norm proof uses the Euclidean square-sum identity, finite scalar sums, continuous square-root composition, and the real inner-product inequality. It explicitly proves nonnegativity of the norm integral, so the zero-vector case is not handled by an invalid division. Complex integration is linked to the real two-dimensional Euclidean representation by a real linear isometry with verified real/imaginary coordinates, integral encoding, and norm preservation; its absolute-value conclusion follows from the actual vector theorem.

**6.26–6.27.** Curve continuity and interval order remain explicit; arcs require injectivity on the actual domain and closed curves require equal endpoint values. Polygonal length uses native partition points, with repeated points allowed. The length is an extended nonnegative supremum over all such partitions, preserving possible infinite length. Although the definition-node identifications are appropriately reflexive, the native length/`eVariationOn` bridge is proved in both directions: native partitions extend to admissible monotone sequences, and arbitrary variation sequences are padded with the interval endpoints. Rectifiability is equivalent to continuity plus bounded variation. The C¹ length proof first obtains finiteness independently via a derivative-bound Lipschitz estimate. Only then does it use finite `toReal` conversions. Native upper sums bound the length, and uniform continuity of the velocity controls the reverse comparison by polygonal sums. The final equality is with the native Riemann integral and includes its integrability, rather than only a totalized integral value.

## Caveats and scope

There is no blocking finding. 6.27 permits `a≤b`, which is a valid extension of the inventory's general nondegenerate derivative convention: its singleton branch is explicitly proved and both length and integral are zero. No uniqueness of a derivative on a singleton is inferred. The more general normed/inner-product codomains in the curve module include the required finite-dimensional Euclidean case and do not reduce source coverage.

This gate covers the exact three final hashes and the ten requested numbered nodes. It does not certify subsequent edits or replace the separate review of 6.18, which this reviewer authored. Only the designated evidence file and a temporary probe file were written; there were no production edits, book copies, Git operations, credential access, installations, or configuration changes.

## Reproducible reviewer probe suite

Save the following as a temporary Lean file and run it with the isolated project's `./lake-local env lean <path>` after the final modules are built.

```lean
import Rudin.PMA.Chapter06.Vector
import Rudin.PMA.Chapter06.Exceptional
import Rudin.PMA.Chapter06.Curve

noncomputable section
open Set Filter Topology
open Rudin.PMA.Chapter06
namespace HostileC

def kink (x : ℝ) : ℝ := x + |x| / 2

theorem kink_strictMono : StrictMono kink := by
  intro x y hxy
  have h := abs_sub_abs_le_abs_sub x y
  rw [abs_of_neg (sub_neg.mpr hxy)] at h
  dsimp [kink]
  linarith

theorem kink_continuous : Continuous kink :=
  continuous_id.add (continuous_id.abs.div_const 2)

theorem kink_not_differentiable : ¬ DifferentiableAt ℝ kink 0 := by
  intro h
  apply not_differentiableAt_abs_zero
  have hh := (h.sub differentiableAt_id).const_mul 2
  convert hh using 1
  funext x
  dsimp [kink]
  ring

theorem kink_substitution :
    RSIntegrable (fun _ : ℝ => 1) kink (-1) 1 ∧
      RSIntegral (fun _ : ℝ => 1) kink (-1) 1 = 2 := by
  have him : kink '' Icc (-1 : ℝ) 1 = Icc (-1 / 2 : ℝ) (3 / 2) := by
    have hh := ContinuousOn.image_Icc_of_monotoneOn (by norm_num : (-1 : ℝ) ≤ 1)
      kink_continuous.continuousOn (kink_strictMono.monotone.monotoneOn _)
    norm_num [kink] at hh ⊢
    exact hh
  have hf := rsIntegral_const (c := (1 : ℝ)) (by norm_num : (-1 / 2 : ℝ) ≤ 3 / 2)
    (show MonotoneOn (id : ℝ → ℝ) (Icc (-1 / 2) (3 / 2)) from fun _ _ _ _ h => h)
  have ht := pma6_19.1 (fun _ => 1) id kink (-1 / 2) (3 / 2) (-1) 1
    (by norm_num) (by norm_num) (kink_strictMono.strictMonoOn _) kink_continuous.continuousOn
    him (fun _ _ _ _ h => h) hf.1
  refine ⟨ht.1, ht.2.trans (hf.2.trans ?_)⟩
  norm_num

theorem zero_dimension_rejects_decreasing_integrator :
    ¬ VectorRSIntegrable (fun _ => (0 : EuclideanSpace ℝ (Fin 0)))
      (fun x => -x) 0 1 := by
  intro h
  have hm := h.2.1 (show (0 : ℝ) ∈ Icc 0 1 by norm_num)
    (show (1 : ℝ) ∈ Icc 0 1 by norm_num) (by norm_num : (0 : ℝ) ≤ 1)
  norm_num at hm

theorem zero_dimension_norm_integral :
    RSIntegrable (fun _ : ℝ => ‖(0 : EuclideanSpace ℝ (Fin 0))‖) id 0 1 ∧
      RSIntegral (fun _ : ℝ => ‖(0 : EuclideanSpace ℝ (Fin 0))‖) id 0 1 = 0 := by
  have hf : VectorRSIntegrable (fun _ => (0 : EuclideanSpace ℝ (Fin 0))) id 0 1 :=
    ⟨by norm_num, fun _ _ _ _ h => h, fun j => Fin.elim0 j⟩
  have hi := (pma6_25 0 _ id 0 1 hf).1
  have hz := rsIntegral_const (c := (0 : ℝ)) (by norm_num : (0 : ℝ) ≤ 1)
    (show MonotoneOn (id : ℝ → ℝ) (Icc 0 1) from fun _ _ _ _ h => h)
  exact ⟨hi, by simpa using hz.2⟩

theorem complex_rotation_has_both_components :
    ComplexRSIntegrable (fun _ : ℝ => (1 + Complex.I) * Complex.I) id 0 1 ∧
      ComplexRSIntegral (fun _ : ℝ => (1 + Complex.I) * Complex.I) id 0 1 = -1 + Complex.I := by
  have hh := complexRSIntegrable_const_mul complex_imaginary_constant_probe.1 (1 + Complex.I)
  rw [complex_imaginary_constant_probe.2] at hh
  refine ⟨hh.1, hh.2.trans ?_⟩
  ring_nf
  simp [add_comm]

def exteriorJump (x : ℝ) : ℝ := if x < 0 then 17 else 2

theorem primitive_uses_relative_endpoint_continuity :
    exteriorJump (-1) = 17 ∧ exteriorJump 0 = 2 ∧
    HasDerivWithinAt (fun u => RSIntegral exteriorJump id 0 u) 2 (Icc 0 1) 0 ∧
    HasDerivWithinAt (fun u => RSIntegral exteriorJump id 0 u) 2 (Icc 0 1) 1 := by
  have heq : ∀ x ∈ Icc (0 : ℝ) 1, exteriorJump x = 2 := by
    intro x hx
    simp [exteriorJump, not_lt.mpr hx.1]
  have hc : ContinuousOn exteriorJump (Icc (0 : ℝ) 1) := continuousOn_const.congr heq
  have hf := rsIntegrable_of_continuousOn (by norm_num : (0 : ℝ) ≤ 1) hc
    (show MonotoneOn (id : ℝ → ℝ) (Icc 0 1) from fun _ _ _ _ h => h)
  have hd := (pma6_20 exteriorJump 0 1 (by norm_num) hf).2.2
  refine ⟨by norm_num [exteriorJump], by norm_num [exteriorJump], ?_, ?_⟩
  · have hh := hd 0 (by norm_num) (hc 0 (by norm_num))
    rw [show exteriorJump 0 = 2 by norm_num [exteriorJump]] at hh
    exact hh
  · have hh := hd 1 (by norm_num) (hc 1 (by norm_num))
    rw [show exteriorJump 1 = 2 by norm_num [exteriorJump]] at hh
    exact hh

open Rudin.PMA.Chapter05

def rho (x : ℝ) : ℝ := 4 + deriv OscillationQuadratic x
def mass (x : ℝ) : ℝ := 4 * x + OscillationQuadratic x

theorem oscillatory_derivative_bound {x : ℝ} (hx : x ∈ Icc (-1 : ℝ) 1) :
    |deriv OscillationQuadratic x| ≤ 3 := by
  by_cases hzero : x = 0
  · subst x
    rw [oscillationQuadratic_hasDerivAt_zero.deriv]
    norm_num
  · rw [(oscillationQuadratic_hasDerivAt hzero).deriv]
    have hxabs : |x| ≤ 1 := abs_le.mpr hx
    have hmul : |2 * x * Real.sin (1 / x)| ≤ 2 := by
      rw [abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
      nlinarith [Real.abs_sin_le_one (1 / x), abs_nonneg (Real.sin (1 / x)), abs_nonneg x]
    have hh := abs_sub_le (2 * x * Real.sin (1 / x)) 0 (Real.cos (1 / x))
    simp only [sub_zero, zero_sub, abs_neg] at hh
    linarith [Real.abs_cos_le_one (1 / x)]

theorem rho_continuous_off_zero {x : ℝ} (hx : x ≠ 0) : ContinuousAt rho x := by
  have hc : ContinuousAt (fun y => 4 + (2 * y * Real.sin (1 / y) - Real.cos (1 / y))) x := by
    fun_prop
  apply hc.congr_of_eventuallyEq
  filter_upwards [eventually_ne_nhds hx] with y hy
  exact congrArg (fun d => 4 + d) (oscillationQuadratic_hasDerivAt hy).deriv

theorem rho_not_continuous : ¬ ContinuousAt rho 0 := by
  intro h
  apply oscillationQuadratic_deriv_not_continuousAt_zero
  have hh := h.sub (show ContinuousAt (fun _ : ℝ => (4 : ℝ)) 0 from continuousAt_const)
  convert hh using 1
  funext x
  dsimp [rho]
  ring

theorem rho_integrable : RIntegrable rho (-1) 1 := by
  apply pma6_10.1 rho id (-1) 1 (by norm_num)
  · refine ⟨7, ?_⟩
    intro x hx
    exact (abs_add_le 4 (deriv OscillationQuadratic x)).trans
      (by norm_num; linarith [oscillatory_derivative_bound hx])
  · exact fun _ _ _ _ h => h
  · apply (finite_singleton (0 : ℝ)).subset
    intro x hx
    by_contra hzero
    apply hx.2
    exact (rho_continuous_off_zero (by simpa using hzero)).continuousWithinAt
  · intro x hx _
    exact continuousWithinAt_id

theorem mass_derivative (x : ℝ) : HasDerivAt mass (rho x) x := by
  have hh := ((hasDerivAt_id x).const_mul 4).add
    (oscillationQuadratic_differentiable x).hasDerivAt
  convert hh using 1 <;> first | rfl | simp only [rho, mul_one]

theorem mass_monotone : MonotoneOn mass (Icc (-1 : ℝ) 1) := by
  apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc (-1 : ℝ) 1)
    (fun x _ => (mass_derivative x).continuousAt.continuousWithinAt)
    (fun x _ => (mass_derivative x).hasDerivWithinAt)
  intro x hx
  have hb := oscillatory_derivative_bound (interior_subset hx)
  dsimp [rho]
  linarith [(abs_le.mp hb).1]

theorem discontinuous_density_full_scalar_iff (f : ℝ → ℝ)
    (hf : BoundedOn f (-1) 1) :
    (RSIntegrable f mass (-1) 1 ↔ RIntegrable (fun x => f x * rho x) (-1) 1) ∧
    (RSIntegrable f mass (-1) 1 →
      RSIntegral f mass (-1) 1 = RIntegral (fun x => f x * rho x) (-1) 1) := by
  exact pma6_17 f mass rho (-1) 1 (by norm_num) mass_monotone
    (fun x _ => (mass_derivative x).hasDerivWithinAt) rho_integrable hf

theorem discontinuous_density_full_vector_iff {n : ℕ}
    (f : ℝ → EuclideanSpace ℝ (Fin n)) (hf : VectorBoundedOn f (-1) 1) :
    (VectorRSIntegrable f mass (-1) 1 ↔
      VectorRSIntegrable (fun x => rho x • f x) id (-1) 1) ∧
    (VectorRSIntegrable f mass (-1) 1 →
      VectorRSIntegral f mass (-1) 1 = VectorRSIntegral (fun x => rho x • f x) id (-1) 1) := by
  exact vectorRSIntegrable_density (by norm_num) mass_monotone
    (fun x _ => (mass_derivative x).hasDerivWithinAt) rho_integrable hf

theorem rho_not_continuousOn_source_interval : ¬ ContinuousOn rho (Icc (-1 : ℝ) 1) := by
  intro h
  exact rho_not_continuous ((h 0 (by norm_num)).continuousAt (Icc_mem_nhds (by norm_num) (by norm_num)))

theorem exteriorJump_not_continuousAt_endpoint : ¬ ContinuousAt exteriorJump 0 := by
  intro h
  obtain ⟨δ, hδ, hh⟩ := Metric.continuousAt_iff.mp h 1 (by norm_num)
  have hx : -δ / 2 < (0 : ℝ) := by linarith
  have hd : dist (-δ / 2) (0 : ℝ) < δ := by
    rw [Real.dist_eq, sub_zero, abs_of_neg hx]
    linarith
  have hbad := hh hd
  norm_num [exteriorJump, hx, Real.dist_eq] at hbad

theorem discontinuous_derivative_ftc_and_parts :
    RIntegral rho (-1) 1 = mass 1 - mass (-1) ∧
    RIntegrable (fun x => mass x * 1) (-1) 1 ∧
    RIntegrable (fun x => rho x * x) (-1) 1 ∧
    RIntegral (fun x => mass x * 1) (-1) 1 =
      mass 1 * 1 - mass (-1) * (-1) - RIntegral (fun x => rho x * x) (-1) 1 := by
  have hconst := (rsIntegral_const (c := (1 : ℝ)) (by norm_num : (-1 : ℝ) ≤ 1)
    (show MonotoneOn (id : ℝ → ℝ) (Icc (-1) 1) from fun _ _ _ _ h => h)).1
  refine ⟨?_, ?_⟩
  · exact pma6_21 mass rho (-1) 1 (by norm_num)
      (fun x _ => (mass_derivative x).hasDerivWithinAt) rho_integrable
  · exact pma6_22 mass id rho (fun _ => 1) (-1) 1 (by norm_num)
      (fun x _ => (mass_derivative x).hasDerivWithinAt)
      (fun x _ => (hasDerivAt_id x).hasDerivWithinAt) rho_integrable hconst

theorem cubic_substitution_allows_zero_derivative :
    HasDerivAt (fun x : ℝ => x ^ 3) 0 0 ∧
    RIntegrable (fun x => 3 * x ^ 2) (-1) 1 ∧
    RIntegral (fun x => 3 * x ^ 2) (-1) 1 = 2 := by
  have hder (x : ℝ) : HasDerivAt (fun x : ℝ => x ^ 3) (3 * x ^ 2) x := by
    simpa using hasDerivAt_pow 3 x
  have hmono : StrictMono (fun x : ℝ => x ^ 3) := (show Odd 3 by decide).strictMono_pow
  have hcont : Continuous (fun x : ℝ => x ^ 3) := continuous_id.pow 3
  have him : (fun x : ℝ => x ^ 3) '' Icc (-1 : ℝ) 1 = Icc (-1 : ℝ) 1 := by
    have hh := ContinuousOn.image_Icc_of_monotoneOn (by norm_num : (-1 : ℝ) ≤ 1)
      hcont.continuousOn (hmono.monotone.monotoneOn _)
    norm_num at hh
    exact hh
  have hi := rsIntegrable_of_continuousOn (by norm_num : (-1 : ℝ) ≤ 1)
    (show ContinuousOn (fun x : ℝ => 3 * x ^ 2) (Icc (-1) 1) from
      (continuous_const.mul (continuous_id.pow 2)).continuousOn)
    (show MonotoneOn (id : ℝ → ℝ) (Icc (-1) 1) from fun _ _ _ _ h => h)
  have hf := rsIntegral_const (c := (1 : ℝ)) (by norm_num : (-1 : ℝ) ≤ 1)
    (show MonotoneOn (id : ℝ → ℝ) (Icc (-1) 1) from fun _ _ _ _ h => h)
  have ht := pma6_19.2 (fun _ => 1) (fun x => x ^ 3) (fun x => 3 * x ^ 2)
    (-1) 1 (-1) 1 (by norm_num) (by norm_num) (hmono.strictMonoOn _)
    hcont.continuousOn him (fun x _ => (hder x).hasDerivWithinAt) hi hf.1
  refine ⟨by simpa using hder 0, hi, ?_⟩
  have heq := ht.2.symm.trans hf.2
  norm_num only [one_mul, id_eq, sub_neg_eq_add] at heq
  exact heq

#print axioms discontinuous_density_full_scalar_iff
#print axioms discontinuous_density_full_vector_iff
#print axioms kink_not_differentiable
#print axioms kink_substitution
#print axioms zero_dimension_rejects_decreasing_integrator
#print axioms zero_dimension_norm_integral
#print axioms complex_rotation_has_both_components
#print axioms primitive_uses_relative_endpoint_continuity
#print axioms rho_not_continuousOn_source_interval
#print axioms exteriorJump_not_continuousAt_endpoint
#print axioms discontinuous_derivative_ftc_and_parts
#print axioms cubic_substitution_allows_zero_derivative

end HostileC
```
