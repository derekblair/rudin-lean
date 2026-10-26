import Rudin.PMA.Chapter10.SimplexChains
import Rudin.PMA.Chapter10.StandardForms
import Mathlib.Analysis.Calculus.BumpFunction.SmoothApprox
import Mathlib.Topology.TietzeExtension

noncomputable section
set_option autoImplicit false
open Set Function MeasureTheory Filter Module Metric
open scoped BigOperators Topology

namespace Rudin.PMA.Chapter10
open Chapter09

lemma smooth_approximation_on_compact {n : ℕ} {K : Set (Euclidean n)}
    (hK : IsCompact K) {f : Euclidean n → ℝ} (hf : ContinuousOn f K)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ g : Euclidean n → ℝ, ContDiff ℝ (↑(⊤ : ENat)) g ∧ ∀ x ∈ K, |g x - f x| < ε := by
  let fK : C(K, ℝ) := ⟨fun x => f x, continuousOn_iff_continuous_restrict.mp hf⟩
  obtain ⟨F, hF⟩ := fK.exists_restrict_eq hK.isClosed
  have hd := (ContinuousMap.dense_setOfPred_contDiff (E := Euclidean n) (F := ℝ)) F
  rw [mem_closure_iff_nhds_basis
    (nhds_basis_uniformity uniformity_basis_dist.compactConvergenceUniformity)] at hd
  simp only [Prod.forall, mem_ofPred_eq, and_imp] at hd
  obtain ⟨g, hg, hdist⟩ := hd K ε hK hε
  refine ⟨g, hg, fun x hx => ?_⟩
  have he : F x = f x := congrArg (fun H : C(K, ℝ) => H ⟨x, hx⟩) hF
  simpa only [Real.dist_eq, he] using hdist x hx

/-- Reconstruct a homogeneous form from its standard coefficient tuple. -/
def standardCoefficientForm {n k : ℕ} (a : StandardIndex n k → Euclidean n → ℝ) :
    FormField n := fun x => ∑ S, a S x • standardWedge S

lemma standardCoefficientForm_isCFormOn {n k : ℕ} {r : ℕ}
    {E : Set (Euclidean n)} {a : StandardIndex n k → Euclidean n → ℝ}
    (ha : ∀ S, ContDiffOn ℝ r (a S) E) : IsCFormOn r E k (standardCoefficientForm a) := by
  constructor
  · intro x hx
    exact Submodule.sum_mem _ (fun S _ => Submodule.smul_mem _ _ (standardWedge_mem S))
  · intro T
    have he : formCoefficient (standardCoefficientForm a) T = fun x =>
        ∑ S, a S x * (exteriorBasis n).repr (standardWedge S) T := by
      funext x
      simp [formCoefficient, standardCoefficientForm]
    rw [he]
    exact ContDiffOn.sum fun S _ => (ha S).mul contDiffOn_const

lemma standardCoefficientForm_coefficient {n k : ℕ}
    (a : StandardIndex n k → Euclidean n → ℝ) (S : StandardIndex n k) (x : Euclidean n) :
    formCoefficient (standardCoefficientForm a) S.val x = a S x := by
  classical
  simp only [formCoefficient, standardCoefficientForm, standardWedge, map_sum, map_smul,
    Basis.repr_self, Finsupp.finsetSum_apply, Finsupp.smul_apply, smul_eq_mul]
  have he : ∀ T : StandardIndex n k,
      a T x * (Finsupp.single T.val 1) S.val = if T = S then a S x else 0 := by
    intro T
    by_cases h : T = S
    · subst T; simp
    · have hv : T.val ≠ S.val := fun h' => h (Subtype.ext h')
      simp [h, hv, Finsupp.single_apply]
  simp_rw [he]
  simp

lemma continuous_form_smooth_approximation {n k : ℕ} {E K : Set (Euclidean n)}
    (hK : IsCompact K) (hKE : K ⊆ E) {ω : FormField n} (hω : IsFormOn E k ω)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ η : FormField n, IsCFormOn 1 E k η ∧
      ∀ S : StandardIndex n k, ∀ x ∈ K,
        |formCoefficient η S.val x - formCoefficient ω S.val x| < ε := by
  classical
  have ha : ∀ S : StandardIndex n k, ∃ g : Euclidean n → ℝ,
      ContDiff ℝ (↑(⊤ : ENat)) g ∧ ∀ x ∈ K, |g x - formCoefficient ω S.val x| < ε :=
    fun S => smooth_approximation_on_compact hK ((hω.2 S.val).mono hKE) hε
  choose a ha he using ha
  refine ⟨standardCoefficientForm a, standardCoefficientForm_isCFormOn
    (fun S => ((ha S).of_le (by simp)).contDiffOn), ?_⟩
  intro S x hx
  rw [standardCoefficientForm_coefficient]
  exact he S x hx

end Rudin.PMA.Chapter10
