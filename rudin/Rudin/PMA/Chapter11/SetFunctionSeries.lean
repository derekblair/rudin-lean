import Rudin.PMA.Chapter11.Foundations
import Rudin.PMA.Chapter03

open Set Filter Topology
open scoped BigOperators

namespace Rudin.PMA.Chapter11

variable {X : Type*} {R : Set (Set X)} {φ : Set X → EReal}

/-- 11.2's rearrangement observation: when the value of a countably additive
set function is finite on the union, the corresponding series is absolutely
convergent. This lemma states the finite-valued series form explicitly. -/
theorem pma11_2_absolute_series (hc : CountablyAdditiveSetFunction R φ)
    (A : ℕ → Set X) (hA : ∀ n, A n ∈ R)
    (hd : Pairwise (fun i j => Disjoint (A i) (A j))) (hu : (⋃ n, A n) ∈ R)
    (a : ℕ → ℝ) (ha : ∀ n, φ (A n) = (a n : EReal))
    (s : ℝ) (hs : φ (⋃ n, A n) = (s : EReal)) :
    Summable (fun n => |a n|) := by
  have hsum (g : ℕ → ℝ) (n : ℕ) :
      ((∑ i ∈ Finset.range n, g i : ℝ) : EReal) = ∑ i ∈ Finset.range n, (g i : EReal) := by
    induction n with
    | zero => simp
    | succ n ih => simp only [Finset.sum_range_succ, EReal.coe_add, ih]
  have hp (e : Equiv.Perm ℕ) :
      Tendsto (fun N => ((Chapter03.PartialSums (a ∘ e) N : ℝ) : EReal)) atTop (𝓝 (s : EReal)) := by
    have heq : (⋃ n, A (e n)) = ⋃ n, A n := e.surjective.iUnion_comp A
    have ht := hc (fun n => A (e n)) (fun n => hA (e n))
      (hd.comp_of_injective e.injective) (by simpa only [heq] using hu)
    rw [heq, hs] at ht
    simpa only [ha, Chapter03.PartialSums, Function.comp_def, hsum] using ht
  have hcvg : Chapter03.SeriesConverges a := by
    refine ⟨s, ?_⟩
    exact EReal.tendsto_coe.mp (by simpa using hp (Equiv.refl ℕ))
  have habs : Chapter03.SeriesAbsolutelyConverges a := by
    by_contra h
    obtain ⟨e, _, he⟩ := Chapter03.pma3_54 a ⊥ ⊤ ⟨hcvg, h⟩ bot_le
    have hfinite := (hp e).limsup_eq
    rw [he] at hfinite
    exact EReal.top_ne_coe s hfinite
  simpa only [Real.norm_eq_abs] using
    (Chapter03.seriesAbsolutelyConverges_iff_summable_norm a).mp habs

/-- Finiteness on the union forces finiteness on each member of a disjoint
sequence. Thus the real-valued series formulation above loses no finite-sum case. -/
theorem setFunction_finite_of_subset (hR : SetRing R)
    (hφ : AdmissibleSetFunction R φ) (hc : CountablyAdditiveSetFunction R φ)
    {A B : Set X} (hA : A ∈ R) (hB : B ∈ R) (hAB : A ⊆ B)
    (ht : φ B ≠ ⊤) (hb : φ B ≠ ⊥) : φ A ≠ ⊤ ∧ φ A ≠ ⊥ := by
  have hdecomp : A ∪ (B \ A) = B := by
    ext x
    simp only [mem_union, Set.mem_sdiff]
    constructor
    · rintro (hx | hx)
      · exact hAB hx
      · exact hx.1
    · intro hx
      by_cases h : x ∈ A
      · exact Or.inl h
      · exact Or.inr ⟨hx, h⟩
  have he := countablyAdditive_additive hR hφ hc A hA (B \ A)
    (hR.sdiff_mem hB hA) disjoint_sdiff_right
  rw [hdecomp] at he
  have hbot : φ A ≠ ⊥ ∧ φ (B \ A) ≠ ⊥ := EReal.add_ne_bot_iff.mp (he ▸ hb)
  refine ⟨?_, hbot.1⟩
  intro htop
  apply ht
  rw [he, htop]
  exact EReal.top_add_of_ne_bot hbot.2

/-- Complete finite-total form of the absolute convergence observation in 11.2. -/
theorem pma11_2_absolute_of_finite_total (hR : SetRing R)
    (hφ : AdmissibleSetFunction R φ) (hc : CountablyAdditiveSetFunction R φ)
    (A : ℕ → Set X) (hA : ∀ n, A n ∈ R)
    (hd : Pairwise (fun i j => Disjoint (A i) (A j))) (hu : (⋃ n, A n) ∈ R)
    (ht : φ (⋃ n, A n) ≠ ⊤) (hb : φ (⋃ n, A n) ≠ ⊥) :
    Summable (fun n => |(φ (A n)).toReal|) := by
  apply pma11_2_absolute_series hc A hA hd hu (fun n => (φ (A n)).toReal)
    (fun n => ?_) (φ (⋃ n, A n)).toReal (EReal.coe_toReal ht hb).symm
  have hfin := setFunction_finite_of_subset hR hφ hc (hA n) hu
    (subset_iUnion A n) ht hb
  exact (EReal.coe_toReal hfin.1 hfin.2).symm

end Rudin.PMA.Chapter11
