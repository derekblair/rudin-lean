import Rudin.PMA.Chapter11.Geometry

open Set MeasureTheory Function

namespace Rudin.PMA.Chapter11

private def IsAxisInterval (A : Set ℝ) : Prop :=
  ∃ a b l r, A = axisInterval a b l r

set_option maxHeartbeats 2000000 in
private theorem axis_inter (a b c d : ℝ) (l r k s : Bool) :
    IsAxisInterval (axisInterval a b l r ∩ axisInterval c d k s) := by
  refine ⟨max a c, min b d,
    if a < c then k else if c < a then l else l && k,
    if b < d then r else if d < b then s else r && s, ?_⟩
  ext x
  cases l <;> cases r <;> cases k <;> cases s <;>
    simp only [axisInterval, mem_inter_iff, mem_ofPred_eq, Bool.false_eq_true,
      ↓reduceIte] <;>
    split_ifs <;> simp_all [max_def, min_def] <;> grind

private theorem axis_empty : IsAxisInterval ∅ := by
  exact ⟨0, 0, false, false, by ext x; simp [axisInterval]; grind⟩

private theorem axisSemiring : IsSetSemiring {A : Set ℝ | IsAxisInterval A} where
  empty_mem := axis_empty
  inter_mem := by
    rintro _ ⟨a,b,l,r,rfl⟩ _ ⟨c,d,k,s,rfl⟩
    exact axis_inter a b c d l r k s
  sdiff_eq_sUnion' := by
    classical
    rintro A ⟨a,b,l,r,rfl⟩ B ⟨c,d,k,s,rfl⟩
    by_cases hB : (axisInterval c d k s).Nonempty
    · let L := axisInterval a b l r ∩ axisInterval a c l (!k)
      let U := axisInterval a b l r ∩ axisInterval d b (!s) r
      refine ⟨{L,U}, ?_, ?_, ?_⟩
      · intro T hT
        simp only [Finset.coe_insert, Finset.coe_singleton, mem_insert_iff, mem_singleton_iff] at hT
        rcases hT with rfl | rfl
        · exact axis_inter _ _ _ _ _ _ _ _
        · exact axis_inter _ _ _ _ _ _ _ _
      · have hdis : Disjoint L U := by
          obtain ⟨z,hz⟩ := hB
          rw [Set.disjoint_left]
          intro x hx hy
          dsimp [L,U,axisInterval] at hx hy
          dsimp [axisInterval] at hz
          cases l <;> cases r <;> cases k <;> cases s <;> simp_all <;> grind
        intro V hV W hW hVW
        simp only [Finset.coe_insert, Finset.coe_singleton, mem_insert_iff, mem_singleton_iff] at hV hW
        rcases hV with rfl | rfl <;> rcases hW with rfl | rfl
        · exact (hVW rfl).elim
        · exact hdis
        · exact hdis.symm
        · exact (hVW rfl).elim
      · ext x
        simp only [Finset.coe_insert, Finset.coe_singleton, sUnion_insert, sUnion_singleton,
          mem_union, Set.mem_sdiff, L, U, mem_inter_iff, axisInterval, mem_ofPred_eq]
        cases l <;> cases r <;> cases k <;> cases s <;> simp_all <;> grind
    · rw [Set.not_nonempty_iff_eq_empty.mp hB, Set.sdiff_empty]
      exact ⟨{axisInterval a b l r}, by
        intro V hV
        have : V = axisInterval a b l r := by simpa using hV
        subst V
        exact ⟨a,b,l,r,rfl⟩, by simp, by simp⟩


private def IsAxisBox (p : ℕ) (A : Set (Fin p → ℝ)) : Prop :=
  A = ∅ ∨ ∃ S : Fin p → Set ℝ, (∀ i, IsAxisInterval (S i)) ∧ A = Set.pi univ S

private def firstDiffBox {p : ℕ} (S T : Fin p → Set ℝ) (k : Fin p) (D : Set ℝ) :
    Set (Fin p → ℝ) :=
  Set.pi univ (fun j => if j < k then S j ∩ T j else if j = k then D else S j)

private theorem firstDiffBox_mem {p : ℕ} {S T : Fin p → Set ℝ} {k : Fin p}
    {D : Set ℝ} {x : Fin p → ℝ} (hx : x ∈ firstDiffBox S T k D) : x k ∈ D := by
  simpa [firstDiffBox] using hx k (mem_univ k)

private theorem firstDiffBox_subset {p : ℕ} {S T : Fin p → Set ℝ} {k : Fin p}
    {D : Set ℝ} (hD : D ⊆ S k \ T k) :
    firstDiffBox S T k D ⊆ Set.pi univ S \ Set.pi univ T := by
  intro x hx
  refine ⟨?_, ?_⟩
  · intro j hj
    have h := hx j hj
    dsimp [firstDiffBox] at h
    split_ifs at h with hjk hje
    · exact h.1
    · subst j
      exact (hD h).1
    · exact h
  · intro hT
    exact (hD (firstDiffBox_mem hx)).2 (hT k (mem_univ k))

private theorem axisBoxSemiring (p : ℕ) : IsSetSemiring {A | IsAxisBox p A} where
  empty_mem := Or.inl rfl
  inter_mem := by
    rintro A (rfl | ⟨S,hS,rfl⟩) B (rfl | ⟨T,hT,rfl⟩)
    · exact Or.inl (by simp)
    · exact Or.inl (by simp)
    · exact Or.inl (by simp)
    · exact Or.inr ⟨fun i => S i ∩ T i, fun i => axisSemiring.inter_mem _ (hS i) _ (hT i),
        Set.pi_inter_distrib.symm⟩
  sdiff_eq_sUnion' := by
    classical
    intro A hA B hB
    rcases hA with rfl | ⟨S,hS,rfl⟩
    · exact ⟨∅, by simp, by simp, by simp⟩
    rcases hB with rfl | ⟨T,hT,rfl⟩
    · exact ⟨{Set.pi univ S}, by simpa [IsAxisBox] using Or.inr ⟨S,hS,rfl⟩,
        by simp, by simp⟩
    let J (k : Fin p) := axisSemiring.disjointOfDiff (hS k) (hT k)
    have hJsub (k : Fin p) {D : Set ℝ} (hD : D ∈ J k) : D ⊆ S k \ T k := by
      rw [← axisSemiring.sUnion_disjointOfDiff (hS k) (hT k)]
      exact subset_sUnion_of_mem hD
    let I := Finset.univ.biUnion (fun k : Fin p => (J k).image (firstDiffBox S T k))
    have hI (D : Set (Fin p → ℝ)) : D ∈ I ↔
        ∃ k, ∃ U ∈ J k, firstDiffBox S T k U = D := by
      simp [I]
    refine ⟨I, ?_, ?_, ?_⟩
    · intro D hD
      obtain ⟨k,U,hU,rfl⟩ := (hI D).mp hD
      refine Or.inr ⟨_, ?_, rfl⟩
      intro j
      split_ifs with hjk hje
      · exact axisSemiring.inter_mem _ (hS j) _ (hT j)
      · exact axisSemiring.subset_disjointOfDiff (hS k) (hT k) hU
      · exact hS j
    · intro D hD E hE hDE
      obtain ⟨k,U,hU,rfl⟩ := (hI D).mp hD
      obtain ⟨l,V,hV,rfl⟩ := (hI E).mp hE
      change Disjoint (firstDiffBox S T k U) (firstDiffBox S T l V)
      rw [Set.disjoint_left]
      intro x hx hy
      rcases lt_trichotomy k l with hkl | hkl | hlk
      · have ht : x k ∈ T k := by
          have hh : x k ∈ S k ∩ T k := by
            simpa [firstDiffBox, hkl] using hy k (mem_univ k)
          exact hh.2
        exact (hJsub k hU (firstDiffBox_mem hx)).2 ht
      · subst l
        have hUV : U ≠ V := by rintro rfl; exact hDE rfl
        exact Set.disjoint_left.mp
          (axisSemiring.pairwiseDisjoint_disjointOfDiff (hS k) (hT k) hU hV hUV)
          (firstDiffBox_mem hx) (firstDiffBox_mem hy)
      · have ht : x l ∈ T l := by
          have hh : x l ∈ S l ∩ T l := by
            simpa [firstDiffBox, hlk] using hx l (mem_univ l)
          exact hh.2
        exact (hJsub l hV (firstDiffBox_mem hy)).2 ht
    · ext x
      constructor
      · rintro ⟨hx,hnot⟩
        let K : Finset (Fin p) := Finset.univ.filter (fun j => x j ∉ T j)
        have hK : K.Nonempty := by
          by_contra hn
          apply hnot
          intro j hj
          by_contra hnj
          have : j ∈ K := by simp [K,hnj]
          exact hn ⟨j,this⟩
        let k := K.min' hK
        have hk : k ∈ K := Finset.min'_mem K hK
        have hkT : x k ∉ T k := (Finset.mem_filter.mp hk).2
        have hlow (j : Fin p) (hj : j < k) : x j ∈ T j := by
          by_contra hnj
          have hjK : j ∈ K := by simp [K,hnj]
          exact (not_le_of_gt hj) (Finset.min'_le K j hjK)
        have hxk : x k ∈ ⋃₀ (↑(J k) : Set (Set ℝ)) := by
          rw [axisSemiring.sUnion_disjointOfDiff (hS k) (hT k)]
          exact ⟨hx k (mem_univ k),hkT⟩
        obtain ⟨U,hU,hxU⟩ := hxk
        refine Set.mem_sUnion.mpr ⟨firstDiffBox S T k U, (hI _).mpr ⟨k,U,hU,rfl⟩, ?_⟩
        intro j hj
        dsimp [firstDiffBox]
        split_ifs with hjk hje
        · exact ⟨hx j hj, hlow j hjk⟩
        · simpa [hje] using hxU
        · exact hx j hj
      · rintro ⟨D,hD,hx⟩
        obtain ⟨k,U,hU,rfl⟩ := (hI D).mp hD
        exact firstDiffBox_subset (hJsub k hU) hx


private theorem axisBox_iff {p : ℕ} {A : Set (Fin p → ℝ)} :
    IsAxisBox p A ↔ A = ∅ ∨ IsInterval A := by
  classical
  constructor
  · rintro (hA | ⟨S,hS,rfl⟩)
    · exact Or.inl hA
    · by_cases hne : (Set.pi univ S).Nonempty
      · right
        choose a b l r he using hS
        refine ⟨a,b,l,r,?_,?_⟩
        · obtain ⟨x,hx⟩ := hne
          intro i
          have hi := hx i (mem_univ i)
          rw [he i] at hi
          exact le_trans (axisInterval_subset_Icc _ _ _ _ hi).1
            (axisInterval_subset_Icc _ _ _ _ hi).2
        · exact congrArg (Set.pi univ) (funext he)
      · exact Or.inl (Set.not_nonempty_iff_eq_empty.mp hne)
  · rintro (rfl | ⟨a,b,l,r,hab,rfl⟩)
    · exact Or.inl rfl
    · exact Or.inr ⟨fun i => axisInterval (a i) (b i) (l i) (r i),
        fun i => ⟨a i,b i,l i,r i,rfl⟩,rfl⟩

private theorem elementary_eq_supClosure (p : ℕ) :
    {A : Set (Fin p → ℝ) | IsElementary A} = supClosure {A | IsAxisBox p A} := by
  ext A
  constructor
  · rintro ⟨I,hI,rfl⟩
    apply supClosed_supClosure.sSup_mem I.finite_toSet
      (subset_supClosure (axisBoxSemiring p).empty_mem)
    intro B hB
    exact subset_supClosure (axisBox_iff.mpr (Or.inr (hI B hB)))
  · apply supClosure_min ?_ ?_
    · intro B hB
      rcases axisBox_iff.mp hB with rfl | hB
      · exact isElementary_empty p
      · exact hB.isElementary
    · intro B hB C hC
      exact hB.union hC

/-- 11.4: elementary sets form a ring, including arbitrary mixtures of open and
closed coordinate endpoints. -/
theorem isSetRing_isElementary (p : ℕ) :
    IsSetRing {A : Set (Fin p → ℝ) | IsElementary A} := by
  rw [elementary_eq_supClosure]
  exact (axisBoxSemiring p).isSetRing_supClosure

/-- 11.4: differences of elementary sets are elementary. -/
theorem IsElementary.sdiff {p : ℕ} {A B : Set (Fin p → ℝ)}
    (hA : IsElementary A) (hB : IsElementary B) : IsElementary (A \ B) :=
  (isSetRing_isElementary p).sdiff_mem hA hB

/-- 11.4: intersections of elementary sets are elementary. -/
theorem IsElementary.inter {p : ℕ} {A B : Set (Fin p → ℝ)}
    (hA : IsElementary A) (hB : IsElementary B) : IsElementary (A ∩ B) :=
  (isSetRing_isElementary p).inter_mem hA hB

/-- 11.4: every elementary set has a finite pairwise disjoint interval
representation. No endpoint conventions are discarded. -/
theorem IsElementary.disjoint_intervals {p : ℕ} {A : Set (Fin p → ℝ)}
    (hA : IsElementary A) :
    ∃ I : Finset (Set (Fin p → ℝ)), (∀ B ∈ I, IsInterval B) ∧
      (↑I : Set (Set (Fin p → ℝ))).PairwiseDisjoint id ∧ A = ⋃₀ (↑I : Set (Set (Fin p → ℝ))) := by
  have hAcl : A ∈ supClosure {B | IsAxisBox p B} := by
    rw [← elementary_eq_supClosure]
    exact hA
  obtain ⟨P,hP⟩ := (axisBoxSemiring p).mem_supClosure_iff.mp hAcl
  refine ⟨P.parts, ?_, P.disjoint, ?_⟩
  · intro B hB
    rcases axisBox_iff.mp (hP hB) with hzero | hB'
    · exact (P.ne_bot hB hzero).elim
    · exact hB'
  · simpa only [Finset.sup_id_set_eq_sUnion] using P.sup_parts.symm

end Rudin.PMA.Chapter11
