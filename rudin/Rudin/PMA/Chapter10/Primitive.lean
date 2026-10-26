import Rudin.PMA.Chapter10.Prerequisites

set_option autoImplicit false
noncomputable section
open Set Filter Topology Module
open scoped BigOperators

namespace Rudin.PMA.Chapter10

open Chapter09

/-- Replace one coordinate by a scalar function. -/
def primitiveMap {n : ℕ} (m : Fin n) (g : Euclidean n → ℝ)
    (x : Euclidean n) : Euclidean n :=
  x + (g x - x m) • coordinateVector n m

/-- The source notion on the stated domain; no regularity is built into it. -/
def IsPrimitiveOn {n : ℕ} (G : Euclidean n → Euclidean n)
    (E : Set (Euclidean n)) : Prop :=
  ∃ m : Fin n, ∃ g : Euclidean n → ℝ, EqOn G (primitiveMap m g) E

/-- The linear operator interchanging two coordinates, with equal indices also
allowed for the identity case needed in the factorization theorem. -/
def flipOperator {n : ℕ} (i j : Fin n) : Operator n n :=
  ∑ k : Fin n, (EuclideanSpace.proj (Equiv.swap i j k)).smulRight (coordinateVector n k)

/-- A flip itself exchanges distinct coordinates. -/
def IsFlip {n : ℕ} (B : Operator n n) : Prop :=
  ∃ i j : Fin n, i ≠ j ∧ B = flipOperator i j

/-- Projection onto the first `m` coordinates, numbered from zero. -/
def prefixProjection (n m : ℕ) : Operator n n :=
  ∑ j : Fin n, if j.val < m then
    (EuclideanSpace.proj j).smulRight (coordinateVector n j) else 0

/-- Function lists are composed in their written order: the rightmost acts first. -/
def composeMaps {X : Type*} (L : List (X → X)) : X → X :=
  L.foldr Function.comp id

/-- Exactly the local properties demanded of each primitive factor in 10.7. -/
def PrimitiveNearZero {n : ℕ} (G : Euclidean n → Euclidean n) : Prop :=
  ∃ U : Set (Euclidean n), IsOpen U ∧ (0 : Euclidean n) ∈ U ∧
    IsPrimitiveOn G U ∧ C1On G U ∧ G 0 = 0 ∧ (fderiv ℝ G 0).IsInvertible

def pma10_5_contract : Prop :=
  (∀ (n : ℕ) (m : Fin n) (g : Euclidean n → ℝ) (x : Euclidean n) (i : Fin n),
    primitiveMap m g x i = if i = m then g x else x i) ∧
  (∀ (n : ℕ) (G : Euclidean n → Euclidean n) (E : Set (Euclidean n)),
    IsPrimitiveOn G E ↔ ∃ m : Fin n, ∃ g : Euclidean n → ℝ, ∀ x ∈ E,
      G x = (∑ i ∈ Finset.univ.erase m, x i • coordinateVector n i) +
        g x • coordinateVector n m) ∧
  (∀ (n : ℕ) (m : Fin n) (g : Euclidean n → ℝ) (a : Euclidean n),
    DifferentiableAt ℝ g a →
    HasFDerivAt (primitiveMap m g)
      (ContinuousLinearMap.id ℝ (Euclidean n) +
        (fderiv ℝ g a - EuclideanSpace.proj m).smulRight (coordinateVector n m)) a ∧
    (∀ i j : Fin n, operatorMatrix (fderiv ℝ (primitiveMap m g) a) i j =
      if i = m then coordinatePartial g a j else if i = j then 1 else 0) ∧
    jacobian (primitiveMap m g) a = coordinatePartial g a m ∧
    ((fderiv ℝ (primitiveMap m g) a).IsInvertible ↔ coordinatePartial g a m ≠ 0))

def pma10_6_contract : Prop :=
  (∀ (n : ℕ) (i j k : Fin n) (x : Euclidean n),
    flipOperator i j x k = x (Equiv.swap i j k)) ∧
  (∀ (n : ℕ) (B : Operator n n), IsFlip B ↔
    ∃ i j : Fin n, i ≠ j ∧ ∀ k : Fin n,
      B (coordinateVector n k) = coordinateVector n (Equiv.swap i j k)) ∧
  (∀ (n : ℕ) (i j : Fin n),
    (flipOperator i j).comp (flipOperator i j) = ContinuousLinearMap.id ℝ (Euclidean n)) ∧
  (∀ (n m : ℕ) (x : Euclidean n) (i : Fin n),
    prefixProjection n m x i = if i.val < m then x i else 0) ∧
  (∀ n : ℕ, prefixProjection n 0 = 0 ∧
    prefixProjection n n = ContinuousLinearMap.id ℝ (Euclidean n)) ∧
  (∀ (n m : ℕ), m ≤ n →
    (prefixProjection n m).toLinearMap.range =
      Submodule.span ℝ (coordinateVector n '' {i : Fin n | i.val < m}) ∧
    (prefixProjection n m).toLinearMap.ker =
      Submodule.span ℝ (coordinateVector n '' {i : Fin n | m ≤ i.val}))

/-- `G` lists the primitive factors in order `G_n,...,G_1`; `B` lists
`B_1,...,B_(n-1)`. Thus the written composite is precisely the book's order.
Positive dimension is the source convention needed to choose a coordinate. -/
def pma10_7_contract : Prop :=
  ∀ (n : ℕ), 0 < n → ∀ (E : Set (Euclidean n)) (F : Euclidean n → Euclidean n),
    IsOpen E → (0 : Euclidean n) ∈ E → C1On F E → F 0 = 0 →
    (fderiv ℝ F 0).IsInvertible →
    ∃ (G : List (Euclidean n → Euclidean n)) (B : List (Operator n n))
      (U : Set (Euclidean n)),
      G.length = n ∧ B.length = n - 1 ∧
      (∀ g ∈ G, PrimitiveNearZero g) ∧
      (∀ b ∈ B, IsFlip b ∨ b = ContinuousLinearMap.id ℝ (Euclidean n)) ∧
      IsOpen U ∧ (0 : Euclidean n) ∈ U ∧ U ⊆ E ∧
      EqOn F (composeMaps ((B.map (fun (b : Operator n n) =>
        (b : Euclidean n → Euclidean n))) ++ G)) U

@[simp] theorem coordinateVector_apply {n : ℕ} (i j : Fin n) :
    coordinateVector n i j = if j = i then 1 else 0 := by
  simp [coordinateVector, EuclideanSpace.basisFun_apply, eq_comm]

theorem sum_coordinates {n : ℕ} (x : Euclidean n) :
    ∑ i : Fin n, x i • coordinateVector n i = x := by
  simpa [coordinateVector] using (EuclideanSpace.basisFun (Fin n) ℝ).sum_repr x

@[simp] theorem primitiveMap_apply {n : ℕ} (m : Fin n) (g : Euclidean n → ℝ)
    (x : Euclidean n) (i : Fin n) :
    primitiveMap m g x i = if i = m then g x else x i := by
  by_cases h : i = m
  · subst i
    simp [primitiveMap] <;> ring
  · simp [primitiveMap, h]

theorem primitiveMap_sum {n : ℕ} (m : Fin n) (g : Euclidean n → ℝ)
    (x : Euclidean n) :
    primitiveMap m g x = (∑ i ∈ Finset.univ.erase m, x i • coordinateVector n i) +
      g x • coordinateVector n m := by
  ext i
  by_cases h : i = m
  · subst i
    simp
  · simp [h]

theorem hasFDerivAt_primitiveMap {n : ℕ} {m : Fin n} {g : Euclidean n → ℝ}
    {a : Euclidean n} (hg : DifferentiableAt ℝ g a) :
    HasFDerivAt (primitiveMap m g)
      (ContinuousLinearMap.id ℝ (Euclidean n) +
        (fderiv ℝ g a - EuclideanSpace.proj m).smulRight (coordinateVector n m)) a :=
  (hasFDerivAt_id a).add
    ((hg.hasFDerivAt.sub (EuclideanSpace.proj m).hasFDerivAt).smul_const
      (coordinateVector n m))

theorem primitiveMap_matrix {n : ℕ} {m : Fin n} {g : Euclidean n → ℝ}
    {a : Euclidean n} (hg : DifferentiableAt ℝ g a) (i j : Fin n) :
    operatorMatrix (fderiv ℝ (primitiveMap m g) a) i j =
      if i = m then coordinatePartial g a j else if i = j then 1 else 0 := by
  rw [(hasFDerivAt_primitiveMap hg).fderiv, operatorMatrix_apply]
  change (coordinateVector n j +
    (fderiv ℝ g a (coordinateVector n j) - coordinateVector n j m) •
      coordinateVector n m) i = _
  by_cases h : i = m
  · subst i
    simp [coordinatePartial_eq_fderiv hg] <;> ring
  · simp [h, coordinatePartial_eq_fderiv hg]

theorem det_identity_updateRow {n : ℕ} (m : Fin n) (c : Fin n → ℝ) :
    ((1 : Matrix (Fin n) (Fin n) ℝ).updateRow m c).det = c m := by
  have hs : (∑ k : Fin n, c k • (1 : Matrix (Fin n) (Fin n) ℝ) k) = c := by
    ext j
    simp [Matrix.one_apply, eq_comm]
  simpa only [hs, Matrix.det_one, smul_eq_mul, mul_one] using
    Matrix.det_updateRow_sum (1 : Matrix (Fin n) (Fin n) ℝ) m c

theorem jacobian_primitiveMap {n : ℕ} {m : Fin n} {g : Euclidean n → ℝ}
    {a : Euclidean n} (hg : DifferentiableAt ℝ g a) :
    jacobian (primitiveMap m g) a = coordinatePartial g a m := by
  have hM : operatorMatrix (fderiv ℝ (primitiveMap m g) a) =
      (1 : Matrix (Fin n) (Fin n) ℝ).updateRow m (coordinatePartial g a) := by
    ext i j
    rw [primitiveMap_matrix hg]
    simp [Matrix.updateRow_apply, Matrix.one_apply]
  rw [jacobian, hM, det_identity_updateRow]

theorem primitiveMap_isInvertible_iff {n : ℕ} {m : Fin n} {g : Euclidean n → ℝ}
    {a : Euclidean n} (hg : DifferentiableAt ℝ g a) :
    (fderiv ℝ (primitiveMap m g) a).IsInvertible ↔ coordinatePartial g a m ≠ 0 := by
  rw [((pma9_38.1 n (primitiveMap m g) a
    (hasFDerivAt_primitiveMap hg).differentiableAt)).2, jacobian_primitiveMap hg]

theorem pma10_5 : pma10_5_contract := by
  refine ⟨fun _ => primitiveMap_apply, ?_, ?_⟩
  · intro n G E
    simp only [IsPrimitiveOn]
    constructor <;> rintro ⟨m, g, h⟩ <;> refine ⟨m, g, ?_⟩
    · intro x hx
      rw [h hx, primitiveMap_sum]
    · intro x hx
      rw [primitiveMap_sum]
      exact h x hx
  · intro n m g a hg
    exact ⟨hasFDerivAt_primitiveMap hg, primitiveMap_matrix hg,
      jacobian_primitiveMap hg, primitiveMap_isInvertible_iff hg⟩

@[simp] theorem flipOperator_apply {n : ℕ} (i j : Fin n) (x : Euclidean n) (k : Fin n) :
    flipOperator i j x k = x (Equiv.swap i j k) := by
  simp [flipOperator]

@[simp] theorem flipOperator_coordinateVector {n : ℕ} (i j k : Fin n) :
    flipOperator i j (coordinateVector n k) = coordinateVector n (Equiv.swap i j k) := by
  ext l
  simp [Equiv.swap_apply_eq_iff]

@[simp] theorem flipOperator_self {n : ℕ} (i : Fin n) :
    flipOperator i i = ContinuousLinearMap.id ℝ (Euclidean n) := by
  apply ContinuousLinearMap.ext
  intro x
  ext k
  simp

theorem flipOperator_involution {n : ℕ} (i j : Fin n) :
    (flipOperator i j).comp (flipOperator i j) = ContinuousLinearMap.id ℝ (Euclidean n) := by
  apply ContinuousLinearMap.ext
  intro x
  ext k
  simp

theorem flipOperator_isInvertible {n : ℕ} (i j : Fin n) :
    (flipOperator i j).IsInvertible := by
  have hi : Function.Involutive (flipOperator i j) := fun x =>
    congrArg (fun A : Operator n n => A x) (flipOperator_involution i j)
  exact ⟨ContinuousLinearEquiv.ofBijective (flipOperator i j)
    (LinearMap.ker_eq_bot.mpr hi.injective) (LinearMap.range_eq_top.mpr hi.surjective), rfl⟩

theorem isFlip_iff_basis {n : ℕ} (B : Operator n n) :
    IsFlip B ↔ ∃ i j : Fin n, i ≠ j ∧ ∀ k : Fin n,
      B (coordinateVector n k) = coordinateVector n (Equiv.swap i j k) := by
  constructor
  · rintro ⟨i, j, hij, rfl⟩
    exact ⟨i, j, hij, flipOperator_coordinateVector i j⟩
  · rintro ⟨i, j, hij, hB⟩
    refine ⟨i, j, hij, ?_⟩
    apply ContinuousLinearMap.coe_injective
    apply (standardBasis n).ext
    intro k
    simpa [coordinateVector, standardBasis] using
      (hB k).trans (flipOperator_coordinateVector i j k).symm

@[simp] theorem prefixProjection_apply (n m : ℕ) (x : Euclidean n) (i : Fin n) :
    prefixProjection n m x i = if i.val < m then x i else 0 := by
  have hterm (j : Fin n) :
      ((if j.val < m then
        (EuclideanSpace.proj j).smulRight (coordinateVector n j) else (0 : Operator n n)) x) i =
      if j = i then (if i.val < m then x i else 0) else 0 := by
    by_cases hji : j = i
    · subst j
      by_cases hi : i.val < m <;> simp [hi]
    · by_cases hj : j.val < m <;> simp [hj, hji, Ne.symm hji]
  simp only [prefixProjection, ContinuousLinearMap.sum_apply, WithLp.ofLp_sum, Finset.sum_apply]
  simp_rw [hterm]
  simp

theorem coordinate_span_iff {n : ℕ} (S : Set (Fin n)) (x : Euclidean n) :
    x ∈ Submodule.span ℝ (coordinateVector n '' S) ↔ ∀ i ∉ S, x i = 0 := by
  constructor
  · intro hx
    induction hx using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨j, hj, rfl⟩ := hy
      intro i hi
      have hij : i ≠ j := fun h => hi (h.symm ▸ hj)
      simp [hij]
    | zero => simp
    | add y z hy hz iy iz =>
      intro i hi
      simp [iy i hi, iz i hi]
    | smul a y hy iy =>
      intro i hi
      simp [iy i hi]
  · intro h
    rw [← sum_coordinates x]
    apply Submodule.sum_mem
    intro i _
    by_cases hi : i ∈ S
    · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, hi, rfl⟩)
    · simp [h i hi]

theorem prefixProjection_range (n m : ℕ) :
    (prefixProjection n m).toLinearMap.range =
      Submodule.span ℝ (coordinateVector n '' {i : Fin n | i.val < m}) := by
  ext x
  rw [coordinate_span_iff]
  constructor
  · rintro ⟨y, rfl⟩ i hi
    simpa using (show (if i.val < m then y i else 0) = 0 from if_neg hi)
  · intro h
    refine ⟨x, ?_⟩
    ext i
    by_cases hi : i.val < m
    · simp [hi]
    · simp [hi, h i hi]

theorem prefixProjection_ker (n m : ℕ) :
    (prefixProjection n m).toLinearMap.ker =
      Submodule.span ℝ (coordinateVector n '' {i : Fin n | m ≤ i.val}) := by
  ext x
  rw [LinearMap.mem_ker, coordinate_span_iff]
  constructor
  · intro hx i hi
    have him : i.val < m := lt_of_not_ge hi
    have h := congrArg (fun y : Euclidean n => y i) hx
    simpa [him] using h
  · intro h
    ext i
    by_cases hi : i.val < m
    · simp [hi, h i (not_le.mpr hi)]
    · simp [hi]

theorem pma10_6 : pma10_6_contract := by
  refine ⟨fun _ i j k x => flipOperator_apply i j x k, fun _ => isFlip_iff_basis,
    fun _ => flipOperator_involution, prefixProjection_apply, ?_, ?_⟩
  · intro n
    constructor
    · apply ContinuousLinearMap.ext
      intro x
      ext i
      simp
    · apply ContinuousLinearMap.ext
      intro x
      ext i
      simp [i.isLt]
  · intro n m _
    exact ⟨prefixProjection_range n m, prefixProjection_ker n m⟩

/-- Local preservation of the first `m` coordinates. -/
def FixesPrefixNear {n : ℕ} (m : ℕ) (F : Euclidean n → Euclidean n) : Prop :=
  ∀ᶠ x in 𝓝 (0 : Euclidean n), ∀ i : Fin n, i.val < m → F x i = x i

theorem primitiveNearZero_of_eventually {n : ℕ} {G : Euclidean n → Euclidean n}
    {m : Fin n} {g : Euclidean n → ℝ} (hC : ContDiffAt ℝ 1 G 0)
    (h0 : G 0 = 0) (hi : (fderiv ℝ G 0).IsInvertible)
    (he : G =ᶠ[𝓝 0] primitiveMap m g) : PrimitiveNearZero G := by
  obtain ⟨U, hU, hUopen, h0U⟩ := mem_nhds_iff.mp
    ((hC.eventually (by norm_num)).and he)
  refine ⟨U, hUopen, h0U, ⟨m, g, fun x hx => (hU hx).2⟩, ?_, h0, hi⟩
  exact (c1On_iff_contDiffOn hUopen).mpr
    (fun x hx => (hU hx).1.contDiffWithinAt)

theorem PrimitiveNearZero.continuousAt {n : ℕ} {G : Euclidean n → Euclidean n}
    (h : PrimitiveNearZero G) : ContinuousAt G 0 := by
  obtain ⟨U, hU, h0, _, hc, _, _⟩ := h
  exact (hc.1 0 h0).continuousAt

theorem PrimitiveNearZero.map_zero {n : ℕ} {G : Euclidean n → Euclidean n}
    (h : PrimitiveNearZero G) : G 0 = 0 := by
  obtain ⟨_, _, _, _, _, h0, _⟩ := h
  exact h0

theorem fixesPrefix_derivative {n m : ℕ} {F : Euclidean n → Euclidean n}
    (hF : DifferentiableAt ℝ F 0) (hfix : FixesPrefixNear m F)
    (i : Fin n) (hi : i.val < m) :
    (EuclideanSpace.proj i).comp (fderiv ℝ F 0) = EuclideanSpace.proj i := by
  have he : (fun x => F x i) =ᶠ[𝓝 (0 : Euclidean n)] (fun x => x i) :=
    hfix.mono fun x hx => hx i hi
  have hdF : HasFDerivAt (fun x => F x i)
      ((EuclideanSpace.proj i).comp (fderiv ℝ F 0)) 0 :=
    (EuclideanSpace.proj i : Euclidean n →L[ℝ] ℝ).hasFDerivAt.comp 0 hF.hasFDerivAt
  have hdId : HasFDerivAt (fun x : Euclidean n => x i)
      (EuclideanSpace.proj i : Euclidean n →L[ℝ] ℝ) 0 :=
    (EuclideanSpace.proj i : Euclidean n →L[ℝ] ℝ).hasFDerivAt
  exact hdF.unique (hdId.congr_of_eventuallyEq he)

theorem exists_remaining_pivot {n m : ℕ} (hm : m < n)
    {F : Euclidean n → Euclidean n} (hF : DifferentiableAt ℝ F 0)
    (hi : (fderiv ℝ F 0).IsInvertible) (hfix : FixesPrefixNear m F) :
    ∃ k : Fin n, m ≤ k.val ∧
      fderiv ℝ F 0 (coordinateVector n ⟨m, hm⟩) k ≠ 0 := by
  let em := coordinateVector n ⟨m, hm⟩
  have hem : em ≠ 0 := by
    intro h
    have hh := congrArg (fun x : Euclidean n => x ⟨m, hm⟩) h
    simpa [em] using hh
  have hne : fderiv ℝ F 0 em ≠ 0 := by
    intro h
    apply hem
    exact hi.injective (by simpa using h)
  obtain ⟨k, hk⟩ : ∃ k : Fin n, fderiv ℝ F 0 em k ≠ 0 := by
    by_contra! h
    apply hne
    ext k
    simpa using h k
  refine ⟨k, ?_, hk⟩
  by_contra h
  have hkm : k.val < m := lt_of_not_ge h
  have he := congrArg (fun A : Euclidean n →L[ℝ] ℝ => A em)
    (fixesPrefix_derivative hF hfix k hkm)
  apply hk
  have hki : k ≠ (⟨m, hm⟩ : Fin n) := fun heq => by
    have hv : k.val = m := congrArg Fin.val heq
    omega
  simpa [em, hki] using he

set_option synthInstance.maxHeartbeats 200000 in
theorem local_primitive_elimination {n m : ℕ} (hm : m < n)
    {F : Euclidean n → Euclidean n} (hF : ContDiffAt ℝ 1 F 0)
    (h0 : F 0 = 0) (hi : (fderiv ℝ F 0).IsInvertible)
    (hfix : FixesPrefixNear m F) :
    ∃ (G : Euclidean n → Euclidean n) (B : Operator n n)
      (H : Euclidean n → Euclidean n),
      PrimitiveNearZero G ∧
      (IsFlip B ∨ B = ContinuousLinearMap.id ℝ (Euclidean n)) ∧
      ContDiffAt ℝ 1 H 0 ∧ H 0 = 0 ∧ (fderiv ℝ H 0).IsInvertible ∧
      FixesPrefixNear (m + 1) H ∧
      F =ᶠ[𝓝 0] (fun x => B (H (G x))) := by
  let j : Fin n := ⟨m, hm⟩
  obtain ⟨k, hmk, hk⟩ := exists_remaining_pivot hm hF.differentiableAt_one hi hfix
  let g : Euclidean n → ℝ := fun x => F x k
  let G := primitiveMap j g
  let B := flipOperator j k
  have hcg : ContDiffAt ℝ 1 g 0 :=
    (EuclideanSpace.proj k : Euclidean n →L[ℝ] ℝ).contDiff.contDiffAt.comp 0 hF
  have hdg : HasFDerivAt g ((EuclideanSpace.proj k).comp (fderiv ℝ F 0)) 0 :=
    (EuclideanSpace.proj k : Euclidean n →L[ℝ] ℝ).hasFDerivAt.comp 0
      hF.differentiableAt_one.hasFDerivAt
  have hpart : coordinatePartial g 0 j ≠ 0 := by
    rw [coordinatePartial_eq_fderiv hcg.differentiableAt_one, hdg.fderiv]
    exact hk
  have hCG : ContDiffAt ℝ 1 G 0 :=
    contDiffAt_id.add
      ((hcg.sub (EuclideanSpace.proj j).contDiff.contDiffAt).smul_const
        (coordinateVector n j))
  have hG0 : G 0 = 0 := by simp [G, primitiveMap, g, h0]
  have hGi : (fderiv ℝ G 0).IsInvertible :=
    (primitiveMap_isInvertible_iff hcg.differentiableAt_one).mpr hpart
  have hGprim : PrimitiveNearZero G :=
    primitiveNearZero_of_eventually hCG hG0 hGi (Eventually.of_forall fun _ => rfl)
  obtain ⟨V, hV, hVopen, h0V⟩ := mem_nhds_iff.mp (hCG.eventually (by norm_num))
  have hCV : C1On G V := (c1On_iff_contDiffOn hVopen).mpr
    (fun x hx => (show ContDiffAt ℝ 1 G x from hV hx).contDiffWithinAt)
  obtain ⟨e, he, hCinv, hdinv⟩ := inverse_neighborhood_c1 hVopen h0V hCV hGi
  have h0target : (0 : Euclidean n) ∈ e.target := by
    simpa only [he.1, hG0] using e.map_source he.2.1
  have hinv0 : e.symm 0 = 0 := by
    simpa only [he.1, hG0] using e.left_inv he.2.1
  have hCinv0 : ContDiffAt ℝ 1 e.symm 0 :=
    ((c1On_iff_contDiffOn e.open_target).mp hCinv 0 h0target).contDiffAt
      (e.open_target.mem_nhds h0target)
  have hdInv : HasFDerivAt e.symm (fderiv ℝ G 0).inverse 0 := by
    simpa only [hinv0] using hdinv 0 h0target
  have hiInv : (fderiv ℝ G 0).inverse.IsInvertible :=
    ContinuousLinearMap.IsInvertible.of_inverse hGi.inverse_comp_self hGi.self_comp_inverse
  let H : Euclidean n → Euclidean n := fun y => B (F (e.symm y))
  have hCH : ContDiffAt ℝ 1 H 0 := by
    apply B.contDiff.contDiffAt.comp 0
    apply ContDiffAt.comp 0
    · simpa only [hinv0] using hF
    · exact hCinv0
  have hH0 : H 0 = 0 := by simp [H, hinv0, h0]
  have hdH : HasFDerivAt H
      (B.comp ((fderiv ℝ F 0).comp (fderiv ℝ G 0).inverse)) 0 := by
    apply B.hasFDerivAt.comp 0
    apply HasFDerivAt.comp 0
    · simpa only [hinv0] using hF.differentiableAt_one.hasFDerivAt
    · exact hdInv
  have hHi : (fderiv ℝ H 0).IsInvertible := by
    rw [hdH.fderiv]
    exact (flipOperator_isInvertible j k).comp (hi.comp hiInv)
  have hB : IsFlip B ∨ B = ContinuousLinearMap.id ℝ (Euclidean n) := by
    by_cases hjk : j = k
    · right
      simp [B, hjk]
    · exact Or.inl ⟨j, k, hjk, rfl⟩
  have hfixH : FixesPrefixNear (m + 1) H := by
    have ht : Tendsto e.symm (𝓝 0) (𝓝 0) := by
      have hc : Tendsto e.symm (𝓝 0) (𝓝 (e.symm 0)) := hCinv0.continuousAt
      simpa only [hinv0] using hc
    have hp := ht.eventually hfix
    filter_upwards [e.open_target.mem_nhds h0target, hp] with y hy hpy
    intro i hi
    have hGe : G (e.symm y) = y := by
      simpa only [he.1] using e.right_inv hy
    by_cases hij : i = j
    · subst i
      have hcoord := congrArg (fun z : Euclidean n => z j) hGe
      simpa [H, B, G, g] using hcoord
    · have him : i.val < m := by
        have hval : i.val ≠ m := fun h => hij (Fin.ext h)
        omega
      have hik : i ≠ k := fun h => by
        have hval := congrArg Fin.val h
        omega
      have hcoord := congrArg (fun z : Euclidean n => z i) hGe
      have hxy : e.symm y i = y i := by simpa [G, hij] using hcoord
      change B (F (e.symm y)) i = y i
      rw [flipOperator_apply, Equiv.swap_apply_of_ne_of_ne hij hik, hpy i him, hxy]
  have hfactor : F =ᶠ[𝓝 0] (fun x => B (H (G x))) := by
    filter_upwards [e.open_source.mem_nhds he.2.1] with x hx
    have hleft : e.symm (G x) = x := by
      simpa only [he.1] using e.left_inv hx
    change F x = B (B (F (e.symm (G x))))
    rw [hleft]
    exact (congrArg (fun A : Operator n n => A (F x))
      (flipOperator_involution j k)).symm
  exact ⟨G, B, H, hGprim, hB, hCH, hH0, hHi, hfixH, hfactor⟩

@[simp] theorem composeMaps_nil {X : Type*} (x : X) : composeMaps [] x = x := rfl

@[simp] theorem composeMaps_cons {X : Type*} (f : X → X) (L : List (X → X)) (x : X) :
    composeMaps (f :: L) x = f (composeMaps L x) := rfl

@[simp] theorem composeMaps_append {X : Type*} (L M : List (X → X)) (x : X) :
    composeMaps (L ++ M) x = composeMaps L (composeMaps M x) := by
  induction L with
  | nil => rfl
  | cons f L ih => simp only [List.cons_append, composeMaps_cons, ih]

theorem factorization_remaining (n r : ℕ) :
    ∀ m : ℕ, m < n → n - m = r → ∀ F : Euclidean n → Euclidean n,
      ContDiffAt ℝ 1 F 0 → F 0 = 0 → (fderiv ℝ F 0).IsInvertible →
      FixesPrefixNear m F →
      ∃ (G : List (Euclidean n → Euclidean n)) (B : List (Operator n n)),
        G.length = r ∧ B.length = r - 1 ∧
        (∀ g ∈ G, PrimitiveNearZero g) ∧
        (∀ b ∈ B, IsFlip b ∨ b = ContinuousLinearMap.id ℝ (Euclidean n)) ∧
        F =ᶠ[𝓝 0] composeMaps ((B.map (fun (b : Operator n n) =>
          (b : Euclidean n → Euclidean n))) ++ G) := by
  induction r using Nat.strong_induction_on with
  | h r ih =>
    intro m hm hmr F hF h0 hi hfix
    by_cases hlast : m + 1 = n
    · let j : Fin n := ⟨m, hm⟩
      have hp : F =ᶠ[𝓝 0] primitiveMap j (fun x => F x j) := by
        filter_upwards [hfix] with x hx
        ext i
        by_cases hij : i = j
        · simp [hij]
        · have him : i.val < m := by
            have hine : i.val ≠ m := fun h => hij (Fin.ext h)
            have hin := i.isLt
            omega
          simp [hij, hx i him]
      have hprim := primitiveNearZero_of_eventually hF h0 hi hp
      have hr : r = 1 := by omega
      refine ⟨[F], [], ?_, ?_, ?_, ?_, ?_⟩
      · simp [hr]
      · simp [hr]
      · simpa using hprim
      · simp
      · exact Eventually.of_forall fun _ => rfl
    · have hmnext : m + 1 < n := by omega
      obtain ⟨G, B, H, hG, hB, hH, hH0, hHi, hfixH, hstep⟩ :=
        local_primitive_elimination hm hF h0 hi hfix
      have hrlt : n - (m + 1) < r := by omega
      obtain ⟨Gs, Bs, hGslen, hBslen, hGs, hBs, htail⟩ :=
        ih (n - (m + 1)) hrlt (m + 1) hmnext rfl H hH hH0 hHi hfixH
      refine ⟨Gs ++ [G], B :: Bs, ?_, ?_, ?_, ?_, ?_⟩
      · simp only [List.length_append, List.length_singleton]
        omega
      · simp only [List.length_cons]
        omega
      · intro g hg
        rcases List.mem_append.mp hg with hg | hg
        · exact hGs g hg
        · rcases List.mem_singleton.mp hg with rfl
          exact hG
      · intro b hb
        rcases List.mem_cons.mp hb with rfl | hb
        · exact hB
        · exact hBs b hb
      · have ht : Tendsto G (𝓝 0) (𝓝 0) := by
          have hc : Tendsto G (𝓝 0) (𝓝 (G 0)) := hG.continuousAt
          simpa only [hG.map_zero] using hc
        have htcomp := htail.comp_tendsto ht
        filter_upwards [hstep, htcomp] with x hx htx
        change H (G x) = composeMaps
          ((Bs.map (fun (b : Operator n n) => (b : Euclidean n → Euclidean n))) ++ Gs)
          (G x) at htx
        simp only [List.map_cons, List.cons_append, composeMaps_cons, composeMaps_append,
          composeMaps_nil]
        rw [hx, htx]
        simp only [composeMaps_append]

theorem pma10_7 : pma10_7_contract := by
  intro n hn E F hE h0E hF h0 hi
  have hCF : ContDiffAt ℝ 1 F 0 :=
    ((c1On_iff_contDiffOn hE).mp hF 0 h0E).contDiffAt (hE.mem_nhds h0E)
  have hfix : FixesPrefixNear 0 F := Eventually.of_forall fun x i hi => by omega
  obtain ⟨G, B, hGlen, hBlen, hG, hB, he⟩ :=
    factorization_remaining n n 0 hn (Nat.sub_zero n) F hCF h0 hi hfix
  obtain ⟨U, hU, hUopen, h0U⟩ := mem_nhds_iff.mp (inter_mem (hE.mem_nhds h0E) he)
  exact ⟨G, B, U, hGlen, hBlen, hG, hB, hUopen, h0U,
    fun x hx => (hU hx).1, fun x hx => (hU hx).2⟩

end Rudin.PMA.Chapter10
