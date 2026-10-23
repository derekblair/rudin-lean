import Rudin.PMA.Chapter08

set_option autoImplicit false

noncomputable section
open Set Filter Topology Module
open scoped BigOperators

namespace Rudin.PMA.Chapter09

/-- Real coordinate space equipped with the Euclidean, rather than supremum, norm. -/
abbrev Euclidean (n : ℕ) := EuclideanSpace ℝ (Fin n)

/-- The standard coordinate basis of Euclidean space. -/
abbrev standardBasis (n : ℕ) := (EuclideanSpace.basisFun (Fin n) ℝ).toBasis

/-- Continuous representatives of the finite-dimensional linear transformations. -/
abbrev Operator (n m : ℕ) := Euclidean n →L[ℝ] Euclidean m

def IsLinearSubspace {X : Type*} [AddCommGroup X] [Module ℝ X] (S : Set X) : Prop :=
  S.Nonempty ∧ ∀ x ∈ S, ∀ y ∈ S, ∀ a b : ℝ, a • x + b • y ∈ S

def HasDimension (X : Type*) [AddCommGroup X] [Module ℝ X] (n : ℕ) : Prop :=
  (∃ v : Fin n → X, LinearIndependent ℝ v) ∧
    ∀ v : Fin (n + 1) → X, ¬ LinearIndependent ℝ v

/-- Matrix coordinates use target-basis rows and source-basis columns. -/
def operatorMatrix {n m : ℕ} (A : Operator n m) : Matrix (Fin m) (Fin n) ℝ :=
  LinearMap.toMatrix (standardBasis n) (standardBasis m) A.toLinearMap

/-! ### PMA-9.1: Subspaces, span, independence, dimension and bases. -/

def pma9_1_contract : Prop :=
  (∀ (X : Type*) [AddCommGroup X] [Module ℝ X],
    (∀ S : Set X, IsLinearSubspace S ↔ ∃ V : Submodule ℝ X, (V : Set X) = S) ∧
    (∀ (r : ℕ) (v : Fin r → X) (x : X),
      x ∈ Submodule.span ℝ (range v) ↔ ∃ c : Fin r → ℝ, ∑ i, c i • v i = x) ∧
    (∀ S : Set X, IsLinearSubspace (Submodule.span ℝ S : Set X)) ∧
    (∀ (S : Set X) (x : X), x ∈ Submodule.span ℝ S ↔
      ∃ (t : Finset X) (c : X → ℝ), (t : Set X) ⊆ S ∧ ∑ v ∈ t, c v • v = x) ∧
    (∀ (r : ℕ) (v : Fin r → X), LinearIndependent ℝ v ↔
      ∀ c : Fin r → ℝ, (∑ i, c i • v i) = 0 → ∀ i, c i = 0) ∧
    (∀ (r : ℕ) (v : Fin r → X), LinearIndependent ℝ v → ∀ i, v i ≠ 0) ∧
    (∀ (n : ℕ) (v : Fin n → X),
      (∃ b : Basis (Fin n) ℝ X, (b : Fin n → X) = v) ↔
        LinearIndependent ℝ v ∧ Submodule.span ℝ (range v) = ⊤) ∧
    (∀ (n : ℕ) (b : Basis (Fin n) ℝ X) (x : X),
      ∃! c : Fin n → ℝ, ∑ i, c i • b i = x) ∧
    (HasDimension X 0 ↔ Subsingleton X)) ∧
  (∀ (X : Type*) [AddCommGroup X] [Module ℝ X] [FiniteDimensional ℝ X] (n : ℕ),
    HasDimension X n ↔ Module.finrank ℝ X = n) ∧
  (∀ (n : ℕ) (i j : Fin n), standardBasis n i j = if j = i then 1 else 0)

/-! ### PMA-9.2: A finite spanning family bounds the dimension. -/

def pma9_2_contract : Prop :=
  (∀ (X : Type*) [AddCommGroup X] [Module ℝ X] (r : ℕ), 0 < r →
    ∀ v : Fin r → X, Submodule.span ℝ (range v) = ⊤ →
      Module.Finite ℝ X ∧ ∃ n : ℕ, n ≤ r ∧ HasDimension X n) ∧
  (∀ n : ℕ, HasDimension (Euclidean n) n)

/-! ### PMA-9.3: Basis criteria, size and extension. -/

def pma9_3_contract : Prop :=
  ∀ (X : Type*) [AddCommGroup X] [Module ℝ X] [FiniteDimensional ℝ X] (n : ℕ),
    HasDimension X n →
    (∀ v : Fin n → X, Submodule.span ℝ (range v) = ⊤ ↔ LinearIndependent ℝ v) ∧
    Nonempty (Basis (Fin n) ℝ X) ∧
    (∀ (r : ℕ) (_b : Basis (Fin r) ℝ X), r = n) ∧
    (∀ (r : ℕ) (v : Fin r → X), r ≤ n → LinearIndependent ℝ v →
      ∃ b : Basis (Fin n) ℝ X, ∃ e : Fin r ↪ Fin n, ∀ i, b (e i) = v i)

/-! ### PMA-9.4: Linear transformations and their algebraic inverses. -/

def pma9_4_contract : Prop :=
  ∀ (X Y : Type*) [AddCommGroup X] [Module ℝ X] [AddCommGroup Y] [Module ℝ Y],
    (∀ f : X → Y,
      (∀ x y : X, ∀ a b : ℝ, f (a • x + b • y) = a • f x + b • f y) ↔
        ∃ A : X →ₗ[ℝ] Y, (A : X → Y) = f) ∧
    (∀ A : X →ₗ[ℝ] Y, A 0 = 0) ∧
    (∀ (r : ℕ) (v : Fin r → X) (c : Fin r → ℝ) (A : X →ₗ[ℝ] Y),
      A (∑ i, c i • v i) = ∑ i, c i • A (v i)) ∧
    (∀ (n : ℕ) (b : Basis (Fin n) ℝ X) (A B : X →ₗ[ℝ] Y),
      (∀ i, A (b i) = B (b i)) → A = B) ∧
    (∀ (n : ℕ) (b : Basis (Fin n) ℝ X) (v : Fin n → Y),
      ∃! A : X →ₗ[ℝ] Y, ∀ i, A (b i) = v i) ∧
    (∀ A : X →ₗ[ℝ] X, Function.Bijective A ↔
      ∃ B : X →ₗ[ℝ] X, B.comp A = LinearMap.id ∧ A.comp B = LinearMap.id)

/-! ### PMA-9.5: Injectivity and surjectivity in equal finite dimensions. -/

def pma9_5_contract : Prop :=
  ∀ (X : Type*) [AddCommGroup X] [Module ℝ X] [FiniteDimensional ℝ X]
    (A : X →ₗ[ℝ] X), Function.Injective A ↔ Function.Surjective A

/-! ### PMA-9.6: Operator arithmetic and the least uniform bound. -/

def pma9_6_contract : Prop :=
  (∀ (n m : ℕ) (A B : Operator n m) (a b : ℝ) (x : Euclidean n),
    (a • A + b • B) x = a • A x + b • B x) ∧
  (∀ (n m k : ℕ) (A : Operator n m) (B : Operator m k) (x : Euclidean n),
    B.comp A x = B (A x)) ∧
  (∃ A B : Operator 2 2, A.comp B ≠ B.comp A) ∧
  (∀ (n m : ℕ) (A : Operator n m),
    ‖A‖ = sSup ((fun x => ‖A x‖) '' Metric.closedBall 0 1) ∧
    (∀ x, ‖A x‖ ≤ ‖A‖ * ‖x‖) ∧
    (∀ M : ℝ, 0 ≤ M → (‖A‖ ≤ M ↔ ∀ x, ‖A x‖ ≤ M * ‖x‖)))

/-! ### PMA-9.7: Continuity and the operator norm laws. -/

def pma9_7_contract : Prop :=
  (∀ (n m : ℕ) (A : Euclidean n →ₗ[ℝ] Euclidean m),
    UniformContinuous (fun x => A x) ∧ ∃ L : Operator n m,
      (fun x => L x) = (fun x => A x)) ∧
  (∀ (n m : ℕ) (A B : Operator n m) (c : ℝ),
    0 ≤ ‖A‖ ∧ (‖A‖ = 0 ↔ A = 0) ∧
    ‖A + B‖ ≤ ‖A‖ + ‖B‖ ∧ ‖c • A‖ = |c| * ‖A‖ ∧ dist A B = ‖A - B‖) ∧
  (∀ (n m k : ℕ) (A : Operator n m) (B : Operator m k),
    ‖B.comp A‖ ≤ ‖B‖ * ‖A‖)

/-! ### PMA-9.8: Perturbing an invertible operator and continuity of inversion. -/

def pma9_8_contract : Prop :=
  ∀ n : ℕ,
    (∀ A : Operator n n, IsUnit A ↔ Function.Bijective A) ∧
    (∀ A B : Operator n n, IsUnit A → ‖B - A‖ * ‖Ring.inverse A‖ < 1 → IsUnit B) ∧
    IsOpen {A : Operator n n | IsUnit A} ∧
    ContinuousOn (Ring.inverse : Operator n n → Operator n n) {A | IsUnit A} ∧
    BijOn (Ring.inverse : Operator n n → Operator n n) {A | IsUnit A} {A | IsUnit A} ∧
    (∀ A : Operator n n, IsUnit A → Ring.inverse (Ring.inverse A) = A)

/-! ### PMA-9.9: Arbitrary-basis matrices and the Euclidean bound. -/

def pma9_9_contract : Prop :=
  (∀ (X Y Z : Type*) [AddCommGroup X] [Module ℝ X]
      [AddCommGroup Y] [Module ℝ Y] [AddCommGroup Z] [Module ℝ Z]
      (n m k : ℕ) (bX : Basis (Fin n) ℝ X) (bY : Basis (Fin m) ℝ Y)
      (bZ : Basis (Fin k) ℝ Z),
    (∀ (A : X →ₗ[ℝ] Y) (i : Fin m) (j : Fin n),
      LinearMap.toMatrix bX bY A i j = bY.repr (A (bX j)) i) ∧
    (∀ (A : X →ₗ[ℝ] Y) (x : X) (i : Fin m),
      bY.repr (A x) i = ∑ j, LinearMap.toMatrix bX bY A i j * bX.repr x j) ∧
    (∀ A : X →ₗ[ℝ] Y, A.range = Submodule.span ℝ (range (fun j => A (bX j)))) ∧
    Function.Bijective (LinearMap.toMatrix bX bY) ∧
    (∀ (A : X →ₗ[ℝ] Y) (B : Y →ₗ[ℝ] Z),
      LinearMap.toMatrix bX bZ (B.comp A) =
        LinearMap.toMatrix bY bZ B * LinearMap.toMatrix bX bY A)) ∧
  (∀ (n m : ℕ) (A : Operator n m),
    ‖A‖ ≤ Real.sqrt (∑ i, ∑ j, (operatorMatrix A i j) ^ 2)) ∧
  (∀ (T : Type*) [MetricSpace T] (n m : ℕ) (A : T → Operator n m),
    (∀ i j, Continuous (fun t => operatorMatrix (A t) i j)) → Continuous A)

private theorem subspace_iff_submodule {X : Type*} [AddCommGroup X] [Module ℝ X]
    (S : Set X) : IsLinearSubspace S ↔ ∃ V : Submodule ℝ X, (V : Set X) = S := by
  constructor
  · rintro ⟨⟨z, hz⟩, h⟩
    have hzero : (0 : X) ∈ S := by simpa using h z hz z hz 0 0
    exact ⟨{ carrier := S
             zero_mem' := hzero
             add_mem' := fun hx hy => by simpa using h _ hx _ hy 1 1
             smul_mem' := fun a x hx => by simpa using h x hx 0 hzero a 0 }, rfl⟩
  · rintro ⟨V, rfl⟩
    exact ⟨⟨0, V.zero_mem⟩, fun x hx y hy a b =>
      V.add_mem (V.smul_mem a hx) (V.smul_mem b hy)⟩

theorem hasDimension_iff_finrank {X : Type*} [AddCommGroup X] [Module ℝ X]
    [FiniteDimensional ℝ X] (n : ℕ) : HasDimension X n ↔ Module.finrank ℝ X = n := by
  constructor
  · rintro ⟨⟨v, hv⟩, hmax⟩
    have hlo : n ≤ Module.finrank ℝ X := by simpa using hv.fintype_card_le_finrank
    have hhi : Module.finrank ℝ X ≤ n := by
      by_contra h
      obtain ⟨w, hw⟩ := exists_linearIndependent_of_le_finrank
        (R := ℝ) (M := X) (show n + 1 ≤ Module.finrank ℝ X by omega)
      exact hmax w hw
    omega
  · intro h
    refine ⟨exists_linearIndependent_of_le_finrank (R := ℝ) (M := X) h.ge, ?_⟩
    intro v hv
    have := hv.fintype_card_le_finrank
    simp only [Fintype.card_fin, h] at this
    omega

private theorem hasDimension_zero_iff {X : Type*} [AddCommGroup X] [Module ℝ X] :
    HasDimension X 0 ↔ Subsingleton X := by
  constructor
  · intro h
    have hz : ∀ x : X, x = 0 := by
      intro x
      by_contra hx
      have hlin : LinearIndependent ℝ (fun _ : Fin 1 => x) :=
        (linearIndependent_subsingleton_index_iff _).2 fun _ => hx
      exact h.2 (fun _ => x) hlin
    exact ⟨fun x y => (hz x).trans (hz y).symm⟩
  · intro h
    letI := h
    refine ⟨⟨Fin.elim0, linearIndependent_empty_type⟩, ?_⟩
    intro v hv
    exact (hv.ne_zero (0 : Fin 1)) (Subsingleton.elim _ _)

theorem pma9_1 : pma9_1_contract := by
  classical
  refine ⟨?_, fun X _ _ _ n => hasDimension_iff_finrank n, ?_⟩
  · intro X _ _
    refine ⟨subspace_iff_submodule, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hasDimension_zero_iff⟩
    · intro r v x
      exact Submodule.mem_span_range_iff_exists_fun ℝ
    · intro S
      exact (subspace_iff_submodule _).2 ⟨Submodule.span ℝ S, rfl⟩
    · intro S x
      constructor
      · intro hx
        obtain ⟨c, t, ht, _, hc⟩ := Submodule.mem_span_iff_exists_finset_subset.mp hx
        exact ⟨t, c, ht, hc⟩
      · rintro ⟨t, c, ht, rfl⟩
        exact Submodule.sum_mem _ fun v hv =>
          Submodule.smul_mem _ _ (Submodule.subset_span (ht hv))
    · intro r v
      exact Fintype.linearIndependent_iff
    · intro r v hv i
      exact hv.ne_zero i
    · intro n v
      constructor
      · rintro ⟨b, rfl⟩
        exact ⟨b.linearIndependent, b.span_eq⟩
      · rintro ⟨hv, hs⟩
        exact ⟨Basis.mk hv hs.ge, by ext i; exact Basis.mk_apply _ _ _⟩
    · intro n b x
      refine ⟨fun i => b.repr x i, b.sum_repr x, ?_⟩
      intro c hc
      have h := congrArg (fun y => (b.repr y : Fin n → ℝ)) hc
      simpa only [b.repr_sum_self] using h
  · intro n i j
    simp [standardBasis, EuclideanSpace.basisFun_apply, eq_comm]

theorem pma9_2 : pma9_2_contract := by
  constructor
  · intro X _ _ r _ v hv
    have hfg : (⊤ : Submodule ℝ X).FG := by
      rw [← hv]
      exact Submodule.fg_span (Set.finite_range v)
    letI : Module.Finite ℝ X := Module.Finite.of_fg_top hfg
    refine ⟨inferInstance, Module.finrank ℝ X, ?_, (hasDimension_iff_finrank _).2 rfl⟩
    simpa using finrank_le_of_span_eq_top hv
  · intro n
    apply (hasDimension_iff_finrank _).2
    simpa using Module.finrank_eq_card_basis (standardBasis n)

private theorem extend_independent {X : Type*} [AddCommGroup X] [Module ℝ X]
    [FiniteDimensional ℝ X] {n r : ℕ} (hn : Module.finrank ℝ X = n)
    (v : Fin r → X) (hv : LinearIndependent ℝ v) :
    ∃ b : Basis (Fin n) ℝ X, ∃ e : Fin r ↪ Fin n, ∀ i, b (e i) = v i := by
  classical
  let S := hv.linearIndepOn_id.extend (Set.subset_univ (range v))
  let b : Basis S ℝ X := Basis.extend hv.linearIndepOn_id
  letI : Finite S := b.linearIndependent.finite
  letI : Fintype S := Fintype.ofFinite S
  have hc : Fintype.card S = n := (Module.finrank_eq_card_basis b).symm.trans hn
  let e : S ≃ Fin n := Fintype.equivFinOfCardEq hc
  let j : Fin r ↪ S :=
    ⟨fun i => ⟨v i, hv.linearIndepOn_id.subset_extend _ (mem_range_self i)⟩,
      fun i k hik => hv.injective (congrArg Subtype.val hik)⟩
  refine ⟨b.reindex e, j.trans e.toEmbedding, ?_⟩
  intro i
  simp only [Function.Embedding.trans_apply, Equiv.toEmbedding_apply,
    Basis.reindex_apply, Equiv.symm_apply_apply]
  exact Basis.extend_apply_self _ _

theorem pma9_3 : pma9_3_contract := by
  intro X _ _ _ n hn
  have hdim := (hasDimension_iff_finrank n).1 hn
  refine ⟨?_, ⟨Module.finBasisOfFinrankEq ℝ X hdim⟩, ?_, ?_⟩
  · intro v
    constructor
    · intro hv
      exact linearIndependent_of_top_le_span_of_card_eq_finrank hv.ge (by simpa using hdim.symm)
    · intro hv
      exact hv.span_eq_top_of_card_eq_finrank' (by simpa using hdim.symm)
  · intro r b
    have := Module.finrank_eq_card_basis b
    simpa [hdim] using this.symm
  · intro r v _ hv
    exact extend_independent hdim v hv

theorem pma9_4 : pma9_4_contract := by
  intro X Y _ _ _ _
  refine ⟨?_, fun A => A.map_zero, ?_, ?_, ?_, ?_⟩
  · intro f
    constructor
    · intro h
      have hz : f 0 = 0 := by simpa using h 0 0 0 0
      exact ⟨{ toFun := f
               map_add' := fun x y => by simpa using h x y 1 1
               map_smul' := fun a x => by simpa [hz] using h x 0 a 0 }, rfl⟩
    · rintro ⟨A, rfl⟩
      intro x y a b
      simp
  · intro r v c A
    simp
  · intro n b A B h
    exact b.ext h
  · intro n b v
    refine ⟨b.constr ℝ v, fun i => b.constr_basis ℝ v i, ?_⟩
    intro A hA
    apply b.ext
    intro i
    simp [hA]
  · intro A
    constructor
    · intro hA
      let e := LinearEquiv.ofBijective A hA
      refine ⟨e.symm.toLinearMap, ?_, ?_⟩ <;> ext x <;> simp [e]
    · rintro ⟨B, hBA, hAB⟩
      have hl : Function.LeftInverse B A := fun x => congrArg (fun L : X →ₗ[ℝ] X => L x) hBA
      have hr : Function.RightInverse B A := fun x => congrArg (fun L : X →ₗ[ℝ] X => L x) hAB
      exact ⟨hl.injective, hr.surjective⟩

theorem pma9_5 : pma9_5_contract := by
  intro X _ _ _ A
  exact LinearMap.injective_iff_surjective

@[simp] theorem standardBasis_repr {n : ℕ} (x : Euclidean n) (i : Fin n) :
    (standardBasis n).repr x i = x i := rfl

@[simp] theorem standardBasis_apply {n : ℕ} (i j : Fin n) :
    standardBasis n i j = if j = i then 1 else 0 := by
  simp [standardBasis, EuclideanSpace.basisFun_apply, eq_comm]

private theorem noncommuting_operators :
    ∃ A B : Operator 2 2, A.comp B ≠ B.comp A := by
  let A : Operator 2 2 := (EuclideanSpace.proj (0 : Fin 2)).smulRight (standardBasis 2 0)
  let B : Operator 2 2 := (EuclideanSpace.proj (1 : Fin 2)).smulRight (standardBasis 2 0)
  refine ⟨A, B, ?_⟩
  intro h
  have he := congrArg (fun L : Operator 2 2 => L (standardBasis 2 1) 0) h
  norm_num [A, B, ContinuousLinearMap.comp_apply, ContinuousLinearMap.smulRight_apply,
    EuclideanSpace.coe_proj] at he

theorem pma9_6 : pma9_6_contract := by
  refine ⟨?_, ?_, noncommuting_operators, ?_⟩
  · intro n m A B a b x
    rfl
  · intro n m k A B x
    rfl
  · intro n m A
    exact ⟨A.sSup_unitClosedBall_eq_norm.symm, A.le_opNorm,
      fun M hM => ContinuousLinearMap.opNorm_le_iff hM⟩

theorem pma9_7 : pma9_7_contract := by
  refine ⟨?_, ?_, ?_⟩
  · intro n m A
    exact ⟨A.toContinuousLinearMap.uniformContinuous, A.toContinuousLinearMap, rfl⟩
  · intro n m A B c
    exact ⟨norm_nonneg A, norm_eq_zero, norm_add_le A B,
      by simpa only [Real.norm_eq_abs] using norm_smul c A, dist_eq_norm A B⟩
  · intro n m k A B
    exact B.opNorm_comp_le A

set_option synthInstance.maxHeartbeats 200000 in
theorem pma9_8 : pma9_8_contract := by
  classical
  intro n
  have hi : ∀ A : Operator n n, IsUnit A → IsUnit (Ring.inverse A) := by
    rintro A ⟨u, rfl⟩
    simpa only [Ring.inverse_unit] using u⁻¹.isUnit
  refine ⟨fun A => ContinuousLinearMap.isUnit_iff_bijective, ?_, Units.isOpen, ?_, ?_,
    fun A hA => Ring.inverse_inverse hA⟩
  · intro A B hA hAB
    by_cases hs : Subsingleton (Operator n n)
    · letI := hs
      exact isUnit_of_subsingleton B
    haveI : Nontrivial (Operator n n) := not_subsingleton_iff_nontrivial.mp hs
    obtain ⟨u, rfl⟩ := hA
    have hpos : 0 < ‖(↑u⁻¹ : Operator n n)‖ := Units.norm_pos u⁻¹
    have hlt : ‖B - ↑u‖ < ‖(↑u⁻¹ : Operator n n)‖⁻¹ := by
      rw [← one_div, lt_div_iff₀ hpos]
      simpa only [Ring.inverse_unit] using hAB
    exact (u.ofNearby B hlt).isUnit
  · rintro A ⟨u, rfl⟩
    exact (NormedRing.inverse_continuousAt u).continuousWithinAt
  · refine ⟨hi, ?_, ?_⟩
    · intro A hA B hB h
      have he := congrArg Ring.inverse h
      simpa only [Ring.inverse_inverse hA, Ring.inverse_inverse hB] using he
    · intro B hB
      exact ⟨Ring.inverse B, hi B hB, Ring.inverse_inverse hB⟩

@[simp] theorem operatorMatrix_apply {n m : ℕ} (A : Operator n m)
    (i : Fin m) (j : Fin n) : operatorMatrix A i j = A (standardBasis n j) i := by
  simp [operatorMatrix, LinearMap.toMatrix_apply]

/-- The Frobenius estimate is proved in the Euclidean norm used by the source. -/
theorem operator_norm_le_frobenius {n m : ℕ} (A : Operator n m) :
    ‖A‖ ≤ Real.sqrt (∑ i, ∑ j, (operatorMatrix A i j) ^ 2) := by
  classical
  apply A.opNorm_le_bound (Real.sqrt_nonneg _)
  intro x
  have hx : ∑ j, x j • standardBasis n j = x := by
    simpa only [standardBasis_repr] using (standardBasis n).sum_repr x
  have hcol : ∑ j, ‖A (standardBasis n j)‖ ^ 2 =
      ∑ i, ∑ j, (operatorMatrix A i j) ^ 2 := by
    simp_rw [EuclideanSpace.real_norm_sq_eq, ← operatorMatrix_apply]
    exact Finset.sum_comm
  calc
    ‖A x‖ = ‖∑ j, x j • A (standardBasis n j)‖ := by
      simpa only [map_sum, map_smul] using congrArg (fun z => ‖A z‖) hx.symm
    _ ≤ ∑ j, ‖x j • A (standardBasis n j)‖ := norm_sum_le _ _
    _ = ∑ j, |x j| * ‖A (standardBasis n j)‖ := by simp_rw [norm_smul, Real.norm_eq_abs]
    _ ≤ Real.sqrt (∑ j, |x j| ^ 2) * Real.sqrt (∑ j, ‖A (standardBasis n j)‖ ^ 2) :=
      Real.sum_mul_le_sqrt_mul_sqrt Finset.univ _ _
    _ = Real.sqrt (∑ i, ∑ j, (operatorMatrix A i j) ^ 2) * ‖x‖ := by
      rw [hcol, mul_comm, EuclideanSpace.norm_eq]
      simp only [Real.norm_eq_abs]

theorem continuous_of_operatorMatrix {T : Type*} [MetricSpace T] {n m : ℕ}
    (A : T → Operator n m) (h : ∀ i j, Continuous (fun t => operatorMatrix (A t) i j)) :
    Continuous A := by
  let e : Operator n m ≃ₗ[ℝ] Matrix (Fin m) (Fin n) ℝ :=
    LinearMap.toContinuousLinearMap.symm.trans
      (LinearMap.toMatrix (standardBasis n) (standardBasis m))
  have hc : Continuous (fun t => operatorMatrix (A t)) :=
    continuous_pi fun i => continuous_pi fun j => h i j
  have he : Continuous (e.symm : Matrix (Fin m) (Fin n) ℝ → Operator n m) :=
    e.symm.toLinearMap.continuous_of_finiteDimensional
  convert he.comp hc using 1
  funext t
  exact (e.symm_apply_apply (A t)).symm

theorem pma9_9 : pma9_9_contract := by
  classical
  refine ⟨?_, fun n m A => operator_norm_le_frobenius A,
    fun T _ n m A h => continuous_of_operatorMatrix A h⟩
  intro X Y Z _ _ _ _ _ _ n m k bX bY bZ
  refine ⟨?_, ?_, ?_, (LinearMap.toMatrix bX bY).bijective, ?_⟩
  · intro A i j
    exact LinearMap.toMatrix_apply bX bY A i j
  · intro A x i
    exact (congrFun (LinearMap.toMatrix_mulVec_repr bX bY A x) i).symm
  · intro A
    rw [← Submodule.map_top, ← bX.span_eq, Submodule.map_span, ← Set.range_comp]
    rfl
  · intro A B
    exact LinearMap.toMatrix_comp bX bY bZ B A


end Rudin.PMA.Chapter09
