import Rudin.PMA.Chapter09.Inverse

set_option autoImplicit false
noncomputable section
open Set Filter Topology Module
open scoped BigOperators

namespace Rudin.PMA.Chapter09

/-- The source rank: the dimension of the image subspace. -/
def operatorRank {n m : ℕ} (A : Operator n m) : ℕ :=
  Module.finrank ℝ A.toLinearMap.range

/-- A projection is an idempotent linear endomorphism; no orthogonality is assumed. -/
def IsProjection {X : Type*} [AddCommGroup X] [Module ℝ X] (P : X →ₗ[ℝ] X) : Prop :=
  P.comp P = P

/-- The same linear transformation with its image as codomain. -/
def rangeMap {n m : ℕ} (A : Operator n m) (x : Euclidean n) : A.toLinearMap.range :=
  ⟨A x, x, rfl⟩

def pma9_30_contract : Prop :=
  (∀ (n m : ℕ) (A : Operator n m),
    IsLinearSubspace (A.toLinearMap.ker : Set (Euclidean n)) ∧
    IsLinearSubspace (A.toLinearMap.range : Set (Euclidean m)) ∧
    HasDimension A.toLinearMap.range (operatorRank A) ∧
    (operatorRank A = 0 ↔ A = 0) ∧
    (operatorRank A = 0 ↔ A.toLinearMap.ker = ⊤)) ∧
  (∀ (n : ℕ) (A : Operator n n), IsUnit A ↔ operatorRank A = n)

def pma9_31_contract : Prop :=
  ∀ (X : Type*) [AddCommGroup X] [Module ℝ X] [FiniteDimensional ℝ X],
    (∀ P : X →ₗ[ℝ] X,
      (IsProjection P ↔ ∀ y ∈ P.range, P y = y) ∧
      (IsProjection P → ∀ x : X,
        ∃! yz : P.range × P.ker, (yz.1 : X) + (yz.2 : X) = x)) ∧
    (∀ S : Submodule ℝ X, ∃ P : X →ₗ[ℝ] X, IsProjection P ∧ P.range = S) ∧
    (∀ S : Submodule ℝ X, S ≠ ⊥ → S ≠ ⊤ →
      Set.Infinite {P : X →ₗ[ℝ] X | IsProjection P ∧ P.range = S})

/-- The book's rank-theorem coordinates, retaining the chosen (possibly oblique)
projection. The coordinate change goes from `H.source = V` to `H.target = U`. -/
structure RankNormalForm {n m : ℕ} (F : Euclidean n → Euclidean m)
    (E : Set (Euclidean n)) (a : Euclidean n) (P : Operator m m) where
  H : OpenPartialHomeomorph (Euclidean n) (Euclidean n)
  mem_target : a ∈ H.target
  target_subset : H.target ⊆ E
  c1_forward : C1On H H.source
  c1_inverse : C1On H.symm H.target
  phi : (fderiv ℝ F a).toLinearMap.range → P.toLinearMap.ker
  open_image : IsOpen (rangeMap (fderiv ℝ F a) '' H.source)
  c1_phi : C1On phi (rangeMap (fderiv ℝ F a) '' H.source)
  normal_form : ∀ x ∈ H.source,
    F (H x) = fderiv ℝ F a x + phi (rangeMap (fderiv ℝ F a) x)

def pma9_32_contract : Prop :=
  ∀ (n m r : ℕ) (E : Set (Euclidean n)) (F : Euclidean n → Euclidean m)
      (a : Euclidean n) (P : Operator m m),
    IsOpen E → a ∈ E → C1On F E →
    (∀ x ∈ E, operatorRank (fderiv ℝ F x) = r) →
    IsProjection P.toLinearMap → P.toLinearMap.range = (fderiv ℝ F a).toLinearMap.range →
    ∃ N : RankNormalForm F E a P,
      r ≤ min m n ∧
      Module.finrank ℝ (fderiv ℝ F a).toLinearMap.ker = n - r ∧
      F '' N.H.target =
        {y | ∃ z ∈ rangeMap (fderiv ℝ F a) '' N.H.source,
          y = (z : Euclidean m) + N.phi z} ∧
      BijOn P (F '' N.H.target) ((fderiv ℝ F a) '' N.H.source) ∧
      (∀ x ∈ N.H.source, ∀ y ∈ N.H.source,
        F (N.H x) = F (N.H y) ↔ fderiv ℝ F a x = fderiv ℝ F a y) ∧
      (∀ x ∈ N.H.source,
        {y ∈ N.H.source | F (N.H y) = F (N.H x)} =
          {y ∈ N.H.source | y - x ∈ (fderiv ℝ F a).toLinearMap.ker}) ∧
      (∀ x ∈ N.H.source,
        {z ∈ N.H.target | F z = F (N.H x)} =
          N.H '' {y ∈ N.H.source | y - x ∈ (fderiv ℝ F a).toLinearMap.ker})

theorem finrank_euclidean (n : ℕ) : Module.finrank ℝ (Euclidean n) = n := by
  simpa using Module.finrank_eq_card_basis (standardBasis n)

theorem operatorRank_zero_iff {n m : ℕ} (A : Operator n m) :
    operatorRank A = 0 ↔ A = 0 := by
  rw [operatorRank, Submodule.finrank_eq_zero, LinearMap.range_eq_bot]
  exact ⟨fun h => ContinuousLinearMap.coe_injective h, fun h => by rw [h]; rfl⟩

theorem pma9_30 : pma9_30_contract := by
  constructor
  · intro n m A
    have hs (V : Submodule ℝ (Euclidean n)) : IsLinearSubspace (V : Set (Euclidean n)) :=
      ⟨⟨0, V.zero_mem⟩, fun x hx y hy a b => V.add_mem (V.smul_mem a hx) (V.smul_mem b hy)⟩
    refine ⟨hs _, ?_, (hasDimension_iff_finrank _).2 rfl, operatorRank_zero_iff A, ?_⟩
    · exact ⟨⟨0, A.toLinearMap.range.zero_mem⟩, fun x hx y hy a b =>
        A.toLinearMap.range.add_mem (A.toLinearMap.range.smul_mem a hx)
          (A.toLinearMap.range.smul_mem b hy)⟩
    · rw [operatorRank_zero_iff, LinearMap.ker_eq_top]
      exact ⟨fun h => by rw [h]; rfl, fun h => ContinuousLinearMap.coe_injective h⟩
  · intro n A
    rw [ContinuousLinearMap.isUnit_iff_bijective]
    constructor
    · intro hA
      simpa only [operatorRank, finrank_euclidean] using
        LinearMap.finrank_range_of_inj hA.1
    · intro hA
      have hr : A.toLinearMap.range = ⊤ :=
        Submodule.eq_top_of_finrank_eq (hA.trans (finrank_euclidean n).symm)
      have hsurj : Function.Surjective A := LinearMap.range_eq_top.mp hr
      exact ⟨LinearMap.injective_iff_surjective.mpr hsurj, hsurj⟩

theorem isProjection_iff_fixes_range {X : Type*} [AddCommGroup X] [Module ℝ X]
    (P : X →ₗ[ℝ] X) : IsProjection P ↔ ∀ y ∈ P.range, P y = y := by
  constructor
  · intro h y hy
    obtain ⟨x, rfl⟩ := hy
    exact congrArg (fun L : X →ₗ[ℝ] X => L x) h
  · intro h
    ext x
    exact h _ ⟨x, rfl⟩

theorem projection_unique_decomposition {X : Type*} [AddCommGroup X] [Module ℝ X]
    (P : X →ₗ[ℝ] X) (hP : IsProjection P) (x : X) :
    ∃! yz : P.range × P.ker, (yz.1 : X) + (yz.2 : X) = x := by
  have hp := (isProjection_iff_fixes_range P).mp hP
  have hPP : P (P x) = P x := hp _ ⟨x, rfl⟩
  refine ⟨(⟨P x, x, rfl⟩, ⟨x - P x, by simp [LinearMap.mem_ker, hPP]⟩),
    by simp, ?_⟩
  rintro ⟨y, z⟩ hyz
  have hy : (y : X) = P x := by
    have h := congrArg P hyz
    simpa only [map_add, hp y y.2, LinearMap.mem_ker.mp z.2, add_zero] using h
  have hz : (z : X) = x - P x := by
    have hyz' : P x + (z : X) = x := by simpa only [hy] using hyz
    calc
      (z : X) = (P x + z) - P x := by abel
      _ = x - P x := by rw [hyz']
  exact Prod.ext (Subtype.ext hy) (Subtype.ext hz)

theorem exists_projection {X : Type*} [AddCommGroup X] [Module ℝ X]
    (S : Submodule ℝ X) : ∃ P : X →ₗ[ℝ] X, IsProjection P ∧ P.range = S := by
  obtain ⟨T, hST⟩ := S.exists_isCompl
  refine ⟨S.projection T hST, ?_, Submodule.range_projection hST⟩
  exact (Submodule.isIdempotentElem_projection hST).eq

theorem infinitely_many_projections {X : Type*} [AddCommGroup X] [Module ℝ X]
    (S : Submodule ℝ X) (hS0 : S ≠ ⊥) (hS1 : S ≠ ⊤) :
    Set.Infinite {P : X →ₗ[ℝ] X | IsProjection P ∧ P.range = S} := by
  classical
  obtain ⟨x, hxS, hx⟩ := S.ne_bot_iff.mp hS0
  obtain ⟨z, hz⟩ : ∃ z : X, z ∉ S := by
    by_contra h
    push_neg at h
    exact hS1 (by ext z; simp [h z])
  obtain ⟨f, hfz, hfS⟩ := S.exists_dual_map_eq_bot_of_notMem hz inferInstance
  obtain ⟨P, hP, hPS⟩ := exists_projection S
  have hp : ∀ y ∈ S, P y = y := by
    simpa only [hPS] using (isProjection_iff_fixes_range P).mp hP
  have hf : ∀ y ∈ S, f y = 0 := by
    intro y hy
    have : f y ∈ S.map f := ⟨y, hy, rfl⟩
    simpa only [hfS, Submodule.mem_bot] using this
  let T : ℝ → X →ₗ[ℝ] X := fun t => P + t • f.smulRight x
  have hT : ∀ t, LinearMap.IsProj S (T t) := by
    intro t
    constructor
    · intro y
      exact S.add_mem (hPS ▸ LinearMap.mem_range_self P y)
        (S.smul_mem t (S.smul_mem (f y) hxS))
    · intro y hy
      simp [T, hp y hy, hf y hy]
  have hi : Function.Injective T := by
    intro t u htu
    have h := congrArg (fun L : X →ₗ[ℝ] X => L z) htu
    have he : t • (f z • x) = u • (f z • x) := by
      simpa only [T, LinearMap.add_apply, LinearMap.smul_apply, LinearMap.smulRight_apply,
        add_right_inj] using h
    exact smul_left_injective ℝ (smul_ne_zero hfz hx) he
  apply Set.infinite_of_injective_forall_mem hi
  intro t
  exact ⟨(hT t).isIdempotentElem.eq, (hT t).range⟩

theorem pma9_31 : pma9_31_contract := by
  intro X _ _ _
  exact ⟨fun P => ⟨isProjection_iff_fixes_range P, projection_unique_decomposition P⟩,
    exists_projection, infinitely_many_projections⟩

set_option synthInstance.maxHeartbeats 200000 in
/-- Split the domain into the actual range coordinate and a kernel coordinate.
The first coordinate is exactly `A`, not an unrelated rank normal form. -/
theorem exists_range_kernel_split {n m : ℕ} (A : Operator n m) :
    ∃ e : Euclidean n ≃L[ℝ] A.toLinearMap.range × A.toLinearMap.ker,
      ∀ x, (e x).1 = rangeMap A x := by
  classical
  let K := A.toLinearMap.ker
  obtain ⟨T, hKT⟩ := K.exists_isCompl
  let Q : Euclidean n →ₗ[ℝ] K := K.projectionOnto T hKT
  let L : Euclidean n →ₗ[ℝ] A.toLinearMap.range × K := A.toLinearMap.rangeRestrict.prod Q
  have hQ (k : K) : Q k = k := Submodule.projectionOnto_apply_left hKT k
  have hinj : Function.Injective L := by
    apply LinearMap.ker_eq_bot.mp
    apply L.ker.eq_bot_iff.mpr
    intro x hx
    have hL : L x = 0 := hx
    have hA : A x = 0 := congrArg (fun p : A.toLinearMap.range × K => (p.1 : Euclidean m)) hL
    have hxK : x ∈ K := hA
    have hq : Q x = 0 := congrArg Prod.snd hL
    have hh := hQ ⟨x, hxK⟩
    rw [hq] at hh
    exact (congrArg (fun k : K => (k : Euclidean n)) hh).symm
  have hsurj : Function.Surjective L := by
    rintro ⟨y, k⟩
    obtain ⟨z, hz⟩ := y.2
    refine ⟨z + (k : Euclidean n) - (Q z : Euclidean n), ?_⟩
    apply Prod.ext
    · apply Subtype.ext
      change A (z + (k : Euclidean n) - (Q z : Euclidean n)) = y
      have hk : A k = 0 := k.2
      have hq : A (Q z) = 0 := (Q z).2
      simp only [map_sub, map_add, hk, hq, add_zero, sub_zero]
      exact hz
    · change Q (z + (k : Euclidean n) - (Q z : Euclidean n)) = k
      simp only [map_sub, map_add, hQ]
      abel
  let e := (LinearEquiv.ofBijective L ⟨hinj, hsurj⟩).toContinuousLinearEquiv
  exact ⟨e, fun _ => rfl⟩

/-- Equal finite ranks make an already contained kernel equal to the larger kernel. -/
theorem ker_eq_of_comp_rank_eq {n m k : ℕ} (A : Operator n m) (P : Operator m k)
    (hr : operatorRank (P.comp A) = operatorRank A) :
    (P.comp A).toLinearMap.ker = A.toLinearMap.ker := by
  apply (Submodule.eq_of_le_of_finrank_eq ?_ ?_).symm
  · intro x hx
    change P (A x) = 0
    have hAx : A x = 0 := hx
    rw [hAx, map_zero]
  · have h1 := A.toLinearMap.finrank_range_add_finrank_ker
    have h2 := (P.comp A).toLinearMap.finrank_range_add_finrank_ker
    change Module.finrank ℝ (P.comp A).toLinearMap.range =
      Module.finrank ℝ A.toLinearMap.range at hr
    omega

theorem derivative_partial_homeomorph_bijective {n : ℕ}
    (e : OpenPartialHomeomorph (Euclidean n) (Euclidean n))
    (hf : C1On e e.source) (hg : C1On e.symm e.target)
    (x : Euclidean n) (hx : x ∈ e.source) :
    Function.Bijective (fderiv ℝ e x) := by
  have hc := (hg.1 (e x) (e.map_source hx)).hasFDerivAt.comp x (hf.1 x hx).hasFDerivAt
  have heq : (fun y => e.symm (e y)) =ᶠ[𝓝 x] id :=
    Filter.eventually_of_mem (e.open_source.mem_nhds hx) fun y hy => e.left_inv hy
  have hid : HasFDerivAt (fun y => e.symm (e y)) (ContinuousLinearMap.id ℝ (Euclidean n)) x :=
    (hasFDerivAt_id x).congr_of_eventuallyEq heq
  have hcomp := hc.unique hid
  have hinj : Function.Injective (fderiv ℝ e x) := by
    intro v w hvw
    have hv := congrArg (fun L : Operator n n => L v) hcomp
    have hw := congrArg (fun L : Operator n n => L w) hcomp
    change fderiv ℝ e.symm (e x) (fderiv ℝ e x v) = v at hv
    change fderiv ℝ e.symm (e x) (fderiv ℝ e x w) = w at hw
    rw [hvw] at hv
    exact hv.symm.trans hw
  exact ⟨hinj, LinearMap.injective_iff_surjective.mp hinj⟩

theorem operatorRank_comp_of_surjective {n m k : ℕ} (A : Operator m k) (B : Operator n m)
    (hB : Function.Surjective B) : operatorRank (A.comp B) = operatorRank A := by
  have hr : (A.comp B).toLinearMap.range = A.toLinearMap.range := by
    change (A.toLinearMap.comp B.toLinearMap).range = A.toLinearMap.range
    rw [LinearMap.range_comp, LinearMap.range_eq_top.mpr hB, Submodule.map_top]
  unfold operatorRank
  rw [hr]

theorem rankNormalForm_project {n m : ℕ} {F : Euclidean n → Euclidean m}
    {E : Set (Euclidean n)} {a : Euclidean n} {P : Operator m m}
    (hP : IsProjection P.toLinearMap)
    (hPA : P.toLinearMap.range = (fderiv ℝ F a).toLinearMap.range)
    (N : RankNormalForm F E a P) {x : Euclidean n} (hx : x ∈ N.H.source) :
    P (F (N.H x)) = fderiv ℝ F a x := by
  have hfix := (isProjection_iff_fixes_range P.toLinearMap).mp hP
  have hpA : P (fderiv ℝ F a x) = fderiv ℝ F a x :=
    hfix _ (hPA.symm ▸ LinearMap.mem_range_self (fderiv ℝ F a).toLinearMap x)
  have hpφ : P (N.phi (rangeMap (fderiv ℝ F a) x)) = 0 :=
    (N.phi (rangeMap (fderiv ℝ F a) x)).2
  rw [N.normal_form x hx, map_add, hpA, hpφ, add_zero]

theorem rankNormalForm_same_level {n m : ℕ} {F : Euclidean n → Euclidean m}
    {E : Set (Euclidean n)} {a : Euclidean n} {P : Operator m m}
    (hP : IsProjection P.toLinearMap)
    (hPA : P.toLinearMap.range = (fderiv ℝ F a).toLinearMap.range)
    (N : RankNormalForm F E a P) {x y : Euclidean n}
    (hx : x ∈ N.H.source) (hy : y ∈ N.H.source) :
    F (N.H x) = F (N.H y) ↔ fderiv ℝ F a x = fderiv ℝ F a y := by
  constructor
  · intro h
    have hp := congrArg P h
    simpa only [rankNormalForm_project hP hPA N hx, rankNormalForm_project hP hPA N hy] using hp
  · intro h
    have hr : rangeMap (fderiv ℝ F a) x = rangeMap (fderiv ℝ F a) y := Subtype.ext h
    rw [N.normal_form x hx, N.normal_form y hy, h, hr]

theorem rankNormalForm_graph {n m : ℕ} {F : Euclidean n → Euclidean m}
    {E : Set (Euclidean n)} {a : Euclidean n} {P : Operator m m}
    (N : RankNormalForm F E a P) :
    F '' N.H.target = {y | ∃ z ∈ rangeMap (fderiv ℝ F a) '' N.H.source,
      y = (z : Euclidean m) + N.phi z} := by
  ext y
  constructor
  · rintro ⟨z, hz, rfl⟩
    refine ⟨rangeMap (fderiv ℝ F a) (N.H.symm z),
      ⟨N.H.symm z, N.H.map_target hz, rfl⟩, ?_⟩
    simpa only [N.H.right_inv hz, rangeMap] using N.normal_form (N.H.symm z) (N.H.map_target hz)
  · rintro ⟨z, ⟨x, hx, rfl⟩, rfl⟩
    exact ⟨N.H x, N.H.map_source hx, N.normal_form x hx⟩

theorem rankNormalForm_projection_bijOn {n m : ℕ} {F : Euclidean n → Euclidean m}
    {E : Set (Euclidean n)} {a : Euclidean n} {P : Operator m m}
    (hP : IsProjection P.toLinearMap)
    (hPA : P.toLinearMap.range = (fderiv ℝ F a).toLinearMap.range)
    (N : RankNormalForm F E a P) :
    BijOn P (F '' N.H.target) ((fderiv ℝ F a) '' N.H.source) := by
  refine ⟨?_, ?_, ?_⟩
  · rintro _ ⟨z, hz, rfl⟩
    refine ⟨N.H.symm z, N.H.map_target hz, ?_⟩
    simpa only [N.H.right_inv hz] using
      (rankNormalForm_project hP hPA N (N.H.map_target hz)).symm
  · rintro _ ⟨z, hz, rfl⟩ _ ⟨w, hw, rfl⟩ hp
    have hx := N.H.map_target hz
    have hy := N.H.map_target hw
    have hA : fderiv ℝ F a (N.H.symm z) = fderiv ℝ F a (N.H.symm w) := by
      rw [← rankNormalForm_project hP hPA N hx, ← rankNormalForm_project hP hPA N hy,
        N.H.right_inv hz, N.H.right_inv hw]
      exact hp
    simpa only [N.H.right_inv hz, N.H.right_inv hw] using
      (rankNormalForm_same_level hP hPA N hx hy).mpr hA
  · rintro _ ⟨x, hx, rfl⟩
    exact ⟨F (N.H x), ⟨N.H x, N.H.map_source hx, rfl⟩,
      rankNormalForm_project hP hPA N hx⟩

theorem rankNormalForm_kernel_level {n m : ℕ} {F : Euclidean n → Euclidean m}
    {E : Set (Euclidean n)} {a : Euclidean n} {P : Operator m m}
    (hP : IsProjection P.toLinearMap)
    (hPA : P.toLinearMap.range = (fderiv ℝ F a).toLinearMap.range)
    (N : RankNormalForm F E a P) {x : Euclidean n} (hx : x ∈ N.H.source) :
    {y ∈ N.H.source | F (N.H y) = F (N.H x)} =
      {y ∈ N.H.source | y - x ∈ (fderiv ℝ F a).toLinearMap.ker} := by
  ext y
  simp only [mem_setOf_eq]
  apply and_congr_right
  intro hy
  rw [rankNormalForm_same_level hP hPA N hy hx]
  change fderiv ℝ F a y = fderiv ℝ F a x ↔ fderiv ℝ F a (y - x) = 0
  rw [map_sub, sub_eq_zero]

theorem rankNormalForm_original_level {n m : ℕ} {F : Euclidean n → Euclidean m}
    {E : Set (Euclidean n)} {a : Euclidean n} {P : Operator m m}
    (hP : IsProjection P.toLinearMap)
    (hPA : P.toLinearMap.range = (fderiv ℝ F a).toLinearMap.range)
    (N : RankNormalForm F E a P) {x : Euclidean n} (hx : x ∈ N.H.source) :
    {z ∈ N.H.target | F z = F (N.H x)} =
      N.H '' {y ∈ N.H.source | y - x ∈ (fderiv ℝ F a).toLinearMap.ker} := by
  rw [← rankNormalForm_kernel_level hP hPA N hx]
  ext z
  constructor
  · rintro ⟨hz, hF⟩
    exact ⟨N.H.symm z, ⟨N.H.map_target hz, by simpa only [N.H.right_inv hz] using hF⟩,
      N.H.right_inv hz⟩
  · rintro ⟨y, ⟨hy, hF⟩, rfl⟩
    exact ⟨N.H.map_source hy, hF⟩

/-- Vanishing derivatives in the kernel directions give constancy on each
fiber of a product neighborhood. This includes the zero-rank case. -/
theorem constant_on_kernel_fiber {n m k : ℕ} (A : Operator n m)
    (e : Euclidean n ≃L[ℝ] A.toLinearMap.range × A.toLinearMap.ker)
    (he : ∀ x, (e x).1 = rangeMap A x)
    (G : Euclidean n → Euclidean k) (c : A.toLinearMap.range × A.toLinearMap.ker)
    (ε : ℝ) (hε : 0 < ε)
    (hf : ∀ x ∈ e ⁻¹' (Metric.ball c.1 ε ×ˢ Metric.ball c.2 ε), DifferentiableAt ℝ G x)
    (hk : ∀ x ∈ e ⁻¹' (Metric.ball c.1 ε ×ˢ Metric.ball c.2 ε),
      ∀ v ∈ A.toLinearMap.ker, fderiv ℝ G x v = 0)
    (x : Euclidean n) (hx : x ∈ e ⁻¹' (Metric.ball c.1 ε ×ˢ Metric.ball c.2 ε)) :
    G x = G (e.symm ((e x).1, c.2)) := by
  let z := (e x).1
  let g : A.toLinearMap.ker → Euclidean k := fun v => G (e.symm (z, v))
  have hm : ∀ v ∈ Metric.ball c.2 ε,
      e.symm (z, v) ∈ e ⁻¹' (Metric.ball c.1 ε ×ˢ Metric.ball c.2 ε) := by
    intro v hv
    change (e (e.symm (z, v))).1 ∈ Metric.ball c.1 ε ∧
      (e (e.symm (z, v))).2 ∈ Metric.ball c.2 ε
    simpa only [e.apply_symm_apply] using And.intro hx.1 hv
  have hd : ∀ v ∈ Metric.ball c.2 ε,
      HasFDerivAt g (0 : A.toLinearMap.ker →L[ℝ] Euclidean k) v := by
    intro v hv
    have hs := e.symm.hasFDerivAt.comp v (hasFDerivAt_prodMk_right z v)
    have hc := (hf _ (hm v hv)).hasFDerivAt.comp v hs
    have hz : (fderiv ℝ G (e.symm (z, v))).comp
        (e.symm.toContinuousLinearMap.comp
          (ContinuousLinearMap.inr ℝ A.toLinearMap.range A.toLinearMap.ker)) = 0 := by
      apply ContinuousLinearMap.ext
      intro w
      apply hk _ (hm v hv)
      change A (e.symm (0, w)) = 0
      have h := congrArg (fun y : A.toLinearMap.range => (y : Euclidean m))
        (he (e.symm (0, w)))
      simpa [rangeMap] using h.symm
    convert! hc using 1 <;> simp only [g, Function.comp_def, hz]
  have hconst := (convex_ball c.2 ε).is_const_of_fderivWithin_eq_zero
    (fun v hv => (hd v hv).differentiableAt.differentiableWithinAt)
    (fun v hv => (hd v hv).hasFDerivWithinAt.fderivWithin (Metric.isOpen_ball.uniqueDiffOn v hv))
    hx.2 (Metric.mem_ball_self hε)
  simpa only [g, z, e.symm_apply_apply] using hconst

theorem constant_rank_chart_kernel {n m r : ℕ} (F : Euclidean n → Euclidean m)
    (E : Set (Euclidean n)) (hf : C1On F E)
    (hr : ∀ y ∈ E, operatorRank (fderiv ℝ F y) = r)
    (A : Operator n m) (hAr : operatorRank A = r) (P : Operator m m)
    (H : OpenPartialHomeomorph (Euclidean n) (Euclidean n))
    (hH : C1On H H.source) (hHi : C1On H.symm H.target) (hHE : H.target ⊆ E)
    (hproj : ∀ x ∈ H.source, P (F (H x)) = A x) :
    ∀ x ∈ H.source, ∀ v ∈ A.toLinearMap.ker,
      fderiv ℝ (fun y => F (H y)) x v = 0 := by
  intro x hx
  let B := fderiv ℝ (fun y => F (H y)) x
  have hFx := (hf.1 _ (hHE (H.map_source hx))).hasFDerivAt
  have hHx := (hH.1 x hx).hasFDerivAt
  have hc := hFx.comp x hHx
  have hB : B = (fderiv ℝ F (H x)).comp (fderiv ℝ H x) := hc.fderiv
  have hBr : operatorRank B = r := by
    rw [hB, operatorRank_comp_of_surjective _ _
      (derivative_partial_homeomorph_bijective H hH hHi x hx).2]
    exact hr _ (hHE (H.map_source hx))
  have hPB : P.comp B = A := by
    have hpder := P.hasFDerivAt.comp x (show HasFDerivAt (fun y => F (H y)) B x from
      by rw [hB]; exact hc)
    have heq : (fun y => P (F (H y))) =ᶠ[𝓝 x] A :=
      Filter.eventually_of_mem (H.open_source.mem_nhds hx) fun y hy => hproj y hy
    exact hpder.unique (A.hasFDerivAt.congr_of_eventuallyEq heq)
  have hker := ker_eq_of_comp_rank_eq B P (by rw [hPB, hAr, hBr])
  rw [hPB] at hker
  intro v hv
  have : v ∈ B.toLinearMap.ker := hker ▸ hv
  exact this

set_option synthInstance.maxHeartbeats 200000 in
theorem exists_rankNormalForm {n m r : ℕ} (E : Set (Euclidean n))
    (F : Euclidean n → Euclidean m) (a : Euclidean n) (P : Operator m m)
    (hE : IsOpen E) (ha : a ∈ E) (hf : C1On F E)
    (hr : ∀ x ∈ E, operatorRank (fderiv ℝ F x) = r)
    (hP : IsProjection P.toLinearMap)
    (hPA : P.toLinearMap.range = (fderiv ℝ F a).toLinearMap.range) :
    Nonempty (RankNormalForm F E a P) := by
  classical
  let A := fderiv ℝ F a
  obtain ⟨e, he⟩ := exists_range_kernel_split A
  let PA : Euclidean m →L[ℝ] A.toLinearMap.range :=
    P.codRestrict A.toLinearMap.range
      (fun y => hPA ▸ LinearMap.mem_range_self P.toLinearMap y)
  let K : Euclidean n →L[ℝ] A.toLinearMap.ker :=
    (ContinuousLinearMap.snd ℝ A.toLinearMap.range A.toLinearMap.ker).comp e.toContinuousLinearMap
  let G : Euclidean n → Euclidean n := fun x => e.symm (PA (F x), K x)
  have hFcont : ContDiffOn ℝ 1 F E := (c1On_iff_contDiffOn hE).mp hf
  have hGcont : ContDiffOn ℝ 1 G E :=
    e.symm.contDiff.comp_contDiffOn
      ((PA.contDiff.comp_contDiffOn hFcont).prodMk K.contDiff.contDiffOn)
  have hGC1 : C1On G E := (c1On_iff_contDiffOn hE).mpr hGcont
  have hfix := (isProjection_iff_fixes_range P.toLinearMap).mp hP
  have hD : e.symm.toContinuousLinearMap.comp ((PA.comp A).prod K) =
      ContinuousLinearMap.id ℝ (Euclidean n) := by
    apply ContinuousLinearMap.ext
    intro x
    apply e.injective
    change e (e.symm (PA (A x), K x)) = e x
    rw [e.apply_symm_apply]
    apply Prod.ext
    · rw [he]
      apply Subtype.ext
      exact hfix _ (hPA.symm ▸ LinearMap.mem_range_self A.toLinearMap x)
    · rfl
  have hGder : HasFDerivAt G (ContinuousLinearMap.id ℝ (Euclidean n)) a := by
    have h := e.symm.hasFDerivAt.comp a
      ((PA.hasFDerivAt.comp a (hf.1 a ha).hasFDerivAt).prodMk K.hasFDerivAt)
    change HasFDerivAt G (e.symm.toContinuousLinearMap.comp ((PA.comp A).prod K)) a at h
    rw [hD] at h
    exact h
  have hi : (fderiv ℝ G a).IsInvertible := by
    rw [hGder.fderiv]
    exact ⟨ContinuousLinearEquiv.refl ℝ (Euclidean n), rfl⟩
  obtain ⟨q, hq, hqC1, _⟩ := inverse_neighborhood_c1 hE ha hGC1 hi
  let c := e (G a)
  have hcq : c ∈ e '' q.target := ⟨G a, by simpa only [hq.1] using q.map_source hq.2.1, rfl⟩
  have hopen : IsOpen (e '' q.target) := e.toHomeomorph.isOpenMap _ q.open_target
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hopen c hcq
  let V : Set (Euclidean n) := e ⁻¹' (Metric.ball c.1 ε ×ˢ Metric.ball c.2 ε)
  have hVopen : IsOpen V := (Metric.isOpen_ball.prod Metric.isOpen_ball).preimage e.continuous
  have hVq : V ⊆ q.target := by
    intro x hx
    have hb : e x ∈ Metric.ball c ε := by
      rw [← ball_prod_same c.1 c.2 ε]
      exact hx
    obtain ⟨y, hy, hexy⟩ := hball hb
    exact e.injective hexy ▸ hy
  have hGa : G a ∈ V := by
    change dist (e (G a)).1 c.1 < ε ∧ dist (e (G a)).2 c.2 < ε
    simpa only [c, dist_self] using And.intro hε hε
  let H := q.symm.restrOpen V hVopen
  have hHsource : H.source = V := by
    change q.target ∩ V = V
    exact Set.inter_eq_right.mpr hVq
  have hHsymm : (H.symm : Euclidean n → Euclidean n) = G := hq.1
  have haH : a ∈ H.target := by
    change a ∈ q.source ∩ q ⁻¹' V
    refine ⟨hq.2.1, ?_⟩
    change q a ∈ V
    rw [hq.1]
    exact hGa
  have hHE : H.target ⊆ E := fun x hx => hq.2.2 hx.1
  have hHC1 : C1On H H.source := by
    exact ⟨fun x hx => hqC1.1 x hx.1, hqC1.2.mono fun x hx => hx.1⟩
  have hHiC1 : C1On H.symm H.target := by
    rw [hHsymm]
    exact ⟨fun x hx => hGC1.1 x (hHE hx), hGC1.2.mono hHE⟩
  have hproj : ∀ x ∈ H.source, P (F (H x)) = A x := by
    intro x hx
    have hGx : G (H x) = x := by simpa only [hHsymm] using H.left_inv hx
    have hp := congrArg (fun u => (e u).1) hGx
    have hp' : PA (F (H x)) = rangeMap A x := by
      simpa only [G, e.apply_symm_apply, he] using hp
    exact congrArg (fun y : A.toLinearMap.range => (y : Euclidean m)) hp'
  have hker := constant_rank_chart_kernel F E hf hr A (hr a ha) P H hHC1 hHiC1 hHE hproj
  let sectionMap : A.toLinearMap.range → Euclidean n := fun z => e.symm (z, c.2)
  have hsection : MapsTo sectionMap (Metric.ball c.1 ε) H.source := by
    intro z hz
    rw [hHsource]
    change e (e.symm (z, c.2)) ∈ Metric.ball c.1 ε ×ˢ Metric.ball c.2 ε
    simpa only [e.apply_symm_apply, Set.mem_prod] using And.intro hz (Metric.mem_ball_self hε)
  have hfirst : ∀ z, rangeMap A (sectionMap z) = z := by
    intro z
    simpa only [sectionMap, e.apply_symm_apply] using (he (sectionMap z)).symm
  have hAV : rangeMap A '' H.source = Metric.ball c.1 ε := by
    ext z
    constructor
    · rintro ⟨x, hx, rfl⟩
      have hxV : x ∈ V := hHsource ▸ hx
      simpa only [he] using hxV.1
    · intro hz
      exact ⟨sectionMap z, hsection hz, hfirst z⟩
  let R : Euclidean m →L[ℝ] P.toLinearMap.ker :=
    (ContinuousLinearMap.id ℝ (Euclidean m) - P).codRestrict P.toLinearMap.ker (by
      intro y
      change P (y - P y) = 0
      have hPP : P (P y) = P y := congrArg (fun L : Euclidean m →ₗ[ℝ] Euclidean m => L y) hP
      simp only [map_sub, hPP, sub_self])
  let φ : A.toLinearMap.range → P.toLinearMap.ker := fun z => R (F (H (sectionMap z)))
  have hsectionCont : ContDiff ℝ 1 sectionMap :=
    e.symm.contDiff.comp (contDiff_prodMk_left c.2)
  have hFHcont : ContDiffOn ℝ 1 (fun x => F (H x)) H.source :=
    hFcont.comp ((c1On_iff_contDiffOn H.open_source).mp hHC1)
      (fun x hx => hHE (H.map_source hx))
  have hφcont : ContDiffOn ℝ 1 φ (Metric.ball c.1 ε) :=
    R.contDiff.comp_contDiffOn (hFHcont.comp hsectionCont.contDiffOn hsection)
  have hφC1 : C1On φ (rangeMap A '' H.source) := by
    rw [hAV]
    exact (c1On_iff_contDiffOn Metric.isOpen_ball).mpr hφcont
  refine ⟨⟨H, haH, hHE, hHC1, hHiC1, φ, by rw [hAV]; exact Metric.isOpen_ball, hφC1, ?_⟩⟩
  intro x hx
  have hxV : x ∈ V := hHsource ▸ hx
  have hconstant : F (H x) = F (H (sectionMap (rangeMap A x))) := by
    have h := constant_on_kernel_fiber A e he (fun y => F (H y)) c ε hε
      (fun y hy => ((hf.1 _ (hHE (H.map_source (hHsource.symm ▸ hy)))).hasFDerivAt.comp y
        (hHC1.1 y (hHsource.symm ▸ hy)).hasFDerivAt).differentiableAt)
      (fun y hy => hker y (hHsource.symm ▸ hy)) x hxV
    simpa only [he, sectionMap] using h
  have hz : rangeMap A x ∈ Metric.ball c.1 ε := by
    simpa only [he] using hxV.1
  have hPsec : P (F (H (sectionMap (rangeMap A x)))) = A x := by
    rw [hproj _ (hsection hz)]
    exact congrArg (fun y : A.toLinearMap.range => (y : Euclidean m)) (hfirst (rangeMap A x))
  change F (H x) = A x + (F (H (sectionMap (rangeMap A x))) -
    P (F (H (sectionMap (rangeMap A x)))))
  rw [hconstant, hPsec]
  abel

theorem pma9_32 : pma9_32_contract := by
  intro n m r E F a P hE ha hf hr hP hPA
  obtain ⟨N⟩ := exists_rankNormalForm E F a P hE ha hf hr hP hPA
  have hAr := hr a ha
  have hdim := (fderiv ℝ F a).toLinearMap.finrank_range_add_finrank_ker
  have hdom := (fderiv ℝ F a).toLinearMap.finrank_range_le
  have hcod := (fderiv ℝ F a).toLinearMap.range.finrank_le
  rw [finrank_euclidean] at hdim hdom hcod
  change Module.finrank ℝ (fderiv ℝ F a).toLinearMap.range = r at hAr
  rw [hAr] at hdim hdom hcod
  refine ⟨N, le_min hcod hdom, by omega, rankNormalForm_graph N,
    rankNormalForm_projection_bijOn hP hPA N, ?_, ?_, ?_⟩
  · intro x hx y hy
    exact rankNormalForm_same_level hP hPA N hx hy
  · intro x hx
    exact rankNormalForm_kernel_level hP hPA N hx
  · intro x hx
    exact rankNormalForm_original_level hP hPA N hx


end Rudin.PMA.Chapter09
