import Mathlib
import Rudin.PMA.Chapter09.FirstHalf

/-!
# PMA 9.30–9.31 and 9.33–9.38: linear algebra and determinants

The indexing of vectors and matrices starts at zero in Lean. The sign product and
sum over all tuples below agree with Rudin's formulas under this reindexing.
-/

noncomputable section
open scoped BigOperators
open Module

namespace Rudin.PMA.Chapter09

/-- PMA 9.30: the null space. -/
abbrev pma9_30_nullSpace {X Y : Type*} [AddCommGroup X] [Module ℝ X]
    [AddCommGroup Y] [Module ℝ Y] (A : X →ₗ[ℝ] Y) : Submodule ℝ X := A.ker

/-- PMA 9.30: the range. -/
abbrev pma9_30_range {X Y : Type*} [AddCommGroup X] [Module ℝ X]
    [AddCommGroup Y] [Module ℝ Y] (A : X →ₗ[ℝ] Y) : Submodule ℝ Y := A.range

/-- PMA 9.30: rank, as a cardinal dimension (also valid in infinite dimensions). -/
abbrev pma9_30_rank {X Y : Type*} [AddCommGroup X] [Module ℝ X]
    [AddCommGroup Y] [Module ℝ Y] (A : X →ₗ[ℝ] Y) : Cardinal :=
  Module.rank ℝ A.range

/-- PMA 9.30: in finite dimensions rank is represented by a natural number. -/
abbrev pma9_30_finrank {X Y : Type*} [AddCommGroup X] [Module ℝ X]
    [AddCommGroup Y] [Module ℝ Y] (A : X →ₗ[ℝ] Y) : ℕ :=
  Module.finrank ℝ A.range

/-- PMA 9.30: an endomorphism of real n-space is invertible exactly at full rank. -/
theorem pma9_30_full_rank {n : ℕ} (A : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ)) :
    Function.Bijective A ↔ pma9_30_finrank A = n := by
  constructor
  · intro h
    simpa using LinearMap.finrank_range_of_inj h.1
  · intro h
    have hr : A.range = ⊤ := Submodule.eq_top_of_finrank_eq (by simpa using h)
    exact ⟨(LinearMap.injective_iff_surjective).mpr (LinearMap.range_eq_top.mp hr),
      LinearMap.range_eq_top.mp hr⟩

/-- PMA 9.30: rank zero means that the map vanishes, and its kernel is the whole space. -/
theorem pma9_30_rank_zero {X Y : Type*} [AddCommGroup X] [Module ℝ X]
    [AddCommGroup Y] [Module ℝ Y] (A : X →ₗ[ℝ] Y)
    (h : pma9_30_rank A = 0) : (∀ x, A x = 0) ∧ A.ker = ⊤ := by
  have hr : A.range = ⊥ := (Submodule.rank_eq_zero).mp h
  have ha : A = 0 := LinearMap.range_eq_bot.mp hr
  simp [ha]

/-- PMA 9.31: a projection is an idempotent linear operator. -/
def pma9_31_isProjection {X : Type*} [AddCommGroup X] [Module ℝ X]
    (P : X →ₗ[ℝ] X) : Prop := P.comp P = P

/-- PMA 9.31: the pointwise form of the definition. -/
theorem pma9_31_iff {X : Type*} [AddCommGroup X] [Module ℝ X] (P : X →ₗ[ℝ] X) :
    pma9_31_isProjection P ↔ ∀ x, P (P x) = P x := LinearMap.ext_iff

/-- PMA 9.31: a projection fixes exactly its range. -/
theorem pma9_31_range_iff {X : Type*} [AddCommGroup X] [Module ℝ X]
    {P : X →ₗ[ℝ] X} (hP : pma9_31_isProjection P) (x : X) :
    x ∈ P.range ↔ P x = x := by
  exact LinearMap.IsIdempotentElem.mem_range_iff (show IsIdempotentElem P from hP)

/-- PMA 9.31(a): every vector decomposes uniquely into range and kernel components. -/
theorem pma9_31_a {X : Type*} [AddCommGroup X] [Module ℝ X]
    {P : X →ₗ[ℝ] X} (hP : pma9_31_isProjection P) (x : X) :
    ∃! yz : X × X, yz.1 ∈ P.range ∧ yz.2 ∈ P.ker ∧ x = yz.1 + yz.2 := by
  have hp := (pma9_31_iff P).mp hP
  refine ⟨(P x, x - P x), ⟨LinearMap.mem_range_self P x, ?_, by simp⟩, ?_⟩
  · simp [LinearMap.mem_ker, hp]
  · rintro ⟨y,z⟩ ⟨hy,hz,hx⟩
    have hpy : P y = y := (pma9_31_range_iff hP y).mp hy
    have hpz : P z = 0 := hz
    have he : P x = y := by rw [hx, map_add, hpy, hpz, add_zero]
    apply Prod.ext
    · exact he.symm
    · rw [he, hx]
      abel_nf

/-- PMA 9.31(b): every subspace is a projection range.
The result is proved in arbitrary vector spaces, which strengthens the printed
finite-dimensional assumption without changing its conclusion. -/
theorem pma9_31_b {X : Type*} [AddCommGroup X] [Module ℝ X]
    (Y : Submodule ℝ X) : ∃ P : X →ₗ[ℝ] X, pma9_31_isProjection P ∧ P.range = Y := by
  obtain ⟨Z, hZ⟩ := Y.exists_isCompl
  exact ⟨Y.projection Z hZ, Submodule.isIdempotentElem_projection hZ,
    Submodule.range_projection hZ⟩

/-- PMA 9.31(b), final observation: a nonzero proper subspace is the range
of infinitely many distinct projections. The arbitrary-dimensional version is
again a strengthening of the printed finite-dimensional case. -/
theorem pma9_31_infinitely_many {X : Type*} [AddCommGroup X] [Module ℝ X]
    (Y : Submodule ℝ X) (hbot : Y ≠ ⊥) (htop : Y ≠ ⊤) :
    {P : X →ₗ[ℝ] X | pma9_31_isProjection P ∧ P.range = Y}.Infinite := by
  obtain ⟨P, hP, hr⟩ := pma9_31_b Y
  obtain ⟨v, hvY, hv⟩ := Y.ne_bot_iff.mp hbot
  obtain ⟨φ, hφ, hφY⟩ := Y.exists_dual_map_eq_bot_of_lt_top (lt_top_iff_ne_top.mpr htop)
    inferInstance
  have hvan : ∀ x ∈ Y, φ x = 0 := by
    intro x hx
    have hm : φ x ∈ Y.map φ := Submodule.mem_map.mpr ⟨x, hx, rfl⟩
    simpa [hφY] using hm
  have hnonzero : φ.smulRight v ≠ 0 := by
    intro he
    apply hφ
    ext x
    have hx := DFunLike.congr_fun he x
    simpa [LinearMap.smulRight_apply, hv] using hx
  let Q : ℝ → (X →ₗ[ℝ] X) := fun c => P + c • φ.smulRight v
  have hQ (c : ℝ) : LinearMap.IsProj Y (Q c) := by
    constructor
    · intro x
      exact Y.add_mem (hr ▸ LinearMap.mem_range_self P x)
        (Y.smul_mem c (Y.smul_mem (φ x) hvY))
    · intro x hx
      have hpx : P x = x := (pma9_31_range_iff hP x).mp (hr ▸ hx)
      simp [Q, hvan x hx, hpx]
  apply Set.infinite_of_injective_forall_mem (f := Q)
  · intro c d he
    exact smul_left_injective ℝ hnonzero (add_left_cancel he)
  · intro c
    exact ⟨(hQ c).isIdempotentElem, (hQ c).range⟩

/-- PMA 9.33, formula (82): sign of an integer tuple. -/
def pma9_33_sign {n : ℕ} (j : Fin n → ℤ) : ℤ :=
  ∏ q, ∏ p ∈ Finset.Iio q, Int.sign (j q - j p)

/-- PMA 9.33: interchanging two tuple entries reverses the sign. -/
theorem pma9_33_sign_swap {n : ℕ} (j : Fin n → ℤ) (a b : Fin n) (hab : a ≠ b) :
    pma9_33_sign (j ∘ Equiv.swap a b) = -pma9_33_sign j := by
  have h := (Equiv.swap a b).prod_Iio_comp_eq_sign_mul_prod
    (f := fun p q => Int.sign (j q - j p)) (fun p q => by
      rw [← neg_sub (j p) (j q), Int.sign_neg])
  simpa [pma9_33_sign, Equiv.Perm.sign_swap hab] using h

/-- PMA 9.33: tuple signs take only the three stated values. -/
theorem pma9_33_sign_values {n : ℕ} (j : Fin n → ℤ) :
    pma9_33_sign j = 1 ∨ pma9_33_sign j = 0 ∨ pma9_33_sign j = -1 := by
  let g : ℤ →* ℤ := ⟨⟨Int.sign, Int.sign_one⟩, Int.sign_mul⟩
  have h : pma9_33_sign j = Int.sign (∏ q, ∏ p ∈ Finset.Iio q, (j q - j p)) := by
    change (∏ q, ∏ p ∈ Finset.Iio q, g (j q - j p)) =
      g (∏ q, ∏ p ∈ Finset.Iio q, (j q - j p))
    simp only [map_prod]
  rw [h]
  exact Int.sign_trichotomy _

/-- PMA 9.33: the sign of an increasing standard tuple is one. -/
theorem pma9_33_sign_standard (n : ℕ) :
    pma9_33_sign (fun i : Fin n => (i : ℤ)) = 1 := by
  apply Finset.prod_eq_one
  intro q _
  apply Finset.prod_eq_one
  intro p hp
  apply Int.sign_eq_one_of_pos
  have hpq := Finset.mem_Iio.mp hp
  apply sub_pos.mpr
  change (p.val : ℤ) < (q.val : ℤ)
  exact_mod_cast hpq

/-- PMA 9.33: on permutations, the product sign equals the usual permutation sign. -/
theorem pma9_33_sign_perm {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    pma9_33_sign (fun i => (σ i : ℤ)) = (σ.sign : ℤ) := by
  have h := σ.prod_Iio_comp_eq_sign_mul_prod
    (f := fun p q => Int.sign ((q : ℤ) - (p : ℤ))) (fun p q => by
      rw [← neg_sub (p : ℤ) (q : ℤ), Int.sign_neg])
  change pma9_33_sign (fun i => (σ i : ℤ)) =
    (σ.sign : ℤ) * pma9_33_sign (fun i => (i : ℤ)) at h
  simpa [pma9_33_sign_standard] using h

/-- PMA 9.33: repetitions force the tuple sign to vanish. -/
theorem pma9_33_sign_repeated {n : ℕ} (j : Fin n → ℤ)
    (a b : Fin n) (hab : a ≠ b) (heq : j a = j b) : pma9_33_sign j = 0 := by
  have h := pma9_33_sign_swap j a b hab
  have hf : j ∘ Equiv.swap a b = j := by
    funext i
    exact Equiv.apply_swap_eq_self heq i
  rw [hf] at h
  omega

/-- PMA 9.33: all nonpermutation index tuples contribute zero. -/
theorem pma9_33_sign_not_bijective {n : ℕ} (j : Fin n → Fin n)
    (hj : ¬ Function.Bijective j) : pma9_33_sign (fun i => (j i : ℤ)) = 0 := by
  have hn : ¬ Function.Injective j := fun h => hj (Finite.injective_iff_bijective.mp h)
  obtain ⟨a, b, heq, hab⟩ : ∃ a b, j a = j b ∧ a ≠ b := by
    unfold Function.Injective at hn
    push Not at hn
    exact hn
  exact pma9_33_sign_repeated _ a b hab (by rw [heq])

/-- PMA 9.33, formula (83): sum over all tuples, including repeated indices. -/
def pma9_33_det {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  ∑ j : Fin n → Fin n, (pma9_33_sign (fun i => (j i : ℤ)) : ℝ) * ∏ i, A i (j i)

/-- PMA 9.33: the printed all-tuples definition agrees with `Matrix.det`. -/
theorem pma9_33_det_eq {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) :
    pma9_33_det A = A.det := by
  classical
  unfold pma9_33_det
  calc
    (∑ j : Fin n → Fin n, (pma9_33_sign (fun i => (j i : ℤ)) : ℝ) * ∏ i, A i (j i)) =
        ∑ j : Fin n → Fin n with Function.Bijective j,
          (pma9_33_sign (fun i => (j i : ℤ)) : ℝ) * ∏ i, A i (j i) := by
      symm
      apply Finset.sum_subset (Finset.filter_subset _ _)
      intro j _ hj
      have hn : ¬ Function.Bijective j := by simpa using hj
      simp [pma9_33_sign_not_bijective j hn]
    _ = ∑ σ : Equiv.Perm (Fin n), (σ.sign : ℝ) * ∏ i, A i (σ i) := by
      apply Finset.sum_bij (fun j hj => Equiv.ofBijective j (Finset.mem_filter.mp hj).2)
      · intro j hj
        exact Finset.mem_univ _
      · intro a ha b hb h
        exact congrArg Equiv.toFun h
      · intro σ _
        exact ⟨σ, Finset.mem_filter.mpr ⟨Finset.mem_univ _, σ.bijective⟩,
          Equiv.coe_fn_injective rfl⟩
      · intro j hj
        rw [← pma9_33_sign_perm (Equiv.ofBijective j (Finset.mem_filter.mp hj).2)]
        rfl
    _ = A.det := by
      rw [← Matrix.det_transpose, Matrix.det_apply']
      rfl

/-- PMA 9.33, formula (84): a column in standard-basis coordinates. -/
theorem pma9_33_column {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (j : Fin n) :
    (fun i => A i j) = ∑ i, A i j • Pi.single i (1 : ℝ) := by
  ext k
  simp [Pi.single_apply, Finset.sum_apply]

/-- PMA 9.33: view the determinant as a function of its column vectors. -/
def pma9_33_detColumns {n : ℕ} (x : Fin n → (Fin n → ℝ)) : ℝ :=
  pma9_33_det (fun i j => x j i)

/-- PMA 9.34(a). -/
theorem pma9_34_a (n : ℕ) : Matrix.det (1 : Matrix (Fin n) (Fin n) ℝ) = 1 :=
  Matrix.det_one

/-- PMA 9.34(b): additivity in one column. -/
theorem pma9_34_b_add {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (j : Fin n)
    (u v : Fin n → ℝ) : (A.updateCol j (u + v)).det =
      (A.updateCol j u).det + (A.updateCol j v).det := Matrix.det_updateCol_add A j u v

/-- PMA 9.34(b): homogeneity in one column. -/
theorem pma9_34_b_smul {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (j : Fin n)
    (c : ℝ) (u : Fin n → ℝ) : (A.updateCol j (c • u)).det =
      c * (A.updateCol j u).det := Matrix.det_updateCol_smul A j c u

/-- PMA 9.34(c). -/
theorem pma9_34_c {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (i j : Fin n) (h : i ≠ j) :
    (A.submatrix id (Equiv.swap i j)).det = -A.det := by
  simpa [Equiv.Perm.sign_swap h] using Matrix.det_permute' (Equiv.swap i j) A

/-- PMA 9.34(d). -/
theorem pma9_34_d {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (i j : Fin n) (h : i ≠ j) (heq : ∀ k, A k i = A k j) : A.det = 0 :=
  Matrix.det_zero_of_column_eq h heq

/-- PMA 9.35: multiplicativity. -/
theorem pma9_35 {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℝ) :
    (B * A).det = B.det * A.det := Matrix.det_mul B A

/-- PMA 9.36: invertibility is equivalent to nonzero determinant.
The basis-free finite-dimensional formulation includes the printed real coordinate spaces. -/
theorem pma9_36 {X : Type*} [AddCommGroup X] [Module ℝ X] [FiniteDimensional ℝ X]
    (A : X →ₗ[ℝ] X) : Function.Bijective A ↔ LinearMap.det A ≠ 0 := by
  rw [ne_eq, LinearMap.det_eq_zero_iff_ker_ne_bot, not_not, LinearMap.ker_eq_bot]
  exact ⟨fun h => h.1, fun h => ⟨h, LinearMap.injective_iff_surjective.mp h⟩⟩

/-- PMA 9.36, matrix formulation. -/
theorem pma9_36_matrix {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) :
    IsUnit A ↔ A.det ≠ 0 := by
  rw [Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero]

/-- PMA 9.37, equation (91): the change-of-basis matrix intertwines the two matrices. -/
theorem pma9_37_change_basis {X : Type*} [AddCommGroup X] [Module ℝ X]
    {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (e : Basis ι ℝ X) (u : Basis κ ℝ X) (A : X →ₗ[ℝ] X) :
    e.toMatrix u * LinearMap.toMatrix u u A =
      LinearMap.toMatrix e e A * e.toMatrix u := by
  rw [basis_toMatrix_mul_linearMap_toMatrix, linearMap_toMatrix_mul_basis_toMatrix]

/-- PMA 9.37: the matrix determinant is independent of the chosen basis. -/
theorem pma9_37 {X : Type*} [AddCommGroup X] [Module ℝ X]
    {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (e : Basis ι ℝ X) (u : Basis κ ℝ X) (A : X →ₗ[ℝ] X) :
    (LinearMap.toMatrix e e A).det = (LinearMap.toMatrix u u A).det :=
  LinearMap.det_toMatrix_eq_det_toMatrix e u A

/-- PMA 9.38: the Jacobian determinant of a differentiable map.
As with `fderiv`, the definition extends to all points by assigning the determinant
of the zero derivative when differentiability fails; theorems below use actual derivatives. -/
def pma9_38_jacobian {n : ℕ} (f : (Fin n → ℝ) → (Fin n → ℝ)) (x : Fin n → ℝ) : ℝ :=
  LinearMap.det (fderiv ℝ f x).toLinearMap

/-- PMA 9.38: an actual derivative calculates the Jacobian. -/
theorem pma9_38_eq {n : ℕ} {f : (Fin n → ℝ) → (Fin n → ℝ)} {x : Fin n → ℝ}
    {A : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ)} (h : HasFDerivAt f A x) :
    pma9_38_jacobian f x = LinearMap.det A.toLinearMap := by
  rw [pma9_38_jacobian, h.fderiv]

/-- PMA 9.38: nonvanishing Jacobian is precisely the invertibility condition. -/
theorem pma9_38_nonzero_iff {n : ℕ} (f : (Fin n → ℝ) → (Fin n → ℝ)) (x : Fin n → ℝ) :
    pma9_38_jacobian f x ≠ 0 ↔ Function.Bijective (fderiv ℝ f x) :=
  (pma9_36 (fderiv ℝ f x).toLinearMap).symm

/-- PMA 9.38: the Jacobian is the determinant of the derivative matrix. -/
theorem pma9_38_matrix {n : ℕ} (f : (Fin n → ℝ) → (Fin n → ℝ)) (x : Fin n → ℝ) :
    pma9_38_jacobian f x =
      Matrix.det (fun i j => (fderiv ℝ f x (Pi.single j 1)) i) := by
  exact (LinearMap.det_toMatrix' (fderiv ℝ f x).toLinearMap).symm

/-- PMA 9.38: at a differentiability point, the derivative matrix entries
are the actual coordinate partial derivatives. -/
theorem pma9_38_partials {n : ℕ} {f : (Fin n → ℝ) → (Fin n → ℝ)}
    {x : Fin n → ℝ} (hf : DifferentiableAt ℝ f x) :
    pma9_38_jacobian f x = Matrix.det
      (fun i j => deriv (fun t : ℝ => f (x + t • Pi.single j 1) i) 0) := by
  rw [pma9_38_matrix]
  congr 1
  funext i j
  have hpath : HasDerivAt (fun t : ℝ => x + t • Pi.single j (1 : ℝ))
      (Pi.single j (1 : ℝ)) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const (Pi.single j (1 : ℝ))).const_add x
  have hfpath : HasFDerivAt f (fderiv ℝ f x)
      ((fun t : ℝ => x + t • Pi.single j (1 : ℝ)) 0) := by
    simpa using hf.hasFDerivAt
  have hcomp := (ContinuousLinearMap.proj (R := ℝ) i).hasFDerivAt.comp_hasDerivAt 0
    (hfpath.comp_hasDerivAt 0 hpath)
  exact hcomp.deriv.symm

/-- PMA 9.38, final paragraph: the implicit-function hypothesis is nonvanishing
of the Jacobian in the first coordinate block. -/
theorem pma9_38_implicit {n m : ℕ}
    {f : ((Fin n → ℝ) × (Fin m → ℝ)) → (Fin n → ℝ)}
    {a : Fin n → ℝ} {b : Fin m → ℝ}
    {L : ((Fin n → ℝ) × (Fin m → ℝ)) →L[ℝ] (Fin n → ℝ)}
    (h : HasFDerivAt f L (a, b)) :
    Function.Bijective (L.comp (ContinuousLinearMap.inl ℝ (Fin n → ℝ) (Fin m → ℝ))) ↔
      pma9_38_jacobian (fun x => f (x, b)) a ≠ 0 := by
  have hd : HasFDerivAt (fun x => f (x, b))
      (L.comp (ContinuousLinearMap.inl ℝ (Fin n → ℝ) (Fin m → ℝ))) a :=
    h.comp a (hasFDerivAt_prodMk_left (𝕜 := ℝ) a b)
  rw [pma9_38_eq hd]
  exact pma9_36 _

end Rudin.PMA.Chapter09
