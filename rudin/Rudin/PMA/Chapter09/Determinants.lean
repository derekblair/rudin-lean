import Rudin.PMA.Chapter09.Differentiation

set_option autoImplicit false
noncomputable section
open Set Filter Topology Module
open scoped BigOperators

namespace Rudin.PMA.Chapter09

/-- Rudin's sign factor for an arbitrary ordered integer tuple. -/
def tupleSign {n : ℕ} (t : Fin n → ℤ) : ℤ :=
  ∏ i, ∏ j ∈ Finset.Ioi i, Int.sign (t j - t i)

/-- The determinant as a function of its ordered column vectors. -/
def columnDet {n : ℕ} (v : Fin n → Euclidean n) : ℝ :=
  Matrix.det (fun i j => v j i)

/-- The Jacobian is the determinant of the total derivative in standard bases. -/
def jacobian {n : ℕ} (f : Euclidean n → Euclidean n) (x : Euclidean n) : ℝ :=
  Matrix.det (operatorMatrix (fderiv ℝ f x))

/-- The partial Jacobian for the first (solved) variable block. -/
def partialJacobian {n m : ℕ} (f : Euclidean n × Euclidean m → Euclidean n)
    (z : Euclidean n × Euclidean m) : ℝ :=
  Matrix.det (operatorMatrix
    ((fderiv ℝ f z).comp (ContinuousLinearMap.inl ℝ (Euclidean n) (Euclidean m))))

def pma9_33_contract : Prop :=
  (∀ (n : ℕ) (t : Fin n → ℤ), tupleSign t = -1 ∨ tupleSign t = 0 ∨ tupleSign t = 1) ∧
  (∀ (n : ℕ) (t : Fin n → ℤ) (i j : Fin n), i ≠ j →
    tupleSign (t ∘ Equiv.swap i j) = -tupleSign t) ∧
  (∀ (n : ℕ) (t : Fin n → ℤ) (i j : Fin n), i ≠ j → t i = t j → tupleSign t = 0) ∧
  (∀ (n : ℕ) (σ : Equiv.Perm (Fin n)),
    tupleSign (fun i => ((σ i).val : ℤ)) = (σ.sign : ℤ)) ∧
  (∀ (n : ℕ) (A : Matrix (Fin n) (Fin n) ℝ),
    A.det = ∑ t : Fin n → Fin n,
      (tupleSign (fun i => ((t i).val : ℤ)) : ℝ) * ∏ i, A i (t i)) ∧
  (∀ (n : ℕ) (v : Fin n → Euclidean n),
    columnDet v = Matrix.det (fun i j => v j i))

def pma9_34_contract : Prop :=
  (∀ n : ℕ, Matrix.det (1 : Matrix (Fin n) (Fin n) ℝ) = 1) ∧
  (∀ (n : ℕ) (A : Matrix (Fin n) (Fin n) ℝ) (j : Fin n)
      (u v : Fin n → ℝ) (a b : ℝ),
    (A.updateCol j (a • u + b • v)).det =
      a * (A.updateCol j u).det + b * (A.updateCol j v).det) ∧
  (∀ (n : ℕ) (A : Matrix (Fin n) (Fin n) ℝ) (i j : Fin n), i ≠ j →
    (A.submatrix id (Equiv.swap i j)).det = -A.det) ∧
  (∀ (n : ℕ) (A : Matrix (Fin n) (Fin n) ℝ) (i j : Fin n), i ≠ j →
    (∀ k, A k i = A k j) → A.det = 0)

def pma9_35_contract : Prop :=
  ∀ (n : ℕ) (A B : Matrix (Fin n) (Fin n) ℝ), (B * A).det = B.det * A.det

def pma9_36_contract : Prop :=
  ∀ (n : ℕ) (A : Operator n n), IsUnit A ↔ (operatorMatrix A).det ≠ 0

def pma9_37_contract : Prop :=
  ∀ (X : Type*) [AddCommGroup X] [Module ℝ X] (n : ℕ)
      (b c : Basis (Fin n) ℝ X) (A : X →ₗ[ℝ] X),
    LinearMap.toMatrix c b LinearMap.id * LinearMap.toMatrix c c A =
      LinearMap.toMatrix b b A * LinearMap.toMatrix c b LinearMap.id ∧
    (LinearMap.toMatrix b b A).det = (LinearMap.toMatrix c c A).det ∧
    (LinearMap.toMatrix b b A).det = LinearMap.det A

def pma9_38_contract : Prop :=
  (∀ (n : ℕ) (f : Euclidean n → Euclidean n) (x : Euclidean n),
    DifferentiableAt ℝ f x →
      jacobian f x = LinearMap.det (fderiv ℝ f x).toLinearMap ∧
      ((fderiv ℝ f x).IsInvertible ↔ jacobian f x ≠ 0)) ∧
  (∀ (n m : ℕ) (f : Euclidean n × Euclidean m → Euclidean n)
      (z : Euclidean n × Euclidean m), DifferentiableAt ℝ f z →
    (((fderiv ℝ f z).comp
      (ContinuousLinearMap.inl ℝ (Euclidean n) (Euclidean m))).IsInvertible ↔
        partialJacobian f z ≠ 0))

private theorem int_sign_prod {ι : Type*} (s : Finset ι) (f : ι → ℤ) :
    Int.sign (∏ i ∈ s, f i) = ∏ i ∈ s, Int.sign (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih => simp [ha, ih]

theorem tupleSign_trichotomy {n : ℕ} (t : Fin n → ℤ) :
    tupleSign t = -1 ∨ tupleSign t = 0 ∨ tupleSign t = 1 := by
  have h : tupleSign t = Int.sign (∏ i, ∏ j ∈ Finset.Ioi i, (t j - t i)) := by
    simp only [tupleSign, int_sign_prod]
  rw [h]
  rcases lt_trichotomy (∏ i, ∏ j ∈ Finset.Ioi i, (t j - t i)) 0 with h | h | h
  · exact Or.inl (Int.sign_eq_neg_one_of_neg h)
  · exact Or.inr (Or.inl (by rw [h]; rfl))
  · exact Or.inr (Or.inr (Int.sign_eq_one_of_pos h))

theorem tupleSign_swap {n : ℕ} (t : Fin n → ℤ) (i j : Fin n) (hij : i ≠ j) :
    tupleSign (t ∘ Equiv.swap i j) = -tupleSign t := by
  have ha : ∀ i j : Fin n, Int.sign (t j - t i) = -Int.sign (t i - t j) := by
    intro i j
    rw [← Int.sign_neg, neg_sub]
  have h := (Equiv.swap i j).prod_Ioi_comp_eq_sign_mul_prod ha
  simpa [tupleSign, Function.comp_def, Equiv.Perm.sign_swap hij] using h

theorem tupleSign_repeated {n : ℕ} (t : Fin n → ℤ) (i j : Fin n)
    (hij : i ≠ j) (ht : t i = t j) : tupleSign t = 0 := by
  have hs : t ∘ Equiv.swap i j = t := by
    funext k
    by_cases hki : k = i
    · subst k; simp [ht]
    by_cases hkj : k = j
    · subst k; simp [ht]
    simp [Equiv.swap_apply_of_ne_of_ne hki hkj]
  have h := tupleSign_swap t i j hij
  rw [hs] at h
  omega

theorem tupleSign_permutation {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    tupleSign (fun i => ((σ i).val : ℤ)) = (σ.sign : ℤ) := by
  rw [tupleSign, σ.sign_eq_prod_prod_Ioi]
  simp only [Units.coe_prod]
  apply Finset.prod_congr rfl
  intro i _
  apply Finset.prod_congr rfl
  intro j hj
  have hij : i < j := Finset.mem_Ioi.mp hj
  have hne : σ i ≠ σ j := fun h => hij.ne (σ.injective h)
  by_cases h : σ i < σ j
  · rw [if_pos h]
    exact Int.sign_eq_one_of_pos (sub_pos.mpr (by exact_mod_cast h))
  · rw [if_neg h]
    exact Int.sign_eq_neg_one_of_neg (by
      have hlt : σ j < σ i := lt_of_le_of_ne (le_of_not_gt h) (Ne.symm hne)
      exact sub_neg.mpr (by exact_mod_cast hlt))

/-- The repeated-index terms vanish, so the permutation and all-tuple formulas agree. -/
theorem determinant_all_tuples {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) :
    A.det = ∑ t : Fin n → Fin n,
      (tupleSign (fun i => ((t i).val : ℤ)) : ℝ) * ∏ i, A i (t i) := by
  classical
  rw [← Matrix.det_transpose, Matrix.det_apply']
  apply Fintype.sum_of_injective (fun σ : Equiv.Perm (Fin n) => (σ : Fin n → Fin n))
    (fun σ τ h => Equiv.ext (congrFun h))
  · intro t ht
    have hn : ¬ Function.Injective t := by
      intro h
      exact ht ⟨Equiv.ofBijective t ⟨h, Finite.surjective_of_injective h⟩, rfl⟩
    simp only [Function.Injective] at hn
    push_neg at hn
    obtain ⟨i, j, heq, hne⟩ := hn
    rw [tupleSign_repeated _ i j hne (by simpa only [heq])]
    simp
  · intro σ
    simp only [tupleSign_permutation, Matrix.transpose_apply]

theorem pma9_33 : pma9_33_contract := by
  exact ⟨fun n t => tupleSign_trichotomy t, fun n t i j => tupleSign_swap t i j,
    fun n t i j => tupleSign_repeated t i j, fun n σ => tupleSign_permutation σ,
    fun n A => determinant_all_tuples A, fun n v => rfl⟩

theorem pma9_34 : pma9_34_contract := by
  refine ⟨fun n => Matrix.det_one, ?_, ?_, ?_⟩
  · intro n A j u v a b
    rw [Matrix.det_updateCol_add, Matrix.det_updateCol_smul, Matrix.det_updateCol_smul]
  · intro n A i j hij
    simpa [Equiv.Perm.sign_swap hij] using Matrix.det_permute' (Equiv.swap i j) A
  · intro n A i j hij heq
    exact Matrix.det_zero_of_column_eq hij heq

theorem pma9_35 : pma9_35_contract := by
  intro n A B
  exact Matrix.det_mul B A

theorem operator_isUnit_iff_det_ne_zero {n : ℕ} (A : Operator n n) :
    IsUnit A ↔ (operatorMatrix A).det ≠ 0 := by
  rw [ContinuousLinearMap.isUnit_iff_isUnit_toLinearMap,
    LinearMap.isUnit_iff_isUnit_det, isUnit_iff_ne_zero]
  rw [operatorMatrix, LinearMap.det_toMatrix]

theorem pma9_36 : pma9_36_contract := by
  intro n A
  exact operator_isUnit_iff_det_ne_zero A

theorem pma9_37 : pma9_37_contract := by
  intro X _ _ n b c A
  refine ⟨?_, LinearMap.det_toMatrix_eq_det_toMatrix b c A, LinearMap.det_toMatrix b A⟩
  rw [← LinearMap.toMatrix_comp c c b, ← LinearMap.toMatrix_comp c b b]
  simp

theorem operator_isInvertible_iff_isUnit {n : ℕ} (A : Operator n n) :
    A.IsInvertible ↔ IsUnit A := by
  rw [ContinuousLinearMap.isUnit_iff_bijective]
  constructor
  · rintro ⟨e, rfl⟩
    exact e.bijective
  · intro h
    exact ⟨ContinuousLinearEquiv.ofBijective A
      (LinearMap.ker_eq_bot.mpr h.1) (LinearMap.range_eq_top.mpr h.2), rfl⟩

theorem pma9_38 : pma9_38_contract := by
  constructor
  · intro n f x _
    refine ⟨LinearMap.det_toMatrix (standardBasis n) _, ?_⟩
    exact (operator_isInvertible_iff_isUnit _).trans (operator_isUnit_iff_det_ne_zero _)
  · intro n m f z _
    exact (operator_isInvertible_iff_isUnit _).trans (operator_isUnit_iff_det_ne_zero _)

end Rudin.PMA.Chapter09
