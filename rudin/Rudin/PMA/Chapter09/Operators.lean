import Mathlib

/-!
# PMA 9.6–9.9: linear operators and their matrices

The real Euclidean spaces here use their Euclidean norm, not the sup norm on
functions. Algebraic linear maps are retained in 9.6(a,b) and 9.9. For normed
results, the equivalence `pma9_6_continuousEquiv` explicitly identifies every
algebraic map on these finite dimensional spaces with a continuous linear map;
thus the bundled continuity condition does not restrict the book's operators.
-/

noncomputable section
set_option synthInstance.maxHeartbeats 200000
open scoped BigOperators
open Set

namespace Rudin.PMA.Chapter09

/-- 9.6(a): the space of linear transformations. -/
abbrev pma9_6_linearMaps (X Y : Type*) [AddCommGroup X] [AddCommGroup Y]
    [Module ℝ X] [Module ℝ Y] := X →ₗ[ℝ] Y

/-- 9.6(a): linear combinations act pointwise. -/
theorem pma9_6_linearCombination {X Y : Type*} [AddCommGroup X] [AddCommGroup Y]
    [Module ℝ X] [Module ℝ Y] (A B : X →ₗ[ℝ] Y) (a b : ℝ) (x : X) :
    (a • A + b • B) x = a • A x + b • B x := rfl

/-- 9.6(b): multiplication of transformations means composition. -/
theorem pma9_6_composition {X Y Z : Type*} [AddCommGroup X] [AddCommGroup Y]
    [AddCommGroup Z] [Module ℝ X] [Module ℝ Y] [Module ℝ Z]
    (A : X →ₗ[ℝ] Y) (B : Y →ₗ[ℝ] Z) (x : X) : B.comp A x = B (A x) := rfl

/-- 9.6(b): compositions of endomorphisms need not commute. -/
theorem pma9_6_noncommutative :
    ∃ A B : (ℝ × ℝ) →ₗ[ℝ] (ℝ × ℝ), A.comp B ≠ B.comp A := by
  let A := (LinearMap.inl ℝ ℝ ℝ).comp (LinearMap.snd ℝ ℝ ℝ)
  let B := (LinearMap.inr ℝ ℝ ℝ).comp (LinearMap.fst ℝ ℝ ℝ)
  refine ⟨A, B, ?_⟩
  intro h
  have h' := congrArg (fun F : (ℝ × ℝ) →ₗ[ℝ] (ℝ × ℝ) => (F (1, 0)).1) h
  norm_num [A, B] at h'

/-- 9.6(c), 9.7(a): bundling continuity does not remove any linear transformation. -/
def pma9_6_continuousEquiv (n m : ℕ) :
    (EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin m)) ≃ₗ[ℝ]
      (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin m)) :=
  LinearMap.toContinuousLinearMap

/-- 9.6(c): the operator norm is the supremum on the closed unit ball. -/
theorem pma9_6_norm_eq_sup {n m : ℕ}
    (A : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin m)) :
    ‖A‖ = sSup ((fun x => ‖A x‖) '' Metric.closedBall 0 1) :=
  A.sSup_unitClosedBall_eq_norm.symm

/-- 9.6(c): the defining norm estimate. -/
theorem pma9_6_bound {n m : ℕ}
    (A : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin m)) (x) :
    ‖A x‖ ≤ ‖A‖ * ‖x‖ := A.le_opNorm x

/-- 9.6(c): least bound characterization. We allow the zero dimensional domain;
there the explicit nonnegativity of the candidate bound is necessary. -/
theorem pma9_6_least_bound {n m : ℕ}
    (A : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin m))
    {c : ℝ} (hc : 0 ≤ c) (h : ∀ x, ‖A x‖ ≤ c * ‖x‖) : ‖A‖ ≤ c :=
  A.opNorm_le_bound hc h

/-- 9.6(c): the least-bound assertion without a sign hypothesis in positive
 dimension, exactly as in the book. -/
theorem pma9_6_least_bound_positive_dimension {n m : ℕ} [Nonempty (Fin n)]
    (A : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin m))
    {c : ℝ} (h : ∀ x, ‖A x‖ ≤ c * ‖x‖) : ‖A‖ ≤ c := by
  obtain ⟨i⟩ := ‹Nonempty (Fin n)›
  have hc : 0 ≤ c := by
    have hi := (norm_nonneg (A (EuclideanSpace.basisFun (Fin n) ℝ i))).trans
      (h (EuclideanSpace.basisFun (Fin n) ℝ i))
    simpa using hi
  exact A.opNorm_le_bound hc h

/-- 9.7(a): the proof's explicit finite bound by the norms of the columns. -/
theorem pma9_7_column_bound {n m : ℕ}
    (A : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin m)) :
    ‖A‖ ≤ ∑ i, ‖A (EuclideanSpace.basisFun (Fin n) ℝ i)‖ := by
  apply A.opNorm_le_bound (Finset.sum_nonneg fun _ _ => norm_nonneg _) ?_
  intro x
  calc
    ‖A x‖ = ‖∑ i, x i • A (EuclideanSpace.basisFun (Fin n) ℝ i)‖ := by
      nth_rw 1 [← (EuclideanSpace.basisFun (Fin n) ℝ).sum_repr x]
      simp only [map_sum, map_smul, EuclideanSpace.basisFun_repr]
    _ ≤ ∑ i, ‖x i • A (EuclideanSpace.basisFun (Fin n) ℝ i)‖ := norm_sum_le _ _
    _ = ∑ i, ‖x i‖ * ‖A (EuclideanSpace.basisFun (Fin n) ℝ i)‖ := by
      simp only [norm_smul]
    _ ≤ ∑ i, ‖x‖ * ‖A (EuclideanSpace.basisFun (Fin n) ℝ i)‖ := by
      exact Finset.sum_le_sum fun i _ =>
        mul_le_mul_of_nonneg_right (PiLp.norm_apply_le x i) (norm_nonneg _)
    _ = (∑ i, ‖A (EuclideanSpace.basisFun (Fin n) ℝ i)‖) * ‖x‖ := by
      rw [← Finset.mul_sum, mul_comm]

/-- 9.7(a): every algebraic linear map has a finite norm and is uniformly continuous.
Finiteness is expressed by a real bound on the operator norm. -/
theorem pma9_7_a {n m : ℕ}
    (A : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin m)) :
    (∃ C : ℝ, ‖pma9_6_continuousEquiv n m A‖ ≤ C) ∧ UniformContinuous A := by
  exact ⟨⟨_, le_rfl⟩, (pma9_6_continuousEquiv n m A).uniformContinuous⟩

/-- 9.7(b): triangle inequality and scalar homogeneity. -/
theorem pma9_7_b {n m : ℕ}
    (A B : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin m)) (c : ℝ) :
    ‖A + B‖ ≤ ‖A‖ + ‖B‖ ∧ ‖c • A‖ = |c| * ‖A‖ := by
  exact ⟨norm_add_le _ _, by simp [norm_smul, Real.norm_eq_abs]⟩

/-- 9.7(b): the metric on the operator space is precisely the norm distance. -/
theorem pma9_7_distance {n m : ℕ}
    (A B : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin m)) :
    dist A B = ‖A - B‖ := dist_eq_norm _ _

/-- 9.7(c): submultiplicativity under composition. -/
theorem pma9_7_c {n m k : ℕ}
    (A : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin m))
    (B : EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin k)) :
    ‖B.comp A‖ ≤ ‖B‖ * ‖A‖ := B.opNorm_comp_le A

/-- 9.8: units are exactly the bijective operators used in the book. -/
theorem pma9_8_invertible_iff {n : ℕ}
    (A : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) :
    IsUnit A ↔ Function.Bijective A := ContinuousLinearMap.isUnit_iff_bijective

/-- 9.8(a): the stated multiplicative perturbation criterion. -/
theorem pma9_8_a {n : ℕ}
    (A : (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))ˣ)
    (B : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (h : ‖B - (A : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))‖ *
      ‖(↑(A⁻¹) : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))‖ < 1) :
    IsUnit B := by
  nontriviality (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
  apply (A.ofNearby B ?_).isUnit
  simpa only [one_div] using (lt_div_iff₀ (Units.norm_pos A⁻¹)).2 h

/-- 9.8(b): invertible operators form an open subset of the operator space. -/
theorem pma9_8_open (n : ℕ) :
    IsOpen {A : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) | IsUnit A} :=
  Units.isOpen

/-- 9.8(b): inversion is continuous on that open set. -/
theorem pma9_8_inverse_continuous (n : ℕ) :
    ContinuousOn Ring.inverse
      {A : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) | IsUnit A} := by
  rintro A ⟨u, rfl⟩
  exact (NormedRing.inverse_continuousAt u).continuousWithinAt

/-- 9.8(b): on the invertible operators inversion is an involution and a bijection. -/
theorem pma9_8_inverse_involution (n : ℕ) :
    Function.Involutive (Inv.inv :
      (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))ˣ →
      (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))ˣ) ∧
    Function.Bijective (Inv.inv :
      (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))ˣ →
      (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))ˣ) :=
  ⟨inv_involutive, inv_involutive.bijective⟩

section Matrices
variable {X Y Z : Type*} [AddCommGroup X] [AddCommGroup Y] [AddCommGroup Z]
  [Module ℝ X] [Module ℝ Y] [Module ℝ Z] {n m k : ℕ}

/-- 9.9: fixing bases gives the linear-map/matrix correspondence. -/
def pma9_9_matrixEquiv (b : Module.Basis (Fin n) ℝ X) (c : Module.Basis (Fin m) ℝ Y) :
    (X →ₗ[ℝ] Y) ≃ₗ[ℝ] Matrix (Fin m) (Fin n) ℝ := LinearMap.toMatrix b c

/-- 9.9, equation (3): a matrix entry is the corresponding coordinate of a column. -/
theorem pma9_9_entry (b : Module.Basis (Fin n) ℝ X) (c : Module.Basis (Fin m) ℝ Y)
    (A : X →ₗ[ℝ] Y) (i : Fin m) (j : Fin n) :
    pma9_9_matrixEquiv b c A i j = c.repr (A (b j)) i :=
  LinearMap.toMatrix_apply b c A i j

/-- 9.9, equation (3): reconstruction of a column from its entries. -/
theorem pma9_9_column (b : Module.Basis (Fin n) ℝ X) (c : Module.Basis (Fin m) ℝ Y)
    (A : X →ₗ[ℝ] Y) (j : Fin n) :
    A (b j) = ∑ i, pma9_9_matrixEquiv b c A i j • c i :=
  by simpa only [pma9_9_entry] using (c.sum_repr (A (b j))).symm

/-- 9.9, equation (4): coordinates of the image are matrix multiplication. -/
theorem pma9_9_coordinates (b : Module.Basis (Fin n) ℝ X) (c : Module.Basis (Fin m) ℝ Y)
    (A : X →ₗ[ℝ] Y) (x : X) (i : Fin m) :
    c.repr (A x) i = ∑ j, pma9_9_matrixEquiv b c A i j * b.repr x j := by
  exact congrFun (LinearMap.toMatrix_mulVec_repr b c A x).symm i

/-- 9.9: the range is spanned by the column vectors. -/
theorem pma9_9_range_columns (b : Module.Basis (Fin n) ℝ X) (A : X →ₗ[ℝ] Y) :
    LinearMap.range A = Submodule.span ℝ (Set.range fun j => A (b j)) := by
  rw [Set.range_comp', ← Submodule.map_span, b.span_eq, Submodule.map_top]

/-- 9.9, equation (5): composition corresponds to matrix multiplication. -/
theorem pma9_9_composition (b : Module.Basis (Fin n) ℝ X) (c : Module.Basis (Fin m) ℝ Y)
    (d : Module.Basis (Fin k) ℝ Z) (A : X →ₗ[ℝ] Y) (B : Y →ₗ[ℝ] Z) :
    pma9_9_matrixEquiv b d (B.comp A) =
      pma9_9_matrixEquiv c d B * pma9_9_matrixEquiv b c A :=
  LinearMap.toMatrix_comp b c d B A

end Matrices

/-- 9.9: the matrix correspondence specialized to standard Euclidean bases. -/
def pma9_9_fromMatrix (n m : ℕ) :
    Matrix (Fin m) (Fin n) ℝ ≃ₗ[ℝ]
      (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin m)) :=
  Matrix.toEuclideanLin.trans (pma9_6_continuousEquiv n m)

/-- 9.9, equation (4), in the standard Euclidean bases. -/
theorem pma9_9_fromMatrix_apply {n m : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (x : EuclideanSpace ℝ (Fin n)) (i : Fin m) :
    pma9_9_fromMatrix n m A x i = ∑ j, A i j * x j := rfl

/-- 9.9: the pointwise Schwarz estimate preceding equation (6). -/
theorem pma9_9_schwarz {n m : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (x : EuclideanSpace ℝ (Fin n)) :
    ‖pma9_9_fromMatrix n m A x‖ ^ 2 ≤ (∑ i, ∑ j, A i j ^ 2) * ‖x‖ ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq]
  simp only [pma9_9_fromMatrix_apply]
  calc
    _ ≤ ∑ i, (∑ j, A i j ^ 2) * (∑ j, x j ^ 2) :=
      Finset.sum_le_sum fun i _ => Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (A i) x
    _ = _ := by rw [← Finset.sum_mul]

/-- 9.9, equation (6): the operator norm is bounded by the Frobenius norm. -/
theorem pma9_9_frobenius_bound {n m : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) :
    ‖pma9_9_fromMatrix n m A‖ ≤ Real.sqrt (∑ i, ∑ j, A i j ^ 2) := by
  apply ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg _) ?_
  intro x
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))).mp
  rw [mul_pow, Real.sq_sqrt (by positivity)]
  exact pma9_9_schwarz A x

/-- 9.9, equation (6), in its printed squared form. -/
theorem pma9_9_frobenius_bound_sq {n m : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) :
    ‖pma9_9_fromMatrix n m A‖ ^ 2 ≤ ∑ i, ∑ j, A i j ^ 2 := by
  have h := (sq_le_sq₀ (norm_nonneg (pma9_9_fromMatrix n m A))
    (Real.sqrt_nonneg (∑ i, ∑ j, A i j ^ 2))).mpr (pma9_9_frobenius_bound A)
  rwa [Real.sq_sqrt (by positivity)] at h

/-- 9.9: continuously varying entries give a continuously varying operator.
Generalization: an arbitrary topological parameter space suffices; the book
assumes a metric space. The target carries its operator norm topology. -/
theorem pma9_9_entrywise_continuous {S : Type*} [TopologicalSpace S] {n m : ℕ}
    (a : S → Matrix (Fin m) (Fin n) ℝ)
    (ha : ∀ i j, Continuous (fun p => a p i j)) :
    Continuous (fun p => pma9_9_fromMatrix n m (a p)) := by
  exact (pma9_9_fromMatrix n m).toLinearMap.continuous_of_finiteDimensional.comp
    (continuous_pi fun i => continuous_pi fun j => ha i j)

end Rudin.PMA.Chapter09
