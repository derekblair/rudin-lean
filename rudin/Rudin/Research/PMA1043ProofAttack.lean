import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.Analysis.Normed.Operator.Extend
import Mathlib.Analysis.Normed.Group.Quotient
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Quotient

import Rudin.Research.PMA1043Compatibility
import Rudin.PMA.AxiomAudit

/-!
# Quantitative lifting and the exact first-order matrix-completion gap

The scalar converse integrates compatible C1 rows to a C2 potential on the
original domains of the printed contract. The matrix existence assertion
remains an explicit hypothesis; this module does not prove the endpoint.

The abstract quotient and dense-data theorems prove a quantitative lifting
mechanism with all kernel directions retained. The concrete function-space
and approximation steps for the fixed-ball estimate are not instantiated.
-/

noncomputable section
set_option autoImplicit false
open Set Function
open scoped BigOperators

namespace Rudin.PMA.Chapter10
open Chapter09


/-- The antisymmetric part of a matrix represented by its three row fields.
The order agrees exactly with the repository's curl orientation. -/
def curlMatrixSkew (M : Fin 3 → VectorField) : VectorField := fun x =>
  coordEquivEuclidean 3
    ![M 2 x 1 - M 1 x 2, M 0 x 2 - M 2 x 0, M 1 x 0 - M 0 x 1]

/-- Three closed C1 rows with the prescribed antisymmetric part. -/
def CompatibleCurlRows (E : Set (Euclidean 3)) (F : VectorField) : Prop :=
  ∃ M : Fin 3 → VectorField,
    (∀ i, ContDiffOn ℝ 1 (M i) E) ∧
    (∀ i, EqOn (curl (M i)) 0 E) ∧ EqOn (curlMatrixSkew M) F E

/-- No endpoint assumption is used: the already proved scalar converse
integrates the three rows separately on the original allowed domain. -/
theorem c2_vectorPotential_iff_compatibleCurlRows {U E : Set (Euclidean 3)}
    (e : C2DomainEquivalence U E) (hU : IsOpen U) (hE : IsOpen E)
    (hc : Convex ℝ U) (F : VectorField) :
    (∃ G : VectorField, ContDiffOn ℝ 2 G E ∧ EqOn (curl G) F E) ↔
      CompatibleCurlRows E F := by
  constructor
  · rintro ⟨G, hG, hcurl⟩
    refine ⟨fun i => gradient (fun x => G x i), ?_, ?_, ?_⟩
    · intro i
      exact contDiffOn_gradient hE (contDiffOn_map_coordinate hG i)
    · intro i
      exact curl_gradient_eq_zero hE (contDiffOn_map_coordinate hG i)
    · exact hcurl
  · rintro ⟨M, hM, hz, hskew⟩
    have hex (i : Fin 3) : ∃ f : Euclidean 3 → ℝ,
        ContDiffOn ℝ 2 f E ∧ EqOn (gradient f) (M i) E :=
      scalarPotential_c2_of_equivalent_convex e hU hE hc (hM i) (hz i)
    choose f hf hgrad using hex
    let G : VectorField := fun x => coordEquivEuclidean 3 (fun i => f i x)
    have hG : ContDiffOn ℝ 2 G E := by
      apply contDiffOn_vector_of_coordinates
      intro i
      exact hf i
    refine ⟨G, hG, ?_⟩
    intro x hx
    have hp (i j : Fin 3) : coordinatePartial (f i) x j = M i x j := by
      exact congrArg (fun v : Euclidean 3 => v j) (hgrad i hx)
    calc
      curl G x = curlMatrixSkew M x := by
        simp only [curl, G, coordEquivEuclidean_apply_coordinate, curlMatrixSkew, hp]
      _ = F x := hskew hx

/-- One analytic matrix-completion assertion, on exactly the contract's
domains. No estimate or extra boundary condition is inserted. -/
def CurlMatrixCompletion : Prop :=
  ∀ (U E : Set (Euclidean 3)) (_e : C2DomainEquivalence U E) (F : VectorField),
    IsOpen U → IsOpen E → Convex ℝ U → ContDiffOn ℝ 1 F E →
      EqOn (divergence F) 0 E → CompatibleCurlRows E F

theorem pma10_43_contract_iff_curlMatrixCompletion :
    pma10_43_contract ↔ CurlMatrixCompletion := by
  constructor
  · intro h U E e F hU hE hc hF hz
    exact (c2_vectorPotential_iff_compatibleCurlRows e hU hE hc F).mp
      (h.2.2.2 U E e F hU hE hc hF hz)
  · intro h
    refine ⟨pma10_43_forward.1, pma10_43_forward.2, pma10_43_scalar_converse, ?_⟩
    intro U E e F hU hE hc hF hz
    exact (c2_vectorPotential_iff_compatibleCurlRows e hU hE hc F).mpr
      (h U E e F hU hE hc hF hz)



/-- Half the cross-product matrix: its skew differences are exactly the datum. -/
def canonicalSkewRows (F : VectorField) (i : Fin 3) : VectorField := fun x =>
  ![coordEquivEuclidean 3 ![0, -F x 2 / 2, F x 1 / 2],
    coordEquivEuclidean 3 ![F x 2 / 2, 0, -F x 0 / 2],
    coordEquivEuclidean 3 ![-F x 1 / 2, F x 0 / 2, 0]] i

/-- Symmetry is required only on the original domain. -/
def SymmetricRowsOn (E : Set (Euclidean 3)) (S : Fin 3 → VectorField) : Prop :=
  ∀ x ∈ E, ∀ i j, S i x j = S j x i

lemma curlMatrixSkew_canonical (F : VectorField) :
    curlMatrixSkew (canonicalSkewRows F) = F := by
  funext x
  ext i
  fin_cases i <;> simp [curlMatrixSkew, canonicalSkewRows] <;> ring

lemma contDiffOn_canonicalSkewRows {E : Set (Euclidean 3)} {F : VectorField}
    (hF : ContDiffOn ℝ 1 F E) (i : Fin 3) :
    ContDiffOn ℝ 1 (canonicalSkewRows F i) E := by
  have h0 := contDiffOn_map_coordinate hF (0 : Fin 3)
  have h1 := contDiffOn_map_coordinate hF (1 : Fin 3)
  have h2 := contDiffOn_map_coordinate hF (2 : Fin 3)
  apply contDiffOn_vector_of_coordinates
  intro j
  fin_cases i <;> fin_cases j
  · exact contDiffOn_const
  · exact h2.neg.div_const 2
  · exact h1.div_const 2
  · exact h2.div_const 2
  · exact contDiffOn_const
  · exact h0.neg.div_const 2
  · exact h1.neg.div_const 2
  · exact h0.div_const 2
  · exact contDiffOn_const

/-- A symmetric correction makes all three canonical rows integrable. -/
def SymmetricCurlCorrection (E : Set (Euclidean 3)) (F : VectorField) : Prop :=
  ∃ S : Fin 3 → VectorField,
    (∀ i, ContDiffOn ℝ 1 (S i) E) ∧ SymmetricRowsOn E S ∧
      ∀ i, EqOn (curl (canonicalSkewRows F i + S i)) 0 E

theorem compatibleCurlRows_iff_symmetricCurlCorrection
    {E : Set (Euclidean 3)} {F : VectorField} (hF : ContDiffOn ℝ 1 F E) :
    CompatibleCurlRows E F ↔ SymmetricCurlCorrection E F := by
  constructor
  · rintro ⟨M, hM, hz, hskew⟩
    let S : Fin 3 → VectorField := fun i => M i - canonicalSkewRows F i
    refine ⟨S, fun i => (hM i).sub (contDiffOn_canonicalSkewRows hF i), ?_, ?_⟩
    · intro x hx i j
      have h0 := congrArg (fun v : Euclidean 3 => v 0) (hskew hx)
      have h1 := congrArg (fun v : Euclidean 3 => v 1) (hskew hx)
      have h2 := congrArg (fun v : Euclidean 3 => v 2) (hskew hx)
      simp [curlMatrixSkew] at h0 h1 h2
      fin_cases i <;> fin_cases j <;>
        simp [S, canonicalSkewRows] <;> linarith
    · intro i
      have he : canonicalSkewRows F i + S i = M i := by
        dsimp [S]
        abel
      rw [he]
      exact hz i
  · rintro ⟨S, hS, hsym, hz⟩
    let M : Fin 3 → VectorField := fun i => canonicalSkewRows F i + S i
    refine ⟨M, fun i => (contDiffOn_canonicalSkewRows hF i).add (hS i), hz, ?_⟩
    intro x hx
    have h01 := hsym x hx 0 1
    have h02 := hsym x hx 0 2
    have h12 := hsym x hx 1 2
    ext i
    fin_cases i <;> simp [M, curlMatrixSkew, canonicalSkewRows] <;> linarith

/-- Universal symmetric completion, with exactly the printed domain assumptions. -/
def SymmetricCurlCompletion : Prop :=
  ∀ (U E : Set (Euclidean 3)) (_e : C2DomainEquivalence U E) (F : VectorField),
    IsOpen U → IsOpen E → Convex ℝ U → ContDiffOn ℝ 1 F E →
      EqOn (divergence F) 0 E → SymmetricCurlCorrection E F

theorem pma10_43_contract_iff_symmetricCurlCompletion :
    pma10_43_contract ↔ SymmetricCurlCompletion := by
  rw [pma10_43_contract_iff_curlMatrixCompletion]
  constructor
  · intro h U E e F hU hE hc hF hz
    exact (compatibleCurlRows_iff_symmetricCurlCorrection hF).mp
      (h U E e F hU hE hc hF hz)
  · intro h U E e F hU hE hc hF hz
    exact (compatibleCurlRows_iff_symmetricCurlCorrection hF).mpr
      (h U E e F hU hE hc hF hz)



/-- The coordinate derivative of a vector field, retaining every component. -/
def vectorCoordinatePartial (F : VectorField) (i : Fin 3) : VectorField := fun x =>
  coordEquivEuclidean 3 (fun j => coordinatePartial (fun y => F y j) x i)

/-- Closedness of the datum turns the canonical row curl into its negative
half coordinate derivative. Only first derivatives are used. -/
lemma curl_canonicalSkewRows_of_divergence_zero {E : Set (Euclidean 3)}
    (hE : IsOpen E) {F : VectorField} (hF : ContDiffOn ℝ 1 F E)
    (hz : EqOn (divergence F) 0 E) (i : Fin 3) :
    EqOn (curl (canonicalSkewRows F i))
      (fun x => -(1 / 2 : ℝ) • vectorCoordinatePartial F i x) E := by
  intro x hx
  have hd (j : Fin 3) : DifferentiableAt ℝ (fun y => F y j) x :=
    (contDiffOn_map_coordinate hF j).differentiableOn_one.differentiableAt
      (hE.mem_nhds hx)
  have hp (j k : Fin 3) :
      coordinatePartial (fun y => F y j / 2) x k =
        coordinatePartial (fun y => F y j) x k / 2 := by
    simpa only [div_eq_mul_inv] using coordinatePartial_mul_const (hd j) (2 : ℝ)⁻¹ k
  have hn (j k : Fin 3) :
      coordinatePartial (fun y => -F y j / 2) x k =
        -coordinatePartial (fun y => F y j) x k / 2 := by
    simpa only [neg_mul, mul_neg, div_eq_mul_inv, mul_comm] using
      coordinatePartial_const_mul (hd j) (-(2 : ℝ)⁻¹) k
  have hdiv := hz hx
  change ∑ j : Fin 3, coordinatePartial (fun y => F y j) x j = 0 at hdiv
  simp only [Fin.sum_univ_three] at hdiv
  ext j
  fin_cases i <;> fin_cases j <;>
    simp [curl, canonicalSkewRows, vectorCoordinatePartial, hp, hn] <;> linarith

lemma curl_canonical_add_eq_zero_iff {E : Set (Euclidean 3)}
    (hE : IsOpen E) {F S : VectorField} (hF : ContDiffOn ℝ 1 F E)
    (hz : EqOn (divergence F) 0 E) (hS : ContDiffOn ℝ 1 S E) (i : Fin 3) :
    EqOn (curl (canonicalSkewRows F i + S)) 0 E ↔
      EqOn (curl S) (fun x => (1 / 2 : ℝ) • vectorCoordinatePartial F i x) E := by
  have hK := contDiffOn_canonicalSkewRows hF i
  have hc := curl_canonicalSkewRows_of_divergence_zero hE hF hz i
  constructor
  · intro h x hx
    have hcx : curl (canonicalSkewRows F i) x =
        -(1 / 2 : ℝ) • vectorCoordinatePartial F i x := hc hx
    have hsum := h hx
    rw [curl_add_eqOn hE hK hS hx] at hsum
    change curl (canonicalSkewRows F i) x + curl S x = 0 at hsum
    rw [hcx] at hsum
    have he := congrArg (fun v : Euclidean 3 =>
      (1 / 2 : ℝ) • vectorCoordinatePartial F i x + v) hsum
    simpa only [neg_smul, ← add_assoc, add_neg_cancel, zero_add, add_zero] using he
  · intro h x hx
    have hcx : curl (canonicalSkewRows F i) x =
        -(1 / 2 : ℝ) • vectorCoordinatePartial F i x := hc hx
    have hsx : curl S x = (1 / 2 : ℝ) • vectorCoordinatePartial F i x := h hx
    rw [curl_add_eqOn hE hK hS hx]
    change curl (canonicalSkewRows F i) x + curl S x = 0
    rw [hcx, hsx]
    simp only [neg_smul, neg_add_cancel]


/-- Six symmetric C1 unknown entries solve all nine first-order equations
simultaneously. Derivatives of the input appear only to first order. -/
def SymmetricCurlSystem (E : Set (Euclidean 3)) (F : VectorField) : Prop :=
  ∃ S : Fin 3 → VectorField,
    (∀ i, ContDiffOn ℝ 1 (S i) E) ∧ SymmetricRowsOn E S ∧
      ∀ i, EqOn (curl (S i))
        (fun x => (1 / 2 : ℝ) • vectorCoordinatePartial F i x) E

theorem symmetricCurlCorrection_iff_system {E : Set (Euclidean 3)}
    (hE : IsOpen E) {F : VectorField} (hF : ContDiffOn ℝ 1 F E)
    (hz : EqOn (divergence F) 0 E) :
    SymmetricCurlCorrection E F ↔ SymmetricCurlSystem E F := by
  constructor
  · rintro ⟨S, hS, hsym, h⟩
    exact ⟨S, hS, hsym, fun i =>
      (curl_canonical_add_eq_zero_iff hE hF hz (hS i) i).mp (h i)⟩
  · rintro ⟨S, hS, hsym, h⟩
    exact ⟨S, hS, hsym, fun i =>
      (curl_canonical_add_eq_zero_iff hE hF hz (hS i) i).mpr (h i)⟩

/-- The sole remaining analytic assertion in the exact qualitative reduction.
This definition asserts no existence theorem and imposes no global norm bound. -/
def SymmetricDerivativeLifting : Prop :=
  ∀ (U E : Set (Euclidean 3)) (_e : C2DomainEquivalence U E) (F : VectorField),
    IsOpen U → IsOpen E → Convex ℝ U → ContDiffOn ℝ 1 F E →
      EqOn (divergence F) 0 E → SymmetricCurlSystem E F

/-- Exact equivalence with the complete, unchanged printed contract.
The remaining analytic assertion is not proved by this equivalence. -/
theorem pma10_43_contract_iff_symmetricDerivativeLifting :
    pma10_43_contract ↔ SymmetricDerivativeLifting := by
  rw [pma10_43_contract_iff_symmetricCurlCompletion]
  constructor
  · intro h U E e F hU hE hc hF hz
    exact (symmetricCurlCorrection_iff_system hE hF hz).mp
      (h U E e F hU hE hc hF hz)
  · intro h U E e F hU hE hc hF hz
    exact (symmetricCurlCorrection_iff_system hE hF hz).mpr
      (h U E e F hU hE hc hF hz)

end Rudin.PMA.Chapter10



namespace Rudin.PMA.Chapter10.ProofAttack

open Set

section Quantitative

variable {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]

/-- The quotient norm measures the infimum over every representative with the same image. -/
def allGaugeCost (T : X →L[ℝ] Y) (x : X) : ℝ :=
  ‖(Submodule.Quotient.mk x : X ⧸ T.ker)‖

lemma allGaugeCost_le_norm (T : X →L[ℝ] Y) (x : X) :
    allGaugeCost T x ≤ ‖x‖ :=
  Submodule.Quotient.norm_mk_le T.ker x

lemma allGaugeCost_eq_of_image_eq (T : X →L[ℝ] Y) {x z : X} (h : T x = T z) :
    allGaugeCost T x = allGaugeCost T z := by
  have he : (Submodule.Quotient.mk x : X ⧸ T.ker) = Submodule.Quotient.mk z := by
    rw [Submodule.Quotient.eq]
    change T (x - z) = 0
    rw [map_sub, h, sub_self]
  exact congrArg norm he

/-- An arbitrary positive slack suffices; attainment of the infimum is not required. -/
lemma exists_same_image_norm_lt_cost_add (T : X →L[ℝ] Y) (x : X) {ε : ℝ}
    (hε : 0 < ε) :
    ∃ z, T z = T x ∧ ‖z‖ < allGaugeCost T x + ε := by
  obtain ⟨z, hz, hn⟩ := Submodule.Quotient.norm_mk_lt
    (Submodule.Quotient.mk x : X ⧸ T.ker) hε
  refine ⟨z, ?_, hn⟩
  have hk : z - x ∈ T.ker := (Submodule.Quotient.eq T.ker).mp hz
  change T (z - x) = 0 at hk
  simpa only [map_sub, sub_eq_zero] using hk

/-- The quotient norm is exactly the infimum over all representatives, not a chosen gauge. -/
lemma allGaugeCost_eq_sInf (T : X →L[ℝ] Y) (x : X) :
    allGaugeCost T x = sInf {r : ℝ | ∃ z : X, T z = T x ∧ ‖z‖ = r} := by
  let s : Set ℝ := {r : ℝ | ∃ z : X, T z = T x ∧ ‖z‖ = r}
  have hs : s.Nonempty := ⟨‖x‖, x, rfl, rfl⟩
  have hb : BddBelow s := by
    refine ⟨0, ?_⟩
    rintro r ⟨z, hz, rfl⟩
    exact norm_nonneg z
  change allGaugeCost T x = sInf s
  apply le_antisymm
  · apply le_csInf hs
    rintro r ⟨z, hz, rfl⟩
    rw [← allGaugeCost_eq_of_image_eq T hz]
    exact allGaugeCost_le_norm T z
  · apply le_of_forall_pos_le_add
    intro ε hε
    obtain ⟨z, hz, hn⟩ := exists_same_image_norm_lt_cost_add T x hε
    exact (csInf_le hb (show ‖z‖ ∈ s from ⟨z, hz, rfl⟩)).trans hn.le

/-- All-gauge infimum bounds give actual representatives after enlarging the constant. -/
theorem allGaugeCost_bound_iff_representative_bound (T : X →L[ℝ] Y) :
    (∃ C > 0, ∀ x, allGaugeCost T x ≤ C * ‖T x‖) ↔
      ∃ C > 0, ∀ x, ∃ z, T z = T x ∧ ‖z‖ ≤ C * ‖T x‖ := by
  constructor
  · rintro ⟨C, hC, hb⟩
    refine ⟨C + 1, by linarith, ?_⟩
    intro x
    by_cases hx : T x = 0
    · exact ⟨0, by simpa using hx.symm, by simp [hx]⟩
    · obtain ⟨z, hz, hn⟩ := exists_same_image_norm_lt_cost_add T x (norm_pos_iff.mpr hx)
      refine ⟨z, hz, ?_⟩
      have hb' := hb x
      nlinarith
  · rintro ⟨C, hC, hb⟩
    refine ⟨C, hC, ?_⟩
    intro x
    obtain ⟨z, hz, hn⟩ := hb x
    rw [← allGaugeCost_eq_of_image_eq T hz]
    exact (allGaugeCost_le_norm T z).trans hn

/-- Completeness of the quotient converts an all-gauge bound and dense range into exact solvability. -/
theorem surjective_of_denseRange_allGaugeCost_bound [CompleteSpace X]
    (T : X →L[ℝ] Y) (hd : DenseRange T)
    (hb : ∃ C > 0, ∀ x, allGaugeCost T x ≤ C * ‖T x‖) :
    Function.Surjective T := by
  obtain ⟨C, hC, hb⟩ := hb
  let : IsClosed (T.ker : Set X) := T.isClosed_ker
  let L : (X ⧸ T.ker) →L[ℝ] Y := T.ker.liftQL T le_rfl
  have ha : AntilipschitzWith ⟨C, hC.le⟩ L := by
    apply AddMonoidHomClass.antilipschitz_of_bound
    intro q
    induction q using Quotient.inductionOn with
    | h x => exact hb x
  have hr : Set.range L = Set.range T := by
    ext y
    constructor
    · rintro ⟨q, rfl⟩
      induction q using Quotient.inductionOn with
      | h x => exact ⟨x, rfl⟩
    · rintro ⟨x, rfl⟩
      exact ⟨Submodule.Quotient.mk x, rfl⟩
  have hc : IsClosed (Set.range T) := hr ▸ ha.isClosed_range L.uniformContinuous
  intro y
  have hy : y ∈ closure (Set.range T) := hd y
  rw [hc.closure_eq] at hy
  exact hy

/-- Banach-space quantitative equivalence, with every kernel direction retained. -/
theorem surjective_iff_denseRange_allGaugeCost_bound [CompleteSpace X] [CompleteSpace Y]
    (T : X →L[ℝ] Y) :
    Function.Surjective T ↔
      DenseRange T ∧ ∃ C > 0, ∀ x, allGaugeCost T x ≤ C * ‖T x‖ := by
  constructor
  · intro hs
    refine ⟨hs.denseRange, ?_⟩
    obtain ⟨C, hC, hb⟩ := T.exists_preimage_norm_le hs
    refine (allGaugeCost_bound_iff_representative_bound T).mpr ⟨C, hC, ?_⟩
    intro x
    exact hb (T x)
  · rintro ⟨hd, hb⟩
    exact surjective_of_denseRange_allGaugeCost_bound T hd hb


/-- A quantitative lift on a dense linear class extends to all data. The map `R` allows
input and output data spaces to differ, for example by restriction to a smaller ball.
No linear or continuous selection of the original representatives is assumed. -/
theorem lifting_extends_from_dense_submodule [CompleteSpace X]
    {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    (T : X →L[ℝ] Z) (R : Y →L[ℝ] Z) (S : Submodule ℝ Y)
    (hd : DenseRange (S.subtype : S →ₗ[ℝ] Y))
    (hb : ∃ C > 0, ∀ y : S, ∃ x : X,
      T x = R (y : Y) ∧ ‖x‖ ≤ C * ‖(y : Y)‖) :
    ∀ y : Y, ∃ x : X, T x = R y := by
  obtain ⟨C, hC, hb⟩ := hb
  let : IsClosed (T.ker : Set X) := T.isClosed_ker
  have hS (y : S) : R (y : Y) ∈ T.range := by
    obtain ⟨x, hx, _⟩ := hb y
    exact ⟨x, hx⟩
  let r : S →ₗ[ℝ] T.range :=
    (R.toLinearMap.comp S.subtype).codRestrict T.range hS
  let f : S →ₗ[ℝ] X ⧸ T.ker :=
    T.toLinearMap.quotKerEquivRange.symm.toLinearMap.comp r
  have hfm (y : S) (x : X) (hx : T x = R (y : Y)) :
      f y = Submodule.Quotient.mk x := by
    change T.toLinearMap.quotKerEquivRange.symm ⟨R (y : Y), hS y⟩ = _
    have he : (⟨R (y : Y), hS y⟩ : T.range) =
        ⟨T x, LinearMap.mem_range_self T.toLinearMap x⟩ := Subtype.ext hx.symm
    rw [he]
    exact T.toLinearMap.quotKerEquivRange_symm_apply_image x _
  have hn (y : S) : ‖f y‖ ≤ C * ‖S.subtype y‖ := by
    obtain ⟨x, hx, hn⟩ := hb y
    rw [hfm y x hx]
    exact (Submodule.Quotient.norm_mk_le T.ker x).trans hn
  let K : Y →L[ℝ] X ⧸ T.ker := f.extendOfNorm S.subtype
  let L : (X ⧸ T.ker) →L[ℝ] Z := T.ker.liftQL T le_rfl
  have hK (y : S) : K (y : Y) = f y :=
    LinearMap.extendOfNorm_eq hd ⟨C, hn⟩ y
  have hLK : (fun y : Y => L (K y)) = R := by
    apply hd.equalizer (L.continuous.comp K.continuous) R.continuous
    funext y
    change L (K (y : Y)) = R (y : Y)
    rw [hK]
    obtain ⟨x, hx, _⟩ := hb y
    rw [hfm y x hx]
    exact hx
  intro y
  obtain ⟨x, hx⟩ := Submodule.Quotient.mk_surjective T.ker (K y)
  refine ⟨x, ?_⟩
  have h := congrFun hLK y
  rw [← hx] at h
  exact h

/-- A bound on a dense linear class gives exact solvability for every datum. -/
theorem surjective_of_dense_submodule_bounded_lifts [CompleteSpace X]
    (T : X →L[ℝ] Y) (S : Submodule ℝ Y)
    (hd : DenseRange (S.subtype : S →ₗ[ℝ] Y))
    (hb : ∃ C > 0, ∀ y : S, ∃ x : X, T x = (y : Y) ∧ ‖x‖ ≤ C * ‖(y : Y)‖) :
    Function.Surjective T :=
  lifting_extends_from_dense_submodule T (ContinuousLinearMap.id ℝ Y) S hd hb

/-- The dense-class version of the Banach all-gauge quantitative equivalence. -/
theorem surjective_iff_dense_submodule_bounded_lifts [CompleteSpace X] [CompleteSpace Y]
    (T : X →L[ℝ] Y) (S : Submodule ℝ Y)
    (hd : DenseRange (S.subtype : S →ₗ[ℝ] Y)) :
    Function.Surjective T ↔
      ∃ C > 0, ∀ y : S, ∃ x : X, T x = (y : Y) ∧ ‖x‖ ≤ C * ‖(y : Y)‖ := by
  constructor
  · intro hs
    obtain ⟨C, hC, hb⟩ := T.exists_preimage_norm_le hs
    exact ⟨C, hC, fun y => hb (y : Y)⟩
  · exact surjective_of_dense_submodule_bounded_lifts T S hd


end Quantitative

end Rudin.PMA.Chapter10.ProofAttack

/-! Audit every declaration owned by this module, including generated ones. -/
run_cmd do
  Rudin.PMA.Audit.checkModuleAxioms `Rudin.Research.PMA1043ProofAttack
    #[`Rudin.PMA.Chapter10.pma10_43_contract_iff_symmetricDerivativeLifting,
      `Rudin.PMA.Chapter10.ProofAttack.lifting_extends_from_dense_submodule]

#print axioms Rudin.PMA.Chapter10.curlMatrixSkew
#print axioms Rudin.PMA.Chapter10.CompatibleCurlRows
#print axioms Rudin.PMA.Chapter10.c2_vectorPotential_iff_compatibleCurlRows
#print axioms Rudin.PMA.Chapter10.CurlMatrixCompletion
#print axioms Rudin.PMA.Chapter10.pma10_43_contract_iff_curlMatrixCompletion
#print axioms Rudin.PMA.Chapter10.canonicalSkewRows
#print axioms Rudin.PMA.Chapter10.SymmetricRowsOn
#print axioms Rudin.PMA.Chapter10.curlMatrixSkew_canonical
#print axioms Rudin.PMA.Chapter10.contDiffOn_canonicalSkewRows
#print axioms Rudin.PMA.Chapter10.SymmetricCurlCorrection
#print axioms Rudin.PMA.Chapter10.compatibleCurlRows_iff_symmetricCurlCorrection
#print axioms Rudin.PMA.Chapter10.SymmetricCurlCompletion
#print axioms Rudin.PMA.Chapter10.pma10_43_contract_iff_symmetricCurlCompletion
#print axioms Rudin.PMA.Chapter10.vectorCoordinatePartial
#print axioms Rudin.PMA.Chapter10.curl_canonicalSkewRows_of_divergence_zero
#print axioms Rudin.PMA.Chapter10.curl_canonical_add_eq_zero_iff
#print axioms Rudin.PMA.Chapter10.SymmetricCurlSystem
#print axioms Rudin.PMA.Chapter10.symmetricCurlCorrection_iff_system
#print axioms Rudin.PMA.Chapter10.SymmetricDerivativeLifting
#print axioms Rudin.PMA.Chapter10.pma10_43_contract_iff_symmetricDerivativeLifting
#print axioms Rudin.PMA.Chapter10.ProofAttack.allGaugeCost
#print axioms Rudin.PMA.Chapter10.ProofAttack.allGaugeCost_le_norm
#print axioms Rudin.PMA.Chapter10.ProofAttack.allGaugeCost_eq_of_image_eq
#print axioms Rudin.PMA.Chapter10.ProofAttack.exists_same_image_norm_lt_cost_add
#print axioms Rudin.PMA.Chapter10.ProofAttack.allGaugeCost_eq_sInf
#print axioms Rudin.PMA.Chapter10.ProofAttack.allGaugeCost_bound_iff_representative_bound
#print axioms Rudin.PMA.Chapter10.ProofAttack.surjective_of_denseRange_allGaugeCost_bound
#print axioms Rudin.PMA.Chapter10.ProofAttack.surjective_iff_denseRange_allGaugeCost_bound
#print axioms Rudin.PMA.Chapter10.ProofAttack.lifting_extends_from_dense_submodule
#print axioms Rudin.PMA.Chapter10.ProofAttack.surjective_of_dense_submodule_bounded_lifts
#print axioms Rudin.PMA.Chapter10.ProofAttack.surjective_iff_dense_submodule_bounded_lifts
