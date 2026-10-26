import Rudin.PMA.Chapter10.OneFormCoordinates
import Rudin.PMA.Chapter10.RadialForm

noncomputable section
set_option autoImplicit false
open Set Function Module
open scoped BigOperators

namespace Rudin.PMA.Chapter10
open Chapter09

abbrev VectorField := Euclidean 3 → Euclidean 3

/-- The one-form associated with the three Cartesian components of a vector field. -/
def vectorOneForm (F : VectorField) : FormField 3 := fun x =>
  ∑ i : Fin 3, F x i • dx i

/-- The cyclic order (dy∧dz,dz∧dx,dx∧dy) fixes the source orientation. -/
def vectorTwoForm (F : VectorField) : FormField 3 := fun x =>
  ∑ i : Fin 3, F x i • radialBasis i

def oneFormVector (ω : FormField 3) : VectorField := fun x =>
  coordEquivEuclidean 3 (fun i => formCoefficient ω {i} x)

def twoFormVector (ω : FormField 3) : VectorField := fun x =>
  coordEquivEuclidean 3
    ![formCoefficient ω {1, 2} x, -formCoefficient ω {0, 2} x,
      formCoefficient ω {0, 1} x]

def gradient (f : Euclidean 3 → ℝ) : VectorField := fun x =>
  coordEquivEuclidean 3 (fun i => coordinatePartial f x i)

def curl (F : VectorField) : VectorField := fun x =>
  coordEquivEuclidean 3
    ![coordinatePartial (fun y => F y 2) x 1 - coordinatePartial (fun y => F y 1) x 2,
      coordinatePartial (fun y => F y 0) x 2 - coordinatePartial (fun y => F y 2) x 0,
      coordinatePartial (fun y => F y 1) x 0 - coordinatePartial (fun y => F y 0) x 1]

def divergence (F : VectorField) : Euclidean 3 → ℝ := fun x =>
  ∑ i : Fin 3, coordinatePartial (fun y => F y i) x i

/-- Source 10.42: the two genuine vector/form correspondences and the Cartesian
partial definitions. Regularity is retained on the original open set. -/
def pma10_42_contract : Prop :=
  (∀ (E : Set (Euclidean 3)), IsOpen E →
    (∀ F : VectorField, ContinuousOn F E →
      IsFormOn E 1 (vectorOneForm F) ∧ IsFormOn E 2 (vectorTwoForm F)) ∧
    (∀ ω : FormField 3, IsFormOn E 1 ω →
      ContinuousOn (oneFormVector ω) E ∧ EqOn (vectorOneForm (oneFormVector ω)) ω E) ∧
    (∀ ω : FormField 3, IsFormOn E 2 ω →
      ContinuousOn (twoFormVector ω) E ∧ EqOn (vectorTwoForm (twoFormVector ω)) ω E) ∧
    (∀ F G : VectorField, EqOn (vectorOneForm F) (vectorOneForm G) E ↔ EqOn F G E) ∧
    (∀ F G : VectorField, EqOn (vectorTwoForm F) (vectorTwoForm G) E ↔ EqOn F G E) ∧
    (∀ f : Euclidean 3 → ℝ, ContDiffOn ℝ 1 f E → ContinuousOn (gradient f) E) ∧
    (∀ F : VectorField, ContDiffOn ℝ 1 F E →
      ContinuousOn (curl F) E ∧ ContinuousOn (divergence F) E)) ∧
  (∀ (f : Euclidean 3 → ℝ) (x : Euclidean 3) (i : Fin 3),
    gradient f x i = coordinatePartial f x i) ∧
  (∀ (F : VectorField) (x : Euclidean 3),
    curl F x = coordEquivEuclidean 3
      ![coordinatePartial (fun y => F y 2) x 1 - coordinatePartial (fun y => F y 1) x 2,
        coordinatePartial (fun y => F y 0) x 2 - coordinatePartial (fun y => F y 2) x 0,
        coordinatePartial (fun y => F y 1) x 0 - coordinatePartial (fun y => F y 0) x 1] ∧
    divergence F x = coordinatePartial (fun y => F y 0) x 0 +
      coordinatePartial (fun y => F y 1) x 1 + coordinatePartial (fun y => F y 2) x 2)

lemma contDiffOn_vector_of_coordinates {r : ℕ} {E : Set (Euclidean 3)} {F : VectorField}
    (hF : ∀ i, ContDiffOn ℝ r (fun x => F x i) E) : ContDiffOn ℝ r F E := by
  have he : (fun x => coordEquivEuclidean 3 (fun i => F x i)) = F := by
    funext x
    ext i
    rfl
  rw [← he]
  exact (coordEquivEuclidean 3).contDiff.comp_contDiffOn (contDiffOn_pi.mpr hF)

lemma continuousOn_vector_of_coordinates {E : Set (Euclidean 3)} {F : VectorField}
    (hF : ∀ i, ContinuousOn (fun x => F x i) E) : ContinuousOn F E :=
  (contDiffOn_vector_of_coordinates (r := 0) (fun i => contDiffOn_zero.mpr (hF i))).continuousOn

lemma isCFormOn_vectorOneForm {r : ℕ} {E : Set (Euclidean 3)} {F : VectorField}
    (hF : ContDiffOn ℝ r F E) : IsCFormOn r E 1 (vectorOneForm F) := by
  apply isCFormOn_sum
  intro i
  apply (isCFormOn_constant E (dx i) ?_).smul_function (contDiffOn_map_coordinate hF i)
  rw [dx_eq_coordinateWedge]
  exact coordinateWedge_mem _

lemma isCFormOn_vectorTwoForm {r : ℕ} {E : Set (Euclidean 3)} {F : VectorField}
    (hF : ContDiffOn ℝ r F E) : IsCFormOn r E 2 (vectorTwoForm F) :=
  isCFormOn_sum fun i =>
    (isCFormOn_constant E (radialBasis i) (radialBasis_mem i)).smul_function
      (contDiffOn_map_coordinate hF i)

lemma isFormOn_vectorOneForm {E : Set (Euclidean 3)} {F : VectorField}
    (hF : ContinuousOn F E) : IsFormOn E 1 (vectorOneForm F) :=
  (isCFormOn_vectorOneForm (r := 0) (contDiffOn_zero.mpr hF)).isFormOn

lemma isFormOn_vectorTwoForm {E : Set (Euclidean 3)} {F : VectorField}
    (hF : ContinuousOn F E) : IsFormOn E 2 (vectorTwoForm F) :=
  (isCFormOn_vectorTwoForm (r := 0) (contDiffOn_zero.mpr hF)).isFormOn

lemma exteriorBasis_pair (i j : Fin 3) (hij : i < j) :
    exteriorBasis 3 {i, j} = dx i * dx j := by
  let S : StandardIndex 3 2 := ⟨{i, j}, Finset.card_pair hij.ne⟩
  let I := Set.powersetCard.ofFinEmbEquiv.symm S
  have hm (a : Fin 2) : I a = i ∨ I a = j := by
    have h := (Set.powersetCard.mem_range_ofFinEmbEquiv_symm_iff_mem S (I a)).mp ⟨a, rfl⟩
    change I a ∈ ({i, j} : Finset (Fin 3)) at h
    simpa only [Finset.mem_insert, Finset.mem_singleton] using h
  have h01 : I 0 < I 1 := I.strictMono (by decide)
  have hi : I 0 = i := by
    rcases hm 0 with h | h
    · exact h
    rcases hm 1 with h' | h'
    · rw [h, h'] at h01
      exact False.elim (not_lt_of_ge hij.le h01)
    · rw [h, h'] at h01
      exact False.elim (lt_irrefl _ h01)
  have hj : I 1 = j := by
    rcases hm 1 with h | h
    · rw [hi, h] at h01
      exact False.elim (lt_irrefl _ h01)
    · exact h
  have he : (I : Fin 2 → Fin 3) = ![i, j] := by
    funext a
    fin_cases a
    · exact hi
    · exact hj
  change standardWedge S = _
  rw [standardWedge_eq_coordinateWedge, show (Set.powersetCard.ofFinEmbEquiv.symm S : Fin 2 → Fin 3) = ![i,j] from he]
  simp [coordinateWedge, dx, ExteriorAlgebra.ιMulti_succ_apply,
    Matrix.vecTail, Function.comp_def]

lemma radialBasis_eq_exteriorBasis :
    radialBasis = ![exteriorBasis 3 {1, 2}, -exteriorBasis 3 {0, 2}, exteriorBasis 3 {0, 1}] := by
  funext i
  fin_cases i
  · exact (exteriorBasis_pair 1 2 (by decide)).symm
  · change dx (2 : Fin 3) * dx 0 = -exteriorBasis 3 {0, 2}
    rw [exteriorBasis_pair 0 2 (by decide), dx_mul_swap]
  · exact (exteriorBasis_pair 0 1 (by decide)).symm

lemma oneFormVector_vectorOneForm (F : VectorField) : oneFormVector (vectorOneForm F) = F := by
  funext x
  ext i
  simp [oneFormVector, vectorOneForm, formCoefficient, ← exteriorBasis_singleton,
    map_sum, map_smul, Basis.repr_self, Finsupp.single_apply, eq_comm]

lemma twoFormVector_vectorTwoForm (F : VectorField) : twoFormVector (vectorTwoForm F) = F := by
  have h01 : ({0, 1} : Finset (Fin 3)) ≠ {0, 2} := by decide
  have h02 : ({0, 1} : Finset (Fin 3)) ≠ {1, 2} := by decide
  have h12 : ({0, 2} : Finset (Fin 3)) ≠ {1, 2} := by decide
  funext x
  ext i
  fin_cases i <;>
    simp [twoFormVector, vectorTwoForm, radialBasis_eq_exteriorBasis,
      Fin.sum_univ_three, formCoefficient, map_sum, map_smul, Basis.repr_self,
      Finsupp.single_apply, h01, h01.symm, h02, h02.symm, h12, h12.symm]

lemma vectorOneForm_oneFormVector {E : Set (Euclidean 3)} {ω : FormField 3}
    (hω : IsFormOn E 1 ω) : EqOn (vectorOneForm (oneFormVector ω)) ω E := by
  intro x hx
  simpa only [vectorOneForm, oneFormVector, coordEquivEuclidean_apply_coordinate]
    using (one_form_expansion hω hx).symm

lemma vectorTwoForm_twoFormVector {E : Set (Euclidean 3)} {ω : FormField 3}
    (hω : IsFormOn E 2 ω) : EqOn (vectorTwoForm (twoFormVector ω)) ω E := by
  classical
  intro x hx
  apply (exteriorBasis 3).repr.injective
  ext S
  have hc : ∀ T : Finset (Fin 3), T.card = 2 →
      T = {0, 1} ∨ T = {0, 2} ∨ T = {1, 2} := by decide
  have h01 : ({0, 1} : Finset (Fin 3)) ≠ {0, 2} := by decide
  have h02 : ({0, 1} : Finset (Fin 3)) ≠ {1, 2} := by decide
  have h12 : ({0, 2} : Finset (Fin 3)) ≠ {1, 2} := by decide
  by_cases hS : S.card = 2
  · rcases hc S hS with rfl | rfl | rfl <;>
      simp [vectorTwoForm, twoFormVector, radialBasis_eq_exteriorBasis,
        Fin.sum_univ_three, formCoefficient, map_sum, map_smul, Basis.repr_self,
        Finsupp.single_apply, h01, h01.symm, h02, h02.symm, h12, h12.symm]
  · have h01 : ({0, 1} : Finset (Fin 3)) ≠ S := by intro h; apply hS; rw [← h]; decide
    have h02 : ({0, 2} : Finset (Fin 3)) ≠ S := by intro h; apply hS; rw [← h]; decide
    have h12 : ({1, 2} : Finset (Fin 3)) ≠ S := by intro h; apply hS; rw [← h]; decide
    rw [exteriorBasis_repr_eq_zero_of_degree (hω.1 x hx) S hS]
    simp [vectorTwoForm, twoFormVector, radialBasis_eq_exteriorBasis,
      Fin.sum_univ_three, map_sum, map_smul, Basis.repr_self,
      Finsupp.single_apply, h01, h02, h12]

lemma contDiffOn_oneFormVector {r : ℕ} {E : Set (Euclidean 3)} {ω : FormField 3}
    (hω : IsCFormOn r E 1 ω) : ContDiffOn ℝ r (oneFormVector ω) E := by
  apply contDiffOn_vector_of_coordinates
  intro i
  exact hω.2 {i}

lemma contDiffOn_twoFormVector {r : ℕ} {E : Set (Euclidean 3)} {ω : FormField 3}
    (hω : IsCFormOn r E 2 ω) : ContDiffOn ℝ r (twoFormVector ω) E := by
  apply contDiffOn_vector_of_coordinates
  intro i
  fin_cases i
  · exact hω.2 {1, 2}
  · exact (hω.2 {0, 2}).neg
  · exact hω.2 {0, 1}

lemma continuousOn_oneFormVector {E : Set (Euclidean 3)} {ω : FormField 3}
    (hω : IsFormOn E 1 ω) : ContinuousOn (oneFormVector ω) E :=
  (contDiffOn_oneFormVector (r := 0) ⟨hω.1, fun S => contDiffOn_zero.mpr (hω.2 S)⟩).continuousOn

lemma continuousOn_twoFormVector {E : Set (Euclidean 3)} {ω : FormField 3}
    (hω : IsFormOn E 2 ω) : ContinuousOn (twoFormVector ω) E :=
  (contDiffOn_twoFormVector (r := 0) ⟨hω.1, fun S => contDiffOn_zero.mpr (hω.2 S)⟩).continuousOn

lemma vectorOneForm_eqOn_iff {E : Set (Euclidean 3)} (F G : VectorField) :
    EqOn (vectorOneForm F) (vectorOneForm G) E ↔ EqOn F G E := by
  constructor
  · intro h x hx
    have he := congrArg (fun a : CotangentExterior 3 =>
      coordEquivEuclidean 3 (fun i => (exteriorBasis 3).repr a {i})) (h hx)
    change oneFormVector (vectorOneForm F) x = oneFormVector (vectorOneForm G) x at he
    simpa only [oneFormVector_vectorOneForm] using he
  · intro h x hx
    simp only [vectorOneForm, h hx]

lemma vectorTwoForm_eqOn_iff {E : Set (Euclidean 3)} (F G : VectorField) :
    EqOn (vectorTwoForm F) (vectorTwoForm G) E ↔ EqOn F G E := by
  constructor
  · intro h x hx
    have he := congrArg (fun a : CotangentExterior 3 => coordEquivEuclidean 3
      ![(exteriorBasis 3).repr a {1, 2}, -(exteriorBasis 3).repr a {0, 2},
        (exteriorBasis 3).repr a {0, 1}]) (h hx)
    change twoFormVector (vectorTwoForm F) x = twoFormVector (vectorTwoForm G) x at he
    simpa only [twoFormVector_vectorTwoForm] using he
  · intro h x hx
    simp only [vectorTwoForm, h hx]

lemma contDiffOn_gradient {r : ℕ} {E : Set (Euclidean 3)} (hE : IsOpen E)
    {f : Euclidean 3 → ℝ} (hf : ContDiffOn ℝ (r + 1) f E) :
    ContDiffOn ℝ r (gradient f) E :=
  contDiffOn_vector_of_coordinates (fun i => contDiffOn_coordinatePartial hE hf i)

lemma contDiffOn_curl {r : ℕ} {E : Set (Euclidean 3)} (hE : IsOpen E)
    {F : VectorField} (hF : ContDiffOn ℝ (r + 1) F E) : ContDiffOn ℝ r (curl F) E := by
  have hc (i j : Fin 3) : ContDiffOn ℝ r (fun x => coordinatePartial (fun y => F y j) x i) E :=
    contDiffOn_coordinatePartial hE (contDiffOn_map_coordinate hF j) i
  apply contDiffOn_vector_of_coordinates
  intro i
  fin_cases i
  · exact (hc 1 2).sub (hc 2 1)
  · exact (hc 2 0).sub (hc 0 2)
  · exact (hc 0 1).sub (hc 1 0)

lemma contDiffOn_divergence {r : ℕ} {E : Set (Euclidean 3)} (hE : IsOpen E)
    {F : VectorField} (hF : ContDiffOn ℝ (r + 1) F E) : ContDiffOn ℝ r (divergence F) E :=
  ContDiffOn.sum fun i _ => contDiffOn_coordinatePartial hE (contDiffOn_map_coordinate hF i) i

lemma isCFormOn_vectorOneForm_iff {r : ℕ} {E : Set (Euclidean 3)} (F : VectorField) :
    IsCFormOn r E 1 (vectorOneForm F) ↔ ContDiffOn ℝ r F E := by
  constructor
  · intro h
    simpa only [oneFormVector_vectorOneForm] using contDiffOn_oneFormVector h
  · exact isCFormOn_vectorOneForm

lemma isCFormOn_vectorTwoForm_iff {r : ℕ} {E : Set (Euclidean 3)} (F : VectorField) :
    IsCFormOn r E 2 (vectorTwoForm F) ↔ ContDiffOn ℝ r F E := by
  constructor
  · intro h
    simpa only [twoFormVector_vectorTwoForm] using contDiffOn_twoFormVector h
  · exact isCFormOn_vectorTwoForm

theorem pma10_42 : pma10_42_contract := by
  refine ⟨?_, fun _ _ _ => rfl, ?_⟩
  · intro E hE
    refine ⟨fun _ hF => ⟨isFormOn_vectorOneForm hF, isFormOn_vectorTwoForm hF⟩,
      fun _ hω => ⟨continuousOn_oneFormVector hω, vectorOneForm_oneFormVector hω⟩,
      fun _ hω => ⟨continuousOn_twoFormVector hω, vectorTwoForm_twoFormVector hω⟩,
      vectorOneForm_eqOn_iff, vectorTwoForm_eqOn_iff,
      fun _ hf => (contDiffOn_gradient (r := 0) hE hf).continuousOn,
      fun _ hF => ⟨(contDiffOn_curl (r := 0) hE hF).continuousOn,
        (contDiffOn_divergence (r := 0) hE hF).continuousOn⟩⟩
  · intro F x
    exact ⟨rfl, by simp only [divergence, Fin.sum_univ_three, add_assoc]⟩

end Rudin.PMA.Chapter10
