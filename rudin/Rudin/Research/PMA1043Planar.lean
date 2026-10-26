import Rudin.PMA.Chapter10.VectorPotentials

/-!
# Planar divergence and the C² vector-potential endpoint

This standalone research module relates the full-plane divergence equation to
vector potentials for vertical fields on all of Euclidean three-space. It does
not assert solvability or nonsolvability of either equation.
-/

noncomputable section
set_option autoImplicit false
open Set Function
open scoped BigOperators

namespace Rudin.PMA.Chapter10

abbrev PlanarVectorField := Euclidean 2 → Euclidean 2

/-- Projection `(x,y,z) ↦ (x,y)`. -/
def planeProjection : Euclidean 3 →L[ℝ] Euclidean 2 :=
  (coordEquivEuclidean 2).toContinuousLinearMap.comp
    (ContinuousLinearMap.pi fun i : Fin 2 => EuclideanSpace.proj i.castSucc)

/-- Inclusion `(x,y) ↦ (x,y,0)`. -/
def planeInclusion : Euclidean 2 →L[ℝ] Euclidean 3 :=
  (EuclideanSpace.proj (0 : Fin 2)).smulRight (coordinateVector 3 0) +
    (EuclideanSpace.proj (1 : Fin 2)).smulRight (coordinateVector 3 1)

@[simp] lemma planeProjection_apply (x : Euclidean 3) (i : Fin 2) :
    planeProjection x i = x i.castSucc := rfl

@[simp] lemma planeInclusion_apply_zero (x : Euclidean 2) : planeInclusion x 0 = x 0 := by
  simp [planeInclusion, coordinateVector, EuclideanSpace.basisFun_apply]

@[simp] lemma planeInclusion_apply_one (x : Euclidean 2) : planeInclusion x 1 = x 1 := by
  simp [planeInclusion, coordinateVector, EuclideanSpace.basisFun_apply]

@[simp] lemma planeInclusion_apply_two (x : Euclidean 2) : planeInclusion x 2 = 0 := by
  simp [planeInclusion, coordinateVector, EuclideanSpace.basisFun_apply]

@[simp] lemma planeProjection_inclusion (x : Euclidean 2) :
    planeProjection (planeInclusion x) = x := by
  ext i
  fin_cases i <;> simp

@[simp] lemma planeProjection_coordinateVector (i : Fin 2) :
    planeProjection (coordinateVector 3 i.castSucc) = coordinateVector 2 i := by
  ext j
  simp [coordinateVector, EuclideanSpace.basisFun_apply]

@[simp] lemma planeProjection_coordinateVector_two :
    planeProjection (coordinateVector 3 2) = 0 := by
  ext i
  fin_cases i <;> simp [coordinateVector, EuclideanSpace.basisFun_apply]

@[simp] lemma planeInclusion_coordinateVector (i : Fin 2) :
    planeInclusion (coordinateVector 2 i) = coordinateVector 3 i.castSucc := by
  ext j
  fin_cases i <;> fin_cases j <;> simp [coordinateVector, EuclideanSpace.basisFun_apply]

lemma coordinatePartial_planeProjection (f : Euclidean 2 → ℝ)
    (x : Euclidean 3) (i : Fin 2) :
    coordinatePartial (fun y => f (planeProjection y)) x i.castSucc =
      coordinatePartial f (planeProjection x) i := by
  simp only [coordinatePartial, map_add, map_smul, planeProjection_coordinateVector]

@[simp] lemma coordinatePartial_planeProjection_two (f : Euclidean 2 → ℝ)
    (x : Euclidean 3) :
    coordinatePartial (fun y => f (planeProjection y)) x 2 = 0 := by
  simp [coordinatePartial]

lemma coordinatePartial_planeInclusion (f : Euclidean 3 → ℝ)
    (x : Euclidean 2) (i : Fin 2) :
    coordinatePartial (fun y => f (planeInclusion y)) x i =
      coordinatePartial f (planeInclusion x) i.castSucc := by
  simp only [coordinatePartial, map_add, map_smul, planeInclusion_coordinateVector]

lemma coordinatePartial_neg_planar {n : ℕ} (f : Euclidean n → ℝ)
    (x : Euclidean n) (i : Fin n) :
    coordinatePartial (fun y => -f y) x i = -coordinatePartial f x i := by
  simp [coordinatePartial]

/-- Planar divergence in the same Cartesian derivative convention as `divergence`. -/
def planarDivergence (u : PlanarVectorField) : Euclidean 2 → ℝ := fun x =>
  coordinatePartial (fun y => u y 0) x 0 + coordinatePartial (fun y => u y 1) x 1

/-- The vertical field associated to a planar scalar datum. -/
def verticalField (f : Euclidean 2 → ℝ) : VectorField := fun x =>
  coordEquivEuclidean 3 ![0, 0, f (planeProjection x)]

/-- A planar divergence solution gives this three-dimensional curl potential. -/
def planarPotentialLift (u : PlanarVectorField) : VectorField := fun x =>
  coordEquivEuclidean 3 ![-u (planeProjection x) 1, u (planeProjection x) 0, 0]

/-- Restrict and rotate the first two components of any vector potential. -/
def potentialPlanarRestriction (G : VectorField) : PlanarVectorField := fun x =>
  coordEquivEuclidean 2 ![G (planeInclusion x) 1, -G (planeInclusion x) 0]

lemma divergence_verticalField (f : Euclidean 2 → ℝ) : divergence (verticalField f) = 0 := by
  funext x
  simp [divergence, verticalField, Fin.sum_univ_three, coordinatePartial]

lemma curl_planarPotentialLift (u : PlanarVectorField) :
    curl (planarPotentialLift u) = verticalField (planarDivergence u) := by
  funext x
  ext i
  fin_cases i <;>
    simp [curl, planarPotentialLift, verticalField, planarDivergence,
      coordinatePartial, map_add, map_smul,
      show planeProjection (coordinateVector 3 0) = coordinateVector 2 0 from
        planeProjection_coordinateVector 0,
      show planeProjection (coordinateVector 3 1) = coordinateVector 2 1 from
        planeProjection_coordinateVector 1]

lemma planarDivergence_potentialPlanarRestriction (G : VectorField) (x : Euclidean 2) :
    planarDivergence (potentialPlanarRestriction G) x = curl G (planeInclusion x) 2 := by
  simp [planarDivergence, potentialPlanarRestriction, curl,
    coordinatePartial, map_add, map_smul,
    show planeInclusion (coordinateVector 2 0) = coordinateVector 3 0 from
      planeInclusion_coordinateVector 0,
    show planeInclusion (coordinateVector 2 1) = coordinateVector 3 1 from
      planeInclusion_coordinateVector 1, sub_eq_add_neg]

lemma contDiff_verticalField {r : ℕ} {f : Euclidean 2 → ℝ}
    (hf : ContDiff ℝ r f) : ContDiff ℝ r (verticalField f) := by
  unfold verticalField
  apply (coordEquivEuclidean 3).contDiff.comp
  apply contDiff_pi.mpr
  intro i
  fin_cases i
  · exact contDiff_const
  · exact contDiff_const
  · exact hf.comp planeProjection.contDiff

lemma contDiff_planarPotentialLift {r : ℕ} {u : PlanarVectorField}
    (hu : ContDiff ℝ r u) : ContDiff ℝ r (planarPotentialLift u) := by
  unfold planarPotentialLift
  apply (coordEquivEuclidean 3).contDiff.comp
  apply contDiff_pi.mpr
  intro i
  fin_cases i
  · exact (((EuclideanSpace.proj (1 : Fin 2)).contDiff.comp hu).comp
      planeProjection.contDiff).neg
  · exact ((EuclideanSpace.proj (0 : Fin 2)).contDiff.comp hu).comp
      planeProjection.contDiff
  · exact contDiff_const

lemma contDiff_potentialPlanarRestriction {r : ℕ} {G : VectorField}
    (hG : ContDiff ℝ r G) : ContDiff ℝ r (potentialPlanarRestriction G) := by
  unfold potentialPlanarRestriction
  apply (coordEquivEuclidean 2).contDiff.comp
  apply contDiff_pi.mpr
  intro i
  fin_cases i
  · exact ((EuclideanSpace.proj (1 : Fin 3)).contDiff.comp hG).comp
      planeInclusion.contDiff
  · exact (((EuclideanSpace.proj (0 : Fin 3)).contDiff.comp hG).comp
      planeInclusion.contDiff).neg

/-- The planar divergence problem is exactly the vector-potential problem for
vertical fields, with no restriction on the gauge of the three-dimensional
potential. This equivalence is on the full spaces, without boundary conditions. -/
theorem c2_verticalPotential_iff_planarDivergence (f : Euclidean 2 → ℝ) :
    (∃ G : VectorField, ContDiff ℝ 2 G ∧ curl G = verticalField f) ↔
      ∃ u : PlanarVectorField, ContDiff ℝ 2 u ∧ planarDivergence u = f := by
  constructor
  · rintro ⟨G, hG, hcurl⟩
    refine ⟨potentialPlanarRestriction G, contDiff_potentialPlanarRestriction hG, ?_⟩
    funext x
    rw [planarDivergence_potentialPlanarRestriction, hcurl]
    simp [verticalField]
  · rintro ⟨u, hu, hdiv⟩
    refine ⟨planarPotentialLift u, contDiff_planarPotentialLift hu, ?_⟩
    rw [curl_planarPotentialLift, hdiv]

/-- A planar C¹ datum with no C² divergence solution would disprove the exact
printed contract. This theorem is a reduction, and supplies no such datum. -/
theorem pma10_43_contract_implies_planarDivergence (h : pma10_43_contract)
    (f : Euclidean 2 → ℝ) (hf : ContDiff ℝ 1 f) :
    ∃ u : PlanarVectorField, ContDiff ℝ 2 u ∧ planarDivergence u = f := by
  let e : C2DomainEquivalence (univ : Set (Euclidean 3)) univ :=
    { forward := id
      inverse := id
      forward_mapsTo := fun _ _ => mem_univ _
      inverse_mapsTo := fun _ _ => mem_univ _
      left_inverse := fun _ _ => rfl
      right_inverse := fun _ _ => rfl
      forward_c2 := contDiff_id.contDiffOn
      inverse_c2 := contDiff_id.contDiffOn }
  have hz : EqOn (divergence (verticalField f)) 0 univ := by
    rw [divergence_verticalField]
    exact fun _ _ => rfl
  obtain ⟨G, hG, hcurl⟩ := h.2.2.2 univ univ e (verticalField f)
    isOpen_univ isOpen_univ convex_univ (contDiff_verticalField hf).contDiffOn hz
  apply (c2_verticalPotential_iff_planarDivergence f).mp
  exact ⟨G, contDiffOn_univ.mp hG, funext fun x => hcurl (mem_univ x)⟩

/-- A scalar function placed in one planar coordinate. -/
def planarCoordinateField (i : Fin 2) (f : Euclidean 2 → ℝ) : PlanarVectorField :=
  fun x => f x • coordinateVector 2 i

lemma contDiff_planarCoordinateField {r : ℕ} {f : Euclidean 2 → ℝ}
    (hf : ContDiff ℝ r f) (i : Fin 2) : ContDiff ℝ r (planarCoordinateField i f) :=
  hf.smul contDiff_const

lemma planarDivergence_coordinateField (f : Euclidean 2 → ℝ) (i : Fin 2) :
    planarDivergence (planarCoordinateField i f) = fun x => coordinatePartial f x i := by
  funext x
  fin_cases i <;>
    simp [planarDivergence, planarCoordinateField, coordinateVector,
      EuclideanSpace.basisFun_apply, coordinatePartial]

/-- A continuous-data divergence obstruction cannot be lifted to C¹ data by
finding a C¹ coordinate antiderivative: that antiderivative would already give
a C¹ divergence solution for the original datum. No regularity of `g` is needed
for this implication. -/
theorem no_c1_planarDivergence_implies_no_c1_coordinatePrimitive
    {g : Euclidean 2 → ℝ}
    (hg : ¬ ∃ u : PlanarVectorField, ContDiff ℝ 1 u ∧ planarDivergence u = g)
    (f : Euclidean 2 → ℝ) (hf : ContDiff ℝ 1 f) (i : Fin 2) :
    (fun x => coordinatePartial f x i) ≠ g := by
  intro he
  apply hg
  refine ⟨planarCoordinateField i f, contDiff_planarCoordinateField hf i, ?_⟩
  rw [planarDivergence_coordinateField, he]

end Rudin.PMA.Chapter10
