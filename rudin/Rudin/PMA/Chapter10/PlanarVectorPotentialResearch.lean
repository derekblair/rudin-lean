import Rudin.PMA.Chapter10.VectorPotentialGaugeResearch

/-!
# The planar divergence reduction for PMA 10.43

On the whole spaces, a vertical field `(0,0,h(x,y))` has a C² vector
potential exactly when `h` is the divergence of a C² planar field.
The necessary direction restricts an arbitrary potential to `z = 0`; it
does not impose any gauge condition or assume independence of `z`.
These are reduction lemmas, not a construction of a counterexample.
-/

noncomputable section
set_option autoImplicit false
open Set Function

namespace Rudin.PMA.Chapter10.PlanarResearch

abbrev PlanarField := Euclidean 2 → Euclidean 2

def planeEmbed (p : Euclidean 2) : Euclidean 3 :=
  coordEquivEuclidean 3 ![p 0, p 1, 0]

def planeProject (x : Euclidean 3) : Euclidean 2 :=
  coordEquivEuclidean 2 ![x 0, x 1]

def verticalLift (h : Euclidean 2 → ℝ) : VectorField := fun x =>
  coordEquivEuclidean 3 ![0, 0, h (planeProject x)]

def planarDivergence (V : PlanarField) (p : Euclidean 2) : ℝ :=
  coordinatePartial (fun q => V q 0) p 0 + coordinatePartial (fun q => V q 1) p 1

def restrictPotential (G : VectorField) : PlanarField := fun p =>
  coordEquivEuclidean 2 ![G (planeEmbed p) 1, -G (planeEmbed p) 0]

def liftPotential (V : PlanarField) : VectorField := fun x =>
  coordEquivEuclidean 3 ![-V (planeProject x) 1, V (planeProject x) 0, 0]

@[simp] lemma planeProject_planeEmbed (p : Euclidean 2) :
    planeProject (planeEmbed p) = p := by
  ext i
  fin_cases i <;> simp [planeProject, planeEmbed]

lemma contDiff_planeEmbed {r : ℕ} : ContDiff ℝ r planeEmbed := by
  apply (contDiff_piLp 2).mpr
  intro i
  fin_cases i
  · exact (EuclideanSpace.proj (0 : Fin 2) : Euclidean 2 →L[ℝ] ℝ).contDiff
  · exact (EuclideanSpace.proj (1 : Fin 2) : Euclidean 2 →L[ℝ] ℝ).contDiff
  · exact contDiff_const

lemma contDiff_planeProject {r : ℕ} : ContDiff ℝ r planeProject := by
  apply (contDiff_piLp 2).mpr
  intro i
  fin_cases i
  · exact (EuclideanSpace.proj (0 : Fin 3) : Euclidean 3 →L[ℝ] ℝ).contDiff
  · exact (EuclideanSpace.proj (1 : Fin 3) : Euclidean 3 →L[ℝ] ℝ).contDiff

lemma contDiff_verticalLift {r : ℕ} {h : Euclidean 2 → ℝ}
    (hh : ContDiff ℝ r h) : ContDiff ℝ r (verticalLift h) := by
  apply (contDiff_piLp 2).mpr
  intro i
  fin_cases i
  · exact contDiff_const
  · exact contDiff_const
  · exact hh.comp contDiff_planeProject

lemma contDiff_restrictPotential {r : ℕ} {G : VectorField}
    (hG : ContDiff ℝ r G) : ContDiff ℝ r (restrictPotential G) := by
  apply (contDiff_piLp 2).mpr
  intro i
  fin_cases i
  · exact ((EuclideanSpace.proj (1 : Fin 3) : Euclidean 3 →L[ℝ] ℝ).contDiff.comp hG).comp
      contDiff_planeEmbed
  · exact (((EuclideanSpace.proj (0 : Fin 3) : Euclidean 3 →L[ℝ] ℝ).contDiff.comp hG).comp
      contDiff_planeEmbed).neg

lemma contDiff_liftPotential {r : ℕ} {V : PlanarField}
    (hV : ContDiff ℝ r V) : ContDiff ℝ r (liftPotential V) := by
  apply (contDiff_piLp 2).mpr
  intro i
  fin_cases i
  · exact (((EuclideanSpace.proj (1 : Fin 2) : Euclidean 2 →L[ℝ] ℝ).contDiff.comp hV).comp
      contDiff_planeProject).neg
  · exact ((EuclideanSpace.proj (0 : Fin 2) : Euclidean 2 →L[ℝ] ℝ).contDiff.comp hV).comp
      contDiff_planeProject
  · exact contDiff_const

lemma coordinatePartial_neg {n : ℕ} (f : Euclidean n → ℝ)
    (p : Euclidean n) (i : Fin n) :
    coordinatePartial (fun q => -f q) p i = -coordinatePartial f p i := by
  exact deriv.neg (f := fun t : ℝ => f (p + t • coordinateVector n i)) (x := 0)

lemma coordinatePartial_planeEmbed (f : Euclidean 3 → ℝ)
    (p : Euclidean 2) (i : Fin 2) :
    coordinatePartial (fun q => f (planeEmbed q)) p i =
      coordinatePartial f (planeEmbed p) (Fin.castLE (by decide) i) := by
  unfold coordinatePartial
  apply congrArg (fun g : ℝ → ℝ => deriv g 0)
  funext t
  apply congrArg f
  ext j
  fin_cases i <;> fin_cases j <;>
    simp [planeEmbed, coordinateVector, EuclideanSpace.basisFun_apply]

lemma coordinatePartial_planeProject (f : Euclidean 2 → ℝ)
    (x : Euclidean 3) (i : Fin 2) :
    coordinatePartial (fun y => f (planeProject y)) x (Fin.castLE (by decide) i) =
      coordinatePartial f (planeProject x) i := by
  unfold coordinatePartial
  apply congrArg (fun g : ℝ → ℝ => deriv g 0)
  funext t
  apply congrArg f
  ext j
  fin_cases i <;> fin_cases j <;>
    simp [planeProject, coordinateVector, EuclideanSpace.basisFun_apply]

lemma coordinatePartial_planeProject_z (f : Euclidean 2 → ℝ) (x : Euclidean 3) :
    coordinatePartial (fun y => f (planeProject y)) x 2 = 0 := by
  have he (t : ℝ) : planeProject (x + t • coordinateVector 3 2) = planeProject x := by
    ext i
    fin_cases i <;> simp [planeProject, coordinateVector, EuclideanSpace.basisFun_apply]
  simp only [coordinatePartial, he, deriv_const]

/-- Vertical fields are divergence-free without any smoothness assumption. -/
lemma divergence_verticalLift (h : Euclidean 2 → ℝ) : divergence (verticalLift h) = 0 := by
  funext x
  simp [divergence, Fin.sum_univ_three, verticalLift, coordinatePartial_const,
    coordinatePartial_planeProject_z]

/-- Restricting any potential to the plane reads exactly the third curl component. -/
lemma planarDivergence_restrictPotential (G : VectorField) (p : Euclidean 2) :
    planarDivergence (restrictPotential G) p = curl G (planeEmbed p) 2 := by
  have hx := coordinatePartial_planeEmbed (fun x => G x 1) p 0
  have hy := coordinatePartial_planeEmbed (fun x => G x 0) p 1
  simpa [planarDivergence, restrictPotential, curl, coordinatePartial_neg,
    sub_eq_add_neg] using congrArg₂ (fun a b : ℝ => a - b) hx hy

lemma curl_liftPotential (V : PlanarField) :
    curl (liftPotential V) = verticalLift (planarDivergence V) := by
  funext x
  ext i
  fin_cases i
  · simpa [curl, liftPotential, verticalLift] using
      (neg_eq_zero.mpr (coordinatePartial_planeProject_z (fun p => V p 0) x))
  · simpa [curl, liftPotential, verticalLift, coordinatePartial_neg] using
      (neg_eq_zero.mpr (coordinatePartial_planeProject_z (fun p => V p 1) x))
  · have hx := coordinatePartial_planeProject (fun p => V p 0) x 0
    have hy := coordinatePartial_planeProject (fun p => V p 1) x 1
    simpa [curl, liftPotential, verticalLift, planarDivergence, coordinatePartial_neg]
      using congrArg₂ (fun a b : ℝ => a + b) hx hy

/-- The necessary implication includes all C² three-dimensional potentials,
including those that depend on the third coordinate. -/
theorem c2_planar_primitive_of_c2_potential {h : Euclidean 2 → ℝ} {G : VectorField}
    (hG : ContDiff ℝ 2 G) (hcurl : curl G = verticalLift h) :
    ContDiff ℝ 2 (restrictPotential G) ∧ planarDivergence (restrictPotential G) = h := by
  refine ⟨contDiff_restrictPotential hG, ?_⟩
  funext p
  rw [planarDivergence_restrictPotential, hcurl]
  simp [verticalLift]

/-- Exact whole-space equivalence of the C² vector-potential and C² planar
divergence problems. It does not assume that either problem is solvable. -/
theorem exists_c2_potential_iff_planar_divergence (h : Euclidean 2 → ℝ) :
    (∃ G : VectorField, ContDiff ℝ 2 G ∧ curl G = verticalLift h) ↔
      ∃ V : PlanarField, ContDiff ℝ 2 V ∧ planarDivergence V = h := by
  constructor
  · rintro ⟨G, hG, hc⟩
    exact ⟨restrictPotential G, c2_planar_primitive_of_c2_potential hG hc⟩
  · rintro ⟨V, hV, hd⟩
    refine ⟨liftPotential V, contDiff_liftPotential hV, ?_⟩
    rw [curl_liftPotential, hd]

private def univIdentityEquivalence :
    C2DomainEquivalence (univ : Set (Euclidean 3)) (univ : Set (Euclidean 3)) where
  forward := id
  inverse := id
  forward_mapsTo := fun _ _ => mem_univ _
  inverse_mapsTo := fun _ _ => mem_univ _
  left_inverse := fun _ _ => rfl
  right_inverse := fun _ _ => rfl
  forward_c2 := contDiffOn_id
  inverse_c2 := contDiffOn_id

/-- The unchanged PMA contract would solve every whole-plane C¹ datum with
a C² planar divergence primitive. -/
theorem contract_implies_c2_planar_divergence (hcontract : pma10_43_contract)
    {h : Euclidean 2 → ℝ} (hh : ContDiff ℝ 1 h) :
    ∃ V : PlanarField, ContDiff ℝ 2 V ∧ planarDivergence V = h := by
  have hz : EqOn (divergence (verticalLift h)) 0 univ := by
    rw [divergence_verticalLift]
    exact fun _ _ => rfl
  obtain ⟨G, hG, hcurl⟩ := hcontract.2.2.2 univ univ univIdentityEquivalence
    (verticalLift h) isOpen_univ isOpen_univ convex_univ
    (contDiff_verticalLift hh).contDiffOn hz
  apply (exists_c2_potential_iff_planar_divergence h).mp
  exact ⟨G, contDiffOn_univ.mp hG, funext (fun x => hcurl (mem_univ x))⟩

/-- A genuine C¹ planar counterexample would disprove the original contract.
This is conditional: no datum satisfying `hbad` is constructed here. -/
theorem planar_obstruction_disproves_contract {h : Euclidean 2 → ℝ}
    (hh : ContDiff ℝ 1 h)
    (hbad : ¬ ∃ V : PlanarField, ContDiff ℝ 2 V ∧ planarDivergence V = h) :
    ¬ pma10_43_contract := by
  intro hcontract
  exact hbad (contract_implies_c2_planar_divergence hcontract hh)

end Rudin.PMA.Chapter10.PlanarResearch
