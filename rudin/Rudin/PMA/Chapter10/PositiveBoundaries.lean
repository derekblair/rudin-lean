import Rudin.PMA.Chapter10.PositiveRegionUnions
import Rudin.PMA.Chapter10.FormIntegralContinuity
import Rudin.PMA.Chapter10.ChainStokes

noncomputable section
set_option autoImplicit false
open Set Function MeasureTheory
open scoped BigOperators

namespace Rudin.PMA.Chapter10
open Chapter09

/-- The positive boundary retains the alternating parametrized faces. -/
def PositiveSimplex.boundary {d : ℕ} {E : Set (Euclidean (d + 1))}
    (P : PositiveSimplex (d + 1) E) : SimplexChain d (d + 1) E :=
  simplexBoundary P.simplex

def PositiveRegion.boundary {d : ℕ} {E : Set (Euclidean (d + 1))}
    (R : PositiveRegion (d + 1) E) : SimplexChain d (d + 1) E := chainBoundary R.chain

lemma PositiveSimplex.boundary_independent {d : ℕ} {E : Set (Euclidean (d + 1))}
    (P Q : PositiveSimplex (d + 1) E) (hE : IsOpen E) (hPQ : P.carrier = Q.carrier) :
    ChainEq P.boundary Q.boundary := by
  apply chainEq_of_c1
  intro ω hω
  have hp := simplex_stokes_of_standard
    (fun U η hSU hU hη => standard_simplex_stokes hU hSU hη) hE hω P.simplex
  have hq := simplex_stokes_of_standard
    (fun U η hSU hU hη => standard_simplex_stokes hU hSU hη) hE hω Q.simplex
  exact hp.symm.trans ((P.integral_independent Q hPQ (pma10_18.1 _ _ _ _ hE hω).1).trans hq)

lemma PositiveRegion.boundary_independent {d : ℕ} {E : Set (Euclidean (d + 1))}
    (R T : PositiveRegion (d + 1) E) (hE : IsOpen E) (hRT : R.carrier = T.carrier) :
    ChainEq R.boundary T.boundary := by
  apply chainEq_of_c1
  intro ω hω
  rw [PositiveRegion.boundary, PositiveRegion.boundary,
    ← pma10_33 d (d + 1) E ω R.chain hE hω,
    ← pma10_33 d (d + 1) E ω T.chain hE hω]
  exact R.integral_independent T hRT (pma10_18.1 _ _ _ _ hE hω).1

lemma PositiveRegion.boundary_eq_sum {d : ℕ} {E : Set (Euclidean (d + 1))}
    (R : PositiveRegion (d + 1) E) : R.boundary = ∑ i, (R.piece i).boundary := by
  simp only [PositiveRegion.boundary, PositiveRegion.chain, map_sum,
    chainBoundary_single, one_smul, PositiveSimplex.boundary]

def positiveBoundary_contract : Prop :=
  (∀ (n : ℕ) (E : Set (Euclidean n)) (P : PositiveSimplex n E),
    IsOpen P.openCarrier ∧ closure P.openCarrier = P.carrier ∧
      ∀ u ∈ standardSimplex n, 0 ≤ coordinateJacobian P.simplex.coordinateMap u) ∧
  (∀ (d : ℕ) (E : Set (Euclidean (d + 1))) (P : PositiveSimplex (d + 1) E),
    P.boundary = ∑ i : Fin (d + 2), (-1 : ℤ) ^ i.val • Finsupp.single (P.simplex.face i) 1 ∧
      ∀ (ω : FormField (d + 1)), IsFormOn E d ω → ∀ i : Fin (d + 2),
        (ParameterDomain.simplex : ParameterDomain d).Integrable
          (surfaceIntegrand (P.simplex.face i).toSurface ω)) ∧
  (∀ (d : ℕ) (E : Set (Euclidean (d + 1))) (P Q : PositiveSimplex (d + 1) E),
    IsOpen E → P.carrier = Q.carrier → ChainEq P.boundary Q.boundary) ∧
  (∀ (d : ℕ) (E : Set (Euclidean (d + 1))) (R : PositiveRegion (d + 1) E),
    R.boundary = ∑ i, (R.piece i).boundary ∧
      ∀ ω : FormField (d + 1), IsFormOn E d ω →
        chainIntegral ω R.boundary = ∑ i, chainIntegral ω (R.piece i).boundary) ∧
  (∀ (d : ℕ) (E : Set (Euclidean (d + 1))) (R T : PositiveRegion (d + 1) E),
    IsOpen E → R.carrier = T.carrier → ChainEq R.boundary T.boundary)

theorem positiveBoundary : positiveBoundary_contract := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro n E P
    exact ⟨P.isOpen_openCarrier, P.closure_openCarrier, fun _ hu => P.jacobian_nonneg hu⟩
  · intro d E P
    refine ⟨rfl, fun ω hω i => ?_⟩
    exact ParameterDomain.integrable_of_continuousOn ((P.simplex.face i).toSurface.continuousOn_integrand hω)
  · intro d E P Q hE hPQ
    exact P.boundary_independent Q hE hPQ
  · intro d E R
    refine ⟨R.boundary_eq_sum, fun ω hω => ?_⟩
    rw [R.boundary_eq_sum, map_sum]
  · intro d E R T hE hRT
    exact R.boundary_independent T hE hRT

end Rudin.PMA.Chapter10
