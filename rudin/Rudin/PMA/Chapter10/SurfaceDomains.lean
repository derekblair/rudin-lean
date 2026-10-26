import Rudin.PMA.Chapter10.Surfaces
import Rudin.PMA.Chapter10.IntegrationProofs

noncomputable section
set_option autoImplicit false
open Set Function
open scoped BigOperators

namespace Rudin.PMA.Chapter10
open Chapter09

lemma surfaceDomain_standardSimplex_subset_unit (k : ℕ) : standardSimplex k ⊆ (Cell.unit k).carrier := by
  intro x hx
  rw [Cell.mem_carrier]
  intro i
  refine ⟨hx.1 i, ?_⟩
  exact (Finset.single_le_sum (fun j _ => hx.1 j) (Finset.mem_univ i)).trans hx.2

lemma surfaceDomain_isClosed_standardSimplex (k : ℕ) : IsClosed (standardSimplex k) := by
  have h : standardSimplex k = (⋂ i : Fin k, {x : Coord k | 0 ≤ x i}) ∩
      {x : Coord k | ∑ i, x i ≤ 1} := by
    ext x
    simp [standardSimplex]
  rw [h]
  exact (isClosed_iInter fun i => isClosed_le continuous_const (continuous_apply i)).inter
    (isClosed_le (continuous_finset_sum _ fun i _ => continuous_apply i) continuous_const)

lemma surfaceDomain_isCompact_standardSimplex (k : ℕ) : IsCompact (standardSimplex k) :=
  (Cell.unit k).isCompact_carrier.of_isClosed_subset (surfaceDomain_isClosed_standardSimplex k)
    (surfaceDomain_standardSimplex_subset_unit k)

lemma ParameterDomain.isCompact {k : ℕ} (D : ParameterDomain k) : IsCompact D.carrier := by
  cases D with
  | cell C => exact C.isCompact_carrier
  | simplex => exact surfaceDomain_isCompact_standardSimplex k

def intervalCell (a b : ℝ) (hab : a ≤ b) : Cell 1 :=
  ⟨fun _ => a, fun _ => b, fun _ => hab⟩

def ParameterDomain.interval : ParameterDomain 1 → ℝ × ℝ
  | .cell C => (C.lower 0, C.upper 0)
  | .simplex => (0, 1)

lemma ParameterDomain.interval_order (D : ParameterDomain 1) : D.interval.1 ≤ D.interval.2 := by
  cases D with
  | cell C => exact C.lower_le_upper 0
  | simplex => exact zero_le_one

lemma ParameterDomain.one_mem (D : ParameterDomain 1) (x : Coord 1) :
    x ∈ D.carrier ↔ x 0 ∈ Icc D.interval.1 D.interval.2 := by
  cases D with
  | cell C =>
    change (∀ i, C.lower i ≤ x i) ∧ (∀ i, x i ≤ C.upper i) ↔ _
    simp [ParameterDomain.interval]
  | simplex => simp [ParameterDomain.carrier, ParameterDomain.interval, standardSimplex, mem_Icc]

/-- A curve with the same neighborhood-extension convention as a surface. -/
structure RegularCurve (n : ℕ) (E : Set (Euclidean n)) where
  lower : ℝ
  upper : ℝ
  ordered : lower ≤ upper
  map : ℝ → Euclidean n
  neighborhood : Set ℝ
  open_neighborhood : IsOpen neighborhood
  interval_subset : Icc lower upper ⊆ neighborhood
  regularity : ContDiffOn ℝ 1 map neighborhood
  mapsTo : MapsTo map (Icc lower upper) E

def RegularCurve.toSurface {n : ℕ} {E : Set (Euclidean n)} (γ : RegularCurve n E) :
    Surface 1 n E where
  domain := .cell (intervalCell γ.lower γ.upper γ.ordered)
  map x := γ.map (x 0)
  neighborhood := (fun x : Coord 1 => x 0) ⁻¹' γ.neighborhood
  open_neighborhood := γ.open_neighborhood.preimage (continuous_apply 0)
  domain_subset := by
    intro x hx
    apply γ.interval_subset
    exact (Cell.mem_carrier.mp hx) 0
  regularity := γ.regularity.comp (contDiff_apply ℝ ℝ (0 : Fin 1)).contDiffOn (fun _ hx => hx)
  mapsTo := by
    intro x hx
    exact γ.mapsTo ((Cell.mem_carrier.mp hx) 0)

def Surface.toCurve {n : ℕ} {E : Set (Euclidean n)} (Φ : Surface 1 n E) :
    RegularCurve n E where
  lower := Φ.domain.interval.1
  upper := Φ.domain.interval.2
  ordered := Φ.domain.interval_order
  map t := Φ.map (fun _ => t)
  neighborhood := (fun t : ℝ => (fun _ : Fin 1 => t)) ⁻¹' Φ.neighborhood
  open_neighborhood := Φ.open_neighborhood.preimage (continuous_pi fun _ => continuous_id)
  interval_subset := by
    intro t ht
    apply Φ.domain_subset
    exact (Φ.domain.one_mem _).mpr ht
  regularity := Φ.regularity.comp (contDiff_pi.mpr fun _ => contDiff_id).contDiffOn
    (fun _ hx => hx)
  mapsTo := by
    intro t ht
    exact Φ.mapsTo ((Φ.domain.one_mem _).mpr ht)

def pma10_10_contract : Prop :=
  (∀ (k : ℕ) (D : ParameterDomain k), IsCompact D.carrier) ∧
  (∀ (k n : ℕ) (E : Set (Euclidean n)), IsOpen E → ∀ Φ : Surface k n E,
    ∃ U : Set (Coord k), IsOpen U ∧ Φ.domain.carrier ⊆ U ∧
      ContDiffOn ℝ 1 Φ.map U ∧ MapsTo Φ.map Φ.domain.carrier E) ∧
  (∀ (k n : ℕ) (E : Set (Euclidean n)), IsOpen E →
    ∀ (D : ParameterDomain k) (f : Coord k → Euclidean n) (U : Set (Coord k)),
    IsOpen U → D.carrier ⊆ U → ContDiffOn ℝ 1 f U → MapsTo f D.carrier E →
    ∃ Φ : Surface k n E, Φ.domain = D ∧ Φ.map = f) ∧
  (∀ (n : ℕ) (E : Set (Euclidean n)), IsOpen E → ∀ γ : RegularCurve n E,
    γ.toSurface.domain = .cell (intervalCell γ.lower γ.upper γ.ordered) ∧
      γ.toSurface.map = (fun x => γ.map (x 0)) ∧ γ.toSurface.toCurve.map = γ.map) ∧
  (∀ (n : ℕ) (E : Set (Euclidean n)), IsOpen E → ∀ Φ : Surface 1 n E,
    Φ.toCurve.lower = Φ.domain.interval.1 ∧ Φ.toCurve.upper = Φ.domain.interval.2 ∧
      Φ.toCurve.map = (fun t => Φ.map (fun _ => t)) ∧
      Φ.toCurve.toSurface.map = Φ.map)

theorem pma10_10 : pma10_10_contract := by
  refine ⟨fun _ D => D.isCompact, ?_, ?_, ?_, ?_⟩
  · intro k n E _ Φ
    exact ⟨Φ.neighborhood, Φ.open_neighborhood, Φ.domain_subset, Φ.regularity, Φ.mapsTo⟩
  · intro k n E _ D f U hU hDU hf hE
    exact ⟨⟨D, f, U, hU, hDU, hf, hE⟩, rfl, rfl⟩
  · intro n E _ γ
    exact ⟨rfl, rfl, rfl⟩
  · intro n E _ Φ
    refine ⟨rfl, rfl, rfl, ?_⟩
    funext x
    change Φ.map (fun _ => x 0) = Φ.map x
    congr 1
    funext i
    exact congrArg x (Subsingleton.elim 0 i)

end Rudin.PMA.Chapter10
