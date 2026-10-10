import Mathlib
import Rudin.PMA.Chapter01

noncomputable section
open scoped BigOperators ComplexConjugate
open Set Filter Topology

/-!
# Rudin, *Principles of Mathematical Analysis* (3rd ed.)

## Chapter 2: Basic Topology

Every definition, theorem, and corollary from this chapter is
formalized below in dependency order. Zero `sorry`s: anything
not yet proved is tracked in `QUEUE.md`, never as a `sorry` here.
-/

namespace Rudin.PMA.Chapter02

/-! ### PMA-2.1: functions and their ranges. -/
abbrev PMAMapping (A B : Type*) := A → B
def pmaRange {A B : Type*} (f : PMAMapping A B) : Set B := {y | ∃ x, f x = y}
theorem pma2_1_unique {A B : Type*} (f : PMAMapping A B) (x : A) :
    ∃! y : B, f x = y := ⟨f x, rfl, fun _ h => h.symm⟩
theorem pma2_1_range {A B : Type*} (f : PMAMapping A B) : pmaRange f = Set.range f := rfl

/-! ### PMA-2.2: images, inverse images, and mapping properties. -/
def pmaImage {A B : Type*} (f : A → B) (E : Set A) : Set B := {y | ∃ x ∈ E, f x = y}
def pmaPreimage {A B : Type*} (f : A → B) (E : Set B) : Set A := {x | f x ∈ E}
def pmaOnto {A B : Type*} (f : A → B) : Prop := pmaRange f = Set.univ
def pmaOneToOne {A B : Type*} (f : A → B) : Prop := ∀ x y, f x = f y → x = y

theorem pma2_2_reference {A B : Type*} (f : A → B) (E : Set A) (F : Set B) :
    pmaImage f E = f '' E ∧ pmaPreimage f F = f ⁻¹' F ∧
    (pmaOnto f ↔ Function.Surjective f) ∧ (pmaOneToOne f ↔ Function.Injective f) := by
  refine ⟨rfl, rfl, ?_, Iff.rfl⟩
  exact Set.range_eq_univ

theorem pma2_2_oneToOne_alternative {A B : Type*} (f : A → B) :
    pmaOneToOne f ↔ ∀ x y, x ≠ y → f x ≠ f y := by
  constructor
  · intro h x y hxy hfx; exact hxy (h x y hfx)
  · intro h x y hfx
    by_contra hxy
    exact h x y hxy hfx

/-! ### PMA-2.3: equinumerosity and equivalence relations. -/
def Equinumerous (A B : Type*) : Prop := Nonempty (A ≃ B)
def PMAEquivalenceRelation {A : Type*} (r : A → A → Prop) : Prop :=
  (∀ x, r x x) ∧ (∀ x y, r x y → r y x) ∧
  (∀ x y z, r x y → r y z → r x z)

theorem pma2_3_reference {A : Type*} (r : A → A → Prop) :
    PMAEquivalenceRelation r ↔ Equivalence r := by
  constructor
  · rintro ⟨hr,hs,ht⟩
    exact ⟨hr,fun h => hs _ _ h,fun h₁ h₂ => ht _ _ _ h₁ h₂⟩
  · intro h
    exact ⟨h.refl,fun _ _ => h.symm,fun _ _ _ => h.trans⟩

theorem pma2_3_reflexive (A : Type*) : Equinumerous A A := ⟨Equiv.refl A⟩
theorem pma2_3_symmetric {A B : Type*} : Equinumerous A B → Equinumerous B A :=
  fun ⟨e⟩ => ⟨e.symm⟩
theorem pma2_3_transitive {A B C : Type*} :
    Equinumerous A B → Equinumerous B C → Equinumerous A C :=
  fun ⟨e⟩ ⟨f⟩ => ⟨e.trans f⟩

theorem pma2_3_bijection {A B : Type*} :
    Equinumerous A B ↔ ∃ f : A → B, Function.Bijective f := by
  constructor
  · rintro ⟨e⟩; exact ⟨e,e.bijective⟩
  · rintro ⟨f,hf⟩; exact ⟨Equiv.ofBijective f hf⟩

end Rudin.PMA.Chapter02
