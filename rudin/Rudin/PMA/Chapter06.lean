import Rudin.PMA.Chapter06.Basic
import Rudin.PMA.Chapter06.Definitions
import Rudin.PMA.Chapter06.Refinement

/-! # PMA Chapter 6: verified sections in dependency order.
The index is in book order; only the listed nodes have been integrated.
Each imported support module preserves its independently reviewed source bytes. -/

open Set
namespace Rudin.PMA.Chapter06

/-! ### PMA-6.1

Principal proof: `pma6_1`. Definitions and supporting proofs: `Chapter06/Definitions.lean`.
-/

/-! ### PMA-6.2

Principal proof: `pma6_2`. Definitions and supporting proofs: `Chapter06/Definitions.lean`.
-/

/-! ### PMA-6.3

Principal proof: `pma6_3`. Definitions and supporting proofs: `Chapter06/Refinement.lean`.
-/

/-- Common refinement and invariance under repetitions of partition points. -/
theorem pma6_3 :
    (∀ {a b : ℝ} (P Q : Partition a b),
      ∃ R : Partition a b,
        Set.range R.point = Set.range P.point ∪ Set.range Q.point ∧
          R.Refines P ∧ R.Refines Q) ∧
    (∀ {f α : ℝ → ℝ} {a b : ℝ} (P Q : Partition a b),
      Set.range P.point = Set.range Q.point → BoundedOn f a b →
      MonotoneOn α (Icc a b) →
      lowerSum f α P = lowerSum f α Q ∧ upperSum f α P = upperSum f α Q) :=
  ⟨pma6_3_common_refinement, pma6_3_repetition_invariant⟩

/-! ### PMA-6.4

Principal proof: `pma6_4`. Definitions and supporting proofs: `Chapter06/Refinement.lean`.
-/

end Rudin.PMA.Chapter06
