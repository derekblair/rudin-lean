import Rudin.PMA.Chapter06.Basic
import Rudin.PMA.Chapter06.Definitions
import Rudin.PMA.Chapter06.Refinement
import Rudin.PMA.Chapter06.Criterion
import Rudin.PMA.Chapter06.Integrability
import Rudin.PMA.Chapter06.Monotone
import Rudin.PMA.Chapter06.Split
import Rudin.PMA.Chapter06.Properties
import Rudin.PMA.Chapter06.Jump
import Rudin.PMA.Chapter06.Endpoint
import Rudin.PMA.Chapter06.Exceptional
import Rudin.PMA.Chapter06.Calculus
import Rudin.PMA.Chapter06.Moment
import Rudin.PMA.Chapter06.Vector
import Rudin.PMA.Chapter06.Curve

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

/-! ### PMA-6.5

Principal proof: `pma6_5`. Definitions and supporting proofs: `Chapter06/Criterion.lean`.
-/

/-! ### PMA-6.6

Principal proof: `pma6_6`. Definitions and supporting proofs: `Chapter06/Criterion.lean`.
-/

/-! ### PMA-6.7

Principal proof: `pma6_7`. Definitions and supporting proofs: `Chapter06/Criterion.lean`.
-/

/-! ### PMA-6.8

Principal proof: `pma6_8`. Definitions and supporting proofs: `Chapter06/Integrability.lean`.
-/

/-! ### PMA-6.9

Principal proof: `pma6_9`. Definitions and supporting proofs: `Chapter06/Monotone.lean`.
-/

/-! ### PMA-6.10

Principal proof: `pma6_10`. Definitions and supporting proofs: `Chapter06/Exceptional.lean`.
-/

/-! ### PMA-6.11

Principal proof: `pma6_11`. Definitions and supporting proofs: `Chapter06/Integrability.lean`.
-/

/-! ### PMA-6.12

Principal proof: `pma6_12`. Definitions and supporting proofs: `Chapter06/Properties.lean`.
-/

/-! ### PMA-6.13

Principal proof: `pma6_13`. Definitions and supporting proofs: `Chapter06/Integrability.lean`.
-/

/-! ### PMA-6.14

Principal proof: `pma6_14`. Definitions and supporting proofs: `Chapter06/Jump.lean`.
-/

/-! ### PMA-6.15

Principal proof: `pma6_15`. Definitions and supporting proofs: `Chapter06/Jump.lean`.
-/

/-! ### PMA-6.16

Principal proof: `pma6_16`. Definitions and supporting proofs: `Chapter06/Jump.lean`.
-/

/-! ### PMA-6.17

Principal proof: `pma6_17`. Definitions and supporting proofs: `Chapter06/Calculus.lean`.
-/

/-! ### PMA-6.18

Principal proof: `pma6_18`. Definitions and supporting proofs: `Chapter06/Moment.lean`.
-/

/-! ### PMA-6.19

Principal proof: `pma6_19`. Definitions and supporting proofs: `Chapter06/Calculus.lean`.
-/

/-! ### PMA-6.20

Principal proof: `pma6_20`. Definitions and supporting proofs: `Chapter06/Calculus.lean`.
-/

/-! ### PMA-6.21

Principal proof: `pma6_21`. Definitions and supporting proofs: `Chapter06/Calculus.lean`.
-/

/-! ### PMA-6.22

Principal proof: `pma6_22`. Definitions and supporting proofs: `Chapter06/Calculus.lean`.
-/

/-! ### PMA-6.23

Principal proof: `pma6_23`. Definitions and supporting proofs: `Chapter06/Vector.lean`.
-/

/-! ### PMA-6.24

Principal proof: `pma6_24`. Definitions and supporting proofs: `Chapter06/Vector.lean`.
-/

/-! ### PMA-6.25

Principal proof: `pma6_25`. Definitions and supporting proofs: `Chapter06/Vector.lean`.
-/

/-! ### PMA-6.26

Principal proof: `pma6_26`. Definitions and supporting proofs: `Chapter06/Curve.lean`.
-/

/-! ### PMA-6.27

Principal proof: `pma6_27`. Definitions and supporting proofs: `Chapter06/Curve.lean`.
-/

end Rudin.PMA.Chapter06
