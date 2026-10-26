import Rudin.PMA.Chapter10.SurfaceMaps
import Rudin.PMA.Chapter10.ExteriorDerivative

noncomputable section
set_option autoImplicit false
open Set Function
open scoped BigOperators

namespace Rudin.PMA.Chapter10
open Chapter09

def pma10_21_contract : Prop :=
  (∀ (n m k : ℕ) (E : Set (Euclidean n)) (V : Set (Euclidean m))
    (T : Euclidean n → Euclidean m) (ω : FormField m),
    IsOpen E → IsOpen V → ContDiffOn ℝ 1 T E → MapsTo T E V → IsFormOn V k ω →
      IsFormOn E k (pullbackForm T ω)) ∧
  (∀ (n m k : ℕ) (E : Set (Euclidean n)) (T : Euclidean n → Euclidean m)
    (a : (Fin k → Fin m) → Euclidean m → ℝ), IsOpen E → ContDiffOn ℝ 1 T E →
    ∀ x ∈ E, pullbackForm T (formFromCoefficients a) x =
      ∑ I, a I (T x) • (List.ofFn fun j => scalarDifferential (fun y => T y (I j)) x).prod) ∧
  (∀ (n m : ℕ) (T : Euclidean n → Euclidean m) (f : Euclidean m → ℝ),
    pullbackForm T (scalarForm f) = scalarForm (f ∘ T))

def pma10_22_contract : Prop :=
  (∀ (n m : ℕ) (T : Euclidean n → Euclidean m) (ω η : FormField m),
    pullbackForm T (ω + η) = pullbackForm T ω + pullbackForm T η ∧
    pullbackForm T (wedge ω η) = wedge (pullbackForm T ω) (pullbackForm T η)) ∧
  (∀ (n m k : ℕ) (E : Set (Euclidean n)) (V : Set (Euclidean m))
    (T : Euclidean n → Euclidean m) (ω : FormField m),
    IsOpen E → IsOpen V → ContDiffOn ℝ 2 T E → MapsTo T E V → IsCFormOn 1 V k ω →
      IsCFormOn 1 E k (pullbackForm T ω) ∧
      EqOn (exteriorDerivative (pullbackForm T ω)) (pullbackForm T (exteriorDerivative ω)) E)

def pma10_23_contract : Prop :=
  ∀ (n m p k : ℕ) (E : Set (Euclidean n)) (V : Set (Euclidean m))
    (W : Set (Euclidean p)) (T : Euclidean n → Euclidean m)
    (S : Euclidean m → Euclidean p) (ω : FormField p),
    IsOpen E → IsOpen V → IsOpen W → ContDiffOn ℝ 1 T E → ContDiffOn ℝ 1 S V →
    MapsTo T E V → MapsTo S V W → IsFormOn W k ω →
      EqOn (pullbackForm (S ∘ T) ω) (pullbackForm T (pullbackForm S ω)) E

def pma10_24_contract : Prop :=
  ∀ (n k : ℕ) (E : Set (Euclidean n)) (Φ : Surface k n E) (ω : FormField n),
    IsOpen E → IsFormOn E k ω →
      Φ.domain.Integrable (surfaceIntegrand Φ ω) ∧
      Φ.domain.Integrable (surfaceIntegrand (identityParameterSurface Φ.domain)
        (pullbackForm Φ.euclideanMap ω)) ∧
      surfaceIntegral Φ ω = surfaceIntegral (identityParameterSurface Φ.domain)
        (pullbackForm Φ.euclideanMap ω)

def pma10_25_contract : Prop :=
  ∀ (n m k : ℕ) (E : Set (Euclidean n)) (V : Set (Euclidean m))
    (T : Euclidean n → Euclidean m) (Φ : Surface k n E) (ω : FormField m)
    (hE : IsOpen E) (hV : IsOpen V) (hT : ContDiffOn ℝ 1 T E) (hTV : MapsTo T E V),
    IsFormOn V k ω →
      (Φ.mapBy T hE hT hTV).domain = Φ.domain ∧
      (Φ.mapBy T hE hT hTV).map = T ∘ Φ.map ∧
      Φ.domain.Integrable (surfaceIntegrand (Φ.mapBy T hE hT hTV) ω) ∧
      Φ.domain.Integrable (surfaceIntegrand Φ (pullbackForm T ω)) ∧
      surfaceIntegral (Φ.mapBy T hE hT hTV) ω = surfaceIntegral Φ (pullbackForm T ω)

end Rudin.PMA.Chapter10
