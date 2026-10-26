import Rudin.PMA.Chapter10.ClosedExact

noncomputable section
set_option autoImplicit false
open Set Function

namespace Rudin.PMA.Chapter10
open Chapter09

/-- Exactness in one fixed positive degree. -/
def ClosedFormsExactOn {n : ℕ} (E : Set (Euclidean n)) (k : ℕ) : Prop :=
  ∀ ω : FormField n, IsClosedOn E (k + 1) ω → IsExactOn E (k + 1) ω

/-- The Poincaré property, in every positive degree, without a chosen primitive. -/
def AllClosedFormsExactOn {n : ℕ} (E : Set (Euclidean n)) : Prop :=
  ∀ (k : ℕ) (ω : FormField n), IsClosedOn E (k + 1) ω → IsExactOn E (k + 1) ω

/-- Both maps are C² on their respective open domains. Their ambient extensions
need not be inverse outside those domains. -/
structure C2DomainEquivalence {n m : ℕ} (E : Set (Euclidean n)) (V : Set (Euclidean m)) where
  forward : Euclidean n → Euclidean m
  inverse : Euclidean m → Euclidean n
  forward_mapsTo : MapsTo forward E V
  inverse_mapsTo : MapsTo inverse V E
  left_inverse : LeftInvOn inverse forward E
  right_inverse : RightInvOn inverse forward V
  forward_c2 : ContDiffOn ℝ 2 forward E
  inverse_c2 : ContDiffOn ℝ 2 inverse V

lemma pullbackForm_identity {n : ℕ} (ω : FormField n) : pullbackForm id ω = ω := by
  funext x
  simp only [pullbackForm, fderiv_id, covectorPullback_id, ExteriorAlgebra.map_id,
    AlgHom.id_apply, id_eq]

lemma pullbackForm_congr_on {n m : ℕ} {E : Set (Euclidean n)}
    {T S : Euclidean n → Euclidean m} (hE : IsOpen E) (he : EqOn T S E)
    (ω : FormField m) : EqOn (pullbackForm T ω) (pullbackForm S ω) E := by
  intro x hx
  have hd := (he.eventuallyEq_of_mem (hE.mem_nhds hx)).fderiv_eq (𝕜 := ℝ)
  simp only [pullbackForm, hd, he hx]

lemma pullbackForm_congr_form {n m : ℕ} {E : Set (Euclidean n)} {V : Set (Euclidean m)}
    (T : Euclidean n → Euclidean m) (hT : MapsTo T E V)
    {ω η : FormField m} (he : EqOn ω η V) :
    EqOn (pullbackForm T ω) (pullbackForm T η) E := by
  intro x hx
  simp only [pullbackForm, he (hT hx)]

lemma pullbackForm_zero {n m : ℕ} (T : Euclidean n → Euclidean m) :
    pullbackForm T 0 = 0 := by
  funext x
  exact map_zero _

lemma C2DomainEquivalence.inverse_pullback {n m : ℕ} {E : Set (Euclidean n)}
    {V : Set (Euclidean m)} (e : C2DomainEquivalence E V) (hE : IsOpen E) (hV : IsOpen V)
    (ω : FormField m) : EqOn (pullbackForm e.inverse (pullbackForm e.forward ω)) ω V := by
  intro x hx
  have hdS := (e.inverse_c2.differentiableOn (by norm_num)).differentiableAt (hV.mem_nhds hx)
  have hdT := (e.forward_c2.differentiableOn (by norm_num)).differentiableAt
    (hE.mem_nhds (e.inverse_mapsTo hx))
  rw [← pullbackForm_comp_at hdS hdT]
  have he : EqOn (e.forward ∘ e.inverse) id V := e.right_inverse
  simpa only [pullbackForm_identity] using pullbackForm_congr_on hV he ω hx

lemma IsClosedOn.pullback {n m k : ℕ} {E : Set (Euclidean n)} {V : Set (Euclidean m)}
    {T : Euclidean n → Euclidean m} (hE : IsOpen E) (hV : IsOpen V)
    (hT : ContDiffOn ℝ 2 T E) (hTV : MapsTo T E V) {ω : FormField m}
    (hω : IsClosedOn V k ω) : IsClosedOn E k (pullbackForm T ω) := by
  refine ⟨pullbackForm_isCFormOn hE hT hTV hω.1, ?_⟩
  intro x hx
  rw [exteriorDerivative_pullback hE hV hT hTV hω.1 hx]
  simpa only [pullbackForm_zero] using pullbackForm_congr_form T hTV hω.2 hx

lemma C2DomainEquivalence.transports_degree_exactness {n m k : ℕ} {E : Set (Euclidean n)}
    {V : Set (Euclidean m)} (e : C2DomainEquivalence E V) (hE : IsOpen E) (hV : IsOpen V)
    (h : ClosedFormsExactOn E k) : ClosedFormsExactOn V k := by
  intro ω hω
  have hp := hω.pullback hE hV e.forward_c2 e.forward_mapsTo
  obtain ⟨η, hη, hdη⟩ := h (pullbackForm e.forward ω) hp
  refine ⟨pullbackForm e.inverse η, pullbackForm_isCFormOn hV e.inverse_c2 e.inverse_mapsTo hη, ?_⟩
  intro x hx
  rw [exteriorDerivative_pullback hV hE e.inverse_c2 e.inverse_mapsTo hη hx,
    pullbackForm_congr_form e.inverse e.inverse_mapsTo hdη hx]
  exact e.inverse_pullback hE hV ω hx

lemma C2DomainEquivalence.transports_exactness {n m : ℕ} {E : Set (Euclidean n)}
    {V : Set (Euclidean m)} (e : C2DomainEquivalence E V) (hE : IsOpen E) (hV : IsOpen V)
    (h : AllClosedFormsExactOn E) : AllClosedFormsExactOn V := by
  intro k
  exact e.transports_degree_exactness hE hV (h k)

end Rudin.PMA.Chapter10
