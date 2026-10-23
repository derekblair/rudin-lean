import Rudin.PMA.Chapter09.Differentiation

set_option autoImplicit false
noncomputable section
open Set Filter Topology

namespace Rudin.PMA.Chapter09

/-- An open partial homeomorphism packages the two open neighborhoods, the
bijection and both inverse identities. Its forward function is the given map. -/
def InverseNeighborhood {V W : Type*} [TopologicalSpace V] [TopologicalSpace W]
    (f : V → W) (E : Set V) (a : V) (e : OpenPartialHomeomorph V W) : Prop :=
  (e : V → W) = f ∧ a ∈ e.source ∧ e.source ⊆ E

def pma9_24_contract : Prop :=
  (∀ n (E : Set (Euclidean n)) (f : Euclidean n → Euclidean n) a,
    IsOpen E → a ∈ E → C1On f E → (fderiv ℝ f a).IsInvertible →
    ∃ e : OpenPartialHomeomorph (Euclidean n) (Euclidean n),
      InverseNeighborhood f E a e ∧ C1On e.symm e.target ∧
      ∀ y ∈ e.target,
        HasFDerivAt e.symm (fderiv ℝ f (e.symm y)).inverse y) ∧
  (∀ n (E : Set (Euclidean n)) (f : Euclidean n → Euclidean n) a,
    IsOpen E → a ∈ E → (∀ x ∈ E, DifferentiableAt ℝ f x) →
    ContinuousAt (fderiv ℝ f) a → (fderiv ℝ f a).IsInvertible →
    ∃ e : OpenPartialHomeomorph (Euclidean n) (Euclidean n),
      InverseNeighborhood f E a e ∧
      ∀ y ∈ e.target,
        HasFDerivAt e.symm (fderiv ℝ f (e.symm y)).inverse y)

def pma9_25_contract : Prop :=
  (∀ n (E : Set (Euclidean n)) (f : Euclidean n → Euclidean n),
    IsOpen E → C1On f E → (∀ x ∈ E, (fderiv ℝ f x).IsInvertible) →
    (∀ W : Set (Euclidean n), IsOpen W → W ⊆ E → IsOpen (f '' W)) ∧
    ∀ a ∈ E, ∃ U : Set (Euclidean n),
      IsOpen U ∧ a ∈ U ∧ U ⊆ E ∧ InjOn f U) ∧
  (∃ f : Euclidean 2 → Euclidean 2,
    C1On f univ ∧ (∀ x, (fderiv ℝ f x).IsInvertible) ∧ ¬ Function.Injective f)

section InverseHelpers

variable {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
  [NormedAddCommGroup W] [NormedSpace ℝ W]

/-- The weak source regularity suffices: shrink to where the derivative is
invertible, and differentiate the local inverse at each point of its domain. -/
theorem inverse_neighborhood_of_continuous_derivative {E : Set V} {f : V → W} {a : V}
    (hE : IsOpen E) (ha : a ∈ E) (hf : ∀ x ∈ E, DifferentiableAt ℝ f x)
    (hcont : ContinuousAt (fderiv ℝ f) a) (hinv : (fderiv ℝ f a).IsInvertible) :
    ∃ e : OpenPartialHomeomorph V W,
      InverseNeighborhood f E a e ∧
      (∀ x ∈ e.source, (fderiv ℝ f x).IsInvertible) ∧
      ∀ y ∈ e.target, HasFDerivAt e.symm (fderiv ℝ f (e.symm y)).inverse y := by
  have hstrict : HasStrictFDerivAt f (fderiv ℝ f a) a :=
    hasStrictFDerivAt_of_hasFDerivAt_of_continuousAt
      (Filter.eventually_of_mem (hE.mem_nhds ha) fun x hx => (hf x hx).hasFDerivAt) hcont
  obtain ⟨A, hA⟩ := hinv
  have hstrictA : HasStrictFDerivAt f (A : V →L[ℝ] W) a := by
    simpa only [hA] using hstrict
  let e₀ := hstrictA.toOpenPartialHomeomorph f
  have hnear : E ∩ {x | (fderiv ℝ f x).IsInvertible} ∈ 𝓝 a :=
    inter_mem (hE.mem_nhds ha) (hcont.eventually
      (show (fderiv ℝ f a).IsInvertible from ⟨A, hA⟩).eventually_nhds)
  obtain ⟨S, hS, hSopen, haS⟩ := mem_nhds_iff.mp hnear
  let e := e₀.restrOpen S hSopen
  have hsource : e.source ⊆ E ∩ {x | (fderiv ℝ f x).IsInvertible} :=
    fun _ hx => hS hx.2
  have he : (e : V → W) = f := rfl
  refine ⟨e, ⟨he, ⟨hstrictA.mem_toOpenPartialHomeomorph_source, haS⟩,
    fun _ hx => (hsource hx).1⟩, fun _ hx => (hsource hx).2, ?_⟩
  intro y hy
  have hx := e.map_target hy
  obtain ⟨B, hB⟩ := (hsource hx).2
  have hder : HasFDerivAt e (B : V →L[ℝ] W) (e.symm y) := by
    rw [he, hB]
    exact (hf _ (hsource hx).1).hasFDerivAt
  simpa only [← hB, ContinuousLinearMap.inverse_equiv] using e.hasFDerivAt_symm hy hder

theorem inverse_neighborhood_c1 {E : Set V} {f : V → W} {a : V}
    (hE : IsOpen E) (ha : a ∈ E) (hf : C1On f E)
    (hinv : (fderiv ℝ f a).IsInvertible) :
    ∃ e : OpenPartialHomeomorph V W,
      InverseNeighborhood f E a e ∧ C1On e.symm e.target ∧
      ∀ y ∈ e.target, HasFDerivAt e.symm (fderiv ℝ f (e.symm y)).inverse y := by
  obtain ⟨e, he, hi, hd⟩ := inverse_neighborhood_of_continuous_derivative hE ha hf.1
    ((hf.2 a ha).continuousAt (hE.mem_nhds ha)) hinv
  have hcf : ContDiffOn ℝ 1 f E := (c1On_iff_contDiffOn hE).mp hf
  have hcg : ContDiffOn ℝ 1 e.symm e.target := by
    intro y hy
    have hx := e.map_target hy
    obtain ⟨B, hB⟩ := hi _ hx
    have hder : HasFDerivAt e (B : V →L[ℝ] W) (e.symm y) := by
      rw [he.1, hB]
      exact (hf.1 _ (he.2.2 hx)).hasFDerivAt
    have hce : ContDiffAt ℝ 1 e (e.symm y) := by
      rw [he.1]
      exact (hcf _ (he.2.2 hx)).contDiffAt (hE.mem_nhds (he.2.2 hx))
    exact (e.contDiffAt_symm hy hder hce).contDiffWithinAt
  exact ⟨e, he, (c1On_iff_contDiffOn e.open_target).mpr hcg, hd⟩

end InverseHelpers

theorem pma9_24 : pma9_24_contract := by
  constructor
  · intro n E f a hE ha hf hi
    exact inverse_neighborhood_c1 hE ha hf hi
  · intro n E f a hE ha hf hc hi
    obtain ⟨e, he, _, hd⟩ := inverse_neighborhood_of_continuous_derivative hE ha hf hc hi
    exact ⟨e, he, hd⟩

theorem open_image_of_invertible_derivative {n : ℕ} {E : Set (Euclidean n)}
    {f : Euclidean n → Euclidean n} (hE : IsOpen E) (hf : C1On f E)
    (hi : ∀ x ∈ E, (fderiv ℝ f x).IsInvertible)
    {W : Set (Euclidean n)} (hW : IsOpen W) (hWE : W ⊆ E) : IsOpen (f '' W) := by
  rw [isOpen_iff_mem_nhds]
  rintro _ ⟨x, hx, rfl⟩
  have hfW : C1On f W := ⟨fun y hy => hf.1 y (hWE hy), hf.2.mono hWE⟩
  obtain ⟨e, he, _, _⟩ := inverse_neighborhood_c1 hW hx hfW (hi x (hWE hx))
  have htarget : e.target ⊆ f '' W := by
    intro y hy
    refine ⟨e.symm y, he.2.2 (e.map_target hy), ?_⟩
    rw [← he.1]
    exact e.right_inv hy
  have hy : f x ∈ e.target := by simpa only [he.1] using e.map_source he.2.1
  exact mem_of_superset (e.open_target.mem_nhds hy) htarget

/-- The complex exponential, transported to the real Euclidean plane, is a
local diffeomorphism with a nonzero period. -/
theorem exists_noninjective_local_diffeomorphism :
    ∃ f : Euclidean 2 → Euclidean 2,
      C1On f univ ∧ (∀ x, (fderiv ℝ f x).IsInvertible) ∧ ¬ Function.Injective f := by
  let e : Euclidean 2 ≃L[ℝ] ℂ := ContinuousLinearEquiv.ofFinrankEq
    (by simp [Euclidean, Complex.finrank_real_complex])
  let f : Euclidean 2 → Euclidean 2 := fun x => e.symm (Complex.exp (e x))
  have hc : ContDiff ℝ 1 f := e.symm.contDiff.comp (Complex.contDiff_exp.comp e.contDiff)
  refine ⟨f, (c1On_iff_contDiffOn isOpen_univ).mpr hc.contDiffOn, ?_, ?_⟩
  · intro x
    let B : ℂ ≃L[ℝ] ℂ :=
      ((LinearEquiv.smulOfNeZero ℂ ℂ (Complex.exp (e x)) (Complex.exp_ne_zero _)).restrictScalars ℝ).toContinuousLinearEquiv
    have hd : HasFDerivAt Complex.exp (B : ℂ →L[ℝ] ℂ) (e x) := by
      convert (Complex.hasDerivAt_exp (e x)).hasFDerivAt.restrictScalars ℝ using 1
      ext z
      simp [B, mul_comm]
    have hh := e.symm.hasFDerivAt.comp x (hd.comp x e.hasFDerivAt)
    refine ⟨(e.trans B).trans e.symm, ?_⟩
    exact hh.fderiv.symm
  · intro hinj
    have hz : f (e.symm 0) = f (e.symm (2 * Real.pi * Complex.I)) := by
      simp [f, Complex.exp_two_pi_mul_I]
    have heq : (0 : ℂ) = 2 * Real.pi * Complex.I := by
      simpa using congrArg e (hinj hz)
    have hne : (2 : ℂ) * Real.pi * Complex.I ≠ 0 :=
      mul_ne_zero (mul_ne_zero (by norm_num) (by exact_mod_cast Real.pi_ne_zero)) Complex.I_ne_zero
    exact hne heq.symm

theorem pma9_25 : pma9_25_contract := by
  refine ⟨?_, exists_noninjective_local_diffeomorphism⟩
  intro n E f hE hf hi
  refine ⟨fun W hW hWE => open_image_of_invertible_derivative hE hf hi hW hWE, ?_⟩
  intro a ha
  obtain ⟨e, he, _, _⟩ := inverse_neighborhood_c1 hE ha hf (hi a ha)
  refine ⟨e.source, e.open_source, he.2.1, he.2.2, ?_⟩
  simpa only [he.1] using e.injOn

end Rudin.PMA.Chapter09
