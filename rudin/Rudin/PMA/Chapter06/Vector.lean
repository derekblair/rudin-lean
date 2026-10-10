import Mathlib
import Rudin.PMA.Chapter05
import Rudin.PMA.Chapter06.Integrability
import Rudin.PMA.Chapter06.Definitions
import Rudin.PMA.Chapter06.Split
import Rudin.PMA.Chapter06.Calculus

noncomputable section
open Set Filter Topology
open scoped BigOperators RealInnerProductSpace InnerProductSpace

namespace Rudin.PMA.Chapter06

/-! ### PMA-6.23: Coordinatewise native vector Riemann–Stieltjes integrals. -/

def VectorRSIntegrable {n : ℕ} (f : ℝ → EuclideanSpace ℝ (Fin n))
    (α : ℝ → ℝ) (a b : ℝ) : Prop :=
  a ≤ b ∧ MonotoneOn α (Icc a b) ∧ ∀ j, RSIntegrable (fun x => f x j) α a b

def VectorRSIntegral {n : ℕ} (f : ℝ → EuclideanSpace ℝ (Fin n))
    (α : ℝ → ℝ) (a b : ℝ) : EuclideanSpace ℝ (Fin n) :=
  WithLp.toLp 2 (fun j => RSIntegral (fun x => f x j) α a b)

def VectorBoundedOn {n : ℕ} (f : ℝ → EuclideanSpace ℝ (Fin n)) (a b : ℝ) : Prop :=
  ∃ M : ℝ, ∀ x ∈ Icc a b, ‖f x‖ ≤ M

def pma6_23_contract : Prop :=
  (∀ (n : ℕ) (f : ℝ → EuclideanSpace ℝ (Fin n)) (α : ℝ → ℝ) (a b : ℝ),
    (VectorRSIntegrable f α a b ↔
      a ≤ b ∧ MonotoneOn α (Icc a b) ∧ ∀ j, RSIntegrable (fun x => f x j) α a b) ∧
    (∀ j, (VectorRSIntegral f α a b) j = RSIntegral (fun x => f x j) α a b)) ∧
  (∀ (n : ℕ) (f g : ℝ → EuclideanSpace ℝ (Fin n)) (α : ℝ → ℝ) (a b c : ℝ),
    VectorRSIntegrable f α a b → VectorRSIntegrable g α a b →
    VectorRSIntegrable (fun x => f x + g x) α a b ∧
    VectorRSIntegral (fun x => f x + g x) α a b =
      VectorRSIntegral f α a b + VectorRSIntegral g α a b ∧
    VectorRSIntegrable (fun x => c • f x) α a b ∧
    VectorRSIntegral (fun x => c • f x) α a b = c • VectorRSIntegral f α a b) ∧
  (∀ (n : ℕ) (f : ℝ → EuclideanSpace ℝ (Fin n)) (α : ℝ → ℝ) (a b c : ℝ),
    a < c → c < b → VectorRSIntegrable f α a b →
    VectorRSIntegrable f α a c ∧ VectorRSIntegrable f α c b ∧
    VectorRSIntegral f α a b = VectorRSIntegral f α a c + VectorRSIntegral f α c b) ∧
  (∀ (n : ℕ) (f : ℝ → EuclideanSpace ℝ (Fin n)) (α β : ℝ → ℝ) (a b c : ℝ),
    VectorRSIntegrable f α a b → VectorRSIntegrable f β a b → 0 < c →
    VectorRSIntegrable f (fun x => α x + β x) a b ∧
    VectorRSIntegral f (fun x => α x + β x) a b =
      VectorRSIntegral f α a b + VectorRSIntegral f β a b ∧
    VectorRSIntegrable f (fun x => c * α x) a b ∧
    VectorRSIntegral f (fun x => c * α x) a b = c • VectorRSIntegral f α a b) ∧
  (∀ (n : ℕ) (f : ℝ → EuclideanSpace ℝ (Fin n)) (α α' : ℝ → ℝ) (a b : ℝ),
    a < b → MonotoneOn α (Icc a b) →
    (∀ x ∈ Icc a b, HasDerivWithinAt α (α' x) (Icc a b) x) →
    RIntegrable α' a b → VectorBoundedOn f a b →
    (VectorRSIntegrable f α a b ↔ VectorRSIntegrable (fun x => α' x • f x) id a b) ∧
    (VectorRSIntegrable f α a b →
      VectorRSIntegral f α a b = VectorRSIntegral (fun x => α' x • f x) id a b)) ∧
  (∀ (n : ℕ) (f : ℝ → EuclideanSpace ℝ (Fin n)) (a b : ℝ),
    a < b → VectorRSIntegrable f id a b →
    ContinuousOn (fun x => VectorRSIntegral f id a x) (Icc a b) ∧
    UniformContinuousOn (fun x => VectorRSIntegral f id a x) (Icc a b) ∧
    (∀ x ∈ Icc a b, ContinuousWithinAt f (Icc a b) x →
      HasDerivWithinAt (fun u => VectorRSIntegral f id a u) (f x) (Icc a b) x))

/-! ### PMA-6.24: Vector fundamental theorem of calculus. -/

def pma6_24_contract : Prop :=
  ∀ (n : ℕ) (F f : ℝ → EuclideanSpace ℝ (Fin n)) (a b : ℝ), a < b →
    (∀ x ∈ Icc a b, HasDerivWithinAt F (f x) (Icc a b) x) →
    VectorRSIntegrable f id a b → VectorRSIntegral f id a b = F b - F a

/-! ### PMA-6.25: Integrability of the Euclidean norm and the integral norm bound. -/

def pma6_25_contract : Prop :=
  ∀ (n : ℕ) (f : ℝ → EuclideanSpace ℝ (Fin n)) (α : ℝ → ℝ) (a b : ℝ),
    VectorRSIntegrable f α a b →
    RSIntegrable (fun x => ‖f x‖) α a b ∧
      ‖VectorRSIntegral f α a b‖ ≤ RSIntegral (fun x => ‖f x‖) α a b

@[simp] theorem vectorRSIntegral_apply {n : ℕ} (f : ℝ → EuclideanSpace ℝ (Fin n))
    (α : ℝ → ℝ) (a b : ℝ) (j : Fin n) :
    VectorRSIntegral f α a b j = RSIntegral (fun x => f x j) α a b := rfl

theorem vectorRSIntegrable_add {n : ℕ} {f g : ℝ → EuclideanSpace ℝ (Fin n)}
    {α : ℝ → ℝ} {a b : ℝ} (hf : VectorRSIntegrable f α a b)
    (hg : VectorRSIntegrable g α a b) :
    VectorRSIntegrable (fun x => f x + g x) α a b ∧
      VectorRSIntegral (fun x => f x + g x) α a b =
        VectorRSIntegral f α a b + VectorRSIntegral g α a b := by
  refine ⟨⟨hf.1, hf.2.1, fun j => (rsIntegrable_add (hf.2.2 j) (hg.2.2 j)).1⟩, ?_⟩
  apply PiLp.ext
  intro j
  exact (rsIntegrable_add (hf.2.2 j) (hg.2.2 j)).2

theorem vectorRSIntegrable_smul {n : ℕ} {f : ℝ → EuclideanSpace ℝ (Fin n)}
    {α : ℝ → ℝ} {a b : ℝ} (hf : VectorRSIntegrable f α a b) (c : ℝ) :
    VectorRSIntegrable (fun x => c • f x) α a b ∧
      VectorRSIntegral (fun x => c • f x) α a b = c • VectorRSIntegral f α a b := by
  refine ⟨⟨hf.1, hf.2.1, fun j => (rsIntegrable_const_mul (hf.2.2 j) c).1⟩, ?_⟩
  apply PiLp.ext
  intro j
  exact (rsIntegrable_const_mul (hf.2.2 j) c).2

theorem vectorRSIntegrable_split {n : ℕ} {f : ℝ → EuclideanSpace ℝ (Fin n)}
    {α : ℝ → ℝ} {a b c : ℝ} (hac : a ≤ c) (hcb : c ≤ b)
    (hf : VectorRSIntegrable f α a b) :
    VectorRSIntegrable f α a c ∧ VectorRSIntegrable f α c b ∧
      VectorRSIntegral f α a b = VectorRSIntegral f α a c + VectorRSIntegral f α c b := by
  refine ⟨⟨hac, hf.2.1.mono (Icc_subset_Icc_right hcb),
      fun j => (split_ordered hac hcb (hf.2.2 j)).1⟩,
    ⟨hcb, hf.2.1.mono (Icc_subset_Icc_left hac),
      fun j => (split_ordered hac hcb (hf.2.2 j)).2.1⟩, ?_⟩
  apply PiLp.ext
  intro j
  exact (split_ordered hac hcb (hf.2.2 j)).2.2

theorem vectorRSIntegrable_integrator_add {n : ℕ}
    {f : ℝ → EuclideanSpace ℝ (Fin n)} {α β : ℝ → ℝ} {a b : ℝ}
    (hf : VectorRSIntegrable f α a b) (hg : VectorRSIntegrable f β a b) :
    VectorRSIntegrable f (fun x => α x + β x) a b ∧
      VectorRSIntegral f (fun x => α x + β x) a b =
        VectorRSIntegral f α a b + VectorRSIntegral f β a b := by
  refine ⟨⟨hf.1, fun _ hx _ hy hxy => add_le_add (hf.2.1 hx hy hxy) (hg.2.1 hx hy hxy),
    fun j => (rsIntegrable_integrator_add (hf.2.2 j) (hg.2.2 j)).1⟩, ?_⟩
  apply PiLp.ext
  intro j
  exact (rsIntegrable_integrator_add (hf.2.2 j) (hg.2.2 j)).2

theorem vectorRSIntegrable_integrator_const_mul {n : ℕ}
    {f : ℝ → EuclideanSpace ℝ (Fin n)} {α : ℝ → ℝ} {a b c : ℝ}
    (hf : VectorRSIntegrable f α a b) (hc : 0 < c) :
    VectorRSIntegrable f (fun x => c * α x) a b ∧
      VectorRSIntegral f (fun x => c * α x) a b = c • VectorRSIntegral f α a b := by
  refine ⟨⟨hf.1, fun _ hx _ hy hxy => mul_le_mul_of_nonneg_left (hf.2.1 hx hy hxy) hc.le,
    fun j => (rsIntegrable_integrator_const_mul (hf.2.2 j) hc).1⟩, ?_⟩
  apply PiLp.ext
  intro j
  exact (rsIntegrable_integrator_const_mul (hf.2.2 j) hc).2

theorem vectorBoundedOn_coordinate {n : ℕ} {f : ℝ → EuclideanSpace ℝ (Fin n)}
    {a b : ℝ} (hf : VectorBoundedOn f a b) (j : Fin n) : BoundedOn (fun x => f x j) a b := by
  obtain ⟨M, hM⟩ := hf
  exact ⟨M, fun x hx => (PiLp.norm_apply_le (f x) j).trans (hM x hx)⟩

theorem vectorRSIntegrable_density {n : ℕ} {f : ℝ → EuclideanSpace ℝ (Fin n)}
    {α α' : ℝ → ℝ} {a b : ℝ} (hab : a < b) (hα : MonotoneOn α (Icc a b))
    (hd : ∀ x ∈ Icc a b, HasDerivWithinAt α (α' x) (Icc a b) x)
    (hi : RIntegrable α' a b) (hb : VectorBoundedOn f a b) :
    (VectorRSIntegrable f α a b ↔ VectorRSIntegrable (fun x => α' x • f x) id a b) ∧
    (VectorRSIntegrable f α a b →
      VectorRSIntegral f α a b = VectorRSIntegral (fun x => α' x • f x) id a b) := by
  have hscalar (j : Fin n) := pma6_17 (fun x => f x j) α α' a b hab hα hd hi
    (vectorBoundedOn_coordinate hb j)
  have hcoord (j : Fin n) :
      (fun x => (α' x • f x) j) = (fun x => f x j * α' x) := by
    funext x
    simp only [PiLp.smul_apply, smul_eq_mul, mul_comm]
  constructor
  · constructor
    · intro hf
      refine ⟨hab.le, fun _ _ _ _ h => h, ?_⟩
      intro j
      rw [hcoord j]
      exact (hscalar j).1.mp (hf.2.2 j)
    · intro hf
      refine ⟨hab.le, hα, ?_⟩
      intro j
      apply (hscalar j).1.mpr
      convert hf.2.2 j using 1
      · funext x
        simp only [PiLp.smul_apply, smul_eq_mul, mul_comm]
      · rfl
  · intro hf
    apply PiLp.ext
    intro j
    change RSIntegral (fun x => f x j) α a b = RSIntegral (fun x => (α' x • f x) j) id a b
    rw [hcoord j]
    exact (hscalar j).2 (hf.2.2 j)

theorem pma6_24 : pma6_24_contract := by
  intro n F f a b hab hd hf
  apply PiLp.ext
  intro j
  exact pma6_21 (fun x => F x j) (fun x => f x j) a b hab
    (fun x hx => (Chapter05.euclidean_derivative_components n F (f x) (Icc a b) x).mp (hd x hx) j)
    (hf.2.2 j)

theorem vectorRSIntegral_primitive {n : ℕ} {f : ℝ → EuclideanSpace ℝ (Fin n)}
    {a b : ℝ} (hab : a < b) (hf : VectorRSIntegrable f id a b) :
    ContinuousOn (fun x => VectorRSIntegral f id a x) (Icc a b) ∧
    UniformContinuousOn (fun x => VectorRSIntegral f id a x) (Icc a b) ∧
    (∀ x ∈ Icc a b, ContinuousWithinAt f (Icc a b) x →
      HasDerivWithinAt (fun u => VectorRSIntegral f id a u) (f x) (Icc a b) x) := by
  have hscalar (j : Fin n) := pma6_20 (fun x => f x j) a b hab (hf.2.2 j)
  have hc : ContinuousOn (fun x => fun j => RSIntegral (fun t => f t j) id a x) (Icc a b) :=
    continuousOn_pi.mpr (fun j => (hscalar j).1)
  have hcv : ContinuousOn (fun x => VectorRSIntegral f id a x) (Icc a b) :=
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin n => ℝ)).symm.continuous.comp_continuousOn hc
  refine ⟨hcv, isCompact_Icc.uniformContinuousOn_of_continuous hcv, ?_⟩
  intro x hx hfx
  apply (Chapter05.euclidean_derivative_components n _ _ _ _).mpr
  intro j
  have hj : ContinuousWithinAt (fun t => f t j) (Icc a b) x :=
    (PiLp.continuous_apply 2 (fun _ : Fin n => ℝ) j).continuousAt.comp_continuousWithinAt hfx
  exact (hscalar j).2.2 x hx hj

theorem pma6_23 : pma6_23_contract := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro n f α a b
    exact ⟨Iff.rfl, fun _ => rfl⟩
  · intro n f g α a b c hf hg
    have hadd := vectorRSIntegrable_add hf hg
    have hsmul := vectorRSIntegrable_smul hf c
    exact ⟨hadd.1, hadd.2, hsmul.1, hsmul.2⟩
  · intro n f α a b c hac hcb hf
    exact vectorRSIntegrable_split hac.le hcb.le hf
  · intro n f α β a b c hf hg hc
    have hadd := vectorRSIntegrable_integrator_add hf hg
    have hsmul := vectorRSIntegrable_integrator_const_mul hf hc
    exact ⟨hadd.1, hadd.2, hsmul.1, hsmul.2⟩
  · intro n f α α' a b hab hα hd hi hb
    exact vectorRSIntegrable_density hab hα hd hi hb
  · intro n f a b hab hf
    exact vectorRSIntegral_primitive hab hf

theorem vector_scalar_finite_sum {ι : Type*} (s : Finset ι) (f : ι → ℝ → ℝ)
    {α : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b) (hα : MonotoneOn α (Icc a b))
    (hf : ∀ j ∈ s, RSIntegrable (f j) α a b) :
    RSIntegrable (fun x => ∑ j ∈ s, f j x) α a b ∧
      RSIntegral (fun x => ∑ j ∈ s, f j x) α a b = ∑ j ∈ s, RSIntegral (f j) α a b := by
  classical
  revert hf
  induction s using Finset.induction_on with
  | empty =>
    intro _
    simpa using (rsIntegral_const (c := 0) hab hα)
  | @insert j s hj ih =>
    intro hf
    have hs := ih (fun k hk => hf k (Finset.mem_insert_of_mem hk))
    have hh := rsIntegrable_add (hf j (Finset.mem_insert_self j s)) hs.1
    rw [hs.2] at hh
    simpa only [Finset.sum_insert hj] using hh

theorem vectorRSIntegrable_norm {n : ℕ} {f : ℝ → EuclideanSpace ℝ (Fin n)}
    {α : ℝ → ℝ} {a b : ℝ} (hf : VectorRSIntegrable f α a b) :
    RSIntegrable (fun x => ‖f x‖) α a b := by
  have hs := (vector_scalar_finite_sum Finset.univ (fun j x => (f x j) ^ 2) hf.1 hf.2.1
    (fun j _ => rsIntegrable_square (hf.2.2 j))).1
  obtain ⟨M, hM⟩ := hs.2.1
  have hh := rsIntegrable_comp hs (fun x hx => abs_le.mp (hM x hx))
    (show ContinuousOn Real.sqrt (Icc (-M) M) from Real.continuous_sqrt.continuousOn)
  simpa only [Function.comp_def, ← EuclideanSpace.real_norm_sq_eq, Real.sqrt_sq_eq_abs,
    abs_of_nonneg (norm_nonneg _)] using hh

theorem vectorRSIntegrable_inner_const {n : ℕ} {f : ℝ → EuclideanSpace ℝ (Fin n)}
    {α : ℝ → ℝ} {a b : ℝ} (hf : VectorRSIntegrable f α a b)
    (v : EuclideanSpace ℝ (Fin n)) :
    RSIntegrable (fun x => ⟪v, f x⟫_ℝ) α a b ∧
      RSIntegral (fun x => ⟪v, f x⟫_ℝ) α a b = ⟪v, VectorRSIntegral f α a b⟫_ℝ := by
  have h := vector_scalar_finite_sum Finset.univ (fun j x => v j * f x j) hf.1 hf.2.1
    (fun j _ => (rsIntegrable_const_mul (hf.2.2 j) (v j)).1)
  have hI : (∑ j, RSIntegral (fun x => v j * f x j) α a b) =
      ∑ j, v j * RSIntegral (fun x => f x j) α a b := by
    apply Finset.sum_congr rfl
    intro j _
    exact (rsIntegrable_const_mul (hf.2.2 j) (v j)).2
  rw [hI] at h
  simpa only [PiLp.inner_apply, Real.inner_apply, vectorRSIntegral_apply] using h

theorem pma6_25 : pma6_25_contract := by
  intro n f α a b hf
  have hnorm := vectorRSIntegrable_norm hf
  refine ⟨hnorm, ?_⟩
  let I := VectorRSIntegral f α a b
  have hinner := vectorRSIntegrable_inner_const hf I
  have hscaled := rsIntegrable_const_mul hnorm ‖I‖
  have hle := rsIntegral_mono hinner.1 hscaled.1 (fun x _ => real_inner_le_norm I (f x))
  rw [hinner.2, hscaled.2, real_inner_self_eq_norm_sq] at hle
  have hnonneg : 0 ≤ RSIntegral (fun x => ‖f x‖) α a b := by
    have hzero := rsIntegral_const (c := 0) hf.1 hf.2.1
    have hh := rsIntegral_mono hzero.1 hnorm (fun x _ => norm_nonneg (f x))
    simpa only [hzero.2, zero_mul] using hh
  change ‖I‖ ≤ RSIntegral (fun x => ‖f x‖) α a b
  nlinarith [norm_nonneg I]

def complexVectorEncoding : ℂ ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 2) :=
  Complex.orthonormalBasisOneI.repr

def ComplexRSIntegrable (f : ℝ → ℂ) (α : ℝ → ℝ) (a b : ℝ) : Prop :=
  RSIntegrable (fun x => (f x).re) α a b ∧ RSIntegrable (fun x => (f x).im) α a b

def ComplexRSIntegral (f : ℝ → ℂ) (α : ℝ → ℝ) (a b : ℝ) : ℂ :=
  (RSIntegral (fun x => (f x).re) α a b : ℂ) +
    (RSIntegral (fun x => (f x).im) α a b : ℂ) * Complex.I

def pma6_23_complex_contract : Prop :=
  (∀ z : ℂ, (complexVectorEncoding z) 0 = z.re ∧
    (complexVectorEncoding z) 1 = z.im ∧ ‖complexVectorEncoding z‖ = ‖z‖) ∧
  (∀ (f : ℝ → ℂ) (α : ℝ → ℝ) (a b : ℝ),
    (ComplexRSIntegrable f α a b ↔ VectorRSIntegrable (complexVectorEncoding ∘ f) α a b) ∧
    complexVectorEncoding (ComplexRSIntegral f α a b) =
      VectorRSIntegral (complexVectorEncoding ∘ f) α a b ∧
    ‖ComplexRSIntegral f α a b‖ = ‖VectorRSIntegral (complexVectorEncoding ∘ f) α a b‖)

def pma6_25_complex_contract : Prop :=
  ∀ (f : ℝ → ℂ) (α : ℝ → ℝ) (a b : ℝ), ComplexRSIntegrable f α a b →
    RSIntegrable (fun x => ‖f x‖) α a b ∧
      ‖ComplexRSIntegral f α a b‖ ≤ RSIntegral (fun x => ‖f x‖) α a b

@[simp] theorem complexVectorEncoding_re (z : ℂ) : (complexVectorEncoding z) 0 = z.re := rfl

@[simp] theorem complexVectorEncoding_im (z : ℂ) : (complexVectorEncoding z) 1 = z.im := rfl

@[simp] theorem complexVectorEncoding_norm (z : ℂ) : ‖complexVectorEncoding z‖ = ‖z‖ :=
  complexVectorEncoding.norm_map z

theorem complexRSIntegrable_iff_vector (f : ℝ → ℂ) (α : ℝ → ℝ) (a b : ℝ) :
    ComplexRSIntegrable f α a b ↔ VectorRSIntegrable (complexVectorEncoding ∘ f) α a b := by
  constructor
  · intro hf
    refine ⟨hf.1.1, hf.1.2.2.1, ?_⟩
    intro j
    fin_cases j
    · exact hf.1
    · exact hf.2
  · intro hf
    exact ⟨hf.2.2 0, hf.2.2 1⟩

theorem complexRSIntegral_encoding (f : ℝ → ℂ) (α : ℝ → ℝ) (a b : ℝ) :
    complexVectorEncoding (ComplexRSIntegral f α a b) =
      VectorRSIntegral (complexVectorEncoding ∘ f) α a b := by
  apply PiLp.ext
  intro j
  fin_cases j <;>
    simp [ComplexRSIntegral, vectorRSIntegral_apply, Function.comp_def]

theorem complexRSIntegral_norm (f : ℝ → ℂ) (α : ℝ → ℝ) (a b : ℝ) :
    ‖ComplexRSIntegral f α a b‖ = ‖VectorRSIntegral (complexVectorEncoding ∘ f) α a b‖ := by
  rw [← complexRSIntegral_encoding, complexVectorEncoding_norm]

theorem pma6_23_complex : pma6_23_complex_contract := by
  refine ⟨fun z => ⟨rfl, rfl, complexVectorEncoding_norm z⟩, ?_⟩
  intro f α a b
  exact ⟨complexRSIntegrable_iff_vector f α a b, complexRSIntegral_encoding f α a b,
    complexRSIntegral_norm f α a b⟩

theorem pma6_25_complex : pma6_25_complex_contract := by
  intro f α a b hf
  have hh := pma6_25 2 (complexVectorEncoding ∘ f) α a b
    ((complexRSIntegrable_iff_vector f α a b).mp hf)
  rw [← complexRSIntegral_norm f α a b] at hh
  simpa only [Function.comp_def, complexVectorEncoding_norm] using hh

theorem complexRSIntegral_ftc {F f : ℝ → ℂ} {a b : ℝ} (hab : a < b)
    (hd : ∀ x ∈ Icc a b, HasDerivWithinAt F (f x) (Icc a b) x)
    (hf : ComplexRSIntegrable f id a b) : ComplexRSIntegral f id a b = F b - F a := by
  have hr := pma6_21 (fun x => (F x).re) (fun x => (f x).re) a b hab
    (fun x hx => ((Chapter05.complex_derivative_components F (f x) (Icc a b) x).mp (hd x hx)).1) hf.1
  have hi := pma6_21 (fun x => (F x).im) (fun x => (f x).im) a b hab
    (fun x hx => ((Chapter05.complex_derivative_components F (f x) (Icc a b) x).mp (hd x hx)).2) hf.2
  rw [show (fun x : ℝ => x) = id from rfl] at hr hi
  apply Complex.ext
  · simpa [ComplexRSIntegral] using hr
  · simpa [ComplexRSIntegral] using hi

theorem complexRSIntegrable_add {f g : ℝ → ℂ} {α : ℝ → ℝ} {a b : ℝ}
    (hf : ComplexRSIntegrable f α a b) (hg : ComplexRSIntegrable g α a b) :
    ComplexRSIntegrable (fun x => f x + g x) α a b ∧
      ComplexRSIntegral (fun x => f x + g x) α a b =
        ComplexRSIntegral f α a b + ComplexRSIntegral g α a b := by
  have hr := rsIntegrable_add hf.1 hg.1
  have hi := rsIntegrable_add hf.2 hg.2
  refine ⟨⟨hr.1, hi.1⟩, ?_⟩
  apply Complex.ext
  · simpa [ComplexRSIntegral] using hr.2
  · simpa [ComplexRSIntegral] using hi.2

theorem complexRSIntegrable_const_mul {f : ℝ → ℂ} {α : ℝ → ℝ} {a b : ℝ}
    (hf : ComplexRSIntegrable f α a b) (c : ℂ) :
    ComplexRSIntegrable (fun x => c * f x) α a b ∧
      ComplexRSIntegral (fun x => c * f x) α a b = c * ComplexRSIntegral f α a b := by
  have hrr := rsIntegrable_const_mul hf.1 c.re
  have hri := rsIntegrable_const_mul hf.2 (-c.im)
  have hir := rsIntegrable_const_mul hf.2 c.re
  have hii := rsIntegrable_const_mul hf.1 c.im
  have hr := rsIntegrable_add hrr.1 hri.1
  have hi := rsIntegrable_add hir.1 hii.1
  have hre : (fun x => (c * f x).re) = (fun x => c.re * (f x).re + -c.im * (f x).im) := by
    funext x
    simp only [Complex.mul_re, sub_eq_add_neg, neg_mul]
  have him : (fun x => (c * f x).im) = (fun x => c.re * (f x).im + c.im * (f x).re) := rfl
  rw [hrr.2, hri.2] at hr
  rw [hir.2, hii.2] at hi
  refine ⟨⟨hre ▸ hr.1, him ▸ hi.1⟩, ?_⟩
  apply Complex.ext
  · simpa [ComplexRSIntegral, Complex.mul_re, Complex.mul_im, sub_eq_add_neg] using hr.2
  · simpa [ComplexRSIntegral, Complex.mul_re, Complex.mul_im] using hi.2

theorem vector_integrability_zero_dimension_guard_probe :
    ¬ VectorRSIntegrable (fun _ => (0 : EuclideanSpace ℝ (Fin 0))) id 1 0 := by
  intro h
  have hh := h.1
  norm_num at hh

theorem complex_imaginary_constant_probe :
    ComplexRSIntegrable (fun _ : ℝ => Complex.I) id 0 1 ∧
      ComplexRSIntegral (fun _ : ℝ => Complex.I) id 0 1 = Complex.I := by
  have hr := rsIntegral_const (c := (0 : ℝ)) (show (0 : ℝ) ≤ 1 by norm_num)
    (show MonotoneOn (id : ℝ → ℝ) (Icc 0 1) from fun _ _ _ _ h => h)
  have hi := rsIntegral_const (c := (1 : ℝ)) (show (0 : ℝ) ≤ 1 by norm_num)
    (show MonotoneOn (id : ℝ → ℝ) (Icc 0 1) from fun _ _ _ _ h => h)
  refine ⟨⟨hr.1, hi.1⟩, ?_⟩
  simp only [ComplexRSIntegral, Complex.I_re, Complex.I_im, hr.2, hi.2, id_eq]
  norm_num

#print axioms pma6_23
#print axioms pma6_24
#print axioms pma6_25
#print axioms pma6_23_complex
#print axioms pma6_25_complex
#print axioms complexRSIntegral_ftc
#print axioms complexRSIntegrable_add
#print axioms complexRSIntegrable_const_mul
#print axioms vector_integrability_zero_dimension_guard_probe
#print axioms complex_imaginary_constant_probe

end Rudin.PMA.Chapter06
