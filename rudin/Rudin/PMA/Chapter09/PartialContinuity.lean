import Rudin.PMA.Chapter09.ContinuousDifferentiability

/-! # Finite-coordinate support for PMA 9.21 -/
noncomputable section
open Set Filter
open scoped Topology BigOperators
namespace Rudin.PMA.Chapter09

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The linear map whose columns are the prescribed coordinate derivatives. -/
def coordinateDerivative {n : ℕ} (p : Fin n → F) : (Fin n → ℝ) →L[ℝ] F :=
  ∑ i, (ContinuousLinearMap.proj i : (Fin n → ℝ) →L[ℝ] ℝ).smulRight (p i)

lemma coordinateDerivative_apply {n : ℕ} (p : Fin n → F) (v : Fin n → ℝ) :
    coordinateDerivative p v = ∑ i, v i • p i := by
  simp [coordinateDerivative]

lemma continuous_coordinateDerivative {n : ℕ} :
    Continuous (coordinateDerivative : (Fin n → F) → ((Fin n → ℝ) →L[ℝ] F)) := by
  unfold coordinateDerivative
  fun_prop

lemma hasFDerivAt_coordinateDerivative {n : ℕ} {f : (Fin n → ℝ) → F}
    {p : Fin n → F} {x : Fin n → ℝ} (hf : DifferentiableAt ℝ f x)
    (hp : ∀ i, HasDerivAt (fun t => f (Function.update x i t)) (p i) (x i)) :
    HasFDerivAt f (coordinateDerivative p) x := by
  have hvalue (i : Fin n) : fderiv ℝ f x (Pi.single i 1) = p i := by
    have hf' : HasFDerivAt f (fderiv ℝ f x) (Function.update x i (x i)) := by simpa using hf.hasFDerivAt
    have h := hf'.comp_hasDerivAt (x i) (hasDerivAt_update x i (x i))
    simpa using h.unique (hp i)
  have hmap : fderiv ℝ f x = coordinateDerivative p := by
    ext v
    rw [← (Pi.basisFun ℝ (Fin n)).sum_repr v]
    simp only [map_sum, map_smul, Pi.basisFun_repr, Pi.basisFun_apply]
    simp only [hvalue]
    simp [coordinateDerivative]
  exact hmap ▸ hf.hasFDerivAt

/-- Continuous coordinate partial derivatives give a total derivative on an open set.
The finite-product norm is used only inside this auxiliary proof. -/
theorem hasFDerivAt_of_continuous_partials (n : ℕ)
    (f : (Fin n → ℝ) → F) (s : Set (Fin n → ℝ)) (hs : IsOpen s)
    (p : Fin n → (Fin n → ℝ) → F)
    (hp : ∀ i, ContinuousOn (p i) s)
    (hd : ∀ x ∈ s, ∀ i, HasDerivAt (fun t => f (Function.update x i t)) (p i x) (x i)) :
    ∀ x ∈ s, HasFDerivAt f (coordinateDerivative (fun i => p i x)) x := by
  induction n with
  | zero =>
    intro x hx
    have heq : f = fun _ => f x := funext fun y => congrArg f (Subsingleton.elim y x)
    rw [heq]
    simpa [coordinateDerivative] using (hasFDerivAt_const (f x) x)
  | succ n ih =>
    intro x hx
    let e := Fin.consEquivL ℝ (fun _ : Fin (n + 1) => ℝ)
    let g : ℝ → (Fin n → ℝ) → F := fun a b => f (Fin.cons a b)
    let p₁ : ℝ → (Fin n → ℝ) → ℝ →L[ℝ] F :=
      fun a b => (1 : ℝ →L[ℝ] ℝ).smulRight (p 0 (Fin.cons a b))
    let p₂ : ℝ → (Fin n → ℝ) → (Fin n → ℝ) →L[ℝ] F :=
      fun a b => coordinateDerivative (fun i => p i.succ (Fin.cons a b))
    have he : e (e.symm x) = x := e.apply_symm_apply x
    have hne : e ⁻¹' s ∈ 𝓝 (e.symm x) :=
      (hs.preimage e.continuous).mem_nhds (by simpa using hx)
    have d₁ : ∀ᶠ v in 𝓝 (e.symm x), HasFDerivAt (g · v.2) (p₁ v.1 v.2) v.1 := by
      filter_upwards [hne] with v hv
      have h := (hd (e v) hv 0).hasFDerivAt
      have hfun : (fun t => f (Function.update (e v) 0 t)) = (g · v.2) := by
        funext t
        congr 1
        ext j
        refine Fin.cases ?_ (fun j => ?_) j <;> simp [e]
      rw [hfun] at h
      exact h
    have d₂ : ∀ᶠ v in 𝓝 (e.symm x), HasFDerivAt (g v.1 ·) (p₂ v.1 v.2) v.2 := by
      filter_upwards [hne] with v hv
      let s' : Set (Fin n → ℝ) := {b | Fin.cons v.1 b ∈ s}
      have hs' : IsOpen s' := by
        change IsOpen ((fun b : Fin n → ℝ => Fin.cons v.1 b) ⁻¹' s)
        exact hs.preimage (by fun_prop)
      apply ih (g v.1) s' hs' (fun i b => p i.succ (Fin.cons v.1 b))
      · intro i
        exact (hp i.succ).comp (by fun_prop) (fun _ h => h)
      · intro b hb i
        have h := hd (Fin.cons v.1 b) hb i.succ
        have hfun : (fun t => f (Function.update (Fin.cons v.1 b) i.succ t)) =
            (fun t => g v.1 (Function.update b i t)) := by
          funext t
          congr 1
          ext j
          refine Fin.cases ?_ (fun j => ?_) j <;> simp [Function.update_apply, Ne.symm (Fin.succ_ne_zero i)]
        simpa only [hfun, Fin.cons_succ] using h
      · exact hv
    have c₁ : ContinuousAt (fun v : ℝ × (Fin n → ℝ) => p₁ v.1 v.2) (e.symm x) := by
      have hc : ContinuousAt (fun v => p 0 (e v)) (e.symm x) :=
        ((hp 0 x hx).continuousAt (hs.mem_nhds hx)).comp_of_eq e.continuous.continuousAt he
      exact (ContinuousLinearMap.smulRightL ℝ ℝ F (1 : ℝ →L[ℝ] ℝ)).continuous.continuousAt.comp hc
    have c₂ : ContinuousAt (fun v : ℝ × (Fin n → ℝ) => p₂ v.1 v.2) (e.symm x) := by
      apply continuous_coordinateDerivative.continuousAt.comp
      apply continuousAt_pi.mpr
      intro i
      exact ((hp i.succ x hx).continuousAt (hs.mem_nhds hx)).comp_of_eq
        e.continuous.continuousAt he
    have hg := (hasStrictFDerivAt_uncurry_coprod (f := g) (f₁ := p₁) (f₂ := p₂) d₁ d₂ c₁ c₂).hasFDerivAt
    have hf : DifferentiableAt ℝ f x := by
      have h := hg.differentiableAt.comp x e.symm.differentiableAt
      change DifferentiableAt ℝ (fun z => f (e (e.symm z))) x at h
      simpa only [e.apply_symm_apply] using h
    exact hasFDerivAt_coordinateDerivative hf (hd x hx)

/-- The continuously varying columns give a continuously varying total derivative. -/
theorem isC1On_of_continuous_partials (n : ℕ)
    (f : (Fin n → ℝ) → F) (s : Set (Fin n → ℝ)) (hs : IsOpen s)
    (p : Fin n → (Fin n → ℝ) → F)
    (hp : ∀ i, ContinuousOn (p i) s)
    (hd : ∀ x ∈ s, ∀ i, HasDerivAt (fun t => f (Function.update x i t)) (p i x) (x i)) :
    IsC1On f s := by
  have h := hasFDerivAt_of_continuous_partials n f s hs p hp hd
  refine ⟨fun x hx => (h x hx).differentiableAt, ?_⟩
  have hc : ContinuousOn (fun x => coordinateDerivative (fun i => p i x)) s :=
    continuous_coordinateDerivative.comp_continuousOn (continuousOn_pi.mpr hp)
  exact hc.congr (fun x hx => (h x hx).fderiv)

end Rudin.PMA.Chapter09
