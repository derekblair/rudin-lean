import Mathlib

open Filter Set
open scoped Topology BoundedContinuousFunction

namespace Rudin.PMA.Chapter07

universe u

/-- Source function algebras are nonempty and need not contain a unit. -/
def IsFunctionAlgebra {X 𝕜 : Type*} [Field 𝕜] (A : Set (X → 𝕜)) : Prop :=
  A.Nonempty ∧
  (∀ f ∈ A, ∀ g ∈ A, (fun x => f x + g x) ∈ A) ∧
  (∀ f ∈ A, ∀ g ∈ A, (fun x => f x * g x) ∈ A) ∧
  (∀ c : 𝕜, ∀ f ∈ A, (fun x => c * f x) ∈ A)

/-- Uniform closure is explicitly the set of sequential uniform limits. -/
def AlgebraUniformClosure {X Y : Type*} [UniformSpace Y]
    (A : Set (X → Y)) : Set (X → Y) :=
  {f | ∃ F : ℕ → X → Y, (∀ n, F n ∈ A) ∧ TendstoUniformly F f atTop}

/-- Sequential closedness in uniform convergence, without continuity premises. -/
def IsAlgebraUniformlyClosed {X Y : Type*} [UniformSpace Y]
    (A : Set (X → Y)) : Prop :=
  ∀ (F : ℕ → X → Y) (f : X → Y),
    (∀ n, F n ∈ A) → TendstoUniformly F f atTop → f ∈ A

def AlgebraFunctionBounded {X Y : Type*} [NormedAddCommGroup Y] (f : X → Y) : Prop :=
  ∃ M : ℝ, ∀ x, ‖f x‖ ≤ M

def PolynomialFunctionFamily {X 𝕜 : Type*} [CommSemiring 𝕜]
    (v : X → 𝕜) : Set (X → 𝕜) :=
  {f | ∃ p : Polynomial 𝕜, ∀ x, f x = p.eval (v x)}

def EvenPolynomialFunctionFamily (S : Set ℝ) : Set (S → ℝ) :=
  {f | ∃ p : Polynomial ℝ, (∀ x : ℝ, p.eval (-x) = p.eval x) ∧
    ∀ x : S, f x = p.eval (x : ℝ)}

def SeparatesFunctionPoints {X Y : Type*} (A : Set (X → Y)) : Prop :=
  ∀ ⦃x y : X⦄, x ≠ y → ∃ f ∈ A, f x ≠ f y

def FunctionVanishesNowhere {X Y : Type*} [Zero Y] (A : Set (X → Y)) : Prop :=
  ∀ x, ∃ f ∈ A, f x ≠ 0

def IsSelfAdjointFunctionFamily {X : Type*} (A : Set (X → ℂ)) : Prop :=
  ∀ f ∈ A, (fun x => star (f x)) ∈ A

/-- PMA-7.26: polynomial sequences, with full complex and real coverage. -/
def pma7_26_contract : Prop :=
  (∀ (a b : ℝ), a ≤ b → ∀ f : ℝ → ℂ, ContinuousOn f (Icc a b) →
    ∃ P : ℕ → Polynomial ℂ,
      TendstoUniformlyOn (fun n (x : ℝ) => (P n).eval (x : ℂ)) f atTop (Icc a b)) ∧
  (∀ (a b : ℝ), a ≤ b → ∀ f : ℝ → ℝ, ContinuousOn f (Icc a b) →
    ∃ P : ℕ → Polynomial ℝ,
      TendstoUniformlyOn (fun n x => (P n).eval x) f atTop (Icc a b))

/-- PMA-7.27: exact zero at the origin for every approximating polynomial. -/
def pma7_27_contract : Prop :=
  ∀ a : ℝ, 0 ≤ a → ∃ P : ℕ → Polynomial ℝ,
    (∀ n, (P n).eval 0 = 0) ∧
    TendstoUniformlyOn (fun n x => (P n).eval x) (fun x : ℝ => |x|)
      atTop (Icc (-a) a)

/-- PMA-7.28: nonunital algebra and sequential closure definitions and polynomial examples. -/
def pma7_28_contract : Prop :=
  (∀ (X : Type u) (A : Set (X → ℂ)), IsFunctionAlgebra A ↔
    A.Nonempty ∧
    (∀ f ∈ A, ∀ g ∈ A, (fun x => f x + g x) ∈ A) ∧
    (∀ f ∈ A, ∀ g ∈ A, (fun x => f x * g x) ∈ A) ∧
    (∀ c : ℂ, ∀ f ∈ A, (fun x => c * f x) ∈ A)) ∧
  (∀ (X : Type u) (A : Set (X → ℝ)), IsFunctionAlgebra A ↔
    A.Nonempty ∧
    (∀ f ∈ A, ∀ g ∈ A, (fun x => f x + g x) ∈ A) ∧
    (∀ f ∈ A, ∀ g ∈ A, (fun x => f x * g x) ∈ A) ∧
    (∀ c : ℝ, ∀ f ∈ A, (fun x => c * f x) ∈ A)) ∧
  (∀ (X : Type u) (A : Set (X → ℂ)), IsAlgebraUniformlyClosed A ↔
    ∀ (F : ℕ → X → ℂ) (f : X → ℂ),
      (∀ n, F n ∈ A) → TendstoUniformly F f atTop → f ∈ A) ∧
  (∀ (X : Type u) (A : Set (X → ℝ)), IsAlgebraUniformlyClosed A ↔
    ∀ (F : ℕ → X → ℝ) (f : X → ℝ),
      (∀ n, F n ∈ A) → TendstoUniformly F f atTop → f ∈ A) ∧
  (∀ (X : Type u) (A : Set (X → ℂ)) (f : X → ℂ), f ∈ AlgebraUniformClosure A ↔
    ∃ F : ℕ → X → ℂ, (∀ n, F n ∈ A) ∧ TendstoUniformly F f atTop) ∧
  (∀ (X : Type u) (A : Set (X → ℝ)) (f : X → ℝ), f ∈ AlgebraUniformClosure A ↔
    ∃ F : ℕ → X → ℝ, (∀ n, F n ∈ A) ∧ TendstoUniformly F f atTop) ∧
  (∀ (X : Type u) (v : X → ℝ), IsFunctionAlgebra (PolynomialFunctionFamily v)) ∧
  (∀ (X : Type u) (v : X → ℂ), IsFunctionAlgebra (PolynomialFunctionFamily v)) ∧
  (∀ (a b : ℝ), a ≤ b →
    AlgebraUniformClosure (PolynomialFunctionFamily (fun x : Icc a b => (x : ℝ))) =
      {f : Icc a b → ℝ | Continuous f}) ∧
  (∀ (a b : ℝ), a ≤ b →
    AlgebraUniformClosure (PolynomialFunctionFamily (fun x : Icc a b => ((x : ℝ) : ℂ))) =
      {f : Icc a b → ℂ | Continuous f})

/-- PMA-7.29: arbitrary domains; every algebra member has its own bound. -/
def pma7_29_contract : Prop :=
  (∀ (X : Type u) (A : Set (X → ℝ)), IsFunctionAlgebra A →
    (∀ f ∈ A, AlgebraFunctionBounded f) →
    IsFunctionAlgebra (AlgebraUniformClosure A) ∧
      IsAlgebraUniformlyClosed (AlgebraUniformClosure A) ∧
      ∀ f ∈ AlgebraUniformClosure A, AlgebraFunctionBounded f) ∧
  (∀ (X : Type u) (A : Set (X → ℂ)), IsFunctionAlgebra A →
    (∀ f ∈ A, AlgebraFunctionBounded f) →
    IsFunctionAlgebra (AlgebraUniformClosure A) ∧
      IsAlgebraUniformlyClosed (AlgebraUniformClosure A) ∧
      ∀ f ∈ AlgebraUniformClosure A, AlgebraFunctionBounded f)

/-- PMA-7.30: separation, point-dependent nonzero witnesses, and polynomial examples. -/
def pma7_30_contract : Prop :=
  (∀ (X : Type u) (A : Set (X → ℂ)), SeparatesFunctionPoints A ↔
    ∀ x y : X, x ≠ y → ∃ f ∈ A, f x ≠ f y) ∧
  (∀ (X : Type u) (A : Set (X → ℝ)), SeparatesFunctionPoints A ↔
    ∀ x y : X, x ≠ y → ∃ f ∈ A, f x ≠ f y) ∧
  (∀ (X : Type u) (A : Set (X → ℂ)), FunctionVanishesNowhere A ↔
    ∀ x, ∃ f ∈ A, f x ≠ 0) ∧
  (∀ (X : Type u) (A : Set (X → ℝ)), FunctionVanishesNowhere A ↔
    ∀ x, ∃ f ∈ A, f x ≠ 0) ∧
  SeparatesFunctionPoints (PolynomialFunctionFamily (fun x : ℝ => x)) ∧
  FunctionVanishesNowhere (PolynomialFunctionFamily (fun x : ℝ => x)) ∧
  SeparatesFunctionPoints (PolynomialFunctionFamily (fun x : ℝ => (x : ℂ))) ∧
  FunctionVanishesNowhere (PolynomialFunctionFamily (fun x : ℝ => (x : ℂ))) ∧
  ¬ SeparatesFunctionPoints (EvenPolynomialFunctionFamily (Icc (-1) 1))

/-- PMA-7.31: exact interpolation without unit, compactness, or continuity assumptions. -/
def pma7_31_contract : Prop :=
  (∀ (X : Type u) (A : Set (X → ℝ)), IsFunctionAlgebra A →
    SeparatesFunctionPoints A → FunctionVanishesNowhere A →
    ∀ x y : X, x ≠ y → ∀ v w : ℝ, ∃ f ∈ A, f x = v ∧ f y = w) ∧
  (∀ (X : Type u) (A : Set (X → ℂ)), IsFunctionAlgebra A →
    SeparatesFunctionPoints A → FunctionVanishesNowhere A →
    ∀ x y : X, x ≠ y → ∀ v w : ℂ, ∃ f ∈ A, f x = v ∧ f y = w)

/-- PMA-7.32: nonunital real Stone-Weierstrass on every compact metric space. -/
def pma7_32_contract : Prop :=
  ∀ (X : Type u) [MetricSpace X] [CompactSpace X] (A : Set (X → ℝ)),
    IsFunctionAlgebra A → (∀ f ∈ A, Continuous f) →
    SeparatesFunctionPoints A → FunctionVanishesNowhere A →
    AlgebraUniformClosure A = {f : X → ℝ | Continuous f}

/-- PMA-7.33: self-adjoint complex theorem and a verified failure without that premise. -/
def pma7_33_contract : Prop :=
  (∀ (X : Type u) (A : Set (X → ℂ)), IsSelfAdjointFunctionFamily A ↔
    ∀ f ∈ A, (fun x => star (f x)) ∈ A) ∧
  (∀ (X : Type u) [MetricSpace X] [CompactSpace X] (A : Set (X → ℂ)),
    IsFunctionAlgebra A → (∀ f ∈ A, Continuous f) →
    SeparatesFunctionPoints A → FunctionVanishesNowhere A →
    IsSelfAdjointFunctionFamily A →
    AlgebraUniformClosure A = {f : X → ℂ | Continuous f}) ∧
  (∃ A : Set (Metric.closedBall (0 : ℂ) 1 → ℂ),
    IsFunctionAlgebra A ∧ (∀ f ∈ A, Continuous f) ∧
    SeparatesFunctionPoints A ∧ FunctionVanishesNowhere A ∧
    ¬ IsSelfAdjointFunctionFamily A ∧
    ∃ f : Metric.closedBall (0 : ℂ) 1 → ℂ,
      Continuous f ∧ f ∉ AlgebraUniformClosure A)

theorem polynomialFunctionFamily_isAlgebra {X 𝕜 : Type*} [Field 𝕜]
    (v : X → 𝕜) : IsFunctionAlgebra (PolynomialFunctionFamily v) := by
  refine ⟨⟨fun _ => 0, 0, ?_⟩, ?_, ?_, ?_⟩
  · intro x
    simp
  · rintro f ⟨p, hp⟩ g ⟨q, hq⟩
    exact ⟨p + q, fun x => by simp [hp x, hq x]⟩
  · rintro f ⟨p, hp⟩ g ⟨q, hq⟩
    exact ⟨p * q, fun x => by simp [hp x, hq x]⟩
  · rintro c f ⟨p, hp⟩
    exact ⟨Polynomial.C c * p, fun x => by simp [hp x]⟩

theorem polynomialFunctionFamily_separates {X 𝕜 : Type*} [Field 𝕜]
    (v : X → 𝕜) (hv : Function.Injective v) :
    SeparatesFunctionPoints (PolynomialFunctionFamily v) := by
  intro x y hxy
  exact ⟨v, ⟨Polynomial.X, fun z => by simp⟩, fun h => hxy (hv h)⟩

theorem polynomialFunctionFamily_nonvanishing {X 𝕜 : Type*} [Field 𝕜]
    (v : X → 𝕜) : FunctionVanishesNowhere (PolynomialFunctionFamily v) := by
  intro x
  exact ⟨fun _ => 1, ⟨1, fun _ => by simp⟩, one_ne_zero⟩

theorem evenPolynomialFunctionFamily_not_separates :
    ¬ SeparatesFunctionPoints (EvenPolynomialFunctionFamily (Icc (-1) 1)) := by
  intro h
  let x : Icc (-1 : ℝ) 1 := ⟨-1, by norm_num⟩
  let y : Icc (-1 : ℝ) 1 := ⟨1, by norm_num⟩
  have hxy : x ≠ y := by
    intro e
    have := congrArg Subtype.val e
    norm_num [x, y] at this
  rcases h hxy with ⟨f, ⟨p, hp, hf⟩, hne⟩
  apply hne
  rw [hf x, hf y]
  exact hp 1

-- PMA-7.30
theorem pma7_30 : pma7_30_contract.{u} := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, evenPolynomialFunctionFamily_not_separates⟩
  · intro X A
    rfl
  · intro X A
    rfl
  · intro X A
    rfl
  · intro X A
    rfl
  · exact polynomialFunctionFamily_separates _ Function.injective_id
  · exact polynomialFunctionFamily_nonvanishing _
  · exact polynomialFunctionFamily_separates _ Complex.ofReal_injective
  · exact polynomialFunctionFamily_nonvanishing _

theorem functionAlgebra_interpolate {X 𝕜 : Type*} [Field 𝕜]
    {A : Set (X → 𝕜)} (hA : IsFunctionAlgebra A)
    (hsep : SeparatesFunctionPoints A) (hnv : FunctionVanishesNowhere A)
    (x y : X) (hxy : x ≠ y) (v w : 𝕜) :
    ∃ f ∈ A, f x = v ∧ f y = w := by
  rcases hsep hxy with ⟨h, hh, hne⟩
  rcases hnv x with ⟨f, hf, hfx⟩
  rcases hnv y with ⟨g, hg, hgy⟩
  let p : X → 𝕜 := fun z => f z * (h z - h y)
  let q : X → 𝕜 := fun z => g z * (h z - h x)
  have hp : p ∈ A := by
    convert hA.2.1 _ (hA.2.2.1 _ hf _ hh) _ (hA.2.2.2 (-h y) _ hf) using 1
    ext z
    dsimp [p]
    ring
  have hq : q ∈ A := by
    convert hA.2.1 _ (hA.2.2.1 _ hg _ hh) _ (hA.2.2.2 (-h x) _ hg) using 1
    ext z
    dsimp [q]
    ring
  have hpx : p x ≠ 0 := mul_ne_zero hfx (sub_ne_zero.mpr hne)
  have hqy : q y ≠ 0 := mul_ne_zero hgy (sub_ne_zero.mpr hne.symm)
  refine ⟨fun z => (v / p x) * p z + (w / q y) * q z,
    hA.2.1 _ (hA.2.2.2 _ _ hp) _ (hA.2.2.2 _ _ hq), ?_, ?_⟩
  · simp [p, q, div_mul_cancel₀ _ hpx]
  · simp [p, q]
    field_simp [hgy, sub_ne_zero.mpr hne.symm]

-- PMA-7.31
theorem pma7_31 : pma7_31_contract.{u} := by
  constructor <;> intro X A hA hsep hnv x y hxy v w
  · exact functionAlgebra_interpolate hA hsep hnv x y hxy v w
  · exact functionAlgebra_interpolate hA hsep hnv x y hxy v w

theorem exists_uniform_approximating_sequence {J X Y : Type*} [PseudoMetricSpace Y]
    (G : J → X → Y) (f : X → Y) (S : Set X)
    (h : ∀ ε > 0, ∃ j, ∀ x ∈ S, dist (G j x) (f x) < ε) :
    ∃ P : ℕ → J, TendstoUniformlyOn (fun n => G (P n)) f atTop S := by
  have hchoice (n : ℕ) : ∃ j, ∀ x ∈ S,
      dist (G j x) (f x) < 1 / ((n : ℝ) + 1) := h _ (by positivity)
  choose P hP using hchoice
  refine ⟨P, Metric.tendstoUniformlyOn_iff.mpr ?_⟩
  intro ε hε
  rcases exists_nat_one_div_lt hε with ⟨N, hN⟩
  filter_upwards [eventually_ge_atTop N] with n hn x hx
  have hle : 1 / ((n : ℝ) + 1) ≤ 1 / ((N : ℝ) + 1) :=
    one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.add_le_add_right hn 1)
  rw [dist_comm]
  exact (hP n x hx).trans_le hle |>.trans hN

theorem complex_polynomial_near {a b : ℝ} {f : ℝ → ℂ}
    (hf : ContinuousOn f (Icc a b)) (ε : ℝ) (hε : 0 < ε) :
    ∃ p : Polynomial ℂ, ∀ x ∈ Icc a b, ‖p.eval (x : ℂ) - f x‖ < ε := by
  rcases exists_polynomial_near_of_continuousOn a b (fun x => (f x).re)
    (Complex.continuous_re.comp_continuousOn hf) (ε / 2) (half_pos hε) with ⟨p, hp⟩
  rcases exists_polynomial_near_of_continuousOn a b (fun x => (f x).im)
    (Complex.continuous_im.comp_continuousOn hf) (ε / 2) (half_pos hε) with ⟨q, hq⟩
  refine ⟨p.map Complex.ofRealHom + Polynomial.C Complex.I * q.map Complex.ofRealHom, ?_⟩
  intro x hx
  have heval : (p.map Complex.ofRealHom + Polynomial.C Complex.I *
      q.map Complex.ofRealHom).eval (x : ℂ) =
      ((p.eval x : ℝ) : ℂ) + Complex.I * ((q.eval x : ℝ) : ℂ) := by
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_map]
    change p.eval₂ Complex.ofRealHom (Complex.ofRealHom x) +
      Complex.I * q.eval₂ Complex.ofRealHom (Complex.ofRealHom x) = _
    rw [Polynomial.eval₂_at_apply, Polynomial.eval₂_at_apply]
    rfl
  rw [heval]
  have hnorm := Complex.norm_le_abs_re_add_abs_im
    (((p.eval x : ℝ) : ℂ) + Complex.I * ((q.eval x : ℝ) : ℂ) - f x)
  simp only [Complex.sub_re, Complex.add_re, Complex.ofReal_re, Complex.mul_re,
    Complex.I_re, Complex.ofReal_im, Complex.I_im, zero_mul, one_mul, sub_zero,
    add_zero, Complex.sub_im, Complex.add_im, Complex.mul_im, zero_add] at hnorm
  linarith [hp x hx, hq x hx]

-- PMA-7.26
theorem pma7_26 : pma7_26_contract := by
  constructor
  · intro a b _hab f hf
    apply exists_uniform_approximating_sequence (fun (p : Polynomial ℂ) (x : ℝ) => p.eval (x : ℂ))
    intro ε hε
    simpa only [dist_eq_norm] using complex_polynomial_near hf ε hε
  · intro a b _hab f hf
    apply exists_uniform_approximating_sequence (fun (p : Polynomial ℝ) (x : ℝ) => p.eval x)
    intro ε hε
    simpa only [Real.dist_eq] using exists_polynomial_near_of_continuousOn a b f hf ε hε

-- PMA-7.27
theorem pma7_27 : pma7_27_contract := by
  intro a ha
  rcases pma7_26.2 (-a) a (by linarith) (fun x : ℝ => |x|)
    continuous_abs.continuousOn with ⟨P, hP⟩
  have h0 : Tendsto (fun n => (P n).eval 0) atTop (𝓝 (0 : ℝ)) := by
    simpa only [abs_zero] using hP.tendsto_at (show (0 : ℝ) ∈ Icc (-a) a by constructor <;> linarith)
  refine ⟨fun n => P n - Polynomial.C ((P n).eval 0), ?_, ?_⟩
  · intro n
    simp
  · have ht : TendstoUniformlyOn (fun n x => (P n).eval x - (P n).eval 0)
        (fun x : ℝ => |x| - 0) atTop (Icc (-a) a) :=
      hP.sub (h0.tendstoUniformlyOn_const (s := Icc (-a) a))
    simpa only [Polynomial.eval_sub, Polynomial.eval_C, sub_zero] using ht

theorem algebraUniformClosure_continuous {X Y : Type*} [TopologicalSpace X]
    [UniformSpace Y] {A : Set (X → Y)} (hA : ∀ f ∈ A, Continuous f)
    {f : X → Y} (hf : f ∈ AlgebraUniformClosure A) : Continuous f := by
  rcases hf with ⟨F, hF, hlim⟩
  exact hlim.continuous (Filter.Eventually.of_forall (fun n => hA _ (hF n))).frequently

theorem polynomialClosure_interval {𝕜 : Type*} [NormedField 𝕜]
    (a b : ℝ) (v : ℝ → 𝕜) (hv : Continuous v)
    (hApprox : ∀ g : ℝ → 𝕜, ContinuousOn g (Icc a b) →
      ∃ P : ℕ → Polynomial 𝕜,
        TendstoUniformlyOn (fun n x => (P n).eval (v x)) g atTop (Icc a b)) :
    AlgebraUniformClosure (PolynomialFunctionFamily (fun x : Icc a b => v x)) =
      {f : Icc a b → 𝕜 | Continuous f} := by
  classical
  ext f
  constructor
  · apply algebraUniformClosure_continuous
    rintro g ⟨p, hp⟩
    have hg : g = fun x : Icc a b => p.eval (v x) := funext hp
    rw [hg]
    exact p.continuous.comp (hv.comp continuous_subtype_val)
  · intro hf
    let g : ℝ → 𝕜 := fun x => if hx : x ∈ Icc a b then f ⟨x, hx⟩ else 0
    have hgval (x : Icc a b) : g x = f x := by
      dsimp [g]
      rw [dite_eq_left x.property]
    have hg : ContinuousOn g (Icc a b) := by
      rw [continuousOn_iff_continuous_domRestrict]
      have hgf : (Icc a b).domRestrict g = f := funext hgval
      rw [hgf]
      exact hf
    rcases hApprox g hg with ⟨P, hP⟩
    refine ⟨fun n x => (P n).eval (v x), fun n => ⟨P n, fun _ => rfl⟩, ?_⟩
    apply Metric.tendstoUniformly_iff.mpr
    intro ε hε
    filter_upwards [Metric.tendstoUniformlyOn_iff.mp hP ε hε] with n hn x
    simpa only [hgval x] using hn x x.property

-- PMA-7.28
theorem pma7_28 : pma7_28_contract.{u} := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro X A; rfl
  · intro X A; rfl
  · intro X A; rfl
  · intro X A; rfl
  · intro X A f; rfl
  · intro X A f; rfl
  · intro X v
    exact polynomialFunctionFamily_isAlgebra v
  · intro X v
    exact polynomialFunctionFamily_isAlgebra v
  · intro a b hab
    exact polynomialClosure_interval a b id continuous_id (pma7_26.2 a b hab)
  · intro a b hab
    exact polynomialClosure_interval a b Complex.ofReal Complex.continuous_ofReal (pma7_26.1 a b hab)

theorem algebraUniformClosure_bounded {X 𝕜 : Type*} [NormedField 𝕜]
    {A : Set (X → 𝕜)} (hA : ∀ f ∈ A, AlgebraFunctionBounded f)
    {f : X → 𝕜} (hf : f ∈ AlgebraUniformClosure A) : AlgebraFunctionBounded f := by
  rcases hf with ⟨F, hF, hlim⟩
  rcases (Metric.tendstoUniformly_iff.mp hlim 1 zero_lt_one).exists with ⟨N, hN⟩
  rcases hA _ (hF N) with ⟨M, hM⟩
  refine ⟨1 + M, fun x => ?_⟩
  calc
    ‖f x‖ ≤ ‖f x - F N x‖ + ‖F N x‖ := norm_le_norm_sub_add _ _
    _ ≤ 1 + M := add_le_add (le_of_lt (by simpa only [dist_eq_norm] using hN x)) (hM x)

noncomputable def algebraBoundedMap {X 𝕜 : Type*} [TopologicalSpace X]
    [DiscreteTopology X] [NormedField 𝕜] (f : X → 𝕜) (hf : AlgebraFunctionBounded f) :
    X →ᵇ 𝕜 :=
  BoundedContinuousFunction.mkOfDiscrete f (2 * hf.choose) (fun x y => by
    calc
      dist (f x) (f y) ≤ ‖f x‖ + ‖f y‖ := dist_le_norm_add_norm _ _
      _ ≤ 2 * hf.choose := by linarith [hf.choose_spec x, hf.choose_spec y])

@[simp] theorem algebraBoundedMap_apply {X 𝕜 : Type*} [TopologicalSpace X]
    [DiscreteTopology X] [NormedField 𝕜] (f : X → 𝕜) (hf : AlgebraFunctionBounded f)
    (x : X) : algebraBoundedMap f hf x = f x := rfl

def nonUnitalBoundedAlgebra {X 𝕜 : Type*} [TopologicalSpace X]
    [NormedField 𝕜] {A : Set (X → 𝕜)} (hA : IsFunctionAlgebra A) :
    NonUnitalSubalgebra 𝕜 (X →ᵇ 𝕜) where
  carrier := {f | (f : X → 𝕜) ∈ A}
  zero_mem' := by
    rcases hA.1 with ⟨f, hf⟩
    change (fun _ : X => (0 : 𝕜)) ∈ A
    simpa only [zero_mul] using hA.2.2.2 0 f hf
  add_mem' := fun hf hg => hA.2.1 _ hf _ hg
  mul_mem' := fun hf hg => hA.2.2.1 _ hf _ hg
  smul_mem' := fun c _ hf => hA.2.2.2 c _ hf

theorem bcfClosure_of_algebraUniformClosure {X 𝕜 : Type*} [TopologicalSpace X]
    [DiscreteTopology X] [NormedField 𝕜] {A : Set (X → 𝕜)}
    (hA : ∀ f ∈ A, AlgebraFunctionBounded f) {f : X → 𝕜}
    (hf : AlgebraFunctionBounded f) (hlim : f ∈ AlgebraUniformClosure A) :
    algebraBoundedMap f hf ∈ closure {g : X →ᵇ 𝕜 | (g : X → 𝕜) ∈ A} := by
  rcases hlim with ⟨F, hF, hconv⟩
  apply mem_closure_iff_seq_limit.mpr
  refine ⟨fun n => algebraBoundedMap (F n) (hA _ (hF n)), hF, ?_⟩
  exact BoundedContinuousFunction.tendsto_iff_tendstoUniformly.mpr hconv

theorem algebraUniformClosure_of_bcfClosure {X 𝕜 : Type*} [TopologicalSpace X]
    [NormedField 𝕜] {A : Set (X → 𝕜)} {f : X →ᵇ 𝕜}
    (hf : f ∈ closure {g : X →ᵇ 𝕜 | (g : X → 𝕜) ∈ A}) :
    (f : X → 𝕜) ∈ AlgebraUniformClosure A := by
  rcases mem_closure_iff_seq_limit.mp hf with ⟨F, hF, hconv⟩
  exact ⟨fun n => F n, hF, BoundedContinuousFunction.tendsto_iff_tendstoUniformly.mp hconv⟩

theorem algebraUniformClosure_algebra_closed {X 𝕜 : Type*} [NormedField 𝕜]
    {A : Set (X → 𝕜)} (hA : IsFunctionAlgebra A)
    (hAb : ∀ f ∈ A, AlgebraFunctionBounded f) :
    IsFunctionAlgebra (AlgebraUniformClosure A) ∧
      IsAlgebraUniformlyClosed (AlgebraUniformClosure A) ∧
      ∀ f ∈ AlgebraUniformClosure A, AlgebraFunctionBounded f := by
  let : TopologicalSpace X := ⊥
  let : DiscreteTopology X := ⟨rfl⟩
  let C := (nonUnitalBoundedAlgebra hA).topologicalClosure
  have hmem {f : X → 𝕜} (hf : f ∈ AlgebraUniformClosure A) :
      algebraBoundedMap f (algebraUniformClosure_bounded hAb hf) ∈ C :=
    bcfClosure_of_algebraUniformClosure hAb _ hf
  have hback {f : X →ᵇ 𝕜} (hf : f ∈ C) : (f : X → 𝕜) ∈ AlgebraUniformClosure A :=
    algebraUniformClosure_of_bcfClosure hf
  refine ⟨⟨⟨fun _ => 0, hback C.zero_mem⟩, ?_, ?_, ?_⟩, ?_,
    fun f hf => algebraUniformClosure_bounded hAb hf⟩
  · intro f hf g hg
    exact hback (C.add_mem (hmem hf) (hmem hg))
  · intro f hf g hg
    exact hback (C.mul_mem (hmem hf) (hmem hg))
  · intro c f hf
    exact hback (C.smul_mem c (hmem hf))
  · intro F f hF hconv
    have hf : AlgebraFunctionBounded f :=
      algebraUniformClosure_bounded (fun g hg => algebraUniformClosure_bounded hAb hg)
        ⟨F, hF, hconv⟩
    have ht : Tendsto (fun n => algebraBoundedMap (F n)
        (algebraUniformClosure_bounded hAb (hF n))) atTop (𝓝 (algebraBoundedMap f hf)) :=
      BoundedContinuousFunction.tendsto_iff_tendstoUniformly.mpr hconv
    exact hback ((nonUnitalBoundedAlgebra hA).isClosed_topologicalClosure.mem_of_tendsto
      ht (Filter.Eventually.of_forall fun n => hmem (hF n)))

-- PMA-7.29
theorem pma7_29 : pma7_29_contract.{u} := by
  constructor <;> intro X A hA hAb
  · exact algebraUniformClosure_algebra_closed hA hAb
  · exact algebraUniformClosure_algebra_closed hA hAb

theorem mem_algebraUniformClosure {X Y : Type*} [PseudoMetricSpace Y]
    {A : Set (X → Y)} {f : X → Y} (hf : f ∈ A) : f ∈ AlgebraUniformClosure A := by
  refine ⟨fun _ => f, fun _ => hf, Metric.tendstoUniformly_iff.mpr ?_⟩
  intro ε hε
  exact Filter.Eventually.of_forall fun _ x => by simpa using hε

theorem functionAlgebra_sub_mem {X 𝕜 : Type*} [Field 𝕜] {A : Set (X → 𝕜)}
    (hA : IsFunctionAlgebra A) {f g : X → 𝕜} (hf : f ∈ A) (hg : g ∈ A) :
    (fun x => f x - g x) ∈ A := by
  simpa only [neg_one_mul, sub_eq_add_neg] using hA.2.1 _ hf _ (hA.2.2.2 (-1) _ hg)

theorem functionAlgebra_mul_polynomial_mem {X 𝕜 : Type*} [Field 𝕜]
    {A : Set (X → 𝕜)} (hA : IsFunctionAlgebra A) {f : X → 𝕜} (hf : f ∈ A)
    (p : Polynomial 𝕜) : (fun x => f x * p.eval (f x)) ∈ A := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    convert hA.2.1 _ hp _ hq using 1
    ext x
    simp only [Polynomial.eval_add, mul_add]
  | monomial n c =>
    have hp (n : ℕ) : (fun x => f x ^ (n + 1)) ∈ A := by
      induction n with
      | zero => simpa using hf
      | succ n hn =>
        simpa only [pow_succ] using hA.2.2.1 _ hn _ hf
    convert hA.2.2.2 c _ (hp n) using 1
    ext x
    simp only [Polynomial.eval_monomial, pow_succ]
    ring

theorem functionAlgebra_polynomial_zero_mem {X 𝕜 : Type*} [Field 𝕜]
    {A : Set (X → 𝕜)} (hA : IsFunctionAlgebra A) {f : X → 𝕜} (hf : f ∈ A)
    (p : Polynomial 𝕜) (hp : p.eval 0 = 0) : (fun x => p.eval (f x)) ∈ A := by
  have hdiv : Polynomial.X ∣ p := Polynomial.X_dvd_iff.mpr (by
    simpa only [Polynomial.coeff_zero_eq_eval_zero] using hp)
  rcases hdiv with ⟨q, rfl⟩
  simpa only [Polynomial.eval_mul, Polynomial.eval_X] using
    functionAlgebra_mul_polynomial_mem hA hf q

theorem uniformlyClosed_functionAlgebra_abs {X : Type*} {A : Set (X → ℝ)}
    (hA : IsFunctionAlgebra A) (hclosed : IsAlgebraUniformlyClosed A)
    (hbounded : ∀ f ∈ A, AlgebraFunctionBounded f) {f : X → ℝ} (hf : f ∈ A) :
    (fun x => |f x|) ∈ A := by
  rcases hbounded f hf with ⟨M, hM⟩
  rcases pma7_27 (max M 0) (le_max_right _ _) with ⟨P, hP0, hP⟩
  apply hclosed (fun n x => (P n).eval (f x)) (fun x => |f x|)
  · exact fun n => functionAlgebra_polynomial_zero_mem hA hf _ (hP0 n)
  · apply Metric.tendstoUniformly_iff.mpr
    intro ε hε
    filter_upwards [Metric.tendstoUniformlyOn_iff.mp hP ε hε] with n hn x
    apply hn (f x)
    apply abs_le.mp
    exact (hM x).trans (le_max_left _ _)

theorem functionAlgebra_min_mem {X : Type*} {A : Set (X → ℝ)}
    (hA : IsFunctionAlgebra A) (habs : ∀ f ∈ A, (fun x => |f x|) ∈ A)
    {f g : X → ℝ} (hf : f ∈ A) (hg : g ∈ A) :
    (fun x => min (f x) (g x)) ∈ A := by
  have hs := functionAlgebra_sub_mem hA (hA.2.1 _ hf _ hg)
    (habs _ (functionAlgebra_sub_mem hA hg hf))
  convert hA.2.2.2 (1 / 2) _ hs using 1
  ext x
  by_cases h : f x ≤ g x
  · simp only [min_eq_left h, abs_of_nonneg (sub_nonneg.mpr h)]
    ring
  · have h' := lt_of_not_ge h
    simp only [min_eq_right h'.le, abs_of_nonpos (sub_nonpos.mpr h'.le)]
    ring

theorem functionAlgebra_max_mem {X : Type*} {A : Set (X → ℝ)}
    (hA : IsFunctionAlgebra A) (habs : ∀ f ∈ A, (fun x => |f x|) ∈ A)
    {f g : X → ℝ} (hf : f ∈ A) (hg : g ∈ A) :
    (fun x => max (f x) (g x)) ∈ A := by
  have hs := hA.2.1 _ (hA.2.1 _ hf _ hg) _
    (habs _ (functionAlgebra_sub_mem hA hg hf))
  convert hA.2.2.2 (1 / 2) _ hs using 1
  ext x
  by_cases h : f x ≤ g x
  · simp only [max_eq_right h, abs_of_nonneg (sub_nonneg.mpr h)]
    ring
  · have h' := lt_of_not_ge h
    simp only [max_eq_left h'.le, abs_of_nonpos (sub_nonpos.mpr h'.le)]
    ring

theorem real_functionAlgebra_uniformClosure {X : Type*} [TopologicalSpace X]
    [CompactSpace X] {A : Set (X → ℝ)} (hA : IsFunctionAlgebra A)
    (hcont : ∀ f ∈ A, Continuous f) (hsep : SeparatesFunctionPoints A)
    (hnv : FunctionVanishesNowhere A) :
    AlgebraUniformClosure A = {f : X → ℝ | Continuous f} := by
  have hbounded (f) (hf : f ∈ A) : AlgebraFunctionBounded f := by
    let F : C(X, ℝ) := ⟨f, hcont f hf⟩
    exact ⟨‖F‖, fun x => F.norm_coe_le_norm x⟩
  rcases algebraUniformClosure_algebra_closed hA hbounded with ⟨hCA, hCC, hCB⟩
  have hCabs (f) (hf : f ∈ AlgebraUniformClosure A) :
      (fun x => |f x|) ∈ AlgebraUniformClosure A :=
    uniformlyClosed_functionAlgebra_abs hCA hCC hCB hf
  let L : Set C(X, ℝ) := {f | (f : X → ℝ) ∈ AlgebraUniformClosure A}
  have hLclosed : IsClosed L := by
    apply IsSeqClosed.isClosed
    intro F f hF hlim
    exact hCC (fun n => F n) f hF (ContinuousMap.tendsto_iff_tendstoUniformly.mp hlim)
  have hLn : L.Nonempty := by
    rcases hA.1 with ⟨f, hf⟩
    exact ⟨⟨f, hcont f hf⟩, mem_algebraUniformClosure hf⟩
  have hLmin : ∀ f ∈ L, ∀ g ∈ L, f ⊓ g ∈ L := by
    intro f hf g hg
    exact functionAlgebra_min_mem hCA hCabs hf hg
  have hLmax : ∀ f ∈ L, ∀ g ∈ L, f ⊔ g ∈ L := by
    intro f hf g hg
    exact functionAlgebra_max_mem hCA hCabs hf hg
  have hLsep : L.SeparatesPointsStrongly := by
    intro v x y
    by_cases hxy : x = y
    · subst y
      rcases hnv x with ⟨f, hf, hfx⟩
      have hg := hA.2.2.2 (v x / f x) f hf
      refine ⟨⟨fun z => (v x / f x) * f z, hcont _ hg⟩,
        mem_algebraUniformClosure hg, ?_, ?_⟩ <;> exact div_mul_cancel₀ _ hfx
    · rcases functionAlgebra_interpolate hA hsep hnv x y hxy (v x) (v y) with
        ⟨f, hf, hfx, hfy⟩
      exact ⟨⟨f, hcont f hf⟩, mem_algebraUniformClosure hf, hfx, hfy⟩
  have hdense := ContinuousMap.sublattice_closure_eq_top L hLn hLmin hLmax hLsep
  rw [hLclosed.closure_eq] at hdense
  ext f
  constructor
  · exact algebraUniformClosure_continuous hcont
  · intro hf
    have hm : (⟨f, hf⟩ : C(X, ℝ)) ∈ L := by rw [hdense]; trivial
    exact hm

-- PMA-7.32
theorem pma7_32 : pma7_32_contract.{u} := by
  intro X _ _ A hA hcont hsep hnv
  exact real_functionAlgebra_uniformClosure hA hcont hsep hnv

theorem functionAlgebra_re_mem {X : Type*} {A : Set (X → ℂ)}
    (hA : IsFunctionAlgebra A) (hstar : IsSelfAdjointFunctionFamily A)
    {f : X → ℂ} (hf : f ∈ A) : (fun x => ((f x).re : ℂ)) ∈ A := by
  convert hA.2.2.2 (1 / 2) _ (hA.2.1 _ hf _ (hstar f hf)) using 1
  ext x
  apply Complex.ext
  · simp
    ring
  · simp

theorem functionAlgebra_im_mem {X : Type*} {A : Set (X → ℂ)}
    (hA : IsFunctionAlgebra A) (hstar : IsSelfAdjointFunctionFamily A)
    {f : X → ℂ} (hf : f ∈ A) : (fun x => ((f x).im : ℂ)) ∈ A := by
  convert hA.2.2.2 (-(Complex.I / 2)) _
    (functionAlgebra_sub_mem hA hf (hstar f hf)) using 1
  ext x
  apply Complex.ext
  · simp
    ring
  · simp

theorem complex_functionAlgebra_uniformClosure {X : Type*} [TopologicalSpace X]
    [CompactSpace X] {A : Set (X → ℂ)} (hA : IsFunctionAlgebra A)
    (hcont : ∀ f ∈ A, Continuous f) (hsep : SeparatesFunctionPoints A)
    (hnv : FunctionVanishesNowhere A) (hstar : IsSelfAdjointFunctionFamily A) :
    AlgebraUniformClosure A = {f : X → ℂ | Continuous f} := by
  let B : Set (X → ℝ) := {f | (fun x => (f x : ℂ)) ∈ A}
  have hBA : IsFunctionAlgebra B := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · rcases hA.1 with ⟨f, hf⟩
      exact ⟨fun x => (f x).re, functionAlgebra_re_mem hA hstar hf⟩
    · intro f hf g hg
      change (fun x => ((f x + g x : ℝ) : ℂ)) ∈ A
      simpa only [Complex.ofReal_add] using hA.2.1 _ hf _ hg
    · intro f hf g hg
      change (fun x => ((f x * g x : ℝ) : ℂ)) ∈ A
      simpa only [Complex.ofReal_mul] using hA.2.2.1 _ hf _ hg
    · intro c f hf
      change (fun x => ((c * f x : ℝ) : ℂ)) ∈ A
      simpa only [Complex.ofReal_mul] using hA.2.2.2 (c : ℂ) _ hf
  have hBcont (f) (hf : f ∈ B) : Continuous f := by
    simpa only [Function.comp_def, Complex.ofReal_re] using
      Complex.continuous_re.comp (hcont _ hf)
  have hBsep : SeparatesFunctionPoints B := by
    intro x y hxy
    rcases hsep hxy with ⟨f, hf, hne⟩
    by_cases hre : (f x).re = (f y).re
    · have him : (f x).im ≠ (f y).im := fun him => hne (Complex.ext hre him)
      exact ⟨fun z => (f z).im, functionAlgebra_im_mem hA hstar hf, him⟩
    · exact ⟨fun z => (f z).re, functionAlgebra_re_mem hA hstar hf, hre⟩
  have hBnv : FunctionVanishesNowhere B := by
    intro x
    rcases hnv x with ⟨f, hf, hne⟩
    by_cases hre : (f x).re = 0
    · have him : (f x).im ≠ 0 := fun him => hne (Complex.ext hre him)
      exact ⟨fun z => (f z).im, functionAlgebra_im_mem hA hstar hf, him⟩
    · exact ⟨fun z => (f z).re, functionAlgebra_re_mem hA hstar hf, hre⟩
  have hBdense := real_functionAlgebra_uniformClosure hBA hBcont hBsep hBnv
  ext f
  constructor
  · exact algebraUniformClosure_continuous hcont
  · intro hf
    have hre : (fun x => (f x).re) ∈ AlgebraUniformClosure B := by
      rw [hBdense]
      exact Complex.continuous_re.comp hf
    have him : (fun x => (f x).im) ∈ AlgebraUniformClosure B := by
      rw [hBdense]
      exact Complex.continuous_im.comp hf
    rcases hre with ⟨F, hF, hFlim⟩
    rcases him with ⟨G, hG, hGlim⟩
    refine ⟨fun n x => (F n x : ℂ) + Complex.I * (G n x : ℂ),
      fun n => hA.2.1 _ (hF n) _ (hA.2.2.2 Complex.I _ (hG n)),
      Metric.tendstoUniformly_iff.mpr ?_⟩
    intro ε hε
    filter_upwards [Metric.tendstoUniformly_iff.mp hFlim (ε / 2) (half_pos hε),
      Metric.tendstoUniformly_iff.mp hGlim (ε / 2) (half_pos hε)] with n hn hm x
    have hnorm := Complex.norm_le_abs_re_add_abs_im
      (f x - ((F n x : ℂ) + Complex.I * (G n x : ℂ)))
    simp only [Complex.sub_re, Complex.add_re, Complex.ofReal_re, Complex.mul_re,
      Complex.I_re, Complex.ofReal_im, Complex.I_im, zero_mul, one_mul, sub_zero,
      add_zero, Complex.sub_im, Complex.add_im, Complex.mul_im, zero_add] at hnorm
    rw [dist_eq_norm]
    have h1 := hn x
    have h2 := hm x
    rw [Real.dist_eq] at h1 h2
    linarith

theorem complex_star_not_differentiable_zero :
    ¬ DifferentiableAt ℂ (star : ℂ → ℂ) 0 := by
  intro h
  let D := fderiv ℂ (star : ℂ → ℂ) 0
  have heq : D.restrictScalars ℝ = Complex.conjCLE.toContinuousLinearMap :=
    (h.hasFDerivAt.restrictScalars ℝ).unique
      Complex.conjCLE.toContinuousLinearMap.hasFDerivAt
  have h1 : D 1 = 1 := by
    have := congrArg (fun L : ℂ →L[ℝ] ℂ => L 1) heq
    simpa using this
  have hI : D Complex.I = -Complex.I := by
    have := congrArg (fun L : ℂ →L[ℝ] ℂ => L Complex.I) heq
    simpa using this
  have hlin := D.map_smul Complex.I (1 : ℂ)
  simp only [smul_eq_mul, mul_one, h1, hI] at hlin
  have him := congrArg Complex.im hlin
  norm_num at him

theorem polynomial_disk_conj_not_uniformClosure :
    (fun z : Metric.closedBall (0 : ℂ) 1 => star (z : ℂ)) ∉
      AlgebraUniformClosure (PolynomialFunctionFamily
        (fun z : Metric.closedBall (0 : ℂ) 1 => (z : ℂ))) := by
  rintro ⟨F, hF, hlim⟩
  change ∀ n, ∃ p : Polynomial ℂ, ∀ z, F n z = p.eval (z : ℂ) at hF
  choose P hP using hF
  have hFeq : F = fun n (z : Metric.closedBall (0 : ℂ) 1) => (P n).eval (z : ℂ) :=
    funext fun n => funext (hP n)
  rw [hFeq] at hlim
  have hwhole : TendstoUniformlyOn (fun n z => (P n).eval z) (star : ℂ → ℂ)
      atTop (Metric.closedBall (0 : ℂ) 1) :=
    tendstoUniformlyOn_iff_tendstoUniformly_comp_coe.mpr hlim
  have hball := (hwhole.mono Metric.ball_subset_closedBall).tendstoLocallyUniformlyOn
  have hdiff : DifferentiableOn ℂ (star : ℂ → ℂ) (Metric.ball (0 : ℂ) 1) :=
    hball.differentiableOn (Filter.Eventually.of_forall fun n => (P n).differentiableOn)
      Metric.isOpen_ball
  exact complex_star_not_differentiable_zero
    (hdiff.differentiableAt (Metric.isOpen_ball.mem_nhds (by simp)))

theorem complex_stoneWeierstrass_without_selfAdjoint_fails :
    ∃ A : Set (Metric.closedBall (0 : ℂ) 1 → ℂ),
      IsFunctionAlgebra A ∧ (∀ f ∈ A, Continuous f) ∧
      SeparatesFunctionPoints A ∧ FunctionVanishesNowhere A ∧
      ¬ IsSelfAdjointFunctionFamily A ∧
      ∃ f : Metric.closedBall (0 : ℂ) 1 → ℂ,
        Continuous f ∧ f ∉ AlgebraUniformClosure A := by
  let A := PolynomialFunctionFamily (fun z : Metric.closedBall (0 : ℂ) 1 => (z : ℂ))
  refine ⟨A, polynomialFunctionFamily_isAlgebra _, ?_,
    polynomialFunctionFamily_separates _ Subtype.val_injective,
    polynomialFunctionFamily_nonvanishing _, ?_, ?_⟩
  · rintro f ⟨p, hp⟩
    have heq : f = fun z : Metric.closedBall (0 : ℂ) 1 => p.eval (z : ℂ) := funext hp
    rw [heq]
    exact p.continuous.comp continuous_subtype_val
  · intro hstar
    have hid : (fun z : Metric.closedBall (0 : ℂ) 1 => (z : ℂ)) ∈ A :=
      ⟨Polynomial.X, fun _ => by simp⟩
    exact polynomial_disk_conj_not_uniformClosure (mem_algebraUniformClosure (hstar _ hid))
  · exact ⟨fun z => star (z : ℂ), continuous_subtype_val.star,
      polynomial_disk_conj_not_uniformClosure⟩

-- PMA-7.33
theorem pma7_33 : pma7_33_contract.{u} := by
  refine ⟨?_, ?_, complex_stoneWeierstrass_without_selfAdjoint_fails⟩
  · intro X A
    rfl
  · intro X _ _ A hA hcont hsep hnv hstar
    exact complex_functionAlgebra_uniformClosure hA hcont hsep hnv hstar

#print axioms pma7_26
#print axioms pma7_27
#print axioms pma7_28
#print axioms pma7_29
#print axioms pma7_30
#print axioms pma7_31
#print axioms pma7_32
#print axioms pma7_33

end Rudin.PMA.Chapter07
