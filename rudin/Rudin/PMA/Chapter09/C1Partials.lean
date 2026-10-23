import Rudin.PMA.Chapter09.Differentiation
import Rudin.PMA.Chapter09.MathlibPartialBridge

/-!
# PMA 9.21: continuous coordinate partials

The converse is proved without assuming total differentiability. Coordinate
increments telescope, and the one-dimensional mean-value remainder is little-o
uniformly in the other coordinates. The finite sum is then a total derivative.
-/

set_option autoImplicit false
noncomputable section
open Set Filter Asymptotics
open scoped Topology BigOperators

namespace Rudin.PMA.Chapter09

/-- Change the first `k` coordinates from `x` to `y`. -/
private def coordinatePrefix {n : ℕ} (x y : Euclidean n) (k : ℕ) : Euclidean n :=
  WithLp.toLp 2 (fun i : Fin n => if i.val < k then y i else x i)

@[simp] private theorem coordinatePrefix_apply {n : ℕ} (x y : Euclidean n)
    (k : ℕ) (i : Fin n) :
    coordinatePrefix x y k i = if i.val < k then y i else x i := rfl

@[simp] private theorem coordinatePrefix_self {n : ℕ} (x : Euclidean n) (k : ℕ) :
    coordinatePrefix x x k = x := by
  ext i
  simp

@[simp] private theorem coordinatePrefix_zero {n : ℕ} (x y : Euclidean n) :
    coordinatePrefix x y 0 = x := by
  ext i
  simp

@[simp] private theorem coordinatePrefix_last {n : ℕ} (x y : Euclidean n) :
    coordinatePrefix x y n = y := by
  ext i
  simp [i.isLt]

private theorem continuous_coordinatePrefix {n : ℕ} (x : Euclidean n) (k : ℕ) :
    Continuous (fun y => coordinatePrefix x y k) := by
  apply (PiLp.continuous_toLp 2 (fun _ : Fin n => ℝ)).comp
  apply continuous_pi
  intro i
  by_cases hi : i.val < k
  · simpa [coordinatePrefix, hi] using (EuclideanSpace.proj i).continuous
  · simp only [ite_eq_right hi]
    exact continuous_const

private theorem coordinatePrefix_step {n : ℕ} (x y : Euclidean n) (j : Fin n) :
    coordinatePrefix x y (j.val + 1) =
      coordinatePrefix x y j.val + (y j - x j) • coordinateVector n j := by
  ext i
  by_cases hij : i = j
  · subst i
    simp [coordinateVector, EuclideanSpace.basisFun_apply]
  · have hval : i.val ≠ j.val := fun h => hij (Fin.ext h)
    have hlt : (i.val < j.val + 1) ↔ i.val < j.val := by omega
    simp [coordinateVector, EuclideanSpace.basisFun_apply, hij, hlt]

/-- Move a coordinate derivative from a line based at the point to any
parameter value on that same line. -/
private theorem hasDerivAt_coordinateLine {n : ℕ} {f : Euclidean n → ℝ}
    (z : Euclidean n) (j : Fin n) (t d : ℝ)
    (h : HasCoordinatePartial f (z + t • coordinateVector n j) j d) :
    HasDerivAt (fun s : ℝ => f (z + s • coordinateVector n j)) d t := by
  change HasDerivAt (fun s : ℝ =>
    f ((z + t • coordinateVector n j) + s • coordinateVector n j)) d 0 at h
  have hh : HasDerivAt
      (fun s : ℝ => f ((z + t • coordinateVector n j) +
        (s - t) • coordinateVector n j)) d t := by
    simpa only [Function.comp_def, id_eq, mul_one] using
      h.comp_of_eq t ((hasDerivAt_id t).sub_const t) (by simp)
  apply hh.congr_of_eventuallyEq
  exact Eventually.of_forall fun s => congrArg f (by module)

/-- The candidate scalar derivative from its coordinate coefficients. -/
private def partialLinear {n : ℕ} (p : Euclidean n → Fin n → ℝ)
    (x : Euclidean n) : Euclidean n →L[ℝ] ℝ :=
  ∑ j, p x j • EuclideanSpace.proj j

@[simp] private theorem partialLinear_apply {n : ℕ}
    (p : Euclidean n → Fin n → ℝ) (x h : Euclidean n) :
    partialLinear p x h = ∑ j, p x j * h j := by
  simp [partialLinear]

private theorem hasFDerivAt_of_continuous_coordinatePartials {n : ℕ}
    {f : Euclidean n → ℝ} {E : Set (Euclidean n)}
    {p : Euclidean n → Fin n → ℝ} (hE : IsOpen E)
    (hp : ∀ y ∈ E, ∀ j, HasCoordinatePartial f y j (p y j))
    (hc : ∀ j, ContinuousOn (fun y => p y j) E)
    {x : Euclidean n} (hx : x ∈ E) : HasFDerivAt f (partialLinear p x) x := by
  have hterm (j : Fin n) :
      (fun y => f (coordinatePrefix x y (j.val + 1)) -
        f (coordinatePrefix x y j.val) - p x j * (y j - x j))
        =o[𝓝 x] (fun y => y - x) := by
    let z : Euclidean n → ℝ → Euclidean n := fun y t =>
      coordinatePrefix x y j.val + (t - x j) • coordinateVector n j
    have hz : Tendsto (fun q : Euclidean n × ℝ => z q.1 q.2)
        (𝓝 x ×ˢ 𝓝 (x j)) (𝓝 x) := by
      rw [← nhds_prod_eq]
      have hzcont : Continuous (fun q : Euclidean n × ℝ => z q.1 q.2) :=
        ((continuous_coordinatePrefix x j.val).comp continuous_fst).add
          ((continuous_snd.sub continuous_const).smul continuous_const)
      simpa only [z, coordinatePrefix_self, sub_self, zero_smul, add_zero] using
        hzcont.continuousAt.tendsto (x := (x, x j))
    have hd : ∀ᶠ q in 𝓝 x ×ˢ 𝓝 (x j),
        HasFDerivWithinAt (fun t : ℝ => f (z q.1 t))
          ((p (z q.1 q.2) j) • (1 : ℝ →L[ℝ] ℝ)) univ q.2 := by
      filter_upwards [hz.eventually (hE.mem_nhds hx)] with q hq
      have hline : HasDerivAt (fun t : ℝ => f (z q.1 t))
          (p (z q.1 q.2) j) q.2 := by
        have h := hasDerivAt_coordinateLine (f := f)
          (coordinatePrefix x q.1 j.val - (x j) • coordinateVector n j)
          j q.2 (p (z q.1 q.2) j)
        have heq : coordinatePrefix x q.1 j.val - (x j) • coordinateVector n j +
            q.2 • coordinateVector n j = z q.1 q.2 := by dsimp [z]; module
        rw [heq] at h
        have hh := h (hp _ hq j)
        apply hh.congr_of_eventuallyEq
        exact Eventually.of_forall fun t => congrArg f (by dsimp [z]; module)
      convert hline.hasFDerivAt.hasFDerivWithinAt using 1
      ext t
      simp [mul_comm]
    have hcp : Tendsto (fun q : Euclidean n × ℝ =>
        p (z q.1 q.2) j • (1 : ℝ →L[ℝ] ℝ))
        (𝓝 x ×ˢ 𝓝 (x j)) (𝓝 (p x j • (1 : ℝ →L[ℝ] ℝ))) :=
      (((hc j x hx).continuousAt (hE.mem_nhds hx)).smul continuousAt_const).tendsto.comp hz
    have ho := parameterized_meanValue_remainder
      (f := fun y t => f (z y t))
      (f' := fun y t => p (z y t) j • (1 : ℝ →L[ℝ] ℝ))
      (φ := p x j • (1 : ℝ →L[ℝ] ℝ))
      (v := fun y : Euclidean n => y j) (w := fun _ : Euclidean n => x j)
      (EuclideanSpace.proj j).continuous.continuousAt.tendsto tendsto_const_nhds
      Set.univ (by simp)
      (by simpa only [nhdsWithin_univ, EuclideanSpace.coe_proj] using hd)
      (by simpa only [nhdsWithin_univ, EuclideanSpace.coe_proj] using! hcp)
    have hb : (fun y : Euclidean n => y j - x j) =O[𝓝 x] (fun y => y - x) :=
      isBigO_of_le _ (fun y => by simpa using PiLp.norm_apply_le (y - x) j)
    simpa only [z, ← coordinatePrefix_step, sub_self, zero_smul, add_zero,
      smul_apply, one_apply_eq_self, smul_eq_mul] using
      ho.trans_isBigO hb
  apply HasFDerivAt.of_isLittleO
  have hs := IsLittleO.sum (s := (Finset.univ : Finset (Fin n)))
    (fun j _ => hterm j)
  apply hs.congr_left
  intro y
  simp only [Finset.sum_apply, Finset.sum_sub_distrib, partialLinear_apply,
    PiLp.sub_apply]
  have ht : (∑ j : Fin n, (f (coordinatePrefix x y (j.val + 1)) -
      f (coordinatePrefix x y j.val))) = f y - f x := by
    rw [Fin.sum_univ_eq_sum_range
      (fun k => f (coordinatePrefix x y (k + 1)) - f (coordinatePrefix x y k)) n]
    simpa using Finset.sum_range_sub (fun k => f (coordinatePrefix x y k)) n
  rw [← Finset.sum_sub_distrib, ht]

theorem c1On_of_continuous_coordinatePartials {n : ℕ}
    {f : Euclidean n → ℝ} {E : Set (Euclidean n)}
    (hE : IsOpen E)
    (hp : ∀ y ∈ E, ∀ j, ∃ d, HasCoordinatePartial f y j d)
    (hc : ∀ j, ContinuousOn (fun y => coordinatePartial f y j) E) : C1On f E := by
  let p : Euclidean n → Fin n → ℝ := fun y j => coordinatePartial f y j
  have hd : ∀ y ∈ E, HasFDerivAt f (partialLinear p y) y := by
    intro y hy
    apply hasFDerivAt_of_continuous_coordinatePartials hE _ hc hy
    intro z hz j
    obtain ⟨d, hd⟩ := hp z hz j
    simpa only [p, coordinatePartial, hd.deriv] using hd
  refine ⟨fun y hy => (hd y hy).differentiableAt, ?_⟩
  have hcont : ContinuousOn (fun y => partialLinear p y) E := by
    unfold partialLinear
    apply continuousOn_finsetSum
    intro j _
    exact (hc j).smul continuousOn_const
  exact hcont.congr (fun y hy => (hd y hy).fderiv)

theorem pma9_21 : pma9_21_contract := by
  intro n m f E hE
  constructor
  · intro hf
    have hp (x : Euclidean n) (hx : x ∈ E) (i : Fin m) (j : Fin n) :
        HasCoordinatePartial (fun y => f y i) x j
          (fderiv ℝ f x (coordinateVector n j) i) :=
      hasCoordinatePartial_of_hasFDerivAt
        ((EuclideanSpace.proj i : Euclidean m →L[ℝ] ℝ).hasFDerivAt.comp x
          (hf.1 x hx).hasFDerivAt) j
    refine ⟨fun x hx i j => ⟨_, hp x hx i j⟩, ?_⟩
    intro i j
    have hh : ContinuousOn (fun x => fderiv ℝ f x (coordinateVector n j) i) E :=
      (EuclideanSpace.proj i).continuous.comp_continuousOn
        (hf.2.clm_apply continuousOn_const)
    exact hh.congr (fun x hx => (hp x hx i j).deriv)
  · intro hp
    apply (c1On_iff_contDiffOn hE).mpr
    apply (contDiffOn_piLp (p := 2)).mpr
    intro i
    apply (c1On_iff_contDiffOn hE).mp
    exact c1On_of_continuous_coordinatePartials hE
      (fun x hx j => hp.1 x hx i j) (fun j => hp.2 i j)

end Rudin.PMA.Chapter09
