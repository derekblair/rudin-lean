import Rudin.PMA.Chapter09.Implicit
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 200000
noncomputable section
open Set
open scoped BigOperators
namespace Rudin.PMA.Chapter09

def implicitExample (z : Euclidean 2 × Euclidean 3) : Euclidean 2 :=
  WithLp.toLp 2 ![2 * Real.exp (z.1 0) + z.1 1 * z.2 0 - 4 * z.2 1 + 3,
    z.1 1 * Real.cos (z.1 0) - 6 * z.1 0 + 2 * z.2 0 - z.2 2]
def implicitExampleA : Euclidean 2 := WithLp.toLp 2 ![0,1]
def implicitExampleB : Euclidean 3 := WithLp.toLp 2 ![3,2,7]

def pma9_29_contract : Prop :=
  C1On implicitExample univ ∧ implicitExample (implicitExampleA,implicitExampleB) = 0 ∧
  (∀ h k, fderiv ℝ implicitExample (implicitExampleA,implicitExampleB) (h,k) =
    WithLp.toLp 2 ![2*h 0+3*h 1+k 0-4*k 1, -6*h 0+h 1+2*k 0-k 2]) ∧
  (blockX (fderiv ℝ implicitExample (implicitExampleA,implicitExampleB))).IsInvertible ∧
  (∀ z, (blockX (fderiv ℝ implicitExample (implicitExampleA,implicitExampleB))).inverse z =
    WithLp.toLp 2 ![(z 0-3*z 1)/20, (6*z 0+2*z 1)/20]) ∧
  ∃ g U W, ImplicitNeighborhood implicitExample univ implicitExampleA implicitExampleB g U W ∧
    ∀ k, fderiv ℝ g implicitExampleB k =
      WithLp.toLp 2 ![k 0/4+k 1/5-3*k 2/20, -k 0/2+6*k 1/5+k 2/10]

private def exX (i : Fin 2) : Euclidean 2 × Euclidean 3 →L[ℝ] ℝ :=
  (EuclideanSpace.proj i).comp (ContinuousLinearMap.fst ℝ (Euclidean 2) (Euclidean 3))
private def exY (i : Fin 3) : Euclidean 2 × Euclidean 3 →L[ℝ] ℝ :=
  (EuclideanSpace.proj i).comp (ContinuousLinearMap.snd ℝ (Euclidean 2) (Euclidean 3))

private theorem example_c1 : C1On implicitExample univ := by
  apply (c1On_iff_contDiffOn isOpen_univ).mpr
  apply ContDiff.contDiffOn
  apply (contDiff_piLp (p := 2)).mpr
  intro i
  fin_cases i
  · change ContDiff ℝ 1 (fun z : Euclidean 2 × Euclidean 3 =>
      2 * Real.exp (z.1 0) + z.1 1 * z.2 0 - 4 * z.2 1 + 3)
    fun_prop
  · change ContDiff ℝ 1 (fun z : Euclidean 2 × Euclidean 3 =>
      z.1 1 * Real.cos (z.1 0) - 6 * z.1 0 + 2 * z.2 0 - z.2 2)
    fun_prop

private theorem example_zero : implicitExample (implicitExampleA,implicitExampleB) = 0 := by
  ext i
  fin_cases i <;> norm_num [implicitExample, implicitExampleA, implicitExampleB]

private theorem example_derivative (h : Euclidean 2) (k : Euclidean 3) :
    fderiv ℝ implicitExample (implicitExampleA,implicitExampleB) (h,k) =
      WithLp.toLp 2 ![2*h 0+3*h 1+k 0-4*k 1, -6*h 0+h 1+2*k 0-k 2] := by
  let p := (implicitExampleA,implicitExampleB)
  have h0 := (((((Real.hasDerivAt_exp (exX 0 p)).comp_hasFDerivAt p (exX 0).hasFDerivAt).const_mul 2).add
    ((exX 1).hasFDerivAt.mul (exY 0).hasFDerivAt)).sub
      ((exY 1).hasFDerivAt.const_mul 4)).add_const 3
  have h1 := ((((exX 1).hasFDerivAt.mul
    ((Real.hasDerivAt_cos (exX 0 p)).comp_hasFDerivAt p (exX 0).hasFDerivAt)).sub
      ((exX 0).hasFDerivAt.const_mul 6)).add ((exY 0).hasFDerivAt.const_mul 2)).sub
        (exY 2).hasFDerivAt
  have hdf := (example_c1.1 p (mem_univ _)).hasFDerivAt
  ext i
  fin_cases i
  · have he := (((EuclideanSpace.proj (0 : Fin 2) : Euclidean 2 →L[ℝ] ℝ).hasFDerivAt.comp p hdf).unique h0)
    have hh := congrArg (fun L : Euclidean 2 × Euclidean 3 →L[ℝ] ℝ => L (h,k)) he
    simp [p, exX, exY, implicitExample, implicitExampleA, implicitExampleB,
      ContinuousLinearMap.smulRight_apply] at hh
    convert hh using 1 <;> first | rfl | (norm_num; ring)
  · have he := (((EuclideanSpace.proj (1 : Fin 2) : Euclidean 2 →L[ℝ] ℝ).hasFDerivAt.comp p hdf).unique h1)
    have hh := congrArg (fun L : Euclidean 2 × Euclidean 3 →L[ℝ] ℝ => L (h,k)) he
    simp [p, exX, exY, implicitExample, implicitExampleA, implicitExampleB,
      ContinuousLinearMap.smulRight_apply] at hh
    convert hh using 1 <;> first | rfl | (norm_num; ring)

private theorem example_inverse :
    (blockX (fderiv ℝ implicitExample (implicitExampleA,implicitExampleB))).IsInvertible ∧
    ∀ z, (blockX (fderiv ℝ implicitExample (implicitExampleA,implicitExampleB))).inverse z =
      WithLp.toLp 2 ![(z 0-3*z 1)/20, (6*z 0+2*z 1)/20] := by
  let A := blockX (fderiv ℝ implicitExample (implicitExampleA,implicitExampleB))
  let inv : Euclidean 2 → Euclidean 2 := fun z =>
    WithLp.toLp 2 ![(z 0-3*z 1)/20, (6*z 0+2*z 1)/20]
  have hA (z : Euclidean 2) : A z = WithLp.toLp 2 ![2*z 0+3*z 1, -6*z 0+z 1] := by
    simpa [A, blockX] using example_derivative z 0
  have hleft (z : Euclidean 2) : inv (A z) = z := by
    ext i
    fin_cases i <;> simp [inv, hA] <;> ring
  have hright (z : Euclidean 2) : A (inv z) = z := by
    ext i
    fin_cases i <;> simp [hA, inv] <;> ring
  have hinj : Function.Injective A := fun x y h => by
    have he := congrArg inv h
    simpa only [hleft] using he
  have hsurj : Function.Surjective A := fun z => ⟨inv z, hright z⟩
  have hi : A.IsInvertible := ⟨ContinuousLinearEquiv.ofBijective A
    (LinearMap.ker_eq_bot.mpr hinj) (LinearMap.range_eq_top.mpr hsurj), rfl⟩
  refine ⟨hi, ?_⟩
  intro z
  exact hi.inverse_apply_eq.mpr (hright z).symm

theorem pma9_29 : pma9_29_contract := by
  refine ⟨example_c1, example_zero, example_derivative, example_inverse.1,
    example_inverse.2, ?_⟩
  obtain ⟨g,U,W,hN,hd,_⟩ := pma9_28 2 3 univ implicitExample
    implicitExampleA implicitExampleB isOpen_univ (mem_univ _) example_c1
    example_zero example_inverse.1
  refine ⟨g,U,W,hN, ?_⟩
  intro k
  rw [hd.fderiv]
  change -(blockX (fderiv ℝ implicitExample (implicitExampleA,implicitExampleB))).inverse
    (blockY (fderiv ℝ implicitExample (implicitExampleA,implicitExampleB)) k) = _
  rw [example_inverse.2]
  have hy : blockY (fderiv ℝ implicitExample (implicitExampleA,implicitExampleB)) k =
      WithLp.toLp 2 ![k 0-4*k 1, 2*k 0-k 2] := by
    simpa [blockY] using example_derivative 0 k
  rw [hy]
  ext i
  fin_cases i <;> simp <;> ring

end Rudin.PMA.Chapter09
