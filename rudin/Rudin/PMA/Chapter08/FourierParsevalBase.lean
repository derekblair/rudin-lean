import Rudin.PMA.Chapter08.RiemannBridge

set_option autoImplicit false

noncomputable section
open Set Filter Topology MeasureTheory AddCircle
open scoped BigOperators ENNReal InnerProductSpace ComplexConjugate

namespace Rudin.PMA.Chapter08

/-! PMA 8.16: Parseval's theorem in the native Riemann-integrable scope.
All coefficient and integral identities below retain the native Chapter 6
integrals, using the independently proved Darboux-to-library bridge.
-/

theorem hasSum_circle_fourier_mul_star {T : ℝ} [hT : Fact (0 < T)]
    (f g : Lp ℂ 2 (@haarAddCircle T hT)) :
    HasSum (fun n => fourierCoeff f n * star (fourierCoeff g n))
      (∫ x : AddCircle T, f x * star (g x) ∂haarAddCircle) := by
  have h := lp.hasSum_inner (𝕜 := ℂ) (fourierBasis.repr g) (fourierBasis.repr f)
  simpa only [fourierBasis_repr, RCLike.inner_apply', LinearIsometryEquiv.inner_map_map,
    L2.inner_def, mul_comm] using! h

theorem hasSum_interval_fourier_mul_star {a b : ℝ} {f g : ℝ → ℂ}
    (hab : a < b) (hf : MemLp f 2 (volume.restrict (Ioc a b)))
    (hg : MemLp g 2 (volume.restrict (Ioc a b))) :
    HasSum (fun n => fourierCoeffOn hab f n * star (fourierCoeffOn hab g n))
      ((b - a)⁻¹ • ∫ x in a..b, f x * star (g x)) := by
  have : Fact (0 < b - a) := ⟨sub_pos.mpr hab⟩
  rw [← add_sub_cancel a b] at hf hg
  have hF := hf.memLp_liftIoc.haarAddCircle
  have hG := hg.memLp_liftIoc.haarAddCircle
  convert hasSum_circle_fourier_mul_star hF.toLp hG.toLp using 1
  · funext n
    simp [fourierCoeff_congr_ae hF.coeFn_toLp, fourierCoeff_congr_ae hG.coeFn_toLp,
      fourierCoeff_liftIoc_eq]
  · nth_rw 2 [← add_sub_cancel a b]
    rw [← AddCircle.integral_liftIoc_eq_intervalIntegral,
      ← AddCircle.integral_haarAddCircle]
    apply integral_congr_ae
    filter_upwards [hF.coeFn_toLp, hG.coeFn_toLp] with x hx hy
    simp only [hx, hy]
    rfl

end Rudin.PMA.Chapter08
