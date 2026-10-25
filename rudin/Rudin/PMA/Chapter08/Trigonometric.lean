import Rudin.PMA.Chapter08.Exponential
import Rudin.PMA.Chapter06.Curve

set_option autoImplicit false
noncomputable section
open Set Filter Topology
open scoped BigOperators ENNReal

namespace Rudin.PMA.Chapter08

/-! PMA 8.7, pp.182–184. The exponential definitions agree with Mathlib's
sine and cosine. The geometric consequence uses Chapter 6 polygonal length.
The parameter convention `t * I` equals the printed `I * t` by commutativity. -/

def trigCircle (t : ℝ) : ℂ := Complex.exp ((t : ℂ) * Complex.I)

theorem cosine_exponential_definition (t : ℝ) :
    (Real.cos t : ℂ) = (trigCircle t + trigCircle (-t)) / 2 := by
  simp only [trigCircle, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin,
    Complex.ofReal_neg, Complex.cos_neg, Complex.sin_neg]
  ring

theorem sine_exponential_definition (t : ℝ) :
    (Real.sin t : ℂ) = (trigCircle t - trigCircle (-t)) / (2 * Complex.I) := by
  simp only [trigCircle, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin,
    Complex.ofReal_neg, Complex.cos_neg, Complex.sin_neg]
  field_simp
  ring

theorem trigCircle_injOn : InjOn trigCircle (Ico 0 (2 * Real.pi)) := by
  intro x hx y hy h
  apply Circle.exp_injOn_Ico (by simp : 2 * Real.pi - 0 ≤ 2 * Real.pi) hx hy
  exact Subtype.ext h

theorem trigCircle_unique (z : ℂ) (hz : ‖z‖ = 1) :
    ∃! t : ℝ, t ∈ Ico 0 (2 * Real.pi) ∧ trigCircle t = z := by
  let w : Circle := ⟨z, mem_sphere_zero_iff_norm.mpr hz⟩
  obtain ⟨t, ht, he⟩ := Circle.periodic_exp.exists_mem_Ico Real.two_pi_pos (Complex.arg z) 0
  have he' : trigCircle t = z := by
    have hw := Circle.exp_arg w
    have hh : Circle.exp t = w := he.symm.trans hw
    exact congrArg Subtype.val hh
  refine ⟨t, ⟨by simpa using ht, he'⟩, ?_⟩
  intro y hy
  exact trigCircle_injOn hy.1 (by simpa using ht) (hy.2.trans he'.symm)

theorem trigCircle_hasDerivAt (t : ℝ) :
    HasDerivAt trigCircle (Complex.I * trigCircle t) t :=
  Chapter05.circle_derivative t

theorem trigCircle_length {t : ℝ} (ht : 0 ≤ t) :
    Chapter06.RectifiableCurveOn trigCircle 0 t ∧
    Chapter06.CurveLength trigCircle 0 t = ENNReal.ofReal t := by
  have h := Chapter06.pma6_27 trigCircle (fun s => Complex.I * trigCircle s) 0 t ht
    (fun s _ => (trigCircle_hasDerivAt s).hasDerivWithinAt) (by unfold trigCircle; fun_prop)
  refine ⟨h.1, ?_⟩
  have hn : (fun s => ‖Complex.I * trigCircle s‖) = fun _ => (1 : ℝ) := by
    funext s
    exact Chapter05.circle_velocity_norm s
  rw [h.2.2, hn]
  have hc := (Chapter06.rsIntegral_const (c := (1 : ℝ)) ht
    (show MonotoneOn (id : ℝ → ℝ) (Icc 0 t) from fun _ _ _ _ h => h)).2
  simpa [Chapter06.RIntegral] using congrArg ENNReal.ofReal hc

def pma8_7_contract : Prop :=
  Function.Periodic Complex.exp (2 * Real.pi * Complex.I) ∧
  Function.Periodic Real.cos (2 * Real.pi) ∧
  Function.Periodic Real.sin (2 * Real.pi) ∧
  (∀ t : ℝ, 0 < t → t < 2 * Real.pi → trigCircle t ≠ 1) ∧
  (∀ z : ℂ, ‖z‖ = 1 → ∃! t : ℝ, t ∈ Ico 0 (2 * Real.pi) ∧ trigCircle t = z) ∧
  (∀ t, trigCircle t = (Real.cos t : ℂ) + (Real.sin t : ℂ) * Complex.I) ∧
  (∀ t, ‖trigCircle t‖ = 1) ∧
  (Real.cos 0 = 1 ∧ Real.sin 0 = 0) ∧
  (∀ t, HasDerivAt Real.cos (-Real.sin t) t ∧ HasDerivAt Real.sin (Real.cos t) t) ∧
  (Real.cos (Real.pi / 2) = 0 ∧
    ∀ t : ℝ, 0 < t → t < Real.pi / 2 → 0 < Real.cos t) ∧
  Chapter06.ClosedCurveOn trigCircle 0 (2 * Real.pi) ∧
  InjOn trigCircle (Ico 0 (2 * Real.pi)) ∧
  trigCircle '' Icc 0 (2 * Real.pi) = {z : ℂ | ‖z‖ = 1} ∧
  (∀ t : ℝ, 0 ≤ t → Chapter06.RectifiableCurveOn trigCircle 0 t ∧
    Chapter06.CurveLength trigCircle 0 t = ENNReal.ofReal t)

theorem pma8_7 : pma8_7_contract := by
  refine ⟨Complex.exp_periodic, Real.cos_periodic, Real.sin_periodic, ?_,
    trigCircle_unique, ?_, ?_, ⟨Real.cos_zero, Real.sin_zero⟩,
    fun t => ⟨Real.hasDerivAt_cos t, Real.hasDerivAt_sin t⟩, ?_, ?_,
    trigCircle_injOn, ?_, fun _ ht => trigCircle_length ht⟩
  · intro t ht htp he
    have hh := trigCircle_injOn ⟨ht.le, htp⟩ ⟨le_rfl, Real.two_pi_pos⟩
      (by simpa [trigCircle] using he)
    exact (ne_of_gt ht) hh
  · intro t
    simpa [trigCircle] using Complex.exp_mul_I (t : ℂ)
  · intro t
    simp [trigCircle]
  · refine ⟨Real.cos_pi_div_two, ?_⟩
    intro t ht htp
    exact Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], htp⟩
  · refine ⟨⟨Real.two_pi_pos.le, ?_⟩, ?_⟩
    · unfold trigCircle; fun_prop
    · simp [trigCircle, Complex.exp_two_pi_mul_I]
  · ext z
    constructor
    · rintro ⟨t, _, rfl⟩
      simp [trigCircle]
    · intro hz
      obtain ⟨t, ht, _⟩ := trigCircle_unique z hz
      exact ⟨t, ⟨ht.1.1, ht.1.2.le⟩, ht.2⟩

end Rudin.PMA.Chapter08
