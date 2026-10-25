import Rudin.PMA.Chapter06

set_option autoImplicit false

noncomputable section
open Set Filter Topology MeasureTheory
open scoped BigOperators ENNReal

namespace Rudin.PMA.Chapter08

/-! Native Darboux integration and the library integral.
The bridge retains arbitrary bounded Riemann-integrable functions, including
discontinuous functions; measurability is a conclusion of the Darboux criterion.
-/

def partitionStep {a b : ℝ} (P : Chapter06.Partition a b)
    (v : Fin P.n → ℝ) (x : ℝ) : ℝ :=
  ∑ i, (Ioc (P.point i.castSucc) (P.point i.succ)).indicator (fun _ => v i) x

theorem partitionStep_measurable {a b : ℝ} (P : Chapter06.Partition a b)
    (v : Fin P.n → ℝ) : Measurable (partitionStep P v) := by
  unfold partitionStep
  exact Finset.measurable_sum _ fun i _ => measurable_const.indicator measurableSet_Ioc

theorem partitionStep_integrable {a b : ℝ} (P : Chapter06.Partition a b)
    (v : Fin P.n → ℝ) : Integrable (partitionStep P v) := by
  apply integrable_finsetSum
  intro i _
  exact (integrableOn_const measure_Ioc_lt_top.ne).integrable_indicator measurableSet_Ioc

theorem partitionStep_integral {a b : ℝ} (P : Chapter06.Partition a b)
    (v : Fin P.n → ℝ) :
    (∫ x, partitionStep P v x) = ∑ i, v i * P.weight id i := by
  simp only [partitionStep]
  rw [integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro i _
    rw [integral_indicator_const _ measurableSet_Ioc, Real.volume_real_Ioc_of_le (P.cell_order i)]
    simp [Chapter06.Partition.weight, smul_eq_mul, mul_comm]
  · intro i _
    exact (integrableOn_const measure_Ioc_lt_top.ne).integrable_indicator measurableSet_Ioc

theorem partition_exists_cell {a b x : ℝ} (P : Chapter06.Partition a b)
    (hx : x ∈ Ioc a b) :
    ∃ i : Fin P.n, x ∈ Ioc (P.point i.castSucc) (P.point i.succ) := by
  let q : ℕ → ℝ := fun k => P.point ⟨min k P.n, by omega⟩
  have hq0 : q 0 = a := by simpa [q] using P.left
  have hqn : q P.n = b := by
    simpa only [q, min_self, Fin.last] using P.right
  have hx' : x ∈ Ioc (q 0) (q P.n) := by simpa only [hq0, hqn] using hx
  have h := Ioc_subset_biUnion_Ioc P.n q hx'
  simp only [mem_iUnion, Finset.mem_range] at h
  obtain ⟨i, hi, hix⟩ := h
  refine ⟨⟨i, hi⟩, ?_⟩
  simpa [q, min_eq_left (Nat.le_of_lt hi), min_eq_left (by omega : i + 1 ≤ P.n),
    Fin.castSucc_mk, Fin.succ_mk] using hix

theorem partition_cell_unique {a b x : ℝ} (P : Chapter06.Partition a b)
    {i j : Fin P.n}
    (hi : x ∈ Ioc (P.point i.castSucc) (P.point i.succ))
    (hj : x ∈ Ioc (P.point j.castSucc) (P.point j.succ)) : i = j := by
  apply le_antisymm
  · by_contra h
    have hji : j.succ ≤ i.castSucc := by exact_mod_cast (show j.val + 1 ≤ i.val by omega)
    have h := P.mono hji
    linarith [hi.1, hj.2]
  · by_contra h
    have hij : i.succ ≤ j.castSucc := by exact_mod_cast (show i.val + 1 ≤ j.val by omega)
    have h := P.mono hij
    linarith [hj.1, hi.2]

theorem partitionStep_eq_cell {a b x : ℝ} (P : Chapter06.Partition a b)
    (v : Fin P.n → ℝ) {i : Fin P.n}
    (hx : x ∈ Ioc (P.point i.castSucc) (P.point i.succ)) :
    partitionStep P v x = v i := by
  rw [partitionStep, Finset.sum_eq_single i]
  · exact indicator_of_mem hx _
  · intro j _ hji
    apply indicator_of_notMem
    intro hj
    exact hji (partition_cell_unique P hj hx)
  · simp

theorem partitionStep_eq_zero {a b x : ℝ} (P : Chapter06.Partition a b)
    (v : Fin P.n → ℝ) (hx : x ∉ Ioc a b) : partitionStep P v x = 0 := by
  apply Finset.sum_eq_zero
  intro i _
  apply indicator_of_notMem
  intro hi
  exact hx ⟨(P.point_mem i.castSucc).1.trans_lt hi.1,
    hi.2.trans (P.point_mem i.succ).2⟩

/-- Measurable upper and lower envelopes with arbitrarily small integral gap
establish integrability without any measurability premise on the sandwiched
function. The common integrable bound controls the countable envelopes. -/
theorem integrable_of_darboux_sandwich (f : ℝ → ℝ) (L U : ℕ → ℝ → ℝ)
    (B : ℝ → ℝ) (hB : Integrable B)
    (hLm : ∀ n, Measurable (L n)) (hUm : ∀ n, Measurable (U n))
    (hLb : ∀ n x, |L n x| ≤ B x) (hUb : ∀ n x, |U n x| ≤ B x)
    (hLf : ∀ n x, L n x ≤ f x) (hfU : ∀ n x, f x ≤ U n x)
    (hgap : ∀ n, (∫ x, U n x) - (∫ x, L n x) < 1 / (n + 1 : ℝ)) :
    Integrable f := by
  let l : ℝ → ℝ := fun x => ⨆ n, L n x
  let u : ℝ → ℝ := fun x => ⨅ n, U n x
  have hLbdd (x : ℝ) : BddAbove (range (fun n => L n x)) :=
    ⟨B x, by rintro _ ⟨n, rfl⟩; exact (le_abs_self _).trans (hLb n x)⟩
  have hUbdd (x : ℝ) : BddBelow (range (fun n => U n x)) :=
    ⟨-B x, by rintro _ ⟨n, rfl⟩; exact (abs_le.mp (hUb n x)).1⟩
  have hLl (n : ℕ) (x : ℝ) : L n x ≤ l x := le_ciSup (hLbdd x) n
  have huU (n : ℕ) (x : ℝ) : u x ≤ U n x := ciInf_le (hUbdd x) n
  have hlf (x : ℝ) : l x ≤ f x := ciSup_le (hLf · x)
  have hfu (x : ℝ) : f x ≤ u x := le_ciInf (hfU · x)
  have hlb (x : ℝ) : |l x| ≤ B x := by
    apply abs_le.mpr
    exact ⟨(abs_le.mp (hLb 0 x)).1.trans (hLl 0 x),
      ciSup_le fun n => (le_abs_self _).trans (hLb n x)⟩
  have hub (x : ℝ) : |u x| ≤ B x := by
    apply abs_le.mpr
    exact ⟨le_ciInf fun n => (abs_le.mp (hUb n x)).1,
      (huU 0 x).trans ((le_abs_self _).trans (hUb 0 x))⟩
  have hli : Integrable l := hB.mono' (Measurable.iSup hLm).aestronglyMeasurable
    (Eventually.of_forall fun x => by simpa only [Real.norm_eq_abs] using hlb x)
  have hui : Integrable u := hB.mono' (Measurable.iInf hUm).aestronglyMeasurable
    (Eventually.of_forall fun x => by simpa only [Real.norm_eq_abs] using hub x)
  have hLi (n : ℕ) : Integrable (L n) := hB.mono' (hLm n).aestronglyMeasurable
    (Eventually.of_forall fun x => by simpa only [Real.norm_eq_abs] using hLb n x)
  have hUi (n : ℕ) : Integrable (U n) := hB.mono' (hUm n).aestronglyMeasurable
    (Eventually.of_forall fun x => by simpa only [Real.norm_eq_abs] using hUb n x)
  have hlu (x : ℝ) : l x ≤ u x := (hlf x).trans (hfu x)
  have hieq : (∫ x, l x) = ∫ x, u x := by
    apply le_antisymm (integral_mono hli hui hlu)
    apply le_of_forall_pos_le_add
    intro ε hε
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt hε
    have h1 := integral_mono (hLi n) hli (hLl n)
    have h2 := integral_mono hui (hUi n) (huU n)
    have h3 := hgap n
    linarith
  have hae : l =ᵐ[volume] u :=
    (integral_eq_iff_of_ae_le hli hui (Eventually.of_forall hlu)).mp hieq
  have hfeq : l =ᵐ[volume] f := hae.mono fun x hx =>
    le_antisymm (hlf x) (hx ▸ hfu x)
  exact hli.congr hfeq

theorem darboux_cell_bounds {a b M : ℝ} {f : ℝ → ℝ}
    (hM : ∀ x ∈ Icc a b, |f x| ≤ M) (P : Chapter06.Partition a b) (i : Fin P.n) :
    |Chapter06.cellLower f P i| ≤ M ∧ |Chapter06.cellUpper f P i| ≤ M := by
  have hf : Chapter06.BoundedOn f a b := ⟨M, hM⟩
  have hl : P.point i.castSucc ∈ P.cell i := ⟨le_rfl, P.cell_order i⟩
  have hp := abs_le.mp (hM _ (P.point_mem i.castSucc))
  constructor
  · apply abs_le.mpr
    constructor
    · apply le_csInf ((P.cell_nonempty i).image f)
      rintro _ ⟨x, hx, rfl⟩
      exact (abs_le.mp (hM x (P.cell_subset i hx))).1
    · exact (Chapter06.cellLower_le_value hf P i hl).trans hp.2
  · apply abs_le.mpr
    constructor
    · exact hp.1.trans (Chapter06.value_le_cellUpper hf P i hl)
    · apply csSup_le ((P.cell_nonempty i).image f)
      rintro _ ⟨x, hx, rfl⟩
      exact (abs_le.mp (hM x (P.cell_subset i hx))).2

theorem darboux_step_bounds {a b M : ℝ} {f : ℝ → ℝ}
    (hM : ∀ x ∈ Icc a b, |f x| ≤ M) (P : Chapter06.Partition a b) (x : ℝ) :
    |partitionStep P (Chapter06.cellLower f P) x| ≤
        (Ioc a b).indicator (fun _ => M) x ∧
    |partitionStep P (Chapter06.cellUpper f P) x| ≤
        (Ioc a b).indicator (fun _ => M) x ∧
    partitionStep P (Chapter06.cellLower f P) x ≤ (Ioc a b).indicator f x ∧
    (Ioc a b).indicator f x ≤ partitionStep P (Chapter06.cellUpper f P) x := by
  by_cases hx : x ∈ Ioc a b
  · obtain ⟨i, hi⟩ := partition_exists_cell P hx
    rw [partitionStep_eq_cell P _ hi, partitionStep_eq_cell P _ hi,
      indicator_of_mem hx, indicator_of_mem hx]
    exact ⟨(darboux_cell_bounds hM P i).1, (darboux_cell_bounds hM P i).2,
      Chapter06.cellLower_le_value ⟨M, hM⟩ P i ⟨hi.1.le, hi.2⟩,
      Chapter06.value_le_cellUpper ⟨M, hM⟩ P i ⟨hi.1.le, hi.2⟩⟩
  · simp only [partitionStep_eq_zero P _ hx, indicator_of_notMem hx, abs_zero,
      le_refl, and_self]

/-- Full native Riemann integrability implies library interval integrability.
The proof derives almost-everywhere measurability from Darboux envelopes. -/
theorem native_riemann_intervalIntegrable {a b : ℝ} {f : ℝ → ℝ}
    (hf : Chapter06.RIntegrable f a b) : IntervalIntegrable f volume a b := by
  obtain ⟨M, hM⟩ := hf.2.1
  have hchoose (n : ℕ) : ∃ P : Chapter06.Partition a b,
      Chapter06.upperSum f id P - Chapter06.lowerSum f id P < 1 / (n + 1 : ℝ) :=
    (Chapter06.rsIntegrable_iff_gap hf.1 hf.2.1 hf.2.2.1).mp hf _ (by positivity)
  choose P hP using hchoose
  let L : ℕ → ℝ → ℝ := fun n => partitionStep (P n) (Chapter06.cellLower f (P n))
  let U : ℕ → ℝ → ℝ := fun n => partitionStep (P n) (Chapter06.cellUpper f (P n))
  have hb (n : ℕ) (x : ℝ) := darboux_step_bounds hM (P n) x
  have hi : Integrable ((Ioc a b).indicator f) :=
    integrable_of_darboux_sandwich _ L U ((Ioc a b).indicator (fun _ => M))
      ((integrableOn_const measure_Ioc_lt_top.ne).integrable_indicator measurableSet_Ioc)
      (fun n => partitionStep_measurable _ _) (fun n => partitionStep_measurable _ _)
      (fun n x => (hb n x).1) (fun n x => (hb n x).2.1)
      (fun n x => (hb n x).2.2.1) (fun n x => (hb n x).2.2.2)
      (fun n => by
        simpa only [L, U, partitionStep_integral, Chapter06.upperSum, Chapter06.lowerSum]
          using hP n)
  exact (intervalIntegrable_iff_integrableOn_Ioc_of_le hf.1).mpr
    ((integrable_indicator_iff measurableSet_Ioc).mp hi)

/-- Equality of the native Darboux value with the library integral, with no
extra continuity or measurability assumption. -/
theorem native_riemann_integral_eq {a b : ℝ} {f : ℝ → ℝ}
    (hf : Chapter06.RIntegrable f a b) :
    Chapter06.RIntegral f a b = ∫ x in a..b, f x := by
  have hfi := native_riemann_intervalIntegrable hf
  have hi : Integrable ((Ioc a b).indicator f) :=
    ((intervalIntegrable_iff_integrableOn_Ioc_of_le hf.1).mp hfi).integrable_indicator
      measurableSet_Ioc
  have hIB (P : Chapter06.Partition a b) :
      Chapter06.lowerSum f id P ≤ ∫ x in a..b, f x ∧
      (∫ x in a..b, f x) ≤ Chapter06.upperSum f id P := by
    obtain ⟨M, hM⟩ := hf.2.1
    have hL := integral_mono (partitionStep_integrable P (Chapter06.cellLower f P)) hi
      (fun x => (darboux_step_bounds hM P x).2.2.1)
    have hU := integral_mono hi (partitionStep_integrable P (Chapter06.cellUpper f P))
      (fun x => (darboux_step_bounds hM P x).2.2.2)
    simpa only [partitionStep_integral, integral_indicator measurableSet_Ioc,
      ← intervalIntegral.integral_of_le hf.1, Chapter06.lowerSum, Chapter06.upperSum]
      using And.intro hL hU
  apply le_antisymm
  · change sSup (range (Chapter06.lowerSum f id : Chapter06.Partition a b → ℝ)) ≤ _
    apply csSup_le
    · exact ⟨_, Chapter06.Partition.single hf.1, rfl⟩
    · rintro _ ⟨P, rfl⟩
      exact (hIB P).1
  · change _ ≤ Chapter06.lowerIntegral f id a b
    rw [hf.2.2.2]
    apply le_csInf
    · exact ⟨_, Chapter06.Partition.single hf.1, rfl⟩
    · rintro _ ⟨P, rfl⟩
      exact (hIB P).2

/-- The native coordinatewise complex Riemann integral has the same full
integrability scope as the scalar bridge. -/
theorem native_complex_intervalIntegrable {a b : ℝ} {f : ℝ → ℂ}
    (hf : Chapter06.ComplexRSIntegrable f id a b) : IntervalIntegrable f volume a b := by
  have hr := native_riemann_intervalIntegrable hf.1
  have hi := native_riemann_intervalIntegrable hf.2
  have heq : (fun x => ((f x).re : ℂ) + ((f x).im : ℂ) * Complex.I) = f := by
    funext x
    exact Complex.re_add_im (f x)
  rw [← heq]
  exact ⟨hr.1.ofReal.add (hi.1.ofReal.mul_const Complex.I),
    hr.2.ofReal.add (hi.2.ofReal.mul_const Complex.I)⟩

theorem native_complex_integral_eq {a b : ℝ} {f : ℝ → ℂ}
    (hf : Chapter06.ComplexRSIntegrable f id a b) :
    Chapter06.ComplexRSIntegral f id a b = ∫ x in a..b, f x := by
  change (Chapter06.RIntegral (fun x => (f x).re) a b : ℂ) +
    (Chapter06.RIntegral (fun x => (f x).im) a b : ℂ) * Complex.I = _
  rw [native_riemann_integral_eq hf.1, native_riemann_integral_eq hf.2]
  simp only [intervalIntegral.integral_of_le hf.1.1]
  exact integral_re_add_im (native_complex_intervalIntegrable hf).1

/-- Native boundedness and the proved measurability bridge give every finite
Lp exponent on the compact interval, as well as essential boundedness. -/
theorem native_complex_memLp {a b : ℝ} {f : ℝ → ℂ}
    (hf : Chapter06.ComplexRSIntegrable f id a b) (p : ℝ≥0∞) :
    MemLp f p (volume.restrict (Ioc a b)) := by
  obtain ⟨M, hM⟩ := hf.1.2.1
  obtain ⟨N, hN⟩ := hf.2.2.1
  apply MemLp.of_bound (native_complex_intervalIntegrable hf).1.aestronglyMeasurable (M + N)
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
  exact (Complex.norm_le_abs_re_add_abs_im (f x)).trans
    (add_le_add (hM x ⟨hx.1.le, hx.2⟩) (hN x ⟨hx.1.le, hx.2⟩))

end Rudin.PMA.Chapter08
