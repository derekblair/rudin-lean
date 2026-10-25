import Rudin.PMA.Chapter08.RiemannBridge

open Set
open scoped BigOperators

noncomputable section
namespace Rudin.PMA.Chapter08
open Chapter06

/-! Affine changes of variables and periodic interval transfer for the native closed-cell
Darboux integral. These preserve ordinary Riemann integrability, with no measurability or
continuity hypothesis. -/

abbrev riemannReflectedPartition {a b : ℝ} (P : Partition a b) (c : ℝ) :
    Partition (c - b) (c - a) where
  n := P.n
  point := fun i => c - P.point i.rev
  mono := by
    intro i j hij
    exact sub_le_sub_left (P.mono (Fin.rev_le_rev.mpr hij)) c
  left := by simp [P.right]
  right := by simp [P.left]

theorem riemannReflectedPartition_image {a b : ℝ} (P : Partition a b) (c : ℝ)
    (i : Fin P.n) :
    (fun x : ℝ => c - x) '' (riemannReflectedPartition P c).cell i = P.cell i.rev := by
  ext x
  simp only [Partition.cell, riemannReflectedPartition, Fin.rev_castSucc, Fin.rev_succ,
    mem_image, mem_Icc]
  constructor
  · rintro ⟨y, hy, rfl⟩
    constructor <;> linarith [hy.1, hy.2]
  · intro hx
    refine ⟨c - x, ⟨?_, ?_⟩, ?_⟩ <;> linarith [hx.1, hx.2]

theorem riemannReflectedPartition_sums {a b : ℝ} (P : Partition a b) (c : ℝ)
    (f : ℝ → ℝ) :
    lowerSum (fun x => f (c - x)) id (riemannReflectedPartition P c) = lowerSum f id P ∧
    upperSum (fun x => f (c - x)) id (riemannReflectedPartition P c) = upperSum f id P := by
  have hc : ∀ i : Fin P.n,
      (fun x => f (c - x)) '' (riemannReflectedPartition P c).cell i = f '' P.cell i.rev := by
    intro i
    rw [← riemannReflectedPartition_image P c i, image_image]
  have hw : ∀ i : Fin P.n, (riemannReflectedPartition P c).weight id i = P.weight id i.rev := by
    intro i
    simp only [Partition.weight, riemannReflectedPartition, Fin.rev_castSucc, Fin.rev_succ, id_eq]
    ring
  constructor
  · unfold lowerSum
    simp_rw [cellLower, hc, hw]
    exact Equiv.sum_comp Fin.revPerm (fun i : Fin P.n => sInf (f '' P.cell i) * P.weight id i)
  · unfold upperSum
    simp_rw [cellUpper, hc, hw]
    exact Equiv.sum_comp Fin.revPerm (fun i : Fin P.n => sSup (f '' P.cell i) * P.weight id i)

theorem native_riemann_reflect {a b : ℝ} {f : ℝ → ℝ}
    (hf : RIntegrable f a b) (c : ℝ) : RIntegrable (fun x => f (c - x)) (c - b) (c - a) := by
  have hb : BoundedOn (fun x => f (c - x)) (c - b) (c - a) := by
    obtain ⟨M, hM⟩ := hf.2.1
    refine ⟨M, fun x hx => hM _ ⟨?_, ?_⟩⟩ <;> linarith [hx.1, hx.2]
  apply (rsIntegrable_iff_gap (by linarith [hf.1]) hb (monotone_id.monotoneOn _)).mpr
  intro ε hε
  obtain ⟨P, hP⟩ := (rsIntegrable_iff_gap hf.1 hf.2.1 hf.2.2.1).mp hf ε hε
  refine ⟨riemannReflectedPartition P c, ?_⟩
  rw [(riemannReflectedPartition_sums P c f).1, (riemannReflectedPartition_sums P c f).2]
  exact hP

abbrev riemannShiftedPartition {a b : ℝ} (P : Partition a b) (c : ℝ) :
    Partition (a + c) (b + c) where
  n := P.n
  point := fun i => P.point i + c
  mono := by intro i j hij; exact add_le_add (P.mono hij) le_rfl
  left := by simp [P.left]
  right := by simp [P.right]

theorem riemannShiftedPartition_image {a b : ℝ} (P : Partition a b) (c : ℝ)
    (i : Fin P.n) :
    (fun x : ℝ => x - c) '' (riemannShiftedPartition P c).cell i = P.cell i := by
  ext x
  simp only [Partition.cell, riemannShiftedPartition, mem_image, mem_Icc]
  constructor
  · rintro ⟨y, hy, rfl⟩
    constructor <;> linarith [hy.1, hy.2]
  · intro hx
    refine ⟨x + c, ⟨?_, ?_⟩, ?_⟩ <;> linarith [hx.1, hx.2]

theorem riemannShiftedPartition_sums {a b : ℝ} (P : Partition a b) (c : ℝ)
    (f : ℝ → ℝ) :
    lowerSum (fun x => f (x - c)) id (riemannShiftedPartition P c) = lowerSum f id P ∧
    upperSum (fun x => f (x - c)) id (riemannShiftedPartition P c) = upperSum f id P := by
  have hc : ∀ i : Fin P.n,
      (fun x => f (x - c)) '' (riemannShiftedPartition P c).cell i = f '' P.cell i := by
    intro i
    rw [← riemannShiftedPartition_image P c i, image_image]
  have hw : ∀ i : Fin P.n, (riemannShiftedPartition P c).weight id i = P.weight id i := by
    intro i
    simp only [Partition.weight, riemannShiftedPartition, id_eq]
    ring
  constructor
  · unfold lowerSum
    apply Finset.sum_congr rfl
    intro i _
    rw [cellLower, hc, hw]
    rfl
  · unfold upperSum
    apply Finset.sum_congr rfl
    intro i _
    rw [cellUpper, hc, hw]
    rfl

theorem native_riemann_shift {a b : ℝ} {f : ℝ → ℝ}
    (hf : RIntegrable f a b) (c : ℝ) : RIntegrable (fun x => f (x - c)) (a + c) (b + c) := by
  have hb : BoundedOn (fun x => f (x - c)) (a + c) (b + c) := by
    obtain ⟨M, hM⟩ := hf.2.1
    refine ⟨M, fun x hx => hM _ ⟨?_, ?_⟩⟩ <;> linarith [hx.1, hx.2]
  apply (rsIntegrable_iff_gap (by linarith [hf.1]) hb (monotone_id.monotoneOn _)).mpr
  intro ε hε
  obtain ⟨P, hP⟩ := (rsIntegrable_iff_gap hf.1 hf.2.1 hf.2.2.1).mp hf ε hε
  refine ⟨riemannShiftedPartition P c, ?_⟩
  rw [(riemannShiftedPartition_sums P c f).1, (riemannShiftedPartition_sums P c f).2]
  exact hP

theorem native_riemann_periodic_integrable {a T : ℝ} {f : ℝ → ℝ}
    (hT : 0 < T) (hf : RIntegrable f a (a + T)) (hp : Function.Periodic f T)
    (b c : ℝ) (hbc : b ≤ c) : RIntegrable f b c := by
  have hn : ∀ n : ℕ, RIntegrable f a (a + n * T) := by
    intro n
    induction n with
    | zero =>
      simpa using (calculus_singleton_integrals f id a).1
    | succ n ih =>
      have hs := native_riemann_shift hf (n * T)
      simp only [hp.sub_nat_mul_eq n] at hs
      have ha := split_rsIntegrable_append ih hs
      convert ha using 1
      push_cast
      ring
  have hs : ∀ n : ℕ, RIntegrable f (a - n * T) (a + n * T) := by
    intro n
    have hh := native_riemann_shift (hn (2 * n)) (-(n * T))
    have he : (fun x => f (x - -(n * T))) = f := by
      funext x
      simpa using (hp.nat_mul n x)
    rw [he] at hh
    convert hh using 1
    push_cast
    ring
  obtain ⟨n, hn⟩ := exists_nat_gt (max ((a - b) / T) ((c - a) / T))
  have hl : a - n * T ≤ b := by
    have : (a - b) / T < n := (le_max_left _ _).trans_lt hn
    have := (div_lt_iff₀ hT).mp this
    linarith
  have hr : c ≤ a + n * T := by
    have : (c - a) / T < n := (le_max_right _ _).trans_lt hn
    have := (div_lt_iff₀ hT).mp this
    linarith
  exact (split_rsIntegrable hbc hr (split_rsIntegrable hl (hbc.trans hr) (hs n)).2).1

theorem native_complex_reflect {a b : ℝ} {f : ℝ → ℂ}
    (hf : ComplexRSIntegrable f id a b) (c : ℝ) :
    ComplexRSIntegrable (fun x => f (c - x)) id (c - b) (c - a) :=
  ⟨native_riemann_reflect hf.1 c, native_riemann_reflect hf.2 c⟩

theorem native_complex_periodic_integrable {a T : ℝ} {f : ℝ → ℂ}
    (hT : 0 < T) (hf : ComplexRSIntegrable f id a (a + T))
    (hp : Function.Periodic f T) (b c : ℝ) (hbc : b ≤ c) :
    ComplexRSIntegrable f id b c := by
  exact ⟨native_riemann_periodic_integrable hT hf.1 (hp.comp Complex.re) b c hbc,
    native_riemann_periodic_integrable hT hf.2 (hp.comp Complex.im) b c hbc⟩

theorem periodic_riemann_translate_native_integrable {f : ℝ → ℂ}
    (hf : ComplexRSIntegrable f id (-Real.pi) Real.pi)
    (hp : Function.Periodic f (2 * Real.pi)) (x : ℝ) :
    ComplexRSIntegrable (fun t => f (x - t)) id (-Real.pi) Real.pi := by
  have hf' : ComplexRSIntegrable f id (-Real.pi) (-Real.pi + 2 * Real.pi) := by
    convert hf using 1
    ring
  have ht := native_complex_periodic_integrable (by positivity : 0 < 2 * Real.pi)
    hf' hp (x - Real.pi) (x + Real.pi) (by linarith [Real.pi_pos])
  convert native_complex_reflect ht x using 1 <;> ring

end Rudin.PMA.Chapter08
