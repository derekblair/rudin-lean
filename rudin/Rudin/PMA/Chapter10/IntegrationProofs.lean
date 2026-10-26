import Rudin.PMA.Chapter10.Integration

noncomputable section
set_option autoImplicit false
open Set Filter MeasureTheory
open scoped Topology BigOperators

namespace Rudin.PMA.Chapter10

open Chapter06

theorem Cell.isCompact_carrier {n : ℕ} (C : Cell n) : IsCompact C.carrier := isCompact_Icc

theorem Cell.isClosed_carrier {n : ℕ} (C : Cell n) : IsClosed C.carrier := isClosed_Icc

theorem Cell.mem_carrier {n : ℕ} {C : Cell n} {x : Coord n} :
    x ∈ C.carrier ↔ ∀ i, C.lower i ≤ x i ∧ x i ≤ C.upper i := by
  simp only [Cell.carrier, mem_Icc, Pi.le_def, forall_and]

theorem Cell.snoc_mem {n : ℕ} (C : Cell (n + 1)) {x : Coord n} {t : ℝ}
    (hx : x ∈ C.init.carrier)
    (ht : t ∈ Icc (C.lower (Fin.last n)) (C.upper (Fin.last n))) :
    Fin.snoc x t ∈ C.carrier := by
  rw [Cell.mem_carrier] at hx ⊢
  intro i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simpa only [Fin.snoc_last] using (And.intro ht.1 ht.2)
  · simpa only [Cell.init, Fin.snoc_castSucc] using hx j

theorem continuous_snoc (n : ℕ) :
    Continuous (fun p : Coord n × ℝ => (Fin.snoc p.1 p.2 : Coord (n + 1))) :=
  Continuous.finSnoc (A := fun _ : Fin (n + 1) => ℝ) continuous_fst continuous_snd

theorem continuousOn_slice {n : ℕ} {C : Cell (n + 1)} {f : Coord (n + 1) → ℝ}
    (hf : ContinuousOn f C.carrier) {x : Coord n} (hx : x ∈ C.init.carrier) :
    ContinuousOn (fun t => f (Fin.snoc x t))
      (Icc (C.lower (Fin.last n)) (C.upper (Fin.last n))) :=
  hf.comp (Continuous.finSnoc (A := fun _ : Fin (n + 1) => ℝ)
    (f := fun _ : ℝ => x) continuous_const continuous_id).continuousOn
      (fun _ ht => C.snoc_mem hx ht)

theorem rIntegral_congr_of_integrable {f g : ℝ → ℝ} {a b : ℝ}
    (hf : RIntegrable f a b) (hg : RIntegrable g a b) (he : EqOn f g (Icc a b)) :
    RIntegral f a b = RIntegral g a b := by
  have hb := Chapter07.rsIntegral_sub_bound (M := 0) hf hg (fun x hx => by
    rw [he hx]
    simp)
  have hz : |RIntegral f a b - RIntegral g a b| ≤ 0 := by simpa using hb
  exact sub_eq_zero.mp (abs_nonpos_iff.mp hz)

theorem exists_continuous_extension {X : Type*} [TopologicalSpace X] [NormalSpace X]
    {s : Set X} {f : X → ℝ} (hs : IsClosed s) (hf : ContinuousOn f s) :
    ∃ g : X → ℝ, Continuous g ∧ EqOn g f s := by
  let F : C(s, ℝ) := ⟨fun x => f x, continuousOn_iff_continuous_domRestrict.mp hf⟩
  obtain ⟨G, hG⟩ := F.exists_restrict_eq hs
  refine ⟨G, G.continuous, ?_⟩
  intro x hx
  exact congrArg (fun H : C(s, ℝ) => H ⟨x, hx⟩) hG

theorem rIntegral_eq_intervalIntegral_of_continuousOn {f : ℝ → ℝ} {a b : ℝ}
    (hab : a ≤ b) (hf : ContinuousOn f (Icc a b)) :
    RIntegral f a b = ∫ t in a..b, f t := by
  obtain ⟨g, hg, he⟩ := exists_continuous_extension isClosed_Icc hf
  have hfi : RIntegrable f a b := pma6_8 f id a b hab hf (monotone_id.monotoneOn _)
  have hgi : RIntegrable g a b := pma6_8 g id a b hab hg.continuousOn (monotone_id.monotoneOn _)
  calc
    RIntegral f a b = RIntegral g a b := rIntegral_congr_of_integrable hfi hgi he.symm
    _ = Chapter08.orientedRIntegral g a b := by
      simp only [Chapter08.orientedRIntegral, ite_eq_left hab]
    _ = ∫ t in a..b, g t := orientedRIntegral_eq_intervalIntegral hg a b
    _ = ∫ t in a..b, f t := intervalIntegral.integral_congr (by simpa only [uIcc_of_le hab] using he)

theorem nativeSliceIntegral_continuousOn {n : ℕ} {C : Cell (n + 1)}
    {f : Coord (n + 1) → ℝ} (hf : ContinuousOn f C.carrier) :
    ContinuousOn (nativeSliceIntegral C f) C.init.carrier := by
  let J := Icc (C.lower (Fin.last n)) (C.upper (Fin.last n))
  have hjoint : ContinuousOn (fun p : Coord n × ℝ => f (Fin.snoc p.1 p.2))
      (C.init.carrier ×ˢ J) :=
    hf.comp (continuous_snoc n).continuousOn (fun p hp => C.snoc_mem hp.1 hp.2)
  have hu := (C.init.isCompact_carrier.prod isCompact_Icc).uniformContinuousOn_of_continuous hjoint
  have hi : ∀ x ∈ C.init.carrier,
      RIntegrable (fun t => f (Fin.snoc x t)) (C.lower (Fin.last n)) (C.upper (Fin.last n)) :=
    fun x hx => pma6_8 _ id _ _ (C.lower_le_upper (Fin.last n))
      (continuousOn_slice hf hx) (monotone_id.monotoneOn _)
  intro x hx
  haveI : (𝓝[C.init.carrier] x).NeBot := nhdsWithin_neBot_of_mem hx
  have hmem : ∀ᶠ y in 𝓝[C.init.carrier] x, y ∈ C.init.carrier := self_mem_nhdsWithin
  have hlim := rsIntegral_tendsto_of_uniformFilterLimit
    (F := fun y t => f (Fin.snoc y t)) (α := id)
    (L := 𝓝[C.init.carrier] x)
    (hmem.mono fun y hy => hi y hy)
    (hu.tendstoUniformlyOn hx)
  exact hlim.2

theorem iteratedRIntegrable_of_continuousOn {n : ℕ} {C : Cell n} {f : Coord n → ℝ}
    (hf : ContinuousOn f C.carrier) : IteratedRIntegrable C f := by
  induction n with
  | zero => trivial
  | succ n ih =>
      constructor
      · intro x hx
        exact pma6_8 _ id _ _ (C.lower_le_upper (Fin.last n))
          (continuousOn_slice hf hx) (monotone_id.monotoneOn _)
      · exact ih (nativeSliceIntegral_continuousOn hf)

end Rudin.PMA.Chapter10
